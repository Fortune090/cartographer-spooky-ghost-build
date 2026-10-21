#include "stdafx.h"
#include "GhostViewer.h"

#ifndef IMGUI_DISABLE
#include "imgui.h"

#include "camera/camera.h"
#include "camera/observer.h"
#include "H2MOD/Modules/Shell/Config.h"
#include "game/game.h"
#include "game/game_time.h"
#include "game/players.h"
#include "math/matrix_math.h"
#include "render/render.h"
#include "main/interpolator.h"
#include "memory/data.h"
#include "objects/objects.h"
#include "physics/collision_bsp_definition.h"
#include "render/render_cameras.h"
#include "structures/structure_bsp_definitions.h"
#include "units/units.h"
#include "ai/ai.h"
#include "cutscene/cinematics.h"
#include "physics/havok.h"

#include <intrin.h>
#include <Xinput.h>
#include <algorithm>
#include <cstdarg>
#include <map>
#include <cmath>
#include <cstdio>
#include <string>

/*
	Halo 2 Vista (halo2.exe, 32-bit) layout used here. Offsets are image-relative (Memory::GetAddress adds the base).
	Found by matching the code against the MCC halo2.dll routines the HCM collision viewer reads:

	hkWorld*                      0x4CE840 (written by havok_initialize_havok_world after `new hkWorld`)
	  active islands              world +0x08 (ptr) / +0x0C (count); every island points back: island +0x20 == world
	  backstep parameters         world +0x244 base, +0x248 per-S step, +0x24C time resolution  (island pass 0x6FCD13)
	island pair list              island +0x68 (ptr) / +0x6C (count), 16-byte entries {handleA, handleB, agent, S}
	  broadphase handle h         collidable = h - 0x10 (shape* at +0, motion state* at +8)
	                              owning entity = *(h + 0x10); motion* = *(entity + 0x3C)
	  motion state                transform at +0x20: rotation columns +0x20/+0x30/+0x40, translation +0x50
	  motion                      previous +0x60, current +0x70, time +0x7C (1.0 after integrate; setTime 0x7002F5)
	havok globals (Cartographer)  0x418AC8: { profiler, environment_body, ... }
	shape getType                 vtable slot 5 (+0x14): `mov eax, type ; ret`;  capsule = 7: radius +0x0C, ends +0x10 / +0x20
	environment MOPP shape vtable 0x3C29FC (c_environment_mopp_bv_tree_shape)
	convex-convex welder agent    vtable 0x3F1274 (symmetric 0x3F1294); processCollision 0x6BF77F, child update 0x6BB7EB
	  children                    agent +0x0C (ptr) / +0x10 (count), 12-byte entries {key, ?, agent}
	  stored query box            agent +0x20 (min) / +0x30 (max): capsule box + 1.5 x tolerance
	GSK / sweep leaf agents       vtables 0x3F15A4 / 0x3F09EC: manifold +0x14, separating normal +0x20, TIM +0x2C
	                              (TIM update 0x6D1B11: tim -= n . (dB - dA) + wA + wB, skipped while tim > 0)
	null agent instance           0x46A1F0
	collision tolerance           0.0328 (hkWorldCinfo in havok_initialize_havok_world)
	level shape child keys        key >> 29: 1 = structure polygon (surface = key & 0xFFFF),
	                              5 = instanced geometry polygon (instance = key & 0xFFFF, surface = (key >> 16) & 0x1FFF)
*/

namespace GhostViewer
{
	s_settings g_settings;

	namespace
	{
		/* ---- offsets ---- */
		constexpr uintptr_t k_world_ptr = 0x4CE840;
		constexpr uintptr_t k_havok_globals = 0x418AC8;
		constexpr uintptr_t k_vt_welder = 0x3F1274;
		constexpr uintptr_t k_vt_welder_sym = 0x3F1294;
		constexpr uintptr_t k_vt_gsk = 0x3F15A4;
		constexpr uintptr_t k_vt_sweep = 0x3F09EC;      // hkConvexSweepConvexAgent (ctor writes 0x7F09EC; confirmed in game: the welder's children)
		constexpr uintptr_t k_vt_sweep_alt = 0x3F09E0;  // neighbouring table, kept as a fallback
		constexpr uintptr_t k_vt_env_mopp = 0x3C29FC;
		constexpr uintptr_t k_null_agent = 0x46A1F0;
		constexpr float k_tolerance = 0.0328f;

		/* ---- safe reads ---- */
		bool rd(uintptr_t a, void* out, size_t n)
		{
			if (a < 0x10000 || a > 0xBFFF0000) return false;
			__try { memcpy(out, (const void*)a, n); return true; }
			__except (EXCEPTION_EXECUTE_HANDLER) { return false; }
		}
		uint32 u32(uintptr_t a, uint32 def = 0) { uint32 v; return rd(a, &v, 4) ? v : def; }
		int32 i32(uintptr_t a, int32 def = 0) { int32 v; return rd(a, &v, 4) ? v : def; }
		float f32(uintptr_t a, float def = 0.f) { float v; return rd(a, &v, 4) ? v : def; }
		bool okp(uintptr_t p) { return p >= 0x10000 && p < 0xBFFF0000 && (p & 3) == 0; }
		bool put(uintptr_t dst, const void* src, size_t n)
		{
			if (dst < 0x10000 || dst >= 0xBFFF0000) return false;   // any alignment (the revert flag is a byte at an odd address)
			__try { memcpy((void*)dst, src, n); return true; }
			__except (EXCEPTION_EXECUTE_HANDLER) { return false; }
		}
		// code addresses are not 4-byte aligned: a function pointer is valid when it lies in the game's code section
		bool okfn(uintptr_t f) { const uintptr_t rel = f - Memory::GetAddress(); return rel >= 0x1000 && rel < 0x39B000; }
		uintptr_t addr(uintptr_t off) { return Memory::GetAddress(off); }

		/* ---- math ---- */
		struct v3 { float x, y, z; };
		v3 operator+(v3 a, v3 b) { return { a.x + b.x, a.y + b.y, a.z + b.z }; }
		v3 operator-(v3 a, v3 b) { return { a.x - b.x, a.y - b.y, a.z - b.z }; }
		v3 operator*(v3 a, float s) { return { a.x * s, a.y * s, a.z * s }; }
		float dot(v3 a, v3 b) { return a.x * b.x + a.y * b.y + a.z * b.z; }
		v3 cross(v3 a, v3 b) { return { a.y * b.z - a.z * b.y, a.z * b.x - a.x * b.z, a.x * b.y - a.y * b.x }; }
		float len(v3 a) { return std::sqrt(dot(a, a)); }
		v3 norm(v3 a) { const float l = len(a); return l > 1e-12f ? a * (1.f / l) : v3{ 0, 0, 0 }; }
		float clampf(float v, float lo, float hi) { return v < lo ? lo : (v > hi ? hi : v); }

		struct xform { v3 c[3]; v3 t; };
		v3 xf_point(const xform& x, v3 p) { return x.c[0] * p.x + x.c[1] * p.y + x.c[2] * p.z + x.t; }

		bool read_vec(uintptr_t a, v3& out) { float f[3]; if (!rd(a, f, 12)) return false; out = { f[0], f[1], f[2] }; return std::isfinite(f[0]) && std::isfinite(f[1]) && std::isfinite(f[2]); }

		// segment / polygon distances (Ericson, Real-Time Collision Detection 5.1.9)
		float seg_seg_dist2(v3 p1, v3 q1, v3 p2, v3 q2)
		{
			const v3 d1 = q1 - p1, d2 = q2 - p2, r = p1 - p2;
			const float a = dot(d1, d1), e = dot(d2, d2), f = dot(d2, r);
			float s, t;
			if (a <= 1e-12f && e <= 1e-12f) return dot(r, r);
			if (a <= 1e-12f) { s = 0; t = clampf(f / e, 0.f, 1.f); }
			else
			{
				const float c = dot(d1, r);
				if (e <= 1e-12f) { t = 0; s = clampf(-c / a, 0.f, 1.f); }
				else
				{
					const float b = dot(d1, d2), den = a * e - b * b;
					s = den != 0 ? clampf((b * f - c * e) / den, 0.f, 1.f) : 0.f;
					t = (b * s + f) / e;
					if (t < 0) { t = 0; s = clampf(-c / a, 0.f, 1.f); }
					else if (t > 1) { t = 1; s = clampf((b - c) / a, 0.f, 1.f); }
				}
			}
			const v3 d = (p1 + d1 * s) - (p2 + d2 * t);
			return dot(d, d);
		}

		// closest point of a convex polygon to p
		v3 closest_point_poly(v3 p, const std::vector<v3>& poly)
		{
			const v3 n = norm(cross(poly[1] - poly[0], poly[2] - poly[0]));
			const v3 q = p - n * dot(p - poly[0], n);
			bool inside = true;
			for (size_t i = 0; i < poly.size(); ++i)
			{
				const v3 a = poly[i], b = poly[(i + 1) % poly.size()];
				if (dot(cross(b - a, q - a), n) < 0) { inside = false; break; }
			}
			if (inside) return q;
			v3 best = poly[0]; float bd = 1e30f;
			for (size_t i = 0; i < poly.size(); ++i)
			{
				const v3 a = poly[i], b = poly[(i + 1) % poly.size()], ab = b - a;
				const float l2 = dot(ab, ab);
				const float tt = l2 > 1e-12f ? clampf(dot(p - a, ab) / l2, 0.f, 1.f) : 0.f;
				const v3 c = a + ab * tt;
				const float d = dot(p - c, p - c);
				if (d < bd) { bd = d; best = c; }
			}
			return best;
		}

		float seg_poly_dist(v3 A, v3 B, const std::vector<v3>& poly)
		{
			if (poly.size() < 3) return 1e9f;
			const v3 n = norm(cross(poly[1] - poly[0], poly[2] - poly[0]));
			auto inside = [&](v3 p)
			{
				for (size_t i = 0; i < poly.size(); ++i)
				{
					const v3 a = poly[i], b = poly[(i + 1) % poly.size()];
					if (dot(cross(b - a, p - a), n) < -1e-6f) return false;
				}
				return true;
			};
			const float da = dot(A - poly[0], n), db = dot(B - poly[0], n);
			if ((da > 0) != (db > 0) && std::fabs(da - db) > 1e-9f)
			{
				const v3 x = A + (B - A) * (da / (da - db));
				if (inside(x)) return 0.f;
			}
			float best = 1e18f;
			for (const v3 p : { A, B })
			{
				const float h = dot(p - poly[0], n);
				if (inside(p - n * h)) best = (std::min)(best, h * h);
			}
			for (size_t i = 0; i < poly.size(); ++i)
				best = (std::min)(best, seg_seg_dist2(A, B, poly[i], poly[(i + 1) % poly.size()]));
			return std::sqrt(best);
		}

		/* ---- colours ---- */
		ImU32 col(int rgb, int alpha = 255)
		{
			return IM_COL32((rgb >> 16) & 0xFF, (rgb >> 8) & 0xFF, rgb & 0xFF, alpha);
		}

		/* ---- projection onto the ImGui background layer ---- */
		// Each player's own camera (observer_get_camera: the camera the frame was rendered with), projected onto that
		// player's split-screen viewport. The global render projection is not usable here: by the time ImGui draws, it
		// holds the last pass's projection (UI), which is why the first build drew everything at one fixed screen point.
		struct s_view
		{
			bool ok = false;
			v3 pos{}, fwd{}, right{}, up{};
			float tanx = 1.f, tany = 1.f;
			bool use_proj = false; const render_projection* proj = nullptr;   // the game's captured projection for this view
			float x0 = 0, y0 = 0, w = 1, h = 1;
			ImDrawList* dl = nullptr;
		};
		s_view g_view;

		// The exact camera and projection each player's view was rendered with, captured during that player's HUD pass
		// (GhostViewer::capture_view, from interface_draw_screen): the game projects nav points with these same matrices.
		struct s_captured_view { bool valid = false; uint32 frame = 0; render_camera camera; render_projection projection; };
		s_captured_view g_captured[4];
		uint32 g_frame_counter = 0;

		bool set_view_from_capture(int32 user)
		{
			if (user < 0 || user > 3) return false;
			const s_captured_view& cv = g_captured[user];
			if (!cv.valid || g_frame_counter - cv.frame > 2) return false;
			const render_camera* cam = &cv.camera;
			const ImGuiIO& io = ImGui::GetIO();
			const float ww = (float)(cam->window_bounds.right - cam->window_bounds.left), wh = (float)(cam->window_bounds.bottom - cam->window_bounds.top);
			if (ww < 2 || wh < 2) return false;
			const float sx = io.DisplaySize.x / ww, sy = io.DisplaySize.y / wh;
			s_view v;
			v.use_proj = true; v.proj = &cv.projection;
			v.x0 = (float)(cam->viewport_bounds.left - cam->window_bounds.left) * sx;
			v.y0 = (float)(cam->viewport_bounds.top - cam->window_bounds.top) * sy;
			v.w = (float)(cam->viewport_bounds.right - cam->viewport_bounds.left) * sx;
			v.h = (float)(cam->viewport_bounds.bottom - cam->viewport_bounds.top) * sy;
			v.pos = { cam->point.x, cam->point.y, cam->point.z };
			v.dl = ImGui::GetBackgroundDrawList();
			v.ok = v.w > 1 && v.h > 1;
			if (!v.ok) return false;
			g_view = v;
			return true;
		}

		bool set_view_for_user(int32 user, int32 slot, int32 count)
		{
			if (set_view_from_capture(user)) return true;
			const s_observer_result* o = camera_override(user, observer_get_camera(user));
			if (!o) return false;
			const ImGuiIO& io = ImGui::GetIO();
			float x0 = 0, y0 = 0, w = io.DisplaySize.x, h = io.DisplaySize.y;
			if (count == 2)
			{
				if ((uint32)H2Config_split_mode == 2) { w *= 0.5f; x0 = (float)slot * w; }   // 2 = _display_split_type_vertical (render/render.h)
				else { h *= 0.5f; y0 = (float)slot * h; }
			}
			else if (count > 2)
			{
				w *= 0.5f; h *= 0.5f; x0 = (float)(slot & 1) * w; y0 = (float)(slot >> 1) * h;
			}
			s_view v;
			v.pos = { o->position.x, o->position.y, o->position.z };
			v.fwd = norm(v3{ o->forward.i, o->forward.j, o->forward.k });
			v.up = norm(v3{ o->up.i, o->up.j, o->up.k });
			v.right = norm(cross(v.fwd, v.up));          // Halo: x forward, y left, z up -> forward x up = right
			v.up = cross(v.right, v.fwd);                // re-orthogonalise
			const float aspect = h > 1 ? w / h : 1.f;
			float vf = o->vertical_field_of_view, hf = o->horizontal_field_of_view;
			if (hf > 3.2f) hf *= 3.14159265f / 180.f;     // degrees, just in case
			if (vf > 3.2f) vf *= 3.14159265f / 180.f;
			if (vf > 0.2f && vf < 2.8f) { v.tany = std::tan(vf * 0.5f); v.tanx = v.tany * aspect; }
			else if (hf > 0.2f && hf < 3.0f) { v.tanx = std::tan(hf * 0.5f); v.tany = v.tanx / aspect; }
			else return false;
			v.x0 = x0; v.y0 = y0; v.w = w; v.h = h;
			v.dl = ImGui::GetBackgroundDrawList();
			v.ok = len(v.fwd) > 0.5f && std::isfinite(v.pos.x);
			g_view = v;
			return v.ok;
		}

		// view space: x right, y up, z = -depth (negative in front of the camera)
		bool to_view(v3 w, v3& v)
		{
			if (g_view.use_proj)
			{
				real_point3d p{}, o{};
				p.x = w.x; p.y = w.y; p.z = w.z;
				matrix4x3_transform_point(&g_view.proj->world_to_view, &p, &o);
				v = { o.x, o.y, o.z };
				return true;
			}
			const v3 d = w - g_view.pos;
			v = { dot(d, g_view.right), dot(d, g_view.up), -dot(d, g_view.fwd) };
			return true;
		}

		ImVec2 view_to_screen(v3 v)
		{
			const float depth = -v.z;
			if (g_view.use_proj)
			{   // render_camera_world_to_screen, with the viewport scaled to the ImGui display
				const auto& m = g_view.proj->projection_matrix.matrix;
				const float iz = -1.f / v.z;
				const float x = (m[0][0] * v.x + m[2][0] * v.z) * iz;
				const float y = (m[1][1] * v.y + m[2][1] * v.z) * -iz;
				return ImVec2(g_view.x0 + (x * 0.5f + 0.5f) * g_view.w, g_view.y0 + (y * 0.5f + 0.5f) * g_view.h);
			}
			const float nx = v.x / (depth * g_view.tanx), ny = v.y / (depth * g_view.tany);
			return ImVec2(g_view.x0 + (nx * 0.5f + 0.5f) * g_view.w, g_view.y0 + (0.5f - ny * 0.5f) * g_view.h);
		}

		constexpr float k_near = 0.05f;

		int g_lines_drawn = 0;   // diagnostics: lines actually handed to ImGui

		// Everything a player's overlay draws is also recorded in world space, so the last live state can be shown again
		// while that player's physics island is asleep (no pairs to read) - see draw_player.
		struct s_prim { uint8 kind; v3 a, b; ImU32 c; float thick; std::string s; std::vector<v3> poly; };
		std::vector<s_prim>* g_rec = nullptr;

		void line(v3 a, v3 b, ImU32 c, float thick = 1.5f)
		{
			if (g_rec) g_rec->push_back({ 0, a, b, c, thick, {}, {} });
			v3 va, vb;
			to_view(a, va); to_view(b, vb);
			// clip against the near plane (view space looks down -z)
			const bool ia = va.z < -k_near, ib = vb.z < -k_near;
			if (!ia && !ib) return;
			if (ia != ib)
			{
				const float t = (-k_near - va.z) / (vb.z - va.z);
				const v3 m = va + (vb - va) * t;
				if (ia) vb = m; else va = m;
			}
			const ImVec2 sa = view_to_screen(va), sb = view_to_screen(vb);
			if (!std::isfinite(sa.x) || !std::isfinite(sb.x)) return;
			g_view.dl->AddLine(sa, sb, c, thick);
			++g_lines_drawn;
		}

		bool point(v3 w, ImVec2& s)
		{
			v3 v; to_view(w, v);
			if (v.z >= -k_near) return false;
			s = view_to_screen(v);
			return std::isfinite(s.x) && std::isfinite(s.y);
		}

		void text(v3 w, ImU32 c, const char* t)
		{
			if (g_rec) g_rec->push_back({ 1, w, w, c, 0.f, t, {} });
			ImVec2 s;
			if (!point(w, s)) return;
			const ImVec2 sz = ImGui::CalcTextSize(t);
			g_view.dl->AddRectFilled(ImVec2(s.x - 2, s.y - 1), ImVec2(s.x + sz.x + 2, s.y + sz.y + 1), IM_COL32(0, 0, 0, 150));
			g_view.dl->AddText(s, c, t);
		}

		void poly_fill(const std::vector<v3>& p, ImU32 c)
		{
			if (g_rec) g_rec->push_back({ 2, {}, {}, c, 0.f, {}, p });
			if (p.size() < 3) return;
			std::vector<ImVec2> s(p.size());
			for (size_t i = 0; i < p.size(); ++i) if (!point(p[i], s[i])) return;   // skip if any corner is behind the camera
			g_view.dl->AddConvexPolyFilled(s.data(), (int)s.size(), c);
		}

		void poly_outline(const std::vector<v3>& p, ImU32 c, float thick)
		{
			for (size_t i = 0; i < p.size(); ++i) line(p[i], p[(i + 1) % p.size()], c, thick);
		}

		void box(v3 mn, v3 mx, ImU32 c, float thick)
		{
			auto k = [&](int i) { return v3{ (i & 1) ? mx.x : mn.x, (i & 2) ? mx.y : mn.y, (i & 4) ? mx.z : mn.z }; };
			static const int e[12][2] = { {0,1},{2,3},{4,5},{6,7},{0,2},{1,3},{4,6},{5,7},{0,4},{1,5},{2,6},{3,7} };
			for (const auto& p : e) line(k(p[0]), k(p[1]), c, thick);
		}

		struct s_capsule { v3 a, b; float r = 0; bool ok = false; };

		// The TIM as a measurement from the player: starts on the capsule surface facing the surface (along -n, n = the
		// cached separating normal pointing at the player) and runs the TIM's length - its end is where the TIM believes
		// the surface is. Labelled with the TIM in world units.
		void tim_measure(const s_capsule& cp, v3 n_to_player, float tim, ImU32 c, bool suspect);

		// wireframe capsule: 3 rings along the axis, 8 meridian lines, 2 cap arcs
		// Render-interpolation offset of the player being drawn: the physics capsule moves once per tick, the rendered
		// biped (and the camera) every frame. Everything attached to the player is drawn shifted by this so it rides
		// with the rendered character instead of stepping at 30 Hz. Physics measurements never use it.
		v3 g_pshift{ 0, 0, 0 };

		void capsule(const s_capsule& cp, v3 shift, ImU32 c, float thick)
		{
			const v3 a = cp.a + shift + g_pshift, b = cp.b + shift + g_pshift;
			v3 ax = b - a;
			const float L = len(ax);
			const v3 u = L > 1e-6f ? ax * (1.f / L) : v3{ 0, 0, 1 };
			const v3 h = std::fabs(u.z) < 0.9f ? v3{ 0, 0, 1 } : v3{ 1, 0, 0 };
			const v3 e1 = norm(cross(u, h)), e2 = cross(u, e1);
			const int N = 16;
			auto ring = [&](v3 cen, float r)
			{
				for (int i = 0; i < N; ++i)
				{
					const float t0 = 6.2831853f * i / N, t1 = 6.2831853f * (i + 1) / N;
					line(cen + (e1 * std::cos(t0) + e2 * std::sin(t0)) * r, cen + (e1 * std::cos(t1) + e2 * std::sin(t1)) * r, c, thick);
				}
			};
			ring(a, cp.r); ring(b, cp.r); ring((a + b) * 0.5f, cp.r);
			for (int i = 0; i < 8; ++i)
			{
				const float t = 6.2831853f * i / 8;
				const v3 o = (e1 * std::cos(t) + e2 * std::sin(t)) * cp.r;
				line(a + o, b + o, c, thick);
			}
			for (int s = 0; s < 2; ++s)   // hemispherical caps
			{
				const v3 cen = s ? b : a;
				const v3 dir = s ? u : u * -1.f;
				for (int m = 0; m < 4; ++m)    // 4 half-circles through the pole = 8 lines, matching the 8 body lines
				{
					const float ang = 3.14159265f * m / 4;
					const v3 side = e1 * std::cos(ang) + e2 * std::sin(ang);
					for (int i = 0; i < 8; ++i)
					{
						const float t0 = 3.14159265f * i / 8 - 1.5707963f, t1 = 3.14159265f * (i + 1) / 8 - 1.5707963f;
						const v3 p0 = cen + (side * std::sin(t0) + dir * std::cos(t0)) * cp.r;
						const v3 p1 = cen + (side * std::sin(t1) + dir * std::cos(t1)) * cp.r;
						line(p0, p1, c, thick);
					}
				}
			}
		}

		/* ---- Havok reads ---- */
		struct s_pair { uintptr_t ha, hb, agent; int32 S; };

		uintptr_t owner_of(uintptr_t handle) { return u32(handle + 0x10); }
		uintptr_t shape_of(uintptr_t handle) { return u32(handle - 0x10); }

		bool body_pose(uintptr_t handle, xform& out)
		{
			const uintptr_t ms = u32(handle - 0x10 + 8);
			float f[16];
			if (!okp(ms) || !rd(ms + 0x20, f, sizeof(f))) return false;
			for (int i = 0; i < 3; ++i)
			{
				out.c[i] = { f[i * 4], f[i * 4 + 1], f[i * 4 + 2] };
				const float l2 = dot(out.c[i], out.c[i]);
				if (!std::isfinite(l2) || l2 < 0.8f || l2 > 1.2f) return false;
			}
			out.t = { f[12], f[13], f[14] };
			return std::isfinite(f[12]) && std::isfinite(f[13]) && std::isfinite(f[14]);
		}

		// getType: vtable slot 5 is `mov eax, imm32 ; ret`
		// hkShape::getType (vtable +0x14). Most are "mov eax, imm32; ret" and are read straight from the code; anything
		// else (Halo's own shape classes can compute it) is called, guarded.
		// Only known shape classes are ever called into. Code is called only through these vtables: an arbitrary pointer
		// (the capsule search probes fields of a shape) could otherwise run some other object's method and corrupt the
		// game - which is what crashed it on crouch, when the biped's shape is swapped.
		bool is_shape(uintptr_t p)
		{
			static const uint32 k_shape_vtables[] = {
				0x3BA964, 0x3BA990, 0x3BA9F4, 0x3BAA3C, 0x3BAA84, 0x3BAAC8, 0x3BAB00, 0x3BAB34, 0x3BAB78, 0x3BABA4,
				0x3BABE8, 0x3BAC1C, 0x3BAC48, 0x3BAC7C, 0x3BACC4, 0x3BAD08, 0x3BAD34, 0x3BAD7C, 0x3BADC0, 0x3BADFC,
				0x3BAE44, 0x3BAE8C, 0x3BAED4, 0x3BC4E4, 0x3BCD70, 0x3C29FC, 0x3C2A34, 0x3C2A74, 0x3C2ABC, 0x3C2ECC,
				0x3C2F0C,
				0x3F0A40,   // Halo's convex sweep shape (type 23, no RTTI)
			};
			if (!okp(p)) return false;
			const uint32 rel = u32(p) - (uint32)Memory::GetAddress();
			for (uint32 v : k_shape_vtables) if (v == rel) return true;
			return false;
		}

		typedef int(__thiscall* t_get_type)(uintptr_t self);
		int call_get_type(uintptr_t fn, uintptr_t shape)
		{
			__try { return ((t_get_type)fn)(shape); }
			__except (EXCEPTION_EXECUTE_HANDLER) { return -1; }
		}
		int shape_type(uintptr_t shape)
		{
			if (!is_shape(shape)) return -1;
			const uintptr_t vt = u32(shape);
			if (!okp(vt)) return -1;
			const uintptr_t fn = u32(vt + 0x14);
			uint8 code[6];
			if (!rd(fn, code, sizeof(code))) return -1;
			if (code[0] == 0xB8 && code[5] == 0xC3) return (int)(code[1] | (code[2] << 8) | (code[3] << 16) | (code[4] << 24));
			if (code[0] == 0x33 && code[1] == 0xC0 && code[2] == 0xC3) return 0;      // xor eax, eax; ret
			const uintptr_t rel = fn - Memory::GetAddress();
			if (rel < 0x1000 || rel >= 0x39B000) return -1;                            // not game code
			const int r = call_get_type(fn, shape);
			return (r >= 0 && r < 64) ? r : -1;
		}

		// the biped's capsule in body space: the shape itself, or a capsule one level below it (sweep / transform wrappers)
		bool read_capsule(uintptr_t shape, s_capsule& out, int depth = 0)
		{
			if (!okp(shape)) return false;
			if (shape_type(shape) == 7)
			{
				out.r = f32(shape + 0x0C);
				if (!read_vec(shape + 0x10, out.a) || !read_vec(shape + 0x20, out.b)) return false;
				out.ok = out.r > 0.01f && out.r < 5.f;
				return out.ok;
			}
			if (depth >= 2) return false;
			for (uintptr_t off = 0x08; off <= 0x40; off += 4)
			{
				const uintptr_t child = u32(shape + off);
				if (child != shape && okp(child) && read_capsule(child, out, depth + 1)) return true;
			}
			return false;
		}

		void collect_islands(uintptr_t world, std::vector<uintptr_t>& out)
		{
			out.clear();
			// hkWorld keeps several island arrays (active, inactive/asleep, fixed): accept any {ptr, count} pair in the
			// first 0x60 bytes whose entries point back at the world (island+0x20), so sleeping islands are seen too
			for (uintptr_t off = 0x08; off <= 0x60; off += 4)
			{
				const uintptr_t arr = u32(world + off);
				const int32 n = i32(world + off + 4);
				if (!okp(arr) || n <= 0 || n > 2048) continue;
				std::vector<uint32> ptrs((size_t)n);
				if (!rd(arr, ptrs.data(), ptrs.size() * 4)) continue;
				for (uint32 p : ptrs)
					if (okp(p) && u32(p + 0x20) == world && std::find(out.begin(), out.end(), (uintptr_t)p) == out.end())
						out.push_back(p);
			}
		}

		void collect_pairs(const std::vector<uintptr_t>& islands, std::vector<s_pair>& out)
		{
			out.clear();
			for (uintptr_t isl : islands)
			{
				const uintptr_t arr = u32(isl + 0x68);
				const int32 n = i32(isl + 0x6C);
				if (!okp(arr) || n <= 0 || n > 8192) continue;
				std::vector<uint32> raw((size_t)n * 4);
				if (!rd(arr, raw.data(), raw.size() * 4)) continue;
				for (int32 i = 0; i < n; ++i)
					out.push_back({ raw[i * 4], raw[i * 4 + 1], raw[i * 4 + 2], (int32)raw[i * 4 + 3] });
			}
		}

		bool is_environment(uintptr_t handle, uintptr_t env_body)
		{
			if (env_body && owner_of(handle) == env_body) return true;
			const uintptr_t shape = shape_of(handle);
			return okp(shape) && u32(shape) == addr(k_vt_env_mopp);
		}

		struct s_child { uint32 key; uintptr_t agent; int32 manifold; v3 normal; float tim; };

		// Leaf agent (GSK / convex sweep) -> one TIM. layout: manifold +0x14, separating normal +0x20, TIM +0x2C
		bool read_leaf(uintptr_t agent, uint32 key, s_child& c)
		{
			const uint32 avt = u32(agent);
			if (avt != addr(k_vt_gsk) && avt != addr(k_vt_sweep) && avt != addr(k_vt_sweep_alt)) return false;
			uint8 g[0x24];
			if (!rd(agent + 0x0C, g, sizeof(g))) return false;
			c.key = key; c.agent = agent;
			c.manifold = *(const int32*)(g + 0x08);
			if (c.manifold < 0 || c.manifold > 16) c.manifold = 0;
			c.normal = { *(const float*)(g + 0x14), *(const float*)(g + 0x18), *(const float*)(g + 0x1C) };
			c.tim = *(const float*)(g + 0x20);
			return std::isfinite(c.tim);
		}

		// Children of a collection agent. The welder keeps {key, ?, agent} 12-byte entries at +0x0C (ptr) / +0x10 (count);
		// the MOPP / BV-tree / list agents share that base (same child-update code), so any agent with a sane array there
		// is walked, and a child that is itself a collection agent is walked one level further (keys from the deepest level).
		bool read_children(uintptr_t agent, std::vector<s_child>& out, std::string& diag, int depth = 0)
		{
			if (depth == 0) out.clear();
			const uint32 vt = u32(agent);
			s_child leaf{};
			if (read_leaf(agent, 0, leaf)) { if (depth == 0) diag = "pair agent is a single convex agent (no children)"; out.push_back(leaf); return true; }
			const uintptr_t arr = u32(agent + 0x0C);
			const int32 n = i32(agent + 0x10);
			if (depth == 0)
			{
				char d[160];
				snprintf(d, sizeof(d), "pair agent vtable %s+0x%X, %d entries", vt ? "halo2" : "?", (unsigned)(vt - Memory::GetAddress()), (int)n);
				diag = d;
			}
			if (n == 0) return true;
			if (!okp(arr) || n < 0 || n > 4096) return false;
			std::vector<uint32> raw((size_t)n * 3);
			if (!rd(arr, raw.data(), raw.size() * 4)) return false;
			const uintptr_t nul = addr(k_null_agent);
			int found = 0;
			static uint32 s_unknown[4]; static int s_unknown_n; static int s_unknown_total;
			if (depth == 0) { s_unknown_n = 0; s_unknown_total = 0; }
			for (int32 i = 0; i < n; ++i)
			{
				const uintptr_t ca = raw[i * 3 + 2];
				if (!okp(ca) || ca == nul) continue;
				s_child c{};
				if (read_leaf(ca, raw[i * 3], c)) { out.push_back(c); ++found; continue; }
				{
					const uint32 cvt = u32(ca) - (uint32)Memory::GetAddress();
					++s_unknown_total;
					bool seen = false;
					for (int k = 0; k < s_unknown_n; ++k) if (s_unknown[k] == cvt) seen = true;
					if (!seen && s_unknown_n < 4) s_unknown[s_unknown_n++] = cvt;
				}
				if (depth < 2)
				{
					std::string sub;
					const size_t before = out.size();
					read_children(ca, out, sub, depth + 1);
					found += (int)(out.size() - before);
				}
			}
			if (depth == 0)
			{
				char d[200]; snprintf(d, sizeof(d), ", %d TIM leaves, %d other children", found, s_unknown_total);
				diag += d;
				for (int k = 0; k < s_unknown_n; ++k) { snprintf(d, sizeof(d), " [vt +0x%X]", (unsigned)s_unknown[k]); diag += d; }
			}
			return found > 0 || n > 0;
		}

		/* ---- level polygons (Cartographer's typed tag blocks) ---- */
		bool bsp_polygon(const collision_bsp* bsp, uint32 s, std::vector<v3>& out)
		{
			out.clear();
			if (!bsp || (int32)s >= bsp->surfaces.count) return false;
			const collision_surface* surf = bsp->surfaces[s];
			uint32 e = surf->first_edge;
			const uint32 start = e;
			for (int guard = 0; guard < 16; ++guard)
			{
				if ((int32)e >= bsp->edges.count) return false;
				const collision_edge* ed = bsp->edges[e];
				uint32 v, next;
				if (ed->right_surface == s) { v = ed->end_vertex; next = ed->reverse_edge; }
				else { v = ed->start_vertex; next = ed->forward_edge; }
				if ((int32)v >= bsp->vertices.count) return false;
				const real_point3d& p = bsp->vertices[v]->point;
				out.push_back({ p.x, p.y, p.z });
				e = next;
				if (e == start) return out.size() >= 3;
			}
			return false;
		}

		bool key_polygon(uint32 key, std::vector<v3>& out)
		{
			const structure_bsp* sbsp = global_structure_bsp_get();
			if (!sbsp) return false;
			const uint32 cat = key >> 29;
			if (cat == 1)
			{
				if (sbsp->collision.count < 1) return false;
				return bsp_polygon(sbsp->collision[0], key & 0xFFFF, out);
			}
			if (cat == 5)
			{
				const uint32 inst = key & 0xFFFF, surf = (key >> 16) & 0x1FFF;
				if ((int32)inst >= sbsp->instanced_geometry_instances.count) return false;
				const structure_instanced_geometry_instance* in = sbsp->instanced_geometry_instances[inst];
				if ((int32)in->instance_definition >= sbsp->instanced_geometry_definitions.count) return false;
				const structure_instanced_geometry_definition* def = sbsp->instanced_geometry_definitions[in->instance_definition];
				if (!bsp_polygon(&def->collision_info, surf, out)) return false;
				const float* m = (const float*)&in->transform;   // forward, left, up (3 x 3)
				const float sc = in->scale;
				for (v3& p : out)
				{
					const v3 f{ m[0], m[1], m[2] }, l{ m[3], m[4], m[5] }, u{ m[6], m[7], m[8] };
					p = v3{ in->position.x, in->position.y, in->position.z } + (f * p.x + l * p.y + u * p.z) * sc;
				}
				return true;
			}
			return false;
		}

		/* ---- objects (rigid bodies paired with the player: crates, machines, doors, vehicles, other bipeds) ----
		   Shapes are walked together with the agent tree:
		     transform (21): child +0x0C, hkTransform +0x10 (rotation columns +0x10/+0x20/+0x30, translation +0x40);
		                     its agent keeps the child agent at +0x0C (hkTransformAgent)
		     MOPP (19):      child collection +0x0C
		     collections (2 Halo collision geometry, 10 list, ...): child shapes through the game's own
		                     getChildShape (vtable +0x34, thiscall (key, buffer)); the agent's children are either
		                     {key, ?, agent} 12-byte entries (welder / MOPP / BV-tree) or agent pointers by index (list)
		     convex leaves (4 sphere, 5 triangle, 6 box, 7 capsule, 8 convex vertices, 9 multi-sphere, 24 Halo
		                     collision-surface polygon): distance by GJK on the game's own getSupportingVertex
		                     (vtable +0x30, thiscall (dir, out)) minus the convex radius (+0x0C).
		   getAabb is vtable +0x18, thiscall (transform, tolerance, out). */
		typedef void(__thiscall* t_support)(uintptr_t self, const float* dir, float* out);
		typedef uintptr_t(__thiscall* t_child_shape)(uintptr_t self, uint32 key, void* buffer);
		typedef void(__thiscall* t_get_aabb)(uintptr_t self, const float* xf, float tolerance, float* out);

		bool call_support(uintptr_t shape, const float* dir16, float* out16)
		{
			if (!is_shape(shape)) return false;
			const uintptr_t fn = u32(u32(shape) + 0x30);
			if (!okfn(fn)) return false;
			__try { ((t_support)fn)(shape, dir16, out16); return true; }
			__except (EXCEPTION_EXECUTE_HANDLER) { return false; }
		}
		uintptr_t call_child_shape(uintptr_t collection, uint32 key, void* buffer)
		{
			if (!is_shape(collection)) return 0;
			const uintptr_t fn = u32(u32(collection) + 0x34);
			if (!okfn(fn)) return 0;
			__try { return ((t_child_shape)fn)(collection, key, buffer); }
			__except (EXCEPTION_EXECUTE_HANDLER) { return 0; }
		}
		bool call_get_aabb(uintptr_t shape, const float* xf16, float* out8)
		{
			if (!is_shape(shape)) return false;
			const uintptr_t fn = u32(u32(shape) + 0x18);
			if (!okfn(fn)) return false;
			__try { ((t_get_aabb)fn)(shape, xf16, 0.f, out8); return true; }
			__except (EXCEPTION_EXECUTE_HANDLER) { return false; }
		}

		// 23 = Halo's convex sweep shape (vtable 0x3F0A40): a convex wrapper around a child (+0x30) extended by a sweep
		// vector (+0x10); its getSupportingVertex / getAabb are the swept volume the sweep agent actually tests against
		bool is_convex_type(int t) { return t == 4 || t == 5 || t == 6 || t == 7 || t == 8 || t == 9 || t == 23 || t == 24; }

		// world support point of a convex shape under transform x
		bool support_world(uintptr_t shape, const xform& x, v3 dw, v3& out)
		{
			alignas(16) float d[4] = { dot(dw, x.c[0]), dot(dw, x.c[1]), dot(dw, x.c[2]), 0.f };
			alignas(16) float o[4] = {};
			if (!call_support(shape, d, o)) return false;
			out = xf_point(x, v3{ o[0], o[1], o[2] });
			return std::isfinite(out.x) && std::isfinite(out.y) && std::isfinite(out.z);
		}

		// closest point to the origin on a simplex (1..4 points); reduces the simplex to the supporting feature
		v3 closest_on_simplex(std::vector<v3>& s)
		{
			auto seg = [](v3 a, v3 b, float& t) { const v3 ab = b - a; const float l2 = dot(ab, ab); t = l2 > 1e-20f ? clampf(-dot(a, ab) / l2, 0.f, 1.f) : 0.f; return a + ab * t; };
			auto tri = [&](v3 a, v3 b, v3 c, std::vector<v3>& keep) -> v3
			{   // Ericson 5.1.5 with the origin as the query point
				const v3 ab = b - a, ac = c - a, ap = a * -1.f;
				const float d1 = dot(ab, ap), d2 = dot(ac, ap);
				if (d1 <= 0 && d2 <= 0) { keep = { a }; return a; }
				const v3 bp = b * -1.f; const float d3 = dot(ab, bp), d4 = dot(ac, bp);
				if (d3 >= 0 && d4 <= d3) { keep = { b }; return b; }
				const float vc = d1 * d4 - d3 * d2;
				if (vc <= 0 && d1 >= 0 && d3 <= 0) { keep = { a, b }; return a + ab * (d1 / (d1 - d3)); }
				const v3 cp = c * -1.f; const float d5 = dot(ab, cp), d6 = dot(ac, cp);
				if (d6 >= 0 && d5 <= d6) { keep = { c }; return c; }
				const float vb = d5 * d2 - d1 * d6;
				if (vb <= 0 && d2 >= 0 && d6 <= 0) { keep = { a, c }; return a + ac * (d2 / (d2 - d6)); }
				const float va = d3 * d6 - d5 * d4;
				if (va <= 0 && (d4 - d3) >= 0 && (d5 - d6) >= 0) { keep = { b, c }; return b + (c - b) * ((d4 - d3) / ((d4 - d3) + (d5 - d6))); }
				const float den = 1.f / (va + vb + vc);
				keep = { a, b, c };
				return a + ab * (vb * den) + ac * (vc * den);
			};
			if (s.size() == 1) return s[0];
			if (s.size() == 2)
			{
				float t; const v3 p = seg(s[0], s[1], t);
				if (t <= 0) s = { s[0] }; else if (t >= 1) s = { s[1] };
				return p;
			}
			if (s.size() == 3) { std::vector<v3> keep; const v3 p = tri(s[0], s[1], s[2], keep); s = keep; return p; }
			// tetrahedron: origin inside -> distance 0, else the closest face
			const int faces[4][4] = { {0,1,2,3}, {0,1,3,2}, {0,2,3,1}, {1,2,3,0} };
			float best = 1e30f; v3 bp{}; std::vector<v3> bk; bool inside = true;
			for (const auto& f : faces)
			{
				const v3 a = s[f[0]], b = s[f[1]], c = s[f[2]], d = s[f[3]];
				const v3 n = cross(b - a, c - a);
				const float so = dot(a * -1.f, n), sd = dot(d - a, n);
				if (so * sd < 0)
				{
					inside = false;
					std::vector<v3> keep; const v3 p = tri(a, b, c, keep);
					if (dot(p, p) < best) { best = dot(p, p); bp = p; bk = keep; }
				}
			}
			if (inside) return v3{ 0, 0, 0 };
			s = bk; return bp;
		}

		// distance between the capsule core segment [a,b] and a convex shape (core, radii not subtracted); -1 on failure
		float gjk_segment_convex(v3 a, v3 b, uintptr_t shape, const xform& x)
		{
			auto sup = [&](v3 d, v3& w) -> bool
			{
				const v3 pa = dot(a, d) >= dot(b, d) ? a : b;
				v3 pb;
				if (!support_world(shape, x, d * -1.f, pb)) return false;
				w = pa - pb;
				return true;
			};
			v3 w;
			if (!sup(v3{ 1, 0, 0 }, w)) return -1.f;
			std::vector<v3> s{ w };
			v3 v = w;
			for (int it = 0; it < 32; ++it)
			{
				const float vv = dot(v, v);
				if (vv < 1e-12f) return 0.f;
				if (!sup(v * -1.f, w)) return -1.f;
				if (vv - dot(v, w) <= 1e-6f * vv + 1e-9f) break;    // no more progress
				s.push_back(w);
				v = closest_on_simplex(s);
				if (s.size() == 4 && dot(v, v) < 1e-12f) return 0.f;
			}
			return len(v);
		}

		struct s_obj_leaf { uint32 key; uintptr_t agent; uintptr_t shape; int type; xform x; s_child tim; v3 mn, mx; float gap;
			std::vector<v3> segs; std::vector<s_capsule> caps;   // the piece's real outline in world space
			// pass-through geometry, along the TIM normal n (pointing at the player): the piece's near face, centre plane
			// and far face, and its extent across n in two directions (to tell whether moving along -n reaches it at all)
			bool pass_ok = false; v3 pass_n{}, pass_u1{}, pass_u2{}; float near_n = 0, mid_n = 0, far_n = 0, u1_lo = 0, u1_hi = 0, u2_lo = 0, u2_hi = 0; };

		// The piece's actual shape as world-space line segments (built at walk time: a child shape returned through a
		// getChildShape buffer is only valid until the next call).
		//   23 sweep -> its child (+0x30); 21 transform -> child (+0x0C) under +0x10; 6 box: half extents +0x10 (+ radius);
		//   7 capsule: ends +0x10 / +0x20, radius +0x0C; 4 sphere: radius +0x0C; 5 triangle: vertices +0x10/+0x20/+0x30;
		//   anything else convex: its oriented extent box from six local support points.
		void outline_shape(uintptr_t shape, const xform& x, std::vector<v3>& segs, std::vector<s_capsule>& caps, int depth = 0);

		xform xf_compose(const xform& p, const xform& c)
		{
			xform r;
			for (int i = 0; i < 3; ++i) r.c[i] = p.c[0] * c.c[i].x + p.c[1] * c.c[i].y + p.c[2] * c.c[i].z;
			r.t = xf_point(p, c.t);
			return r;
		}

		bool agent_like(uintptr_t p)
		{
			if (!okp(p)) return false;
			const uintptr_t vt = u32(p);
			const uintptr_t rel = vt - Memory::GetAddress();
			return rel >= 0x39B000 && rel < 0x411000;     // a vtable in the game's .rdata
		}

		int g_obj_skip_type = -1; uint32 g_obj_skip_vt = 0;   // last shape type a convex agent was found on but could not be measured (diagnostics)
		std::map<uintptr_t, int> g_obj_side; std::map<uintptr_t, uint32> g_obj_side_seen; uint32 g_obj_side_frame = 0;   // pass-through side per object TIM agent

		void oriented_box(const xform& x, v3 lmn, v3 lmx, std::vector<v3>& segs)
		{
			auto k = [&](int i) { return xf_point(x, v3{ (i & 1) ? lmx.x : lmn.x, (i & 2) ? lmx.y : lmn.y, (i & 4) ? lmx.z : lmn.z }); };
			static const int e[12][2] = { {0,1},{2,3},{4,5},{6,7},{0,2},{1,3},{4,6},{5,7},{0,4},{1,5},{2,6},{3,7} };
			for (const auto& p : e) { segs.push_back(k(p[0])); segs.push_back(k(p[1])); }
		}

		void outline_shape(uintptr_t shape, const xform& x, std::vector<v3>& segs, std::vector<s_capsule>& caps, int depth)
		{
			if (depth > 4 || !okp(shape)) return;
			const int t = shape_type(shape);
			const float r = f32(shape + 0x0C);
			switch (t)
			{
			case 23: outline_shape(u32(shape + 0x30), x, segs, caps, depth + 1); return;
			case 21:
			{
				float f[16];
				if (!rd(shape + 0x10, f, sizeof(f))) return;
				xform T; T.c[0] = { f[0], f[1], f[2] }; T.c[1] = { f[4], f[5], f[6] }; T.c[2] = { f[8], f[9], f[10] }; T.t = { f[12], f[13], f[14] };
				outline_shape(u32(shape + 0x0C), xf_compose(x, T), segs, caps, depth + 1);
				return;
			}
			case 6:
			{
				v3 he;
				if (!read_vec(shape + 0x10, he)) return;
				const float rr = (r >= 0 && r < 1.f) ? r : 0.f;
				he = he + v3{ rr, rr, rr };
				oriented_box(x, he * -1.f, he, segs);
				return;
			}
			case 7:
			{
				s_capsule c; v3 a, b;
				if (!read_vec(shape + 0x10, a) || !read_vec(shape + 0x20, b)) return;
				c.a = xf_point(x, a); c.b = xf_point(x, b); c.r = r; c.ok = r > 0 && r < 10.f;
				if (c.ok) caps.push_back(c);
				return;
			}
			case 4:
			{
				s_capsule c; c.a = c.b = x.t; c.r = r; c.ok = r > 0 && r < 10.f;
				if (c.ok) caps.push_back(c);
				return;
			}
			case 5:
			{
				v3 v[3];
				if (!read_vec(shape + 0x10, v[0]) || !read_vec(shape + 0x20, v[1]) || !read_vec(shape + 0x30, v[2])) return;
				for (int i = 0; i < 3; ++i) { segs.push_back(xf_point(x, v[i])); segs.push_back(xf_point(x, v[(i + 1) % 3])); }
				return;
			}
			default:
			{
				if (!is_convex_type(t)) return;
				xform id; id.c[0] = { 1, 0, 0 }; id.c[1] = { 0, 1, 0 }; id.c[2] = { 0, 0, 1 }; id.t = { 0, 0, 0 };
				v3 px, nx, py, ny, pz, nz;
				if (!support_world(shape, id, { 1, 0, 0 }, px) || !support_world(shape, id, { -1, 0, 0 }, nx) || !support_world(shape, id, { 0, 1, 0 }, py) ||
					!support_world(shape, id, { 0, -1, 0 }, ny) || !support_world(shape, id, { 0, 0, 1 }, pz) || !support_world(shape, id, { 0, 0, -1 }, nz)) return;
				const float rr = (r >= 0 && r < 1.f) ? r : 0.f;
				oriented_box(x, v3{ nx.x - rr, ny.y - rr, nz.z - rr }, v3{ px.x + rr, py.y + rr, pz.z + rr }, segs);
				return;
			}
			}
		}

		void walk_object(uintptr_t agent, uintptr_t shape, const xform& x, v3 cap_a, v3 cap_b, float cap_r,
			std::vector<s_obj_leaf>& out, int depth, int& skipped)
		{
			if (depth > 6 || !okp(shape) || out.size() > 256) return;
			const int t = shape_type(shape);
			s_child leaf{};
			if (okp(agent) && read_leaf(agent, 0, leaf))
			{
				if (t == 21)   // a convex agent over a transformed shape: the agent works on the child in the transformed frame
				{
					float f[16];
					if (!rd(shape + 0x10, f, sizeof(f))) { ++skipped; return; }
					xform T; T.c[0] = { f[0], f[1], f[2] }; T.c[1] = { f[4], f[5], f[6] }; T.c[2] = { f[8], f[9], f[10] }; T.t = { f[12], f[13], f[14] };
					walk_object(agent, u32(shape + 0x0C), xf_compose(x, T), cap_a, cap_b, cap_r, out, depth + 1, skipped);
					return;
				}
				if (!is_convex_type(t)) { ++skipped; g_obj_skip_type = t; g_obj_skip_vt = u32(shape) - (uint32)Memory::GetAddress(); return; }
				s_obj_leaf l{}; l.agent = agent; l.shape = shape; l.type = t; l.x = x; l.tim = leaf;
				const float core = gjk_segment_convex(cap_a, cap_b, shape, x);
				l.gap = core < 0 ? 1e9f : core - cap_r - f32(shape + 0x0C);
				alignas(16) float xf16[16] = { x.c[0].x, x.c[0].y, x.c[0].z, 0, x.c[1].x, x.c[1].y, x.c[1].z, 0, x.c[2].x, x.c[2].y, x.c[2].z, 0, x.t.x, x.t.y, x.t.z, 1 };
				alignas(16) float bb[8] = {};
				if (call_get_aabb(shape, xf16, bb) && bb[0] <= bb[4] && bb[1] <= bb[5] && bb[2] <= bb[6]) { l.mn = { bb[0], bb[1], bb[2] }; l.mx = { bb[4], bb[5], bb[6] }; }
				else
				{   // fallback: the box from six support points plus the convex radius
					const float r = f32(shape + 0x0C);
					v3 px, nx, py, ny, pz, nz;
					if (support_world(shape, x, { 1, 0, 0 }, px) && support_world(shape, x, { -1, 0, 0 }, nx) && support_world(shape, x, { 0, 1, 0 }, py) &&
						support_world(shape, x, { 0, -1, 0 }, ny) && support_world(shape, x, { 0, 0, 1 }, pz) && support_world(shape, x, { 0, 0, -1 }, nz))
					{
						l.mn = { nx.x - r, ny.y - r, nz.z - r }; l.mx = { px.x + r, py.y + r, pz.z + r };
					}
					else { l.mn = l.mx = x.t; }
				}
				outline_shape(shape, x, l.segs, l.caps);
				if (len(l.tim.normal) > 0.5f)
				{
					const v3 pmid = (cap_a + cap_b) * 0.5f, pc = (l.mn + l.mx) * 0.5f;
					v3 n = norm(l.tim.normal);
					{
						auto it = g_obj_side.find(agent);
						if (it == g_obj_side.end()) it = g_obj_side.emplace(agent, dot(n, pmid - pc) < 0 ? -1 : 1).first;
						if (it->second < 0) n = n * -1.f;
						g_obj_side_seen[agent] = g_obj_side_frame;
					}
					const v3 h = std::fabs(n.z) < 0.9f ? v3{ 0, 0, 1 } : v3{ 1, 0, 0 };
					const v3 u1 = norm(cross(n, h)), u2 = norm(cross(n, u1));
					const float r = f32(shape + 0x0C);
					const float rr = (r >= 0 && r < 1.f) ? r : 0.f;
					v3 sp, sm, a1, b1, a2, b2;
					if (support_world(shape, x, n, sp) && support_world(shape, x, n * -1.f, sm) && support_world(shape, x, u1, a1) &&
						support_world(shape, x, u1 * -1.f, b1) && support_world(shape, x, u2, a2) && support_world(shape, x, u2 * -1.f, b2))
					{
						l.pass_ok = true; l.pass_n = n; l.pass_u1 = u1; l.pass_u2 = u2;
						l.near_n = dot(sp, n) + rr; l.far_n = dot(sm, n) - rr; l.mid_n = (l.near_n + l.far_n) * 0.5f;
						l.u1_hi = dot(a1, u1) + rr; l.u1_lo = dot(b1, u1) - rr; l.u2_hi = dot(a2, u2) + rr; l.u2_lo = dot(b2, u2) - rr;
					}
				}
				out.push_back(l);
				return;
			}
			if (t == 21)   // transform
			{
				float f[16];
				if (!rd(shape + 0x10, f, sizeof(f))) return;
				xform T; T.c[0] = { f[0], f[1], f[2] }; T.c[1] = { f[4], f[5], f[6] }; T.c[2] = { f[8], f[9], f[10] }; T.t = { f[12], f[13], f[14] };
				const uintptr_t child_agent = agent_like(u32(agent + 0x0C)) ? u32(agent + 0x0C) : agent;
				walk_object(child_agent, u32(shape + 0x0C), xf_compose(x, T), cap_a, cap_b, cap_r, out, depth + 1, skipped);
				return;
			}
			uintptr_t collection = shape;
			if (t == 19 || t == 3) collection = u32(shape + 0x0C);   // MOPP / BV tree -> its collection
			if (!okp(collection) || !okp(agent)) { ++skipped; g_obj_skip_type = t; return; }
			const uintptr_t arr = u32(agent + 0x0C);
			const int32 n = i32(agent + 0x10);
			if (!okp(arr) || n <= 0 || n > 1024) return;
			// keyed {key, ?, agent} entries (welder / MOPP / BV tree) or agent pointers by index (list)?
			std::vector<uint32> raw((size_t)n * 3);
			const bool have12 = rd(arr, raw.data(), raw.size() * 4);
			int good12 = 0, good4 = 0;
			for (int32 i = 0; i < (std::min)(n, (int32)4); ++i)
			{
				if (have12 && agent_like(raw[i * 3 + 2])) ++good12;
				if (agent_like(u32(arr + 4 * (uintptr_t)i))) ++good4;
			}
			const bool keyed = have12 && good12 >= good4;
			alignas(16) uint8 buffer[1024];
			for (int32 i = 0; i < n; ++i)
			{
				const uint32 key = keyed ? raw[i * 3] : (uint32)i;
				const uintptr_t ca = keyed ? raw[i * 3 + 2] : u32(arr + 4 * (uintptr_t)i);
				if (!agent_like(ca) || ca == addr(k_null_agent)) continue;
				const uintptr_t child = call_child_shape(collection, key, buffer);
				if (!okp(child)) { ++skipped; g_obj_skip_type = -2; continue; }   // -2: getChildShape gave nothing
				const size_t before = out.size();
				walk_object(ca, child, x, cap_a, cap_b, cap_r, out, depth + 1, skipped);
				for (size_t j = before; j < out.size(); ++j) out[j].key = key;
				// a child built in `buffer` is only valid until the next call: its leaves are already measured
			}
		}

		struct s_obj_believed { float over; v3 dir; uintptr_t key = 0; v3 at{}; };   // key: the object's TIM agent; at: capsule centre when read

		/* ---- pass-through prediction ----
		   The TIM is the distance the engine lets you move toward a surface along its cached normal n before it looks at
		   that surface again (each step spends n . dp of it). Moving straight in along -n, the check comes when your
		   capsule centre has travelled TIM: centre' = centre - n * TIM. If centre' is already past the surface's middle
		   (a polygon's plane; a convex piece's centre plane along n), the penetration found at that check is resolved
		   out the FAR side - you pass through. If centre' is short of the middle, you are pushed back out (the red
		   reset sheet comes before the centre). So, along n:
		       margin = middle - (centre . n - TIM)        pass-through when margin > 0
		   Where the surface is relative to you does not matter - only its plane / centre plane along n and your TIM.
		   Thicker pieces and pieces seen at an angle need more TIM - this is that rule. */
		float pulse_alpha() { const float s = 0.5f + 0.5f * std::sin((float)ImGui::GetTime() * 9.f); return 0.35f + 0.65f * s; }

		/* ---- per-player state ---- */
		void tim_measure(const s_capsule& cp, v3 n_to_player, float tim, ImU32 c, bool suspect)
		{
			if (!(tim > 0) || len(n_to_player) < 0.5f) return;
			const v3 dn = norm(n_to_player) * -1.f;                     // toward the surface
			const v3 core = dot(cp.a, dn) >= dot(cp.b, dn) ? cp.a : cp.b;
			const v3 s = core + dn * cp.r + g_pshift, e = s + dn * tim;
			line(s, e, c, 1.6f);
			// end tick, perpendicular to the line
			const v3 h = std::fabs(dn.z) < 0.9f ? v3{ 0, 0, 1 } : v3{ 1, 0, 0 };
			const v3 side = norm(cross(dn, h)) * 0.03f;
			line(e - side, e + side, c, 1.6f);
			char t[40];
			snprintf(t, sizeof(t), "%.3f%s", tim, suspect ? "!" : "");
			text(e, c, t);
		}

		/* ---- offset save state ----
		   Save: snapshot every skipped TIM the player holds (level polygons by key, object pieces by shape + position + key),
		   set the game's own checkpoint flag (0x482250, the same byte HCM's Force Checkpoint sets in MCC), and once the
		   checkpoint has rebuilt the player's pairs (new level welder) write the snapshot back. Load: set the revert flag
		   (0x48224F), wait for the pairs, check the player is where the snapshot was taken, write the TIMs back.
		   Written per pair: the cached separating normal (+0x20) and the TIM (+0x2C); never pairs in contact. */
		// out-of-bounds / kill volume death bar state (see update_death_state)
		struct s_death_state
		{
			bool valid = false;
			int oob_counter = 0, oob_limit = 15, oob_next_check = 0, player_index = 0;
			int kv_count = 0, kv_enabled = 0, kv_checking = -1;
			std::vector<std::pair<int, int>> kv_inside;      // (kill volume, ticks until its turn)
			float bar = -1.f; char text[64] = {};
		};
		s_death_state g_death;
		struct s_offset_entry { bool obj; uint64_t id; v3 normal; float tim; };
		enum e_offset_phase { _offset_idle, _offset_wait, _offset_apply };
		int g_offset_req = 0;                 // 1 save, 2 load (GUI button / hotkey, render thread)
		std::string g_offset_status;          // panel line
		double g_toast_until = 0; std::string g_toast;
		void offset_toast(const std::string& s) { g_offset_status = s; g_toast = s; g_toast_until = ImGui::GetTime() + 3.5; }
		constexpr uintptr_t k_checkpoint_flag = 0x482250, k_revert_flag = 0x48224F;   // halo2.exe image offsets (byte flags)

		// object piece identity that survives a revert (the Havok objects are rebuilt, the Halo objects come back in place)
		uint64_t piece_id(int type, v3 mn, v3 mx, uint32 key)
		{
			const v3 c = (mn + mx) * 0.5f;
			auto q = [](float f) { return (uint64_t)(int64_t)std::lround(f * 64.f) & 0xFFFFF; };
			return (q(c.x) << 44) ^ (q(c.y) << 24) ^ (q(c.z) << 4) ^ ((uint64_t)(type & 0xF)) ^ ((uint64_t)key * 0x9E3779B97F4A7C15ull);
		}

		// kept outside the per-player state: that is cleared whenever the physics world is rebuilt (a revert can do that)
		struct s_offset_state
		{
			bool valid = false; v3 pos{}; std::vector<s_offset_entry> saved;
			int phase = _offset_idle; bool is_load = false; uintptr_t old_agent = 0; int frames = 0, restored = 0;
			std::vector<bool> done;
			uint32 save_tick = 0, req_tick = 0, last_tick = 0;   // game ticks: when saved / when Load was pressed / last frame
		};
		s_offset_state g_offset[4];
		int g_offset_user = 0;               // offsets are saved / loaded for the first local player

		struct s_player_state
		{
			uint32 last_tick = 0, last_backstep_tick = 0, rewind_tick = 0;
			bool have = false, ever_backstep = false, have_rewind = false;
			v3 last_cur{}, rewind_from{}, rewind_to{};
			float rewind_dist = 0, t_star = 0;
			s_capsule cap_local{}; bool have_cap = false; ImU32 last_pill = 0;   // the pill keeps drawing when the pair list goes quiet
			// offsets kept while their pairs are asleep (unreadable) and the player has not moved; replaced as soon as they read again
			std::vector<s_obj_believed> kept_obj, kept_level;
			int crouch = -1;   // last crouch state: changing stance swaps the biped's shape, which resets its TIMs
			float crouch_amount = -1.f;
			s_capsule cap_stand{}, cap_crouch{}; bool have_stand = false, have_crouch = false;   // body-space capsule per stance
			v3 pill_pos{}; datum pill_unit = NONE; bool was_live = false;
			std::map<uint32, int> pass_side; std::map<uint32, uint32> pass_seen; uint32 frame_no = 0;   // per-TIM side, kept while it lives
			std::vector<s_prim> last_live_prims; uint32 last_live_tick = 0; bool have_last_live = false;
		};
		s_player_state g_players[4];

		struct s_info
		{
			bool valid = false; int32 user = 0;
			std::string note, diag, diag2, diag3;
			int32 S = 0, children = 0, skipped = 0, contacts = 0, suspect = 0, believed = 0;
			int32 weld_near = 0, weld_welded = 0, obj_believed_kept = 0, obj_unmeasured = 0;
			int32 pass_level = 0, pass_obj = 0; float pass_best = 0.f;
			std::vector<std::string> pass_rows;   // per offset polygon: the pass-through numbers
			std::vector<std::string> obj_diag;
			int32 obj_lines = 0;
			int32 obj_pairs = 0, obj_leaves = 0, obj_unread = 0, obj_suspect = 0, obj_believed = 0; float obj_max_over = 0;
			float max_over = 0;
			std::vector<std::string> travel;
			bool rewind = false; float rewind_dist = 0, t_star = 0; int32 rewind_age = 0;
		};
		s_info g_info[4];
		s_info g_last_info[4];   // the last live frame's panel rows (bridged over a pair blink)

		struct s_believed { float over; v3 dir; };
		struct s_travel { uint32 key; v3 n; float tim, over; std::vector<v3> poly; v3 pmn, pmx; bool object = false; };

		/* ---- desync logger (CSV next to halo2.exe: GhostViewerLog.csv) ---- */
		FILE* g_log = nullptr;
		struct s_log_state { std::map<uint64_t, float> active; };   // key -> max over-credit while the episode lasts
		s_log_state g_log_state[4];
		void log_line(const char* fmt, ...)
		{
			if (!g_settings.logger) return;
			if (!g_log)
			{
				if (fopen_s(&g_log, "GhostViewerLog.csv", "a") != 0 || !g_log) { g_log = nullptr; return; }
				fprintf(g_log, "tick,player,event,kind,key,tim,over_credit,detail\n");
			}
			va_list va; va_start(va, fmt); vfprintf(g_log, fmt, va); va_end(va);
			fputc('\n', g_log);
			fflush(g_log);
		}
		// over-credit episodes: start when a TIM first goes suspect, end (with its peak) when it stops being suspect
		void log_episodes(int32 user, uint32 tick, const std::map<uint64_t, std::pair<float, float>>& now, const char* const* kinds)
		{
			if (!g_settings.logger) { g_log_state[user].active.clear(); return; }
			auto& act = g_log_state[user].active;
			for (const auto& e : now)
			{
				auto it = act.find(e.first);
				const char* kind = kinds[(e.first >> 63) ? 1 : 0];
				if (it == act.end())
				{
					act[e.first] = e.second.second;
					log_line("%u,%d,overcredit_start,%s,0x%llX,%.4f,%.4f,", tick, (int)user + 1, kind, (unsigned long long)(e.first & 0x7FFFFFFFFFFFFFFFull), e.second.first, e.second.second);
				}
				else it->second = (std::max)(it->second, e.second.second);
			}
			for (auto it = act.begin(); it != act.end();)
			{
				if (now.find(it->first) == now.end())
				{
					const char* kind = kinds[(it->first >> 63) ? 1 : 0];
					log_line("%u,%d,overcredit_end,%s,0x%llX,,%.4f,peak", tick, (int)user + 1, kind, (unsigned long long)(it->first & 0x7FFFFFFFFFFFFFFFull), it->second);
					it = act.erase(it);
				}
				else ++it;
			}
		}

		/* ---- weld zones: every level polygon's box, cached per structure bsp ---- */
		struct s_zone_cache { const void* bsp = nullptr; std::vector<v3> mn, mx; };
		s_zone_cache g_zones;
		void build_zone_cache()
		{
			const structure_bsp* sbsp = global_structure_bsp_get();
			if (!sbsp || sbsp->collision.count < 1) { g_zones = s_zone_cache{}; return; }
			const collision_bsp* bsp = sbsp->collision[0];
			if (g_zones.bsp == bsp && !g_zones.mn.empty()) return;
			g_zones = s_zone_cache{}; g_zones.bsp = bsp;
			const int32 n = (std::min)(bsp->surfaces.count, (int32)65535);
			g_zones.mn.resize((size_t)n); g_zones.mx.resize((size_t)n);
			std::vector<v3> poly;
			for (int32 s = 0; s < n; ++s)
			{
				v3 a{ 1e30f, 1e30f, 1e30f }, b{ -1e30f, -1e30f, -1e30f };
				if (bsp_polygon(bsp, (uint32)s, poly))
					for (const v3& p : poly)
					{
						a = { (std::min)(a.x, p.x), (std::min)(a.y, p.y), (std::min)(a.z, p.z) };
						b = { (std::max)(b.x, p.x), (std::max)(b.y, p.y), (std::max)(b.z, p.z) };
					}
				g_zones.mn[(size_t)s] = a; g_zones.mx[(size_t)s] = b;
			}
		}
		float box_dist(v3 p, v3 mn, v3 mx)
		{
			const float dx = (std::max)({ mn.x - p.x, 0.f, p.x - mx.x }), dy = (std::max)({ mn.y - p.y, 0.f, p.y - mx.y }), dz = (std::max)({ mn.z - p.z, 0.f, p.z - mx.z });
			return std::sqrt(dx * dx + dy * dy + dz * dz);
		}

		// The unit's own rigid bodies, straight from its Havok component (no pair needed, so it works at rest):
		//   object +0xB4 = havok component datum; components are 0xA0-byte elements of havok_components_get();
		//   component +0x70 / +0x74 = rigid body entries (0x60 bytes each), entry +0x40 = the hkRigidBody (entity),
		//   entity +0x3C = motion (as used by halo2 0x4DCA67).
		// The handle used everywhere else (shape at handle-0x10, owner at handle+0x10) sits at a fixed offset inside the
		// entity; it is found once by its back-pointer and cached.
		int32 g_handle_offset = -1;
		uintptr_t handle_in_entity(uintptr_t entity)
		{
			if (!okp(entity)) return 0;
			if (g_handle_offset >= 0)
			{
				const uintptr_t h = entity + (uintptr_t)g_handle_offset;
				if (u32(h + 0x10) == entity && is_shape(u32(h - 0x10))) return h;
			}
			for (int32 off = 0x10; off <= 0x80; off += 4)
			{
				const uintptr_t h = entity + (uintptr_t)off;
				if (u32(h + 0x10) == entity && is_shape(u32(h - 0x10))) { g_handle_offset = off; return h; }
			}
			return 0;
		}
		uintptr_t unit_body_handle(datum unit)
		{
			const uintptr_t obj = (uintptr_t)object_try_and_get_and_verify_type(unit, _object_mask_all);
			if (!okp(obj)) return 0;
			const uint32 hv = u32(obj + 0xB4);
			if (hv == 0xFFFFFFFF) return 0;
			const data_array* comps = havok_components_get();
			if (!comps || !okp((uintptr_t)comps->data)) return 0;
			const int32 idx = (int32)(hv & 0xFFFF);
			if (idx < 0 || idx >= comps->maximum_count || comps->size < 0x78) return 0;
			const uintptr_t comp = (uintptr_t)comps->data + (uintptr_t)idx * (uintptr_t)comps->size;
			const uintptr_t arr = u32(comp + 0x70);
			const int32 n = i32(comp + 0x74);
			if (!okp(arr) || n <= 0 || n > 64) return 0;
			for (int32 i = 0; i < n; ++i)
			{
				const uintptr_t h = handle_in_entity(u32(arr + (uintptr_t)i * 0x60 + 0x40));
				s_capsule c;
				if (h && read_capsule(u32(h - 0x10), c)) return h;   // the body carrying the biped capsule
			}
			return 0;
		}

		bool draw_player_live(int32 user, uintptr_t world, uintptr_t env, const std::vector<s_pair>& pairs)
		{
			s_info& gi = g_info[user];
			gi = s_info{};
			gi.user = user;
			s_player_state& gp = g_players[user];
			// forget the pass-through side of TIMs that are gone (a new TIM on the same polygon decides afresh)
			++gp.frame_no;
			for (auto it = gp.pass_seen.begin(); it != gp.pass_seen.end();)
				if (gp.frame_no - it->second > 2) { gp.pass_side.erase(it->first); it = gp.pass_seen.erase(it); } else ++it;
			if (user == 0)
			{
				++g_obj_side_frame;
				for (auto it = g_obj_side_seen.begin(); it != g_obj_side_seen.end();)
					if (g_obj_side_frame - it->second > 2) { g_obj_side.erase(it->first); it = g_obj_side_seen.erase(it); } else ++it;
			}

			const datum player_index = player_index_from_user_index(user);
			if (player_index == NONE) { gi.note = "no player"; return false; }
			const player_datum* player = (const player_datum*)datum_get(player_data_get(), player_index);
			if (!player || player->unit_index == NONE) { gi.note = "no unit"; return false; }
			real_point3d origin;
			object_get_origin(player->unit_index, &origin, false);
			const v3 unit_pos{ origin.x, origin.y, origin.z };

			// the biped's pair against the level: the pair holding the unit's own Havok body (found through its physics
			// component), else the environment-paired body closest to the unit
			const uintptr_t own = unit_body_handle(player->unit_index);
			const s_pair* best = nullptr; uintptr_t body = 0; xform pose{}; float best_d = 2.0f;
			for (const auto& p : pairs)
			{
				uintptr_t other = 0;
				if (is_environment(p.ha, env)) other = p.hb;
				else if (is_environment(p.hb, env)) other = p.ha;
				else continue;
				if (own && other != own) continue;
				if (!okp(p.agent) || p.agent == addr(k_null_agent)) continue;   // entries without an agent are skipped by the engine too
				xform x;
				if (!body_pose(other, x)) continue;
				const float d = len(x.t - unit_pos);
				if (d < best_d) { best_d = d; best = &p; body = other; pose = x; }
			}
			if (!best) { gi.note = "no (player, level) pair: in a vehicle, or the layout differs on this build"; return false; }

			s_capsule cap_local;
			if (!read_capsule(shape_of(body), cap_local)) { gi.note = "capsule shape not found"; return false; }
			gp.cap_local = cap_local; gp.have_cap = true;
			// classified by the shape itself, not the stance flag (the flag changes a tick before the shape is swapped):
			// standing core ~0.37 wu, crouched ~0.15 wu
			if (len(cap_local.a - cap_local.b) < 0.26f) { gp.cap_crouch = cap_local; gp.have_crouch = true; }
			else { gp.cap_stand = cap_local; gp.have_stand = true; }
			s_capsule cap = cap_local;
			cap.a = xf_point(pose, cap_local.a); cap.b = xf_point(pose, cap_local.b);
			const v3 mid = (cap.a + cap.b) * 0.5f;
			gi.valid = true;
			gi.S = best->S;

			const uint32 tick = game_time_get();
			const int32 hold = g_settings.hold_ticks;
			if (best->S > 0) { gp.last_backstep_tick = tick; gp.ever_backstep = true; }

			// rewind detection, once per tick after integrate (motion time == 1): PREV_k must equal CUR_(k-1)
			const uintptr_t entity = owner_of(body);
			const uintptr_t motion = okp(entity) ? u32(entity + 0x3C) : 0;
			v3 prev{}, cur{};
			const float mtime = okp(motion) ? f32(motion + 0x7C, -1.f) : -1.f;
			if (okp(motion) && read_vec(motion + 0x60, prev) && read_vec(motion + 0x70, cur) && std::fabs(mtime - 1.f) < 1e-4f && tick != gp.last_tick)
			{
				if (gp.have && tick == gp.last_tick + 1)
				{
					const float d = len(prev - gp.last_cur);
					if (d > 1e-4f && d < 1.f)
					{
						gp.have_rewind = true; gp.rewind_tick = tick; gp.rewind_from = gp.last_cur; gp.rewind_to = prev; gp.rewind_dist = d;
						log_line("%u,%d,rewind,,,,,%.4f wu from (%.3f %.3f %.3f) to (%.3f %.3f %.3f) S=%d", tick, (int)user + 1, d,
							gp.last_cur.x, gp.last_cur.y, gp.last_cur.z, prev.x, prev.y, prev.z, (int)best->S);
						gp.last_backstep_tick = tick; gp.ever_backstep = true;
					}
				}
				gp.last_cur = cur; gp.last_tick = tick; gp.have = true;
			}
			const bool hold_active = gp.ever_backstep && tick >= gp.last_backstep_tick && tick - gp.last_backstep_tick <= (uint32)hold;
			if (gp.have_rewind) { gi.rewind = true; gi.rewind_dist = gp.rewind_dist; gi.rewind_age = (int32)(tick - gp.rewind_tick); }

			// welder children
			std::vector<s_child> kids;
			std::string diag;
			const bool welder = read_children(best->agent, kids, diag);
			gi.diag = diag;
			if (!welder) gi.note = "could not read the pair agent's children";
			{
				char d[200];
				snprintf(d, sizeof(d), "capsule r %.3f  a (%.2f %.2f %.2f)  b (%.2f %.2f %.2f)  unit (%.2f %.2f %.2f)  body-unit %.2f wu",
					cap.r, cap.a.x, cap.a.y, cap.a.z, cap.b.x, cap.b.y, cap.b.z, unit_pos.x, unit_pos.y, unit_pos.z, best_d);
				gi.diag2 = d;
			}
			gi.children = (int32)kids.size();
			const float over_min = g_settings.over_min_um * 1e-6f;          // offset: red, heavy, lime pill, logged
			const float over_show = g_settings.show_min_um * 1e-6f;         // believed poses and travel regions appear above this
			v3 qmn{}, qmx{};
			const bool have_q = welder && read_vec(best->agent + 0x20, qmn) && read_vec(best->agent + 0x30, qmx);
			(void)have_q;

			{
				int cat_n[8] = {}, resolved = 0;
				std::vector<v3> tmp;
				for (const auto& k : kids) { ++cat_n[k.key >> 29]; if (key_polygon(k.key, tmp)) ++resolved; }
				char d[200];
				snprintf(d, sizeof(d), "keys by category 0..7: %d %d %d %d %d %d %d %d   polygons resolved %d   biped root shape type %d",
					cat_n[0], cat_n[1], cat_n[2], cat_n[3], cat_n[4], cat_n[5], cat_n[6], cat_n[7], resolved, shape_type(shape_of(body)));
				gi.diag3 = d;
			}
			std::map<uint64_t, std::pair<float, float>> episodes;   // key -> (tim, over) of every suspect TIM this frame
			std::vector<s_believed> bel;
			std::vector<s_travel> travel;
			std::vector<v3> poly;
			for (const auto& k : kids)
			{
				if (!key_polygon(k.key, poly)) continue;
				const bool skipping = k.tim > 0 && k.manifold == 0;
				if (k.manifold > 0) ++gi.contacts;
				float over = 0; bool suspect = false;
				if (skipping)
				{
					++gi.skipped;
					const float gap = seg_poly_dist(cap.a, cap.b, poly) - cap.r;
					const float true_dist = gap - 0.01f;
					over = true_dist > -0.5f ? k.tim - (true_dist - 1.1f * k_tolerance) : 0.f;
					suspect = over > over_min;   // offset (red) only past the threshold
					if (suspect) { ++gi.suspect; episodes[(uint64_t)k.key] = { k.tim, over }; }
					gi.max_over = (std::max)(gi.max_over, over);
				}
				v3 c{ 0, 0, 0 }; for (const v3& p : poly) c = c + p; c = c * (1.f / (float)poly.size());
				// pass-through test for this polygon (see the note above pulse_alpha)
				bool passable = false, pass_risky = false; float pass_margin = 0.f, pass_drain = 0.f;
				if (skipping && g_settings.pass_through)
				{
					// The TIM is spent linearly: moving the centre by dp costs n . dp, whatever the path. Passing through
					// needs the capsule to get fully onto and past this polygon before the TIM runs out:
					//   - over it: your whole footprint over the polygon, so the polygon you are standing on / next to
					//     (honest, in contact) no longer holds you - the closest point q pulled inside the polygon by
					//     your radius;
					//   - past it: the whole capsule beyond its plane - q moved through the plane by the capsule's
					//     half-extent along the polygon normal.
					//     target = q_in - pn * (r + |core . pn| / 2)      needed = n . (centre - target)
					//     margin = TIM - needed                              pass-through when margin > 0
					// Orientation is decided once per TIM - from the side you were on when it was first seen - and kept for
					// as long as that TIM lives: while you pass through, your centre crosses the plane, and re-deciding then
					// would flip the normals and turn the face back to "short" half-way. With the side kept, the margin
					// stays constant all the way through (TIM and "needed" drain by the same n . dp).
					v3 pn = norm(cross(poly[1] - poly[0], poly[2] - poly[0]));
					{
						auto it = gp.pass_side.find(k.key);
						if (it == gp.pass_side.end()) it = gp.pass_side.emplace(k.key, dot(pn, mid - c) < 0 ? -1 : 1).first;
						if (it->second < 0) pn = pn * -1.f;
						gp.pass_seen[k.key] = gp.frame_no;
					}
					v3 n = len(k.normal) > 0.5f ? norm(k.normal) : pn;
					if (dot(n, pn) < 0) n = n * -1.f;
					const v3 q = closest_point_poly(mid, poly);
					// pull q inside the polygon by the capsule radius (toward its centroid, in its plane)
					v3 inward = c - q; inward = inward - pn * dot(inward, pn);
					const float il = len(inward);
					const v3 q_in = il > 1e-4f ? q + inward * ((std::min)(cap.r, il) / il) : q;
					const float half = cap.r + 0.5f * std::fabs(dot(cap.a - cap.b, pn));
					const v3 target = q_in - pn * half;
					const float needed = dot(n, mid - target);
					pass_margin = k.tim - needed;
					// Only real offsets count: plain walking leaves new welds about one step (~0.075 wu) over-credited, which
					// is not an offset you can use - so the over-credit must pass the offset threshold first.
					passable = over > over_min && pass_margin > 0.f;
					// Re-evaluated every frame from the live TIM. Speed matters because the engine only checks at tick
					// boundaries: one step moving toward the polygon drains n . step at once, so when the margin left is
					// smaller than that, a step at this speed can reach the reset point before you are through.
					pass_drain = (std::max)(0.f, -dot(n, cur - prev));
					pass_risky = passable && pass_margin < pass_drain;
					if (suspect && gi.pass_rows.size() < 6)
					{
						char row[240];
						snprintf(row, sizeof(row), "surf %u: TIM %.3f  needed %.3f (over-credit needed %.3f, have %.3f)  n.pn %.2f  margin %+.3f  step drain %.3f  -> %s",
							(unsigned)(k.key & 0xFFFF), k.tim, needed, needed - (k.tim - over), over, dot(n, pn), pass_margin, pass_drain,
							!passable ? "short" : pass_risky ? "PASS at risk (slow down)" : "PASS");
						gi.pass_rows.push_back(row);
					}
					if (passable) { ++gi.pass_level; gi.pass_best = (std::max)(gi.pass_best, pass_margin); }
				}
				if (passable)
				{
					const int rgb = pass_risky ? 0xFFB000 : g_settings.col_pass;   // amber: this speed's step may hit the reset point
					const ImU32 pc = col(rgb, (int)(255.f * pulse_alpha()));
					poly_outline(poly, pc, 5.f);
					char lt[64];
					if (pass_risky) snprintf(lt, sizeof(lt), "PASS? +%.3f (step %.3f)", pass_margin, pass_drain);
					else snprintf(lt, sizeof(lt), "PASS +%.3f", pass_margin);
					text(c, col(rgb), lt);
				}
				if (g_settings.tim_overlay)
				{
					const ImU32 cc = k.manifold > 0 ? col(g_settings.col_tim_contact, 200) : suspect ? col(g_settings.col_tim_suspect, 220) : col(g_settings.col_tim_ok, 160);
					if (!passable) poly_outline(poly, cc, suspect ? 4.5f : 1.2f);       // offset polygons drawn heavy, as in HCM
					if (g_settings.tim_labels && skipping)
					{
						v3 n = len(k.normal) > 0.5f ? norm(k.normal) : norm(cross(poly[1] - poly[0], poly[2] - poly[0]));
						if (dot(n, mid - c) < 0) n = n * -1.f;                 // point it at the player
						tim_measure(cap, n, k.tim, cc, suspect);
					}
				}
				if (g_settings.edges && skipping && (suspect || !g_settings.edges_suspect_only))
					poly_outline(poly, suspect ? col(g_settings.col_tim_suspect) : col(g_settings.col_tim_ok), 3.f);
				if (skipping && over > over_show)
				{
					v3 pn = norm(cross(poly[1] - poly[0], poly[2] - poly[0]));
					const float side = dot(mid - poly[0], pn);
					if (std::fabs(side) < 1e-6f) pn = norm(k.normal); else if (side < 0) pn = pn * -1.f;   // away from the polygon
					bel.push_back({ over, pn });
				}
				// travel region for every welded (skipped) polygon, offset or not - you see the zones while walking
				if (skipping && travel.size() < 12)
				{
					v3 pn = norm(cross(poly[1] - poly[0], poly[2] - poly[0]));
					const float side = dot(mid - poly[0], pn);
					if (std::fabs(side) < 1e-6f) pn = norm(k.normal); else if (side < 0) pn = pn * -1.f;
					{
						v3 n = len(k.normal) > 0.5f ? norm(k.normal) : pn;
						if (dot(n, pn) < 0) n = n * -1.f;
						s_travel tr; tr.key = k.key; tr.n = n; tr.tim = k.tim; tr.over = over; tr.poly = poly;
						tr.pmn = tr.pmx = poly[0];
						for (const v3& p : poly)
						{
							tr.pmn = { (std::min)(tr.pmn.x, p.x), (std::min)(tr.pmn.y, p.y), (std::min)(tr.pmn.z, p.z) };
							tr.pmx = { (std::max)(tr.pmx.x, p.x), (std::max)(tr.pmx.y, p.y), (std::max)(tr.pmx.z, p.z) };
						}
						travel.push_back(tr);
					}
				}
			}

			// ---- objects: every other rigid body paired with this biped ----
			std::vector<s_obj_believed> obel;
			int obj_travel_count = 0;
			struct s_live_piece { uint64_t id; uintptr_t agent; s_child tim; };
			std::vector<s_live_piece> live_pieces;
			const bool offset_busy = g_offset_req != 0 || g_offset[user].phase != _offset_idle;
			if (g_settings.obj_tims || g_settings.obj_believed || offset_busy)
			{
				std::vector<s_obj_leaf> leaves;
				for (const auto& p : pairs)
				{
					uintptr_t other = 0;
					if (p.ha == body) other = p.hb; else if (p.hb == body) other = p.ha; else continue;
					if (is_environment(other, env) || !okp(p.agent) || p.agent == addr(k_null_agent)) continue;
					xform ox;
					if (!body_pose(other, ox)) continue;
					++gi.obj_pairs;
					leaves.clear();
					int unread = 0;
					g_obj_skip_type = -1; g_obj_skip_vt = 0;
					walk_object(p.agent, shape_of(other), ox, cap.a, cap.b, cap.r, leaves, 0, unread);
					if (gi.obj_diag.size() < 4)
					{
						char d[320];
						s_child probe{};
						const bool leaf_agent = read_leaf(p.agent, 0, probe);
						char ent[24];
						if (leaf_agent) snprintf(ent, sizeof(ent), "convex agent"); else snprintf(ent, sizeof(ent), "%d entries", (int)i32(p.agent + 0x10));
						snprintf(d, sizeof(d), "object %d: %.2f wu away  root shape type %d  pair agent vt +0x%X (%s)  %d TIM leaves",
							gi.obj_pairs, len(ox.t - mid), shape_type(shape_of(other)), (unsigned)(u32(p.agent) - (uint32)Memory::GetAddress()),
							ent, (int)leaves.size());
						std::string s = d;
						if (unread) { snprintf(d, sizeof(d), "  unread %d (shape type %d, vt +0x%X)", unread, g_obj_skip_type, (unsigned)g_obj_skip_vt); s += d; }
						if (!leaves.empty())
						{
							const auto& l0 = leaves[0];
							const uintptr_t inner = l0.type == 23 ? u32(l0.shape + 0x30) : 0;
							snprintf(d, sizeof(d), "  | piece type %d (vt +0x%X) inner %d  pos (%.2f %.2f %.2f) box %.2fx%.2fx%.2f  outline %d segs %d caps  gap %.3f  TIM %.3f",
								l0.type, (unsigned)(u32(l0.shape) - (uint32)Memory::GetAddress()), inner ? shape_type(inner) : -1,
								l0.x.t.x, l0.x.t.y, l0.x.t.z, l0.mx.x - l0.mn.x, l0.mx.y - l0.mn.y, l0.mx.z - l0.mn.z,
								(int)l0.segs.size() / 2, (int)l0.caps.size(), l0.gap, l0.tim.tim);
							s += d;
						}
						gi.obj_diag.push_back(s);
					}
					gi.obj_unread += unread;
					for (const auto& l : leaves)
					{
						live_pieces.push_back({ piece_id(l.type, l.mn, l.mx, l.key), l.agent, l.tim });
						++gi.obj_leaves;
						const bool skipping = l.tim.tim > 0 && l.tim.manifold == 0;
						float over = 0; bool suspect = false;
						// A skipped TIM with no contact points means the engine sees a positive gap: a measured gap at or
						// below zero contradicts that, so it is a measurement failure (shape / transform not read right),
						// not an offset - left unmeasured instead of reported as a huge over-credit.
						const bool measured = l.gap < 1e8f && l.gap > -1e-4f;
						if (skipping && !measured) ++gi.obj_unmeasured;
						if (skipping && measured)
						{
							const float true_dist = l.gap - 0.01f;
							over = true_dist > -0.5f ? l.tim.tim - (true_dist - 1.1f * k_tolerance) : 0.f;
							suspect = over > over_min;   // offset (red) only past the threshold
							if (suspect) { ++gi.obj_suspect; episodes[(1ull << 63) | (uint64_t)l.agent] = { l.tim.tim, over }; }
							gi.obj_max_over = (std::max)(gi.obj_max_over, over);
						}
						const v3 c = (l.mn + l.mx) * 0.5f;
						bool obj_pass = false, obj_risky = false; float obj_margin = 0.f, obj_drain = 0.f;
						if (skipping && measured && g_settings.pass_through && l.pass_ok)
						{
							// same rule: TIM is spent only along n; the centre must get past the piece's middle along n
							const v3& n = l.pass_n;
							obj_margin = l.tim.tim - (dot(mid, n) - l.mid_n);
							obj_pass = over > over_min && obj_margin > 0.f;   // real offsets only (see the polygon test)
							obj_drain = (std::max)(0.f, -dot(n, cur - prev));
							obj_risky = obj_pass && obj_margin < obj_drain;
							if (obj_pass) { ++gi.pass_obj; gi.pass_best = (std::max)(gi.pass_best, obj_margin); }
						}
						if (obj_pass)
						{
							const ImU32 pc = col(obj_risky ? 0xFFB000 : g_settings.col_pass, (int)(255.f * pulse_alpha()));
							if (l.segs.empty() && l.caps.empty()) box(l.mn, l.mx, pc, 5.f);
							for (size_t si = 0; si + 1 < l.segs.size(); si += 2) line(l.segs[si], l.segs[si + 1], pc, 5.f);
							for (const auto& oc : l.caps) capsule(oc, v3{ 0, 0, 0 }, pc, 5.f);
							char lt[64];
							if (obj_risky) snprintf(lt, sizeof(lt), "PASS? +%.3f (step %.3f)", obj_margin, obj_drain);
							else snprintf(lt, sizeof(lt), "PASS +%.3f", obj_margin);
							text(c, col(obj_risky ? 0xFFB000 : g_settings.col_pass), lt);
						}
						if (g_settings.obj_tims)
						{
							const int piece_rgb = (g_settings.col_obj_box & 0xFFFFFF) ? g_settings.col_obj_box : 0x9090FF;   // never black
							const ImU32 cc = l.tim.manifold > 0 ? col(g_settings.col_tim_contact, 230) : suspect ? col(g_settings.col_tim_suspect, 240) : col(piece_rgb, 230);
							const int drawn_before = g_lines_drawn;
							const float th = suspect ? 4.5f : 1.4f;     // offset pieces drawn heavy, as in HCM
							if (!obj_pass)
							{
								if (l.segs.empty() && l.caps.empty()) box(l.mn, l.mx, cc, th);
								for (size_t si = 0; si + 1 < l.segs.size(); si += 2) line(l.segs[si], l.segs[si + 1], cc, th);
								for (const auto& oc : l.caps) capsule(oc, v3{ 0, 0, 0 }, cc, th);
							}
							gi.obj_lines += g_lines_drawn - drawn_before;
							if (g_settings.tim_labels && skipping)
							{
								v3 n = len(l.tim.normal) > 0.5f ? norm(l.tim.normal) : norm(mid - c);
								if (dot(n, mid - c) < 0) n = n * -1.f;
								tim_measure(cap, n, l.tim.tim, cc, suspect);
							}
						}
						if (skipping && over > over_show)
						{
							v3 d = len(l.tim.normal) > 0.5f ? norm(l.tim.normal) : norm(mid - c);
							if (dot(d, mid - c) < 0) d = d * -1.f;
							obel.push_back({ over, d, l.agent, mid });
						}
						// travel region for every welded (skipped) object piece, offset or not
						if (skipping && obj_travel_count < 6)
						{
							v3 d = len(l.tim.normal) > 0.5f ? norm(l.tim.normal) : norm(mid - c);
							if (dot(d, mid - c) < 0) d = d * -1.f;
							s_travel tr; tr.key = (uint32)l.agent; tr.n = d; tr.tim = l.tim.tim; tr.over = over; tr.pmn = l.mn; tr.pmx = l.mx; tr.object = true;
							travel.push_back(tr); ++obj_travel_count;
						}
					}
				}
			}
			// object pairs that went to sleep (no longer readable) keep their offset while you stay put: the engine keeps it too
			{
				std::vector<s_obj_believed> keep;
				for (const auto& k : gp.kept_obj)
				{
					bool seen = false;
					for (const auto& b : obel) if (b.key == k.key) { seen = true; break; }
					if (!seen && len(mid - k.at) < 0.01f) { keep.push_back(k); if (k.over > over_min) ++gi.obj_suspect; }   // asleep, still offset
				}
				for (const auto& b : obel) keep.push_back(b);
				gp.kept_obj = keep;
				obel = keep;
			}
			if (g_settings.obj_believed && !obel.empty())
			{
				std::sort(obel.begin(), obel.end(), [](const s_obj_believed& a, const s_obj_believed& b) { return a.over > b.over; });
				if ((int)obel.size() > g_settings.believed_max) obel.resize((size_t)(std::max)(0, g_settings.believed_max));
				gi.obj_believed = (int32)obel.size();
				for (const auto& b : obel)
				{
					const v3 d = b.dir * b.over;
					capsule(cap, d, col(g_settings.col_obj_believed, 220), 1.6f);
					line(mid + d + g_pshift, mid + g_pshift, col(g_settings.col_obj_believed, 140), 1.2f);
					if (g_settings.link_labels)
					{
						char lt[32]; snprintf(lt, sizeof(lt), "%.4f wu", b.over);
						text(mid + d * 0.5f, col(g_settings.col_obj_believed), lt);
					}
				}
			}

			// ---- weld zones: level polygons whose box your capsule centre is inside (welded) or near ----
			if (g_settings.weld_zones)
			{
				build_zone_cache();
				v3 cmn{ (std::min)(cap.a.x, cap.b.x) - cap.r, (std::min)(cap.a.y, cap.b.y) - cap.r, (std::min)(cap.a.z, cap.b.z) - cap.r };
				v3 cmx{ (std::max)(cap.a.x, cap.b.x) + cap.r, (std::max)(cap.a.y, cap.b.y) + cap.r, (std::max)(cap.a.z, cap.b.z) + cap.r };
				const v3 cen = (cmn + cmx) * 0.5f;
				const float wm = 1.5f * k_tolerance;
				const v3 g = (cmx - cmn) * 0.5f + v3{ wm, wm, wm };
				const float range = g_settings.weld_range_mwu * 0.001f;
				std::vector<uint32> welded;
				for (const auto& k : kids) if ((k.key >> 29) == 1) welded.push_back(k.key & 0xFFFF);
				struct s_z { float d; size_t i; bool w; };
				std::vector<s_z> zs;
				for (size_t i = 0; i < g_zones.mn.size(); ++i)
				{
					if (g_zones.mn[i].x > g_zones.mx[i].x) continue;
					const float d = box_dist(cen, g_zones.mn[i] - g, g_zones.mx[i] + g);
					const bool w = std::find(welded.begin(), welded.end(), (uint32)i) != welded.end();
					if (d <= range || w) zs.push_back({ d, i, w });
				}
				std::sort(zs.begin(), zs.end(), [](const s_z& a, const s_z& b) { return a.d < b.d; });
				if (zs.size() > 400) zs.resize(400);
				for (const auto& z : zs)
					box(g_zones.mn[z.i] - g, g_zones.mx[z.i] + g, z.w ? col(g_settings.col_tim_ok, 150) : IM_COL32(0, 200, 255, 90), z.w ? 1.2f : 1.f);
				gi.weld_near = (int32)zs.size(); gi.weld_welded = (int32)welded.size();
			}

			// ---- logger ----
			{
				static const char* const kinds[2] = { "level", "object" };
				log_episodes(user, tick, episodes, kinds);
			}


			// ghost pill
			const bool lime = best->S > 0 || hold_active || gi.suspect > 0 || gi.obj_suspect > 0;
			const ImU32 pill = best->S == -3 ? col(g_settings.col_stuck) : lime ? col(g_settings.col_desync) : col(g_settings.col_normal);
			capsule(cap, v3{ 0, 0, 0 }, pill, 2.f);
			gp.last_pill = pill;

			// rewind target / pre-rewind pose
			if (g_settings.rewind && gp.have_rewind && tick - gp.rewind_tick <= (uint32)hold && gp.have)
			{
				const v3 to_shift = gp.rewind_to - cur, from_shift = gp.rewind_from - cur;
				capsule(cap, from_shift, col(g_settings.col_rewind_from, 170), 1.2f);
				capsule(cap, to_shift, col(g_settings.col_rewind_to, 200), 1.4f);
				line(gp.rewind_from + (mid - cur), gp.rewind_to + (mid - cur), col(g_settings.col_rewind_to), 2.f);
			}

			// believed poses
			if (g_settings.believed && !bel.empty())
			{
				std::sort(bel.begin(), bel.end(), [](const s_believed& a, const s_believed& b) { return a.over > b.over; });
				if ((int32)bel.size() > g_settings.believed_max) bel.resize((size_t)(std::max)(0, g_settings.believed_max));
				gi.believed = (int32)bel.size();
				for (const auto& b : bel)
				{
					const v3 d = b.dir * b.over;
					capsule(cap, d, col(g_settings.col_believed, 220), 1.6f);
					line(mid + d + g_pshift, mid + g_pshift, col(g_settings.col_believed, 140), 1.2f);
					if (g_settings.link_labels)
					{
						char t[32]; snprintf(t, sizeof(t), "%.4f wu", b.over);
						text(mid + d * 0.5f, col(g_settings.col_believed), t);
					}
				}
			}

			// ghost travel regions (level): weld zone (polygon box grown by the capsule half-size + 1.5 x tolerance, fixed
			// to the polygon; the capsule centre must stay inside) and reset sheet (polygon pushed to n.x = n.mid - tim)
			if ((g_settings.travel || g_settings.travel_objects) && !travel.empty())
			{
				static const int hues[6] = { 0xFFDC00, 0x00DCFF, 0xFF78FF, 0x78FF78, 0xFF963C, 0xA0A0FF };
				v3 cmn{ (std::min)(cap.a.x, cap.b.x) - cap.r, (std::min)(cap.a.y, cap.b.y) - cap.r, (std::min)(cap.a.z, cap.b.z) - cap.r };
				v3 cmx{ (std::max)(cap.a.x, cap.b.x) + cap.r, (std::max)(cap.a.y, cap.b.y) + cap.r, (std::max)(cap.a.z, cap.b.z) + cap.r };
				const v3 cen = (cmn + cmx) * 0.5f;
				const v3 dcen = cen + g_pshift;   // drawn with the rendered character; margins use the physics centre
				const float wm = 1.5f * k_tolerance;
				const v3 g = (cmx - cmn) * 0.5f + v3{ wm, wm, wm };
				const float cs = 0.06f;
				line(dcen - v3{ cs, 0, 0 }, dcen + v3{ cs, 0, 0 }, IM_COL32_WHITE, 2.f);
				line(dcen - v3{ 0, cs, 0 }, dcen + v3{ 0, cs, 0 }, IM_COL32_WHITE, 2.f);
				line(dcen - v3{ 0, 0, cs }, dcen + v3{ 0, 0, cs }, IM_COL32_WHITE, 2.f);
				// offsets first (they get the first colors and panel rows), then the plain welds
				std::stable_sort(travel.begin(), travel.end(), [](const s_travel& a, const s_travel& b) { return a.over > b.over; });
				for (size_t i = 0; i < travel.size(); ++i)
				{
					const s_travel& t = travel[i];
					if (t.object ? !g_settings.travel_objects : !g_settings.travel) continue;
					const v3 zmn = t.pmn - g, zmx = t.pmx + g;
					box(zmn, zmx, col(hues[i % 6], 190), 1.3f);
					const v3 p0 = dcen - t.n * t.tim;
					std::vector<v3> sheet = t.poly;
					if (sheet.empty())   // object piece: a 0.7 wu square sheet around the point straight ahead of your centre
					{
						const v3 h = std::fabs(t.n.z) < 0.9f ? v3{ 0, 0, 1 } : v3{ 1, 0, 0 };
						const v3 u1 = norm(cross(t.n, h)) * 0.35f, u2 = norm(cross(t.n, norm(cross(t.n, h)))) * 0.35f;
						sheet = { p0 + u1 + u2, p0 - u1 + u2, p0 - u1 - u2, p0 + u1 - u2 };
					}
					for (v3& v : sheet) v = v - t.n * dot(t.n, v - p0);
					poly_fill(sheet, col(g_settings.col_sheet, 45));
					poly_outline(sheet, col(g_settings.col_sheet), 2.f);
					if (!t.poly.empty()) poly_outline(t.poly, col(hues[i % 6]), 2.f);
					line(dcen, p0, col(g_settings.col_sheet, 200), 1.2f);
					const float margin = (std::min)({ cen.x - zmn.x, zmx.x - cen.x, cen.y - zmn.y, zmx.y - cen.y, cen.z - zmn.z, zmx.z - cen.z });
					char row[200], mg[24];
					if (margin < 0) snprintf(mg, sizeof(mg), "OUTSIDE"); else snprintf(mg, sizeof(mg), "%.4f wu", margin);
					const uint32 cat = t.key >> 29;
					if (t.object)
						snprintf(row, sizeof(row), "#%zu object piece: toward-object budget %.4f wu (over-credit %.4f)  zone margin %s (approx: piece box + welder margin)",
							i + 1, t.tim, t.over, mg);
					else
						snprintf(row, sizeof(row), "#%zu %s surf %u: toward-polygon budget %.4f wu (over-credit %.4f)  zone margin %s",
							i + 1, cat == 5 ? "IG" : "world", (unsigned)(cat == 5 ? ((t.key >> 16) & 0x1FFF) : (t.key & 0xFFFF)), t.tim, t.over, mg);
					if (gi.travel.size() < 6) gi.travel.push_back(row);   // panel: the first six (offsets first)
				}
			}
			// ---- offset save state ----
			{
				auto finish = [&](const std::string& s) { offset_toast(s); g_offset[user].phase = _offset_idle; };
				const uintptr_t level_agent = best->agent;
				std::vector<std::pair<uint64_t, uintptr_t>> live_level;
				std::vector<s_offset_entry> snap;
				for (const auto& k : kids)
				{
					const uint32 cat = k.key >> 29;
					if (cat != 1 && cat != 5) continue;                       // world / instanced-geometry polygons
					live_level.push_back({ k.key, k.agent });
					if (k.tim > 0 && k.manifold == 0) snap.push_back({ false, k.key, k.normal, k.tim });
				}
				for (const auto& lp : live_pieces)
					if (lp.tim.tim > 0 && lp.tim.manifold == 0) snap.push_back({ true, lp.id, lp.tim.normal, lp.tim.tim });

				if (g_offset_req == 1 && user == g_offset_user)
				{
					g_offset[user].valid = true; g_offset[user].pos = unit_pos; g_offset[user].saved = snap; g_offset[user].save_tick = tick;
					g_offset[user].phase = _offset_wait; g_offset[user].is_load = false; g_offset[user].old_agent = level_agent; g_offset[user].frames = 0; g_offset[user].restored = 0;
					g_offset[user].done.assign(snap.size(), false);
					uint8 one = 1; put(addr(k_checkpoint_flag), &one, 1);
					g_offset_req = 0;
					offset_toast("Offsets saved: " + std::to_string(snap.size()) + " TIMs - checkpoint requested");
				}
				else if (g_offset_req == 2 && user == g_offset_user)
				{
					g_offset_req = 0;
					if (!g_offset[user].valid) offset_toast("Load offsets: nothing saved yet");
					else
					{
						g_offset[user].phase = _offset_wait; g_offset[user].is_load = true; g_offset[user].old_agent = level_agent; g_offset[user].frames = 0; g_offset[user].restored = 0;
						g_offset[user].req_tick = tick;
						g_offset[user].done.assign(g_offset[user].saved.size(), false);
						uint8 one = 1; put(addr(k_revert_flag), &one, 1);
						offset_toast("Load offsets: revert requested");
					}
				}
				else if (g_offset[user].phase == _offset_wait)
				{
					// Only our own Save / Load ever reaches here (natural checkpoints and reverts leave the offsets alone):
					//   Save: the checkpoint is taken on the next tick(s) -> write the snapshot back 3 ticks after the save
					//   Load: the revert is seen as game time going backwards -> write it back once that has happened
					s_offset_state& os = g_offset[user];
					++os.frames;
					const bool ready = os.is_load ? (tick < os.req_tick) : (tick >= os.save_tick + 3);
					if (ready) { os.phase = _offset_apply; os.frames = 0; }
					else if (os.frames > 300)
						finish(os.is_load ? "Load offsets: the revert did not happen (nothing restored)" : "Offsets saved (no checkpoint seen - offsets untouched)");
				}
				else if (g_offset[user].phase == _offset_idle && g_settings.offset_natural_reverts && g_offset[user].valid &&
					tick < g_offset[user].last_tick && len(unit_pos - g_offset[user].pos) < 0.05f)
				{
					// optional: a natural revert back to the offset checkpoint (death, menu revert) restores them too
					s_offset_state& os = g_offset[user];
					os.phase = _offset_apply; os.is_load = true; os.frames = 0; os.restored = 0; os.done.assign(os.saved.size(), false);
				}
				else if (g_offset[user].phase == _offset_apply)
				{
					++g_offset[user].frames;
					if (g_offset[user].is_load && g_offset[user].frames == 1 && len(unit_pos - g_offset[user].pos) > 0.05f)
						finish("Load offsets: you are not where they were saved - a newer checkpoint replaced it (nothing restored)");
					else
					{
						// TIM corrected by your movement since the save (TIM_new = TIM + n . dp): zero after a load
						const v3 dp = unit_pos - g_offset[user].pos;
						for (size_t i = 0; i < g_offset[user].saved.size(); ++i)
						{
							if (g_offset[user].done[i]) continue;
							const s_offset_entry& e = g_offset[user].saved[i];
							uintptr_t agent = 0;
							if (e.obj) { for (const auto& lp : live_pieces) if (lp.id == e.id) { agent = lp.agent; break; } }
							else { for (const auto& l : live_level) if (l.first == e.id) { agent = l.second; break; } }
							if (!agent) continue;
							s_child live{};
							if (!read_leaf(agent, 0, live) || live.manifold > 0) continue;   // never touch a pair in contact
							const float tim = e.tim + dot(e.normal, dp);
							if (!(tim > 0)) continue;
							const float n[3] = { e.normal.x, e.normal.y, e.normal.z };
							if (put(agent + 0x20, n, sizeof(n)) && put(agent + 0x2C, &tim, sizeof(tim))) { g_offset[user].done[i] = true; ++g_offset[user].restored; }
						}
						const int total = (int)g_offset[user].saved.size();   // (see below for last_tick)
						if (g_offset[user].restored == total || g_offset[user].frames >= 60)
							finish(std::string(g_offset[user].is_load ? "Offsets loaded: " : "Offsets kept: ") + std::to_string(g_offset[user].restored) + " of " +
								std::to_string(total) + " TIMs restored" + (g_offset[user].restored == total ? "" : " (the rest have no matching pair)"));
					}
				}
			}

			g_offset[user].last_tick = tick;
			return true;
		}

		/* While a player stands still, Havok puts their island to sleep and its collision pairs (with every TIM) are no
		   longer listed, but nothing has been reset: the TIMs are kept and apply again as soon as the island wakes. So the
		   last live frame - capsule colour, offset capsules, level and object TIMs, travel regions, panel - is kept on
		   screen until something actually resets it: the player moves away from where it was recorded (teleport, revert,
		   respawn), the unit changes, the BSP changes, or the game ends. */

		// Live state only - nothing is frozen or replayed: whatever the engine currently holds is what is drawn, so a
		// rewind or anything else that resets TIMs clears them here too. The pill itself is always drawn: when no live
		// pair can be read this frame it is placed at the unit with the capsule last read (default biped capsule before
		// that), pink unless the last live read was offset and the player has not moved since.
		void draw_player(int32 user, uintptr_t world, uintptr_t env, const std::vector<s_pair>& pairs)
		{
			s_player_state& gp = g_players[user];
			g_pshift = v3{ 0, 0, 0 };
			// crouching / standing replaces the biped's physics shape, so the engine rebuilds its pairs and every TIM
			// (level and object) starts over: drop anything kept from before
			{
				const datum player_index = player_index_from_user_index(user);
				const player_datum* player = player_index != NONE ? (const player_datum*)datum_get(player_data_get(), player_index) : nullptr;
				const unit_datum* u = (player && player->unit_index != NONE) ? (const unit_datum*)object_try_and_get_and_verify_type(player->unit_index, _object_mask_all) : nullptr;
				// stance from the unit's crouch amount (0 standing .. 1 crouched), the value Halo itself uses for the eye
				// height; the crouch flag bit alone did not track it on this build
				const int crouch = u ? ((u->unit.crouching > 0.5f || ((u->unit.unit_flags >> _unit_is_crouching_bit) & 1)) ? 1 : 0) : -1;
				gp.crouch_amount = u ? u->unit.crouching : -1.f;
				if (crouch != gp.crouch)
				{
					if (gp.crouch != -1) { gp.kept_obj.clear(); gp.kept_level.clear(); gp.last_pill = 0; }
					gp.crouch = crouch;
				}
			}
			{
				const datum player_index = player_index_from_user_index(user);
				const player_datum* player = player_index != NONE ? (const player_datum*)datum_get(player_data_get(), player_index) : nullptr;
				real_point3d now, drawn;
				if (player && player->unit_index != NONE && halo_frame_interpolator_enabled() &&
					halo_interpolator_interpolate_object_position(player->unit_index, &drawn))
				{
					object_get_origin(player->unit_index, &now, false);
					const v3 d{ drawn.x - now.x, drawn.y - now.y, drawn.z - now.z };
					if (len(d) < 1.f) g_pshift = d;   // ignore teleports / respawns
				}
			}
			std::vector<s_prim> rec;
			g_rec = &rec;
			const bool live = draw_player_live(user, world, env, pairs);
			g_rec = nullptr;
			const uint32 now_tick = game_time_get();
			if (live)
			{
				gp.last_live_prims = std::move(rec);
				gp.last_live_tick = now_tick;
				g_last_info[user] = g_info[user];
				gp.have_last_live = true;
			}
			else if (gp.have_last_live && now_tick - gp.last_live_tick <= 2)
			{
				// welding / island merging can drop the pair for a tick or two: bridge that gap with the last live frame
				// (moved with you) instead of blinking out. Anything longer than two ticks is real and shown as such.
				datum u0 = NONE;
				{
					const datum pi = player_index_from_user_index(user);
					const player_datum* pl = pi != NONE ? (const player_datum*)datum_get(player_data_get(), pi) : nullptr;
					if (pl) u0 = pl->unit_index;
				}
				v3 d{ 0, 0, 0 };
				if (u0 != NONE && gp.pill_unit == u0) { real_point3d o; object_get_origin(u0, &o, false); d = v3{ o.x, o.y, o.z } - gp.pill_pos; }
				for (const s_prim& pr : gp.last_live_prims)
				{
					if (pr.kind == 0) line(pr.a + d, pr.b + d, pr.c, pr.thick);
					else if (pr.kind == 1) text(pr.a + d, pr.c, pr.s.c_str());
					else { std::vector<v3> q = pr.poly; for (v3& v : q) v = v + d; poly_fill(q, pr.c); }
				}
				g_info[user] = g_last_info[user];
				g_pshift = v3{ 0, 0, 0 };
				return;
			}

			datum unit = NONE; v3 pos{};
			{
				const datum player_index = player_index_from_user_index(user);
				const player_datum* player = player_index != NONE ? (const player_datum*)datum_get(player_data_get(), player_index) : nullptr;
				if (player && player->unit_index != NONE)
				{
					unit = player->unit_index;
					real_point3d o; object_get_origin(unit, &o, false);
					pos = { o.x, o.y, o.z };
				}
			}
			if (live) { gp.pill_pos = pos; gp.pill_unit = unit; gp.was_live = true; g_pshift = v3{ 0, 0, 0 }; return; }
			if (unit == NONE) return;

			// The real Havok capsule, read from the unit's own rigid body (exact for either stance, every frame);
			// the remembered / estimated shape below is only a last resort if that body cannot be found.
			s_capsule real_cap; bool have_real = false;
			{
				const uintptr_t h = unit_body_handle(unit);
				xform bx; s_capsule lc;
				if (h && body_pose(h, bx) && read_capsule(u32(h - 0x10), lc))
				{
					real_cap = lc; real_cap.a = xf_point(bx, lc.a); real_cap.b = xf_point(bx, lc.b);
					have_real = true;
				}
			}
			s_capsule local;
			s_capsule stand;
			if (gp.have_stand) stand = gp.cap_stand;
			else if (gp.have_cap && gp.crouch != 1) stand = gp.cap_local;
			else { stand.r = 0.175f; stand.a = { 0, 0, 0.55f }; stand.b = { 0, 0, 0.18f }; stand.ok = true; }   // biped capsule, relative to the unit origin
			if (gp.crouch == 1 && gp.have_crouch) local = gp.cap_crouch;
			else if (gp.crouch == 1 || gp.crouch_amount > 0.5f)
			{
				const float amt = gp.crouch_amount >= 0.f ? (std::min)(gp.crouch_amount, 1.f) : 1.f;
				local = stand;
				v3& top = stand.a.z >= stand.b.z ? local.a : local.b;
				const v3& bot = stand.a.z >= stand.b.z ? stand.b : stand.a;
				top.z = top.z - (top.z - bot.z) * 0.6f * amt;
			}
			else local = stand;
			// gp.cap_local is in body space; the body origin sits at the unit origin (body-unit 0.00 in the panel)
			s_capsule cap = local;
			cap.a = local.a + pos; cap.b = local.b + pos;
			if (have_real) cap = real_cap;
			// the moment the pair disappears (you came to rest) the kept object offsets are re-anchored to where you are
			// now: the last live read happened while you were still settling, a few millimetres away
			const v3 rest_mid = (cap.a + cap.b) * 0.5f;
			if (gp.was_live)
			{
				gp.was_live = false;
				gp.pill_pos = pos; gp.pill_unit = unit;
				for (auto& k : gp.kept_obj) k.at = rest_mid;
			}
			const bool unmoved = gp.pill_unit == unit && len(pos - gp.pill_pos) < 0.01f;
			// No live pair: the level pair is gone, and with it every level TIM (they come back fresh), so only object
			// offsets the engine still keeps can make the pill lime here.
			if (!unmoved) gp.kept_obj.clear();
			const float over_min = g_settings.over_min_um * 1e-6f;
			bool obj_offset = false;
			for (const auto& b : gp.kept_obj) if (b.over > over_min) obj_offset = true;
			const ImU32 pill = obj_offset ? col(g_settings.col_desync) : col(g_settings.col_normal);
			capsule(cap, v3{ 0, 0, 0 }, pill, 2.f);
			// offsets the engine still holds but that cannot be read while asleep: kept until you move
			const v3 mid = (cap.a + cap.b) * 0.5f;
			auto draw_kept = [&](std::vector<s_obj_believed>& list, int rgb, bool enabled)
			{
				std::vector<s_obj_believed> keep;
				for (const auto& b : list) if (len(mid - b.at) < 0.01f) keep.push_back(b);
				list = keep;
				if (!enabled) return;
				for (const auto& b : list)
				{
					const v3 d = b.dir * b.over;
					capsule(cap, d, col(rgb, 220), 1.6f);
					line(mid + d + g_pshift, mid + g_pshift, col(rgb, 140), 1.2f);
					if (g_settings.link_labels) { char lt[32]; snprintf(lt, sizeof(lt), "%.4f wu", b.over); text(mid + d * 0.5f, col(rgb), lt); }
				}
			};
			draw_kept(gp.kept_obj, g_settings.col_obj_believed, g_settings.obj_believed);
			g_info[user].valid = false;
			if (g_info[user].note.empty()) g_info[user].note = "no live pair this frame";
			{
				char st[64]; snprintf(st, sizeof(st), " (pill only: %s, crouch %.2f)", have_real ? "Havok body read" : "body NOT found, estimated shape", gp.crouch_amount);
				g_info[user].note += st;
				// where are the islands? (to find the asleep pair list): every {ptr, count} in the world header whose
				// entries point back at the world, with their island and pair counts
				std::string isl = "\n    world island arrays:";
				for (uintptr_t off = 0x08; off <= 0x80; off += 4)
				{
					const uintptr_t arr = u32(world + off);
					const int32 n = i32(world + off + 4);
					if (!okp(arr) || n <= 0 || n > 2048) continue;
					int islands = 0, pairs_n = 0;
					for (int32 i = 0; i < n && i < 2048; ++i)
					{
						const uintptr_t isp = u32(arr + 4 * (uintptr_t)i);
						if (!okp(isp)) continue;
						if (u32(isp + 0x20) != world) continue;
						++islands;
						const int32 pc = i32(isp + 0x6C);
						if (pc > 0 && pc < 100000) pairs_n += pc;
					}
					if (islands > 0) { char b[64]; snprintf(b, sizeof(b), " +0x%X: %d islands %d pairs;", (unsigned)off, islands, pairs_n); isl += b; }
				}
				g_info[user].note += isl;
			}
			g_pshift = v3{ 0, 0, 0 };
		}

		void draw_info_panel(uintptr_t world)
		{
			ImGui::SetNextWindowPos(ImVec2(10, 120), ImGuiCond_FirstUseEver);
			ImGui::SetNextWindowBgAlpha(0.6f);
			if (!ImGui::Begin("Ghost / TIM viewer", nullptr, ImGuiWindowFlags_AlwaysAutoResize | ImGuiWindowFlags_NoFocusOnAppearing | ImGuiWindowFlags_NoNav | ImGuiWindowFlags_NoInputs | ImGuiWindowFlags_NoSavedSettings))
			{
				ImGui::End();
				return;
			}
			if (okp(world))
			{
				const float base = f32(world + 0x244), per = f32(world + 0x248), res = f32(world + 0x24C);
				ImGui::Text("collision tolerance %.4f wu   backstep: delta(S) = %.4f + S x %.4f wu   rewind resolution %.4f step",
					k_tolerance, -base, -per, res);
			}
			for (int32 u = 0; u < 4; ++u)
			{
				const s_info& g = g_info[u];
				if (!g.valid && g.note.empty()) continue;
				if (!g.valid) { ImGui::TextDisabled("P%d: %s", u + 1, g.note.c_str()); continue; }
				ImGui::Text("P%d: S=%d  children %d  skipped %d  contacts %d  suspect %d  max over-credit %.4f wu  believed %d",
					u + 1, g.S, g.children, g.skipped, g.contacts, g.suspect, g.max_over, g.believed);
				if (!g.note.empty()) ImGui::TextDisabled("    %s", g.note.c_str());
				if (!g.diag.empty()) ImGui::TextDisabled("    %s", g.diag.c_str());
				if (!g.diag2.empty()) ImGui::TextDisabled("    %s", g.diag2.c_str());
				if (!g.diag3.empty()) ImGui::TextDisabled("    %s", g.diag3.c_str());
				if (g.obj_pairs > 0)
					ImGui::Text("    objects: %d paired bodies  %d TIM leaves  suspect %d  max over-credit %.4f wu  believed %d%s   [Object TIMs %s, %d outline lines drawn, color %06X]",
						g.obj_pairs, g.obj_leaves, g.obj_suspect, g.obj_max_over, g.obj_believed, g.obj_unread ? "  (some shapes not read)" : "",
						g_settings.obj_tims ? "on" : "OFF", (int)g.obj_lines, (unsigned)(g_settings.col_obj_box & 0xFFFFFF));
				if (g.obj_unmeasured > 0)
					ImGui::TextDisabled("      %d object piece(s) could not be measured (distance read as touching while the engine has no contact) - not counted", (int)g.obj_unmeasured);
				for (const auto& d : g.obj_diag) ImGui::TextDisabled("      %s", d.c_str());
				if (g_settings.weld_zones)
					ImGui::Text("    weld zones: %d drawn (%d welded) within %.2f wu - a polygon stays welded while the white cross is inside its zone",
						g.weld_near, g.weld_welded, g_settings.weld_range_mwu * 0.001f);
				if (g_settings.logger) ImGui::TextDisabled("    logging to GhostViewerLog.csv (next to halo2.exe)");
				if (g.user == g_offset_user && !g_offset_status.empty()) ImGui::TextColored(ImVec4(0.55f, 0.85f, 1.f, 1.f), "    %s", g_offset_status.c_str());
				if (g_settings.pass_through && (g.pass_level || g.pass_obj))
					ImGui::TextColored(ImVec4(((g_settings.col_pass >> 16) & 0xFF) / 255.f, ((g_settings.col_pass >> 8) & 0xFF) / 255.f, (g_settings.col_pass & 0xFF) / 255.f, 1.f),
						"    PASS-THROUGH: %d polygon(s), %d object piece(s) - moving straight in, your centre clears their middle by up to %.3f wu before the check",
						(int)g.pass_level, (int)g.pass_obj, g.pass_best);
				if (g_settings.pass_through) for (const auto& r : g.pass_rows) ImGui::TextDisabled("      pass test %s", r.c_str());
				if (g.rewind) ImGui::Text("    last rewind %.4f wu, %d ticks ago", g.rewind_dist, g.rewind_age);
				if (!g.travel.empty())
				{
					ImGui::TextColored(ImVec4(1, 0.85f, 0.2f, 1), "    TRAVEL REGION: keep the white cross inside each box and short of its red sheet");
					for (const auto& r : g.travel) ImGui::Text("      %s", r.c_str());
				}
			}
			if (g_settings.oob_bar && g_death.valid)
			{
				ImGui::Separator();
				if (g_death.oob_counter > 0)
					ImGui::TextColored(ImVec4(0.47f, 0.86f, 1.f, 1.f), "OUT OF BOUNDS (your body is inside solid / outside the level): %d of %d ticks - killed in %d ticks",
						g_death.oob_counter, g_death.oob_limit + 1, g_death.oob_limit + 1 - g_death.oob_counter);
				else
					ImGui::TextDisabled("OUT OF BOUNDS: not counting. The check starts only on ticks where (tick + player index %d) %% 16 == 0 - next in %d ticks; then %d ticks in a row kill",
						g_death.player_index, g_death.oob_next_check, g_death.oob_limit + 1);
				if (g_death.kv_count > 0)
				{
					ImGui::Text("KILL VOLUMES: %d (%d enabled)   one checked per tick: #%d this tick", g_death.kv_count, g_death.kv_enabled, g_death.kv_checking);
					if (g_death.kv_inside.empty()) ImGui::TextDisabled("    you are not inside an enabled kill volume");
					for (const auto& in : g_death.kv_inside)
						ImGui::TextColored(ImVec4(1.f, 0.9f, 0.f, 1.f), "    INSIDE kill volume #%d - checked in %d ticks; then every %d ticks", in.first, in.second, g_death.kv_count);
				}
				else ImGui::TextDisabled("KILL VOLUMES: none on this map");
			}
			ImGui::End();
		}
	}

	/* ---- third person camera ----
	   The render camera is moved behind the player in main_render (Cartographer's own reimplementation), and the game
	   director's perspective (director_get_perspective, 0x59E2B) reports 3 ("following", the vehicle third-person
	   perspective) instead of 0 for the player while it is on, so the game treats the view as third person
	   (no first-person weapon view effects, HUD indicators as in vehicles). Aiming and physics are untouched. */
	namespace
	{
		s_observer_result g_tp_camera[4];
		typedef int32(__cdecl* t_director_get_perspective)(int32 user_index);
		t_director_get_perspective p_director_get_perspective = nullptr;

		// Only the game's own render code sees "third person": the HUD (interface code, image 0x220000..0x22FFFF, which
		// hides itself for perspective 3) and Cartographer's own callers (outside the game image) get the real value.
		int32 __cdecl director_get_perspective_hook(int32 user_index)
		{
			const int32 perspective = p_director_get_perspective(user_index);
			if (!g_settings.third_person || perspective != 0 || !game_in_progress() || cinematic_in_progress()) return perspective;
			// only the render code sees "third person" (scene visibility 0x190755, render_camera_scene 0x1912B3, first-person
			// render 0x195E72 / 0x19624C, ...): the simulation, units and HUD keep the real perspective, so third person
			// cannot change anything the game simulates
			const uintptr_t caller = (uintptr_t)_ReturnAddress() - Memory::GetAddress();
			// + the effect code that picks first- vs third-person particles / lights / lens flares (0x29324, 0x2A20D,
			//   0xA6B2D, 0xA7F91, 0xA9AFC, 0xA9C68), so first-person-only effects (the sword's glow) stay out of the view
			const bool render_code = (caller >= 0x18E000 && caller < 0x1A0000) || (caller >= 0x27E000 && caller < 0x280000) ||
				(caller >= 0x29000 && caller < 0x2B000) || (caller >= 0xA6000 && caller < 0xAA000);
			return render_code ? 3 : perspective;
		}
	}

	bool third_person_active(void) { return g_settings.third_person && game_in_progress() && !cinematic_in_progress(); }

	s_observer_result* camera_override(int32 user_index, s_observer_result* camera)
	{
		if (!camera || !third_person_active() || user_index < 0 || user_index > 3) return camera;
		s_observer_result& c = g_tp_camera[user_index];
		c = *camera;
		const v3 f = norm(v3{ camera->forward.i, camera->forward.j, camera->forward.k });
		// placed from the game's own (frame-interpolated) camera position: the unit origin only moves once per tick,
		// so anchoring to it stutters. Shake / melee / recoil kicks are already removed in observer_apply_camera_effect.
		const v3 eye{ camera->position.x, camera->position.y, camera->position.z };
		const v3 up_world{ 0, 0, 1 };
		v3 right = norm(cross(f, up_world));
		if (len(right) < 0.5f) right = v3{ 0, -1, 0 };
		const float back = g_settings.tp_distance_mwu * 0.001f, up = g_settings.tp_height_mwu * 0.001f, side = g_settings.tp_side_mwu * 0.001f;
		const v3 p = eye - f * back + up_world * up + right * side;
		c.position.x = p.x; c.position.y = p.y; c.position.z = p.z;
		return &c;
	}

	void apply_patches(void)
	{
		DETOUR_ATTACH(p_director_get_perspective, Memory::GetAddress<t_director_get_perspective>(0x59E2B), director_get_perspective_hook);
	}

	void capture_view(int32 user_index, const s_frame* frame)
	{
		if (!frame || user_index < 0 || user_index > 3) return;
		s_captured_view& cv = g_captured[user_index];
		cv.camera = frame->camera;
		cv.projection = frame->projection;
		cv.frame = g_frame_counter;
		cv.valid = true;
	}

	/* ---- practice toggles: Disable AI / Invulnerability ----
	   Local campaign only (never in networked or multiplayer games). Both are undone when switched off.
	     Disable AI:      ai_globals->ai_active = false (what "ai_enable false" does; ai_update at 0x70D941 skips all
	                      AI while it is false - actors stand still and do not perceive or shoot).
	     Invulnerability: the unit's "cannot take damage" object flag, bit 0x200000 of object+4 (what
	                      object_cannot_take_damage sets: hs function 90 -> 0x533C93).                          */
	namespace
	{
		bool g_ai_forced_off = false;
		datum g_invuln_units[4] = { NONE, NONE, NONE, NONE };
		constexpr uint32 k_cannot_take_damage = 0x200000;

		void apply_practice_toggles(void)
		{
			const bool allowed = game_in_progress() && game_is_campaign() && !game_is_networked();
			// AI
			ai_globals_type* ai = allowed ? ai_globals_get() : nullptr;
			if (ai)
			{
				if (g_settings.disable_ai) { ai->ai_active = false; g_ai_forced_off = true; }
				else if (g_ai_forced_off) { ai->ai_active = true; g_ai_forced_off = false; }
			}
			else g_ai_forced_off = false;
			// invulnerability, per local player's current unit
			for (int32 u = 0; u < 4; ++u)
			{
				datum unit = NONE;
				if (allowed && players_user_is_active(u))
				{
					const datum pi = player_index_from_user_index(u);
					const player_datum* pl = pi != NONE ? (const player_datum*)datum_get(player_data_get(), pi) : nullptr;
					if (pl) unit = pl->unit_index;
				}
				auto flags_of = [](datum d) -> uint32* {
					if (d == NONE) return nullptr;
					const uintptr_t obj = (uintptr_t)object_try_and_get_and_verify_type(d, _object_mask_all);
					return okp(obj) ? (uint32*)(obj + 4) : nullptr;
				};
				// release a unit we protected when the toggle goes off or the player changes unit (death, vehicle swap)
				if (g_invuln_units[u] != NONE && (!g_settings.invulnerable || g_invuln_units[u] != unit))
				{
					if (uint32* f = flags_of(g_invuln_units[u])) *f &= ~k_cannot_take_damage;
					g_invuln_units[u] = NONE;
				}
				if (g_settings.invulnerable && unit != NONE)
				{
					if (uint32* f = flags_of(unit)) { *f |= k_cannot_take_damage; g_invuln_units[u] = unit; }
				}
			}
		}
	}

	namespace
	{
		// keyboard / controller shortcuts for Save / Load Offsets (only while the game window has focus)
		typedef DWORD(WINAPI* t_xinput_get_state)(DWORD, XINPUT_STATE*);
		t_xinput_get_state xinput_get_state()
		{
			static t_xinput_get_state fn = nullptr; static bool tried = false;
			if (!tried)
			{
				tried = true;
				for (const char* dll : { "xinput1_4.dll", "xinput1_3.dll", "xinput9_1_0.dll" })
					if (HMODULE m = LoadLibraryA(dll)) { fn = (t_xinput_get_state)GetProcAddress(m, "XInputGetState"); if (fn) break; }
			}
			return fn;
		}
		bool game_has_focus()
		{
			DWORD pid = 0; GetWindowThreadProcessId(GetForegroundWindow(), &pid);
			return pid == GetCurrentProcessId();
		}
		void poll_offset_shortcuts()
		{
			static bool prev_save = false, prev_load = false;
			bool save = false, load = false;
			if (game_has_focus())
			{
				if (g_settings.key_offset_save > 0) save |= (GetAsyncKeyState(g_settings.key_offset_save) & 0x8000) != 0;
				if (g_settings.key_offset_load > 0) load |= (GetAsyncKeyState(g_settings.key_offset_load) & 0x8000) != 0;
				if (g_settings.pad_offset > 0)
					if (t_xinput_get_state fn = xinput_get_state())
						for (DWORD i = 0; i < 4; ++i)
						{
							XINPUT_STATE st{};
							if (fn(i, &st) != ERROR_SUCCESS) continue;
							const WORD b = st.Gamepad.wButtons;
							if (g_settings.pad_offset == 1 && (b & XINPUT_GAMEPAD_BACK))
							{
								save |= (b & XINPUT_GAMEPAD_DPAD_LEFT) != 0; load |= (b & XINPUT_GAMEPAD_DPAD_RIGHT) != 0;
							}
							else if (g_settings.pad_offset == 2 && (b & XINPUT_GAMEPAD_BACK))
							{
								save |= (b & XINPUT_GAMEPAD_LEFT_SHOULDER) != 0; load |= (b & XINPUT_GAMEPAD_RIGHT_SHOULDER) != 0;
							}
							else if (g_settings.pad_offset == 3 && (b & XINPUT_GAMEPAD_LEFT_THUMB))
							{
								save |= (b & XINPUT_GAMEPAD_DPAD_LEFT) != 0; load |= (b & XINPUT_GAMEPAD_DPAD_RIGHT) != 0;
							}
						}
			}
			if (save && !prev_save) g_offset_req = 1;
			if (load && !prev_load) g_offset_req = 2;
			prev_save = save; prev_load = load;
		}
		void draw_toast()
		{
			if (ImGui::GetTime() > g_toast_until || g_toast.empty()) return;
			const ImGuiIO& io = ImGui::GetIO();
			const ImVec2 ts = ImGui::CalcTextSize(g_toast.c_str());
			const ImVec2 p(io.DisplaySize.x * 0.5f - ts.x * 0.5f, io.DisplaySize.y * 0.12f);
			ImDrawList* dl = ImGui::GetForegroundDrawList();
			dl->AddRectFilled(ImVec2(p.x - 10, p.y - 6), ImVec2(p.x + ts.x + 10, p.y + ts.y + 6), IM_COL32(10, 20, 30, 200), 6.f);
			dl->AddText(p, IM_COL32(140, 215, 255, 255), g_toast.c_str());
		}
	}

	/* ---- out-of-bounds / kill volume death bar ----
	   Two ways the game kills you outside the level (halo2.exe, found in MCC first and matched here):
	   OUT OF BOUNDS (player update 0x458CC6): the unit's physics point is tested against solid collision
	     (sub_53DD81). Counter = byte player+0x3A: +1 per tick inside solid, reset to 0 the first tick it is not. While
	     it is 0 the test only runs on ticks where (game_time + player index) % 16 == 0. Killed when the counter passes
	     round(0.5 s * ticks/s) = 15, i.e. on the 16th tick in a row.
	   KILL VOLUMES (unit update -> sub_4B3B0A): ONE kill volume is tested per tick, in rotation:
	     (game_time + (unit index & 0xFFFF)) % count. Inside an enabled one, you die on its turn.
	   The bar shows whichever comes first, full / green draining to red, with what it is and the ticks left. */
	namespace
	{

		typedef bool(__cdecl* t_trigger_volume_test)(int32 trigger_volume, datum object);
		int trigger_volume_test(int16 trigger, datum object)
		{
			__try { return ((t_trigger_volume_test)addr(0x27E58))(trigger, object) ? 1 : 0; }   // halo2.exe 0x427E58
			__except (EXCEPTION_EXECUTE_HANDLER) { return -1; }
		}

		void update_death_state()
		{
			s_death_state d;
			const datum pi = player_index_from_user_index(0);
			const player_datum* player = pi != NONE ? (const player_datum*)datum_get(player_data_get(), pi) : nullptr;
			if (!player || player->unit_index == NONE) { g_death = d; return; }
			const datum unit = player->unit_index;
			const uintptr_t time_globals = u32(addr(0x4C06E4));                    // game time globals
			const uint32 tick = okp(time_globals) ? u32(time_globals + 8) : 0;
			int tps = okp(time_globals) ? (int)*(const int16*)(time_globals + 2) : 30;
			if (tps <= 0 || tps > 120) tps = 30;
			d.valid = true;
			d.player_index = DATUM_INDEX_TO_ABSOLUTE_INDEX(pi);
			d.oob_counter = *((const uint8*)player + 0x3A);
			d.oob_limit = (int)std::lround(tps * 0.5f);                          // sub_47C0DB (fistp, nearest)
			d.oob_next_check = (int)((16u - ((tick + (uint32)d.player_index) & 15u)) & 15u);

			int best = INT32_MAX;
			auto offer = [&](int left, int period, const char* what)
			{
				if (left < 0 || period <= 0 || left >= best) return;
				best = left;
				d.bar = std::clamp((float)left / (float)period, 0.f, 1.f);
				snprintf(d.text, sizeof(d.text), "%s - %d ticks", what, left);
			};
			if (d.oob_counter > 0) offer(d.oob_limit + 1 - d.oob_counter, d.oob_limit + 1, "OUT OF BOUNDS");

			// kill volumes: scenario (*0x879E74) +0x230 count / +0x234 offset of the int16 trigger volume list (tag
			// data base *0x882290); disabled bits at *0x8D2AB0 (bit set = disabled by script)
			const uintptr_t scen = u32(addr(0x479E74)), tag_base = u32(addr(0x482290));
			if (okp(scen) && okp(tag_base))
			{
				const int32 count = *(const int32*)(scen + 0x230), off = *(const int32*)(scen + 0x234);
				const uintptr_t bits = u32(addr(0x4D2AB0));
				if (count > 0 && count < 4096 && off != -1)
				{
					const int16* list = (const int16*)(tag_base + (uint32)off);
					d.kv_count = count;
					d.kv_checking = (int)((tick + (unit & 0xFFFF)) % (uint32)count);
					for (int k = 0; k < count; ++k)
					{
						const bool enabled = !okp(bits) || ((u32(bits + 4 * (k >> 5)) >> (k & 31)) & 1) == 0;
						if (!enabled) continue;
						++d.kv_enabled;
						const int16 trigger = list[k];
						if (trigger < 0 || trigger_volume_test(trigger, unit) != 1) continue;
						const int64_t r = ((int64_t)k - (int64_t)tick - (int64_t)(unit & 0xFFFF)) % count;
						const int ticks = (int)(r < 0 ? r + count : r);
						d.kv_inside.push_back({ k, ticks });
						char what[32]; snprintf(what, sizeof(what), "KILL VOLUME #%d", k);
						offer(ticks, count, what);
					}
				}
			}
			g_death = d;
		}

		void draw_death_bar()
		{
			if (g_death.bar < 0.f) return;
			const ImGuiIO& io = ImGui::GetIO();
			ImDrawList* dl = ImGui::GetForegroundDrawList();
			const float w = (std::max)(220.f, io.DisplaySize.x * 0.28f), h = (std::max)(14.f, io.DisplaySize.y * 0.018f);
			const ImVec2 a(io.DisplaySize.x * 0.5f - w * 0.5f, io.DisplaySize.y * 0.30f), b(a.x + w, a.y + h);
			const float f = g_death.bar;
			const ImU32 fill = IM_COL32((int)(255.f * (1.f - f)), (int)(220.f * f + 35.f * (1.f - f)), 40, 235);
			dl->AddRectFilled(ImVec2(a.x - 3, a.y - 3), ImVec2(b.x + 3, b.y + 3), IM_COL32(0, 0, 0, 170), 4.f);
			dl->AddRectFilled(a, ImVec2(a.x + w * f, b.y), fill, 3.f);
			dl->AddRect(a, b, IM_COL32(255, 255, 255, 120), 3.f, 0, 1.5f);
			if (g_death.text[0])
			{
				const ImVec2 ts = ImGui::CalcTextSize(g_death.text);
				const ImVec2 tp(io.DisplaySize.x * 0.5f - ts.x * 0.5f, a.y - ts.y - 6.f);
				dl->AddRectFilled(ImVec2(tp.x - 4, tp.y - 2), ImVec2(tp.x + ts.x + 4, tp.y + ts.y + 2), IM_COL32(0, 0, 0, 170), 3.f);
				dl->AddText(tp, fill | 0xFF000000u, g_death.text);
			}
		}
	}

	void draw_overlay(void)
	{
		++g_frame_counter;
		apply_practice_toggles();
		poll_offset_shortcuts();
		draw_toast();
		if (g_offset_req && (!g_settings.enabled || !game_in_progress()))
		{
			offset_toast("Save / Load Offsets needs the Ghost viewer on, in a game");
			g_offset_req = 0;
		}
		{
			// a request that no player frame picked up (no physics pair at the moment, e.g. standing still) is dropped
			// after a second instead of firing later, unexpectedly
			static int pending = 0;
			if (g_offset_req) { if (++pending > 60) { offset_toast("Save / Load Offsets: no player physics pair right now - move and try again"); g_offset_req = 0; pending = 0; } }
			else pending = 0;
		}
		for (auto& g : g_info) g = s_info{};
		if (!game_in_progress()) { g_death = s_death_state{}; return; }
		// the death bar works on its own (it only needs the game running, not the Ghost viewer)
		if (g_settings.oob_bar && !game_time_get_paused() && !cinematic_in_progress()) { update_death_state(); draw_death_bar(); }
		else g_death = s_death_state{};
		if (!g_settings.enabled || game_time_get_paused() || cinematic_in_progress()) return;   // nothing while paused / in menus / in cutscenes


		const uintptr_t world = u32(addr(k_world_ptr));
		if (!okp(world)) return;
		// stand down for a moment whenever the physics world or the BSP changes (level start, restart, BSP switch):
		// nothing is read or called into while the engine tears down and rebuilds it
		{
			static uintptr_t s_world = 0; static const void* s_bsp = nullptr; static int s_quiet = 0;
			const void* bsp = global_structure_bsp_get();
			if (world != s_world || bsp != s_bsp) { s_world = world; s_bsp = bsp; s_quiet = 30; for (auto& p : g_players) p = s_player_state{}; }
			if (s_quiet > 0) { --s_quiet; return; }
		}
		const uintptr_t env = u32(addr(k_havok_globals) + 4);
		static std::vector<uintptr_t> islands;
		static std::vector<s_pair> pairs;
		collect_islands(world, islands);
		collect_pairs(islands, pairs);

		int32 count = 0;
		for (int32 u = 0; u < 4; ++u) if (players_user_is_active(u)) ++count;
		int32 slot = 0;
		for (int32 u = 0; u < 4; ++u)
		{
			if (!players_user_is_active(u)) continue;
			if (set_view_for_user(u, slot, count)) draw_player(u, world, env, pairs);
			else g_info[u].note = "no camera for this player";
			++slot;
		}

		if (g_settings.info_panel) draw_info_panel(world);
	}

	void render_settings_ui(void)
	{
		s_settings& s = g_settings;
		auto color_edit = [](const char* label, int* rgb)
		{
			float c[3] = { ((*rgb >> 16) & 0xFF) / 255.f, ((*rgb >> 8) & 0xFF) / 255.f, (*rgb & 0xFF) / 255.f };
			if (ImGui::ColorEdit3(label, c, ImGuiColorEditFlags_NoInputs))
				*rgb = ((int)(c[0] * 255.f + 0.5f) << 16) | ((int)(c[1] * 255.f + 0.5f) << 8) | (int)(c[2] * 255.f + 0.5f);
		};
		auto tip = [](const char* t) { if (ImGui::IsItemHovered()) ImGui::SetTooltip("%s", t); };

		if (!ImGui::CollapsingHeader("Ghost / TIM Viewer")) return;
		ImGui::Checkbox("Third person camera", &s.third_person);
		tip("Moves your view behind your character (render camera only: aiming and physics are unchanged). Works with or without the ghost viewer.");
		ImGui::SameLine(); ImGui::Checkbox("Disable AI", &s.disable_ai);
		tip("Freezes all AI (same as 'ai_enable false'): actors stop moving, perceiving and shooting. Local campaign only.");
		ImGui::SameLine(); ImGui::Checkbox("Invulnerability", &s.invulnerable);
		tip("Your unit cannot take damage (same as 'object_cannot_take_damage'). Local campaign only; undone when unticked.");
		if (s.third_person)
		{
			ImGui::SliderInt("Distance (mwu)", &s.tp_distance_mwu, 0, 4000);
			ImGui::SliderInt("Height (mwu)", &s.tp_height_mwu, -1000, 2000);
			ImGui::SliderInt("Side (mwu)", &s.tp_side_mwu, -1500, 1500);
		}
		ImGui::Separator();
		ImGui::Checkbox("Ghost viewer", &s.enabled);
		tip("Your Havok capsule: pink at rest / honest, lime while a backstep, its hold or an offset TIM is active, red when stuck (S = -3). The options below appear when this is ticked.");
		if (!s.enabled) { ImGui::NewLine(); return; }
		ImGui::Indent();

		auto section = [](const char* name) { ImGui::Spacing(); ImGui::TextDisabled("%s", name); ImGui::Separator(); };

		section("Player");
		ImGui::Checkbox("Out-of-bounds timer bar", &s.oob_bar);
		tip("An on-screen bar for whatever will kill you first outside the level: the out-of-bounds count (your body inside solid / outside the level; 16 ticks in a row kill, and the first check only comes on every 16th tick) or the turn of a kill volume you are inside (one volume is checked per tick, in rotation). Full / green draining to red, labelled OUT OF BOUNDS or KILL VOLUME #k with the ticks left. Works without the Ghost viewer; the info panel adds the numbers.");
		ImGui::Checkbox("Backstep rewind poses", &s.rewind);
		tip("Yellow = where the last backstep put you back to, orange = where you were before it.");
		ImGui::Checkbox("Pass-through prediction", &s.pass_through);
		tip("Flashes (green) every welded polygon / object piece your current offset lets you pass through. The TIM is spent linearly (n . dp per move, whatever the path); you pass when it still has some left once your capsule is fully over the surface and fully past its plane (object pieces: your centre past the piece's middle along the TIM normal). Amber: you get through, but not at your current speed. Only offsets above the offset threshold count. The info panel lists the numbers per offset polygon.");
		ImGui::Checkbox("Believed pose distances", &s.link_labels);
		tip("Label each believed pose's link line (level and object) with its over-credit in world units.");

		section("Level");
		ImGui::Checkbox("Level TIMs", &s.tim_overlay);
		tip("Every level polygon in your welder: green = skipped with an honest TIM, red (heavy) = offset, yellow = in contact.");
		ImGui::Checkbox("Level believed poses", &s.believed);
		tip("Where each over-credited level TIM believes you are: your capsule moved back along the polygon normal by the over-credit.");
		ImGui::Checkbox("Level travel regions", &s.travel);
		tip("Per over-credited polygon (up to 6): the zone your centre (white cross) must stay inside, and the red sheet it must stay short of, for the offset to survive.");
		ImGui::Checkbox("Weld zones", &s.weld_zones);
		tip("Every level polygon's zone near you: its box grown by your capsule's half-size + 1.5 x tolerance. Green = welded now (it has a TIM), blue = near.");
		if (s.weld_zones) { ImGui::Indent(); ImGui::SliderInt("Weld zone range (mwu)", &s.weld_range_mwu, 0, 5000); ImGui::Unindent(); }
		ImGui::Checkbox("Desync edges", &s.edges);
		tip("Thick outline on level polygons whose TIM disagrees with the real distance.");
		if (s.edges) { ImGui::Indent(); ImGui::Checkbox("Offset polygons only", &s.edges_suspect_only); ImGui::Unindent(); }

		section("Objects");
		ImGui::Checkbox("Object TIMs", &s.obj_tims);
		tip("Each piece of an object paired with you (crates, doors, machines, vehicles, other bipeds) that holds a TIM, outlined: blue-gray = honest, red (heavy) = offset, yellow = in contact.");
		ImGui::Checkbox("Object believed poses", &s.obj_believed);
		tip("An orange capsule where each over-credited object TIM believes you are (moved by its over-credit). Kept while the object is asleep and you have not moved.");
		ImGui::Checkbox("Object travel regions", &s.travel_objects);
		tip("Per over-credited object piece: its weld zone (approximate: piece box grown by your capsule + welder margin) and the red reset sheet.");

		if (s.tim_overlay || s.obj_tims)
		{
			section("Labels");
			ImGui::Checkbox("TIM distance lines", &s.tim_labels);
			tip("For every skipped polygon / object piece: a line from your capsule toward it, as long as its TIM, labeled in world units. Its end is where that TIM believes the surface is ('!' = offset).");
		}

		section("Thresholds");
		ImGui::SliderInt("Offset threshold (um)", &s.over_min_um, 0, 200000);
		tip("A TIM counts as offset (red, heavy lines, lime capsule, logged) when its over-credit exceeds this, in millionths of a world unit (80000 = 0.08 wu).");
		if (s.believed || s.obj_believed || s.travel || s.travel_objects)
		{
			ImGui::SliderInt("Believed / travel threshold (um)", &s.show_min_um, 0, 200000);
			tip("Believed poses and travel regions are drawn for TIMs whose over-credit exceeds this (5000 = 0.005 wu), independently of the offset threshold.");
		}
		if (s.believed || s.obj_believed) ImGui::SliderInt("Max believed poses", &s.believed_max, 1, 16);
		ImGui::SliderInt("Backstep hold (ticks)", &s.hold_ticks, 0, 60);
		tip("How long the capsule stays lime (and the rewind poses stay up) after a backstep.");

		section("Offset save state");
		if (ImGui::Button("Save Offsets (+ checkpoint)")) g_offset_req = 1;
		tip("Snapshots every TIM you hold (level polygons and object pieces, offsets included), then makes a checkpoint the normal way - the checkpoint stores the objects. When the checkpoint has rebuilt your physics pairs the snapshot is written back, so you keep your offsets.");
		ImGui::SameLine();
		if (ImGui::Button("Load Offsets (revert)")) g_offset_req = 2;
		tip("Reverts to that checkpoint the normal way, waits for your physics pairs, checks you are where the offsets were saved and writes the saved TIMs back. If a newer checkpoint replaced it, nothing is written.");
		{
			static const char* keys[] = { "None", "F1", "F2", "F3", "F4", "F5", "F6", "F7", "F8", "F9", "F10", "F11", "F12", "Insert", "Delete", "Home", "End", "Page Up", "Page Down" };
			static const int vks[] = { 0, VK_F1, VK_F2, VK_F3, VK_F4, VK_F5, VK_F6, VK_F7, VK_F8, VK_F9, VK_F10, VK_F11, VK_F12, VK_INSERT, VK_DELETE, VK_HOME, VK_END, VK_PRIOR, VK_NEXT };
			auto key_combo = [&](const char* label, int* vk)
			{
				int idx = 0;
				for (int i = 0; i < IM_ARRAYSIZE(vks); ++i) if (vks[i] == *vk) idx = i;
				ImGui::SetNextItemWidth(110);
				if (ImGui::Combo(label, &idx, keys, IM_ARRAYSIZE(keys))) *vk = vks[idx];
			};
			key_combo("Save key", &s.key_offset_save); ImGui::SameLine();
			key_combo("Load key", &s.key_offset_load);
			static const char* pads[] = { "None", "Back + D-pad Left / Right", "Back + LB / RB", "Left stick click + D-pad Left / Right" };
			ImGui::SetNextItemWidth(260);
			ImGui::Combo("Controller (save / load)", &s.pad_offset, pads, IM_ARRAYSIZE(pads));
			ImGui::Checkbox("Restore offsets after natural reverts too", &s.offset_natural_reverts);
			tip("Off: only Load Offsets restores them; dying or reverting from the pause menu resets them like normal. On: any revert that puts you back where the offsets were saved restores them.");
			tip("Controller shortcut: hold the first button and press the second - left side saves, right side loads.");
		}

		section("Logging");
		ImGui::Checkbox("Info panel", &s.info_panel);
		tip("The on-screen panel with tolerances, pair / TIM counts, over-credit, travel rows and diagnostics.");
		ImGui::Checkbox("Desync logger", &s.logger);
		tip("Appends to GhostViewerLog.csv next to halo2.exe: every backstep rewind (distance, from/to, S) and every offset episode (start with TIM and over-credit, end with its peak), for level polygons and objects.");

		ImGui::Spacing();
		if (ImGui::TreeNode("Colors"))
		{
			ImGui::TextDisabled("Capsule");
			color_edit("Normal", &s.col_normal); ImGui::SameLine();
			color_edit("Desync", &s.col_desync); ImGui::SameLine();
			color_edit("Stuck", &s.col_stuck);
			ImGui::TextDisabled("Backstep");
			color_edit("Rewind target", &s.col_rewind_to); ImGui::SameLine();
			color_edit("Pre-rewind", &s.col_rewind_from);
			ImGui::TextDisabled("TIMs");
			color_edit("Honest", &s.col_tim_ok); ImGui::SameLine();
			color_edit("Offset", &s.col_tim_suspect); ImGui::SameLine();
			color_edit("Contact", &s.col_tim_contact); ImGui::SameLine();
			color_edit("Object pieces", &s.col_obj_box);
			ImGui::TextDisabled("Believed poses / travel");
			color_edit("Level believed", &s.col_believed); ImGui::SameLine();
			color_edit("Object believed", &s.col_obj_believed); ImGui::SameLine();
			color_edit("Reset sheet", &s.col_sheet); ImGui::SameLine();
			color_edit("Pass-through", &s.col_pass);
			ImGui::TreePop();
		}
		ImGui::Unindent();
		ImGui::NewLine();
	}
}
#else
namespace GhostViewer
{
	s_settings g_settings;
	void draw_overlay(void) {}
	void render_settings_ui(void) {}
	s_observer_result* camera_override(int32, s_observer_result* camera) { return camera; }
	bool third_person_active(void) { return false; }
	void capture_view(int32, const s_frame*) {}
	void apply_patches(void) {}
}
#endif

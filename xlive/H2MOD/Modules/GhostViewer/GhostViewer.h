#pragma once

// Ghost / TIM viewer (ported from the HCM Halo 2 collision viewer, MCC halo2.dll -> Halo 2 Vista halo2.exe)
//
// Shows, for every local player on foot, the Havok state behind "ghosting":
//   - the player's Havok capsule ("ghost pill"), coloured by backstep / desync state, plus the backstep rewind target
//   - the level-welder children around the capsule with their cached TIMs ("TIM overlay", values in world units)
//   - believed poses: where each over-credited TIM thinks the player is, with the over-credit in world units
//   - ghost travel regions: per over-credited polygon, the weld zone the capsule centre must stay inside and the reset
//     sheet it must stay short of for the offset to survive
//   - an info panel with the per-player numbers and the world's backstep parameters
//
// Everything is read-only: the viewer only reads game memory and draws on ImGui's background layer.

struct s_observer_result;
struct s_frame;

namespace GhostViewer
{
	struct s_settings
	{
		bool enabled = false;            // master switch: ghost pill + everything below
		bool rewind = true;              // backstep rewind target / pre-rewind pose
		bool tim_overlay = true;         // welder children polygons
		bool tim_labels = true;          // TIM value (wu) on each child polygon
		bool believed = true;            // believed poses
		bool link_labels = false;         // over-credit (wu) on the believed-pose link lines
		bool edges = true;               // desync edges (thick outline on suspect polygons)
		bool edges_suspect_only = true;
		bool travel = true;              // ghost travel regions (level)
		bool info_panel = true;
		int believed_max = 6;
		int show_min_um = 5000;        // believed poses / travel regions shown above this over-credit, micro wu (5000 = 0.005 wu)
		int over_min_um = 80000;       // offset threshold: a TIM is offset (red, heavy) when its over-credit exceeds this, micro wu (80000 = 0.08 wu)
		int hold_ticks = 8;            // ticks a backstep keeps the pill lime / the rewind target shown
		// colours, 0xRRGGBB
		int col_normal = 0xFF69B4;     // pink: nothing suspect
		int col_desync = 0xAAFF00;     // lime: backstep / hold / suspect child
		int col_stuck = 0xFF2020;      // red: S = -3
		int col_believed = 0x00E0FF;   // believed poses
		int col_rewind_to = 0xFFE600;  // rewind target
		int col_rewind_from = 0xFF5A00;// pre-rewind pose
		int col_tim_ok = 0x80FF80;     // skipped child, honest TIM
		int col_tim_suspect = 0xFF3030;// skipped child, over-credited / stale
		int col_tim_contact = 0xFFFF80;// child in contact
		int col_sheet = 0xFF2828;      // travel region reset sheet
		bool obj_tims = true;             // TIMs against objects (boxes of each convex piece)
		bool obj_believed = true;         // believed poses against objects
		bool travel_objects = false;      // travel regions for object pieces (approximate)
		bool weld_zones = false;          // level polygon weld zones near you
		int weld_range_mwu = 1000;        // weld zone draw range, thousandths of a wu
		bool logger = false;              // CSV desync logger
		bool pass_through = true;         // flash welded geometry you would pass through
		int col_pass = 0x20FF40;          // pass-through (flashing green)
		int key_offset_save = 0x74;       // Save Offsets key (VK_F5)
		int key_offset_load = 0x75;       // Load Offsets key (VK_F6)
		bool offset_natural_reverts = false;  // also restore saved offsets after natural reverts to that checkpoint
		int pad_offset = 1;               // controller shortcut: 0 none, 1 Back + D-pad L/R, 2 Back + LB/RB, 3 LS click + D-pad L/R
		int col_obj_box = 0x9090FF;       // object piece box (skipped, honest)
		int col_obj_believed = 0xFFA000;  // believed poses (objects)
		// third person camera (render camera only; aiming / physics are unchanged)
		bool third_person = false;
		bool disable_ai = false;          // practice: freeze all AI (local campaign only)
		bool invulnerable = false;        // practice: your unit cannot take damage (local campaign only)
		int tp_distance_mwu = 1000;    // behind the eye, thousandths of a world unit (1000 = 1.0 wu)
		int tp_height_mwu = 150;       // above the eye
		int tp_side_mwu = 0;           // to the right (+) / left (-)
	};

	extern s_settings g_settings;

	// call once per frame between ImGui::NewFrame() and ImGui::Render()
	void draw_overlay(void);

	// the "Ghost / TIM Viewer" section of Advanced Settings (its own collapsing header, under Game Settings)
	void render_settings_ui(void);

	// third person: main_render passes each player's camera through this before building the render camera.
	// Returns `camera` unchanged when third person is off, otherwise a per-user copy moved behind the player.
	s_observer_result* camera_override(int32 user_index, s_observer_result* camera);

	// called from the HUD pass (interface_draw_screen) with the frame parameters of the player being drawn: the exact
	// camera and projection that player's view was rendered with
	void capture_view(int32 user_index, const s_frame* frame);

	// true while the third person camera is on and a game is running (camera effects are skipped then)
	bool third_person_active(void);

	// installs the director-perspective hook (call inside the DETOUR_BEGIN / DETOUR_COMMIT block, client only)
	void apply_patches(void);
}

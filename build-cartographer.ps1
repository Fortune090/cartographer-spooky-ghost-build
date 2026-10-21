<#
.SYNOPSIS
    Builds Project Cartographer's xlive.dll (release_msvc | Win32) and optionally installs it into your Halo 2 folder.

.PARAMETER Patch
    A .patch to apply first (git diff format, paths starting with xlive\). Skipped if already applied. Needs git.

.PARAMETER DeployTo
    Your Halo 2 folder (the one with halo2.exe). The built xlive.dll is copied there; the old one is renamed to
    xlive.dll.bak-<yyyyMMdd-HHmmss> first.

.PARAMETER Toolset
    Force a C++ toolset (e.g. v145). By default v143 is used if this MSBuild has it, otherwise the newest one it has.

.EXAMPLE
    .\build-cartographer.ps1 -Patch .\cartographer-ghost-viewer.patch -DeployTo "C:\Games\Halo 2"
#>
param(
    [string]$Patch,
    [string]$DeployTo,
    [string]$Toolset,
    [string]$Configuration = 'release_msvc'
)
$ErrorActionPreference = 'Stop'
function Fail($m) { Write-Host "`nBUILD ABORTED: $m" -ForegroundColor Red; exit 1 }

# find the repo root (the folder with Project_Cartographer.sln): the current folder, the script's folder, or a parent of either
$repo = $null
foreach ($start in @((Get-Location).Path, $PSScriptRoot)) {
    $d = $start
    while ($d) {
        if (Test-Path (Join-Path $d 'Project_Cartographer.sln')) { $repo = $d; break }
        $parent = Split-Path $d -Parent
        if ($parent -eq $d) { break }
        $d = $parent
    }
    if ($repo) { break }
}
if (-not $repo) { Fail ("Project_Cartographer.sln not found from '{0}' or '{1}' (or any parent folder) - run this inside the Cartographer source folder" -f (Get-Location).Path, $PSScriptRoot) }
Write-Host "repo: $repo" -ForegroundColor DarkGray
$proj = Join-Path $repo 'xlive\Project_Cartographer.vcxproj'
if (-not (Test-Path $proj)) { Fail "xlive\Project_Cartographer.vcxproj not found under $repo" }

if ($DeployTo) {
    $running = Get-Process -Name halo2 -ErrorAction SilentlyContinue
    if ($running) { Fail "close Halo 2 first (xlive.dll is in use)" }
}

# ---- patch ---------------------------------------------------------------------------------------
if ($Patch) {
    if (-not (Get-Command git -ErrorAction SilentlyContinue)) { Fail "-Patch needs git on PATH" }
    if (-not (Test-Path $Patch)) { Fail "patch not found: $Patch" }
    $pp = (Resolve-Path $Patch).Path
    Push-Location $repo
    $eap = $ErrorActionPreference; $ErrorActionPreference = 'Continue'
    try {
        & git apply --reverse --check --ignore-whitespace $pp 2>$null
        if ($LASTEXITCODE -eq 0) { Write-Host "[patch] already applied - skipping" -ForegroundColor DarkGray }
        else {
            $ok = $false
            foreach ($o in @(@(), @('--ignore-whitespace'), @('--3way', '--ignore-whitespace'))) {
                & git apply --check @o $pp 2>$null
                if ($LASTEXITCODE -eq 0) { & git apply @o $pp; if ($LASTEXITCODE -eq 0) { $ok = $true; break } }
            }
            if (-not $ok) { & git apply --check --ignore-whitespace $pp; Fail "patch does not apply (see above)" }
            Write-Host "[patch] applied" -ForegroundColor Green
        }
    } finally { $ErrorActionPreference = $eap; Pop-Location }
}

# ---- DirectX June 2010 SDK (Cartographer includes d3dx9.h from it via $(DXSDK_DIR)) -------------------
$dx = $env:DXSDK_DIR
if (-not $dx) {
    foreach ($c in @("${env:ProgramFiles(x86)}\Microsoft DirectX SDK (June 2010)\", "$env:ProgramFiles\Microsoft DirectX SDK (June 2010)\")) {
        if (Test-Path (Join-Path $c 'Include\d3dx9.h')) { $dx = $c; break }
    }
}
if (-not $dx -or -not (Test-Path (Join-Path $dx 'Include\d3dx9.h'))) {
    Fail ("the DirectX June 2010 SDK is missing (d3dx9.h). Install it from https://www.microsoft.com/en-us/download/details.aspx?id=6812 " +
          "and open a NEW PowerShell window afterwards. If its installer ends with error S1023, the SDK files are still installed - that " +
          "error is only its VC++ 2010 redistributable step.")
}
if (-not $dx.EndsWith('\')) { $dx += '\' }
$env:DXSDK_DIR = $dx
Write-Host "DirectX SDK: $dx" -ForegroundColor DarkGray

# ---- MSBuild + toolset -----------------------------------------------------------------------------
$vswhere = "${env:ProgramFiles(x86)}\Microsoft Visual Studio\Installer\vswhere.exe"
if (-not (Test-Path $vswhere)) { Fail "vswhere not found - install Visual Studio Build Tools with 'Desktop development with C++'" }
$msbuild = & $vswhere -latest -products * -requires Microsoft.Component.MSBuild -find MSBuild\**\Bin\MSBuild.exe | Select-Object -First 1
if (-not $msbuild) { Fail "MSBuild not found" }
$vsRoot = $msbuild.Substring(0, $msbuild.IndexOf('\MSBuild\', [StringComparison]::OrdinalIgnoreCase))
$vcDir = Get-ChildItem (Join-Path $vsRoot 'MSBuild\Microsoft\VC') -Directory -Filter 'v*' -ErrorAction SilentlyContinue |
         Sort-Object { [int]($_.Name.TrimStart('v')) } -Descending | Select-Object -First 1
$toolsets = @()
if ($vcDir) {
    # Cartographer is 32-bit: look at the Win32 toolsets
    $toolsets = @(Get-ChildItem (Join-Path $vcDir.FullName 'Platforms\Win32\PlatformToolsets') -Directory -ErrorAction SilentlyContinue |
                  Where-Object { $_.Name -match '^v\d+$' } | ForEach-Object { $_.Name } | Sort-Object { [int]($_.TrimStart('v')) } -Descending)
}
Write-Host "MSBuild: $msbuild" -ForegroundColor DarkGray
Write-Host ("Win32 toolsets it can use: {0}" -f $(if ($toolsets) { $toolsets -join ', ' } else { '(none found)' })) -ForegroundColor DarkGray
if (-not $Toolset -and $toolsets.Count -gt 0 -and $toolsets -notcontains 'v143') { $Toolset = $toolsets[0]; Write-Host "v143 not usable - building with $Toolset" -ForegroundColor Yellow }
$extra = @()
if ($Toolset) { $extra += "/p:PlatformToolset=$Toolset" }

# ---- build -------------------------------------------------------------------------------------------
$started = Get-Date
Write-Host "[build] xlive ($Configuration | Win32) ..." -ForegroundColor Cyan
# build the solution, not just xlive: xlive links imguilib / tinyxmllib / zlib, which are separate projects in it
$sln = Join-Path $repo 'Project_Cartographer.sln'
& $msbuild $sln "/p:Configuration=$Configuration" /p:Platform=x86 /m /nologo /v:minimal @extra
if ($LASTEXITCODE -ne 0) { Fail "build failed - the first 'error' line above is the one to look at" }

$dll = Join-Path $repo 'Halo2\xlive.dll'
if (-not (Test-Path $dll)) { Fail "build reported success but $dll is missing" }
$item = Get-Item $dll
Write-Host ("built {0}  {1:N0} bytes  {2}" -f $item.FullName, $item.Length, $item.LastWriteTime) -ForegroundColor DarkGray
if ($item.LastWriteTime -lt $started.AddSeconds(-5)) { Write-Host "note: xlive.dll was up to date (not relinked)" -ForegroundColor DarkGray }

if ($DeployTo) {
    if (-not (Test-Path $DeployTo -PathType Container)) { Fail "folder not found: $DeployTo" }
    $dst = Join-Path $DeployTo 'xlive.dll'
    if (Test-Path $dst) {
        $bak = "xlive.dll.bak-$(Get-Date -Format 'yyyyMMdd-HHmmss')"
        Rename-Item $dst $bak
        Write-Host "backed up old xlive.dll -> $bak" -ForegroundColor DarkGray
    }
    Copy-Item $dll $dst -Force
    Write-Host "[deploy] xlive.dll -> $DeployTo" -ForegroundColor Green
}
Write-Host "`nOK" -ForegroundColor Green

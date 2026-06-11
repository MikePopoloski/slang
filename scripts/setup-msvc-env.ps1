#!/usr/bin/env pwsh
# Locate the latest Visual Studio installation with vswhere, initialize the
# MSVC build environment by running the appropriate vcvars batch file, and
# export the resulting environment variables to GITHUB_ENV so that subsequent
# workflow steps (CMake configure, build and test) can find the compiler,
# linker and Windows SDK without relying on a hardcoded install path.
#
# SPDX-FileCopyrightText: Michael Popoloski
# SPDX-License-Identifier: MIT

[CmdletBinding()]
param(
    [ValidateSet('x64', 'arm64')]
    [string]$Arch = 'x64'
)

$ErrorActionPreference = 'Stop'

$vcvarsName = if ($Arch -eq 'arm64') { 'vcvarsarm64.bat' } else { 'vcvars64.bat' }

# vswhere ships with the Visual Studio installer at this fixed, documented path.
$vswhere = Join-Path ${env:ProgramFiles(x86)} 'Microsoft Visual Studio\Installer\vswhere.exe'
if (-not (Test-Path -LiteralPath $vswhere)) {
    throw "vswhere.exe was not found at '$vswhere'"
}

$installPath = & $vswhere -latest -products * -property installationPath | Select-Object -First 1
if ([string]::IsNullOrWhiteSpace($installPath)) {
    throw 'vswhere did not locate any Visual Studio installation'
}

$vcvars = Join-Path $installPath "VC\Auxiliary\Build\$vcvarsName"
if (-not (Test-Path -LiteralPath $vcvars)) {
    throw "Could not find '$vcvarsName' at '$vcvars'"
}

Write-Host "Using Visual Studio installation: $installPath"
Write-Host "Initializing MSVC environment for $Arch with $vcvarsName"

# Snapshot the environment as cmd sees it before and after running vcvars so we
# can export only the variables that vcvars actually added or modified.
$before = @{}
foreach ($line in (cmd /c 'set')) {
    if ($line -match '^([^=]+)=(.*)$') { $before[$matches[1]] = $matches[2] }
}

$after = @{}
foreach ($line in (cmd /c "`"$vcvars`" >nul && set")) {
    if ($line -match '^([^=]+)=(.*)$') { $after[$matches[1]] = $matches[2] }
}
if ($LASTEXITCODE -ne 0) {
    throw "Failed to initialize the MSVC environment (vcvars exited with code $LASTEXITCODE)"
}

$changes = [System.Collections.Generic.List[string]]::new()
foreach ($entry in $after.GetEnumerator()) {
    if (-not $before.ContainsKey($entry.Key) -or $before[$entry.Key] -ne $entry.Value) {
        $changes.Add("$($entry.Key)=$($entry.Value)")
    }
}

if ($env:GITHUB_ENV) {
    # Append without a BOM so GitHub Actions parses every entry correctly.
    [System.IO.File]::AppendAllLines($env:GITHUB_ENV, $changes, [System.Text.UTF8Encoding]::new($false))
    Write-Host "Exported $($changes.Count) environment variable(s) to GITHUB_ENV"
}
else {
    Write-Host 'GITHUB_ENV is not set; the following variables would be exported:'
    $changes | ForEach-Object { Write-Host "  $_" }
}

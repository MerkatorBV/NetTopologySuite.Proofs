#requires -Version 5
# SqlMmFactoryHunt — .NET hunter for SqlMmExampleFactory vs C# WktIntakeWalker μ.
# House style: $ErrorActionPreference='Stop'; factory stays Java; intake is C# CLI.
# claimId: none (tools). No new ADR-0006 keyword. Rocq emit stays QEX.
#
#   pwsh ./tests/SqlMmFactoryHunt/hunt.ps1 -Budget 300 -Seed 42
#   dotnet cake --target=SqlMmFactoryHunt --budget=300 --seed=42
#
# This script was drafted with AI assistance; human review remains required.

[CmdletBinding()]
param(
    [int]$Budget = 300,
    [int]$Seed = 42,
    [switch]$PinsOnly,
    [switch]$SkipBuild
)

$ErrorActionPreference = 'Stop'
if ($PSVersionTable.PSVersion.Major -ge 7) {
    $PSNativeCommandUseErrorActionPreference = $true
}

$here = $PSScriptRoot
$repo = (Resolve-Path (Join-Path $here '../..')).Path
$factory = Join-Path $repo 'tools/SqlMmExampleFactory'
$intake = Join-Path $repo 'tools/WktIntakeWalker'
$proj = Join-Path $here 'SqlMmFactoryHunt.csproj'
$intakeProj = Join-Path $intake 'WktIntakeWalker.csproj'

function Find-DotNet {
    if (Get-Command dotnet -ErrorAction SilentlyContinue) {
        return (Get-Command dotnet).Source
    }
    foreach ($c in @(
            (Join-Path $env:HOME '.dotnet/dotnet'),
            (Join-Path $env:USERPROFILE '.dotnet\dotnet'),
            '/usr/share/dotnet/dotnet'
        )) {
        if ($c -and (Test-Path $c)) {
            $root = Split-Path $c
            $env:DOTNET_ROOT = $root
            $env:PATH = "$root$([IO.Path]::PathSeparator)$env:PATH"
            return $c
        }
    }
    throw "dotnet not found. Install the .NET 10 SDK (same TFM as tests/CurveOracleBugHunt)."
}

function Invoke-Bash([string]$Script) {
    $bash = Get-Command bash -ErrorAction SilentlyContinue
    if (-not $bash) {
        foreach ($c in @(
                'C:\Program Files\Git\bin\bash.exe',
                'C:\Windows\System32\bash.exe'
            )) {
            if (Test-Path $c) { $bash = @{ Source = $c }; break }
        }
    }
    if (-not $bash) {
        throw "bash not found (needed for tools/SqlMmExampleFactory/generate.sh)."
    }
    & $bash.Source $Script
    if ($LASTEXITCODE -ne 0) { throw "bash $Script failed (exit $LASTEXITCODE)" }
}

function Invoke-JavacDir([string]$JavaDir, [string]$OutDir, [string]$ClassPath) {
    New-Item -ItemType Directory -Force -Path $OutDir | Out-Null
    $list = Join-Path $OutDir 'sources.list'
    Get-ChildItem -Path $JavaDir -Filter '*.java' -Recurse |
        ForEach-Object { $_.FullName } |
        Set-Content -Path $list -Encoding ascii
    & javac -cp $ClassPath -d $OutDir "@$list"
    if ($LASTEXITCODE -ne 0) { throw "javac failed in $JavaDir (exit $LASTEXITCODE)" }
}

Push-Location $repo
try {
    $dotnet = Find-DotNet
    $sep = [IO.Path]::PathSeparator
    $st4 = if ($env:ST4_VER) { $env:ST4_VER } else { '4.3.4' }
    $a3 = if ($env:ANTLR3_RUNTIME_VER) { $env:ANTLR3_RUNTIME_VER } else { '3.5.3' }
    $factoryLib = Join-Path $factory '.lib'
    $factoryOut = Join-Path $factory '.build'
    $factoryJars = "$(Join-Path $factoryLib "ST4-$st4.jar")$sep$(Join-Path $factoryLib "antlr-runtime-$a3.jar")"

    if (-not $SkipBuild) {
        Write-Host "Building Java factory + C# WktIntakeWalker ..." -ForegroundColor Cyan
        Invoke-Bash (Join-Path $factory 'generate.sh')
        Invoke-JavacDir (Join-Path $factory 'java') $factoryOut $factoryJars
        & (Join-Path $intake 'generate.ps1')
        Write-Host "dotnet build $intakeProj" -ForegroundColor Cyan
        & $dotnet build $intakeProj --nologo
        if ($LASTEXITCODE -ne 0) { throw "dotnet build WktIntakeWalker failed (exit $LASTEXITCODE)" }
    }

    $intakeDll = Join-Path $intake 'bin/Debug/net10.0/WktIntakeWalker.dll'
    if (-not (Test-Path $intakeDll)) { throw "missing $intakeDll after C# walker build" }

    $env:SQLMM_REPO = $repo
    $env:SQLMM_FACTORY_TEMPLATES = Join-Path $factory 'templates'
    $env:SQLMM_FACTORY_CP = "$factoryOut$sep$factoryJars"
    $env:SQLMM_INTAKE = $intakeDll
    if ($env:SQLMM_INTAKE_CP) { Remove-Item Env:SQLMM_INTAKE_CP }

    Write-Host "dotnet build $proj" -ForegroundColor Cyan
    & $dotnet build $proj --nologo
    if ($LASTEXITCODE -ne 0) { throw "dotnet build failed (exit $LASTEXITCODE)" }

    $runArgs = @('--no-build', '--project', $proj, '--', '--budget', "$Budget", '--seed', "$Seed")
    if ($PinsOnly) { $runArgs += '--pins-only' }
    Write-Host "dotnet run $($runArgs -join ' ')" -ForegroundColor Cyan
    & $dotnet run @runArgs
    if ($LASTEXITCODE -ne 0) { throw "SqlMmFactoryHunt failed (exit $LASTEXITCODE)" }
}
finally {
    Pop-Location
}

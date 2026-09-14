#requires -Version 5
# Generate ANTLR C# lexer/parser from the pinned grammars-v4 #4997 .g4 files.
# House style: $ErrorActionPreference='Stop'. Does not invent productions.
# claimId: none (tools). No new ADR-0006 keyword.
#
#   pwsh ./tools/WktIntakeWalker/generate.ps1
#
# This script was drafted with AI assistance; human review remains required.

[CmdletBinding()]
param()

$ErrorActionPreference = 'Stop'
if ($PSVersionTable.PSVersion.Major -ge 7) {
    $PSNativeCommandUseErrorActionPreference = $true
}

$root = $PSScriptRoot
$gen = Join-Path $root 'gen'
$jar = if ($env:ANTLR_JAR) { $env:ANTLR_JAR } else { Join-Path $root '.antlr/antlr-4.13.2-complete.jar' }
$ver = if ($env:ANTLR_VER) { $env:ANTLR_VER } else { '4.13.2' }

New-Item -ItemType Directory -Force -Path (Split-Path $jar) | Out-Null
New-Item -ItemType Directory -Force -Path $gen | Out-Null

if (-not (Test-Path $jar)) {
    $url = "https://www.antlr.org/download/antlr-$ver-complete.jar"
    Write-Host "Downloading $url" -ForegroundColor Cyan
    Invoke-WebRequest -Uri $url -OutFile $jar
}

$java = Get-Command java -ErrorAction SilentlyContinue
if (-not $java) {
    throw "java not found (needed to run the ANTLR $ver tool against the pinned .g4)."
}

$lexer = Join-Path $root 'grammar/wktLexer.g4'
$parser = Join-Path $root 'grammar/wktParser.g4'
if (-not (Test-Path $lexer) -or -not (Test-Path $parser)) {
    throw "pinned grammars missing under $root/grammar (do not invent productions)."
}

Write-Host "antlr -Dlanguage=CSharp → $gen" -ForegroundColor Cyan
& $java.Source -jar $jar -Dlanguage=CSharp -visitor -no-listener `
    -Xexact-output-dir `
    -o $gen -package Nts.Proofs.Intake.Gen `
    $lexer $parser
if ($LASTEXITCODE -ne 0) { throw "antlr generation failed (exit $LASTEXITCODE)" }

Get-ChildItem -Path $gen -Include '*.interp', '*.tokens' -Recurse -ErrorAction SilentlyContinue |
    Remove-Item -Force
Write-Host "generated $gen"

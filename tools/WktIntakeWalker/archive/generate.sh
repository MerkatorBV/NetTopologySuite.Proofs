#!/usr/bin/env bash
# Archived Java generate. Primary is ../generate.ps1 (C#).
# Grammar pin stays at ../grammar (grammars-v4 #4997 merge 181f4c9).
set -euo pipefail
ROOT="$(cd "$(dirname "$0")" && pwd)"
PARENT="$(cd "$ROOT/.." && pwd)"
GEN="$ROOT/java/org/nts/proofs/intake/gen"
JAR="${ANTLR_JAR:-$PARENT/.antlr/antlr-4.13.2-complete.jar}"
mkdir -p "$(dirname "$JAR")" "$GEN"
if [ ! -f "$JAR" ]; then
  curl -fsSL -o "$JAR" https://www.antlr.org/download/antlr-4.13.2-complete.jar
fi
java -jar "$JAR" -Dlanguage=Java -visitor -no-listener \
  -o "$GEN" -package org.nts.proofs.intake.gen \
  "$PARENT/grammar/wktLexer.g4" "$PARENT/grammar/wktParser.g4"
rm -f "$GEN"/*.interp "$GEN"/*.tokens
echo "generated $GEN"

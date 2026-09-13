#!/usr/bin/env bash
# Download StringTemplate 4 + ANTLR runtime (local jars, no Maven reactor).
# Pattern matches tools/WktIntakeWalker/generate.sh.
set -euo pipefail
ROOT="$(cd "$(dirname "$0")" && pwd)"
LIB="$ROOT/.lib"
mkdir -p "$LIB"

ST4_VER="${ST4_VER:-4.3.4}"
RT_VER="${ANTLR_RUNTIME_VER:-4.13.2}"
ST4="$LIB/ST4-${ST4_VER}.jar"
RT="$LIB/antlr4-runtime-${RT_VER}.jar"

if [ ! -f "$ST4" ]; then
  curl -fsSL -o "$ST4" \
    "https://repo1.maven.org/maven2/org/antlr/ST4/${ST4_VER}/ST4-${ST4_VER}.jar"
fi
if [ ! -f "$RT" ]; then
  curl -fsSL -o "$RT" \
    "https://repo1.maven.org/maven2/org/antlr/antlr4-runtime/${RT_VER}/antlr4-runtime-${RT_VER}.jar"
fi

echo "ST4=$ST4"
echo "ANTLR_RUNTIME=$RT"

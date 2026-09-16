#!/usr/bin/env bash
# Download StringTemplate 4 + ANTLR runtime (local jars, no Maven reactor).
# Pattern matches the retired Java WktIntakeWalker generate (now archive/).
set -euo pipefail
ROOT="$(cd "$(dirname "$0")" && pwd)"
LIB="$ROOT/.lib"
mkdir -p "$LIB"

# ST4 4.3.4 depends on ANTLR 3 runtime (org.antlr:antlr-runtime:3.5.3),
# not antlr4-runtime. See ST4-4.3.4.pom.
ST4_VER="${ST4_VER:-4.3.4}"
A3_VER="${ANTLR3_RUNTIME_VER:-3.5.3}"
ST4="$LIB/ST4-${ST4_VER}.jar"
A3="$LIB/antlr-runtime-${A3_VER}.jar"

if [ ! -f "$ST4" ]; then
  curl -fsSL -o "$ST4" \
    "https://repo1.maven.org/maven2/org/antlr/ST4/${ST4_VER}/ST4-${ST4_VER}.jar"
fi
if [ ! -f "$A3" ]; then
  curl -fsSL -o "$A3" \
    "https://repo1.maven.org/maven2/org/antlr/antlr-runtime/${A3_VER}/antlr-runtime-${A3_VER}.jar"
fi

echo "ST4=$ST4"
echo "ANTLR3_RUNTIME=$A3"

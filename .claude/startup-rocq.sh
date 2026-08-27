#!/usr/bin/env bash
set -euo pipefail
# Startup for AI coding agents (Claude/Grok/etc.) working on NetTopologySuite.Proofs.
# See docs/HELP.md (Joost / Tech-Lead Tess / Scrum-Master Sara paths) and
# docs/development-environment.md for context. This assumes the nts-flocq opam
# switch provisioned by .claude/hooks/session-start.sh.
eval "$(opam env --switch=nts-flocq)"

# The rocq binary reports only "9.2" (no patch level) — ask opam for the exact
# installed rocq-core pin instead.
ROCQ_VERSION=$(opam list --installed --columns=version rocq-core 2>/dev/null | grep -v '^#' | tail -1 || true)
[ -n "$ROCQ_VERSION" ] || ROCQ_VERSION="NOT FOUND"

# Flocq is built from source into Rocq's user-contrib (NOT an opam/ocamlfind
# package — see the session-start hook), so detect it there and confirm the
# exact pin from its Flocq_version constant (4.2.2 = 40202).
FLOCQ_VERSION="NOT FOUND"
if [ -d "$(rocq -where 2>/dev/null)/user-contrib/Flocq" ]; then
  FLOCQ_VERSION="user-contrib present (version unverified)"
  if out=$(printf 'From Flocq Require Import Version.\nFrom Stdlib Require Import BinNat.\nGoal (Flocq_version =? 40202)%%N = true. reflexivity. Qed.\n' \
             | rocq top -quiet 2>&1) && ! grep -q "Error" <<<"$out"; then
    FLOCQ_VERSION="4.2.2"
  fi
fi

echo "Rocq:  $ROCQ_VERSION"
echo "Flocq: $FLOCQ_VERSION"
[[ "$ROCQ_VERSION" == "9.2.0" ]] || echo "WARNING: expected Rocq 9.2.0"
[[ "$FLOCQ_VERSION" == "4.2.2" ]] || echo "WARNING: expected Flocq 4.2.2"

if [ ! -f Makefile.gen ] || [ _CoqProject.full -nt Makefile.gen ]; then
  rocq makefile -f _CoqProject.full -o Makefile.gen
fi
make -f Makefile.gen -j"$(nproc)" 2>&1 | tail -10
echo "✓ Environment ready."

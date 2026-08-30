#!/usr/bin/env bash
# =============================================================================
# scripts/validate-claims.sh
# -----------------------------------------------------------------------------
# Keeps cited `Module.v : name` claims honest (see docs/HELP.md etc. for actors).
# The markdown is a *citable index*,
# not the source of truth -- the .v files are.  This script cross-checks that
# every theorem the docs cite actually exists in the corpus, so a rename or
# removal that orphans a claim fails CI instead of silently rotting.
#
# Default docs (one gate, #578 / 522-l): docs/gated-prose-docs.txt when
# present, else docs/verified-claims.md. Extra paths may be passed as args.
#
# What it checks:
#   - Every `<Module>.v : <name>` reference in the doc resolves to a file
#     under theories/ or theories-flocq/.
#   - Each cited <name> is defined there as a Theorem/Lemma/Corollary/
#     Definition/Fact/Example/Property/Remark/Inductive/Fixpoint.
#   - `<stem>_{a,b}` brace shorthand is expanded (e.g. b64_intersect_point_{x,y}
#     checks _x and _y).
#
# What it does NOT check:
#   - That the theorem is Qed-closed (the corpus-wide invariant is enforced
#     separately by scripts/check_admitted.sh).
#   - That every theorem in the corpus is documented (the doc is curated,
#     not exhaustive).
#
# Backtick tokens without the `<Module>.v : <name>` shape (axiom names,
# deferred-but-unproved names like hobby_lemma_4_3_no_proper, prose) are
# intentionally ignored -- they are not claims.
#
# Exit non-zero on any orphaned claim.
# =============================================================================
set -uo pipefail

docs=()
if [ "$#" -gt 0 ]; then
  docs=("$@")
elif [ -f docs/gated-prose-docs.txt ]; then
  while IFS= read -r line || [ -n "$line" ]; do
    case "$line" in
      ''|\#*) continue ;;
      *) docs+=("$line") ;;
    esac
  done < docs/gated-prose-docs.txt
else
  docs=("docs/verified-claims.md")
fi

fail=0
checked=0

check_doc() {
  local DOC="$1"
  if [ ! -f "$DOC" ]; then
    echo "[validate-claims] ERROR: doc not found: $DOC"
    return 2
  fi

  local refs=()
  local ref
  while IFS= read -r ref; do
    [ -n "$ref" ] && refs+=("$ref")
  done < <(grep -oE '`[A-Za-z0-9_]+\.v[[:space:]]*:[[:space:]]*[A-Za-z0-9_{},]+`' "$DOC" \
           | tr -d '`' | sort -u)

  if [ "${#refs[@]}" -eq 0 ]; then
    echo "[validate-claims] ERROR: no \`Module.v : name\` claims found in $DOC"
    return 2
  fi

  local base name path d names stem opts p nm
  for ref in "${refs[@]}"; do
    base="$(echo "${ref%%:*}" | xargs)"
    name="$(echo "${ref#*:}"  | xargs)"

    path=""
    for d in theories theories-flocq; do
      if [ -f "$d/$base" ]; then path="$d/$base"; fi
    done
    if [ -z "$path" ]; then
      echo "  ORPHAN (no such file): $base   <- cited as \`$ref\` in $DOC"
      fail=1
      continue
    fi

    names=()
    if [[ "$name" == *"{"* ]]; then
      stem="${name%%\{*}"
      opts="${name#*\{}"; opts="${opts%\}*}"
      IFS=',' read -ra parts <<< "$opts"
      for p in "${parts[@]}"; do names+=("${stem}$(echo "$p" | xargs)"); done
    else
      names+=("$name")
    fi

    for nm in "${names[@]}"; do
      checked=$((checked + 1))
      if ! grep -qE "^[[:space:]]*(Theorem|Lemma|Corollary|Definition|Fact|Example|Property|Remark|Inductive|Fixpoint)[[:space:]]+${nm}([[:space:]]|:|\()" "$path"; then
        echo "  ORPHAN (not defined in $path): $nm   <- $DOC"
        fail=1
      fi
    done
  done
}

for doc in "${docs[@]}"; do
  check_doc "$doc" || {
    rc=$?
    [ "$rc" -eq 2 ] && exit 2
  }
done

if [ "$fail" -ne 0 ]; then
  echo "[validate-claims] FAIL: gated docs cite theorems that do not exist."
  echo "  Fix the doc (rename/remove the orphaned claim) or restore the theorem."
  exit 1
fi

echo "[validate-claims] OK: all $checked cited theorems exist in the corpus."

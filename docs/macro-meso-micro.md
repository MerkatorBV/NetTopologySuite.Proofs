# Macro · Meso · Micro

**Status:** living paradigm for NetTopologySuite.Proofs  
**Audience:** humans, auditors, RGR agents

The corpus is too large to maintain as a flat list of theorems. Work is organised
on **three scales**. The observatory dashboard
([GitHub Pages](https://grootstebozewolf.github.io/NetTopologySuite.Proofs/))
surfaces the same stack.

## Macro — domains & epics

| Idea | Examples |
|------|----------|
| Board epic | Issues **#64–#69** (arcs, buffer, precision/overlay, RelateNG, Delaunay/Voronoi, SQL/MM umbrella) |
| Topic tag | `topic: mesh`, `topic: relate`, `topic: arc`, `topic: koc`, … |
| Role | Human-scale “where does this live?” and blast-cone epicenter |

Macro answers: *which geometry family / open issue owns this work?*

## Meso — modules

| Idea | Examples |
|------|----------|
| Atom | A `.v` module (not 5 000 free-floating statements) |
| Graph | `Require` edges; blast cone = module + dependents |
| Layer law | core → predicates → **overlay** → topology (Jordan) → arcs → mesh |
| ADR-0001 | Jordan **needs** Overlay; circular Require is a tripwire; prefer **rocq makefile** / `_CoqProject` |

Meso answers: *which file is the audit unit, and what does a change irradiate?*

Smoke without the full chain: self-contained tripwire files that duplicate
already-Qed leaves (e.g. ring lemmas, `inCircle_R`) and `Require` only a thin
witness module — mark with `(* ADR-0001: self-contained smoke *)`.

## Micro — claims & witnesses

| Idea | Examples |
|------|----------|
| Claim key | Board subtask `claimId: 68-a` or teaching seed `even-square` |
| Witness | `witness: empty-circle`, `(* WITNESS {"claimId":"…"} *)` |
| Loop | **Red** (failing surface) → **Green** (Qed + CI) → **Refactor** (merge or next rung) |
| Eval | Micro-kernel / Rocq: Eval → Qed; mutation suite probes vacuity |
| Registry | Dynamic micro claims: board sync + register + auto-WITNESS |

Micro answers: *what is the smallest falsifiable obligation right now?*

## Machine header (PR bodies)

```text
topic: mesh
claimId: 68-a
witness: empty-circle
```

| Tag | Scale | Skip form |
|-----|-------|-----------|
| `topic:` | macro | `topic: none` |
| `claimId:` | micro (board or seed) | `claimId: none` |
| `witness:` | micro falsifier | `witness: none` |

## Why three scales

1. **Auditors** sample modules (meso), not every lemma.
2. **Agents** plan RGR on claimIds (micro) without loading the whole corpus.
3. **Humans** track open geometry programs via epics (macro).
4. **CI / review** attach blast cones, ADR-0001 dep checks, and mutation only
   when the right scale is named.

## Related

- `docs/adr/` (dependency order, witness tags) when present in-tree  
- `docs/verified-claims.md` — cited theorem ledger (meso/micro evidence)  
- `TRIAGE_NTS_JTS_ISSUES.md` — macro issue map  
- Observatory generator: `scripts/gen_dashboard.py`

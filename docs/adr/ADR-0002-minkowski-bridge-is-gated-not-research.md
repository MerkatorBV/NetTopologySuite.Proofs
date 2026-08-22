# ADR-0002 — The Minkowski buffer bridge is dependency-gated, not research-scale

| Field | Value |
|---|---|
| **Order** | ADR-0002 |
| **Status** | **Accepted** — 2026-08-22 |
| **Deciders** | Jeroen Bloemscheer (BDFL) |
| **Supersedes** | the "research-scale" characterisation of P2 carried in issue #65's round-2 queue |
| **Superseded by** | — |

---

## Context

> Terminology note: `doc/EXACT_CURVE_BIBLE.md`, cited elsewhere in this effort,
> lives in the **`jts-*` fork clones**, not in this repository. It is not
> load-bearing for this ADR.

Issue #65's round-2 queue listed **P2 Minkowski point-set semantics** as
*"parked (research-scale; pinned by `gen_buffer_region_tests.py`)"*. That label
was challenged before being carried into the successor epic, and it does not
survive contact with the corpus.

What the tree actually contains:

- **The semantics is already formalised.** `theories/BufferCorrectness.v:57`
  defines the Minkowski dilation directly —
  `buffer_spec g d p := exists q, point_set g q /\ dist p q <= d`, i.e.
  `buffer(g,d) = { p | dist(p,g) ≤ d }` — with two Qed theorems giving it
  content: `buffer_contains_input` (:70) and `buffer_spec_monotone`.
- **Proven Minkowski machinery exists elsewhere.**
  `theories/PenetrationMinimax.v:78 interval_minkowski_diff` (1-D Minkowski
  difference is the sum of half-widths, `Print Assumptions` at :291), consumed by
  `theories/PenetrationGauge.v`.
- **A differential pin already exists.** `oracle/gen_buffer_region_tests.py`
  generates an independent dense-Minkowski reference, cited by
  `theories/CurveBufferArea.v:29-31`.
- **The corpus's own cost assessment is not "research".**
  `docs/audit-rgr-comparison.md:640` rates P2 as value **high** ("the buffer
  point-set headline"), risk **medium–high** — *"needs H1-adjacent analytic
  machinery; sequence AFTER P5"* — cost **multi-session**. §8.3 decision 3 reads
  *"Sequence P2 (Minkowski) after P5"*, and decision 2 notes that P5
  *"additionally unlocks P2"*.

For comparison, the items this corpus genuinely parks for research reasons are
P11–13, and the reason given for the arc-Hobby analog is that there is **"no
published true statement"**. That is the bar "research-scale" denotes here, and
P2 does not meet it.

## Decision

**P2 is reclassified from *research-scale / parked* to *dependency-gated,
multi-session, partially unblocked*.** It is carried inside the buffer
hero-shot epic as that epic's semantic foundation, not as standalone backlog and
not as a research park.

Two further findings shape how it is carried:

1. **The gate is already partly open.** P5's residual `even_parity_escapes` is
   Qed for concrete shape families — `theories/JCTSeparation.v:113
   rect_even_parity_escapes`, `:141 gtri_even_parity_escapes` (general triangle),
   `:156 rtri_even_parity_escapes` — and
   `theories/JCTEscapeDescent.v:279 even_parity_escapes_of_descent` reduces the
   general case to a descent that still carries `ray_avoids_vertices`
   (`theories/HalfOpenTrapped.v:30`). Only the fully general simple-ring case is
   outstanding.
2. **A witness-scoped bridge is therefore available now.** The shape families
   already discharged are exactly the ones a demonstration uses. A Minkowski
   bridge scoped to those shapes needs no new analytic machinery, and it matches
   the corpus's most reliable idiom — *"bounded structural slice with a usable
   headline"* (`audit-rgr-comparison.md` §8.2), the pattern that landed eight
   curve-offset rungs in two days.

## Consequences

- The successor epic must state the Minkowski bridge as an **ask with a
  witness-scoped first slice**, not as a parked item. Anyone reading "parked"
  would otherwise skip the reachable part.
- Terminology is now load-bearing: in this corpus **"research-scale" means no
  published true statement to aim at**, and must not be used for work that is
  merely multi-session or gated behind another lane. Sequencing parks and
  difficulty parks are recorded differently because they graduate differently —
  a sequencing park graduates when its gate lands, a research park only when
  someone finds a statement worth proving.
- The general simple-ring `even_parity_escapes` case remains the gate for the
  *unrestricted* bridge, and stays where it is (P5, the JCT escape descent).
- No claim in `docs/verified-claims.md` changes: nothing here proves anything
  new, it reclassifies what remains to be proven.

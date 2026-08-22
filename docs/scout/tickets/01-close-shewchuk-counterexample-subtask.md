# Close #482 — Shewchuk half-ulp counterexample retip

**Type:** task · **Map:** [Retire the epic block #64–#69](../map-epic-block-64-69.md)
**Blocked by:** —

## Question

#482 asks that the `fast_expansion_sum_nonoverlap_shewchuk` headline be retipped
as a disproof of the *corpus* postcondition (half-ulp `strict_succ_b64`), not of
Shewchuk 1997 as published. Is that ask satisfied by the corpus today, and does
it close?

Audit evidence to verify, then cite:

- `docs/phase0-completion.md:93-113` already carries the retipped wording and
  links both the issue and the witness.
- `theories-flocq/B64_Shewchuk_Thm13_counterexample.v` — `nonoverlap_shewchuk_256_1_false`,
  `e_nonoverlap`, `f_nonoverlap`, `inputs_sum_eq`, all Qed.
- Registered in `docs/admitted-counterexamples.txt:119-142` and
  `docs/audit-exceptions.txt:106-113`.
- `b64_orient2d_exact_sound` untouched; the restricted true form lives in
  `theories-flocq/B64_FastExpansionSum_Shewchuk_Route2.v`.

Decide also whether the one gap the audit noticed — the counterexample has no
`docs/verified-claims.md` row, living only in the two registries — is part of
this ask or a separate micro.

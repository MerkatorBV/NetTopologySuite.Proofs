# nts-eval micro units

Self-contained Rocq units for the `nts-eval` micro-kernel harness.

Each file embeds a `(* WITNESS {"claimId":"…", …} *)` marker so static
matching can bind the formal lemma to the claim id without loading the full
`_CoqProject.full` dependency cone.

| claimId | topic | File | Lemma |
|--------:|-------|------|-------|
| `65-a` | `buffer` | [`Claim65a.v`](Claim65a.v) | `flat_endcap_is_diameter_segment` |
| `65-b` | `buffer` | [`Claim65b.v`](Claim65b.v) | `round_endcap_is_forward_semicircle` |
| `67-a` | `relate` | [`Claim67a.v`](Claim67a.v) | `unit_square_self_relate_de9im_eq` |
| `67-b` | `relate` | [`Claim67b.v`](Claim67b.v) | `boundary_op_eq_relateng_boundary_graph` |
| `68-a` | `mesh` | [`Claim68a.v`](Claim68a.v) | `delaunay_edge_iff_empty_circumcircle` |
| `425-a` | `coverage` | [`Claim425a.v`](Claim425a.v) | `coverage_gap_overlap_cleaner_valid` |

Production home for 65-a (Green/Qed: full biconditional — flat endcap =
perpendicular diameter segment `p ± r·J(t)`, with the rational witness pins
and the two mismatch probes): `theories/BufferEndcapDiameter.v` (same
WITNESS tag; sqrt-free `m = vmag ein` normaliser). The unit here carries
the self-contained m = 1 proof plus the pins.

Production home for 65-b (Green/Qed: full biconditional — round endcap =
forward semicircle, the frame image of the unit half-circle
`q = E + d·(a·unit_perp + b·unit_dir)`, `a² + b² = 1`, `b ≥ 0`, plus the
signed apex pin and the diameter-endpoint seam pins):
`theories/BufferEndcapSemicircle.v` (same WITNESS tag). The unit here
carries the self-contained unit-tangent proof plus the pins.

Production home for 67-a (Green/Qed: classical strata + rational unit-square
self-relate / OGC equal DE-9IM): `theories/RelateNGMatrixEqual.v` (same WITNESS tag).

Production home for 67-b (Green/Qed: rectangle core + rational unit-square
witness): `theories/RelateNGBoundaryGraph.v` (same WITNESS tag).

Production home for 68-a (full witness cluster, shared helpers):
`theories/DelaunayEdgeEmptyCircle.v` (also tagged with the same WITNESS).

Production home for 425-a (Green/Qed: witness-scoped cleaner soundness —
3-cell open-interior-disjoint partition of the rational two-cell overlap
coverage, same-union up to boundary null sets):
`theories/CoverageGapOverlapCleaner.v` (same WITNESS tag).

## Re-run

```text
# micro-kernel static match (Rocq optional):
#   source = eval/Claim65a.v | eval/Claim67a.v | eval/Claim67b.v | eval/Claim68a.v | eval/Claim425a.v
# full compile (needs Rocq / nts-eval switch):
rocq compile eval/Claim65a.v
rocq compile eval/Claim67a.v
rocq compile eval/Claim67b.v
rocq compile eval/Claim68a.v
rocq compile eval/Claim425a.v
```

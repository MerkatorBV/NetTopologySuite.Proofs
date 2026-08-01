# nts-eval micro units

Self-contained Rocq units for the `nts-eval` micro-kernel harness.

Each file embeds a `(* WITNESS {"claimId":"…", …} *)` marker so static
matching can bind the formal lemma to the claim id without loading the full
`_CoqProject.full` dependency cone.

| claimId | topic | File | Lemma |
|--------:|-------|------|-------|
| `65-a` | `buffer` | [`Claim65a.v`](Claim65a.v) | `flat_endcap_is_diameter_segment` — **RED** (claim stated, witness pins Qed; Green pending) |
| `67-b` | `relate` | [`Claim67b.v`](Claim67b.v) | `boundary_op_eq_relateng_boundary_graph` |
| `68-a` | `mesh` | [`Claim68a.v`](Claim68a.v) | `delaunay_edge_iff_empty_circumcircle` |

Production home for 67-b (Green/Qed: rectangle core + rational unit-square
witness): `theories/RelateNGBoundaryGraph.v` (same WITNESS tag).

Production home for 68-a (full witness cluster, shared helpers):
`theories/DelaunayEdgeEmptyCircle.v` (also tagged with the same WITNESS).

**65-a is RED**: `Claim65a.v` states `flat_endcap_is_diameter_segment_claim`
(flat endcap = perpendicular diameter segment `p ± r·J(t)`) with the rational
witness pinned Qed (unit segment ending (1,0), r = 1 ⇒ diameter (1,−1)—(1,1);
endpoint/interior pins + two mismatch probes refuting the perpendicular-line
and along-tangent wrong geometries). No production home yet — Green must Qed
the claim in the `BufferEndcap.v` neighbourhood under the same WITNESS tag.

## Re-run

```text
# micro-kernel static match (Rocq optional):
#   source = eval/Claim67b.v | eval/Claim68a.v
# full compile (needs Rocq / nts-eval switch):
rocq compile eval/Claim67b.v
rocq compile eval/Claim68a.v
```

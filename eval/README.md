# nts-eval micro units

Self-contained Rocq units for the `nts-eval` micro-kernel harness.

Each file embeds a `(* WITNESS {"claimId":"…", …} *)` marker so static
matching can bind the formal lemma to the claim id without loading the full
`_CoqProject.full` dependency cone.

| claimId | topic | File | Lemma |
|--------:|-------|------|-------|
| `67-b` | `relate` | [`Claim67b.v`](Claim67b.v) | `boundary_op_eq_relateng_boundary_graph` |
| `68-a` | `mesh` | [`Claim68a.v`](Claim68a.v) | `delaunay_edge_iff_empty_circumcircle` |

Production home for 67-b (Red surface, Abort headlines + rational unit-square
witness): `theories/RelateNGBoundaryGraph.v` (same WITNESS tag).

Production home for 68-a (full witness cluster, shared helpers):
`theories/DelaunayEdgeEmptyCircle.v` (also tagged with the same WITNESS).

## Re-run

```text
# micro-kernel static match (Rocq optional):
#   source = eval/Claim67b.v | eval/Claim68a.v
# full compile (needs Rocq / nts-eval switch):
rocq compile eval/Claim67b.v
rocq compile eval/Claim68a.v
```

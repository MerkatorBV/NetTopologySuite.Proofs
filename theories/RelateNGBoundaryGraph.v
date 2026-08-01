(* ============================================================================
   NetTopologySuite.Proofs.RelateNGBoundaryGraph
   ----------------------------------------------------------------------------
   Issue #67 subtask 67-b — RED surface only: classical boundary operator ∂
   equals the RelateNG boundary-graph extraction (polygonal regions).

   WHAT THIS FILE IS.  The smallest failing claim for the identification
     ∂P  =  RelateNGBoundaryGraph P
   over polygonal regions in classical reals, packaged as
   `boundary_op_eq_relateng_boundary_graph`, with a rational unit-square
   witness that exercises both sides on an explicit edge midpoint.
   Green / Refactor are out of scope: no production body that closes the
   goal, no `Admitted` as a fake green.  Open goals end with `Abort`
   (same discipline as HobbyTheorem_b64 / InArc Red / InDisk Red /
   DelaunayEdgeEmptyCircle Red — an Aborted claim is not `apply`-able
   and cannot silently poison consumers).

   WHAT IS MISSING ON MAIN (why the focused check fails without Green).
   Neighbouring #67 slices formalise *policy* and *matrix fill*, not the
   ∂ ↔ boundary-graph identification:
     - `RelateBoundary.v` — MOD2 / endpoint contact, JTS#1175 class; no
       classical topological ∂ on polygonal regions;
     - `RelateNG.point_on_boundary` / `RelateCurveMatrix.geom_boundary` —
       combinatorial on-edge membership (the graph side), not the
       neighbourhood characterisation of ∂, and not an equality theorem;
     - `RelateNodingLineLine` / matrix fills — DE-9IM cells for line×line
       and regime witnesses, not boundary-operator fidelity for areas;
     - `Overlay.point_set` / JCT seam — interior membership via ray
       parity; the frontier of that set is not identified with the ring
       edge graph.
   There is no named `boundary_op` / `RelateNGBoundaryGraph` surface on
   main, and no rational polygonal witness discharging their equality.

   INTENDED PREDICATE (spec shape for Green).
     - `boundary_op P p` — classical topological boundary of the corpus
       point-set carrier of polygonal geometry [P]: every open Euclidean
       neighbourhood of [p] meets both `{q | point_set P q}` and its
       complement (frontier of the ray-parity region).
     - `RelateNGBoundaryGraph P p` — combinatorial RelateNG extraction:
       [p] lies on some ring edge of [P] (closed segment via `between`).
       This is the carrier RelateNG uses when contributing boundary cells
       of the DE-9IM matrix (twins `geom_boundary` / `point_on_boundary`).
   Green is authorised to refine half-open vs closed conventions, MOD2
   node filtering on multi-component collections, or strengthen
   `valid_geometry` hypotheses if the full classical biconditional needs
   them; Red only fixes the ∂ ↔ graph shape and the rational witness.
   Operator Eval → Qed via the nts-eval micro-kernel is required for the
   Green close (operator CI status unknown at Red time).

   RATIONAL WITNESS (unit square ⊂ ℚ²).
     P = unit square with closed outer ring
         (0,0) → (1,0) → (1,1) → (0,1) → (0,0)
     candidate boundary point m = (1/2, 0)  (midpoint of bottom edge)
   Combinatorial side: [m] lies on edge (0,0)–(1,0) via `between` at t=1/2.
   Classical side: every open disk about [m] meets the filled square and
   its complement (Green discharges via point_set / neighbourhood facts).
   The focused equality on this witness (and the universal biconditional)
   remain Abort until Green.

   Refs: issue #67 (RelateNG / DE-9IM boundary handling, ask #3c),
   `docs/issue-67-relateng-triage.md`, JTS RelateNG boundary node graph,
   OGC 06-103r4 boundary of polygonal regions.
   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Grok (grok-4.5)
   ========================================================================== *)

From Stdlib Require Import Reals Lra List.
Import ListNotations.
From NTS.Proofs Require Import Distance Overlay Segment.

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  Spec shape — classical ∂ and RelateNG boundary graph.                  *)
(*                                                                            *)
(* Spec shape only.  Green may refine carrier conventions (half-open ring     *)
(* parity vs closed topological interior) once a consumer pins the OGC/JTS    *)
(* boundary cells exactly; the Red claims use the neighbourhood form of ∂     *)
(* against the corpus [point_set] carrier and the on-edge graph extraction.   *)
(* -------------------------------------------------------------------------- *)

(** Edges of a polygon = outer-ring edges plus every hole-ring's edges. *)
Definition poly_edges (poly : Polygon) : list Edge :=
  ring_edges (outer_ring poly) ++ flat_map ring_edges (hole_rings poly).

(** All ring edges of a multi-polygon geometry (RelateNG edge bag). *)
Definition relateng_boundary_edges (P : Geometry) : list Edge :=
  flat_map poly_edges P.

(** Classical topological boundary operator [∂] of polygonal geometry [P]
    relative to the corpus [point_set] carrier: [p] is a frontier point of
    `{q | point_set P q}` under the Euclidean metric.

    Every open disk of positive radius about [p] meets both the carrier set
    and its complement. *)
Definition boundary_op (P : Geometry) (p : Point) : Prop :=
  forall eps : R, 0 < eps ->
    (exists q : Point, dist p q < eps /\ point_set P q) /\
    (exists r : Point, dist p r < eps /\ ~ point_set P r).

(** RelateNG boundary-graph extraction: [p] lies on some ring edge of [P]
    (closed segment membership via [between]).  Twin of
    [RelateCurveMatrix.geom_boundary] / [RelateNG.point_on_boundary],
    restated here so the Red surface does not require the full RelateNG
    pipeline cone. *)
Definition RelateNGBoundaryGraph (P : Geometry) (p : Point) : Prop :=
  exists e, In e (relateng_boundary_edges P) /\
    between (fst e) (snd e) p.

(* -------------------------------------------------------------------------- *)
(* §2  Rational unit-square witness (ℚ²).                                     *)
(*                                                                            *)
(* Closed outer ring of the unit square [0,1]×[0,1]; midpoint of the bottom   *)
(* edge is the concrete boundary sample.                                      *)
(* -------------------------------------------------------------------------- *)

Definition bnd_sw : Point := mkPoint 0 0.
Definition bnd_se : Point := mkPoint 1 0.
Definition bnd_ne : Point := mkPoint 1 1.
Definition bnd_nw : Point := mkPoint 0 1.

(** Closed outer ring of the unit square (CCW, repeated first vertex). *)
Definition bnd_unit_square_ring : Ring :=
  [bnd_sw; bnd_se; bnd_ne; bnd_nw; bnd_sw].

Definition bnd_unit_square_poly : Polygon :=
  mkPolygon bnd_unit_square_ring [].

(** Polygonal region P for the witness (single unit-square polygon). *)
Definition bnd_witness_P : Geometry := [bnd_unit_square_poly].

(** Midpoint of the bottom edge (0,0)–(1,0); rational coordinates. *)
Definition bnd_mid_bottom : Point := mkPoint (1 / 2) 0.

(** Bottom edge of the unit-square ring (directed). *)
Definition bnd_bottom_edge : Edge := (bnd_sw, bnd_se).

(* Geometric scaffolding for the witness — Qed.  Mentions only list
   membership / [between] / edge bag, so it cannot accidentally close the
   Red equality claims (those need classical ∂ ↔ graph). *)

Lemma bnd_unit_square_edges :
  ring_edges bnd_unit_square_ring =
    [ (bnd_sw, bnd_se)
    ; (bnd_se, bnd_ne)
    ; (bnd_ne, bnd_nw)
    ; (bnd_nw, bnd_sw) ].
Proof. reflexivity. Qed.

Lemma bnd_bottom_edge_in_ring :
  In bnd_bottom_edge (ring_edges bnd_unit_square_ring).
Proof. rewrite bnd_unit_square_edges. simpl. left. reflexivity. Qed.

Lemma bnd_bottom_edge_in_witness_edges :
  In bnd_bottom_edge (relateng_boundary_edges bnd_witness_P).
Proof.
  unfold relateng_boundary_edges, poly_edges, bnd_witness_P, bnd_unit_square_poly.
  simpl.
  (* poly_edges poly ++ []  with  hole_rings = []  ⇒  ring_edges ring ++ [] *)
  repeat rewrite app_nil_r.
  exact bnd_bottom_edge_in_ring.
Qed.

(** Midpoint lies on the closed bottom segment via the parametric form
    [between] at [t = 1/2]. *)
Lemma bnd_mid_bottom_between_bottom_edge :
  between bnd_sw bnd_se bnd_mid_bottom.
Proof.
  unfold between, bnd_sw, bnd_se, bnd_mid_bottom; cbn [px py].
  exists (1 / 2). split; [lra |]. split; [lra |]. split; field.
Qed.

(** Combinatorial scaffolding: the midpoint is on the RelateNG boundary
    graph of the unit-square witness (on-edge extraction only). *)
Lemma bnd_mid_bottom_on_relateng_graph :
  RelateNGBoundaryGraph bnd_witness_P bnd_mid_bottom.
Proof.
  unfold RelateNGBoundaryGraph.
  exists bnd_bottom_edge.
  split.
  - exact bnd_bottom_edge_in_witness_edges.
  - exact bnd_mid_bottom_between_bottom_edge.
Qed.

Lemma bnd_corners_distinct_sw_se : bnd_sw <> bnd_se.
Proof.
  unfold bnd_sw, bnd_se. intros Heq.
  assert (Hpx : px (mkPoint 0 0) = px (mkPoint 1 0))
    by (rewrite Heq; reflexivity).
  cbn in Hpx. lra.
Qed.

Lemma bnd_mid_not_corner :
  bnd_mid_bottom <> bnd_sw /\ bnd_mid_bottom <> bnd_se.
Proof.
  unfold bnd_mid_bottom, bnd_sw, bnd_se. split; intros Heq.
  - assert (Hpx : px (mkPoint (1 / 2) 0) = px (mkPoint 0 0))
      by (rewrite Heq; reflexivity).
    cbn in Hpx. lra.
  - assert (Hpx : px (mkPoint (1 / 2) 0) = px (mkPoint 1 0))
      by (rewrite Heq; reflexivity).
    cbn in Hpx. lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Focused Red claims — open, not Admitted.                               *)
(*                                                                            *)
(* These are the surface Eval / nts-eval will re-check after Green is          *)
(* authorised.  Until then they remain Abort: neither closed nor disproven.   *)
(* -------------------------------------------------------------------------- *)

(* WITNESS {"claimId":"67-b","topic":"relate","lemma":"boundary_op_eq_relateng_boundary_graph","title":"Classical ∂P = RelateNG boundary graph","file":"theories/RelateNGBoundaryGraph.v"} *)

(** RED (67-b): classical topological boundary of a polygonal region equals
    the RelateNG boundary-graph extraction, pointwise on classical reals.

    [boundary_op P p]  ↔  [RelateNGBoundaryGraph P p]

    Green closes under whatever [valid_geometry] / simplicity hypotheses the
    frontier-of-[point_set] argument needs (JCT seam may appear).  Do not
    Admitted. *)
Theorem boundary_op_eq_relateng_boundary_graph :
  forall (P : Geometry) (p : Point),
    boundary_op P p <-> RelateNGBoundaryGraph P p.
Proof.
  (* RED #67-b: Green identifies neighbourhood frontier of [point_set]
     with the combinatorial ring-edge graph.  Do not Admitted — that would
     be a fake green. *)
Abort.

(** RED (67-b): the same equality specialised to the rational unit-square
    witness [bnd_witness_P].  Exercises the biconditional on a concrete
    polygonal region with vertices in ℚ². *)
Theorem boundary_op_eq_relateng_boundary_graph_on_witness :
  forall (p : Point),
    boundary_op bnd_witness_P p <-> RelateNGBoundaryGraph bnd_witness_P p.
Proof.
  (* RED #67-b: Green discharges the unit-square case (optionally first,
     before the universal claim).  Do not Admitted. *)
Abort.

(** RED (67-b): the bottom-edge midpoint of the unit square lies on the
    classical boundary [∂P] (neighbourhood form).  Combinatorial twin
    [bnd_mid_bottom_on_relateng_graph] is already Qed scaffolding; this
    claim is the classical side that still needs Green. *)
Theorem bnd_mid_bottom_on_classical_boundary :
  boundary_op bnd_witness_P bnd_mid_bottom.
Proof.
  (* RED #67-b: Green shows every open disk about (1/2,0) meets both the
     filled unit square and its exterior under [point_set].  Do not
     Admitted. *)
Abort.

(** RED (67-b): both sides agree on the rational midpoint witness
    (conjunction form of the equality at one concrete point). *)
Theorem bnd_mid_bottom_boundary_sides_agree :
  boundary_op bnd_witness_P bnd_mid_bottom /\
  RelateNGBoundaryGraph bnd_witness_P bnd_mid_bottom.
Proof.
  (* RED #67-b: Green packages [bnd_mid_bottom_on_classical_boundary] with
     the Qed scaffolding [bnd_mid_bottom_on_relateng_graph].  Do not
     Admitted. *)
Abort.

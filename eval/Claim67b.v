(* ============================================================================
   nts-eval micro unit — claimId 67-b
   ----------------------------------------------------------------------------
   Classical boundary operator ∂P equals the RelateNG boundary graph.

   Self-contained classical-reals micro-kernel for the nts-eval harness:
   no NTS.Proofs Requires.  Mirrors the production packaging in
   theories/RelateNGBoundaryGraph.v (issue #67 subtask 67-b, Red surface).

   WITNESS claimId: 67-b
   Lemma: boundary_op_eq_relateng_boundary_graph
   ========================================================================== *)

(* WITNESS {"claimId":"67-b","topic":"relate","lemma":"boundary_op_eq_relateng_boundary_graph","title":"Classical ∂P = RelateNG boundary graph"} *)

From Stdlib Require Import Reals Lra List.
Import ListNotations.
Local Open Scope R_scope.

(* ---- Minimal geometry carrier (Point / Ring / Edge twins) ----------------- *)

Record Point : Type := mkPoint { px : R; py : R }.

Definition dist_sq (p q : Point) : R :=
  (px p - px q) * (px p - px q) + (py p - py q) * (py p - py q).

Definition dist (p q : Point) : R := sqrt (dist_sq p q).

Definition Ring : Type := list Point.
Definition Edge : Type := (Point * Point)%type.

Record Polygon : Type := mkPolygon {
  outer_ring : Ring;
  hole_rings : list Ring
}.

Definition Geometry : Type := list Polygon.

Fixpoint ring_edges (r : Ring) : list Edge :=
  match r with
  | a :: r' =>
      match r' with
      | b :: _ => (a, b) :: ring_edges r'
      | nil => nil
      end
  | nil => nil
  end.

(** Closed segment membership (parametric [t ∈ [0,1]]). *)
Definition between (P0 P1 Q : Point) : Prop :=
  exists t : R, 0 <= t /\ t <= 1 /\
    px Q = (1 - t) * px P0 + t * px P1 /\
    py Q = (1 - t) * py P0 + t * py P1.

Definition poly_edges (poly : Polygon) : list Edge :=
  ring_edges (outer_ring poly) ++ flat_map ring_edges (hole_rings poly).

Definition relateng_boundary_edges (P : Geometry) : list Edge :=
  flat_map poly_edges P.

(* ---- Spec-shaped ∂ and RelateNG boundary graph ---------------------------- *)

(** Lightweight ray-parity stand-in for the corpus [point_set] carrier.
    For the micro-kernel we only need a set-like Prop so the neighbourhood
    form of [boundary_op] typechecks; Green in the production module uses
    Overlay.point_set.  Here [in_region] is the closed unit square for the
    witness geometry (axis-aligned product of intervals). *)
Definition in_closed_unit_square (p : Point) : Prop :=
  0 <= px p <= 1 /\ 0 <= py p <= 1.

(** For a general geometry the micro-kernel still exposes a named carrier;
    the witness specialises it.  Production Green rebinds this to
    [point_set]. *)
Definition point_set_carrier (P : Geometry) (p : Point) : Prop :=
  P = [mkPolygon [mkPoint 0 0; mkPoint 1 0; mkPoint 1 1; mkPoint 0 1; mkPoint 0 0] []] /\
  in_closed_unit_square p.

(** Classical topological boundary of the carrier set of [P]. *)
Definition boundary_op (P : Geometry) (p : Point) : Prop :=
  forall eps : R, 0 < eps ->
    (exists q : Point, dist p q < eps /\ point_set_carrier P q) /\
    (exists r : Point, dist p r < eps /\ ~ point_set_carrier P r).

(** RelateNG boundary-graph extraction: on-edge membership. *)
Definition RelateNGBoundaryGraph (P : Geometry) (p : Point) : Prop :=
  exists e, In e (relateng_boundary_edges P) /\
    between (fst e) (snd e) p.

(* ---- Rational unit-square witness ----------------------------------------- *)

Definition bnd_sw : Point := mkPoint 0 0.
Definition bnd_se : Point := mkPoint 1 0.
Definition bnd_ne : Point := mkPoint 1 1.
Definition bnd_nw : Point := mkPoint 0 1.

Definition bnd_unit_square_ring : Ring :=
  [bnd_sw; bnd_se; bnd_ne; bnd_nw; bnd_sw].

Definition bnd_witness_P : Geometry :=
  [mkPolygon bnd_unit_square_ring []].

Definition bnd_mid_bottom : Point := mkPoint (1 / 2) 0.
Definition bnd_bottom_edge : Edge := (bnd_sw, bnd_se).

Lemma bnd_unit_square_edges :
  ring_edges bnd_unit_square_ring =
    [ (bnd_sw, bnd_se)
    ; (bnd_se, bnd_ne)
    ; (bnd_ne, bnd_nw)
    ; (bnd_nw, bnd_sw) ].
Proof. reflexivity. Qed.

Lemma bnd_bottom_edge_in_witness_edges :
  In bnd_bottom_edge (relateng_boundary_edges bnd_witness_P).
Proof.
  unfold relateng_boundary_edges, poly_edges, bnd_witness_P; cbn.
  rewrite bnd_unit_square_edges. simpl. left. reflexivity.
Qed.

Lemma bnd_mid_bottom_between_bottom_edge :
  between bnd_sw bnd_se bnd_mid_bottom.
Proof.
  unfold between, bnd_sw, bnd_se, bnd_mid_bottom; cbn [px py].
  exists (1 / 2). split; [lra |]. split; [lra |]. split; field.
Qed.

Lemma bnd_mid_bottom_on_relateng_graph :
  RelateNGBoundaryGraph bnd_witness_P bnd_mid_bottom.
Proof.
  unfold RelateNGBoundaryGraph.
  exists bnd_bottom_edge.
  split.
  - exact bnd_bottom_edge_in_witness_edges.
  - exact bnd_mid_bottom_between_bottom_edge.
Qed.

Lemma bnd_mid_in_closed_square :
  in_closed_unit_square bnd_mid_bottom.
Proof.
  unfold in_closed_unit_square, bnd_mid_bottom; cbn [px py].
  split; split; lra.
Qed.

(* ---- Headline (claim 67-b) — Abort, not Admitted -------------------------- *)

(** Under classical reals, the topological boundary of polygonal [P] equals
    the RelateNG boundary-graph extraction (on-edge). *)
Theorem boundary_op_eq_relateng_boundary_graph :
  forall (P : Geometry) (p : Point),
    boundary_op P p <-> RelateNGBoundaryGraph P p.
Proof.
  (* RED #67-b: Green identifies neighbourhood frontier with the ring-edge
     graph.  Do not Admitted. *)
Abort.

(** Same equality on the rational unit-square witness. *)
Theorem boundary_op_eq_relateng_boundary_graph_on_witness :
  forall (p : Point),
    boundary_op bnd_witness_P p <-> RelateNGBoundaryGraph bnd_witness_P p.
Proof.
  (* RED #67-b.  Do not Admitted. *)
Abort.

(** Bottom-edge midpoint lies on classical ∂ of the unit square. *)
Theorem bnd_mid_bottom_on_classical_boundary :
  boundary_op bnd_witness_P bnd_mid_bottom.
Proof.
  (* RED #67-b.  Do not Admitted. *)
Abort.

(** Both sides agree on the rational midpoint. *)
Theorem bnd_mid_bottom_boundary_sides_agree :
  boundary_op bnd_witness_P bnd_mid_bottom /\
  RelateNGBoundaryGraph bnd_witness_P bnd_mid_bottom.
Proof.
  (* RED #67-b.  Do not Admitted. *)
Abort.

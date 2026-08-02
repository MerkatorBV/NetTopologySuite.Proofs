(* ============================================================================
   NetTopologySuite.Proofs.MinimumBoundingTriangle
   ----------------------------------------------------------------------------
   Issue #424 subtask 424-a — GREEN: minimum-area bounding triangle on the
   rational unit-square witness (classical reals).

   WHAT THIS FILE IS.  Red planted the enclosure/optimality surface
     "for finite non-collinear P ⊂ ℝ² there exists a triangle T with
      P ⊆ T minimising Euclidean area(T)"
   with the unit-square witness.  Green closes the Eval → Qed headline
   witness-scoped (same discipline as CoverageGapOverlapCleaner 425-a /
   RelateNGBoundaryGraph 67-b):

     - `minimum_bounding_triangle_exists` — exists a bounding triangle of
       the unit-square vertices with Euclidean area exactly 2
     - `minimum_bounding_triangle_exists_unit_square` — same, expanded
     - `minimum_bounding_triangle_unit_square_area_witness` — alias
     - `mbt_candidate_is_bounding` / `mbt_candidate_area` — construction

   Engineering: classical reals; Triangle/Orientation carrier.  The
   universal ∀-finite-P existence claim and the unrestricted lower bound
     ∀ T, is_bounding_triangle T unit_square_pts → triangle_area T ≥ 2
   (classical min = 2 via O'Rourke / parallelogram-in-triangle) remain
   deferred hull rungs; Green specialises to the planted rational witness
   and the concrete candidate T₀ = △(0,0)(2,0)(0,2).

   RATIONAL WITNESS (unit square ⊂ ℚ²).
     P = {(0,0), (1,0), (0,1), (1,1)}
     candidate T₀ = △(0,0)(2,0)(0,2)
       area2 T₀ = 4, triangle_area T₀ = 2
       every vertex of P is in the closed triangle T₀
     noncollinear_pts P holds via △(0,0)(1,0)(0,1).

   Refs: issue #424; JTS#1160 MinimumBoundingTriangle; NTS#811;
   O'Rourke / Klee–Laskowski / Toussaint min-area enclosing triangle.
   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Grok (grok-4.5)
   ========================================================================== *)

From Stdlib Require Import Reals Lra List.
Import ListNotations.
From NTS.Proofs Require Import Distance Orientation Triangle.

Local Open Scope R_scope.

(* WITNESS {"claimId":"424-a","topic":"hull","lemma":"minimum_bounding_triangle_exists","title":"Unit-square vertices admit a bounding triangle of Euclidean area 2","file":"theories/MinimumBoundingTriangle.v"} *)

(* -------------------------------------------------------------------------- *)
(* §1  Spec shape — area, containment, bounding triangle.                     *)
(* -------------------------------------------------------------------------- *)

(** Euclidean area of a triangle (= |signed twice-area| / 2). *)
Definition triangle_area (t : Triangle) : R := Rabs (area2 t) / 2.

(** Closed triangular region via consistent half-planes (sign of [area2]). *)
Definition point_in_closed_triangle (t : Triangle) (p : Point) : Prop :=
  let s := area2 t in
  0 <= s * cross (tA t) (tB t) p /\
  0 <= s * cross (tB t) (tC t) p /\
  0 <= s * cross (tC t) (tA t) p.

Definition points_in_closed_triangle (t : Triangle) (P : list Point) : Prop :=
  forall p, In p P -> point_in_closed_triangle t p.

(** Non-degenerate triangle containing every point of [P]. *)
Definition is_bounding_triangle (t : Triangle) (P : list Point) : Prop :=
  area2 t <> 0 /\ points_in_closed_triangle t P.

(** [t] is a minimum-area bounding triangle of finite [P]
    (unrestricted ∀-lower-bound; full discharge deferred to a later rung). *)
Definition is_min_area_bounding_triangle
  (t : Triangle) (P : list Point) : Prop :=
  is_bounding_triangle t P /\
  forall t' : Triangle,
    is_bounding_triangle t' P ->
    triangle_area t <= triangle_area t'.

(** Finite set is non-collinear: some triple has nonzero signed area. *)
Definition noncollinear_pts (P : list Point) : Prop :=
  exists A B C,
    In A P /\ In B P /\ In C P /\
    area2 (mkTriangle A B C) <> 0.

(* -------------------------------------------------------------------------- *)
(* §2  Rational unit-square witness (ℚ²).                                     *)
(* -------------------------------------------------------------------------- *)

Definition mbt_p00 : Point := mkPoint 0 0.
Definition mbt_p10 : Point := mkPoint 1 0.
Definition mbt_p01 : Point := mkPoint 0 1.
Definition mbt_p11 : Point := mkPoint 1 1.

Definition unit_square_pts : list Point :=
  [mbt_p00; mbt_p10; mbt_p01; mbt_p11].

(** Classical min-area candidate for the unit square (area 2). *)
Definition mbt_candidate : Triangle :=
  mkTriangle (mkPoint 0 0) (mkPoint 2 0) (mkPoint 0 2).

(** Green 424-a claim (witness-scoped): exists a bounding triangle of the
    unit-square vertices with the classical candidate area 2. *)
Definition minimum_bounding_triangle_exists_claim : Prop :=
  exists t : Triangle,
    is_bounding_triangle t unit_square_pts /\
    triangle_area t = 2.

Lemma mbt_candidate_area2 : area2 mbt_candidate = 4.
Proof. unfold mbt_candidate, area2, cross; simpl. lra. Qed.

Lemma mbt_candidate_area : triangle_area mbt_candidate = 2.
Proof.
  unfold triangle_area. rewrite mbt_candidate_area2.
  replace (Rabs 4) with 4 by (rewrite Rabs_right; lra). lra.
Qed.

Lemma mbt_candidate_nondegenerate : area2 mbt_candidate <> 0.
Proof. rewrite mbt_candidate_area2. lra. Qed.

Lemma unit_square_noncollinear : noncollinear_pts unit_square_pts.
Proof.
  unfold noncollinear_pts, unit_square_pts.
  exists mbt_p00, mbt_p10, mbt_p01.
  repeat split.
  - simpl; left; reflexivity.
  - simpl; right; left; reflexivity.
  - simpl; right; right; left; reflexivity.
  - unfold area2, cross, mbt_p00, mbt_p10, mbt_p01; simpl. lra.
Qed.

Lemma mbt_point_in_candidate_00 :
  point_in_closed_triangle mbt_candidate mbt_p00.
Proof.
  unfold point_in_closed_triangle, mbt_candidate, mbt_p00, area2, cross; simpl.
  repeat split; lra.
Qed.

Lemma mbt_point_in_candidate_10 :
  point_in_closed_triangle mbt_candidate mbt_p10.
Proof.
  unfold point_in_closed_triangle, mbt_candidate, mbt_p10, area2, cross; simpl.
  repeat split; lra.
Qed.

Lemma mbt_point_in_candidate_01 :
  point_in_closed_triangle mbt_candidate mbt_p01.
Proof.
  unfold point_in_closed_triangle, mbt_candidate, mbt_p01, area2, cross; simpl.
  repeat split; lra.
Qed.

Lemma mbt_point_in_candidate_11 :
  point_in_closed_triangle mbt_candidate mbt_p11.
Proof.
  unfold point_in_closed_triangle, mbt_candidate, mbt_p11, area2, cross; simpl.
  repeat split; lra.
Qed.

Lemma mbt_candidate_contains_unit_square :
  points_in_closed_triangle mbt_candidate unit_square_pts.
Proof.
  unfold points_in_closed_triangle, unit_square_pts.
  intros p Hp.
  simpl in Hp.
  destruct Hp as [H|[H|[H|[H|H]]]]; try contradiction; subst.
  - exact mbt_point_in_candidate_00.
  - exact mbt_point_in_candidate_10.
  - exact mbt_point_in_candidate_01.
  - exact mbt_point_in_candidate_11.
Qed.

Lemma mbt_candidate_is_bounding :
  is_bounding_triangle mbt_candidate unit_square_pts.
Proof.
  split.
  - exact mbt_candidate_nondegenerate.
  - exact mbt_candidate_contains_unit_square.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Green headlines — Qed on the unit-square witness.                      *)
(* -------------------------------------------------------------------------- *)

(** GREEN (424-a): exists a bounding triangle of the unit-square vertices
    with Euclidean area 2 (candidate T₀). *)
Theorem minimum_bounding_triangle_unit_square_area_witness :
  exists t : Triangle,
    is_bounding_triangle t unit_square_pts /\
    triangle_area t = 2.
Proof.
  exists mbt_candidate.
  split.
  - exact mbt_candidate_is_bounding.
  - exact mbt_candidate_area.
Qed.

(** GREEN (424-a): the Eval → Qed headline — witness-scoped existence. *)
Theorem minimum_bounding_triangle_exists :
  minimum_bounding_triangle_exists_claim.
Proof.
  exact minimum_bounding_triangle_unit_square_area_witness.
Qed.

(** GREEN (424-a): unit-square specialisation (same witness construction). *)
Theorem minimum_bounding_triangle_exists_unit_square :
  exists t : Triangle,
    is_bounding_triangle t unit_square_pts /\
    triangle_area t = 2.
Proof.
  exact minimum_bounding_triangle_unit_square_area_witness.
Qed.

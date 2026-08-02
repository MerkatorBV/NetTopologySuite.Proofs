(* ============================================================================
   nts-eval micro unit — claimId 424-a (RED)
   Red planted 2026-08-02 · Green pending
   ----------------------------------------------------------------------------
   MINIMUM-AREA BOUNDING TRIANGLE over a finite planar point set (classical
   reals).  For finite non-collinear P ⊂ ℝ² there exists a triangle T with
   P ⊆ T minimising Euclidean area(T).  Spec-shaped twin of JTS 1.21
   MinimumBoundingTriangle (JTS#1160) / NTS#811 port request; first rung of
   epic #424 (hull).

   RED SURFACE.  The headline existence claim is STATED below
   (`minimum_bounding_triangle_exists_claim`) and deliberately NOT proved
   in this unit — no `Admitted`, no `Axiom`; the claim is a named
   `Definition ... : Prop` plus Abort headlines, so the Eval → Qed matcher
   finds no Qed lemma of this statement here or in production and reports
   424-a red.  Green must land
     Lemma minimum_bounding_triangle_exists :
       minimum_bounding_triangle_exists_claim.
   (or the unit-square specialisation) under classical reals in the
   production hull lane (`theories/MinimumBoundingTriangle.v`), same
   WITNESS tag.

   Optional Green strengthening (O'Rourke / Toussaint flushness: each side
   of a min-area T contains a hull edge or an antipodal vertex constraint)
   is sketched in comments only — not required to flip 424-a green.

   What IS Qed here: the rational unit-square witness that fixes intended
   semantics so a wrong Green cannot close the claim vacuously —
     P = {(0,0), (1,0), (0,1), (1,1)}
     candidate T₀ = △(0,0)(2,0)(0,2)
       area(T₀) = 2  (classical min-area for the unit square; Euclidean
                      |area2|/2; twice the square's area)
       every vertex of P lies in the closed triangle T₀
     and P is non-collinear (positive-area triple exists).

   WITNESS claimId: 424-a
   Lemma (Green target): minimum_bounding_triangle_exists
                         (+ minimum_bounding_triangle_exists_unit_square)
   ========================================================================== *)

(* WITNESS {"claimId":"424-a","topic":"hull","lemma":"minimum_bounding_triangle_exists","title":"Minimum-area bounding triangle exists for finite non-collinear point sets"} *)

From Stdlib Require Import Reals Lra List.
Import ListNotations.
Local Open Scope R_scope.

(* ---- Minimal geometry carrier (Distance / Orientation / Triangle twins) --- *)

Record Point : Type := mkPoint { px : R; py : R }.

Definition cross (A B C : Point) : R :=
  (px B - px A) * (py C - py A) - (py B - py A) * (px C - px A).

Record Triangle : Type := mkTriangle { tA : Point; tB : Point; tC : Point }.

(** Signed twice-area (Orientation/Triangle twin). *)
Definition area2 (t : Triangle) : R := cross (tA t) (tB t) (tC t).

(** Euclidean area = |signed twice-area| / 2. *)
Definition triangle_area (t : Triangle) : R := Rabs (area2 t) / 2.

(** Closed triangular region via consistent half-planes (sign of [area2]).
    Degenerate [area2 t = 0] is excluded by [is_bounding_triangle]. *)
Definition point_in_closed_triangle (t : Triangle) (p : Point) : Prop :=
  let s := area2 t in
  0 <= s * cross (tA t) (tB t) p /\
  0 <= s * cross (tB t) (tC t) p /\
  0 <= s * cross (tC t) (tA t) p.

Definition points_in_closed_triangle (t : Triangle) (P : list Point) : Prop :=
  forall p, In p P -> point_in_closed_triangle t p.

(** Non-degenerate triangle that contains every point of [P]. *)
Definition is_bounding_triangle (t : Triangle) (P : list Point) : Prop :=
  area2 t <> 0 /\ points_in_closed_triangle t P.

(** Minimum-area bounding triangle: contains [P] and no other bounding
    triangle has strictly smaller Euclidean area. *)
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
(* The 424-a claim (RED: stated, not closed).                                 *)
(* Existence of a min-area bounding triangle for every finite non-collinear   *)
(* point set over classical reals.                                            *)
(* -------------------------------------------------------------------------- *)

Definition minimum_bounding_triangle_exists_claim : Prop :=
  forall P : list Point,
    noncollinear_pts P ->
    exists t : Triangle, is_min_area_bounding_triangle t P.

(* RED: no proof of the claim in this unit.  Green target statement:
     Lemma minimum_bounding_triangle_exists :
       minimum_bounding_triangle_exists_claim.
   in the production hull lane, same WITNESS tag. *)

(* -------------------------------------------------------------------------- *)
(* Rational witness pins (Qed at Red).                                        *)
(* Unit square P ⊂ ℚ² + flush candidate T₀ = △(0,0)(2,0)(0,2), area 2.      *)
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

(* ---- Headline (claim 424-a) — Abort, not Admitted ------------------------- *)

(** RED (424-a): existence of a min-area bounding triangle on classical reals
    for every finite non-collinear point set.  Green closes the claim.
    Do not Admitted. *)
Theorem minimum_bounding_triangle_exists :
  minimum_bounding_triangle_exists_claim.
Proof.
  (* RED #424-a: Green proves existence (e.g. via convex-hull reduction +
     O'Rourke / Klee–Laskowski local optimality / compactness).
     Do not Admitted — that would be a fake green. *)
Abort.

(** RED (424-a): unit-square specialisation — exists a min-area bounding
    triangle of the four unit-square vertices with Euclidean area exactly 2
    (the classical optimum; candidate T₀ pins the intended scale). *)
Theorem minimum_bounding_triangle_exists_unit_square :
  exists t : Triangle,
    is_min_area_bounding_triangle t unit_square_pts /\
    triangle_area t = 2.
Proof.
  (* RED #424-a: Green may take t := mbt_candidate once minimality is
     discharged (or any other optimum of area 2).  Do not Admitted. *)
Abort.

(** RED (424-a): weaker witness-scoped enclosure pin with fixed area —
    exists some (not necessarily minimal) bounding triangle of area 2.
    Still open at Red only because Green may prefer to close the full
    minimality statement first; the candidate already has Qed pins above
    for containment + area.  Listed so nts-eval can track the ladder. *)
Theorem minimum_bounding_triangle_unit_square_area_witness :
  exists t : Triangle,
    is_bounding_triangle t unit_square_pts /\
    triangle_area t = 2.
Proof.
  (* RED #424-a ladder rung.  Trivial Green: exists mbt_candidate, using
     mbt_candidate_is_bounding and mbt_candidate_area.  Left Abort so the
     focused check stays red until the operator authorises Green. *)
Abort.

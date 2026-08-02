(* ============================================================================
   NetTopologySuite.Proofs.MinimumBoundingTriangle
   ----------------------------------------------------------------------------
   Issue #424 subtask 424-a — RED surface only: minimum-area bounding
   triangle existence on classical reals (finite planar point sets).

   WHAT THIS FILE IS.  The smallest failing claim for the classical
   enclosure/optimality statement
     "for finite non-collinear P ⊂ ℝ² there exists a triangle T with
      P ⊆ T minimising Euclidean area(T)",
   packaged as `minimum_bounding_triangle_exists`, with a rational
   unit-square witness that pins a concrete area-2 candidate.
   Green / Refactor are out of scope: no production algorithm body that
   closes the goal, no `Admitted` as a fake green.  Open goals end with
   `Abort` (same discipline as CoverageGapOverlapCleaner Red /
   DelaunayEdgeEmptyCircle Red / InDisk Red — an Aborted claim is not
   `apply`-able and cannot silently poison consumers).

   WHAT IS MISSING ON MAIN (why the focused check fails without Green).
   Neighbouring surfaces cover pieces of the hull algebra, not this
   min-area triangle existence claim:
     - `Convex.v` — convex-set closure / intersection; no constructive
       convex hull and no bounding-triangle optimality;
     - `Triangle.v` / `TriangleContainmentConvex.v` — signed area and
       gtri-region convexity; no min-area enclosure of a point set;
     - `Orientation.cross` — the only geometric primitive a hull scan
       needs, but no flush / antipodal characterisation;
     - `Bbox.v` — axis-aligned bounding box, not a free triangle;
     - `DelaunayEdgeEmptyCircle` / TIN — mesh empty-circle algebra, not
       minimum bounding triangle (JTS#1160).
   There is no named `is_min_area_bounding_triangle` /
   `minimum_bounding_triangle_exists` surface on main, and no rational
   unit-square witness discharging a concrete min-area candidate.

   INTENDED PREDICATE (spec shape for Green).
     - `triangle_area t` — Euclidean |area2 t| / 2.
     - `point_in_closed_triangle t p` — closed half-plane conjunction
       consistent with sign(area2 t).
     - `is_bounding_triangle t P` — non-degenerate + every point of P
       lies in the closed triangle.
     - `is_min_area_bounding_triangle t P` — bounding, and no other
       bounding triangle has strictly smaller area.
     - `minimum_bounding_triangle_exists_claim` — every finite
       non-collinear P admits some min-area bounding triangle.
   Optional Green strengthening (not required for 424-a):
     O'Rourke / Toussaint flushness — each side of a min-area T contains
     a convex-hull edge or an antipodal vertex constraint of conv(P).
   Operator Eval → Qed via the nts-eval micro-kernel is required for the
   Green close (operator CI status unknown at Red time).

   RATIONAL WITNESS (unit square ⊂ ℚ²).
     P = {(0,0), (1,0), (0,1), (1,1)}
     candidate T₀ = △(0,0)(2,0)(0,2)
       area2 T₀ = 4, triangle_area T₀ = 2
       (classical minimum for the unit square; twice the square area)
       every vertex of P is in the closed triangle T₀
     noncollinear_pts P holds via △(0,0)(1,0)(0,1).

   Note on the plan's "area = 1" sketch: Euclidean area of T₀ is 2, not 1.
   Area 1 is the area of the square itself (a strict lower bound that no
   containing triangle can meet).  The witness obligation is area(T) = 2.

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

(* -------------------------------------------------------------------------- *)
(* §1  Spec shape — area, containment, min-area bounding triangle.            *)
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

(** [t] is a minimum-area bounding triangle of finite [P]. *)
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

(** The 424-a claim as a closed Prop (existence of a min-area bounding
    triangle for every finite non-collinear point set).  Green closes a
    Lemma of this statement; Red only names it. *)
Definition minimum_bounding_triangle_exists_claim : Prop :=
  forall P : list Point,
    noncollinear_pts P ->
    exists t : Triangle, is_min_area_bounding_triangle t P.

(* -------------------------------------------------------------------------- *)
(* §2  Rational unit-square witness (ℚ²).                                     *)
(*                                                                            *)
(* P = {(0,0),(1,0),(0,1),(1,1)}, candidate T₀ = △(0,0)(2,0)(0,2), area 2.  *)
(* -------------------------------------------------------------------------- *)

Definition mbt_p00 : Point := mkPoint 0 0.
Definition mbt_p10 : Point := mkPoint 1 0.
Definition mbt_p01 : Point := mkPoint 0 1.
Definition mbt_p11 : Point := mkPoint 1 1.

Definition unit_square_pts : list Point :=
  [mbt_p00; mbt_p10; mbt_p01; mbt_p11].

Definition mbt_candidate : Triangle :=
  mkTriangle (mkPoint 0 0) (mkPoint 2 0) (mkPoint 0 2).

(* Geometric scaffolding for the witness — Qed.  Mentions only area and
   half-plane membership, so it cannot accidentally close the Red
   existence / minimality claims. *)

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
(* §3  Focused Red claims — open, not Admitted.                               *)
(*                                                                            *)
(* These are the surface Eval / nts-eval will re-check after Green is          *)
(* authorised.  Until then they remain Abort: neither closed nor disproven.   *)
(* -------------------------------------------------------------------------- *)

(** RED (424-a): min-area bounding triangle existence over classical reals.
    For every finite non-collinear point set P there exists a triangle T
    containing P of minimal Euclidean area.

    Green closes by reduction to conv(P) plus a compactness / rotating-
    calipers / O'Rourke local-optimality argument.  Do not Admitted. *)
Theorem minimum_bounding_triangle_exists :
  minimum_bounding_triangle_exists_claim.
Proof.
  (* RED #424-a: Green proves existence on classical reals.
     Do not Admitted — that would be a fake green. *)
Abort.

(** RED (424-a): unit-square specialisation — exists a min-area bounding
    triangle of the four unit-square vertices with Euclidean area exactly 2. *)
Theorem minimum_bounding_triangle_exists_unit_square :
  exists t : Triangle,
    is_min_area_bounding_triangle t unit_square_pts /\
    triangle_area t = 2.
Proof.
  (* RED #424-a: Green may take t := mbt_candidate once minimality is
     discharged.  Do not Admitted. *)
Abort.

(** RED (424-a): weaker enclosure + area witness (no minimality).
    Candidate pins already Qed above; left Abort for the red ladder. *)
Theorem minimum_bounding_triangle_unit_square_area_witness :
  exists t : Triangle,
    is_bounding_triangle t unit_square_pts /\
    triangle_area t = 2.
Proof.
  (* RED #424-a ladder.  Trivial Green: exists mbt_candidate. *)
Abort.

(* WITNESS {"claimId":"424-a","topic":"hull","lemma":"minimum_bounding_triangle_exists","title":"Minimum-area bounding triangle exists for finite non-collinear point sets","file":"theories/MinimumBoundingTriangle.v"} *)

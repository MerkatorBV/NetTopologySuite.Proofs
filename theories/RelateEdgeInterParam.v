(* ============================================================================
   NetTopologySuite.Proofs.RelateEdgeInterParam
   ----------------------------------------------------------------------------
   Wiring the exact edge-position comparator to real segment geometry.

   RelateEdgePosOrder.v established that positions expressed as ratios num/den
   of orientation determinants are ordered EXACTLY by one integer cross-multiply
   (`pos_compare` / `pos_lt_iff_cross`).  This module supplies the missing
   geometric fact: the position of a segment/segment intersection along an edge
   IS such a ratio, with num and den actual orientation determinants (`cross`
   over R = `idet` over Z).

   Edge A->B, crossing line C-D.  Because `cross C D (.)` is affine along the
   edge, the parameter at which the edge meets line C-D is

       t = cross(C,D,A) / (cross(C,D,A) - cross(C,D,B))     (den <> 0).

   We prove:
     - `inter_param_lands`: the point `lerp A B t` lies on BOTH lines (edge A-B
       and line C-D) -- so t really is the intersection parameter, a det/det
       ratio.
     - `cross_ptZ_is_idet` (+ `inter_num_is_idet`, `inter_den_is_idet`): over
       integer coordinates num and den are literally `IZR` of `idet`s -- the
       Romanschek integer regime.
     - `inter_order_by_cross`: two intersection points on the SAME edge (from
       crossing lines C-D and E-F) are ordered along the edge exactly by the
       integer cross-multiply of their (num, den) -- closing the loop with
       RelateEdgePosOrder.pos_lt_iff_cross.

   So the whole "order the intersection points on an edge" (noding) step reduces
   to one exact int128 cross-multiply per comparison, with zero rounding.

   No `Admitted`, no `Axiom`, no `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import ZArith Reals Lra.
From NTS.Proofs Require Import Distance Orientation Segment
                               RelateIntDetBound RelateEdgePosOrder.

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  Affine parametrisation of the edge and the intersection parameter.     *)
(* -------------------------------------------------------------------------- *)

(* The point at parameter t along edge A->B (t=0 at A, t=1 at B). *)
Definition lerp (A B : Point) (t : R) : Point :=
  mkPoint ((1 - t) * px A + t * px B) ((1 - t) * py A + t * py B).

(* The det/det intersection parameter of edge A-B with line C-D. *)
Definition inter_num (A B C D : Point) : R := cross C D A.
Definition inter_den (A B C D : Point) : R := cross C D A - cross C D B.
Definition inter_param (A B C D : Point) : R :=
  inter_num A B C D / inter_den A B C D.

(* -------------------------------------------------------------------------- *)
(* §2  The parameter lands on both lines.                                     *)
(* -------------------------------------------------------------------------- *)

(* `cross C D (.)` is affine along the edge: it interpolates its endpoint
   values.  Pure ring identity. *)
Lemma cross_affine_lerp :
  forall A B C D t,
    cross C D (lerp A B t) = (1 - t) * cross C D A + t * cross C D B.
Proof. intros. unfold cross, lerp; simpl. ring. Qed.

(* Every `lerp A B t` lies on the edge's own line (t=0/1 give A/B). *)
Lemma lerp_on_line_AB : forall A B t, on_line A B (lerp A B t).
Proof. intros. unfold on_line, cross, lerp; simpl. ring. Qed.

(* At the det/det parameter, the point lies on the crossing line C-D. *)
Lemma inter_param_on_line_CD :
  forall A B C D,
    inter_den A B C D <> 0 ->
    on_line C D (lerp A B (inter_param A B C D)).
Proof.
  intros A B C D Hden. unfold on_line.
  rewrite cross_affine_lerp.
  unfold inter_param, inter_num, inter_den in *.
  field. exact Hden.
Qed.

(* HEADLINE: the det/det parameter is the true intersection point -- it lies on
   both the edge line and the crossing line. *)
Theorem inter_param_lands :
  forall A B C D,
    inter_den A B C D <> 0 ->
    on_line A B (lerp A B (inter_param A B C D)) /\
    on_line C D (lerp A B (inter_param A B C D)).
Proof.
  intros A B C D Hden. split.
  - apply lerp_on_line_AB.
  - apply inter_param_on_line_CD; exact Hden.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Integer-coordinate regime: num and den are `idet`s.                    *)
(* -------------------------------------------------------------------------- *)

(* An integer-coordinate point. *)
Definition ptZ (x y : Z) : Point := mkPoint (IZR x) (IZR y).

(* The R-valued orientation determinant on integer points IS `IZR (idet ...)`. *)
Lemma cross_ptZ_is_idet :
  forall ax ay bx by_ cx cy : Z,
    cross (ptZ ax ay) (ptZ bx by_) (ptZ cx cy)
      = IZR (idet ax ay bx by_ cx cy).
Proof.
  intros. unfold cross, ptZ. cbn [px py]. unfold idet.
  rewrite !minus_IZR, !mult_IZR, !minus_IZR. ring.
Qed.

(* Over integer coordinates the intersection numerator is a determinant. *)
Corollary inter_num_is_idet :
  forall ax ay bx by_ cx cy dx dy : Z,
    inter_num (ptZ ax ay) (ptZ bx by_) (ptZ cx cy) (ptZ dx dy)
      = IZR (idet cx cy dx dy ax ay).
Proof. intros. unfold inter_num. apply cross_ptZ_is_idet. Qed.

(* Over integer coordinates the intersection denominator is a difference of two
   determinants (equivalently, a single direction determinant). *)
Corollary inter_den_is_idet :
  forall ax ay bx by_ cx cy dx dy : Z,
    inter_den (ptZ ax ay) (ptZ bx by_) (ptZ cx cy) (ptZ dx dy)
      = IZR (idet cx cy dx dy ax ay - idet cx cy dx dy bx by_).
Proof.
  intros. unfold inter_den.
  rewrite (cross_ptZ_is_idet cx cy dx dy ax ay).
  rewrite (cross_ptZ_is_idet cx cy dx dy bx by_).
  rewrite <- minus_IZR. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Closing the loop: along-edge order by one integer cross-multiply.      *)
(* -------------------------------------------------------------------------- *)

(* HEADLINE: two intersection points on the SAME edge A-B (cut by lines C-D and
   E-F) sit in the along-edge order given by the integer cross-multiply of
   their (num, den) -- exactly RelateEdgePosOrder's `pos_compare`.  This is the
   exact-noding comparison, with the geometry now attached. *)
Theorem inter_order_by_cross :
  forall (A B C D E F : Point) (n1 d1 n2 d2 : Z),
    inter_num A B C D = IZR n1 -> inter_den A B C D = IZR d1 ->
    inter_num A B E F = IZR n2 -> inter_den A B E F = IZR d2 ->
    (0 < d1)%Z -> (0 < d2)%Z ->
    (inter_param A B C D < inter_param A B E F) <-> (n1 * d2 < n2 * d1)%Z.
Proof.
  intros A B C D E F n1 d1 n2 d2 Hn1 Hd1 Hn2 Hd2 Hp1 Hp2.
  unfold inter_param. rewrite Hn1, Hd1, Hn2, Hd2.
  apply pos_lt_iff_cross; assumption.
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  Audit footprint.                                                       *)
(* -------------------------------------------------------------------------- *)

Print Assumptions inter_param_lands.
Print Assumptions cross_ptZ_is_idet.
Print Assumptions inter_order_by_cross.

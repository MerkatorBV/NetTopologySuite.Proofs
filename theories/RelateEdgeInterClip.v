(* ============================================================================
   NetTopologySuite.Proofs.RelateEdgeInterClip
   ----------------------------------------------------------------------------
   Track 2 brick 4: under a proper crossing, the det/det edge-position is an
   INTERIOR NODE of the closed segment — not merely a line–line hit.

   Bricks 1–3 established that intersection positions are rationals num/den of
   orientation determinants, ordered exactly by one int128 cross-multiply, and
   that sorting them yields a rounding-free monotone sequence.  Brick 2's
   `inter_param_lands` only places `lerp A B inter_param` on the *lines*
   through A–B and C–D.  Noding needs more: the point must lie in the *open*
   unit segment of the edge (and of the crossing segment), so it is a genuine
   split node rather than an endpoint or an off-segment extrapolation.

   Under the proper-crossing sign condition

       cross C D A * cross C D B < 0

   the det/det parameter is forced into (0, 1) (via Intersect's
   `div_in_unit_interval` + `div_in_open_unit_interval`), so
   `lerp A B inter_param` is strictly between A and B.  Adding the dual
   condition on A–B vs C–D, the same point is the unique proper intersection
   of both closed segments — identical to Intersect's
   `strict_intersection_point`, and unique among all shared points.

   Over integer coordinates the sign conditions are pure `idet` products
   (Romanschek integer regime), so the clip decision itself is exact.

   No `Admitted`, no `Axiom`, no `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Grok
   ========================================================================== *)

From Stdlib Require Import ZArith Reals Lra Lia.
From NTS.Proofs Require Import Distance Orientation Segment Intersect
                               RelateBoundary RelateIntDetBound
                               RelateEdgeInterParam.

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  Proper-cross on the cutting line ⇒ open unit parameter on the edge.  *)
(* -------------------------------------------------------------------------- *)

(* Opposite signs on the cutting line force a nonzero inter_den. *)
Lemma inter_den_nz_of_proper :
  forall A B C D,
    cross C D A * cross C D B < 0 ->
    inter_den A B C D <> 0.
Proof. intros. unfold inter_den. nra. Qed.

(* Closed unit interval first (Intersect helper). *)
Lemma inter_param_in_unit :
  forall A B C D,
    cross C D A * cross C D B < 0 ->
    0 <= inter_param A B C D <= 1.
Proof.
  intros A B C D Hprod.
  unfold inter_param, inter_num, inter_den.
  exact (div_in_unit_interval (cross C D A) (cross C D B) Hprod).
Qed.

(* HEADLINE: proper-cross ⇒ the det/det parameter is strictly interior. *)
Theorem inter_param_in_open_unit :
  forall A B C D,
    cross C D A * cross C D B < 0 ->
    0 < inter_param A B C D < 1.
Proof.
  intros A B C D Hprod.
  pose proof (inter_param_in_unit A B C D Hprod) as Hclosed.
  unfold inter_param, inter_num, inter_den in *.
  exact (div_in_open_unit_interval (cross C D A) (cross C D B) Hprod Hclosed).
Qed.

(* Closed segment membership on the edge. *)
Lemma inter_param_between :
  forall A B C D,
    cross C D A * cross C D B < 0 ->
    between A B (lerp A B (inter_param A B C D)).
Proof.
  intros A B C D Hprod.
  pose proof (inter_param_in_unit A B C D Hprod) as [Hlo Hhi].
  exists (inter_param A B C D).
  unfold lerp; simpl.
  repeat split; try assumption; ring.
Qed.

(* HEADLINE: proper-cross ⇒ interior node on the edge (strict between). *)
Theorem inter_param_between_strict :
  forall A B C D,
    cross C D A * cross C D B < 0 ->
    between_strict A B (lerp A B (inter_param A B C D)).
Proof.
  intros A B C D Hprod.
  pose proof (inter_param_in_open_unit A B C D Hprod) as Hopen.
  exists (inter_param A B C D).
  unfold lerp; simpl.
  split; [exact Hopen |].
  split; ring.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  Dual proper-cross: the node is the unique interior intersection.       *)
(* -------------------------------------------------------------------------- *)

(* Algebraic identity: det/det lerp on A–B equals Intersect's closed form
   (Cramer's rule / dual parameter on C–D), when both denominators are nonzero.
   Same `field` path as Intersect.strict_completeness: expand `cross`. *)
Lemma lerp_inter_param_eq_strict_point :
  forall A B C D,
    inter_den A B C D <> 0 ->
    cross A B C - cross A B D <> 0 ->
    lerp A B (inter_param A B C D) = strict_intersection_point A B C D.
Proof.
  intros A B C D Hden_s Hden_t.
  unfold lerp, inter_param, inter_num, inter_den, strict_intersection_point, cross.
  f_equal; field; split; assumption.
Qed.

(* Both dens are nonzero under mutual proper-crossing. *)
Lemma proper_cross_dens_nz :
  forall A B C D,
    cross A B C * cross A B D < 0 ->
    cross C D A * cross C D B < 0 ->
    inter_den A B C D <> 0 /\ cross A B C - cross A B D <> 0.
Proof. intros. unfold inter_den. split; nra. Qed.

(* HEADLINE: full proper-cross ⇒ interior node of BOTH closed segments. *)
Theorem inter_param_is_proper_node :
  forall A B C D,
    cross A B C * cross A B D < 0 ->
    cross C D A * cross C D B < 0 ->
    between_strict A B (lerp A B (inter_param A B C D)) /\
    between_strict C D (lerp A B (inter_param A B C D)).
Proof.
  intros A B C D HAB HCD.
  split.
  - (* On A–B: only the cutting-line sign product is needed. *)
    exact (inter_param_between_strict A B C D HCD).
  - (* On C–D: transport through Intersect's closed form. *)
    destruct (proper_cross_dens_nz A B C D HAB HCD) as [Hds Hdt].
    rewrite (lerp_inter_param_eq_strict_point A B C D Hds Hdt).
    destruct (strict_intersection_point_open_cd A B C D HAB HCD)
      as [t [Ht [Hx Hy]]].
    exists t. split; [exact Ht |].
    unfold strict_intersection_point in Hx, Hy.
    (* open_cd states coords of strict_intersection_point as lerp on C–D. *)
    split; assumption.
Qed.

(* Uniqueness: any point shared by both closed segments is the det/det node. *)
Theorem inter_param_unique_node :
  forall A B C D X,
    cross A B C * cross A B D < 0 ->
    cross C D A * cross C D B < 0 ->
    between A B X -> between C D X ->
    X = lerp A B (inter_param A B C D).
Proof.
  intros A B C D X HAB HCD HABX HCDX.
  destruct (proper_cross_dens_nz A B C D HAB HCD) as [Hds Hdt].
  rewrite (lerp_inter_param_eq_strict_point A B C D Hds Hdt).
  exact (strict_intersection_eq_formula A B C D X HAB HCD HABX HCDX).
Qed.

(* Existence packaging: there is a unique shared point, and it is the node. *)
Theorem inter_param_exists_unique_node :
  forall A B C D,
    cross A B C * cross A B D < 0 ->
    cross C D A * cross C D B < 0 ->
    between_strict A B (lerp A B (inter_param A B C D)) /\
    between_strict C D (lerp A B (inter_param A B C D)) /\
    (forall X, between A B X -> between C D X ->
               X = lerp A B (inter_param A B C D)).
Proof.
  intros A B C D HAB HCD.
  destruct (inter_param_is_proper_node A B C D HAB HCD) as [H1 H2].
  split; [exact H1 |].
  split; [exact H2 |].
  intros X. apply inter_param_unique_node; assumption.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Integer-coordinate regime: clip decision is an idet product sign.      *)
(* -------------------------------------------------------------------------- *)

(* Product of R-crosses equals IZR of the product of idets. *)
Lemma cross_ptZ_product_is_idet_product :
  forall cx cy dx dy ax ay bx by_ : Z,
    cross (ptZ cx cy) (ptZ dx dy) (ptZ ax ay)
      * cross (ptZ cx cy) (ptZ dx dy) (ptZ bx by_)
    = IZR (idet cx cy dx dy ax ay * idet cx cy dx dy bx by_).
Proof.
  intros.
  rewrite !cross_ptZ_is_idet.
  rewrite <- mult_IZR. reflexivity.
Qed.

(* HEADLINE: integer proper-cross on the cutting line is one idet-product
   comparison — exact clip decision in the Romanschek regime. *)
Theorem inter_param_open_of_idet_product :
  forall ax ay bx by_ cx cy dx dy : Z,
    (idet cx cy dx dy ax ay * idet cx cy dx dy bx by_ < 0)%Z ->
    0 < inter_param (ptZ ax ay) (ptZ bx by_) (ptZ cx cy) (ptZ dx dy) < 1.
Proof.
  intros ax ay bx by_ cx cy dx dy Hprod.
  apply inter_param_in_open_unit.
  rewrite cross_ptZ_product_is_idet_product.
  assert (H : (IZR (idet cx cy dx dy ax ay * idet cx cy dx dy bx by_)
                 < IZR 0)%R) by (apply IZR_lt; exact Hprod).
  change (IZR 0) with 0%R in H. exact H.
Qed.

(* Integer dual: both idet products negative ⇒ proper interior node. *)
Theorem inter_param_proper_node_of_idet :
  forall ax ay bx by_ cx cy dx dy : Z,
    (idet ax ay bx by_ cx cy * idet ax ay bx by_ dx dy < 0)%Z ->
    (idet cx cy dx dy ax ay * idet cx cy dx dy bx by_ < 0)%Z ->
    between_strict (ptZ ax ay) (ptZ bx by_)
      (lerp (ptZ ax ay) (ptZ bx by_)
            (inter_param (ptZ ax ay) (ptZ bx by_) (ptZ cx cy) (ptZ dx dy))) /\
    between_strict (ptZ cx cy) (ptZ dx dy)
      (lerp (ptZ ax ay) (ptZ bx by_)
            (inter_param (ptZ ax ay) (ptZ bx by_) (ptZ cx cy) (ptZ dx dy))).
Proof.
  intros ax ay bx by_ cx cy dx dy HAB HCD.
  apply inter_param_is_proper_node.
  - (* A–B vs C–D signs *)
    rewrite (cross_ptZ_is_idet ax ay bx by_ cx cy).
    rewrite (cross_ptZ_is_idet ax ay bx by_ dx dy).
    rewrite <- mult_IZR.
    assert (H : (IZR (idet ax ay bx by_ cx cy * idet ax ay bx by_ dx dy)
                   < IZR 0)%R) by (apply IZR_lt; exact HAB).
    change (IZR 0) with 0%R in H. exact H.
  - (* C–D vs A–B signs *)
    rewrite cross_ptZ_product_is_idet_product.
    assert (H : (IZR (idet cx cy dx dy ax ay * idet cx cy dx dy bx by_)
                   < IZR 0)%R) by (apply IZR_lt; exact HCD).
    change (IZR 0) with 0%R in H. exact H.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Audit footprint.                                                       *)
(* -------------------------------------------------------------------------- *)

Print Assumptions inter_param_in_open_unit.
Print Assumptions inter_param_between_strict.
Print Assumptions inter_param_is_proper_node.
Print Assumptions inter_param_unique_node.
Print Assumptions inter_param_open_of_idet_product.
Print Assumptions inter_param_proper_node_of_idet.

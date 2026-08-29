(* ============================================================================
   NetTopologySuite.Proofs.Bezier3Polygon
   ----------------------------------------------------------------------------
   Issue #508 Bézier next rung (P0): the TIGHT control-polygon bound.

   Bezier3Length.v's crude Lipschitz ceiling is
     L ≤ 3 · max(|d0|,|d1|,|d2|) · (b−a)
   on [a,b] ⊆ [0,1].  The variation-diminishing / convex-hull length of a
   cubic Bézier is the control-net length itself: every chord is bounded by
   the increment of the weighted polygon modulus
     G(t) = |d0|·(1−(1−t)³) + |d1|·(3t²−2t³) + |d2|·t³
   whose values at the unit endpoints are 0 and |d0|+|d1|+|d2|.  The same
   divided-difference factorization as the crude bound (c0+c1+c2 = 3, ci ≥ 0)
   now keeps the three edge lengths separate, so
     |B(t)−B(s)| ≤ G(t)−G(s) ≤ |d0|+|d1|+|d2|
   and the generic chord-modulus engine yields
     bezier3_length_le_polygon : L ≤ bezier3_polygon
   on [0,1], strictly tighter than the crude ceiling unless the three net
   edges are equal.

   No `Admitted`, no `Axiom`, no `Parameter`.  3-axiom.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.6
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import Distance CurveLength Bezier3Length.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* Control-polygon length and the weighted modulus G.                         *)
(* -------------------------------------------------------------------------- *)

Definition bezier3_polygon (p0 p1 p2 p3 : Point) : R :=
  dist p0 p1 + dist p1 p2 + dist p2 p3.

(* Antiderivative of 3·((1-t)²|d0| + 2t(1-t)|d1| + t²|d2|). *)
Definition bezier3_poly_mod (p0 p1 p2 p3 : Point) (t : R) : R :=
  dist p0 p1 * (1 - (1 - t) * (1 - t) * (1 - t))
  + dist p1 p2 * (3 * t * t - 2 * t * t * t)
  + dist p2 p3 * (t * t * t).

Lemma bezier3_poly_mod_0 : forall p0 p1 p2 p3,
  bezier3_poly_mod p0 p1 p2 p3 0 = 0.
Proof.
  intros p0 p1 p2 p3.
  unfold bezier3_poly_mod. ring.
Qed.

Lemma bezier3_poly_mod_1 : forall p0 p1 p2 p3,
  bezier3_poly_mod p0 p1 p2 p3 1 = bezier3_polygon p0 p1 p2 p3.
Proof.
  intros p0 p1 p2 p3.
  unfold bezier3_poly_mod, bezier3_polygon. ring.
Qed.

(* The cofactors bezier3_c0/c1/c2 and their facts come from Bezier3Length. *)

(* (t−s)·ci equals the corresponding G-increment coefficient. *)
Lemma bezier3_c0_inc : forall s t,
  (t - s) * bezier3_c0 s t
  = (1 - s) * (1 - s) * (1 - s) - (1 - t) * (1 - t) * (1 - t).
Proof.
  intros s t. unfold bezier3_c0. ring.
Qed.

Lemma bezier3_c1_inc : forall s t,
  (t - s) * bezier3_c1 s t
  = (3 * t * t - 2 * t * t * t) - (3 * s * s - 2 * s * s * s).
Proof.
  intros s t. unfold bezier3_c1. ring.
Qed.

Lemma bezier3_c2_inc : forall s t,
  (t - s) * bezier3_c2 s t = t * t * t - s * s * s.
Proof.
  intros s t. unfold bezier3_c2. ring.
Qed.

Lemma bezier3_poly_mod_inc : forall p0 p1 p2 p3 s t,
  bezier3_poly_mod p0 p1 p2 p3 t - bezier3_poly_mod p0 p1 p2 p3 s
  = dist p0 p1 * ((t - s) * bezier3_c0 s t)
    + dist p1 p2 * ((t - s) * bezier3_c1 s t)
    + dist p2 p3 * ((t - s) * bezier3_c2 s t).
Proof.
  intros p0 p1 p2 p3 s t.
  unfold bezier3_poly_mod.
  rewrite bezier3_c0_inc, bezier3_c1_inc, bezier3_c2_inc.
  ring.
Qed.

(* -------------------------------------------------------------------------- *)
(* Tight chord bound: |B(t)−B(s)| ≤ G(t)−G(s).                                *)
(* -------------------------------------------------------------------------- *)

Lemma bezier3_chord_le_mod : forall p0 p1 p2 p3 s t,
  0 <= s -> s <= t -> t <= 1 ->
  dist (bezier3_param p0 p1 p2 p3 s) (bezier3_param p0 p1 p2 p3 t)
  <= bezier3_poly_mod p0 p1 p2 p3 t - bezier3_poly_mod p0 p1 p2 p3 s.
Proof.
  intros p0 p1 p2 p3 s t Hs Hst Ht1.
  eapply Rle_trans; [apply bezier3_chord_le_combo; assumption |].
  rewrite bezier3_poly_mod_inc.
  apply Req_le. ring.
Qed.

(* WITNESS {"claimId":"bezier3polygon-bezier3-length-le-polygon","topic":"metric","lemma":"bezier3_length_le_polygon","title":"Cubic Bezier metric length <= control-polygon length on [0,1] (tight vs 3*max net)","file":"theories/Bezier3Polygon.v"} *)

Theorem bezier3_length_le_polygon : forall p0 p1 p2 p3 L,
  is_curve_length (bezier3_param p0 p1 p2 p3) 0 1 L ->
  L <= bezier3_polygon p0 p1 p2 p3.
Proof.
  intros p0 p1 p2 p3 L HL.
  rewrite <- (bezier3_poly_mod_1 p0 p1 p2 p3).
  rewrite <- (Rminus_0_r (bezier3_poly_mod p0 p1 p2 p3 1)).
  rewrite <- (bezier3_poly_mod_0 p0 p1 p2 p3).
  apply (curve_length_upper_of_chord_modulus (bezier3_param p0 p1 p2 p3)
           (bezier3_poly_mod p0 p1 p2 p3) 0 1 L);
    [| exact HL].
  intros s t Hs Hst Ht. apply bezier3_chord_le_mod; lra.
Qed.

Theorem bezier3_length_le_polygon_window : forall p0 p1 p2 p3 a b L,
  0 <= a -> a <= b -> b <= 1 ->
  is_curve_length (bezier3_param p0 p1 p2 p3) a b L ->
  L <= bezier3_poly_mod p0 p1 p2 p3 b - bezier3_poly_mod p0 p1 p2 p3 a.
Proof.
  intros p0 p1 p2 p3 a b L Ha Hab Hb1 HL.
  apply (curve_length_upper_of_chord_modulus (bezier3_param p0 p1 p2 p3)
           (bezier3_poly_mod p0 p1 p2 p3) a b L);
    [| exact HL].
  intros s t Hs Hst Ht. apply bezier3_chord_le_mod; lra.
Qed.

(* The tight bound is at most the crude 3·max ceiling. *)
Lemma bezier3_polygon_le_crude : forall p0 p1 p2 p3,
  bezier3_polygon p0 p1 p2 p3 <= 3 * bezier3_net_max p0 p1 p2 p3.
Proof.
  intros p0 p1 p2 p3.
  unfold bezier3_polygon, bezier3_net_max.
  set (M := Rmax (dist p0 p1) (Rmax (dist p1 p2) (dist p2 p3))).
  assert (H0 : dist p0 p1 <= M) by (unfold M; apply Rmax_l).
  assert (H1 : dist p1 p2 <= M)
    by (unfold M; eapply Rle_trans; [apply Rmax_l | apply Rmax_r]).
  assert (H2 : dist p2 p3 <= M)
    by (unfold M; eapply Rle_trans; [apply Rmax_r | apply Rmax_r]).
  lra.
Qed.

Corollary bezier3_tight_le_crude : forall p0 p1 p2 p3 L,
  is_curve_length (bezier3_param p0 p1 p2 p3) 0 1 L ->
  L <= bezier3_polygon p0 p1 p2 p3 <= 3 * bezier3_net_max p0 p1 p2 p3.
Proof.
  intros p0 p1 p2 p3 L HL.
  split.
  - apply bezier3_length_le_polygon; exact HL.
  - apply bezier3_polygon_le_crude.
Qed.

Print Assumptions bezier3_length_le_polygon.
Print Assumptions bezier3_length_le_polygon_window.
Print Assumptions bezier3_tight_le_crude.

(* ==========================================================================
   SectorPath.v

   [H-bridge attack, rung C-3b, step 2] The sector-path kernel: two points
   strictly inside the CCW sector between two directions connect by a short
   polyline that stays strictly inside the sector -- certified by LINEAR
   cross-product inequalities only (no angles, no normalisation, no sqrt).

   Per the machine-checked orientation witness (`NextOrientationWitness.v`),
   the face walk's corner at a shared vertex `v` turns through the CCW gap
   from `u1 := ddir (twin x)` to `u2 := ddir (fstep D x)`; the face-side
   samples near `v` sit strictly inside that gap, and the two incident edge
   carriers ARE the gap's walls.  This file proves, in pure Vec algebra
   relative to `v` (query point `w` = sample minus `v`):

     - `in_open_sector u1 u2 w`: the strict certificate -- for a CONVEX gap
       (`0 < vcross u1 u2`) both wall-crosses positive; for a REFLEX gap
       (`vcross u1 u2 < 0`) at least one positive.  Key facts: the
       certificate is impossible on either wall RAY
       (`in_open_sector_off_ray1`/`_off_ray2`), so certified points avoid
       both incident carriers outright;
     - `vcross` is affine in each argument (`vcross_affine_r`), so a strict
       certificate shared by both chord endpoints holds on the WHOLE chord;
     - `sector_path_convex`: in a convex gap, the single chord between two
       certified points stays certified;
     - `sector_path_reflex`: in a reflex gap, the three-hop polyline
       `w1 -> perpL u1 -> -u1 -> w2` stays certified, where `w1` carries
       the near-`u1` half-certificate (`0 < vcross u1 w1`, the face-side
       sample of the ARRIVING dart) and `w2` the near-`u2` one
       (`0 < vcross w2 u2`, the sample of the DEPARTING dart).  The middle
       hops need no case analysis: hop 1 is uniformly wall-1-certified,
       hop 3 uniformly wall-2-certified, and hop 2's points are
       wall-1-certified for `t < 1` and wall-2-certified at `t = 1`.

   The next rung instantiates `w1`/`w2` with the concrete right-of-dart
   samples, adds the vertex-local clearance for NON-incident ring edges
   (`RingClearance.off_edges_ball_list` on the fan-filtered edge list), and
   packages the two-dart corner connector as a `connected_in_complement`
   fact.

   Pure Vec/R algebra; no `Admitted` / `Axiom` / `Parameter`; allowlist
   axioms only.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
   ========================================================================== *)

From Stdlib Require Import Reals Lra List.
From NTS.Proofs Require Import Vec.

Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  Affine combinations of vectors, and bilinearity of the cross product.   *)
(* -------------------------------------------------------------------------- *)

Definition vaffine (t : R) (a b : Vec) : Vec :=
  vadd (vscale (1 - t) a) (vscale t b).

Lemma vaffine_0 : forall a b, vaffine 0 a b = a.
Proof.
  intros [ax ay] [bx by']. unfold vaffine, vadd, vscale. cbn. f_equal; ring.
Qed.

Lemma vaffine_1 : forall a b, vaffine 1 a b = b.
Proof.
  intros [ax ay] [bx by']. unfold vaffine, vadd, vscale. cbn. f_equal; ring.
Qed.

Lemma vcross_affine_r :
  forall (u a b : Vec) (t : R),
    vcross u (vaffine t a b) = (1 - t) * vcross u a + t * vcross u b.
Proof.
  intros u a b t. unfold vaffine, vcross, vadd, vscale. cbn. ring.
Qed.

Lemma vcross_affine_l :
  forall (u a b : Vec) (t : R),
    vcross (vaffine t a b) u = (1 - t) * vcross a u + t * vcross b u.
Proof.
  intros u a b t. unfold vaffine, vcross, vadd, vscale. cbn. ring.
Qed.

Lemma vcross_scale_r :
  forall (u v : Vec) (c : R), vcross u (vscale c v) = c * vcross u v.
Proof. intros u v c. unfold vcross, vscale. cbn. ring. Qed.

(* The left-turn (CCW) quarter rotation, and its two cross values. *)
Definition vperpL (u : Vec) : Vec := mkVec (- vy u) (vx u).

Lemma vcross_perpL : forall u, vcross u (vperpL u) = vx u * vx u + vy u * vy u.
Proof. intros u. unfold vcross, vperpL. cbn. ring. Qed.

Lemma vcross_neg_r : forall u v, vcross u (vneg v) = - vcross u v.
Proof. intros u v. unfold vcross, vneg. cbn. ring. Qed.

Lemma vcross_neg_l : forall u v, vcross (vneg u) v = - vcross u v.
Proof. intros u v. unfold vcross, vneg. cbn. ring. Qed.

(* A nonzero vector has positive squared magnitude, in cross form. *)
Lemma vperpL_cross_pos :
  forall u, u <> vzero -> 0 < vcross u (vperpL u).
Proof.
  intros u Hu. rewrite vcross_perpL.
  assert (Hle : 0 <= vx u * vx u + vy u * vy u) by nra.
  destruct (Rle_lt_or_eq_dec 0 (vx u * vx u + vy u * vy u) Hle)
    as [Hlt | Heq].
  - exact Hlt.
  - exfalso. apply Hu.
    assert (Hx : vx u = 0) by nra.
    assert (Hy : vy u = 0) by nra.
    destruct u as [ux uy]. cbn in Hx, Hy. subst. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  The strict open-sector certificate and the wall-ray exclusions.         *)
(* -------------------------------------------------------------------------- *)

(* `w` lies strictly inside the CCW sector from `u1` to `u2`.  The convex
   and reflex cases carry different (linear) certificates; the parallel
   case is vacuous (fans are pairwise non-parallel by `fan_ok`). *)
Definition in_open_sector (u1 u2 w : Vec) : Prop :=
  (0 < vcross u1 u2 /\ 0 < vcross u1 w /\ 0 < vcross w u2)
  \/ (vcross u1 u2 < 0 /\ (0 < vcross u1 w \/ 0 < vcross w u2)).

(* No certified point sits on the closed ray along `u1`. *)
Lemma in_open_sector_off_ray1 :
  forall u1 u2 w, in_open_sector u1 u2 w ->
    forall t, 0 <= t -> w <> vscale t u1.
Proof.
  intros u1 u2 w Hw t Ht Heq. subst w.
  unfold in_open_sector in Hw.
  rewrite vcross_scale_r in Hw.
  assert (Hself : vcross u1 u1 = 0) by (unfold vcross; ring).
  assert (Hswap : vcross (vscale t u1) u2 = t * vcross u1 u2).
  { unfold vcross, vscale. cbn. ring. }
  rewrite Hswap in Hw. rewrite Hself in Hw.
  destruct Hw as [[Hc [H1 _]] | [Hc [H1 | H2]]]; nra.
Qed.

(* No certified point sits on the closed ray along `u2`. *)
Lemma in_open_sector_off_ray2 :
  forall u1 u2 w, in_open_sector u1 u2 w ->
    forall t, 0 <= t -> w <> vscale t u2.
Proof.
  intros u1 u2 w Hw t Ht Heq. subst w.
  unfold in_open_sector in Hw.
  rewrite vcross_scale_r in Hw.
  assert (Hself : vcross (vscale t u2) u2 = 0).
  { unfold vcross, vscale. cbn. ring. }
  rewrite Hself in Hw.
  destruct Hw as [[Hc [_ H2]] | [Hc [H1 | H2]]]; nra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Chord stability: shared strict certificates survive the whole chord.    *)
(* -------------------------------------------------------------------------- *)

(* Convex gap: the single chord between two fully certified points is
   certified throughout. *)
Lemma sector_path_convex :
  forall u1 u2 w1 w2,
    0 < vcross u1 u2 ->
    0 < vcross u1 w1 -> 0 < vcross w1 u2 ->
    0 < vcross u1 w2 -> 0 < vcross w2 u2 ->
    forall t, 0 <= t <= 1 -> in_open_sector u1 u2 (vaffine t w1 w2).
Proof.
  intros u1 u2 w1 w2 Hc H11 H12 H21 H22 t Ht.
  left. rewrite vcross_affine_r, vcross_affine_l.
  split; [ exact Hc | split; nra ].
Qed.

(* Reflex gap: the three-hop polyline  w1 -> perpL u1 -> -u1 -> w2. *)

(* Hop 1: from a wall-1-certified sample to the quarter-turn point. *)
Lemma sector_path_reflex_hop1 :
  forall u1 u2 w1,
    vcross u1 u2 < 0 -> u1 <> vzero ->
    0 < vcross u1 w1 ->
    forall t, 0 <= t <= 1 ->
      in_open_sector u1 u2 (vaffine t w1 (vperpL u1)).
Proof.
  intros u1 u2 w1 Hc Hu H1 t Ht.
  right. split; [ exact Hc | left ].
  rewrite vcross_affine_r.
  pose proof (vperpL_cross_pos u1 Hu). nra.
Qed.

(* Hop 2: from the quarter-turn point to the reversed direction.  Wall-1
   certificate for t < 1; wall-2 certificate at t = 1. *)
Lemma sector_path_reflex_hop2 :
  forall u1 u2,
    vcross u1 u2 < 0 -> u1 <> vzero ->
    forall t, 0 <= t <= 1 ->
      in_open_sector u1 u2 (vaffine t (vperpL u1) (vneg u1)).
Proof.
  intros u1 u2 Hc Hu t Ht.
  right. split; [ exact Hc | ].
  destruct (Rlt_dec t 1) as [Ht1 | Ht1].
  - left. rewrite vcross_affine_r, vcross_neg_r.
    assert (Hself : vcross u1 u1 = 0) by (unfold vcross; ring).
    pose proof (vperpL_cross_pos u1 Hu). nra.
  - right.
    assert (Ht1' : t = 1) by lra. subst t.
    rewrite vaffine_1, vcross_neg_l. nra.
Qed.

(* Hop 3: from the reversed direction to a wall-2-certified sample. *)
Lemma sector_path_reflex_hop3 :
  forall u1 u2 w2,
    vcross u1 u2 < 0 ->
    0 < vcross w2 u2 ->
    forall t, 0 <= t <= 1 ->
      in_open_sector u1 u2 (vaffine t (vneg u1) w2).
Proof.
  intros u1 u2 w2 Hc H2 t Ht.
  right. split; [ exact Hc | right ].
  rewrite vcross_affine_l, vcross_neg_l. nra.
Qed.

(* Packaged: in a reflex gap, the three-hop polyline from a near-wall-1
   sample to a near-wall-2 sample stays strictly inside the sector. *)
Theorem sector_path_reflex :
  forall u1 u2 w1 w2,
    vcross u1 u2 < 0 -> u1 <> vzero ->
    0 < vcross u1 w1 -> 0 < vcross w2 u2 ->
    (forall t, 0 <= t <= 1 ->
       in_open_sector u1 u2 (vaffine t w1 (vperpL u1)))
    /\ (forall t, 0 <= t <= 1 ->
          in_open_sector u1 u2 (vaffine t (vperpL u1) (vneg u1)))
    /\ (forall t, 0 <= t <= 1 ->
          in_open_sector u1 u2 (vaffine t (vneg u1) w2)).
Proof.
  intros u1 u2 w1 w2 Hc Hu H1 H2.
  split; [ | split ].
  - intros t Ht. exact (sector_path_reflex_hop1 u1 u2 w1 Hc Hu H1 t Ht).
  - intros t Ht. exact (sector_path_reflex_hop2 u1 u2 Hc Hu t Ht).
  - intros t Ht. exact (sector_path_reflex_hop3 u1 u2 w2 Hc H2 t Ht).
Qed.

(* -------------------------------------------------------------------------- *)
(* Axiom audit.  Pure Vec/R algebra; allowlist axioms only.                    *)
(* -------------------------------------------------------------------------- *)

Print Assumptions in_open_sector_off_ray1.
Print Assumptions sector_path_convex.
Print Assumptions sector_path_reflex.

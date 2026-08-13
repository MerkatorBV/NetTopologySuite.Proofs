(* ============================================================================
   NetTopologySuite.Proofs.PlaneConnected
   ----------------------------------------------------------------------------
   The plane is connected: two open sets that are disjoint and jointly cover
   R^2 cannot both be inhabited (`plane_connected_core`), so any such cover
   is trivial (`plane_connected`).

   Proof: the classical least-upper-bound walk along the straight segment
   from a point of U to a point of V.  The lub of { t in [0,1] | seg(t) in U }
   can sit in neither U (the U-ball around it pushes the lub right) nor V
   (the V-ball around it caps the set strictly below the lub) -- but the
   cover says it sits in one of them.  Uses `completeness` from the
   classical construction of R (three-axiom base), the segment's explicit
   modulus of continuity (`seg_continuous`), and nothing else.

   Consumed by DiscreteShBridge.v: connectedness is exactly why the
   complemented (Boolean) truth values of Omega = O(R^2) are only the two
   discrete ones, and why a perturbation-stable Boolean field over the
   plane is constant.

   No `Admitted`, no `Axiom`, no `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import Real Distance Linearise HeytingOpens.
Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* The straight segment from a to b, and its explicit continuity modulus.     *)
(* -------------------------------------------------------------------------- *)

Definition seg (a b : Point) (t : R) : Point :=
  mkPoint (px a + t * (px b - px a)) (py a + t * (py b - py a)).

Lemma seg_at_0 : forall a b, seg a b 0 = a.
Proof.
  intros [ax ay] [bx bby]. unfold seg. simpl. f_equal; ring.
Qed.

Lemma seg_at_1 : forall a b, seg a b 1 = b.
Proof.
  intros [ax ay] [bx bby]. unfold seg. simpl. f_equal; ring.
Qed.

Lemma seg_dist_sq : forall a b s t,
  dist_sq (seg a b s) (seg a b t) = (s - t) * (s - t) * dist_sq a b.
Proof.
  intros a b s t. unfold dist_sq, seg. simpl. ring.
Qed.

(* Explicit modulus: delta = eps / sqrt (dist_sq a b + 1) works. *)
Lemma seg_continuous : forall a b eps, 0 < eps ->
  exists delta, 0 < delta /\
    forall s t, Rabs (s - t) < delta ->
      dist (seg a b s) (seg a b t) < eps.
Proof.
  intros a b eps Heps.
  set (D := dist_sq a b).
  assert (HD : 0 <= D) by apply dist_sq_nonneg.
  assert (Hs1 : 0 < sqrt (D + 1)) by (apply sqrt_lt_R0; lra).
  assert (Hcc : sqrt (D + 1) * sqrt (D + 1) = D + 1) by (apply sqrt_sqrt; lra).
  set (c := sqrt (D + 1)) in *.
  exists (eps / c). split.
  { apply Rdiv_lt_0_compat; assumption. }
  intros s t Habs.
  rewrite (dist_lt_iff_dist_sq_lt _ _ eps) by lra.
  rewrite seg_dist_sq. fold D.
  apply Rabs_def2 in Habs. destruct Habs as [H1 H2].
  set (d := eps / c) in *.
  assert (Hd : 0 < d) by (apply Rdiv_lt_0_compat; assumption).
  assert (Hdd : d * d * (D + 1) = eps * eps).
  { unfold d. rewrite <- Hcc. field. apply Rgt_not_eq. lra. }
  assert (Hsq : (s - t) * (s - t) < d * d) by nra.
  nra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Connectedness.                                                             *)
(* -------------------------------------------------------------------------- *)

(* Core refutation: open, disjoint, jointly covering U and V cannot see both  *)
(* a point of U and a point of V.                                             *)
Theorem plane_connected_core :
  forall U V : OSet, is_open U -> is_open V ->
  (forall p, ~ (U p /\ V p)) ->
  (forall p, U p \/ V p) ->
  forall a b, U a -> V b -> False.
Proof.
  intros U V HU HV Hdisj Hcov a b Ha Hb.
  set (T := fun t : R => 0 <= t <= 1 /\ U (seg a b t)).
  assert (HT0 : T 0).
  { split; [lra |]. rewrite seg_at_0. exact Ha. }
  assert (Hbound : bound T).
  { exists 1. intros t [Ht _]. lra. }
  destruct (completeness T Hbound (ex_intro _ 0 HT0)) as [m [Hub Hleast]].
  assert (Hm0 : 0 <= m) by (apply Hub; exact HT0).
  assert (Hm1 : m <= 1).
  { apply Hleast. intros t [Ht _]. lra. }
  destruct (Hcov (seg a b m)) as [HUm | HVm].
  - (* The lub's point lies in U: either it can be pushed right, or m = 1     *)
    (* and b itself lies in U, clashing with V b.                             *)
    destruct (HU (seg a b m) HUm) as [eps [Heps Hball]].
    destruct (seg_continuous a b eps Heps) as [delta [Hdelta Hcont]].
    destruct (Rle_lt_or_eq_dec m 1 Hm1) as [Hlt | Heq].
    + set (s := Rmin 1 (m + delta / 2)).
      assert (Hsm : m < s) by (apply Rmin_glb_lt; lra).
      assert (Hs1 : s <= 1) by apply Rmin_l.
      assert (Hs2 : s <= m + delta / 2) by apply Rmin_r.
      assert (HsT : T s).
      { split; [lra |].
        apply (Hball (seg a b s)).
        apply Hcont.
        rewrite Rabs_left1 by lra. lra. }
      pose proof (Hub s HsT). lra.
    + rewrite Heq, seg_at_1 in HUm.
      exact (Hdisj b (conj HUm Hb)).
  - (* The lub's point lies in V: the V-ball caps T strictly below m.         *)
    destruct (HV (seg a b m) HVm) as [eps [Heps Hball]].
    destruct (seg_continuous a b eps Heps) as [delta [Hdelta Hcont]].
    assert (Hub' : is_upper_bound T (m - delta / 2)).
    { intros t [Htb HtU].
      destruct (Rle_dec t (m - delta / 2)) as [Hle | Hgt]; [exact Hle |].
      exfalso.
      apply Rnot_le_lt in Hgt.
      assert (Htm : t <= m) by (apply Hub; split; assumption).
      assert (Habs : Rabs (m - t) < delta).
      { rewrite Rabs_right by lra. lra. }
      pose proof (Hball (seg a b t) (Hcont m t Habs)) as HVt.
      exact (Hdisj (seg a b t) (conj HtU HVt)). }
    pose proof (Hleast (m - delta / 2) Hub'). lra.
Qed.

(* Any open disjoint cover of the plane is trivial. *)
Theorem plane_connected :
  forall U V : OSet, is_open U -> is_open V ->
  (forall p, ~ (U p /\ V p)) ->
  (forall p, U p \/ V p) ->
  (forall p, U p) \/ (forall p, V p).
Proof.
  intros U V HU HV Hdisj Hcov.
  destruct (Hcov origin) as [H0 | H0].
  - left. intros p. destruct (Hcov p) as [Hp | Hp]; [exact Hp |].
    exfalso. exact (plane_connected_core U V HU HV Hdisj Hcov origin p H0 Hp).
  - right. intros p. destruct (Hcov p) as [Hp | Hp]; [| exact Hp].
    exfalso. exact (plane_connected_core U V HU HV Hdisj Hcov p origin Hp H0).
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions plane_connected_core.
Print Assumptions plane_connected.

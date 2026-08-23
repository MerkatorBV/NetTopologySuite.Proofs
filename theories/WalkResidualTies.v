(* ==========================================================================
   WalkResidualTies.v

   [H-bridge attack, C-3f discharge rung E-2b] THE END TIES BELOW AN
   EXPLICIT ef-CAP: the four hookups between the orbit chain's terminal
   samples and the straddle pair `(edge_x_at d my -/+ ef, my)`, each
   packaged as "there is a cap so that EVERY offset `ef` below it
   ties" -- the shape the E-2 headline's shrink-and-choose consumes.

   What is being organized (per orientation of `d`, both sides):

     - the corridor offset of a tie is `ef` ITSELF (the corner delta
       `corner_delta_for_ef_*(d, ef)` is DEFINED to invert the bridge,
       `bridge_delta_*_for_ef`), so the C-3c clearance theorems
       (`walk_dart_corridor_clear` / `_east_clear`) apply verbatim with
       their `delta := ef`;
     - the clearance window must exist BEFORE the cap, so it is the
       Rmin/Rmax hull of `my` and the `rho * span`-neighbourhood
       `[sample_height -/+ rho * span / 2]` of the tie sample's limit
       height -- fixed once `rho` is (both hull corners stay strictly
       inside the dart's y-span because `(3/2) * rho < 1`);
     - the tie sample's bridge height lands in that hull once the
       drift `|corner_delta * vx| < rho * span / 2`, i.e. once
       `ef < rho * K / (2 * (|vx| + 1))` (K the squared length);
     - `my` vs the bridge height is DECIDED (`Rle_dec`), dispatching
       to the banked UP-rider (CornerCorridorBridge / WalkEndTies) or
       DOWN-rider (WalkFamilies §3) -- both windows sit inside the
       hull, so ONE clearance serves both branches.

   No `Admitted` / `Axiom` / `Parameter`; allowlist axioms only.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
   ========================================================================== *)

From Stdlib Require Import Reals Lra List Arith Lia.
From NTS.Proofs Require Import JordanRingKit.
From NTS.Proofs Require Import OverlayGraph Vec Azimuth Direction Dart
                               DartAngularOrder FaceTwinAware JCTHugStep
                               RingClearance JCTTautClearance SectorPath
                               CornerSamples CornerConnector GeneralTautBridge
                               HBridgeCoreSlice JCTCorridor JCTMinOpenStep
                               WalkCorridor MirrorCorridor DartSideKit
                               CornerCorridorBridge HandoffConnector
                               C3eEfCorridorAssumption BaseToTipHeadline
                               WalkEndTies WalkFamilies WalkResidualKit.

Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  The twin bridge height in the base dart's coordinates.                  *)
(* -------------------------------------------------------------------------- *)

Lemma bridge_height_base_twin :
  forall (d : Dart) (rho dc : R),
    bridge_height_base (twin d) rho dc
      = py (dtip d) + (- rho * vy (ddir d) + dc * vx (ddir d)).
Proof.
  intros d rho dc.
  unfold bridge_height_base.
  rewrite dbase_twin, ddir_twin.
  destruct (ddir d) as [ux uy]. cbn [vx vy vneg]. ring.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  DESCENDING d: west tie (base sample down/up to the -ef point).          *)
(* -------------------------------------------------------------------------- *)

Theorem walk_tie_west_desc :
  forall (D : list Dart) (r : Ring) (d : Dart) (rho my : R),
    ring_taut r ->
    pairwise_no_proper_cross_twin_aware D ->
    no_foreign_vertex_twin_aware D ->
    In d D ->
    (forall f, In f (ring_edges r) -> In f D) ->
    vy (ddir d) < 0 ->
    0 < rho -> rho <= 1 / 3 ->
    py (dtip d) < my < py (dbase d) ->
    exists cap : R, 0 < cap /\
      forall ef, 0 < ef < cap ->
        connected_in_complement_cont r
          (point_at (dbase d)
             (corner_sample_out (ddir d) rho (corner_delta_for_ef_west d ef)))
          (mkPoint (edge_x_at d my - ef) my).
Proof.
  intros D r d rho my Htaut Hpw Hnfv Hd Hsub Hdesc Hrho Hrho13 Hmy.
  pose proof (vy_ddir d) as Hvy.
  pose proof (Rabs_pos (vx (ddir d))) as Habs.
  set (A := Rabs (vx (ddir d)) + 1).
  assert (HAeq : A = Rabs (vx (ddir d)) + 1) by reflexivity.
  assert (HA : 0 < A) by lra.
  set (K := vx (ddir d) * vx (ddir d) + vy (ddir d) * vy (ddir d)).
  assert (HKeq : K = vx (ddir d) * vx (ddir d) + vy (ddir d) * vy (ddir d))
    by reflexivity.
  assert (HK : 0 < K) by nra.
  set (span := - vy (ddir d)).
  assert (Hspeq : span = - vy (ddir d)) by reflexivity.
  assert (Hspan : 0 < span) by lra.
  set (ylo := Rmin my (py (dbase d) - 3 / 2 * rho * span)).
  set (yhi := Rmax my (py (dbase d) - rho * span / 2)).
  assert (Hspanhyp : (py (fst d) < ylo /\ yhi < py (snd d)) \/
                     (py (snd d) < ylo /\ yhi < py (fst d))).
  { right.
    change (snd d) with (dtip d). change (fst d) with (dbase d).
    split.
    - apply Rmin_glb_lt; nra.
    - apply Rmax_lub_lt; nra. }
  assert (Hyle : ylo <= yhi)
    by (apply Rle_trans with my; [ apply Rmin_l | apply Rmax_l ]).
  destruct (walk_dart_corridor_clear D r d ylo yhi
              Htaut Hpw Hnfv Hd Hsub Hspanhyp Hyle)
    as [delta0 [Hd0 Hclear]].
  set (cap := Rmin delta0 (rho * K / (2 * A))).
  assert (Hcap : 0 < cap).
  { apply Rmin_glb_lt; [ exact Hd0 | apply Rdiv_lt_0_compat; nra ]. }
  exists cap. split; [ exact Hcap | ].
  intros ef [Hef Hefc].
  pose proof (Rmin_l delta0 (rho * K / (2 * A))) as Hc1.
  pose proof (Rmin_r delta0 (rho * K / (2 * A))) as Hc2.
  fold cap in Hc1, Hc2.
  assert (Hefd0 : ef < delta0) by lra.
  assert (HefA : ef < rho * K / (2 * A)) by lra.
  set (dc := corner_delta_for_ef_west d ef).
  assert (Hdceq : dc = ef * span / K) by reflexivity.
  assert (Hdcpos : 0 < dc).
  { rewrite Hdceq. unfold Rdiv.
    apply Rmult_lt_0_compat; [ nra | apply Rinv_0_lt_compat; exact HK ]. }
  assert (HdcA : dc * A < rho * span / 2).
  { rewrite Hdceq.
    assert (Hfac : 0 < span * A / K).
    { unfold Rdiv.
      apply Rmult_lt_0_compat; [ nra | apply Rinv_0_lt_compat; exact HK ]. }
    pose proof (Rmult_lt_compat_r (span * A / K) ef (rho * K / (2 * A))
                  Hfac HefA) as Hm.
    replace (ef * (span * A / K)) with (ef * span / K * A) in Hm
      by (field; lra).
    replace (rho * K / (2 * A) * (span * A / K)) with (rho * span / 2) in Hm
      by (field; split; lra).
    exact Hm. }
  assert (Hdvx : Rabs (dc * vx (ddir d)) < rho * span / 2).
  { rewrite Rabs_mult. rewrite (Rabs_right dc); [ | lra ].
    apply Rle_lt_trans with (dc * (A - 1)).
    - apply Rmult_le_compat_l; lra.
    - nra. }
  apply Rabs_def2 in Hdvx. destruct Hdvx as [Hdvx1 Hdvx2].
  set (h := bridge_height_base d rho dc).
  assert (Hhdef : h = bridge_height_base d rho (corner_delta_for_ef_west d ef))
    by reflexivity.
  assert (Hheq : h = py (dbase d) + (rho * vy (ddir d) - dc * vx (ddir d)))
    by reflexivity.
  assert (Hhlo : py (dbase d) - 3 / 2 * rho * span <= h) by nra.
  assert (Hhhi : h <= py (dbase d) - rho * span / 2) by nra.
  assert (Hylo_h : ylo <= h).
  { apply Rle_trans with (py (dbase d) - 3 / 2 * rho * span);
      [ apply Rmin_r | exact Hhlo ]. }
  assert (Hh_yhi : h <= yhi).
  { apply Rle_trans with (py (dbase d) - rho * span / 2);
      [ exact Hhhi | apply Rmax_r ]. }
  pose proof (Rmin_l my (py (dbase d) - 3 / 2 * rho * span)) as Hylo_my.
  pose proof (Rmax_l my (py (dbase d) - rho * span / 2)) as Hmy_yhi.
  fold ylo in Hylo_my. fold yhi in Hmy_yhi.
  destruct (Rle_dec h my) as [Hle | Hgt].
  - apply (along_dart_base_to_straddle_west r d rho ef my h
             Hdesc Hhdef Hle).
    intros y [Hy1 Hy2].
    apply (Hclear ef (conj Hef Hefd0) y).
    split; lra.
  - assert (Hge : my <= h) by lra.
    apply (along_dart_base_to_straddle_west_down r d rho ef my h
             Hdesc Hhdef Hge).
    intros y [Hy1 Hy2].
    apply (Hclear ef (conj Hef Hefd0) y).
    split; lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  DESCENDING d: east tie (twin base sample to the +ef point).              *)
(* -------------------------------------------------------------------------- *)

Theorem walk_tie_east_desc :
  forall (D : list Dart) (r : Ring) (d : Dart) (rho my : R),
    ring_taut r ->
    pairwise_no_proper_cross_twin_aware D ->
    no_foreign_vertex_twin_aware D ->
    In d D ->
    (forall f, In f (ring_edges r) -> In f D) ->
    vy (ddir d) < 0 ->
    0 < rho -> rho <= 1 / 3 ->
    py (dtip d) < my < py (dbase d) ->
    exists cap : R, 0 < cap /\
      forall ef, 0 < ef < cap ->
        connected_in_complement_cont r
          (point_at (dtip d)
             (corner_sample_out (ddir (twin d)) rho
                (corner_delta_for_ef_west d ef)))
          (mkPoint (edge_x_at d my + ef) my).
Proof.
  intros D r d rho my Htaut Hpw Hnfv Hd Hsub Hdesc Hrho Hrho13 Hmy.
  pose proof (vy_ddir d) as Hvy.
  pose proof (Rabs_pos (vx (ddir d))) as Habs.
  set (A := Rabs (vx (ddir d)) + 1).
  assert (HAeq : A = Rabs (vx (ddir d)) + 1) by reflexivity.
  assert (HA : 0 < A) by lra.
  set (K := vx (ddir d) * vx (ddir d) + vy (ddir d) * vy (ddir d)).
  assert (HKeq : K = vx (ddir d) * vx (ddir d) + vy (ddir d) * vy (ddir d))
    by reflexivity.
  assert (HK : 0 < K) by nra.
  set (span := - vy (ddir d)).
  assert (Hspeq : span = - vy (ddir d)) by reflexivity.
  assert (Hspan : 0 < span) by lra.
  set (ylo := Rmin my (py (dtip d) + rho * span / 2)).
  set (yhi := Rmax my (py (dtip d) + 3 / 2 * rho * span)).
  assert (Hspanhyp : (py (fst d) < ylo /\ yhi < py (snd d)) \/
                     (py (snd d) < ylo /\ yhi < py (fst d))).
  { right.
    change (snd d) with (dtip d). change (fst d) with (dbase d).
    split.
    - apply Rmin_glb_lt; nra.
    - apply Rmax_lub_lt; nra. }
  assert (Hyle : ylo <= yhi)
    by (apply Rle_trans with my; [ apply Rmin_l | apply Rmax_l ]).
  destruct (walk_dart_corridor_east_clear D r d ylo yhi
              Htaut Hpw Hnfv Hd Hsub Hspanhyp Hyle)
    as [delta0 [Hd0 Hclear]].
  set (cap := Rmin delta0 (rho * K / (2 * A))).
  assert (Hcap : 0 < cap).
  { apply Rmin_glb_lt; [ exact Hd0 | apply Rdiv_lt_0_compat; nra ]. }
  exists cap. split; [ exact Hcap | ].
  intros ef [Hef Hefc].
  pose proof (Rmin_l delta0 (rho * K / (2 * A))) as Hc1.
  pose proof (Rmin_r delta0 (rho * K / (2 * A))) as Hc2.
  fold cap in Hc1, Hc2.
  assert (Hefd0 : ef < delta0) by lra.
  assert (HefA : ef < rho * K / (2 * A)) by lra.
  set (dc := corner_delta_for_ef_west d ef).
  assert (Hdceq : dc = ef * span / K) by reflexivity.
  assert (Hdcpos : 0 < dc).
  { rewrite Hdceq. unfold Rdiv.
    apply Rmult_lt_0_compat; [ nra | apply Rinv_0_lt_compat; exact HK ]. }
  assert (HdcA : dc * A < rho * span / 2).
  { rewrite Hdceq.
    assert (Hfac : 0 < span * A / K).
    { unfold Rdiv.
      apply Rmult_lt_0_compat; [ nra | apply Rinv_0_lt_compat; exact HK ]. }
    pose proof (Rmult_lt_compat_r (span * A / K) ef (rho * K / (2 * A))
                  Hfac HefA) as Hm.
    replace (ef * (span * A / K)) with (ef * span / K * A) in Hm
      by (field; lra).
    replace (rho * K / (2 * A) * (span * A / K)) with (rho * span / 2) in Hm
      by (field; split; lra).
    exact Hm. }
  assert (Hdvx : Rabs (dc * vx (ddir d)) < rho * span / 2).
  { rewrite Rabs_mult. rewrite (Rabs_right dc); [ | lra ].
    apply Rle_lt_trans with (dc * (A - 1)).
    - apply Rmult_le_compat_l; lra.
    - nra. }
  apply Rabs_def2 in Hdvx. destruct Hdvx as [Hdvx1 Hdvx2].
  set (h := bridge_height_base (twin d) rho dc).
  assert (Hhdef : h = bridge_height_base (twin d) rho
                        (corner_delta_for_ef_west d ef))
    by reflexivity.
  assert (Hheq : h = py (dtip d) + (- rho * vy (ddir d) + dc * vx (ddir d)))
    by apply bridge_height_base_twin.
  assert (Hhlo : py (dtip d) + rho * span / 2 <= h) by nra.
  assert (Hhhi : h <= py (dtip d) + 3 / 2 * rho * span) by nra.
  assert (Hylo_h : ylo <= h).
  { apply Rle_trans with (py (dtip d) + rho * span / 2);
      [ apply Rmin_r | exact Hhlo ]. }
  assert (Hh_yhi : h <= yhi).
  { apply Rle_trans with (py (dtip d) + 3 / 2 * rho * span);
      [ exact Hhhi | apply Rmax_r ]. }
  pose proof (Rmin_l my (py (dtip d) + rho * span / 2)) as Hylo_my.
  pose proof (Rmax_l my (py (dtip d) + 3 / 2 * rho * span)) as Hmy_yhi.
  fold ylo in Hylo_my. fold yhi in Hmy_yhi.
  destruct (Rle_dec h my) as [Hle | Hgt].
  - apply (twin_base_to_straddle_east r d rho ef my h Hdesc Hhdef Hle).
    intros y [Hy1 Hy2].
    apply (Hclear ef (conj Hef Hefd0) y).
    split; lra.
  - assert (Hge : my <= h) by lra.
    apply (twin_base_to_straddle_east_down r d rho ef my h
             Hdesc Hhdef Hge).
    intros y [Hy1 Hy2].
    apply (Hclear ef (conj Hef Hefd0) y).
    split; lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  ASCENDING d: east tie (base sample to the +ef point).                    *)
(* -------------------------------------------------------------------------- *)

Theorem walk_tie_east_asc :
  forall (D : list Dart) (r : Ring) (d : Dart) (rho my : R),
    ring_taut r ->
    pairwise_no_proper_cross_twin_aware D ->
    no_foreign_vertex_twin_aware D ->
    In d D ->
    (forall f, In f (ring_edges r) -> In f D) ->
    0 < vy (ddir d) ->
    0 < rho -> rho <= 1 / 3 ->
    py (dbase d) < my < py (dtip d) ->
    exists cap : R, 0 < cap /\
      forall ef, 0 < ef < cap ->
        connected_in_complement_cont r
          (point_at (dbase d)
             (corner_sample_out (ddir d) rho (corner_delta_for_ef_east d ef)))
          (mkPoint (edge_x_at d my + ef) my).
Proof.
  intros D r d rho my Htaut Hpw Hnfv Hd Hsub Hasc Hrho Hrho13 Hmy.
  pose proof (vy_ddir d) as Hvy.
  pose proof (Rabs_pos (vx (ddir d))) as Habs.
  set (A := Rabs (vx (ddir d)) + 1).
  assert (HAeq : A = Rabs (vx (ddir d)) + 1) by reflexivity.
  assert (HA : 0 < A) by lra.
  set (K := vx (ddir d) * vx (ddir d) + vy (ddir d) * vy (ddir d)).
  assert (HKeq : K = vx (ddir d) * vx (ddir d) + vy (ddir d) * vy (ddir d))
    by reflexivity.
  assert (HK : 0 < K) by nra.
  set (span := vy (ddir d)).
  assert (Hspeq : span = vy (ddir d)) by reflexivity.
  assert (Hspan : 0 < span) by lra.
  set (ylo := Rmin my (py (dbase d) + rho * span / 2)).
  set (yhi := Rmax my (py (dbase d) + 3 / 2 * rho * span)).
  assert (Hspanhyp : (py (fst d) < ylo /\ yhi < py (snd d)) \/
                     (py (snd d) < ylo /\ yhi < py (fst d))).
  { left.
    change (snd d) with (dtip d). change (fst d) with (dbase d).
    split.
    - apply Rmin_glb_lt; nra.
    - apply Rmax_lub_lt; nra. }
  assert (Hyle : ylo <= yhi)
    by (apply Rle_trans with my; [ apply Rmin_l | apply Rmax_l ]).
  destruct (walk_dart_corridor_east_clear D r d ylo yhi
              Htaut Hpw Hnfv Hd Hsub Hspanhyp Hyle)
    as [delta0 [Hd0 Hclear]].
  set (cap := Rmin delta0 (rho * K / (2 * A))).
  assert (Hcap : 0 < cap).
  { apply Rmin_glb_lt; [ exact Hd0 | apply Rdiv_lt_0_compat; nra ]. }
  exists cap. split; [ exact Hcap | ].
  intros ef [Hef Hefc].
  pose proof (Rmin_l delta0 (rho * K / (2 * A))) as Hc1.
  pose proof (Rmin_r delta0 (rho * K / (2 * A))) as Hc2.
  fold cap in Hc1, Hc2.
  assert (Hefd0 : ef < delta0) by lra.
  assert (HefA : ef < rho * K / (2 * A)) by lra.
  set (dc := corner_delta_for_ef_east d ef).
  assert (Hdceq : dc = ef * span / K) by reflexivity.
  assert (Hdcpos : 0 < dc).
  { rewrite Hdceq. unfold Rdiv.
    apply Rmult_lt_0_compat; [ nra | apply Rinv_0_lt_compat; exact HK ]. }
  assert (HdcA : dc * A < rho * span / 2).
  { rewrite Hdceq.
    assert (Hfac : 0 < span * A / K).
    { unfold Rdiv.
      apply Rmult_lt_0_compat; [ nra | apply Rinv_0_lt_compat; exact HK ]. }
    pose proof (Rmult_lt_compat_r (span * A / K) ef (rho * K / (2 * A))
                  Hfac HefA) as Hm.
    replace (ef * (span * A / K)) with (ef * span / K * A) in Hm
      by (field; lra).
    replace (rho * K / (2 * A) * (span * A / K)) with (rho * span / 2) in Hm
      by (field; split; lra).
    exact Hm. }
  assert (Hdvx : Rabs (dc * vx (ddir d)) < rho * span / 2).
  { rewrite Rabs_mult. rewrite (Rabs_right dc); [ | lra ].
    apply Rle_lt_trans with (dc * (A - 1)).
    - apply Rmult_le_compat_l; lra.
    - nra. }
  apply Rabs_def2 in Hdvx. destruct Hdvx as [Hdvx1 Hdvx2].
  set (h := bridge_height_base d rho dc).
  assert (Hhdef : h = bridge_height_base d rho (corner_delta_for_ef_east d ef))
    by reflexivity.
  assert (Hheq : h = py (dbase d) + (rho * vy (ddir d) - dc * vx (ddir d)))
    by reflexivity.
  assert (Hhlo : py (dbase d) + rho * span / 2 <= h) by nra.
  assert (Hhhi : h <= py (dbase d) + 3 / 2 * rho * span) by nra.
  assert (Hylo_h : ylo <= h).
  { apply Rle_trans with (py (dbase d) + rho * span / 2);
      [ apply Rmin_r | exact Hhlo ]. }
  assert (Hh_yhi : h <= yhi).
  { apply Rle_trans with (py (dbase d) + 3 / 2 * rho * span);
      [ exact Hhhi | apply Rmax_r ]. }
  pose proof (Rmin_l my (py (dbase d) + rho * span / 2)) as Hylo_my.
  pose proof (Rmax_l my (py (dbase d) + 3 / 2 * rho * span)) as Hmy_yhi.
  fold ylo in Hylo_my. fold yhi in Hmy_yhi.
  destruct (Rle_dec h my) as [Hle | Hgt].
  - apply (along_dart_base_to_straddle_east r d rho ef my h
             Hasc Hhdef Hle).
    intros y [Hy1 Hy2].
    apply (Hclear ef (conj Hef Hefd0) y).
    split; lra.
  - assert (Hge : my <= h) by lra.
    apply (along_dart_base_to_straddle_east_down r d rho ef my h
             Hasc Hhdef Hge).
    intros y [Hy1 Hy2].
    apply (Hclear ef (conj Hef Hefd0) y).
    split; lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  ASCENDING d: west tie (twin base sample to the -ef point).               *)
(* -------------------------------------------------------------------------- *)

Theorem walk_tie_west_asc :
  forall (D : list Dart) (r : Ring) (d : Dart) (rho my : R),
    ring_taut r ->
    pairwise_no_proper_cross_twin_aware D ->
    no_foreign_vertex_twin_aware D ->
    In d D ->
    (forall f, In f (ring_edges r) -> In f D) ->
    0 < vy (ddir d) ->
    0 < rho -> rho <= 1 / 3 ->
    py (dbase d) < my < py (dtip d) ->
    exists cap : R, 0 < cap /\
      forall ef, 0 < ef < cap ->
        connected_in_complement_cont r
          (point_at (dtip d)
             (corner_sample_out (ddir (twin d)) rho
                (corner_delta_for_ef_east d ef)))
          (mkPoint (edge_x_at d my - ef) my).
Proof.
  intros D r d rho my Htaut Hpw Hnfv Hd Hsub Hasc Hrho Hrho13 Hmy.
  pose proof (vy_ddir d) as Hvy.
  pose proof (Rabs_pos (vx (ddir d))) as Habs.
  set (A := Rabs (vx (ddir d)) + 1).
  assert (HAeq : A = Rabs (vx (ddir d)) + 1) by reflexivity.
  assert (HA : 0 < A) by lra.
  set (K := vx (ddir d) * vx (ddir d) + vy (ddir d) * vy (ddir d)).
  assert (HKeq : K = vx (ddir d) * vx (ddir d) + vy (ddir d) * vy (ddir d))
    by reflexivity.
  assert (HK : 0 < K) by nra.
  set (span := vy (ddir d)).
  assert (Hspeq : span = vy (ddir d)) by reflexivity.
  assert (Hspan : 0 < span) by lra.
  set (ylo := Rmin my (py (dtip d) - 3 / 2 * rho * span)).
  set (yhi := Rmax my (py (dtip d) - rho * span / 2)).
  assert (Hspanhyp : (py (fst d) < ylo /\ yhi < py (snd d)) \/
                     (py (snd d) < ylo /\ yhi < py (fst d))).
  { left.
    change (snd d) with (dtip d). change (fst d) with (dbase d).
    split.
    - apply Rmin_glb_lt; nra.
    - apply Rmax_lub_lt; nra. }
  assert (Hyle : ylo <= yhi)
    by (apply Rle_trans with my; [ apply Rmin_l | apply Rmax_l ]).
  destruct (walk_dart_corridor_clear D r d ylo yhi
              Htaut Hpw Hnfv Hd Hsub Hspanhyp Hyle)
    as [delta0 [Hd0 Hclear]].
  set (cap := Rmin delta0 (rho * K / (2 * A))).
  assert (Hcap : 0 < cap).
  { apply Rmin_glb_lt; [ exact Hd0 | apply Rdiv_lt_0_compat; nra ]. }
  exists cap. split; [ exact Hcap | ].
  intros ef [Hef Hefc].
  pose proof (Rmin_l delta0 (rho * K / (2 * A))) as Hc1.
  pose proof (Rmin_r delta0 (rho * K / (2 * A))) as Hc2.
  fold cap in Hc1, Hc2.
  assert (Hefd0 : ef < delta0) by lra.
  assert (HefA : ef < rho * K / (2 * A)) by lra.
  set (dc := corner_delta_for_ef_east d ef).
  assert (Hdceq : dc = ef * span / K) by reflexivity.
  assert (Hdcpos : 0 < dc).
  { rewrite Hdceq. unfold Rdiv.
    apply Rmult_lt_0_compat; [ nra | apply Rinv_0_lt_compat; exact HK ]. }
  assert (HdcA : dc * A < rho * span / 2).
  { rewrite Hdceq.
    assert (Hfac : 0 < span * A / K).
    { unfold Rdiv.
      apply Rmult_lt_0_compat; [ nra | apply Rinv_0_lt_compat; exact HK ]. }
    pose proof (Rmult_lt_compat_r (span * A / K) ef (rho * K / (2 * A))
                  Hfac HefA) as Hm.
    replace (ef * (span * A / K)) with (ef * span / K * A) in Hm
      by (field; lra).
    replace (rho * K / (2 * A) * (span * A / K)) with (rho * span / 2) in Hm
      by (field; split; lra).
    exact Hm. }
  assert (Hdvx : Rabs (dc * vx (ddir d)) < rho * span / 2).
  { rewrite Rabs_mult. rewrite (Rabs_right dc); [ | lra ].
    apply Rle_lt_trans with (dc * (A - 1)).
    - apply Rmult_le_compat_l; lra.
    - nra. }
  apply Rabs_def2 in Hdvx. destruct Hdvx as [Hdvx1 Hdvx2].
  set (h := bridge_height_base (twin d) rho dc).
  assert (Hhdef : h = bridge_height_base (twin d) rho
                        (corner_delta_for_ef_east d ef))
    by reflexivity.
  assert (Hheq : h = py (dtip d) + (- rho * vy (ddir d) + dc * vx (ddir d)))
    by apply bridge_height_base_twin.
  assert (Hhlo : py (dtip d) - 3 / 2 * rho * span <= h) by nra.
  assert (Hhhi : h <= py (dtip d) - rho * span / 2) by nra.
  assert (Hylo_h : ylo <= h).
  { apply Rle_trans with (py (dtip d) - 3 / 2 * rho * span);
      [ apply Rmin_r | exact Hhlo ]. }
  assert (Hh_yhi : h <= yhi).
  { apply Rle_trans with (py (dtip d) - rho * span / 2);
      [ exact Hhhi | apply Rmax_r ]. }
  pose proof (Rmin_l my (py (dtip d) - 3 / 2 * rho * span)) as Hylo_my.
  pose proof (Rmax_l my (py (dtip d) - rho * span / 2)) as Hmy_yhi.
  fold ylo in Hylo_my. fold yhi in Hmy_yhi.
  destruct (Rle_dec h my) as [Hle | Hgt].
  - apply (twin_base_to_straddle_west r d rho ef my h Hasc Hhdef Hle).
    intros y [Hy1 Hy2].
    apply (Hclear ef (conj Hef Hefd0) y).
    split; lra.
  - assert (Hge : my <= h) by lra.
    apply (twin_base_to_straddle_west_down r d rho ef my h
             Hasc Hhdef Hge).
    intros y [Hy1 Hy2].
    apply (Hclear ef (conj Hef Hefd0) y).
    split; lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Axiom audit.  End ties below explicit caps; allowlist axioms only.          *)
(* -------------------------------------------------------------------------- *)

(* Used by: the E-2 headline (`walk_small_offset_connectivity_holds`) --
   the four caps join the folded corner/ride thresholds in the final
   Rmin, and the tie samples are exactly the orbit chain's start and
   terminal samples at the shared corner delta. *)

Print Assumptions walk_tie_west_desc.
Print Assumptions walk_tie_east_desc.
Print Assumptions walk_tie_east_asc.
Print Assumptions walk_tie_west_asc.

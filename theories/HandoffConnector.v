(* ==========================================================================
   HandoffConnector.v

   [H-bridge attack, C-3e step B] The HANDOFF CONNECTOR: a single certified
   chord from a corner sample to the adjacent corridor end at a dart vertex,
   composed from the pruned clearance ball (non-incident ring edges),
   the step-1 side kit (dart and twin), and the step-2 wedge sector
   certificates (the other incident ring edge).

   When `CornerCorridorBridge` identifies the corner sample with the
   corridor point at the bridge height, the handoff collapses to a
   zero-hop equality (`handoff_base_bridge_*` / `handoff_tip_bridge_*`);
   the convex-gap chord below is the general case.

   No `Admitted` / `Axiom` / `Parameter`; allowlist axioms only.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
   ========================================================================== *)

From Stdlib Require Import Reals Lra List.
From NTS.Proofs Require Import JordanRingKit.
From NTS.Proofs Require Import OverlayGraph Vec Azimuth Direction Dart
                               DartAngularOrder JCTHugStep RingClearance
                               SectorPath CornerSamples CornerConnector
                               JCTCorridor StraddleSides MirrorCorridor
                               DartSideKit HandoffWedge.
From NTS.Proofs Require Export CornerCorridorBridge.

Import ListNotations.
Local Open Scope R_scope.
(* -------------------------------------------------------------------------- *)
(* §C-3e-B  Handoff connector (pruned ball + side kit + wedge).                *)
(* -------------------------------------------------------------------------- *)

Lemma vy_nonzero_of_lt : forall v : Vec, vy v < 0 -> v <> vzero.
Proof.
  intros v Hlt Hzero. inversion Hzero. subst. cbn in Hlt. lra.
Qed.

Lemma vy_nonzero_of_gt : forall v : Vec, vy v > 0 -> v <> vzero.
Proof.
  intros v Hgt Hzero. inversion Hzero. subst. cbn in Hgt. lra.
Qed.

Lemma dart_descend_tip_below_base : forall d : Dart,
  vy (ddir d) < 0 -> py (dtip d) < py (dbase d).
Proof.
  intros [base tip] H.
  unfold ddir, point_diff, dtip, dbase, vy, fst, snd in H.
  cbn in H. unfold dtip, dbase. cbn. lra.
Qed.

Lemma dart_ascend_base_below_tip : forall d : Dart,
  vy (ddir d) > 0 -> py (dbase d) < py (dtip d).
Proof.
  intros [base tip] H.
  unfold ddir, point_diff, dtip, dbase, vy, fst, snd in H.
  cbn in H. unfold dtip, dbase. cbn. lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §1  Re-export the complement mechanism under dart-handoff naming.          *)
(* -------------------------------------------------------------------------- *)

Lemma handoff_offset_in_complement :
  forall (r : Ring) (v a b : Point) (eps : R) (w : Vec),
    (forall q : Point,
       Rabs (px q - px v) < eps -> Rabs (py q - py v) < eps ->
       forall f, In f (ring_edges r) -> f <> (a, v) -> f <> (v, b) ->
         ~ on_edge f q) ->
    in_open_sector (point_diff a v) (point_diff b v) w ->
    Rabs (vx w) < eps -> Rabs (vy w) < eps ->
    ring_complement r (point_at v w).
Proof.
  intros r v a b eps w Hball Hsect Hbx Hby.
  exact (corner_offset_in_complement r v a b eps w Hball Hsect Hbx Hby).
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  Convex-gap handoff: one sector-certified chord.                          *)
(* -------------------------------------------------------------------------- *)

Theorem handoff_chord_connected_convex :
  forall (r : Ring) (v a b : Point) (u1 u2 w1 w2 : Vec) (eps : R),
    u1 = point_diff a v ->
    u2 = point_diff b v ->
    In (a, v) (ring_edges r) ->
    In (v, b) (ring_edges r) ->
    (forall q : Point,
       Rabs (px q - px v) < eps -> Rabs (py q - py v) < eps ->
       forall f, In f (ring_edges r) -> f <> (a, v) -> f <> (v, b) ->
         ~ on_edge f q) ->
    0 < vcross u1 u2 ->
    0 < vcross u1 w1 -> 0 < vcross w1 u2 ->
    0 < vcross u1 w2 -> 0 < vcross w2 u2 ->
    Rabs (vx w1) < eps -> Rabs (vy w1) < eps ->
    Rabs (vx w2) < eps -> Rabs (vy w2) < eps ->
    connected_in_complement_cont r (point_at v w1) (point_at v w2).
Proof.
  intros r v a b u1 u2 w1 w2 eps Hu1 Hu2 Hin Hout Hball Hc H11 H12 H21 H22
         H1x H1y H2x H2y.
  apply hop_connected. intros t Ht.
  apply (handoff_offset_in_complement r v a b eps); [ exact Hball | | | ].
  - pose proof (sector_path_convex u1 u2 w1 w2 Hc H11 H12 H21 H22 t Ht)
      as Hsect.
    rewrite Hu1, Hu2 in Hsect. exact Hsect.
  - eapply Rle_lt_trans; [ apply vaffine_bound_x; exact Ht | ].
    apply Rmax_lub_lt; assumption.
  - eapply Rle_lt_trans; [ apply vaffine_bound_y; exact Ht | ].
    apply Rmax_lub_lt; assumption.
Qed.

(* DESCENDING dart, west corridor, BASE vertex: corner sample to corridor end
   at height `y` inside the y-span. *)
Theorem handoff_base_to_corridor_west_convex :
  forall (r : Ring) (d : Dart) (a : Point) (eps rho delta y : R),
    In (a, dbase d) (ring_edges r) ->
    In d (ring_edges r) ->
    (forall q : Point,
       Rabs (px q - px (dbase d)) < eps ->
       Rabs (py q - py (dbase d)) < eps ->
       forall f, In f (ring_edges r) -> f <> (a, dbase d) -> f <> d ->
         ~ on_edge f q) ->
    vy (ddir d) < 0 ->
    0 < vcross (point_diff a (dbase d)) (ddir d) ->
    0 < rho -> 0 < delta ->
    delta * Rabs (vcross (vperpL (point_diff a (dbase d))) (ddir d))
      < rho * vcross (point_diff a (dbase d)) (ddir d) ->
    delta * Rabs (vcross (point_diff a (dbase d)) (vperpL (ddir d)))
      < rho * vcross (point_diff a (dbase d)) (ddir d) ->
    rho * Rabs (vx (ddir d)) + delta * Rabs (vy (ddir d)) < eps ->
    rho * Rabs (vy (ddir d)) + delta * Rabs (vx (ddir d)) < eps ->
    Rabs (vx (point_diff (corridor d delta y) (dbase d))) < eps ->
    Rabs (vy (point_diff (corridor d delta y) (dbase d))) < eps ->
    0 < vcross (point_diff a (dbase d))
               (point_diff (corridor d delta y) (dbase d)) ->
    connected_in_complement_cont r
      (point_at (dbase d) (corner_sample_out (ddir d) rho delta))
      (corridor d delta y).
Proof.
  intros r d a eps rho delta y Hin Hout Hball Hdesc Hc Hr Hd Hsmall1 Hsmall2
         Hb_out_x Hb_out_y Hcor_x Hcor_y Hcor_far.
  set (u1 := point_diff a (dbase d)).
  set (u2 := ddir d).
  set (w1 := corner_sample_out u2 rho delta).
  set (w2 := point_diff (corridor d delta y) (dbase d)).
  assert (Hu2eq : u2 = point_diff (dtip d) (dbase d)) by (unfold u2; reflexivity).
  assert (Hu2nz : u2 <> vzero) by (unfold u2; exact (vy_nonzero_of_lt _ Hdesc)).
  assert (Hwest : py (dtip d) < py (dbase d))
    by (apply dart_descend_tip_below_base; exact Hdesc).
  assert (H11 : 0 < vcross u1 w1).
  { apply corner_sample_out_cert_far; [ | exact Hr | lra | ].
    - unfold u1, u2. exact Hc.
    - unfold u1, u2. exact Hsmall2. }
  assert (H12 : 0 < vcross w1 u2)
    by (apply corner_sample_out_cert; [ exact Hu2nz | exact Hd ]).
  assert (H22 : 0 < vcross w2 u2)
    by (apply corridor_end_cert_base_west; [ exact Hwest | exact Hd ]).
  pose proof (corner_sample_out_bound u2 rho delta ltac:(lra) ltac:(lra))
    as [HoutBx HoutBy].
  assert (Hdart : d = (dbase d, dtip d)).
  { destruct d as [base tip]. unfold dbase, dtip. cbn. reflexivity. }
  assert (Hout' : In (dbase d, dtip d) (ring_edges r))
    by (rewrite <- Hdart; exact Hout).
  assert (Hball' :
    forall q : Point,
      Rabs (px q - px (dbase d)) < eps ->
      Rabs (py q - py (dbase d)) < eps ->
      forall f, In f (ring_edges r) -> f <> (a, dbase d) ->
        f <> (dbase d, dtip d) -> ~ on_edge f q).
  { intros q Hqx Hqy f Hf Hne1 Hne2.
    apply (Hball q Hqx Hqy f Hf Hne1). intro Heq. apply Hne2.
    rewrite <- Hdart. exact Heq. }
  assert (Hw2 : point_at (dbase d) w2 = corridor d delta y)
    by (unfold w2; rewrite point_at_diff; reflexivity).
  rewrite <- Hw2.
  apply (handoff_chord_connected_convex r (dbase d) a (dtip d) u1 u2 w1 w2 eps);
    [ reflexivity | exact Hu2eq | exact Hin | exact Hout' | exact Hball' | exact Hc
    | exact H11 | exact H12 | exact Hcor_far | exact H22
    | eapply Rle_lt_trans; [ exact HoutBx | exact Hb_out_x ]
    | eapply Rle_lt_trans; [ exact HoutBy | exact Hb_out_y ]
    | exact Hcor_x | exact Hcor_y ].
Qed.

(* ASCENDING dart, east corridor, TIP vertex: arriving sample to corridor end. *)
Theorem handoff_tip_to_corridor_east_convex :
  forall (r : Ring) (d : Dart) (b : Point) (eps rho delta y : R),
    In d (ring_edges r) ->
    In (dtip d, b) (ring_edges r) ->
    (forall q : Point,
       Rabs (px q - px (dtip d)) < eps ->
       Rabs (py q - py (dtip d)) < eps ->
       forall f, In f (ring_edges r) -> f <> d -> f <> (dtip d, b) ->
         ~ on_edge f q) ->
    vy (ddir d) > 0 ->
    0 < vcross (ddir (twin d)) (point_diff b (dtip d)) ->
    0 < rho -> 0 < delta ->
    delta * Rabs (vcross (vperpL (ddir (twin d))) (point_diff b (dtip d)))
      < rho * vcross (ddir (twin d)) (point_diff b (dtip d)) ->
    delta * Rabs (vcross (ddir (twin d)) (vperpL (point_diff b (dtip d))))
      < rho * vcross (ddir (twin d)) (point_diff b (dtip d)) ->
    rho * Rabs (vx (ddir (twin d))) + delta * Rabs (vy (ddir (twin d))) < eps ->
    rho * Rabs (vy (ddir (twin d))) + delta * Rabs (vx (ddir (twin d))) < eps ->
    Rabs (vx (point_diff (corridor_east d delta y) (dtip d))) < eps ->
    Rabs (vy (point_diff (corridor_east d delta y) (dtip d))) < eps ->
    0 < vcross (ddir (twin d))
               (point_diff (corridor_east d delta y) (dtip d)) ->
    0 < vcross (point_diff (corridor_east d delta y) (dtip d))
               (point_diff b (dtip d)) ->
    connected_in_complement_cont r
      (point_at (dtip d) (corner_sample_in (ddir (twin d)) rho delta))
      (corridor_east d delta y).
Proof.
  intros r d b eps rho delta y Hin Hout Hball Hasc Hc Hr Hd Hsmall1 Hsmall2
         Hb_in_x Hb_in_y Hcor_x Hcor_y Hcor_far Hcor_wall2.
  set (u1 := ddir (twin d)).
  set (u2 := point_diff b (dtip d)).
  set (w1 := corner_sample_in u1 rho delta).
  set (w2 := point_diff (corridor_east d delta y) (dtip d)).
  assert (Hu1eq : u1 = point_diff (dbase d) (dtip d)).
  { destruct d as [base tip].
    unfold u1, point_diff, ddir, twin, dtip, dbase, vneg, vx, vy. cbn.
    reflexivity. }
  assert (Hu1neg : vy u1 < 0).
  { destruct d as [base tip]. unfold u1, ddir, twin, vneg, vy in *. cbn in *. lra. }
  assert (Hu1nz : u1 <> vzero) by (exact (vy_nonzero_of_lt _ Hu1neg)).
  assert (Hasc' : py (dbase d) < py (dtip d))
    by (apply dart_ascend_base_below_tip; exact Hasc).
  assert (H11 : 0 < vcross u1 w1)
    by (apply corner_sample_in_cert; [ exact Hu1nz | exact Hd ]).
  assert (H12 : 0 < vcross w1 u2).
  { apply corner_sample_in_cert_far; [ | exact Hr | lra | ].
    - unfold u1, u2. exact Hc.
    - unfold u1, u2. exact Hsmall1. }
  assert (H21 : 0 < vcross u1 w2) by (unfold u1, w2; exact Hcor_far).
  assert (H22 : 0 < vcross w2 u2) by (unfold u2, w2; exact Hcor_wall2).
  pose proof (corner_sample_in_bound u1 rho delta ltac:(lra) ltac:(lra))
    as [HinBx HinBy].
  assert (Hdart : d = (dbase d, dtip d)).
  { destruct d as [base tip]. unfold dbase, dtip. cbn. reflexivity. }
  assert (Hin' : In (dbase d, dtip d) (ring_edges r))
    by (rewrite <- Hdart; exact Hin).
  assert (Hball' :
    forall q : Point,
      Rabs (px q - px (dtip d)) < eps ->
      Rabs (py q - py (dtip d)) < eps ->
      forall f, In f (ring_edges r) -> f <> (dbase d, dtip d) ->
        f <> (dtip d, b) -> ~ on_edge f q).
  { intros q Hqx Hqy f Hf Hne1 Hne2.
    apply (Hball q Hqx Hqy f Hf).
    - intro Hfd. apply Hne1. rewrite <- Hdart. exact Hfd.
    - exact Hne2. }
  assert (Hw2 : point_at (dtip d) w2 = corridor_east d delta y)
    by (unfold w2; rewrite point_at_diff; reflexivity).
  rewrite <- Hw2.
  apply (handoff_chord_connected_convex r (dtip d) (dbase d) b u1 u2 w1 w2 eps);
    [ exact Hu1eq | reflexivity | exact Hin' | exact Hout | exact Hball' | exact Hc
    | exact H11 | exact H12 | exact H21 | exact H22
    | eapply Rle_lt_trans; [ exact HinBx | exact Hb_in_x ]
    | eapply Rle_lt_trans; [ exact HinBy | exact Hb_in_y ]
    | exact Hcor_x | exact Hcor_y ].
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Algebraic bypass: corner sample = corridor point (zero-hop handoff).    *)
(* -------------------------------------------------------------------------- *)

Lemma handoff_base_bridge_west :
  forall (d : Dart) (rho delta : R),
    vy (ddir d) < 0 ->
    point_at (dbase d) (corner_sample_out (ddir d) rho delta)
      = corridor d
          (delta * (vx (ddir d) * vx (ddir d) + vy (ddir d) * vy (ddir d))
             / (- vy (ddir d)))
          (py (dbase d) + (rho * vy (ddir d) - delta * vx (ddir d))).
Proof.
  intros d rho delta Hdesc.
  exact (corner_sample_out_on_corridor_west d rho delta Hdesc).
Qed.

Lemma handoff_tip_bridge_west :
  forall (d : Dart) (rho delta : R),
    vy (ddir d) < 0 ->
    point_at (dtip d)
      (corner_sample_in (point_diff (dbase d) (dtip d)) rho delta)
      = corridor d
          (delta * (vx (ddir d) * vx (ddir d) + vy (ddir d) * vy (ddir d))
             / (- vy (ddir d)))
          (py (dtip d) + (- rho * vy (ddir d) - delta * vx (ddir d))).
Proof.
  intros d rho delta Hdesc.
  exact (corner_sample_in_on_corridor_west d rho delta Hdesc).
Qed.

Lemma handoff_base_bridge_east :
  forall (d : Dart) (rho delta : R),
    vy (ddir d) > 0 ->
    point_at (dbase d) (corner_sample_out (ddir d) rho delta)
      = corridor_east d
          (delta * (vx (ddir d) * vx (ddir d) + vy (ddir d) * vy (ddir d))
             / vy (ddir d))
          (py (dbase d) + (rho * vy (ddir d) - delta * vx (ddir d))).
Proof.
  intros d rho delta Hasc.
  exact (corner_sample_out_on_corridor_east d rho delta Hasc).
Qed.

Lemma handoff_tip_bridge_east :
  forall (d : Dart) (rho delta : R),
    vy (ddir d) > 0 ->
    point_at (dtip d)
      (corner_sample_in (point_diff (dbase d) (dtip d)) rho delta)
      = corridor_east d
          (delta * (vx (ddir d) * vx (ddir d) + vy (ddir d) * vy (ddir d))
             / vy (ddir d))
          (py (dtip d) + (- rho * vy (ddir d) - delta * vx (ddir d))).
Proof.
  intros d rho delta Hasc.
  exact (corner_sample_in_on_corridor_east d rho delta Hasc).
Qed.

Theorem handoff_base_bridge_connected_west :
  forall (r : Ring) (d : Dart) (rho delta : R),
    vy (ddir d) < 0 ->
    ring_complement r
      (corridor d
         (delta * (vx (ddir d) * vx (ddir d) + vy (ddir d) * vy (ddir d))
            / (- vy (ddir d)))
         (py (dbase d) + (rho * vy (ddir d) - delta * vx (ddir d)))) ->
    connected_in_complement_cont r
      (point_at (dbase d) (corner_sample_out (ddir d) rho delta))
      (corridor d
         (delta * (vx (ddir d) * vx (ddir d) + vy (ddir d) * vy (ddir d))
            / (- vy (ddir d)))
         (py (dbase d) + (rho * vy (ddir d) - delta * vx (ddir d)))).
Proof.
  intros r d rho delta Hdesc Hcomp.
  pose proof (handoff_base_bridge_west d rho delta Hdesc) as Heq.
  rewrite Heq.
  apply connected_in_complement_cont_refl. exact Hcomp.
Qed.

(* -------------------------------------------------------------------------- *)
(* Axiom audit.                                                                *)
(* -------------------------------------------------------------------------- *)

Print Assumptions handoff_chord_connected_convex.
Print Assumptions handoff_base_to_corridor_west_convex.
Print Assumptions handoff_base_bridge_connected_west.

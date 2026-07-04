(* ==========================================================================
   WalkRides.v

   [H-bridge attack, C-3f discharge rung D-1] The SAMPLE-TO-SAMPLE
   RIDES: the along-dart legs the orbit chain consumes (`walk_chain_
   connected`'s ride family), packaged at a PRESCRIBED corner delta --
   base sample of `x` to tip sample of `x`, one corridor ride, on the
   face side given by `x`'s orientation.

   Nothing here is new geometry: the two `CornerCorridorBridge`
   equalities (`handoff_base_bridge_*`, `handoff_tip_bridge_*`) rewrite
   both samples into points of `x`'s own corridor at ONE common offset,
   and `corridor_connected` / `corridor_connected_east` carry the
   segment.  The window hypotheses are exactly what the C-3c clearance
   theorems produce; the IN-SPAN lemmas below put the two bridge
   heights strictly inside the dart's y-span (the window shape those
   theorems demand) under the explicit smallness
   `|delta * vx| < rho_i * |vy|`, ordered when `rho1 + rho2 < 1`.

   No `Admitted` / `Axiom` / `Parameter`; allowlist axioms only.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
   ========================================================================== *)

From Stdlib Require Import Reals Lra List.
From NTS.Proofs Require Import Distance Overlay OverlayGraph Vec Azimuth
                               Direction Dart DartAngularOrder
                               PointInRingTangents JordanCurveSeam JCT
                               JCTHugStep RingClearance SectorPath
                               CornerSamples CornerConnector JCTCorridor
                               JCTMinOpenStep WalkCorridor MirrorCorridor
                               DartSideKit CornerCorridorBridge.

Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  The two rides.                                                          *)
(* -------------------------------------------------------------------------- *)

Theorem along_dart_ride_west :
  forall (r : Ring) (d : Dart) (rho1 rho2 delta : R),
    vy (ddir d) < 0 ->
    py (dtip d) + (- rho2 * vy (ddir d) - delta * vx (ddir d))
      <= py (dbase d) + (rho1 * vy (ddir d) - delta * vx (ddir d)) ->
    (forall y,
       py (dtip d) + (- rho2 * vy (ddir d) - delta * vx (ddir d)) <= y <=
       py (dbase d) + (rho1 * vy (ddir d) - delta * vx (ddir d)) ->
       ~ ring_image r
           (corridor d
              (delta * (vx (ddir d) * vx (ddir d) + vy (ddir d) * vy (ddir d))
                 / (- vy (ddir d))) y)) ->
    connected_in_complement_cont r
      (point_at (dbase d) (corner_sample_out (ddir d) rho1 delta))
      (point_at (dtip d)
         (corner_sample_in (point_diff (dbase d) (dtip d)) rho2 delta)).
Proof.
  intros r d rho1 rho2 delta Hdesc Hord Hfree.
  assert (Hnh : py (fst d) <> py (snd d)).
  { intro Heq.
    assert (Hvy : vy (ddir d) = py (snd d) - py (fst d))
      by (destruct d as [a b]; reflexivity).
    lra. }
  rewrite (handoff_base_bridge_west d rho1 delta Hdesc).
  rewrite (handoff_tip_bridge_west d rho2 delta Hdesc).
  apply corridor_connected; [ exact Hnh | exact Hord | exact Hfree ].
Qed.

Theorem along_dart_ride_east :
  forall (r : Ring) (d : Dart) (rho1 rho2 delta : R),
    0 < vy (ddir d) ->
    py (dbase d) + (rho1 * vy (ddir d) - delta * vx (ddir d))
      <= py (dtip d) + (- rho2 * vy (ddir d) - delta * vx (ddir d)) ->
    (forall y,
       py (dbase d) + (rho1 * vy (ddir d) - delta * vx (ddir d)) <= y <=
       py (dtip d) + (- rho2 * vy (ddir d) - delta * vx (ddir d)) ->
       ~ ring_image r
           (corridor_east d
              (delta * (vx (ddir d) * vx (ddir d) + vy (ddir d) * vy (ddir d))
                 / vy (ddir d)) y)) ->
    connected_in_complement_cont r
      (point_at (dbase d) (corner_sample_out (ddir d) rho1 delta))
      (point_at (dtip d)
         (corner_sample_in (point_diff (dbase d) (dtip d)) rho2 delta)).
Proof.
  intros r d rho1 rho2 delta Hasc Hord Hfree.
  assert (Hnh : py (fst d) <> py (snd d)).
  { intro Heq.
    assert (Hvy : vy (ddir d) = py (snd d) - py (fst d))
      by (destruct d as [a b]; reflexivity).
    lra. }
  assert (Hasc' : vy (ddir d) > 0) by lra.
  rewrite (handoff_base_bridge_east d rho1 delta Hasc').
  rewrite (handoff_tip_bridge_east d rho2 delta Hasc').
  apply connected_in_complement_cont_sym.
  unfold corridor_east.
  apply corridor_connected_east; [ exact Hnh | exact Hord | ].
  intros y Hy.
  pose proof (Hfree y Hy) as H.
  unfold corridor_east in H.
  exact H.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  The bridge heights sit strictly inside the dart's y-span.               *)
(* -------------------------------------------------------------------------- *)

Lemma ride_heights_in_span_west :
  forall (d : Dart) (rho1 rho2 delta : R),
    vy (ddir d) < 0 -> 0 < rho1 -> 0 < rho2 -> rho1 + rho2 < 1 ->
    Rabs (delta * vx (ddir d)) < rho1 * (- vy (ddir d)) ->
    Rabs (delta * vx (ddir d)) < rho2 * (- vy (ddir d)) ->
    py (dtip d)
      < py (dtip d) + (- rho2 * vy (ddir d) - delta * vx (ddir d)) /\
    py (dtip d) + (- rho2 * vy (ddir d) - delta * vx (ddir d))
      <= py (dbase d) + (rho1 * vy (ddir d) - delta * vx (ddir d)) /\
    py (dbase d) + (rho1 * vy (ddir d) - delta * vx (ddir d))
      < py (dbase d).
Proof.
  intros d rho1 rho2 delta Hdesc Hr1 Hr2 Hsum Hs1 Hs2.
  apply Rabs_def2 in Hs1. apply Rabs_def2 in Hs2.
  assert (Hvy : vy (ddir d) = py (dtip d) - py (dbase d))
    by (destruct d as [a b]; reflexivity).
  split; [ nra | split; nra ].
Qed.

Lemma ride_heights_in_span_east :
  forall (d : Dart) (rho1 rho2 delta : R),
    0 < vy (ddir d) -> 0 < rho1 -> 0 < rho2 -> rho1 + rho2 < 1 ->
    Rabs (delta * vx (ddir d)) < rho1 * vy (ddir d) ->
    Rabs (delta * vx (ddir d)) < rho2 * vy (ddir d) ->
    py (dbase d)
      < py (dbase d) + (rho1 * vy (ddir d) - delta * vx (ddir d)) /\
    py (dbase d) + (rho1 * vy (ddir d) - delta * vx (ddir d))
      <= py (dtip d) + (- rho2 * vy (ddir d) - delta * vx (ddir d)) /\
    py (dtip d) + (- rho2 * vy (ddir d) - delta * vx (ddir d))
      < py (dtip d).
Proof.
  intros d rho1 rho2 delta Hasc Hr1 Hr2 Hsum Hs1 Hs2.
  apply Rabs_def2 in Hs1. apply Rabs_def2 in Hs2.
  assert (Hvy : vy (ddir d) = py (dtip d) - py (dbase d))
    by (destruct d as [a b]; reflexivity).
  split; [ nra | split; nra ].
Qed.

(* -------------------------------------------------------------------------- *)
(* Axiom audit.  Assembly of banked pieces; allowlist axioms only.             *)
(* -------------------------------------------------------------------------- *)

Print Assumptions along_dart_ride_west.
Print Assumptions along_dart_ride_east.
Print Assumptions ride_heights_in_span_west.

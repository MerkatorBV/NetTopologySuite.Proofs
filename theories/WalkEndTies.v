(* ==========================================================================
   WalkEndTies.v

   [H-bridge attack, C-3f step 1(iii)] The END TIES of the orbit chain:
   the chain's two terminal samples (`walk_chain_to_twin`: d's base
   sample and TWIN d's base sample at `dtip d`) reach the premise's
   straddle pair `(edge_x_at d my -/+ ef, my)` -- one corridor ride
   each, on the two SIDES of d's carrier.

   The load-bearing observation is a delta CONSISTENCY identity: the
   corner delta that makes twin d's ride hit corridor offset `ef` on
   ITS side equals the one for d --

     `corner_delta_for_ef_east (twin d) ef = corner_delta_for_ef_west d ef`

   (the twin negates both `vy` and the side convention, and the squared
   norm is twin-invariant), and mirrored for ascending d.  So ONE
   shared delta serves the whole chain INCLUDING both end ties, exactly
   the discipline `walk_chain_connected` carries.

   Contents (descending d; the ascending mirror swaps which end gets
   which straddle sign):
     - `corner_delta_for_ef_twin_east`/`_twin_west`: the consistency
       identities;
     - `corridor_east_twin`: twin d's east corridor is pointwise d's
       (same carrier line, `edge_x_at_twin`), so clearance hypotheses
       are stated on d's own corridors throughout;
     - `twin_base_to_straddle_east` (descending d): twin d's base
       sample at `dtip d` rides twin d's east corridor -- which IS d's
       east corridor -- down to `(edge_x_at d my + ef, my)`;
     - `twin_base_to_straddle_west` (ascending d): the mirror.
   The west/east ties on d ITSELF are `CornerCorridorBridge.along_dart_
   base_to_straddle_west`/`_east` verbatim -- no wrapper needed.

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
                               JCTCorridor WalkCorridor MirrorCorridor
                               DartSideKit CornerCorridorBridge
                               HandoffConnector C3eEfCorridorAssumption
                               BaseToTipHeadline.

Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  Delta consistency across the twin.                                      *)
(* -------------------------------------------------------------------------- *)

Lemma vy_vneg : forall u : Vec, vy (vneg u) = - vy u.
Proof. intros [ux uy]. reflexivity. Qed.

Lemma corner_delta_for_ef_twin_east :
  forall (d : Dart) (ef : R),
    corner_delta_for_ef_east (twin d) ef = corner_delta_for_ef_west d ef.
Proof.
  intros d ef.
  unfold corner_delta_for_ef_east, corner_delta_for_ef_west.
  rewrite ddir_twin.
  destruct (ddir d) as [ux uy]. unfold vneg. cbn [vx vy].
  replace (- ux * - ux + - uy * - uy) with (ux * ux + uy * uy) by ring.
  reflexivity.
Qed.

Lemma corner_delta_for_ef_twin_west :
  forall (d : Dart) (ef : R),
    corner_delta_for_ef_west (twin d) ef = corner_delta_for_ef_east d ef.
Proof.
  intros d ef.
  unfold corner_delta_for_ef_east, corner_delta_for_ef_west.
  rewrite ddir_twin.
  destruct (ddir d) as [ux uy]. unfold vneg. cbn [vx vy].
  replace (- ux * - ux + - uy * - uy) with (ux * ux + uy * uy) by ring.
  replace (- - uy) with uy by ring.
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  Twin corridors are pointwise the original's (same carrier line).        *)
(* -------------------------------------------------------------------------- *)

Lemma corridor_east_twin :
  forall (e : Edge) (delta y : R),
    py (fst e) <> py (snd e) ->
    corridor_east (twin e) delta y = corridor_east e delta y.
Proof.
  intros e delta y Hnh.
  unfold corridor_east. rewrite (edge_x_at_twin e y Hnh). reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  The twin-side end ties.                                                 *)
(* -------------------------------------------------------------------------- *)

(* DESCENDING d: the chain's terminal sample (twin d's base sample at
   dtip d, on the face side = d's EAST) rides down to the +ef straddle
   point.  The clearance hypothesis is on d's OWN east corridor. *)
Theorem twin_base_to_straddle_east :
  forall (r : Ring) (d : Dart) (rho ef my h_base : R),
    vy (ddir d) < 0 ->
    h_base = bridge_height_base (twin d) rho (corner_delta_for_ef_west d ef) ->
    h_base <= my ->
    (forall y, h_base <= y <= my ->
       ~ ring_image r (corridor_east d ef y)) ->
    connected_in_complement_cont r
      (point_at (dtip d)
         (corner_sample_out (ddir (twin d))
            rho (corner_delta_for_ef_west d ef)))
      (mkPoint (edge_x_at d my + ef) my).
Proof.
  intros r d rho ef my h_base Hdesc Hhbase Hle Hclear.
  assert (Hnh : py (fst d) <> py (snd d)).
  { intro Heq.
    assert (Hvy : vy (ddir d) = py (snd d) - py (fst d))
      by (destruct d as [a b]; reflexivity).
    lra. }
  assert (Hasc : vy (ddir (twin d)) > 0)
    by (rewrite ddir_twin, vy_vneg; lra).
  pose proof (along_dart_base_to_straddle_east r (twin d) rho ef my h_base
                Hasc) as Htie.
  rewrite corner_delta_for_ef_twin_east in Htie.
  rewrite (edge_x_at_twin d my Hnh) in Htie.
  rewrite dbase_twin in Htie.
  apply Htie; [ exact Hhbase | exact Hle | ].
  intros y Hy.
  rewrite (corridor_east_twin d ef y Hnh).
  exact (Hclear y Hy).
Qed.

(* ASCENDING d: the mirror -- twin d's base sample rides twin d's WEST
   corridor (= d's west corridor) down to the -ef straddle point. *)
Theorem twin_base_to_straddle_west :
  forall (r : Ring) (d : Dart) (rho ef my h_base : R),
    0 < vy (ddir d) ->
    h_base = bridge_height_base (twin d) rho (corner_delta_for_ef_east d ef) ->
    h_base <= my ->
    (forall y, h_base <= y <= my ->
       ~ ring_image r (corridor d ef y)) ->
    connected_in_complement_cont r
      (point_at (dtip d)
         (corner_sample_out (ddir (twin d))
            rho (corner_delta_for_ef_east d ef)))
      (mkPoint (edge_x_at d my - ef) my).
Proof.
  intros r d rho ef my h_base Hasc Hhbase Hle Hclear.
  assert (Hnh : py (fst d) <> py (snd d)).
  { intro Heq.
    assert (Hvy : vy (ddir d) = py (snd d) - py (fst d))
      by (destruct d as [a b]; reflexivity).
    lra. }
  assert (Hdesc : vy (ddir (twin d)) < 0)
    by (rewrite ddir_twin, vy_vneg; lra).
  pose proof (along_dart_base_to_straddle_west r (twin d) rho ef my h_base
                Hdesc) as Htie.
  rewrite corner_delta_for_ef_twin_west in Htie.
  rewrite (edge_x_at_twin d my Hnh) in Htie.
  rewrite dbase_twin in Htie.
  apply Htie; [ exact Hhbase | exact Hle | ].
  intros y Hy.
  rewrite (corridor_twin d ef y Hnh).
  exact (Hclear y Hy).
Qed.

(* -------------------------------------------------------------------------- *)
(* Axiom audit.  Pure algebra + banked rides; allowlist axioms only.           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions corner_delta_for_ef_twin_east.
Print Assumptions twin_base_to_straddle_east.
Print Assumptions twin_base_to_straddle_west.

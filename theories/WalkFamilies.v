(* ==========================================================================
   WalkFamilies.v

   [H-bridge attack, C-3f discharge rung D-4b-1] THE WALK-VERTEX
   TRICHOTOMY RESOLUTION: at any walk vertex (the tip of any E-dart),
   membership in the cycle ring's vertex trace is decidable, and each
   branch yields the D-4a corner-threshold inputs --

     - a TRACE vertex has an incident chain-edge pair
       (`trace_vertex_incident_pair`: tips of the chain ARE the trace,
       bases its rotation, so both directions of `in_map_iff` apply);
     - an OFF-TRACE walk vertex is in the ring COMPLEMENT
       (`off_trace_vertex_complement`): an endpoint hit would place it
       in the trace (tips) or its rotation (bases); an interior hit
       violates the E-level `no_foreign_vertex_twin_aware` guard, with
       the `x = f` / `x = twin f` escapes closed by the same trace
       membership.

   With D-4a's `on_ring_corner_threshold` / `off_ring_corner_threshold`
   these resolve every corner of the orbit chain; the remaining D-4b
   work is the ride/tie window plumbing and the headline assembly.

   No `Admitted` / `Axiom` / `Parameter`; allowlist axioms only.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
   ========================================================================== *)

From Stdlib Require Import Reals Lra List Permutation.
From NTS.Proofs Require Import JordanRingKit.
From NTS.Proofs Require Import OverlayGraph Vec Azimuth Direction Dart
                               DartAngularOrder JCTHugStep RingClearance
                               SectorPath CornerSamples CornerConnector
                               FanGapSector FanCorner WalkCorners DartPath
                               RingExtract CycleRing GeneralTautBridge
                               EdgeConnectivity ArrangementEMinus
                               HBridgeCoreSlice WalkVertexPack JCTCorridor
                               JCTMinOpenStep WalkCorridor MirrorCorridor
                               DartSideKit CornerCorridorBridge
                               HandoffConnector C3eEfCorridorAssumption
                               BaseToTipHeadline WalkEndTies.

Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  A trace vertex has an incident chain-edge pair.                         *)
(* -------------------------------------------------------------------------- *)

Lemma trace_vertex_incident_pair :
  forall (D : list Dart) (d : Dart) (c : list Dart) (v : Point),
    dpath D (dtip d) (dbase d) c ->
    In v (dtip d :: map dtip c) ->
    exists e_in e_out : Dart,
      In e_in (d :: c) /\ In e_out (d :: c) /\
      dtip e_in = v /\ dbase e_out = v.
Proof.
  intros D d c v Hp Hv.
  assert (Hv' : In v (map dtip (d :: c))) by (cbn [map]; exact Hv).
  apply in_map_iff in Hv'.
  destruct Hv' as [e_in [Htip Hin]].
  pose proof (dpath_base_trace D (dtip d) (dbase d) c Hp) as Htr.
  assert (Hvb : In v (map dbase (d :: c))).
  { cbn [map].
    apply Permutation_in with (l := map dbase c ++ [dbase d]).
    - apply Permutation_sym.
      apply (Permutation_cons_append (map dbase c) (dbase d)).
    - rewrite Htr. exact Hv. }
  apply in_map_iff in Hvb.
  destruct Hvb as [e_out [Hbase Hout]].
  exists e_in, e_out.
  split; [ exact Hin | split; [ exact Hout | ] ].
  split; [ exact Htip | exact Hbase ].
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  An off-trace walk vertex is in the ring complement.                     *)
(* -------------------------------------------------------------------------- *)

Lemma off_trace_vertex_complement :
  forall (E : list Edge) (d : Dart) (c : list Dart) (x : Dart),
    no_foreign_vertex_twin_aware (darts_of E) ->
    dpath (darts_of (E_minus E d)) (dtip d) (dbase d) c ->
    ring_edges (ring_of_chain (d :: c)) = d :: c ->
    (forall f, In f (d :: c) -> In f (darts_of E)) ->
    In x (darts_of E) ->
    ~ In (dtip x) (dtip d :: map dtip c) ->
    ring_complement (ring_of_chain (d :: c)) (dtip x).
Proof.
  intros E d c x Hnfv Hp Hedges HWD Hx Hnv [f [s [Hf [Hs [Hpx Hpy]]]]].
  rewrite Hedges in Hf.
  assert (Htipin : In (dtip f) (dtip d :: map dtip c)).
  { change (In (dtip f) (map dtip (d :: c))). apply in_map. exact Hf. }
  assert (Hbasein : In (dbase f) (dtip d :: map dtip c)).
  { pose proof (dpath_base_trace _ _ _ _ Hp) as Htr.
    rewrite <- Htr.
    apply Permutation_in with (l := dbase d :: map dbase c).
    - apply (Permutation_cons_append (map dbase c) (dbase d)).
    - change (In (dbase f) (map dbase (d :: c))). apply in_map. exact Hf. }
  destruct (Rle_lt_or_eq_dec 0 s (proj1 Hs)) as [Hs0 | Hs0].
  - destruct (Rle_lt_or_eq_dec s 1 (proj2 Hs)) as [Hs1 | Hs1].
    + (* interior hit: the twin-aware foreign-vertex guard *)
      assert (Hxf : f <> x)
        by (intro He; apply Hnv; rewrite <- He; exact Htipin).
      assert (Hftx : f <> twin x).
      { intro He. apply Hnv.
        assert (Hdt : dtip x = dbase f)
          by (rewrite He, dbase_twin; reflexivity).
        rewrite Hdt. exact Hbasein. }
      destruct (Hnfv f x (HWD f Hf) Hx Hxf Hftx) as [_ Hsnd].
      apply Hsnd. exists s. split; [ lra | ].
      unfold dtip in Hpx, Hpy.
      split; [ exact Hpx | exact Hpy ].
    + (* s = 1: the vertex IS f's tip, a trace vertex *)
      subst s. apply Hnv.
      assert (Hdt : dtip x = dtip f).
      { apply point_eq_of_coords.
        - rewrite Hpx. unfold dtip. ring.
        - rewrite Hpy. unfold dtip. ring. }
      rewrite Hdt. exact Htipin.
  - (* s = 0: the vertex IS f's base, in the trace's rotation *)
    subst s. apply Hnv.
    assert (Hdt : dtip x = dbase f).
    { apply point_eq_of_coords.
      - rewrite Hpx. unfold dbase. ring.
      - rewrite Hpy. unfold dbase. ring. }
    rewrite Hdt. exact Hbasein.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  DOWN-riding tie variants.  [D-4b-2]                                     *)
(*                                                                             *)
(* The banked ties ride UP (`h <= my`); the chain's corner-capped sample       *)
(* rhos hug the dart endpoints, so when `my` sits below the sample the         *)
(* mirror window `[my, h]` is needed -- same bridge equality, the              *)
(* corridor connector applied in its native orientation (no `sym`).            *)
(* -------------------------------------------------------------------------- *)

Theorem along_dart_base_to_straddle_west_down :
  forall (r : Ring) (d : Dart) (rho ef my h_base : R),
    vy (ddir d) < 0 ->
    h_base = bridge_height_base d rho (corner_delta_for_ef_west d ef) ->
    my <= h_base ->
    (forall y, my <= y <= h_base ->
       ~ ring_image r (corridor d ef y)) ->
    connected_in_complement_cont r
      (point_at (dbase d)
         (corner_sample_out (ddir d) rho (corner_delta_for_ef_west d ef)))
      (mkPoint (edge_x_at d my - ef) my).
Proof.
  intros r d rho ef my h_base Hdesc Hhbase Hle Hclear.
  set (delta_c := corner_delta_for_ef_west d ef).
  assert (Hbase_eq :
    point_at (dbase d) (corner_sample_out (ddir d) rho delta_c)
      = corridor d ef h_base).
  { rewrite (handoff_base_bridge_west d rho delta_c Hdesc).
    change (delta_c * (vx (ddir d) * vx (ddir d) + vy (ddir d) * vy (ddir d))
              / (- vy (ddir d))) with (bridge_delta_west d delta_c).
    change (py (dbase d) + (rho * vy (ddir d) - delta_c * vx (ddir d)))
      with (bridge_height_base d rho delta_c).
    assert (Hbd : bridge_delta_west d delta_c = ef)
      by (unfold delta_c; exact (bridge_delta_west_for_ef d ef Hdesc)).
    assert (Hbh : bridge_height_base d rho delta_c = h_base)
      by (unfold delta_c; symmetry; exact Hhbase).
    rewrite Hbd, Hbh. reflexivity. }
  assert (Hnh : py (dbase d) <> py (dtip d)).
  { intro Heq. pose proof (dart_descend_tip_below_base d Hdesc) as Hw.
    rewrite Heq in Hw. lra. }
  rewrite Hbase_eq, <- straddle_west_eq_corridor.
  exact (corridor_connected r d my h_base ef Hnh Hle Hclear).
Qed.

Theorem along_dart_base_to_straddle_east_down :
  forall (r : Ring) (d : Dart) (rho ef my h_base : R),
    vy (ddir d) > 0 ->
    h_base = bridge_height_base d rho (corner_delta_for_ef_east d ef) ->
    my <= h_base ->
    (forall y, my <= y <= h_base ->
       ~ ring_image r (corridor_east d ef y)) ->
    connected_in_complement_cont r
      (point_at (dbase d)
         (corner_sample_out (ddir d) rho (corner_delta_for_ef_east d ef)))
      (mkPoint (edge_x_at d my + ef) my).
Proof.
  intros r d rho ef my h_base Hasc Hhbase Hle Hclear.
  set (delta_c := corner_delta_for_ef_east d ef).
  assert (Hbase_eq :
    point_at (dbase d) (corner_sample_out (ddir d) rho delta_c)
      = corridor_east d ef h_base).
  { rewrite (handoff_base_bridge_east d rho delta_c Hasc).
    change (delta_c * (vx (ddir d) * vx (ddir d) + vy (ddir d) * vy (ddir d))
              / vy (ddir d)) with (bridge_delta_east d delta_c).
    change (py (dbase d) + (rho * vy (ddir d) - delta_c * vx (ddir d)))
      with (bridge_height_base d rho delta_c).
    assert (Hbd : bridge_delta_east d delta_c = ef)
      by (unfold delta_c; exact (bridge_delta_east_for_ef d ef Hasc)).
    assert (Hbh : bridge_height_base d rho delta_c = h_base)
      by (unfold delta_c; symmetry; exact Hhbase).
    rewrite Hbd, Hbh. reflexivity. }
  assert (Hnh : py (dbase d) <> py (dtip d)).
  { intro Heq. pose proof (dart_ascend_base_below_tip d Hasc) as Hw.
    rewrite Heq in Hw. lra. }
  rewrite Hbase_eq, <- straddle_east_eq_corridor_east.
  assert (Hride := corridor_connected_east r d my h_base ef Hnh Hle).
  unfold corridor_east.
  apply Hride.
  intros y Hy.
  pose proof (Hclear y Hy) as H.
  unfold corridor_east in H.
  exact H.
Qed.

(* The twin-side mirrors: the chain's terminal sample rides DOWN to a
   straddle point below it. *)
Theorem twin_base_to_straddle_east_down :
  forall (r : Ring) (d : Dart) (rho ef my h_base : R),
    vy (ddir d) < 0 ->
    h_base = bridge_height_base (twin d) rho (corner_delta_for_ef_west d ef) ->
    my <= h_base ->
    (forall y, my <= y <= h_base ->
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
  pose proof (along_dart_base_to_straddle_east_down r (twin d) rho ef my
                h_base Hasc) as Htie.
  rewrite corner_delta_for_ef_twin_east in Htie.
  rewrite (edge_x_at_twin d my Hnh) in Htie.
  rewrite dbase_twin in Htie.
  apply Htie; [ exact Hhbase | exact Hle | ].
  intros y Hy.
  rewrite (corridor_east_twin d ef y Hnh).
  exact (Hclear y Hy).
Qed.

Theorem twin_base_to_straddle_west_down :
  forall (r : Ring) (d : Dart) (rho ef my h_base : R),
    0 < vy (ddir d) ->
    h_base = bridge_height_base (twin d) rho (corner_delta_for_ef_east d ef) ->
    my <= h_base ->
    (forall y, my <= y <= h_base ->
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
  pose proof (along_dart_base_to_straddle_west_down r (twin d) rho ef my
                h_base Hdesc) as Htie.
  rewrite corner_delta_for_ef_twin_west in Htie.
  rewrite (edge_x_at_twin d my Hnh) in Htie.
  rewrite dbase_twin in Htie.
  apply Htie; [ exact Hhbase | exact Hle | ].
  intros y Hy.
  rewrite (corridor_twin d ef y Hnh).
  exact (Hclear y Hy).
Qed.

(* -------------------------------------------------------------------------- *)
(* Axiom audit.  Trace combinatorics + tie mirrors; allowlist only.            *)
(* -------------------------------------------------------------------------- *)

Print Assumptions trace_vertex_incident_pair.
Print Assumptions off_trace_vertex_complement.
Print Assumptions along_dart_base_to_straddle_west_down.
Print Assumptions twin_base_to_straddle_west_down.

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
From NTS.Proofs Require Import Distance Overlay OverlayGraph Vec Azimuth
                               Direction Dart DartAngularOrder
                               PointInRingTangents JordanCurveSeam JCT
                               JCTHugStep RingClearance SectorPath
                               CornerSamples CornerConnector FanGapSector
                               FanCorner WalkCorners DartPath RingExtract
                               CycleRing GeneralTautBridge EdgeConnectivity
                               ArrangementEMinus HBridgeCoreSlice
                               WalkVertexPack.

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
(* Axiom audit.  Trace combinatorics + guard transfer; allowlist only.         *)
(* -------------------------------------------------------------------------- *)

Print Assumptions trace_vertex_incident_pair.
Print Assumptions off_trace_vertex_complement.

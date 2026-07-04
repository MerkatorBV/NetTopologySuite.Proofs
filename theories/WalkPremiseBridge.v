(* ==========================================================================
   WalkPremiseBridge.v

   [H-bridge attack, C-3f discharge, D-4b conditional close] THE NAMED
   RESIDUAL AND THE BRIDGE: `face_transport_premise` follows outright
   from ONE named connectivity residual, `walk_small_offset_
   connectivity` -- under the premise's own hypothesis set, SOME
   sub-offset `ef' <= ef` has its straddle pair connected in the ring
   complement.

   This is the RGR risk/cost pivot of the discharge campaign: every
   GEOMETRIC ingredient of the residual is already Qed-banked --
     - the rides (`WalkRides.along_dart_ride_*` + in-span windows),
     - the corners (`WalkCorners.walk_corner_threshold` +
       `nat_threshold_fold`, dispatched per vertex by
       `WalkVertexPack.on/off_ring_corner_threshold` +
       `WalkFamilies.trace_vertex_incident_pair` /
       `off_trace_vertex_complement`),
     - the ties (`WalkEndTies` up-riders + `WalkFamilies` down-riders),
     - the chain (`WalkChainInduction.walk_chain_to_twin` over
       `WalkStepChain.walk_step_connected`), and
     - the frame (`WalkAssembly.walk_straddle_connected_desc`/`_asc`)
   -- so the residual is pure per-step WIRING (choose the walk index,
   the shared delta below the folded thresholds, and the per-step
   rho's), carried in the corpus's named-premise discipline exactly as
   `face_transport_premise` itself was.

   The bridge is small and closes the parity: the #343 strip hypothesis
   lifts the sub-offset connectivity to the premise's `ef`
   (`WalkStripLift.strip_lift_connected`), `RingExtract.face_walk_
   closed` gives `ring_closed`, and `WalkAssembly.walk_straddle_parity`
   lands exactly the premise's biconditional.

   No `Admitted` / `Axiom` / `Parameter`; allowlist axioms only.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
   ========================================================================== *)

From Stdlib Require Import Reals Lra List Arith Lia.
From NTS.Proofs Require Import Distance Overlay OverlayGraph Vec Azimuth
                               Dart DartAngularOrder DartFace
                               PointInRingTangents PointInRingCorrect
                               JordanCurveSeam JCT JCTHugStep RingClearance
                               JCTCorridor EdgeConnectivity
                               ArrangementEMinus DartPath RingExtract
                               CycleRing EdgeFaceBridge FaceOrbitSep
                               HBridgeCoreSlice WalkStripLift WalkAssembly.

Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  The named residual.                                                     *)
(* -------------------------------------------------------------------------- *)

(* Under `face_transport_premise`'s own hypothesis set, SOME sub-offset
   of the requested one has its straddle pair connected in the cycle
   ring's complement.  This is what the orbit chain produces at its
   small-offset regime; its discharge from the banked D-1..D-4a pieces
   is the remaining per-step wiring (plan.md, D-4b-2/3). *)
Definition walk_small_offset_connectivity (E : list Edge) : Prop :=
  forall (d : Dart) (c : list Dart) (my ef : R),
    In d E -> ~ In (twin d) E ->
    dbase d <> dtip d ->
    same_face (darts_of E) d (twin d) ->
    dpath (darts_of (E_minus E d)) (dtip d) (dbase d) c ->
    NoDup (dtip d :: map dtip c) ->
    (2 <= length c)%nat ->
    (forall v, In v (ring_of_chain (d :: c)) -> my <> py v) ->
    (exists t, 0 < t < 1 /\
       edge_x_at d my = (1 - t) * px (fst d) + t * px (snd d) /\
       my = (1 - t) * py (fst d) + t * py (snd d)) ->
    0 < ef ->
    exists ef', 0 < ef' /\ ef' <= ef /\
      connected_in_complement_cont (ring_of_chain (d :: c))
        (mkPoint (edge_x_at d my - ef') my)
        (mkPoint (edge_x_at d my + ef') my).

(* -------------------------------------------------------------------------- *)
(* §2  The bridge: the residual discharges the transport premise.              *)
(* -------------------------------------------------------------------------- *)

Theorem face_transport_premise_of_walk_connectivity :
  forall (E : list Edge),
    no_horizontal_darts (darts_of E) ->
    walk_small_offset_connectivity E ->
    face_transport_premise E.
Proof.
  intros E Hnh Hwalk d c my ef HdE Hntwin Hproper Hsf Hp Hnd Hlen
         Hgen Hint Hef Hav1 Hav2 Hc1 Hc2 Hstrip.
  destruct (Hwalk d c my ef HdE Hntwin Hproper Hsf Hp Hnd Hlen
              Hgen Hint Hef) as [ef' [Hef'0 [Hef'le Hconn]]].
  assert (Hnhd : py (fst d) <> py (snd d)).
  { apply Hnh. apply in_darts_of_orig. exact HdE. }
  pose proof (strip_lift_connected (ring_of_chain (d :: c)) d my ef ef'
                Hnhd Hef'0 Hef'le Hstrip Hconn) as Hbig.
  apply (walk_straddle_parity (ring_of_chain (d :: c)) d ef my).
  - apply face_walk_closed. discriminate.
  - exact Hav1.
  - exact Hav2.
  - exact Hbig.
Qed.

(* -------------------------------------------------------------------------- *)
(* Axiom audit.  Named-residual bridge; allowlist axioms only.                 *)
(* -------------------------------------------------------------------------- *)

Print Assumptions face_transport_premise_of_walk_connectivity.

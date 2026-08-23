(* ==========================================================================
   WalkCorridor.v

   [H-bridge attack, C-3c step 2] The WALK-DART CORRIDOR DICHOTOMY: every
   non-horizontal dart of the arrangement carries a ring-free westward
   corridor over any window strictly inside its y-span -- no matter how
   the dart sits relative to the cycle ring.

   The face-walk transport visits arbitrary E-darts; against the cycle
   ring each one is in exactly one of three positions, and each position
   already has its wall theorem:

     - a RING dart: `JCTWallClear.wall_corridor_clear` on the taut cycle
       ring (tautness is derived in `HBridgeCoreSlice.v`);
     - the TWIN of a ring dart: the SAME carrier line, so the corridor
       is pointwise the ring dart's corridor (`edge_x_at_twin` /
       `corridor_twin`) and the wall theorem transfers (the span window
       mirrors because `twin` swaps the endpoints);
     - FOREIGN (neither): `ForeignCorridor.foreign_corridor_clear`, the
       twin-aware-guards route.

   `walk_dart_corridor_clear` packages the three-way split behind
   `in_dec`/`edge_eq_dec`, so downstream transport steps (C-3e/C-3f)
   never case on ring membership themselves.

   No `Admitted` / `Axiom` / `Parameter`; allowlist axioms only.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
   ========================================================================== *)

From Stdlib Require Import Reals Lra List.
From NTS.Proofs Require Import JordanRingKit.
From NTS.Proofs Require Import ConvexOffringSeam JCTParityTransport
                               JCTHalfOpenParity JCTGenericStability
                               JCTLevelJump JCTTrappedHalf JCTSeamAssembly
                               JCTEscapeDescent JCTEastApproach JCTCorridor
                               JCTWalkKit JCTWalkStep JCTTautClearance
                               JCTWallClear Dart FaceTwinAware
                               EdgeConnectivity HBridgeCoreSlice
                               ForeignCorridor.

Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  Twin transfer: the reversed dart has the SAME carrier line.             *)
(* -------------------------------------------------------------------------- *)

Lemma edge_x_at_twin :
  forall (e : Edge) (y : R),
    py (fst e) <> py (snd e) ->
    edge_x_at (twin e) y = edge_x_at e y.
Proof.
  intros e y Hnh.
  destruct e as [a b]. cbn [fst snd] in Hnh.
  unfold twin, edge_x_at. cbn [fst snd].
  field. lra.
Qed.

Lemma corridor_twin :
  forall (e : Edge) (delta y : R),
    py (fst e) <> py (snd e) ->
    corridor (twin e) delta y = corridor e delta y.
Proof.
  intros e delta y Hnh.
  unfold corridor. rewrite (edge_x_at_twin e y Hnh). reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  The dichotomy headline.                                                 *)
(* -------------------------------------------------------------------------- *)

Theorem walk_dart_corridor_clear :
  forall (D : list Dart) (r : Ring) (x : Dart) (ylo yhi : R),
    ring_taut r ->
    pairwise_no_proper_cross_twin_aware D ->
    no_foreign_vertex_twin_aware D ->
    In x D ->
    (forall f, In f (ring_edges r) -> In f D) ->
    ((py (fst x) < ylo /\ yhi < py (snd x)) \/
     (py (snd x) < ylo /\ yhi < py (fst x))) ->
    ylo <= yhi ->
    exists delta0, 0 < delta0 /\
      forall delta, 0 < delta < delta0 ->
        forall y, ylo <= y <= yhi ->
          ~ ring_image r (corridor x delta y).
Proof.
  intros D r x ylo yhi Htaut Hcross Hforeign Hx HringD Hspan Hle.
  assert (Hnh : py (fst x) <> py (snd x)) by (destruct Hspan; lra).
  destruct (in_dec edge_eq_dec x (ring_edges r)) as [Hring | Hnotring].
  - (* a ring dart: the taut wall theorem *)
    exact (wall_corridor_clear r x ylo yhi Htaut Hring Hspan Hle).
  - destruct (in_dec edge_eq_dec (twin x) (ring_edges r))
      as [Hringtw | Hnotringtw].
    + (* the twin of a ring dart: same carrier, mirrored span *)
      assert (Hspan' : (py (fst (twin x)) < ylo /\ yhi < py (snd (twin x))) \/
                       (py (snd (twin x)) < ylo /\ yhi < py (fst (twin x)))).
      { unfold twin. cbn [fst snd].
        destruct Hspan as [H | H]; [ right | left ]; exact H. }
      destruct (wall_corridor_clear r (twin x) ylo yhi Htaut Hringtw
                  Hspan' Hle) as [delta0 [Hd0 Hclear]].
      exists delta0. split; [ exact Hd0 | ].
      intros delta Hd y Hw.
      rewrite <- (corridor_twin x delta y Hnh).
      exact (Hclear delta Hd y Hw).
    + (* foreign: the twin-aware-guards route *)
      apply (foreign_corridor_clear D r x ylo yhi Hcross Hforeign Hx);
        [ | exact Hspan | exact Hle ].
      intros f Hf.
      split; [ exact (HringD f Hf) | ].
      split.
      * intro Heq. subst f. exact (Hnotring Hf).
      * intro Heq.
        apply Hnotringtw.
        rewrite Heq, twin_involutive. exact Hf.
Qed.

(* -------------------------------------------------------------------------- *)
(* Axiom audit.  Assembly wiring; allowlist axioms only.                       *)
(* -------------------------------------------------------------------------- *)

Print Assumptions edge_x_at_twin.
Print Assumptions walk_dart_corridor_clear.

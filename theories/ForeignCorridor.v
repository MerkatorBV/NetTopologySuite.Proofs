(* ==========================================================================
   ForeignCorridor.v

   [H-bridge attack, C-3c step 1] The E-LEVEL corridor clearance: the
   westward corridor along a NON-RING dart of the arrangement is
   skeleton-free against the cycle ring, for every sufficiently small
   positive offset.

   `JCTWallClear.wall_corridor_clear` proves this when the carrier is a
   RING edge, using ring tautness to dispose of the one branch of the
   case tree that produces a TOUCH WITNESS (the edge f meeting the
   carrier's LINE at a window height): by `taut_no_line_touch` the
   toucher IS the carrier.  For a face-walk dart that is NOT on the
   cycle, tautness against the ring says nothing -- but the two
   twin-aware noding guards refute the touch OUTRIGHT
   (`foreign_dart_no_line_touch`): inside a window strictly interior to
   the carrier's y-span the touch point is interior to the carrier, so

     - a touch at interior parameter of f is an interior-interior
       meeting, excluded by `pairwise_no_proper_cross_twin_aware`;
     - a touch at an ENDPOINT of f puts that endpoint in the open
       interior of the carrier, excluded by
       `no_foreign_vertex_twin_aware`.

   The rest of the case tree is geometry shared with the taut route --
   factored in `JCTWallClear.per_edge_clear_core` (this rung's refactor)
   and instantiated here with the refutation handler
   (`foreign_per_edge_clear`).  `foreign_corridor_clear` folds the
   per-edge margins over the ring's edge list, exactly mirroring
   `wall_corridor_clear`.

   Together the two wall theorems cover every along-edge step of the
   face-walk transport: ring darts (and twins of ring darts, whose
   carrier LINE is the same) via `wall_corridor_clear` on the taut cycle
   ring; every other walk dart via this file.

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
                               HBridgeCoreSlice.

Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  The guards refute any line touch inside the span-interior window.       *)
(* -------------------------------------------------------------------------- *)

Lemma foreign_dart_no_line_touch :
  forall (D : list Dart) (e1 f : Dart) (ylo yhi : R),
    pairwise_no_proper_cross_twin_aware D ->
    no_foreign_vertex_twin_aware D ->
    In e1 D -> In f D -> e1 <> f -> e1 <> twin f ->
    py (fst e1) <> py (snd e1) ->
    ((py (fst e1) < ylo /\ yhi < py (snd e1)) \/
     (py (snd e1) < ylo /\ yhi < py (fst e1))) ->
    forall (s y : R),
      0 <= s <= 1 ->
      ylo <= y <= yhi ->
      y = (1 - s) * py (fst f) + s * py (snd f) ->
      edge_x_at e1 y = (1 - s) * px (fst f) + s * px (snd f) ->
      False.
Proof.
  intros D e1 f ylo yhi Hcross Hforeign Hin1 Hinf Hne Hnetw Hnh Hspan
         s y Hs Hw Hyf Hxf.
  set (t := (y - py (fst e1)) / (py (snd e1) - py (fst e1))).
  assert (Hd : py (snd e1) - py (fst e1) <> 0) by lra.
  (* t is strictly interior: the window is strictly inside the span *)
  assert (Htint : 0 < t < 1).
  { unfold t. destruct Hspan as [[H1 H2] | [H1 H2]].
    - split.
      + apply Rmult_lt_reg_r with (py (snd e1) - py (fst e1)); [ lra | ].
        replace ((y - py (fst e1)) / (py (snd e1) - py (fst e1))
                   * (py (snd e1) - py (fst e1)))
          with (y - py (fst e1)) by (field; lra). lra.
      + apply Rmult_lt_reg_r with (py (snd e1) - py (fst e1)); [ lra | ].
        replace ((y - py (fst e1)) / (py (snd e1) - py (fst e1))
                   * (py (snd e1) - py (fst e1)))
          with (y - py (fst e1)) by (field; lra). lra.
    - split.
      + apply Rmult_lt_reg_r with (py (fst e1) - py (snd e1)); [ lra | ].
        replace ((y - py (fst e1)) / (py (snd e1) - py (fst e1))
                   * (py (fst e1) - py (snd e1)))
          with (py (fst e1) - y) by (field; lra). lra.
      + apply Rmult_lt_reg_r with (py (fst e1) - py (snd e1)); [ lra | ].
        replace ((y - py (fst e1)) / (py (snd e1) - py (fst e1))
                   * (py (fst e1) - py (snd e1)))
          with (py (fst e1) - y) by (field; lra). lra. }
  (* e1 at parameter t sits exactly at (edge_x_at e1 y, y) *)
  assert (Hyt : (1 - t) * py (fst e1) + t * py (snd e1) = y)
    by (unfold t; field; lra).
  assert (Hxt : (1 - t) * px (fst e1) + t * px (snd e1) = edge_x_at e1 y).
  { rewrite <- Hyt. rewrite (on_carrier_x e1 t Hnh). reflexivity. }
  destruct Hs as [Hs0 Hs1].
  destruct (Rle_lt_or_eq_dec 0 s Hs0) as [Hspos | Hzero].
  - destruct (Rle_lt_or_eq_dec s 1 Hs1) as [Hslt | Hone].
    + (* interior-interior meeting: a proper cross *)
      apply (Hcross e1 f Hin1 Hinf Hne Hnetw).
      exists t, s.
      split; [ exact Htint | ].
      split; [ lra | ].
      split; lra.
    + (* s = 1: f's SECOND endpoint is interior to the carrier *)
      destruct (Hforeign e1 f Hin1 Hinf Hne Hnetw) as [_ Hsnd].
      apply Hsnd. exists t.
      split; [ exact Htint | ].
      rewrite Hone in Hxf, Hyf.
      split; lra.
  - (* s = 0: f's FIRST endpoint is interior to the carrier *)
    destruct (Hforeign e1 f Hin1 Hinf Hne Hnetw) as [Hfst _].
    apply Hfst. exists t.
    split; [ exact Htint | ].
    rewrite <- Hzero in Hxf, Hyf.
    split; lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  The per-edge clearance for a foreign carrier.                           *)
(* -------------------------------------------------------------------------- *)

Lemma foreign_per_edge_clear :
  forall (D : list Dart) (e1 f : Dart) (ylo yhi : R),
    pairwise_no_proper_cross_twin_aware D ->
    no_foreign_vertex_twin_aware D ->
    In e1 D -> In f D -> e1 <> f -> e1 <> twin f ->
    ((py (fst e1) < ylo /\ yhi < py (snd e1)) \/
     (py (snd e1) < ylo /\ yhi < py (fst e1))) ->
    ylo <= yhi ->
    exists df, 0 < df /\
      forall delta, 0 < delta < df ->
        forall y, ylo <= y <= yhi ->
          ~ (exists s : R, 0 <= s <= 1 /\
               edge_x_at e1 y - delta = (1 - s) * px (fst f) + s * px (snd f) /\
               y = (1 - s) * py (fst f) + s * py (snd f)).
Proof.
  intros D e1 f ylo yhi Hcross Hforeign Hin1 Hinf Hne Hnetw Hspan Hle.
  assert (Hnh : py (fst e1) <> py (snd e1)) by (destruct Hspan; lra).
  apply (per_edge_clear_core e1 f ylo yhi Hnh Hle).
  intros [s [y [Hs [Hw [Hyf Hxf]]]]].
  exfalso.
  exact (foreign_dart_no_line_touch D e1 f ylo yhi Hcross Hforeign
           Hin1 Hinf Hne Hnetw Hnh Hspan s y Hs Hw Hyf Hxf).
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  The foreign wall theorem: fold over the ring's edges.                   *)
(* -------------------------------------------------------------------------- *)

Theorem foreign_corridor_clear :
  forall (D : list Dart) (r : Ring) (e1 : Dart) (ylo yhi : R),
    pairwise_no_proper_cross_twin_aware D ->
    no_foreign_vertex_twin_aware D ->
    In e1 D ->
    (forall f, In f (ring_edges r) -> In f D /\ e1 <> f /\ e1 <> twin f) ->
    ((py (fst e1) < ylo /\ yhi < py (snd e1)) \/
     (py (snd e1) < ylo /\ yhi < py (fst e1))) ->
    ylo <= yhi ->
    exists delta0, 0 < delta0 /\
      forall delta, 0 < delta < delta0 ->
        forall y, ylo <= y <= yhi ->
          ~ ring_image r (corridor e1 delta y).
Proof.
  intros D r e1 ylo yhi Hcross Hforeign Hin1 Hring Hspan Hle.
  destruct (clear_fold
              (fun f delta => forall y, ylo <= y <= yhi ->
                 ~ (exists s : R, 0 <= s <= 1 /\
                      edge_x_at e1 y - delta
                        = (1 - s) * px (fst f) + s * px (snd f) /\
                      y = (1 - s) * py (fst f) + s * py (snd f)))
              (ring_edges r)) as [d0 [Hd0 Hball]].
  { intros f Hinf.
    destruct (Hring f Hinf) as [HfD [Hne Hnetw]].
    exact (foreign_per_edge_clear D e1 f ylo yhi Hcross Hforeign
             Hin1 HfD Hne Hnetw Hspan Hle). }
  exists d0. split; [ exact Hd0 | ].
  intros delta Hd y Hw.
  apply (corridor_free_of_edges r e1 ylo yhi delta); [ | exact Hw ].
  intros f Hinf y' Hw'.
  exact (Hball delta Hd f Hinf y' Hw').
Qed.

(* -------------------------------------------------------------------------- *)
(* Axiom audit.  Assembly of banked pieces; allowlist axioms only.             *)
(* -------------------------------------------------------------------------- *)

Print Assumptions foreign_dart_no_line_touch.
Print Assumptions foreign_corridor_clear.

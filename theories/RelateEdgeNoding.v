(* ============================================================================
   NetTopologySuite.Proofs.RelateEdgeNoding
   ----------------------------------------------------------------------------
   Track 2 brick 8: the exact edge-noding pipeline composed end-to-end.

   Bricks 1–7 supply the parts of the Romanschek-style integer-exact noding
   lane for a single host edge:

     1. pos_compare / int128 fit          (RelateEdgePosOrder)
     2. det/det inter_param               (RelateEdgeInterParam)
     3. strict total order + sort         (RelateEdgePosSort)
     4. proper-cross clip to (0,1)        (RelateEdgeInterClip)
     5. equal-ratio merge (epdedup)       (RelateEdgePosMerge)
     6. multi-node cover                  (RelateEdgeSplit)
     7. adjacent exclusive meet + EPos    (RelateEdgeSplitAdj)

   This module packages the **operator** a noder runs on an edge:

     Sorted eple interior EPos list
       --epdedup-->  Sorted eplt unique positions
       --epval---->  sorted real parameters in (0,1)
       --split---->  covering pieces of A–B that meet only at shared nodes.

   Headlines:

     - `noded_edge_params` — the real parameter chain after merge.
     - `edge_noding_cover` / `edge_noding_cover_pieces` — cover after the pipe.
     - `edge_noding_adj_meet` — exclusive meet after the pipe.

   No new geometry: pure composition of Qed-closed bricks.  No `Admitted`,
   no `Axiom`, no `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Grok
   ========================================================================== *)

From Stdlib Require Import Reals Lra List.
From Stdlib Require Import Sorting.Sorted.
From NTS.Proofs Require Import Distance Orientation Segment
                               RelateEdgeInterParam RelateEdgePosOrder
                               RelateEdgePosSort RelateEdgePosMerge
                               RelateEdgeSplit RelateEdgeSplitAdj.

Local Open Scope R_scope.
Import ListNotations.

(* -------------------------------------------------------------------------- *)
(* §1  Interior is hereditary; epdedup preserves it.                          *)
(* -------------------------------------------------------------------------- *)

Lemma all_epos_interior_In :
  forall ps p,
    all_epos_interior ps ->
    In p ps ->
    epos_interior p.
Proof.
  intros ps p Hall Hin.
  induction ps as [| q rest IH]; [contradiction |].
  simpl in Hall. destruct Hall as [Hq Hrest].
  destruct Hin as [Heq | Hin'].
  - rewrite <- Heq. exact Hq.
  - apply IH; assumption.
Qed.

Lemma all_epos_interior_of_In :
  forall ps,
    (forall p, In p ps -> epos_interior p) ->
    all_epos_interior ps.
Proof.
  intros ps H.
  induction ps as [| p rest IH].
  - simpl. exact I.
  - simpl. split.
    + apply H. left. reflexivity.
    + apply IH. intros q Hin. apply H. right. exact Hin.
Qed.

(* Merge never invents positions: every survivor was already interior. *)
Lemma epdedup_all_epos_interior :
  forall ps,
    all_epos_interior ps ->
    all_epos_interior (epdedup ps).
Proof.
  intros ps Hall.
  apply all_epos_interior_of_In.
  intros p Hin.
  apply (all_epos_interior_In ps p Hall).
  apply epdedup_In. exact Hin.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  The pipeline operator.                                                 *)
(* -------------------------------------------------------------------------- *)

(* Real parameters after exact merge: unique strict chain in epval. *)
Definition noded_edge_params (ps : list EPos) : list R :=
  epos_vals (epdedup ps).

Lemma noded_edge_params_sorted_lt :
  forall ps,
    Sorted eple ps ->
    sorted_lt (noded_edge_params ps).
Proof.
  intros ps Hs.
  unfold noded_edge_params.
  apply sorted_eplt_sorted_lt_epval.
  apply epdedup_sorted_eplt.
  exact Hs.
Qed.

Lemma noded_edge_params_all_interior :
  forall ps,
    all_epos_interior ps ->
    all_interior (noded_edge_params ps).
Proof.
  intros ps Hall.
  unfold noded_edge_params.
  apply all_epos_interior_all_interior.
  apply epdedup_all_epos_interior.
  exact Hall.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Cover after the full pipeline.                                         *)
(* -------------------------------------------------------------------------- *)

(* HEADLINE: merge + epval + split covers the host edge. *)
Theorem edge_noding_cover :
  forall A B ps X,
    all_epos_interior ps ->
    Sorted eple ps ->
    between A B X ->
    exists t0 t1,
      In (t0, t1) (consecutive_pairs (edge_params (noded_edge_params ps))) /\
      between (lerp A B t0) (lerp A B t1) X.
Proof.
  intros A B ps X Hall Hs HX.
  unfold noded_edge_params.
  apply edge_split_cover_of_epos.
  - apply epdedup_all_epos_interior. exact Hall.
  - apply epdedup_sorted_eplt. exact Hs.
  - exact HX.
Qed.

Theorem edge_noding_cover_pieces :
  forall A B ps X,
    all_epos_interior ps ->
    Sorted eple ps ->
    between A B X ->
    exists P Q,
      In (P, Q) (edge_pieces A B (noded_edge_params ps)) /\
      between P Q X.
Proof.
  intros A B ps X Hall Hs HX.
  unfold noded_edge_params.
  apply edge_split_cover_pieces_of_epos.
  - apply epdedup_all_epos_interior. exact Hall.
  - apply epdedup_sorted_eplt. exact Hs.
  - exact HX.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Exclusive meet after the full pipeline.                                *)
(* -------------------------------------------------------------------------- *)

(* HEADLINE: after merge, adjacent noded pieces meet only at the shared node. *)
Theorem edge_noding_adj_meet :
  forall A B ps t0 t1 t2 X,
    all_epos_interior ps ->
    Sorted eple ps ->
    In (t0, t1) (consecutive_pairs (edge_params (noded_edge_params ps))) ->
    In (t1, t2) (consecutive_pairs (edge_params (noded_edge_params ps))) ->
    between (lerp A B t0) (lerp A B t1) X ->
    between (lerp A B t1) (lerp A B t2) X ->
    X = lerp A B t1.
Proof.
  intros A B ps t0 t1 t2 X Hall Hs H01 H12 Hb01 Hb12.
  unfold noded_edge_params in *.
  apply (edge_params_adj_meet_of_epos A B (epdedup ps) t0 t1 t2 X).
  - apply epdedup_all_epos_interior. exact Hall.
  - apply epdedup_sorted_eplt. exact Hs.
  - exact H01.
  - exact H12.
  - exact Hb01.
  - exact Hb12.
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  Packaging: cover and meet in one statement.                            *)
(* -------------------------------------------------------------------------- *)

(* The noder's contract on one host edge: every host point sits on a piece of
   the merged chain, and any two adjacent pieces of that chain are exclusive
   except at their shared node. *)
Theorem edge_noding_sound :
  forall A B ps,
    all_epos_interior ps ->
    Sorted eple ps ->
    (forall X, between A B X ->
       exists t0 t1,
         In (t0, t1) (consecutive_pairs (edge_params (noded_edge_params ps))) /\
         between (lerp A B t0) (lerp A B t1) X) /\
    (forall t0 t1 t2 X,
       In (t0, t1) (consecutive_pairs (edge_params (noded_edge_params ps))) ->
       In (t1, t2) (consecutive_pairs (edge_params (noded_edge_params ps))) ->
       between (lerp A B t0) (lerp A B t1) X ->
       between (lerp A B t1) (lerp A B t2) X ->
       X = lerp A B t1).
Proof.
  intros A B ps Hall Hs.
  split.
  - intros X HX. apply edge_noding_cover; assumption.
  - intros t0 t1 t2 X H01 H12 Hb01 Hb12.
    apply (edge_noding_adj_meet A B ps t0 t1 t2 X Hall Hs H01 H12 Hb01 Hb12).
Qed.

(* -------------------------------------------------------------------------- *)
(* §6  Audit footprint.                                                       *)
(* -------------------------------------------------------------------------- *)

Print Assumptions edge_noding_cover.
Print Assumptions edge_noding_cover_pieces.
Print Assumptions edge_noding_adj_meet.
Print Assumptions edge_noding_sound.

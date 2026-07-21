(* ============================================================================
   NetTopologySuite.Proofs.RelateEdgeNode
   ----------------------------------------------------------------------------
   Track 2 brick 9: a proper-crossing intersection is an interior `EPos` node.

   Bricks 1–8 deliver compare → geometry → sort → clip → merge → split cover
   → exclusive meet → the composed noding pipeline.  The missing producer is:
   given integer endpoints and a proper-crossing cut, *construct* the exact
   edge-position node that the pipeline consumes.

   Under the Romanschek integer regime the intersection parameter on edge
   A–B cut by C–D is the rational

       num / den   with   num = idet C D A,
                          den = idet C D A − idet C D B

   (brick 2).  Brick 4 proves that a negative idet-product forces this ratio
   into (0, 1).  This module:

     - normalises (num, den) into an `EPos` (positive denominator WLOG),
     - proves `epval` recovers `inter_param`,
     - proves the node is `epos_interior` under proper-cross,
     - feeds the singleton list into `edge_noding_sound` (brick 8).

   No `Admitted`, no `Axiom`, no `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Grok
   ========================================================================== *)

From Stdlib Require Import ZArith Lia Reals Lra List.
From Stdlib Require Import Sorting.Sorted.
From NTS.Proofs Require Import Distance Orientation Segment
                               RelateIntDetBound RelateEdgePosOrder
                               RelateEdgePosSort RelateEdgeInterParam
                               RelateEdgeInterClip RelateEdgePosMerge
                               RelateEdgeSplit RelateEdgeSplitAdj
                               RelateEdgeNoding.

Local Open Scope Z_scope.
Import ListNotations.

(* -------------------------------------------------------------------------- *)
(* §1  Ratio → EPos with positive-denominator normal form.                    *)
(* -------------------------------------------------------------------------- *)

(* Opposite signs force a nonzero difference (the inter_den). *)
Lemma den_nz_of_opposite_signs :
  forall a b : Z, a * b < 0 -> a - b <> 0.
Proof. intros a b H. nia. Qed.

(* Build an EPos from a nonzero-denominator integer ratio, flipping both
   signs when the raw denominator is negative (ratio unchanged). *)
Definition epos_of_ratio (n d : Z) (Hd : d <> 0) : EPos.
Proof.
  destruct (Z_lt_dec 0 d) as [Hp | Hn].
  - exact {| pnum := n; pden := d; pden_pos := Hp |}.
  - assert (Hpos : 0 < - d) by lia.
    exact {| pnum := - n; pden := - d; pden_pos := Hpos |}.
Defined.

Lemma epos_of_ratio_pden_pos :
  forall n d (Hd : d <> 0), 0 < pden (epos_of_ratio n d Hd).
Proof.
  intros n d Hd.
  unfold epos_of_ratio.
  destruct (Z_lt_dec 0 d) as [Hp | Hn]; simpl; lia.
Qed.

(* epval recovers the true rational (sign normalisation is invisible in R). *)
Lemma epval_epos_of_ratio :
  forall n d (Hd : d <> 0),
    (epval (epos_of_ratio n d Hd) = IZR n / IZR d)%R.
Proof.
  intros n d Hd.
  unfold epos_of_ratio, epval.
  destruct (Z_lt_dec 0 d) as [Hp | Hn]; simpl.
  - reflexivity.
  - (* IZR (-n) / IZR (-d) = IZR n / IZR d *)
    rewrite !opp_IZR.
    field.
    apply not_0_IZR. exact Hd.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  Integer proper-cross → EPos node.                                      *)
(* -------------------------------------------------------------------------- *)

Definition inter_numZ (ax ay bx by_ cx cy dx dy : Z) : Z :=
  idet cx cy dx dy ax ay.

Definition inter_denZ (ax ay bx by_ cx cy dx dy : Z) : Z :=
  idet cx cy dx dy ax ay - idet cx cy dx dy bx by_.

(* Cutting-line opposite signs ⇒ inter_denZ ≠ 0. *)
Lemma inter_denZ_nz_of_product :
  forall ax ay bx by_ cx cy dx dy : Z,
    idet cx cy dx dy ax ay * idet cx cy dx dy bx by_ < 0 ->
    inter_denZ ax ay bx by_ cx cy dx dy <> 0.
Proof.
  intros. unfold inter_denZ.
  apply den_nz_of_opposite_signs. exact H.
Qed.

(* The exact node on edge A–B from a proper-crossing cut C–D (integer coords). *)
Definition epos_of_proper_cross
  (ax ay bx by_ cx cy dx dy : Z)
  (Hprod : idet cx cy dx dy ax ay * idet cx cy dx dy bx by_ < 0) : EPos :=
  epos_of_ratio
    (inter_numZ ax ay bx by_ cx cy dx dy)
    (inter_denZ ax ay bx by_ cx cy dx dy)
    (inter_denZ_nz_of_product ax ay bx by_ cx cy dx dy Hprod).

(* HEADLINE: epval of the constructed node is the real inter_param. *)
Theorem epos_of_proper_cross_epval :
  forall ax ay bx by_ cx cy dx dy
    (Hprod : idet cx cy dx dy ax ay * idet cx cy dx dy bx by_ < 0),
    (epval (epos_of_proper_cross ax ay bx by_ cx cy dx dy Hprod)
     = inter_param (ptZ ax ay) (ptZ bx by_) (ptZ cx cy) (ptZ dx dy))%R.
Proof.
  intros ax ay bx by_ cx cy dx dy Hprod.
  unfold epos_of_proper_cross, inter_param, inter_numZ, inter_denZ.
  rewrite epval_epos_of_ratio.
  rewrite inter_num_is_idet, inter_den_is_idet.
  reflexivity.
Qed.

(* HEADLINE: the constructed node is strictly interior (clip regime). *)
Theorem epos_of_proper_cross_interior :
  forall ax ay bx by_ cx cy dx dy
    (Hprod : idet cx cy dx dy ax ay * idet cx cy dx dy bx by_ < 0),
    epos_interior (epos_of_proper_cross ax ay bx by_ cx cy dx dy Hprod).
Proof.
  intros ax ay bx by_ cx cy dx dy Hprod.
  unfold epos_interior.
  rewrite epos_of_proper_cross_epval.
  exact (inter_param_open_of_idet_product ax ay bx by_ cx cy dx dy Hprod).
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Singleton feeds the noding pipeline.                                   *)
(* -------------------------------------------------------------------------- *)

Lemma Sorted_eple_singleton : forall p : EPos, Sorted eple [p].
Proof.
  intros p. constructor; [constructor | constructor].
Qed.

Lemma all_epos_interior_singleton :
  forall p, epos_interior p -> all_epos_interior [p].
Proof.
  intros p Hp. simpl. split; [exact Hp | exact I].
Qed.

(* HEADLINE: a proper-cross node is a valid one-node input to edge_noding_sound. *)
Theorem edge_noding_of_proper_cross :
  forall ax ay bx by_ cx cy dx dy
    (Hprod : idet cx cy dx dy ax ay * idet cx cy dx dy bx by_ < 0),
    let p := epos_of_proper_cross ax ay bx by_ cx cy dx dy Hprod in
    all_epos_interior [p] /\
    Sorted eple [p] /\
    (forall X,
       between (ptZ ax ay) (ptZ bx by_) X ->
       exists t0 t1 : R,
         In (t0, t1)
           (consecutive_pairs
              (edge_params (noded_edge_params [p]))) /\
         between (lerp (ptZ ax ay) (ptZ bx by_) t0)
                 (lerp (ptZ ax ay) (ptZ bx by_) t1) X).
Proof.
  intros ax ay bx by_ cx cy dx dy Hprod.
  set (p := epos_of_proper_cross ax ay bx by_ cx cy dx dy Hprod).
  pose proof (epos_of_proper_cross_interior ax ay bx by_ cx cy dx dy Hprod) as Hint.
  assert (Hall : all_epos_interior [p]).
  { apply all_epos_interior_singleton. exact Hint. }
  assert (Hs : Sorted eple [p]) by apply Sorted_eple_singleton.
  split; [exact Hall |].
  split; [exact Hs |].
  intros X HX.
  apply (edge_noding_cover (ptZ ax ay) (ptZ bx by_) [p] X Hall Hs HX).
Qed.

(* Full noder contract on the singleton proper-cross node. *)
Theorem edge_noding_sound_of_proper_cross :
  forall ax ay bx by_ cx cy dx dy
    (Hprod : idet cx cy dx dy ax ay * idet cx cy dx dy bx by_ < 0),
    let p := epos_of_proper_cross ax ay bx by_ cx cy dx dy Hprod in
    all_epos_interior [p] /\
    Sorted eple [p] /\
    (forall X,
       between (ptZ ax ay) (ptZ bx by_) X ->
       exists t0 t1 : R,
         In (t0, t1)
           (consecutive_pairs
              (edge_params (noded_edge_params [p]))) /\
         between (lerp (ptZ ax ay) (ptZ bx by_) t0)
                 (lerp (ptZ ax ay) (ptZ bx by_) t1) X) /\
    (forall t0 t1 t2 X,
       In (t0, t1)
         (consecutive_pairs (edge_params (noded_edge_params [p]))) ->
       In (t1, t2)
         (consecutive_pairs (edge_params (noded_edge_params [p]))) ->
       between (lerp (ptZ ax ay) (ptZ bx by_) t0)
               (lerp (ptZ ax ay) (ptZ bx by_) t1) X ->
       between (lerp (ptZ ax ay) (ptZ bx by_) t1)
               (lerp (ptZ ax ay) (ptZ bx by_) t2) X ->
       X = lerp (ptZ ax ay) (ptZ bx by_) t1).
Proof.
  intros ax ay bx by_ cx cy dx dy Hprod.
  set (p := epos_of_proper_cross ax ay bx by_ cx cy dx dy Hprod).
  pose proof (epos_of_proper_cross_interior ax ay bx by_ cx cy dx dy Hprod) as Hint.
  assert (Hall : all_epos_interior [p]) by (apply all_epos_interior_singleton; exact Hint).
  assert (Hs : Sorted eple [p]) by apply Sorted_eple_singleton.
  split; [exact Hall |].
  split; [exact Hs |].
  pose proof (edge_noding_sound (ptZ ax ay) (ptZ bx by_) [p] Hall Hs) as Hsnd.
  destruct Hsnd as [Hcov Hmeet].
  split; [exact Hcov | exact Hmeet].
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Audit footprint.                                                       *)
(* -------------------------------------------------------------------------- *)

Print Assumptions epos_of_proper_cross_epval.
Print Assumptions epos_of_proper_cross_interior.
Print Assumptions edge_noding_of_proper_cross.
Print Assumptions edge_noding_sound_of_proper_cross.

(* ============================================================================
   NetTopologySuite.Proofs.DiscOverlay
   ----------------------------------------------------------------------------
   DISC_OVERLAY oracle mode — two-disc OverlayNGCurve closed form (OV-DISC).

   JTS draft PR #8 (`cursor/curve-perf-gate-45a0`, head `f58d56a3`) landed
   exact two-disc overlay as package-private `CircularDiscOverlay` (R1.5 in
   OverlayNGCurve).  Crossing CAP/CUP/SUB/XOR of two circular discs is a
   closed form (lens / blob / crescent / both crescents).  This file is the
   Rocq twin: the corpus does not trust unpinned hand-written geometry.

   Name gate (NTSC0001): OverlayNGCurve, never OverlayNGCurved.

   Phase-0 (`feat/overlayng-phase0-red`, OverlayNGCurve.v) already proved
   that crossing cells never collapse algebraically to A / B / A∪B / ∅.
   This file is the per-shape closed form for the disc-disc crossing cell —
   not a shortcut around that theorem.

   Reuses the EXISTING radical-axis kernel (do not invent a second one):

     ArcArcCircles.radical_axis_{a,h,ux,uy}
     ArcArcCircles.radical_point_{plus,minus}
     ArcArcCircles.radical_points_on_circles
     ArcArcCircles.two_circles_radical_point_unique

   Same formula as ARC_ARC_XY / CircularArcDensifier.intersectCircles:

     d  = |C2 − C1|
     reject if d > r1+r2 or d < |r1−r2| or d = 0
     a  = (r1² − r2² + d²) / (2d)
     h² = r1² − a²
     M  = C1 + a · û
     P± = M ± h · û⊥

   Then the four OverlayNGCurve results as point-sets of two FULL discs
   (Disk.in_disk, closed):

     CAP ∩  lens      = A ∩ B
     CUP ∪  blob      = A ∪ B
     SUB ∖  crescent  = A \ B
     XOR Δ  crescents = (A \ B) ∪ (B \ A)

   INTERFACE-BOUNDARY split (same as ARC_ARC_XY): this file is the R-side
   characterization (Qed, 3-axiom, no new axioms, no Admitted).  Emitted
   node coordinates and the closed-form area (acos / sqrt) live in the
   oracle driver — transcendental, no Coq-extractable form, rounded once
   past exact Q centres.

   Locked fixture (CIRCLE_5 ∩ CIRCLE_CROSSING):
     centres (0,0) and (7,0), r = 5
     nodes   (7/2, ±√(51/4))  i.e. (3.5, ±√12.75)

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.6
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import Distance Disk Overlay ArcArcCircles.

Local Open Scope R_scope.

(* ========================================================================== *)
(* §1  OverlayNGCurve mnemonics on two closed discs.                          *)
(* ========================================================================== *)

Definition lens (A B : Disk) (p : Point) : Prop :=
  in_disk A p /\ in_disk B p.

Definition blob (A B : Disk) (p : Point) : Prop :=
  in_disk A p \/ in_disk B p.

Definition crescent (A B : Disk) (p : Point) : Prop :=
  in_disk A p /\ ~ in_disk B p.

Definition crescents (A B : Disk) (p : Point) : Prop :=
  crescent A B p \/ crescent B A p.

(* OverlayNGCurve op dispatch.  CAP/CUP/SUB/XOR are the product mnemonics
   for Intersection/Union/Difference/SymDiff (docs/overlay-ng-curve-ops-
   mnemonics.md).  Never OverlayNGCurved. *)
Definition disc_overlay (op : BooleanOp) (A B : Disk) (p : Point) : Prop :=
  match op with
  | Intersection => lens A B p
  | Union        => blob A B p
  | Difference   => crescent A B p
  | SymDiff      => crescents A B p
  end.

Definition overlayng_cap (A B : Disk) (p : Point) : Prop := lens A B p.
Definition overlayng_cup (A B : Disk) (p : Point) : Prop := blob A B p.
Definition overlayng_sub (A B : Disk) (p : Point) : Prop := crescent A B p.
Definition overlayng_xor (A B : Disk) (p : Point) : Prop := crescents A B p.

Lemma disc_overlay_cap :
  forall A B p, disc_overlay Intersection A B p <-> overlayng_cap A B p.
Proof. intros. reflexivity. Qed.

Lemma disc_overlay_cup :
  forall A B p, disc_overlay Union A B p <-> overlayng_cup A B p.
Proof. intros. reflexivity. Qed.

Lemma disc_overlay_sub :
  forall A B p, disc_overlay Difference A B p <-> overlayng_sub A B p.
Proof. intros. reflexivity. Qed.

Lemma disc_overlay_xor :
  forall A B p, disc_overlay SymDiff A B p <-> overlayng_xor A B p.
Proof. intros. reflexivity. Qed.

(* ========================================================================== *)
(* §2  Point-set algebra (G1–G4 self-ops + crossing-cell identities).         *)
(* ========================================================================== *)

Lemma lens_self : forall A p, lens A A p <-> in_disk A p.
Proof. intros. unfold lens. tauto. Qed.

Lemma blob_self : forall A p, blob A A p <-> in_disk A p.
Proof. intros. unfold blob. tauto. Qed.

Lemma crescent_self_empty : forall A p, ~ crescent A A p.
Proof. intros. unfold crescent. tauto. Qed.

Lemma crescents_self_empty : forall A p, ~ crescents A A p.
Proof. intros. unfold crescents, crescent. tauto. Qed.

Lemma lens_comm : forall A B p, lens A B p <-> lens B A p.
Proof. intros. unfold lens. tauto. Qed.

Lemma blob_comm : forall A B p, blob A B p <-> blob B A p.
Proof. intros. unfold blob. tauto. Qed.

Lemma crescents_comm : forall A B p, crescents A B p <-> crescents B A p.
Proof. intros. unfold crescents, crescent. tauto. Qed.

(* CAP ∪ XOR = CUP  and  CAP ∪ SUB = A, as point-sets. *)
Lemma lens_or_crescents_iff_blob :
  forall A B p, lens A B p \/ crescents A B p <-> blob A B p.
Proof. intros. unfold lens, crescents, crescent, blob. tauto. Qed.

Lemma lens_or_crescent_iff_A :
  forall A B p, lens A B p \/ crescent A B p <-> in_disk A p.
Proof. intros. unfold lens, crescent. tauto. Qed.

Lemma crescent_subset_blob :
  forall A B p, crescent A B p -> blob A B p.
Proof. intros. unfold crescent, blob in *. tauto. Qed.

(* ========================================================================== *)
(* §3  Proper intersection + radical-axis nodes lie in the lens.              *)
(*                                                                            *)
(* Reuses ArcArcCircles: any point on both CIRCLE boundaries is one of the   *)
(* two named radical points, and both named points lie on both circles,      *)
(* hence in both CLOSED discs (the lens).                                    *)
(* ========================================================================== *)

Definition discs_properly_intersect (A B : Disk) : Prop :=
  0 < dradius A /\
  0 < dradius B /\
  0 < dist (dcentre A) (dcentre B) /\
  Rabs (dradius A - dradius B) < dist (dcentre A) (dcentre B) /\
  dist (dcentre A) (dcentre B) < dradius A + dradius B.

Lemma on_circle_in_disk :
  forall (O : Point) (r : R) (P : Point),
    dist_sq O P = r * r ->
    in_disk (mkDisk O r) P.
Proof.
  intros O r P Heq.
  apply in_disk_extensionality. lra.
Qed.

Theorem radical_nodes_in_lens :
  forall (A B : Disk),
    discs_properly_intersect A B ->
    lens A B (radical_point_plus (dcentre A) (dcentre B) (dradius A) (dradius B)) /\
    lens A B (radical_point_minus (dcentre A) (dcentre B) (dradius A) (dradius B)).
Proof.
  intros A B [Hr1 [Hr2 [Hdpos [Hrabs Hdlt]]]].
  destruct (radical_points_on_circles
              (dcentre A) (dcentre B) (dradius A) (dradius B)
              Hr1 Hr2 Hdpos Hrabs Hdlt)
    as [[Hp1 Hp2] [Hm1 Hm2]].
  unfold lens.
  destruct A as [O1 r1], B as [O2 r2]. cbn in *.
  split.
  - split; apply on_circle_in_disk; assumption.
  - split; apply on_circle_in_disk; assumption.
Qed.

Theorem lens_boundary_is_radical_node :
  forall (A B : Disk) (X : Point),
    0 < dist (dcentre A) (dcentre B) ->
    dist_sq (dcentre A) X = dradius A * dradius A ->
    dist_sq (dcentre B) X = dradius B * dradius B ->
    X = radical_point_plus (dcentre A) (dcentre B) (dradius A) (dradius B) \/
    X = radical_point_minus (dcentre A) (dcentre B) (dradius A) (dradius B).
Proof.
  intros A B X Hd H1 H2.
  apply two_circles_radical_point_unique; assumption.
Qed.

(* ========================================================================== *)
(* §4  Locked fixture: centres (0,0) and (7,0), r = 5.                        *)
(*     Nodes (7/2, ±√(51/4)) = (3.5, ±√12.75).                                *)
(* ========================================================================== *)

Definition locked_O1 : Point := mkPoint 0 0.
Definition locked_O2 : Point := mkPoint 7 0.
Definition locked_r : R := 5.
Definition locked_A : Disk := mkDisk locked_O1 locked_r.
Definition locked_B : Disk := mkDisk locked_O2 locked_r.

Lemma locked_centres_dist :
  dist locked_O1 locked_O2 = 7.
Proof.
  unfold locked_O1, locked_O2, dist, dist_sq. cbn [px py].
  replace ((0 - 7) * (0 - 7) + (0 - 0) * (0 - 0)) with (7 * 7) by ring.
  replace (7 * 7) with (Rsqr 7) by (unfold Rsqr; ring).
  rewrite sqrt_Rsqr_abs.
  rewrite Rabs_right; lra.
Qed.

Lemma locked_properly_intersect :
  discs_properly_intersect locked_A locked_B.
Proof.
  unfold discs_properly_intersect, locked_A, locked_B, locked_r.
  cbn [dcentre dradius].
  rewrite locked_centres_dist.
  split; [lra|].
  split; [lra|].
  split; [lra|].
  split.
  - replace (5 - 5) with 0 by ring. rewrite Rabs_R0. lra.
  - lra.
Qed.

Lemma locked_radical_a :
  radical_axis_a locked_O1 locked_O2 locked_r locked_r = 7 / 2.
Proof.
  unfold radical_axis_a, locked_r.
  rewrite locked_centres_dist.
  field.
Qed.

Lemma locked_radical_ux :
  radical_axis_ux locked_O1 locked_O2 = 1.
Proof.
  unfold radical_axis_ux.
  rewrite locked_centres_dist.
  unfold locked_O1, locked_O2. cbn [px py].
  field.
Qed.

Lemma locked_radical_uy :
  radical_axis_uy locked_O1 locked_O2 = 0.
Proof.
  unfold radical_axis_uy.
  rewrite locked_centres_dist.
  unfold locked_O1, locked_O2. cbn [px py].
  field.
Qed.

Lemma locked_h2 :
  locked_r * locked_r
    - radical_axis_a locked_O1 locked_O2 locked_r locked_r
      * radical_axis_a locked_O1 locked_O2 locked_r locked_r
  = 51 / 4.
Proof.
  rewrite locked_radical_a. unfold locked_r. field.
Qed.

Lemma locked_h2_nonneg :
  0 <= 51 / 4.
Proof. lra. Qed.

(* P+ = (7/2, +h) and P− = (7/2, −h) with h = √(51/4) = √12.75. *)
Lemma locked_node_plus_coords :
  px (radical_point_plus locked_O1 locked_O2 locked_r locked_r) = 7 / 2 /\
  py (radical_point_plus locked_O1 locked_O2 locked_r locked_r)
    = radical_axis_h locked_O1 locked_O2 locked_r locked_r.
Proof.
  unfold radical_point_plus, locked_O1. cbn [px py].
  rewrite locked_radical_a, locked_radical_ux, locked_radical_uy.
  split; ring.
Qed.

Lemma locked_node_minus_coords :
  px (radical_point_minus locked_O1 locked_O2 locked_r locked_r) = 7 / 2 /\
  py (radical_point_minus locked_O1 locked_O2 locked_r locked_r)
    = - radical_axis_h locked_O1 locked_O2 locked_r locked_r.
Proof.
  unfold radical_point_minus, locked_O1. cbn [px py].
  rewrite locked_radical_a, locked_radical_ux, locked_radical_uy.
  split; ring.
Qed.

Lemma locked_h_sq :
  radical_axis_h locked_O1 locked_O2 locked_r locked_r
    * radical_axis_h locked_O1 locked_O2 locked_r locked_r
  = 51 / 4.
Proof.
  unfold radical_axis_h. rewrite locked_h2.
  apply sqrt_sqrt. exact locked_h2_nonneg.
Qed.

Lemma locked_h_pos :
  0 < radical_axis_h locked_O1 locked_O2 locked_r locked_r.
Proof.
  unfold radical_axis_h. rewrite locked_h2.
  assert (Hsq : sqrt (51 / 4) * sqrt (51 / 4) = 51 / 4).
  { apply sqrt_sqrt. lra. }
  destruct (Rle_or_lt (sqrt (51 / 4)) 0) as [Hle | Hlt].
  - exfalso. nra.
  - exact Hlt.
Qed.

(* Headline: the locked pair's radical nodes are (3.5, ±√12.75).
   Stated as x = 7/2 and y² = 51/4 = 12.75, with opposite y-signs. *)
Theorem locked_disc_nodes :
  px (radical_point_plus locked_O1 locked_O2 locked_r locked_r) = 7 / 2 /\
  py (radical_point_plus locked_O1 locked_O2 locked_r locked_r)
    * py (radical_point_plus locked_O1 locked_O2 locked_r locked_r)
    = 51 / 4 /\
  0 < py (radical_point_plus locked_O1 locked_O2 locked_r locked_r) /\
  px (radical_point_minus locked_O1 locked_O2 locked_r locked_r) = 7 / 2 /\
  py (radical_point_minus locked_O1 locked_O2 locked_r locked_r)
    * py (radical_point_minus locked_O1 locked_O2 locked_r locked_r)
    = 51 / 4 /\
  py (radical_point_minus locked_O1 locked_O2 locked_r locked_r) < 0.
Proof.
  destruct locked_node_plus_coords as [Hpxp Hpyp].
  destruct locked_node_minus_coords as [Hpxm Hpym].
  split; [exact Hpxp|].
  split.
  { rewrite Hpyp. exact locked_h_sq. }
  split.
  { rewrite Hpyp. exact locked_h_pos. }
  split; [exact Hpxm|].
  split.
  { rewrite Hpym. replace ((- radical_axis_h locked_O1 locked_O2 locked_r locked_r)
                             * (- radical_axis_h locked_O1 locked_O2 locked_r locked_r))
      with (radical_axis_h locked_O1 locked_O2 locked_r locked_r
            * radical_axis_h locked_O1 locked_O2 locked_r locked_r) by ring.
    exact locked_h_sq. }
  rewrite Hpym.
  pose proof locked_h_pos as Hh.
  lra.
Qed.

Theorem locked_nodes_in_lens :
  lens locked_A locked_B
    (radical_point_plus locked_O1 locked_O2 locked_r locked_r) /\
  lens locked_A locked_B
    (radical_point_minus locked_O1 locked_O2 locked_r locked_r).
Proof.
  apply radical_nodes_in_lens.
  exact locked_properly_intersect.
Qed.

(* ========================================================================== *)
(* §5  Locked crossing cell is nontrivial (does not collapse to A/B/A∪B/∅).  *)
(*     Concrete witnesses; the general Phase-0 theorem is a separate PR.      *)
(* ========================================================================== *)

Lemma locked_O1_in_A_not_B :
  in_disk locked_A locked_O1 /\ ~ in_disk locked_B locked_O1.
Proof.
  unfold locked_A, locked_B, locked_O1, locked_O2, locked_r, in_disk.
  cbn [dcentre dradius px py].
  split.
  - unfold dist_sq. cbn [px py]. lra.
  - unfold dist_sq. cbn [px py]. lra.
Qed.

Lemma locked_O2_in_B_not_A :
  in_disk locked_B locked_O2 /\ ~ in_disk locked_A locked_O2.
Proof.
  unfold locked_A, locked_B, locked_O1, locked_O2, locked_r, in_disk.
  cbn [dcentre dradius px py].
  split.
  - unfold dist_sq. cbn [px py]. lra.
  - unfold dist_sq. cbn [px py]. lra.
Qed.

Lemma locked_far_outside :
  ~ blob locked_A locked_B (mkPoint 100 0).
Proof.
  unfold blob, locked_A, locked_B, locked_O1, locked_O2, locked_r, in_disk.
  cbn [dcentre dradius].
  unfold dist_sq. cbn [px py].
  intros [H | H]; lra.
Qed.

(* CAP = lens is inhabited (the two nodes) and is neither A, B, A∪B, nor ∅. *)
Theorem locked_crossing_cap_nontrivial :
  (exists p, overlayng_cap locked_A locked_B p) /\
  (exists p, in_disk locked_A p /\ ~ overlayng_cap locked_A locked_B p) /\
  (exists p, in_disk locked_B p /\ ~ overlayng_cap locked_A locked_B p) /\
  (exists p, ~ overlayng_cup locked_A locked_B p).
Proof.
  split.
  - exists (radical_point_plus locked_O1 locked_O2 locked_r locked_r).
    unfold overlayng_cap. apply locked_nodes_in_lens.
  - split.
    + exists locked_O1.
      destruct locked_O1_in_A_not_B as [HA HB].
      split; [exact HA|].
      unfold overlayng_cap, lens. tauto.
    + split.
      * exists locked_O2.
        destruct locked_O2_in_B_not_A as [HB HA].
        split; [exact HB|].
        unfold overlayng_cap, lens. tauto.
      * exists (mkPoint 100 0).
        unfold overlayng_cup. exact locked_far_outside.
Qed.

(* ========================================================================== *)
(* §6  Audit footprint.  3-axiom (classical reals only).  No Admitted.        *)
(* ========================================================================== *)

Print Assumptions disc_overlay_cap.
Print Assumptions lens_or_crescents_iff_blob.
Print Assumptions radical_nodes_in_lens.
Print Assumptions lens_boundary_is_radical_node.
Print Assumptions locked_disc_nodes.
Print Assumptions locked_nodes_in_lens.
Print Assumptions locked_crossing_cap_nontrivial.

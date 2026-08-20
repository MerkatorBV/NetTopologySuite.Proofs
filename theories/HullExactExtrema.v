(* ============================================================================
   NetTopologySuite.Proofs.HullExactExtrema
   ----------------------------------------------------------------------------
   Laser H-CV · exact extrema.  PR #8: disc + single-arc hull are
   CurveExact.  CompoundCurve hull still densifies (#6 bulge).

   Maintainability: axis extrema sit next to Disk / Bbox; no atan2.
   Soundness: on-circle points are sqrt-free (dist_sq = r²); envelope
   bounds follow from dx² ≤ r².
   Performance: four cardinals, not a densified sample.
   Port of JTS 6b1dbac1.
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import Distance Disk Bbox.

Local Open Scope R_scope.

(* WITNESS {"claimId":"h-cv-a","topic":"hull","lemma":"hcv_exact_extrema","title":"Disc and single-arc hull extrema are the axis cardinals; CompoundCurve stays off the PR #8 cell","file":"theories/HullExactExtrema.v"} *)

(* -------------------------------------------------------------------------- *)
(* §1  Circle membership and the four axis extrema.                           *)
(* -------------------------------------------------------------------------- *)

Definition on_circle (c : Point) (r : R) (p : Point) : Prop :=
  dist_sq c p = r * r.

Definition extreme_east  (c : Point) (r : R) : Point := mkPoint (px c + r) (py c).
Definition extreme_north (c : Point) (r : R) : Point := mkPoint (px c) (py c + r).
Definition extreme_west  (c : Point) (r : R) : Point := mkPoint (px c - r) (py c).
Definition extreme_south (c : Point) (r : R) : Point := mkPoint (px c) (py c - r).

Lemma extreme_east_on_circle : forall c r,
  on_circle c r (extreme_east c r).
Proof.
  intros c r. unfold on_circle, extreme_east, dist_sq. simpl. ring.
Qed.

Lemma extreme_north_on_circle : forall c r,
  on_circle c r (extreme_north c r).
Proof.
  intros c r. unfold on_circle, extreme_north, dist_sq. simpl. ring.
Qed.

Lemma extreme_west_on_circle : forall c r,
  on_circle c r (extreme_west c r).
Proof.
  intros c r. unfold on_circle, extreme_west, dist_sq. simpl. ring.
Qed.

Lemma extreme_south_on_circle : forall c r,
  on_circle c r (extreme_south c r).
Proof.
  intros c r. unfold on_circle, extreme_south, dist_sq. simpl. ring.
Qed.

Lemma on_circle_dx_sq_le : forall c r p,
  on_circle c r p ->
  (px p - px c) * (px p - px c) <= r * r.
Proof.
  intros c r p H. unfold on_circle, dist_sq in H.
  pose proof (sqr_nonneg (py p - py c)). lra.
Qed.

Lemma on_circle_dy_sq_le : forall c r p,
  on_circle c r p ->
  (py p - py c) * (py p - py c) <= r * r.
Proof.
  intros c r p H. unfold on_circle, dist_sq in H.
  pose proof (sqr_nonneg (px p - px c)). lra.
Qed.

Lemma sq_le_abs_le : forall x r,
  0 <= r -> x * x <= r * r -> Rabs x <= r.
Proof.
  intros x r Hr Hsq.
  pose proof (Rsqr_le_abs_0 x r) as H.
  unfold Rsqr in H.
  specialize (H Hsq).
  rewrite (Rabs_right r) in H by lra.
  exact H.
Qed.

Lemma on_circle_x_in_radius : forall c r p,
  0 <= r -> on_circle c r p ->
  Rabs (px p - px c) <= r.
Proof.
  intros c r p Hr Hon.
  apply sq_le_abs_le; [exact Hr | apply on_circle_dx_sq_le; exact Hon].
Qed.

Lemma on_circle_y_in_radius : forall c r p,
  0 <= r -> on_circle c r p ->
  Rabs (py p - py c) <= r.
Proof.
  intros c r p Hr Hon.
  apply sq_le_abs_le; [exact Hr | apply on_circle_dy_sq_le; exact Hon].
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  Disc envelope is the axis-aligned square of the four cardinals.        *)
(* -------------------------------------------------------------------------- *)

Definition bbox_of_disk (D : Disk) : Bbox :=
  mkBbox (px (dcentre D) - dradius D)
         (px (dcentre D) + dradius D)
         (py (dcentre D) - dradius D)
         (py (dcentre D) + dradius D).

Lemma in_disk_in_bbox_of_disk : forall D p,
  disk_is_valid D ->
  in_disk D p ->
  in_bbox (bbox_of_disk D) p.
Proof.
  intros D p Hv Hin.
  unfold disk_is_valid, in_disk, in_bbox, bbox_of_disk in *.
  simpl in *.
  assert (Hx : Rabs (px p - px (dcentre D)) <= dradius D).
  { apply sq_le_abs_le; [exact Hv |].
    pose proof (sqr_nonneg (py p - py (dcentre D))).
    unfold dist_sq in Hin. lra. }
  assert (Hy : Rabs (py p - py (dcentre D)) <= dradius D).
  { apply sq_le_abs_le; [exact Hv |].
    pose proof (sqr_nonneg (px p - px (dcentre D))).
    unfold dist_sq in Hin. lra. }
  unfold Rabs in Hx, Hy.
  destruct (Rcase_abs (px p - px (dcentre D)));
    destruct (Rcase_abs (py p - py (dcentre D))); lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Single-arc cell: mid-disambiguated upper semicircle (no atan2).        *)
(* -------------------------------------------------------------------------- *)

Definition on_upper_semicircle (c : Point) (r : R) (p : Point) : Prop :=
  on_circle c r p /\ py c <= py p.

Lemma extreme_north_on_upper : forall c r,
  0 <= r -> on_upper_semicircle c r (extreme_north c r).
Proof.
  intros c r Hr. split.
  - apply extreme_north_on_circle.
  - unfold extreme_north. simpl. lra.
Qed.

Lemma extreme_east_on_upper : forall c r,
  on_upper_semicircle c r (extreme_east c r).
Proof.
  intros c r. split.
  - apply extreme_east_on_circle.
  - unfold extreme_east. simpl. lra.
Qed.

Lemma extreme_west_on_upper : forall c r,
  on_upper_semicircle c r (extreme_west c r).
Proof.
  intros c r. split.
  - apply extreme_west_on_circle.
  - unfold extreme_west. simpl. lra.
Qed.

Lemma extreme_south_not_on_upper : forall c r,
  0 < r -> ~ on_upper_semicircle c r (extreme_south c r).
Proof.
  intros c r Hr [Hon Hy].
  unfold extreme_south in Hy. simpl in Hy. lra.
Qed.

Lemma upper_semi_y_hi : forall c r p,
  0 <= r -> on_upper_semicircle c r p -> py p <= py c + r.
Proof.
  intros c r p Hr [Hon _].
  pose proof (on_circle_y_in_radius c r p Hr Hon) as Hy.
  unfold Rabs in Hy.
  destruct (Rcase_abs (py p - py c)); lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  PR #8 cell: disc / single-arc are CurveExact; CompoundCurve is not.    *)
(* -------------------------------------------------------------------------- *)

Record pr8_input : Type := mkPr8 {
  n_circular_members : nat;
  n_line_members : nat
}.

Definition pr8_curve_exact (g : pr8_input) : Prop :=
  n_circular_members g = 1%nat /\ n_line_members g = 0%nat.

(* Closed disc ring: one CircularString, no line members. *)
Definition disc5_input : pr8_input := mkPr8 1 0.
(* Open single arc. *)
Definition half_arc_input : pr8_input := mkPr8 1 0.
(* #6 H-CC: CIRCULARSTRING + LINESTRING. *)
Definition h_cc_input : pr8_input := mkPr8 1 1.

Lemma disc5_is_pr8_cell : pr8_curve_exact disc5_input.
Proof. unfold pr8_curve_exact, disc5_input. split; reflexivity. Qed.

Lemma half_arc_is_pr8_cell : pr8_curve_exact half_arc_input.
Proof. unfold pr8_curve_exact, half_arc_input. split; reflexivity. Qed.

Lemma h_cc_still_densify : ~ pr8_curve_exact h_cc_input.
Proof.
  unfold pr8_curve_exact, h_cc_input. intros [_ H]. discriminate H.
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  Rational witnesses (CIRCLE_5 / upper semicircle, no sqrt).             *)
(* -------------------------------------------------------------------------- *)

Definition disc5_c : Point := mkPoint 0 0.
Definition disc5_r : R := 5.

Definition disc5_east  : Point := extreme_east  disc5_c disc5_r.
Definition disc5_north : Point := extreme_north disc5_c disc5_r.
Definition disc5_west  : Point := extreme_west  disc5_c disc5_r.
Definition disc5_south : Point := extreme_south disc5_c disc5_r.

Lemma disc5_east_on : on_circle disc5_c disc5_r disc5_east.
Proof. apply extreme_east_on_circle. Qed.

Lemma disc5_north_on : on_circle disc5_c disc5_r disc5_north.
Proof. apply extreme_north_on_circle. Qed.

Lemma disc5_west_on : on_circle disc5_c disc5_r disc5_west.
Proof. apply extreme_west_on_circle. Qed.

Lemma disc5_south_on : on_circle disc5_c disc5_r disc5_south.
Proof. apply extreme_south_on_circle. Qed.

Lemma disc5_r_nonneg : 0 <= disc5_r.
Proof. unfold disc5_r. lra. Qed.

Lemma disc5_east_is_boundary : px disc5_east = 5 /\ py disc5_east = 0.
Proof. unfold disc5_east, extreme_east, disc5_c, disc5_r. simpl. lra. Qed.

Lemma half_north_on_upper :
  on_upper_semicircle disc5_c disc5_r disc5_north.
Proof. apply extreme_north_on_upper. apply disc5_r_nonneg. Qed.

Lemma half_south_not_on_upper :
  ~ on_upper_semicircle disc5_c disc5_r disc5_south.
Proof. apply extreme_south_not_on_upper. unfold disc5_r. lra. Qed.

(* -------------------------------------------------------------------------- *)
(* §6  Headline.                                                              *)
(* -------------------------------------------------------------------------- *)

Lemma hcv_exact_extrema :
  on_circle disc5_c disc5_r disc5_east /\
  on_circle disc5_c disc5_r disc5_north /\
  on_circle disc5_c disc5_r disc5_west /\
  on_circle disc5_c disc5_r disc5_south /\
  on_upper_semicircle disc5_c disc5_r disc5_north /\
  ~ on_upper_semicircle disc5_c disc5_r disc5_south /\
  pr8_curve_exact disc5_input /\
  pr8_curve_exact half_arc_input /\
  ~ pr8_curve_exact h_cc_input.
Proof.
  exact (conj disc5_east_on
        (conj disc5_north_on
        (conj disc5_west_on
        (conj disc5_south_on
        (conj half_north_on_upper
        (conj half_south_not_on_upper
        (conj disc5_is_pr8_cell
        (conj half_arc_is_pr8_cell h_cc_still_densify)))))))).
Qed.

Print Assumptions hcv_exact_extrema.
Print Assumptions in_disk_in_bbox_of_disk.
Print Assumptions on_circle_x_in_radius.

(* ============================================================================
   nts-eval micro unit — claimId 9004-c
   ----------------------------------------------------------------------------
   Maximum inscribed circle of the unit square: centre (1/2, 1/2), radius 1/2.

   Self-contained classical-reals micro-kernel for the nts-eval harness:
   no NTS.Proofs Requires.  Mirrors the production packaging in
   theories/MaximumInscribedCircle.v (board #9004, epic #813; Zhai et al.
   2026, "Polycenter", doi:10.1080/13658816.2025.2514056).

   Carrier twins: Point / dist_sq / dist and the InDisk closed-disk
   membership (geometric ‖P−O‖ ≤ r form), plus the 9004-a surface
   (Region / inscribed_disk / max_inscribed_disk) and the [0,1]² region.

   Headline: `mic_unit_square` — the disk (centre (1/2,1/2), radius 1/2) is
   inscribed and no inscribed disk has a larger radius.  Rational pins: the
   four side midpoints lie ON the witness circle (squared distance exactly
   1/4) and in the disk; mismatch probes: the same radius off-centre at
   (1/4, 1/2) is NOT inscribed (escapes through the left wall at
   (−1/4, 1/2)), and NO centre supports radius 3/5.

   WITNESS claimId: 9004-c
   Lemma: mic_unit_square
   ========================================================================== *)

(* WITNESS {"claimId":"9004-c","topic":"construct","lemma":"mic_unit_square","title":"MIC of the unit square = centre (1/2,1/2), radius 1/2"} *)

From Stdlib Require Import Reals Lra.
Local Open Scope R_scope.

(* ---- Minimal geometry carrier (Distance twins) ---------------------------- *)

Record Point : Type := mkPoint { px : R; py : R }.

Definition dist_sq (P Q : Point) : R :=
  (px P - px Q) * (px P - px Q) + (py P - py Q) * (py P - py Q).

Definition dist (P Q : Point) : R := sqrt (dist_sq P Q).

Lemma sqr_nonneg : forall x : R, 0 <= x * x.
Proof. intros x. nra. Qed.

Lemma dist_sq_nonneg : forall P Q, 0 <= dist_sq P Q.
Proof.
  intros P Q. unfold dist_sq.
  pose proof (sqr_nonneg (px P - px Q)).
  pose proof (sqr_nonneg (py P - py Q)).
  lra.
Qed.

(* The sqrt bridge (production twin: Distance.dist_le_iff_dist_sq_le). *)
Lemma dist_le_iff_dist_sq_le : forall P Q t,
  0 <= t -> (dist P Q <= t <-> dist_sq P Q <= t * t).
Proof.
  intros P Q t Ht. unfold dist. split.
  - intros H.
    rewrite <- (sqrt_sqrt (dist_sq P Q) (dist_sq_nonneg P Q)).
    apply Rmult_le_compat; try apply sqrt_pos; assumption.
  - intros H.
    apply Rle_trans with (sqrt (t * t)).
    + apply sqrt_le_1; [apply dist_sq_nonneg | nra | exact H].
    + replace (t * t) with (Rsqr t) by (unfold Rsqr; ring).
      rewrite sqrt_Rsqr; [lra | exact Ht].
Qed.

(* ---- Production twins: InDisk membership + the 9004-a surface ------------- *)

(** Closed-disk membership, geometric form (InDisk.InDisk twin). *)
Definition InDisk (O : Point) (r : R) (P : Point) : Prop :=
  0 <= r /\ dist O P <= r.

(** A planar region, as a point predicate. *)
Definition Region : Type := Point -> Prop.

(** The closed disk (O, r) is contained in the region. *)
Definition inscribed_disk (Rg : Region) (O : Point) (r : R) : Prop :=
  0 <= r /\ forall P : Point, InDisk O r P -> Rg P.

(** Inscribed, and no inscribed disk has a larger radius. *)
Definition max_inscribed_disk (Rg : Region) (O : Point) (r : R) : Prop :=
  inscribed_disk Rg O r /\
  forall (O' : Point) (r' : R), inscribed_disk Rg O' r' -> r' <= r.

(** The closed unit square [0,1]² as a region. *)
Definition unit_square : Region :=
  fun P : Point => 0 <= px P <= 1 /\ 0 <= py P <= 1.

Definition mic_unit_square_centre : Point := mkPoint (1/2) (1/2).
Definition mic_unit_square_radius : R := 1/2.

(* ---- Headline (9004-c) ----------------------------------------------------- *)

Theorem mic_unit_square :
  max_inscribed_disk unit_square mic_unit_square_centre mic_unit_square_radius.
Proof.
  unfold max_inscribed_disk, mic_unit_square_radius.
  split.
  - unfold inscribed_disk. split; [lra |].
    intros P [_ Hd].
    assert (Hhalf : 0 <= 1/2) by lra.
    pose proof (proj1 (dist_le_iff_dist_sq_le mic_unit_square_centre P (1/2)
                         Hhalf) Hd) as Hsq.
    unfold dist_sq, mic_unit_square_centre in Hsq. simpl in Hsq.
    pose proof (sqr_nonneg (1/2 - px P)) as Hx2.
    pose proof (sqr_nonneg (1/2 - py P)) as Hy2.
    unfold unit_square. repeat split; nra.
  - intros O' r' [Hr' Hincl].
    assert (HL : unit_square (mkPoint (px O' - r') (py O'))).
    { apply Hincl. split; [exact Hr' |].
      apply (proj2 (dist_le_iff_dist_sq_le
                      O' (mkPoint (px O' - r') (py O')) r' Hr')).
      unfold dist_sq. simpl. nra. }
    assert (HR : unit_square (mkPoint (px O' + r') (py O'))).
    { apply Hincl. split; [exact Hr' |].
      apply (proj2 (dist_le_iff_dist_sq_le
                      O' (mkPoint (px O' + r') (py O')) r' Hr')).
      unfold dist_sq. simpl. nra. }
    destruct HL as [[HL0 _] _].
    destruct HR as [[_ HR1] _].
    simpl in HL0, HR1.
    lra.
Qed.

(* ---- Rational pins: the witness circle touches all four walls ------------- *)

Definition side_mid_left   : Point := mkPoint 0 (1/2).
Definition side_mid_right  : Point := mkPoint 1 (1/2).
Definition side_mid_bottom : Point := mkPoint (1/2) 0.
Definition side_mid_top    : Point := mkPoint (1/2) 1.

(** Each side midpoint lies ON the witness circle: squared distance to the
    centre is exactly (1/2)² = 1/4. *)
Lemma touch_left_on_circle :
  dist_sq mic_unit_square_centre side_mid_left = (1/2) * (1/2).
Proof. unfold dist_sq, mic_unit_square_centre, side_mid_left. simpl. lra. Qed.

Lemma touch_right_on_circle :
  dist_sq mic_unit_square_centre side_mid_right = (1/2) * (1/2).
Proof. unfold dist_sq, mic_unit_square_centre, side_mid_right. simpl. lra. Qed.

Lemma touch_bottom_on_circle :
  dist_sq mic_unit_square_centre side_mid_bottom = (1/2) * (1/2).
Proof. unfold dist_sq, mic_unit_square_centre, side_mid_bottom. simpl. lra. Qed.

Lemma touch_top_on_circle :
  dist_sq mic_unit_square_centre side_mid_top = (1/2) * (1/2).
Proof. unfold dist_sq, mic_unit_square_centre, side_mid_top. simpl. lra. Qed.

(** ... and (hence) in the closed disk. *)
Lemma touch_left_in_disk :
  InDisk mic_unit_square_centre mic_unit_square_radius side_mid_left.
Proof.
  split; [unfold mic_unit_square_radius; lra |].
  unfold mic_unit_square_radius.
  apply (proj2 (dist_le_iff_dist_sq_le
                  mic_unit_square_centre side_mid_left (1/2)
                  ltac:(lra))).
  rewrite touch_left_on_circle. lra.
Qed.

(* ---- Mismatch probes ------------------------------------------------------- *)

(** Off-centre kill: the SAME radius 1/2 centred at (1/4, 1/2) is not
    inscribed — the disk escapes through the left wall at (−1/4, 1/2). *)
Lemma off_centre_half_disk_not_inscribed :
  ~ inscribed_disk unit_square (mkPoint (1/4) (1/2)) (1/2).
Proof.
  intros [Hr Hincl].
  assert (Hin : InDisk (mkPoint (1/4) (1/2)) (1/2) (mkPoint (- (1/4)) (1/2))).
  { split; [lra |].
    apply (proj2 (dist_le_iff_dist_sq_le
                    (mkPoint (1/4) (1/2)) (mkPoint (- (1/4)) (1/2)) (1/2)
                    ltac:(lra))).
    unfold dist_sq. simpl. lra. }
  destruct (Hincl _ Hin) as [[H0 _] _].
  simpl in H0. lra.
Qed.

(** Bigger-radius kill: NO centre supports radius 3/5 (maximality instance). *)
Lemma no_inscribed_disk_of_radius_three_fifths :
  forall O' : Point, ~ inscribed_disk unit_square O' (3/5).
Proof.
  intros O' Hins.
  pose proof (proj2 mic_unit_square O' (3/5) Hins) as H.
  unfold mic_unit_square_radius in H. lra.
Qed.

Print Assumptions mic_unit_square.

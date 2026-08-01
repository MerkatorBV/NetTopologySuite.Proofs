(* ============================================================================
   NetTopologySuite.Proofs.InDisk
   ----------------------------------------------------------------------------
   Issue #64 subtask 64-d — GREEN: closed-disk membership on the supporting
   circle of a circular arc.

   `InDisk O r P` is geometric closed-disk membership (‖P−O‖ ≤ r with r ≥ 0).
   `InDisk_supporting_circle a P` specialises it at the orientation-stable
   supporting circle `(arc_center a, arc_radius a)`.  The rational unit-arc
   witness closes every headline with `Qed` (no Abort, no Admitted):

     a = CircularArc (1,0) → (0,1) → (−1,0)
       ⇒ arc_center a = (0,0), arc_radius a = 1
     P_int  = (0, 1/2)    strict interior (‖P‖ = 1/2 < 1)
     P_bdry = (3/5, 4/5)  on boundary (3-4-5; ‖P‖² = 1)
     P_ext  = (2, 0)      exterior rejected (‖P‖ = 2 > 1)
     P_ctr  = (0, 0)      centre (strict interior; ‖P‖ = 0 < 1)

   Geometric ↔ squared-radius equivalence
     (px−ox)² + (py−oy)² ≤ r²
   is `in_disk_iff_squared_radius`, citing `dist_le_iff_dist_sq_le`.
   Agreement with `Disk.in_disk` on `supporting_disk a` is
   `in_disk_supporting_circle_iff_disk_in_disk`.

   3-axiom classical-reals footprint (Distance / CurveGeometry / Disk;
   no atan2 / classic lineage).  No Admitted.

   Refs: issue #64, docs/issue-64-arc-primitives-triage.md (ask #4 / in-circle
   disk membership; sibling of 64-c InArc).
   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Grok (grok-4.5)
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import Distance CurveGeometry Disk.

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  InDisk / InDisk_supporting_circle — closed-disk membership on the      *)
(*     supporting circle of a circular arc.                                   *)
(* -------------------------------------------------------------------------- *)

(** [InDisk O r P]: [P] lies in the closed disk of centre [O] and radius [r].

    Geometric form (classical Euclidean norm via [dist]):
      [0 ≤ r] and [dist O P ≤ r], i.e. ‖P − O‖ ≤ r.

    Distinct from [Disk.in_disk], which is the *squared-radius* form on a
    [Disk] record.  The two agree by [in_disk_iff_squared_radius]. *)
Definition InDisk (O : Point) (r : R) (P : Point) : Prop :=
  0 <= r /\ dist O P <= r.

(** Squared-radius comparison form of closed-disk membership (matches the
    body of [Disk.in_disk] once [0 ≤ r] is packaged). *)
Definition InDisk_sq (O : Point) (r : R) (P : Point) : Prop :=
  0 <= r /\ dist_sq O P <= r * r.

(** Supporting disk of arc [a]: the closed disk of the unique circle through
    the three control points ([arc_center], [arc_radius]). *)
Definition supporting_disk (a : CircularArc) : Disk :=
  mkDisk (arc_center a) (arc_radius a).

(** [InDisk_supporting_circle a P]: [P] lies in the closed disk of the
    supporting circle of arc [a].

    Geometric packaging of ‖P − arc_center a‖ ≤ arc_radius a. *)
Definition InDisk_supporting_circle (a : CircularArc) (P : Point) : Prop :=
  InDisk (arc_center a) (arc_radius a) P.

(* -------------------------------------------------------------------------- *)
(* §2  Rational unit supporting-circle witness (concrete valid arc).          *)
(* -------------------------------------------------------------------------- *)

(** Unit semicircle through (1,0), (0,1), (−1,0): supporting circle is the
    unit circle centred at the origin. *)
Definition disk_unit_arc : CircularArc :=
  mkCircularArc (mkPoint 1 0) (mkPoint 0 1) (mkPoint (-1) 0).

(** Strict interior test point (rational coords). *)
Definition disk_P_interior : Point := mkPoint 0 (1/2).
(** Boundary test point (3-4-5 rational on the unit circle). *)
Definition disk_P_boundary : Point := mkPoint (3/5) (4/5).
(** Exterior counter-position. *)
Definition disk_P_exterior : Point := mkPoint 2 0.
(** Centre-as-interior point. *)
Definition disk_P_centre : Point := mkPoint 0 0.

Lemma disk_P_interior_dist_sq_origin :
  dist_sq (mkPoint 0 0) disk_P_interior = 1/4.
Proof.
  unfold disk_P_interior, dist_sq; cbn [px py]. field.
Qed.

Lemma disk_P_boundary_dist_sq_origin :
  dist_sq (mkPoint 0 0) disk_P_boundary = 1.
Proof.
  unfold disk_P_boundary, dist_sq; cbn [px py]. field.
Qed.

Lemma disk_P_exterior_dist_sq_origin :
  dist_sq (mkPoint 0 0) disk_P_exterior = 4.
Proof.
  unfold disk_P_exterior, dist_sq; cbn [px py]. lra.
Qed.

Lemma disk_P_centre_dist_sq_origin :
  dist_sq (mkPoint 0 0) disk_P_centre = 0.
Proof.
  unfold disk_P_centre, dist_sq; cbn [px py]. lra.
Qed.

Lemma disk_P_interior_dist_sq_lt_one :
  dist_sq (mkPoint 0 0) disk_P_interior < 1.
Proof.
  rewrite disk_P_interior_dist_sq_origin. lra.
Qed.

Lemma disk_P_boundary_dist_sq_eq_one :
  dist_sq (mkPoint 0 0) disk_P_boundary = 1.
Proof. exact disk_P_boundary_dist_sq_origin. Qed.

Lemma disk_P_exterior_dist_sq_gt_one :
  1 < dist_sq (mkPoint 0 0) disk_P_exterior.
Proof.
  rewrite disk_P_exterior_dist_sq_origin. lra.
Qed.

Lemma disk_P_centre_dist_sq_lt_one :
  dist_sq (mkPoint 0 0) disk_P_centre < 1.
Proof.
  rewrite disk_P_centre_dist_sq_origin. lra.
Qed.

Lemma disk_unit_arc_valid : valid_arc disk_unit_arc.
Proof.
  unfold valid_arc, disk_unit_arc; cbn [arc_start arc_mid arc_end px py].
  (* v1 = (−1, 1), v2 = (−2, 0); cross = (−1)·0 − 1·(−2) = 2 ≠ 0 *)
  lra.
Qed.

Lemma arc_radius_nonneg : forall a : CircularArc, 0 <= arc_radius a.
Proof.
  intros a. unfold arc_radius. apply dist_nonneg.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Headlines — fully Qed.                                                 *)
(* -------------------------------------------------------------------------- *)

(** Geometric closed-disk membership is equivalent to the squared-radius
    comparison over classical reals. *)
Theorem in_disk_iff_squared_radius :
  forall (O : Point) (r : R) (P : Point),
    InDisk O r P <-> InDisk_sq O r P.
Proof.
  intros O r P. unfold InDisk, InDisk_sq. split.
  - intros [Hr Hdist]. split; [exact Hr|].
    apply (proj1 (dist_le_iff_dist_sq_le O P r Hr)). exact Hdist.
  - intros [Hr Hsq]. split; [exact Hr|].
    apply (proj2 (dist_le_iff_dist_sq_le O P r Hr)). exact Hsq.
Qed.

(** [InDisk_supporting_circle] agrees with [Disk.in_disk] on the supporting
    disk of any arc (geometric vs squared packaging). *)
Theorem in_disk_supporting_circle_iff_disk_in_disk :
  forall (a : CircularArc) (P : Point),
    InDisk_supporting_circle a P
    <-> in_disk (supporting_disk a) P.
Proof.
  intros a P.
  unfold InDisk_supporting_circle, supporting_disk, in_disk; cbn [dcentre dradius].
  pose proof (arc_radius_nonneg a) as Hr.
  split.
  - intros Hindisk.
    destruct (proj1 (in_disk_iff_squared_radius (arc_center a) (arc_radius a) P)
                      Hindisk) as [_ Hsq].
    exact Hsq.
  - intros Hsq.
    apply (proj2 (in_disk_iff_squared_radius (arc_center a) (arc_radius a) P)).
    split; [exact Hr | exact Hsq].
Qed.

(** Unit-arc witness: supporting circle is the unit circle at the origin. *)
Theorem disk_unit_arc_supporting_circle :
  arc_center disk_unit_arc = mkPoint 0 0
  /\ arc_radius disk_unit_arc = 1.
Proof.
  assert (Hc : arc_center disk_unit_arc = mkPoint 0 0).
  { unfold arc_center, disk_unit_arc; cbn [arc_start arc_mid arc_end px py].
    f_equal; field. }
  split; [exact Hc|].
  unfold arc_radius. rewrite Hc.
  unfold dist.
  assert (Hds : dist_sq (mkPoint 0 0) (arc_start disk_unit_arc) = 1).
  { unfold dist_sq, disk_unit_arc; cbn [arc_start px py]. ring. }
  rewrite Hds. exact sqrt_1.
Qed.

(** Strict-interior rational point satisfies [InDisk_supporting_circle].
    Witness: [disk_P_interior] = (0, 1/2). *)
Theorem in_disk_supporting_circle_strict_interior_witness :
  InDisk_supporting_circle disk_unit_arc disk_P_interior.
Proof.
  unfold InDisk_supporting_circle.
  destruct disk_unit_arc_supporting_circle as [Hc Hr].
  rewrite Hc, Hr.
  unfold InDisk.
  split; [lra|].
  apply (proj2 (dist_le_iff_dist_sq_le (mkPoint 0 0) disk_P_interior 1 ltac:(lra))).
  rewrite disk_P_interior_dist_sq_origin. lra.
Qed.

(** Boundary 3-4-5 rational point satisfies [InDisk_supporting_circle]
    (closed disk includes the circumference).
    Witness: [disk_P_boundary]. *)
Theorem in_disk_supporting_circle_boundary_witness :
  InDisk_supporting_circle disk_unit_arc disk_P_boundary.
Proof.
  unfold InDisk_supporting_circle.
  destruct disk_unit_arc_supporting_circle as [Hc Hr].
  rewrite Hc, Hr.
  unfold InDisk.
  split; [lra|].
  apply (proj2 (dist_le_iff_dist_sq_le (mkPoint 0 0) disk_P_boundary 1 ltac:(lra))).
  rewrite disk_P_boundary_dist_sq_origin. lra.
Qed.

(** Supporting-circle centre satisfies [InDisk_supporting_circle]
    (strict interior).  Witness: [disk_P_centre] = (0, 0). *)
Theorem in_disk_supporting_circle_centre_witness :
  InDisk_supporting_circle disk_unit_arc disk_P_centre.
Proof.
  unfold InDisk_supporting_circle.
  destruct disk_unit_arc_supporting_circle as [Hc Hr].
  rewrite Hc, Hr.
  unfold InDisk.
  split; [lra|].
  apply (proj2 (dist_le_iff_dist_sq_le (mkPoint 0 0) disk_P_centre 1 ltac:(lra))).
  rewrite disk_P_centre_dist_sq_origin. lra.
Qed.

(** Exterior rational point does not satisfy [InDisk_supporting_circle]
    for the unit arc.  Witness: [disk_P_exterior] = (2, 0). *)
Theorem in_disk_supporting_circle_exterior_rejected :
  ~ InDisk_supporting_circle disk_unit_arc disk_P_exterior.
Proof.
  unfold InDisk_supporting_circle.
  destruct disk_unit_arc_supporting_circle as [Hc Hr].
  rewrite Hc, Hr.
  unfold InDisk.
  intros [_ Hdist].
  pose proof (proj1 (dist_le_iff_dist_sq_le (mkPoint 0 0) disk_P_exterior 1
                       ltac:(lra)) Hdist) as Hsq.
  rewrite disk_P_exterior_dist_sq_origin in Hsq.
  lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Audit footprint.                                                       *)
(* -------------------------------------------------------------------------- *)

Print Assumptions in_disk_iff_squared_radius.
Print Assumptions in_disk_supporting_circle_iff_disk_in_disk.
Print Assumptions disk_unit_arc_supporting_circle.
Print Assumptions in_disk_supporting_circle_strict_interior_witness.
Print Assumptions in_disk_supporting_circle_boundary_witness.
Print Assumptions in_disk_supporting_circle_centre_witness.
Print Assumptions in_disk_supporting_circle_exterior_rejected.

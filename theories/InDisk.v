(* ============================================================================
   NetTopologySuite.Proofs.InDisk
   ----------------------------------------------------------------------------
   Issue #64 subtask 64-d — RED surface only: disk membership on the
   supporting circle of a circular arc.

   WHAT THIS FILE IS.  The smallest failing claim for "point in the closed
   disk of the arc's supporting circle", with a rational unit-circle witness.
   Green / Refactor are out of scope: no production body that closes the
   goal, no `Admitted` as a fake green.  Open goals end with `Abort` (same
   discipline as HobbyTheorem_b64 / B64_FastExpansionSum / InArc Red —
   an Aborted claim is not `apply`-able and cannot silently poison consumers).

   WHAT IS MISSING ON MAIN (why the focused check fails without Green).
   There is no named disk-membership predicate specialising the supporting
   circle of a `CircularArc` (`arc_center` / `arc_radius`).  Existing pieces
   are related but not this surface:
     - `Disk.in_disk` / `Disk.in_disk_iff` — generic closed disks, not the
       arc supporting-circle packaging or the rational arc witness below;
     - `inCircle_R` (ArcOrient) — algebraic in-circle *determinant* (side of
       the circumcircle of three defining points), not closed-disk membership
       of a point vs a fixed centre/radius;
     - inline `dist_sq (arc_center a) P <= dist_sq (arc_center a) (arc_start a)`
       in `ArcControlTriangleInSegment.in_circular_segment` — a local
       conjunct of the circular-segment region, not a reusable
       `InDisk_supporting_circle` primitive with a proved geometric ↔
       squared-radius equivalence under the supporting-circle reading;
     - `dist_le_iff_dist_sq_le` (Distance) — the generic non-negative
       threshold fact Green will cite; it does not package supporting-circle
       disk membership or the rational witness claims below.
   `InArc` (64-c) is on-circle minor-arc membership, not disk membership.

   INTENDED PREDICATE (spec shape for Green).  For supporting circle C of
   arc [a] with centre [o = arc_center a] and radius [r = arc_radius a]
   (orientation-stable from prior #64 rungs), a point [p] satisfies disk
   membership iff ‖p − o‖ ≤ r.  The Red definition packages the geometric
   form (`dist O P ≤ r`); Green Qeds the rational witnesses and the
   equivalence to the squared-radius comparison
     (px−ox)² + (py−oy)² ≤ r²
   over classical reals, reusing `Disk.in_disk` / `dist_le_iff_dist_sq_le`
   where appropriate.  Operator Eval → Qed via nts-eval micro-kernel is
   required for the Green close.

   RATIONAL WITNESS (unit supporting circle via a concrete valid arc).
     a = CircularArc (1,0) → (0,1) → (−1,0)
       ⇒ arc_center a = (0,0), arc_radius a = 1  (Green discharges)
     P_int  = (0, 1/2)    strict interior (‖P‖ = 1/2 < 1)
     P_bdry = (3/5, 4/5)  on boundary (3-4-5; ‖P‖² = 1)
     P_ext  = (2, 0)      exterior (‖P‖ = 2 > 1)
     P_ctr  = (0, 0)      centre (strict interior; ‖P‖ = 0 < 1)

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
(*                                                                            *)
(* Spec shape only.  Green is authorised to refine the boundary convention    *)
(* (closed vs open disk) if a consumer needs the open interior; the Red       *)
(* claims are the closed-disk rational witnesses below.                       *)
(* -------------------------------------------------------------------------- *)

(** [InDisk O r P]: [P] lies in the closed disk of centre [O] and radius [r].

    Geometric form (classical Euclidean norm via [dist]):
      [0 ≤ r] and [dist O P ≤ r], i.e. ‖P − O‖ ≤ r.

    Distinct from [Disk.in_disk], which is the *squared-radius* form on a
    [Disk] record.  Green proves the two agree (see
    [in_disk_iff_squared_radius] below). *)
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

    Geometric packaging of ‖P − arc_center a‖ ≤ arc_radius a.
    RED: stated for typechecking and the failing claims; the rational
    witness is not discharged here.  Green specialises [InDisk] at
    [(arc_center a, arc_radius a)] and Qeds the witness headlines. *)
Definition InDisk_supporting_circle (a : CircularArc) (P : Point) : Prop :=
  InDisk (arc_center a) (arc_radius a) P.

(* -------------------------------------------------------------------------- *)
(* §2  Rational unit supporting-circle witness (concrete valid arc).          *)
(* -------------------------------------------------------------------------- *)

(** Unit semicircle through (1,0), (0,1), (−1,0): supporting circle is the
    unit circle centred at the origin (Green discharges centre/radius). *)
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

(* Geometric scaffolding for the witness points — Qed.  Does not mention
   InDisk / arc_center, so it cannot accidentally close the Red claims. *)

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

(* Control-point collinearity check for the unit arc — Qed scaffolding.
   Does not mention InDisk. *)
Lemma disk_unit_arc_valid : valid_arc disk_unit_arc.
Proof.
  unfold valid_arc, disk_unit_arc; cbn [arc_start arc_mid arc_end px py].
  (* v1 = (−1, 1), v2 = (−2, 0); cross = (−1)·0 − 1·(−2) = 2 ≠ 0 *)
  lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Focused Red claims — open, not Admitted.                               *)
(*                                                                            *)
(* These are the surface Eval / nts-eval will re-check after Green is          *)
(* authorised.  Until then they remain Abort: neither closed nor disproven.   *)
(* -------------------------------------------------------------------------- *)

(** RED (64-d): geometric closed-disk membership is equivalent to the
    squared-radius comparison over classical reals.
    Green closes via [dist_le_iff_dist_sq_le] / [Disk.in_disk_iff], packaging
    the supporting-circle reading. *)
Theorem in_disk_iff_squared_radius :
  forall (O : Point) (r : R) (P : Point),
    InDisk O r P <-> InDisk_sq O r P.
Proof.
  (* RED #64-d: Green closes the geometric ↔ squared-radius equivalence.
     Do not Admitted — that would be a fake green. *)
Abort.

(** RED (64-d): [InDisk_supporting_circle] agrees with [Disk.in_disk] on the
    supporting disk of any arc (geometric vs squared packaging). *)
Theorem in_disk_supporting_circle_iff_disk_in_disk :
  forall (a : CircularArc) (P : Point),
    InDisk_supporting_circle a P
    <-> in_disk (supporting_disk a) P.
Proof.
  (* RED #64-d: Green closes once arc_radius non-negativity and
     in_disk_iff_squared_radius are in hand.  Do not Admitted. *)
Abort.

(** RED (64-d): the unit-arc witness has supporting circle centre origin and
    radius 1.  Green discharges the circumcentre algebra of [arc_center]. *)
Theorem disk_unit_arc_supporting_circle :
  arc_center disk_unit_arc = mkPoint 0 0
  /\ arc_radius disk_unit_arc = 1.
Proof.
  (* RED #64-d: Green closes the orientation-stable supporting-circle data
     for the rational unit arc.  Do not Admitted. *)
Abort.

(** RED (64-d): a strict-interior rational point satisfies
    [InDisk_supporting_circle] for the unit arc.
    Witness: [disk_P_interior] = (0, 1/2). *)
Theorem in_disk_supporting_circle_strict_interior_witness :
  InDisk_supporting_circle disk_unit_arc disk_P_interior.
Proof.
  (* RED #64-d: Green closes once supporting-circle data + geometric
     membership are discharged (‖(0,1/2)‖ = 1/2 ≤ 1).  Do not Admitted. *)
Abort.

(** RED (64-d): a boundary 3-4-5 rational point satisfies
    [InDisk_supporting_circle] (closed disk includes the circumference).
    Witness: [disk_P_boundary]. *)
Theorem in_disk_supporting_circle_boundary_witness :
  InDisk_supporting_circle disk_unit_arc disk_P_boundary.
Proof.
  (* RED #64-d: Green closes (‖(3/5,4/5)‖ = 1 ≤ 1).  Do not Admitted. *)
Abort.

(** RED (64-d): the supporting-circle centre satisfies
    [InDisk_supporting_circle] (strict interior).
    Witness: [disk_P_centre] = (0, 0). *)
Theorem in_disk_supporting_circle_centre_witness :
  InDisk_supporting_circle disk_unit_arc disk_P_centre.
Proof.
  (* RED #64-d: Green closes (‖(0,0)‖ = 0 ≤ 1).  Do not Admitted. *)
Abort.

(** RED counter-position (64-d): an exterior rational point does not satisfy
    [InDisk_supporting_circle] for the unit arc.
    Witness: [disk_P_exterior] = (2, 0). *)
Theorem in_disk_supporting_circle_exterior_rejected :
  ~ InDisk_supporting_circle disk_unit_arc disk_P_exterior.
Proof.
  (* RED #64-d: Green closes the rejection (‖(2,0)‖ = 2 > 1).
     Do not Admitted. *)
Abort.

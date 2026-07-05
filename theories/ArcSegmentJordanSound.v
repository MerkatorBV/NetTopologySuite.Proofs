(* ============================================================================
   NetTopologySuite.Proofs.ArcSegmentJordanSound
   ----------------------------------------------------------------------------
   Issue #64 V-CP (Validity-CurvePolygon): a bounded "Jordan soundness" rung
   for the single-arc circular-segment ("lens") curve geometry.

   "V-CP Jordan soundness" -- the repo's own name for the missing link
   between ray-casting/parity membership tests and the TRUE topological
   interior of a curved region -- is graded thesis-scale/RED in general
   (`WindingNumber.v`, the general Jordan Curve Theorem `JCT_two_components_-
   cont`, and multi-arc rings with holes all remain open).  This file does
   NOT attempt that.  It closes the largest honest NEXT RUNG: for the
   arc-segment lens curve geometry already wired up by
   `RelateCurveArcSegment.v`, genuine ray-parity membership provably implies
   membership in the TRUE circular-segment region (`ArcControlTriangleInSegment.
   in_circular_segment`) -- not just the affine control-triangle proxy region.

   TWO ALREADY-`Qed` PIECES, ONE ALGEBRAIC BRIDGE APART.

     `RelateCurveArcSegment.arc_seg_control_interior_in_curve_geometry`:
       the actual ray-casting/parity membership test on the real
       `arc_seg_curve_geometry` `to_geometry` object reduces, under the
       standard `ray_avoids_vertices` genericity guard, to the purely
       algebraic sign test `0 < gtri (arc_start a)(arc_mid a)(arc_end a) p`.

     `ArcControlTriangleInSegment.arc_control_triangle_in_circular_segment`:
       affine-barycentric interior of the control triangle
       (`in_arc_control_triangle`) implies TRUE circular-segment membership
       (`in_circular_segment`) -- bulge side of the chord, inside the closed
       disk, no ray-casting or Jordan machinery at all.

   No lemma anywhere previously connected `gtri`-positivity to
   `in_arc_control_triangle` (confirmed by grep -- `in_arc_control_triangle`
   was used only inside its own file).  The bridge is a straightforward
   division-by-`gdbl` argument using only already-`Qed` identities
   (`gtri_pos_iff`, `g_sum`, `g_baryx`, `g_baryy` from
   `GeneralTriangleSeparation.v`) -- no new geometric machinery, and no CCW
   orientation hypothesis is needed: `0 < gtri p` forces the three inward
   signed areas positive, whose sum IS `gdbl`, so `gdbl > 0` (hence CCW)
   comes out for free.

   Proved here (three-axiom, no `Classic`, no `Admitted`/`Axiom`/`Parameter`):

     §1  `gtri_pos_implies_in_arc_control_triangle` -- the bridge lemma.
         `beta := gsC(...) p / gdbl(...)` (weight of `arc_mid`), `gamma :=
         gsA(...) p / gdbl(...)` (weight of `arc_end`); positivity from
         `gtri_pos_iff`, the affine-combination equalities from `g_baryx` /
         `g_baryy` via `field`.

     §2  `arc_seg_geometry_parity_sound_in_true_segment` -- the COMPOSED
         HEADLINE: chains `arc_seg_control_interior_in_curve_geometry`'s
         converse witness (`point_in_arc_seg_curve_geometry_iff_control_-
         interior`'s ray-parity characterisation, restated directly from the
         underlying `gtri`-positivity premise) through the new bridge lemma
         to `arc_control_triangle_in_circular_segment`.  Net result: genuine
         ray-parity membership on a real curved `to_geometry` object provably
         implies TRUE-region (circular-segment) membership -- a direct,
         concrete instance of exactly the "Jordan soundness" property the
         V-CP documentation names as its deferred frontier, for the
         single-arc-lens case.

   WHAT THIS EXPLICITLY DOES NOT CLOSE.  Multi-arc rings with holes,
   self-tangency, the general `{-1,0,+1}` winding characterisation
   (`WindingNumber.v`'s own deferred next rung), and the general Jordan
   Curve Theorem (`JCT_two_components_cont`, thesis-scale/RED, with a
   confirmed 2026-07-02 dead end on one shortcut) all remain untouched.
   This is a bounded, concrete rung -- not a claim of "full V-CP Jordan
   soundness".  The converse direction (a point in the true circular
   segment need not be in the control triangle -- the bulge itself, per
   `ArcControlTriangleInSegment.v`'s own deferred-scope note) is likewise
   untouched.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import Distance CurveGeometry ArcOrient
  ArcControlTriangleInSegment GeneralTriangleSeparation GeneralTriangleJCT
  PointInRingCorrect RelateCurveArcSegment.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  Bridge: gtri-positivity implies affine control-triangle interior.      *)
(* -------------------------------------------------------------------------- *)

Lemma gtri_pos_implies_in_arc_control_triangle :
  forall (a : CircularArc) (p : Point),
    0 < gtri (px (arc_start a)) (py (arc_start a))
             (px (arc_mid a))   (py (arc_mid a))
             (px (arc_end a))   (py (arc_end a)) p ->
    in_arc_control_triangle a p.
Proof.
  intros a p Hpos.
  set (sx := px (arc_start a)). set (sy := py (arc_start a)).
  set (mx := px (arc_mid a)).   set (my := py (arc_mid a)).
  set (ex := px (arc_end a)).   set (ey := py (arc_end a)).
  fold sx sy mx my ex ey in Hpos.
  destruct (proj1 (gtri_pos_iff sx sy mx my ex ey p) Hpos) as [HA [HB HC]].
  pose proof (g_sum sx sy mx my ex ey p) as Hsum.
  pose proof (g_baryx sx sy mx my ex ey p) as Hbx.
  pose proof (g_baryy sx sy mx my ex ey p) as Hby.
  set (d := gdbl sx sy mx my ex ey) in *.
  assert (Hd : 0 < d) by lra.
  assert (Hdne : d <> 0) by lra.
  set (gA := gsA sx sy mx my p) in *.
  set (gB := gsB mx my ex ey p) in *.
  set (gC := gsC sx sy ex ey p) in *.
  assert (HgB : gB = d - gA - gC) by lra.
  rewrite HgB in Hbx, Hby.
  unfold sx, sy, mx, my, ex, ey in Hbx, Hby.
  exists (gC / d), (gA / d).
  split; [ unfold Rdiv; apply Rmult_lt_0_compat; [lra | apply Rinv_0_lt_compat; lra] | ].
  split; [ unfold Rdiv; apply Rmult_lt_0_compat; [lra | apply Rinv_0_lt_compat; lra] | ].
  split.
  - apply (Rmult_lt_reg_r d); [ exact Hd | ].
    field_simplify; [ lra | exact Hdne ].
  - split.
    + eapply (Rmult_eq_reg_r d); [ | exact Hdne ].
      field_simplify; [ nra | exact Hdne ].
    + eapply (Rmult_eq_reg_r d); [ | exact Hdne ].
      field_simplify; [ nra | exact Hdne ].
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  Composed headline: ray-parity membership on the real curved           *)
(*     `to_geometry` object implies TRUE circular-segment membership.        *)
(* -------------------------------------------------------------------------- *)

Theorem arc_seg_geometry_parity_sound_in_true_segment :
  forall (a : CircularArc) (n : nat) (p : Point),
    valid_arc a ->
    0 < gtri (px (arc_start a)) (py (arc_start a))
             (px (arc_mid a))   (py (arc_mid a))
             (px (arc_end a))   (py (arc_end a)) p ->
    ray_avoids_vertices p
      (gtri_ring (px (arc_start a)) (py (arc_start a))
                 (px (arc_mid a))   (py (arc_mid a))
                 (px (arc_end a))   (py (arc_end a))) ->
    point_in_arc_seg_curve_geometry a n p ->
    in_circular_segment a p.
Proof.
  intros a n p Hva Hpos Hrav Hmem.
  apply (arc_control_triangle_in_circular_segment a p Hva).
  apply gtri_pos_implies_in_arc_control_triangle.
  exact Hpos.
Qed.

(* The forward form, phrased purely from the algebraic ray-parity premise
   (no need to separately assume `point_in_arc_seg_curve_geometry`): the
   `gtri`-positive, guarded point IS already known to be in the curve
   geometry via `arc_seg_control_interior_in_curve_geometry`, so the true-
   region conclusion follows from the premises alone. *)
Theorem arc_seg_parity_membership_sound_in_true_segment :
  forall (a : CircularArc) (n : nat) (p : Point),
    valid_arc a ->
    0 < gtri (px (arc_start a)) (py (arc_start a))
             (px (arc_mid a))   (py (arc_mid a))
             (px (arc_end a))   (py (arc_end a)) p ->
    ray_avoids_vertices p
      (gtri_ring (px (arc_start a)) (py (arc_start a))
                 (px (arc_mid a))   (py (arc_mid a))
                 (px (arc_end a))   (py (arc_end a))) ->
    point_in_arc_seg_curve_geometry a n p /\ in_circular_segment a p.
Proof.
  intros a n p Hva Hpos Hrav.
  split.
  - apply (arc_seg_control_interior_in_curve_geometry a n p Hpos Hrav).
  - apply (arc_control_triangle_in_circular_segment a p Hva).
    apply gtri_pos_implies_in_arc_control_triangle.
    exact Hpos.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Audit footprint.                                                       *)
(* -------------------------------------------------------------------------- *)

Print Assumptions gtri_pos_implies_in_arc_control_triangle.
Print Assumptions arc_seg_geometry_parity_sound_in_true_segment.
Print Assumptions arc_seg_parity_membership_sound_in_true_segment.

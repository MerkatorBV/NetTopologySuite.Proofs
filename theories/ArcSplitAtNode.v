(* ============================================================================
   NetTopologySuite.Proofs.ArcSplitAtNode
   ----------------------------------------------------------------------------
   General circular noding, rung 1 — GREEN (Qed-closed headline; Red
   surface planted and witnessed in the previous commit).

   Wishlist v7.0 unparked "general circular noding + arrangement: split
   arcs at N-AA/N-AL nodes, face labels, then general CAP·CUP·SUB·XOR" as
   the JTS laser after two-disc (OverlayNGCurve R1.5 — name gate NTSC0001:
   never OverlayNGCurved).  This rung is the first obligation of that
   lane: SPLITTING an arc at an intersection node is sound — the two
   children cover the parent, meet only at the node, and stay on the
   parent's circle.

   Witness-scoped, on the DISC_OVERLAY locked fixture (deliberately the
   SAME configuration that pins the oracle mode and JTS
   CircularDiscOverlay): circle A = centre (0,0), r = 5; parent arc = the
   open upper semicircle, chord (5,0)—(−5,0), mid (0,5); node =
   `radical_point_plus locked_O1 locked_O2 locked_r locked_r`
   = (7/2, √(51/4)), i.e. the N-AA node (3.5, √12.75) of the locked
   crossing pair, reused from ArcArcCircles / DiscOverlay (no second
   radical axis, and the node pins — px = 7/2, py² = 51/4, py > 0 — are
   consumed from `locked_disc_nodes`, not re-derived).

   Child membership is stated in the corpus' 3-axiom chord-sign form
   (the `arc_side_chord` cross-product convention of ArcSpanAtan2 /
   ArcChordSound, without the atan2 layer): a point of the parent arc is
   in a child iff it lies strictly on the child's side of the cut chord.

   GREEN (this rung).  The headline `arc_split_at_node_partition` is
   Qed: on the parent arc the child side tests coincide with the
   px-trichotomy at the node —

     side (X—A cut) > 0  ⟺  px P > 7/2      (child A→X, node side)
     side (C—X cut) > 0  ⟺  px P < 7/2      (child X→C, node side)
     px P = 7/2          ⟹  P = the node    (the only seam point)

   — by the squaring identities
     9·(25 − x²) − 51·(5 − x)²  = 60·(5 − x)·(x − 7/2)
     289·(25 − x²) − 51·(x + 5)² = 340·(x + 5)·(7/2 − x)
   over y² = 25 − x², h² = 51/4.  The noder-facing corollaries follow:
   `arc_split_cover` (no parent point is lost: every one is in a child
   or IS the node) and `arc_split_disjoint` (no point is double-counted).
   Pins: the node is on the circle (`split_node_on_circle`, via
   ArcArcCircles.radical_points_on_circles), in the parent span, and ON
   both cut chords (`split_node_on_both_cuts` — the seam, by ring alone).
   Mismatch probes: the lower-circle point (4,−3) has px > 7/2 yet fails
   the child test (the side test is NOT bare px-trichotomy off the
   span), and the off-circle point (4, 1/10) shows the on-circle
   hypothesis is load-bearing.

   Deliberately NOT in scope on this rung:
     - the general-configuration partition (arbitrary circle, arbitrary
       in-span node) — the inscribed-angle algebra is the next rung;
     - child MID selection (JTS recomputes sub-arc midpoints; here child
       spans are cut-chord sides, mid-free);
     - faces, labels, and the arrangement (later rungs of the lane);
     - line–circle (N-AL) split twins.

   No `Admitted`, no `Axiom`, no `Parameter`; 3-axiom classical-reals
   footprint (no atan2 / Classical_Prop; not in audit-exceptions).

   Registered in `_CoqProject.full` only: it imports DiscOverlay.v /
   ArcArcCircles.v (full-lane), so `make host` does not see it.

   Refs: docs/oracle-wishlist.md (v7.0 Remaining: general circular
   noding, rung 1 landed here); siblings DiscOverlay.v (locked fixture +
   node pins), ArcArcCircles.v (radical axis), ArcSpanAtan2.v /
   ArcChordSound.v (chord-sign span form), OverlayNGCurve.v (Phase-0
   exact cells).
   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import Distance Disk Overlay ArcArcCircles DiscOverlay.

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  The split configuration on the locked circle.                          *)
(* -------------------------------------------------------------------------- *)

(** Parent arc endpoints and mid: the upper semicircle of the locked
    circle A (centre (0,0), r = 5). *)
Definition split_A : Point := mkPoint 5 0.
Definition split_C : Point := mkPoint (-5) 0.
Definition split_B : Point := mkPoint 0 5.

(** The split node: the +h radical point of the locked crossing pair —
    the DISC_OVERLAY / ARC_ARC_XY node (7/2, √(51/4)). *)
Definition split_X : Point :=
  radical_point_plus locked_O1 locked_O2 locked_r locked_r.

(** Membership of the locked circle (squared form). *)
Definition on_locked_circle (P : Point) : Prop :=
  dist_sq locked_O1 P = locked_r * locked_r.

(** Chord side: the cross product `cross(V−U, P−U)` — the
    `arc_side_chord` convention, parameterised by the chord. *)
Definition chord_side (U V P : Point) : R :=
  (px V - px U) * (py P - py U) - (py V - py U) * (px P - px U).

(** Parent span (open upper semicircle), and its chord-sign form. *)
Definition in_parent_span (P : Point) : Prop := 0 < py P.

(** Child cut-chord side tests, oriented so the child interiors are the
    POSITIVE side (orientation fixed by the parent mid (0,5)). *)
Definition side_child_AX (P : Point) : R := chord_side split_X split_A P.
Definition side_child_XC (P : Point) : R := chord_side split_C split_X P.

(* -------------------------------------------------------------------------- *)
(* §2  Node pins consumed from DiscOverlay (locked_disc_nodes).                *)
(* -------------------------------------------------------------------------- *)

Lemma split_X_px : px split_X = 7/2.
Proof. exact (proj1 locked_disc_nodes). Qed.

Lemma split_X_py_sq : py split_X * py split_X = 51/4.
Proof. exact (proj1 (proj2 locked_disc_nodes)). Qed.

Lemma split_X_py_pos : 0 < py split_X.
Proof. exact (proj1 (proj2 (proj2 locked_disc_nodes))). Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Headline — GREEN.                                                      *)
(* -------------------------------------------------------------------------- *)

(** On the parent arc, the child side tests are exactly the
    px-trichotomy at the node, and the node is the only seam point. *)
Theorem arc_split_at_node_partition :
  forall P : Point,
    on_locked_circle P ->
    in_parent_span P ->
    (0 < side_child_AX P <-> 7/2 < px P) /\
    (0 < side_child_XC P <-> px P < 7/2) /\
    (px P = 7/2 -> P = split_X).
Proof.
  intros P Hc Hspan.
  unfold on_locked_circle, dist_sq, locked_O1, locked_r in Hc.
  cbn [px py] in Hc.
  unfold in_parent_span in Hspan.
  unfold side_child_AX, side_child_XC, chord_side, split_A, split_C.
  cbn [px py].
  rewrite split_X_px.
  set (x := px P) in *. set (y := py P) in *. set (h := py split_X) in *.
  assert (Hxy : x * x + y * y = 25) by nra.
  assert (Hh2 : h * h = 51/4) by (unfold h; exact split_X_py_sq).
  assert (Hh0 : 0 < h) by (unfold h; exact split_X_py_pos).
  assert (Hxlt5 : x < 5) by nra.
  assert (Hxgt5 : -5 < x) by nra.
  split; [| split].
  - (* side (X—A cut) > 0  ⟺  x > 7/2 *)
    split.
    + intros Hside.
      destruct (Rle_or_lt x (7/2)) as [Hle | Hgt]; [exfalso | exact Hgt].
      (* side = (3/2)·y − h·(5−x); with x ≤ 7/2 both halves square-compare *)
      assert (Hpos2 : 0 < 3/2 * y + h * (5 - x)) by nra.
      assert (Hsq : (3/2 * y) * (3/2 * y) > (h * (5 - x)) * (h * (5 - x)))
        by nra.
      assert (Hpoly : 9 * (25 - x * x) > 51 * ((5 - x) * (5 - x))) by nra.
      nra.
    + intros Hgt.
      assert (Hpoly : (3/2 * y) * (3/2 * y) - (h * (5 - x)) * (h * (5 - x))
                      > 0) by nra.
      assert (Hb0 : 0 <= h * (5 - x)) by nra.
      nra.
  - (* side (C—X cut) > 0  ⟺  x < 7/2 *)
    split.
    + intros Hside.
      destruct (Rle_or_lt (7/2) x) as [Hge | Hlt]; [exfalso | exact Hlt].
      assert (Hpos2 : 0 < 17/2 * y + h * (x + 5)) by nra.
      assert (Hsq : (17/2 * y) * (17/2 * y) > (h * (x + 5)) * (h * (x + 5)))
        by nra.
      assert (Hpoly : 289 * (25 - x * x) > 51 * ((x + 5) * (x + 5))) by nra.
      nra.
    + intros Hlt.
      assert (Hpoly : (17/2 * y) * (17/2 * y) - (h * (x + 5)) * (h * (x + 5))
                      > 0) by nra.
      assert (Hb0 : 0 <= h * (x + 5)) by nra.
      nra.
  - (* the seam: x = 7/2 pins P to the node *)
    intros Hx72.
    assert (Hyh : y = h).
    { assert (Hzero : (y - h) * (y + h) = 0) by nra.
      assert (Hsum : 0 < y + h) by lra.
      destruct (Rmult_integral _ _ Hzero) as [H0 | H0]; lra. }
    assert (HP : P = mkPoint x y) by (unfold x, y; destruct P; reflexivity).
    assert (HX : split_X = mkPoint (7/2) h).
    { assert (Heta : split_X = mkPoint (px split_X) (py split_X))
        by (destruct split_X; reflexivity).
      rewrite Heta, split_X_px. reflexivity. }
    rewrite HP, HX, Hx72, Hyh. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  The noder-facing corollaries: no point lost, none double-counted.      *)
(* -------------------------------------------------------------------------- *)

Corollary arc_split_cover :
  forall P : Point,
    on_locked_circle P -> in_parent_span P ->
    0 < side_child_AX P \/ 0 < side_child_XC P \/ P = split_X.
Proof.
  intros P Hc Hs.
  destruct (arc_split_at_node_partition P Hc Hs) as [H1 [H2 H3]].
  destruct (Rtotal_order (px P) (7/2)) as [Hlt | [Heq | Hgt]].
  - right. left. apply H2. exact Hlt.
  - right. right. apply H3. exact Heq.
  - left. apply H1. exact Hgt.
Qed.

Corollary arc_split_disjoint :
  forall P : Point,
    on_locked_circle P -> in_parent_span P ->
    ~ (0 < side_child_AX P /\ 0 < side_child_XC P).
Proof.
  intros P Hc Hs [Ha Hx].
  destruct (arc_split_at_node_partition P Hc Hs) as [H1 [H2 _]].
  apply H1 in Ha. apply H2 in Hx. lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  Pins: the node is on the circle, in the parent span, and on both       *)
(*     cut chords (the seam).                                                 *)
(* -------------------------------------------------------------------------- *)

Lemma split_node_on_circle : on_locked_circle split_X.
Proof.
  unfold on_locked_circle.
  pose proof locked_properly_intersect as H.
  unfold discs_properly_intersect, locked_A, locked_B in H.
  cbn [dcentre dradius] in H.
  destruct H as [Hr1 [Hr2 [Hd [Hrabs Hdlt]]]].
  exact (proj1 (proj1 (radical_points_on_circles
                         locked_O1 locked_O2 locked_r locked_r
                         Hr1 Hr2 Hd Hrabs Hdlt))).
Qed.

Lemma split_node_in_parent : in_parent_span split_X.
Proof.
  unfold in_parent_span. exact split_X_py_pos.
Qed.

(** The seam pin: the node lies ON both cut chords — pure ring, no
    coordinate pins needed. *)
Lemma split_node_on_both_cuts :
  side_child_AX split_X = 0 /\ side_child_XC split_X = 0.
Proof.
  unfold side_child_AX, side_child_XC, chord_side, split_A, split_C.
  cbn [px py].
  split; ring.
Qed.

(* -------------------------------------------------------------------------- *)
(* §6  Mismatch probes: the side tests are not bare px-trichotomy, and        *)
(*     the on-circle hypothesis is load-bearing.                              *)
(* -------------------------------------------------------------------------- *)

(** The lower-circle point (4,−3): px > 7/2, yet the child-AX test
    fails — the partition lives on the PARENT ARC, not on a vertical
    strip of the plane. *)
Lemma probe_lower_point_fails_AX :
  on_locked_circle (mkPoint 4 (-3)) /\
  ~ (0 < side_child_AX (mkPoint 4 (-3))).
Proof.
  split.
  - unfold on_locked_circle, dist_sq, locked_O1, locked_r. cbn [px py]. lra.
  - unfold side_child_AX, chord_side, split_A. cbn [px py].
    rewrite split_X_px.
    pose proof split_X_py_pos as Hh0.
    lra.
Qed.

(** The off-circle point (4, 1/10): px > 7/2 and in the upper
    half-plane, yet the child-AX test fails — on-circle is
    load-bearing. *)
Lemma probe_off_circle_fails_AX :
  ~ on_locked_circle (mkPoint 4 (1/10)) /\
  ~ (0 < side_child_AX (mkPoint 4 (1/10))).
Proof.
  split.
  - unfold on_locked_circle, dist_sq, locked_O1, locked_r. cbn [px py]. lra.
  - unfold side_child_AX, chord_side, split_A. cbn [px py].
    rewrite split_X_px.
    pose proof split_X_py_sq as Hh2.
    pose proof split_X_py_pos as Hh0.
    nra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.  3-axiom classical reals; no atan2, no Classic.           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions arc_split_at_node_partition.
Print Assumptions arc_split_cover.
Print Assumptions arc_split_disjoint.
Print Assumptions split_node_on_circle.
Print Assumptions split_node_on_both_cuts.
Print Assumptions probe_off_circle_fails_AX.

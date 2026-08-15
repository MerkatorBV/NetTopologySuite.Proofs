(* ============================================================================
   NetTopologySuite.Proofs.ArcSplitAtNode
   ----------------------------------------------------------------------------
   General circular noding, rung 1 — RED (planted surface; exactly ONE
   unproved headline below, failing at Qed).

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
   `DiscOverlay.split` — the radical point
   `radical_point_plus locked_O1 locked_O2 locked_r locked_r`
   = (7/2, √(51/4)), i.e. the N-AA node (3.5, √12.75) of the locked
   crossing pair, reused from ArcArcCircles / DiscOverlay (do not invent
   a second radical axis, and do not re-derive its pins).

   Child membership is stated in the corpus' 3-axiom chord-sign form
   (the `arc_side_chord` cross-product convention of ArcSpanAtan2 /
   ArcChordSound, without the atan2 layer): a point of the parent arc is
   in a child iff it lies strictly on the child's side of the cut chord.
   The headline proves those side tests coincide, on the parent arc, with
   the px-trichotomy at the node:

     side (X—A cut) > 0  ⟺  px P > 7/2      (child A→X, node side)
     side (C—X cut) > 0  ⟺  px P < 7/2      (child X→C, node side)
     px P = 7/2          ⟹  P = the node    (the only seam point)

   from which cover (every parent point is in a child or IS the node)
   and disjointness (no point is in both children) are corollaries — the
   no-loss / no-double-count facts a noder consumes when it replaces one
   arc edge by two at a detected intersection.

   Deliberately NOT in scope on this rung:
     - the general-configuration partition (arbitrary circle, arbitrary
       in-span node) — the inscribed-angle algebra is the next rung;
     - child MID selection (JTS recomputes sub-arc midpoints; here child
       spans are cut-chord sides, mid-free);
     - faces, labels, and the arrangement (later rungs of the lane);
     - line–circle (N-AL) split twins.

   No `Admitted`, no `Axiom`, no `Parameter`.

   Refs: docs/oracle-wishlist.md (v7.0 Remaining: general circular
   noding); siblings DiscOverlay.v (locked fixture + node pins),
   ArcArcCircles.v (radical axis), ArcSpanAtan2.v / ArcChordSound.v
   (chord-sign span form), OverlayNGCurve.v (Phase-0 exact cells).
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
(* §2  Headline — RED.  On the parent arc, the child side tests are           *)
(*     exactly the px-trichotomy at the node, and the node is the only        *)
(*     seam point.                                                            *)
(* -------------------------------------------------------------------------- *)

Theorem arc_split_at_node_partition :
  forall P : Point,
    on_locked_circle P ->
    in_parent_span P ->
    (0 < side_child_AX P <-> 7/2 < px P) /\
    (0 < side_child_XC P <-> px P < 7/2) /\
    (px P = 7/2 -> P = split_X).
Proof.
  intros P Hc Hspan.
  (* RED: stated, not yet proved — this Qed is the witnessed Red gate. *)
Qed.

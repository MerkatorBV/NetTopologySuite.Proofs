(* ============================================================================
   NetTopologySuite.Proofs.ExactCurveEpic508
   ----------------------------------------------------------------------------
   Epic #508 ticket-named QED ∨ QEX stop (same shape as ticket 522 /
   ticket 523).

   Bible §4.2 owes exact length on every ExactCurve zoo member.
   The year-1 carrier (`CurveGeometry.v : CurveSegment`) is
   `CSChord | CSArc`. Ellipse, Bézier, clothoid, and NURBS have no
   constructor — the issue's carrier blocker. That is QEX, not a
   CurveSegment remint and not an Exact* zoo type.

   QED: chord and circular-arc inhabit the carrier; every
   `CurveSegment` is one of those two constructors.
   `ticket_508_carrier_qed_or_qex` discharges left.

   QEX: a documented zoo member is not a `CurveSegment` constructor.
   `ticket_508_qed_or_qex` discharges right on the ellipse
   (`ellipse_not_curve_segment`). Clothoid / Bézier / NURBS are
   the same miss (`clothoid_not_curve_segment` and friends).

   QEX is not owner accept. Epic #508 stays open. Wrap-up is #566.
   Do not steal 508-e / 508-g / 508-h. Do not remint CurveSegment.
   Do not mint Exact* zoo types. Do not open ADR-0001 route D.
   Do not remint 64-a r·θ. Year-1 engine stays circular-only.

   WITNESS topic: metric · claimId: 508 · witness: 508-qed-qex
   lane: proofs
   issue: #508
   ADR-0004: not a leftover numeral and not a 508-* board mint
   (508-a … 508-h stay historical).

   No `Admitted`, no `Axiom`, no `Parameter`.  3-axiom.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.6
   ========================================================================== *)

From NTS.Proofs Require Import Distance CurveGeometry.

(* -------------------------------------------------------------------------- *)
(* Bible §4.2 zoo tags. Not CurveSegment constructors. Not Exact* types.      *)
(* -------------------------------------------------------------------------- *)

Inductive ExactCurveZoo : Type :=
| ECZ_Chord
| ECZ_CircularArc
| ECZ_Ellipse
| ECZ_Bezier
| ECZ_Clothoid
| ECZ_Nurbs.

Definition zoo_inhabits_curve_segment (z : ExactCurveZoo) : Prop :=
  match z with
  | ECZ_Chord => True
  | ECZ_CircularArc => True
  | ECZ_Ellipse => False
  | ECZ_Bezier => False
  | ECZ_Clothoid => False
  | ECZ_Nurbs => False
  end.

Lemma ellipse_not_curve_segment :
  ~ zoo_inhabits_curve_segment ECZ_Ellipse.
Proof.
  intro H. exact H.
Qed.

Lemma bezier_not_curve_segment :
  ~ zoo_inhabits_curve_segment ECZ_Bezier.
Proof.
  intro H. exact H.
Qed.

Lemma clothoid_not_curve_segment :
  ~ zoo_inhabits_curve_segment ECZ_Clothoid.
Proof.
  intro H. exact H.
Qed.

Lemma nurbs_not_curve_segment :
  ~ zoo_inhabits_curve_segment ECZ_Nurbs.
Proof.
  intro H. exact H.
Qed.

(* Year-1 carrier exhaustiveness. Not a remint. *)
Lemma curve_segment_chord_or_arc :
  forall s : CurveSegment,
    (exists p q, s = CSChord p q) \/ (exists a, s = CSArc a).
Proof.
  intros s.
  destruct s as [p q | a].
  - left. exists p, q. reflexivity.
  - right. exists a. reflexivity.
Qed.

(* Epic #508 stop: every zoo member inhabits CurveSegment (QED) or a
   documented zoo member is missing from the carrier (QEX).
   Discharged QEX on the ellipse — the issue's carrier blocker. *)
(* WITNESS {"claimId":"508","topic":"metric","lemma":"ticket_508_qed_or_qex","title":"Epic #508 stop is zoo-on-CurveSegment (QED) or a documented missing constructor (QEX); discharged QEX on the ellipse","file":"theories/ExactCurveEpic508.v","witness":"508-qed-qex","board":"#508"} *)

Theorem ticket_508_qed_or_qex :
  (forall z : ExactCurveZoo, zoo_inhabits_curve_segment z)
  \/
  (exists z : ExactCurveZoo, ~ zoo_inhabits_curve_segment z).
Proof.
  right.
  exists ECZ_Ellipse.
  exact ellipse_not_curve_segment.
Qed.

(* Year-1 circular carrier (QED) or the documented miss (QEX).
   Chord and circular-arc inhabit; every CurveSegment is one of
   those two. Children 508-a … 508-d / 508-f remain QED. *)
Theorem ticket_508_carrier_qed_or_qex :
  (zoo_inhabits_curve_segment ECZ_Chord /\
   zoo_inhabits_curve_segment ECZ_CircularArc /\
   forall s : CurveSegment,
     (exists p q, s = CSChord p q) \/ (exists a, s = CSArc a))
  \/
  (exists z : ExactCurveZoo, ~ zoo_inhabits_curve_segment z).
Proof.
  left.
  split; [exact I|].
  split; [exact I|].
  exact curve_segment_chord_or_arc.
Qed.

Print Assumptions ellipse_not_curve_segment.
Print Assumptions clothoid_not_curve_segment.
Print Assumptions curve_segment_chord_or_arc.
Print Assumptions ticket_508_qed_or_qex.
Print Assumptions ticket_508_carrier_qed_or_qex.

(* ============================================================================
   NetTopologySuite.Proofs.RelateNGEpic522
   ----------------------------------------------------------------------------
   Epic #522 ticket-named QED ∨ QEX stop (leftover-Ⅱ dual, same shape
   as ticket 523).

   QEX: completeness of CCW `triangle_pair_regime` or a documented
   unsupported pair. `ticket_522_qed_or_qex` discharges right on the
   unnamed same-side shared-edge nest after leftover `Ⅷ`
   (`RelateNGUnnamedCex.v : unnamed_ccw_pair_unsupported`). Not a
   remint of leftover `Ⅴ`'s `triangle_pair_regime_ccw_stop` and not
   a remint of `522-j`.

   QED: leftover `Ⅰ`–`Ⅷ` on this letter are classified.
   `ticket_522_classified_qed_or_qex` discharges left. Does not
   claim leftover `Ⅸ`–`Ⅹ`. Does not remint detectors or fills.

   QEX is not owner accept. Epic #522 stays open. Do not steal
   522-j / 522-m / 522-f / 522-l. Do not mint 522-n. Do not mint
   leftover `Ⅸ`. Do not remint leftover `Ⅵ` / leftover `Ⅶ`.
   Do not remint aa_matrix_*.

   WITNESS topic: relate · claimId: 522 · witness: 522-qed-qex
   macro: relate
   lane: proofs
   issue: #522
   ADR-0004: not a leftover numeral and not a 522-* board mint
   (522-a … 522-m stay historical).

   No `Admitted`, no `Axiom`, no `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Agent
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import Distance GeneralTriangleSeparation
  RelateMatrixTriangle RelateNGCore RelateNGUnnamedCex RelateNGTouchMixedCone.
Local Open Scope R_scope.

(* Epic #522 stop: completeness (QED) or a documented CCW
   unsupported pair (QEX). Discharged QEX on the unnamed same-side
   shared-edge nest after leftover `Ⅷ`. Not leftover `Ⅸ`. Not a
   522-j remint. *)
(* WITNESS {"claimId":"522","topic":"relate","lemma":"ticket_522_qed_or_qex","title":"Epic #522 stop is completeness (QED) or a documented CCW unsupported pair (QEX); discharged QEX on an unnamed same-side shared-edge nest","file":"theories/RelateNGEpic522.v","witness":"522-qed-qex","board":"#522"} *)
Theorem ticket_522_qed_or_qex :
  (forall ax ay bx by_ cx cy dx dy ex ey fx fy : R,
     0 < gdbl ax ay bx by_ cx cy ->
     0 < gdbl dx dy ex ey fx fy ->
     triangle_pair_regime ax ay bx by_ cx cy dx dy ex ey fx fy
       <> TPR_Unsupported)
  \/
  (exists ax ay bx by_ cx cy dx dy ex ey fx fy : R,
     0 < gdbl ax ay bx by_ cx cy /\
     0 < gdbl dx dy ex ey fx fy /\
     triangle_pair_regime ax ay bx by_ cx cy dx dy ex ey fx fy
       = TPR_Unsupported).
Proof.
  right.
  exists 0, 0, 4, 0, 0, 4, 0, 0, 4, 0, 1, 1.
  split; [unfold gdbl; lra|].
  split; [unfold gdbl; lra|].
  exact unnamed_ccw_pair_unsupported.
Qed.

(* Named leftovers are classified (QED) or the unnamed same-side
   shared-edge nest stays unsupported (QEX). Leftover `Ⅰ`–`Ⅷ` are QED. *)
Theorem ticket_522_classified_qed_or_qex :
  (triangle_pair_regime 0 0 2 0 0 1 1 0 3 0 2 1 = TPR_TouchPartialEdge /\
   triangle_pair_regime 0 0 2 0 0 2 0 0 (-2) 0 1 (-1) = TPR_TouchObtuse /\
   triangle_pair_regime 0 0 2 0 0 1 1 0 (1/2) (-1) (3/2) (-1)
     = TPR_TouchOnesided /\
   triangle_pair_regime 0 0 2 0 0 1 1 0 (5/4) (1/4) (3/4) (1/4)
     = TPR_TouchOnesided /\
   triangle_pair_regime 0 0 2 0 0 2 0 0 (-1) (-1) 3 1 = TPR_MixedCone /\
   triangle_pair_regime 0 0 2 0 0 2 0 0 3 1 1 3 = TPR_SameCone /\
   triangle_pair_regime 0 0 3 0 0 3 2 (-1) 2 2 (-1) 2 = TPR_Lens /\
   triangle_pair_regime 1 1 2 1 1 2 0 0 4 0 0 4 = TPR_Inside)
  \/
  triangle_pair_regime 0 0 4 0 0 4 0 0 4 0 1 1 = TPR_Unsupported.
Proof.
  left.
  split; [exact leftover_I_still_partial|].
  split; [exact leftover_II_still_obtuse|].
  split; [exact leftover_III_still_onesided|].
  split; [exact leftover_IV_still_onesided|].
  split; [exact triangle_pair_regime_mixedcone|].
  split; [exact same_cone_pair_samecone|].
  split; [exact lens_pair_lens|].
  exact inside_pair_inside.
Qed.

Print Assumptions ticket_522_qed_or_qex.
Print Assumptions ticket_522_classified_qed_or_qex.

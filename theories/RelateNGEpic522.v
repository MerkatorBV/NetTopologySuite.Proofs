(* ============================================================================
   NetTopologySuite.Proofs.RelateNGEpic522
   ----------------------------------------------------------------------------
   Epic #522 ticket-named QED ∨ QEX stop (leftover-Ⅱ dual, same shape
   as ticket 523).

   QEX: completeness of CCW `triangle_pair_regime` or a documented
   unsupported pair. `ticket_522_qed_or_qex` restates
   `RelateNGTouchMixedCone.v : triangle_pair_regime_ccw_stop` and
   discharges right on the unnamed pair after leftover `Ⅴ`
   (`RelateNGUnnamedCex.v : unnamed_ccw_pair_unsupported`).

   QED: leftover `Ⅰ`–`Ⅴ` on `main` are classified.
   `ticket_522_classified_qed_or_qex` discharges left. Does not
   claim leftover `Ⅵ`–`Ⅹ`. Does not remint detectors or fills.

   QEX is not owner accept. Epic #522 stays open. Do not steal
   522-j / 522-m / 522-f / 522-l. Do not mint 522-n. Do not mint
   leftover `Ⅵ`. Do not remint aa_matrix_*.

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

From Stdlib Require Import Reals.
From NTS.Proofs Require Import Distance RelateNGCore RelateNGTouchMixedCone.
Local Open Scope R_scope.

(* Epic #522 stop: completeness (QED) or a documented CCW
   unsupported pair (QEX). Discharged QEX — unnamed after leftover
   `Ⅴ`, not leftover `Ⅵ`. Not a 522-j remint. *)
(* WITNESS {"claimId":"522","topic":"relate","lemma":"ticket_522_qed_or_qex","title":"Epic #522 stop is completeness (QED) or a documented CCW unsupported pair (QEX); discharged QEX on an unnamed pair","file":"theories/RelateNGEpic522.v","witness":"522-qed-qex","board":"#522"} *)
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
  exact triangle_pair_regime_ccw_stop.
Qed.

(* Named leftovers on main are classified (QED) or the unnamed
   pair stays unsupported (QEX). Leftover `Ⅰ`–`Ⅴ` are QED. *)
Theorem ticket_522_classified_qed_or_qex :
  (triangle_pair_regime 0 0 2 0 0 1 1 0 3 0 2 1 = TPR_TouchPartialEdge /\
   triangle_pair_regime 0 0 2 0 0 2 0 0 (-2) 0 1 (-1) = TPR_TouchObtuse /\
   triangle_pair_regime 0 0 2 0 0 1 1 0 (1/2) (-1) (3/2) (-1)
     = TPR_TouchOnesided /\
   triangle_pair_regime 0 0 2 0 0 1 1 0 (5/4) (1/4) (3/4) (1/4)
     = TPR_TouchOnesided /\
   triangle_pair_regime 0 0 2 0 0 2 0 0 (-1) (-1) 3 1 = TPR_MixedCone)
  \/
  triangle_pair_regime 0 0 2 0 0 2 0 0 3 1 1 3 = TPR_Unsupported.
Proof.
  left.
  split; [exact leftover_I_still_partial|].
  split; [exact leftover_II_still_obtuse|].
  split; [exact leftover_III_still_onesided|].
  split; [exact leftover_IV_still_onesided|].
  exact triangle_pair_regime_mixedcone.
Qed.

Print Assumptions ticket_522_qed_or_qex.
Print Assumptions ticket_522_classified_qed_or_qex.

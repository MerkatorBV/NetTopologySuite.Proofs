(* ============================================================================
   NetTopologySuite.Proofs.RelateCurveAlphabet
   ----------------------------------------------------------------------------
   Ticket 523 stop: QED ∨ QEX on the `CURVE_RELATE_MATRIX` result alphabet.

   ISO/IEC 13249-3 Table 13 (`ST_Relate` intersection-matrix pattern) is
   F / 0 / 1 / 2 / T / *. Coq `PatternChar` is that alphabet
   (`PFalse` / `PDim` / `PTrue` / `PWild`). There is no `?` constructor.
   The computed result 9-char is the narrower set F / 0 / 1 / 2.
   Coq emptiness is `DimValue` `None` (`RelateCurveMatrix.v :
   cell_none_iff_empty`), which encodes as `F`, not `?`.

   523-c prints `?` where emptiness is not established (exhausted
   probe / lineal undistinguished). That glyph is not Table 13 and
   not a result cell. `DimValue` cannot encode it
   (`dim_to_result_never_unknown`).

   QED: every `CURVE_RELATE_MATRIX` result glyph is ISO F/0/1/2.
   QEX: a documented non-ISO glyph exists.
   `ticket_523_qed_or_qex` is that disjunction, discharged QEX on
   `CRR_Unknown`. Children `523-a` / `523-b` / `523-c` remain QED
   (landed). This stop is not owner accept. Ticket 523 stays open.
   Ticket 11 precondition 3 still waits.

   Does not remint `RelateNGOracleSurface.v` `WireCell` (F/0/1/2 only;
   that surface is `522-f`). Does not put `?` in catalog keys or
   `RELATE_TOKENS`. Does not steal `522-f` / `522-n`. Does not mint
   leftover `Ⅺ`. Year 1 is circular; no elliptic / Bézier zoo.

   WITNESS topic: relate · claimId: 523 · witness: 523-qex-question
   macro: relate
   lane: proofs
   issue: #523
   ADR-0004: not a leftover numeral and not a 522-* board mint.

   No `Admitted`, no `Axiom`, no `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Agent
   ========================================================================== *)

From Stdlib Require Import Lia.
From NTS.Proofs Require Import DE9IM.

(* -------------------------------------------------------------------------- *)
(* ISO Table 13 pattern alphabet, as already modelled by `PatternChar`.       *)
(* -------------------------------------------------------------------------- *)

Definition iso_table13_pattern (c : PatternChar) : Prop :=
  match c with
  | PWild => True
  | PFalse => True
  | PTrue => True
  | PDim n => (n <= 2)%nat
  end.

(* -------------------------------------------------------------------------- *)
(* `CURVE_RELATE_MATRIX` result glyphs. `CRR_Unknown` is the 523-c `?`.       *)
(* Not a remint of `WireCell` (F/0/1/2 only).                                 *)
(* -------------------------------------------------------------------------- *)

Inductive CurveRelateResult : Type :=
| CRR_F
| CRR_0
| CRR_1
| CRR_2
| CRR_Unknown.

Definition iso_result_cell (c : CurveRelateResult) : Prop :=
  match c with
  | CRR_Unknown => False
  | _ => True
  end.

Definition result_to_pattern (c : CurveRelateResult) : option PatternChar :=
  match c with
  | CRR_F => Some PFalse
  | CRR_0 => Some (PDim 0)
  | CRR_1 => Some (PDim 1)
  | CRR_2 => Some (PDim 2)
  | CRR_Unknown => None
  end.

Lemma question_mark_not_iso_result :
  ~ iso_result_cell CRR_Unknown.
Proof.
  intro H. exact H.
Qed.

Lemma question_mark_not_iso_table13 :
  ~ (exists p, result_to_pattern CRR_Unknown = Some p
               /\ iso_table13_pattern p).
Proof.
  intros [p [Hp _]]. discriminate.
Qed.

Lemma unknown_neq_F : CRR_Unknown <> CRR_F.
Proof.
  discriminate.
Qed.

Lemma result_to_pattern_iso :
  forall c p,
    result_to_pattern c = Some p -> iso_table13_pattern p.
Proof.
  intros c p H.
  destruct c; simpl in H; inversion H; subst; simpl; try exact I; lia.
Qed.

Lemma iso_result_iff_pattern :
  forall c,
    iso_result_cell c <->
    exists p, result_to_pattern c = Some p /\ iso_table13_pattern p.
Proof.
  intros c. split.
  - destruct c; intro H.
    + exists PFalse. split; [reflexivity | exact I].
    + exists (PDim 0). split; [reflexivity | simpl; lia].
    + exists (PDim 1). split; [reflexivity | simpl; lia].
    + exists (PDim 2). split; [reflexivity | simpl; lia].
    + destruct H.
  - intros [p [Hp _]].
    destruct c; simpl in Hp; try exact I; discriminate.
Qed.

(* -------------------------------------------------------------------------- *)
(* Coq emptiness is `None` → `F`. `DimValue` cannot encode `?`.               *)
(* -------------------------------------------------------------------------- *)

Definition dim_to_result (d : DimValue) : option CurveRelateResult :=
  match d with
  | None => Some CRR_F
  | Some 0 => Some CRR_0
  | Some 1 => Some CRR_1
  | Some 2 => Some CRR_2
  | Some _ => None
  end.

Lemma dim_empty_encodes_F :
  dim_to_result None = Some CRR_F.
Proof.
  reflexivity.
Qed.

Lemma dim_to_result_never_unknown :
  forall d, dim_to_result d <> Some CRR_Unknown.
Proof.
  intros d H.
  destruct d as [n|].
  - destruct n as [|[|[|n]]]; discriminate.
  - discriminate.
Qed.

(* Ticket 523 stop: every result glyph is ISO F/0/1/2 (QED) or a
   documented non-ISO cell exists (QEX). Discharged QEX — 523-c `?`.
   Children 523-a/b/c remain QED. Not owner accept. *)
(* WITNESS {"claimId":"523","topic":"relate","lemma":"ticket_523_qed_or_qex","title":"Ticket 523 stop is ISO result-alphabet completeness (QED) or a documented non-ISO cell (QEX); discharged QEX on '?'","file":"theories/RelateCurveAlphabet.v","witness":"523-qex-question","board":"#523"} *)
Theorem ticket_523_qed_or_qex :
  (forall c : CurveRelateResult, iso_result_cell c)
  \/
  (exists c : CurveRelateResult, ~ iso_result_cell c).
Proof.
  right.
  exists CRR_Unknown.
  exact question_mark_not_iso_result.
Qed.

Print Assumptions question_mark_not_iso_result.
Print Assumptions question_mark_not_iso_table13.
Print Assumptions unknown_neq_F.
Print Assumptions iso_result_iff_pattern.
Print Assumptions dim_empty_encodes_F.
Print Assumptions dim_to_result_never_unknown.
Print Assumptions ticket_523_qed_or_qex.

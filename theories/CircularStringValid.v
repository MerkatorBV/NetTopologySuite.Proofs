(* ============================================================================
   NetTopologySuite.Proofs.CircularStringValid
   ----------------------------------------------------------------------------
   V-CS / JTS #86: even CircularString control count is valid only as the
   closed 4-control annulus ring CIRCULARSTRING(A,B,C,A).

   JTS pin 2b56b1a4 (`CircularString.isValidControlCount`):
     empty                        → valid
     odd n ≥ 3                    → valid (usual SFA chained 3-point arcs)
     n = 4 ∧ first = last         → valid closed circular ring (annulus)
     even leftover, first ≠ last  → invalid

   This file certifies the control-count predicate and the three witnesses.
   Non-collinear / circumcircle is the existing `valid_arc` rule, not reminted.
   Not H-CC area `50 + 12.5 acos(0.6)`. Year-1 circular only.

   topic: arc
   claimId: V-CS
   witness: circularstring-abca

   (* WITNESS {"claimId":"V-CS","topic":"arc","lemma":"circularstring_abca_valid","title":"Even CircularString controls valid only as CIRCULARSTRING(A,B,C,A)","witness":"circularstring-abca","file":"theories/CircularStringValid.v","board":"#86"} *)

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.6
   ========================================================================== *)

From Stdlib Require Import Reals List Arith Lia Lra.
From NTS.Proofs Require Import Distance.

Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  Control-count predicate (JTS isValidControlCount @ 2b56b1a4).           *)
(* -------------------------------------------------------------------------- *)

Definition cs_first_eq_last (cs : list Point) : Prop :=
  match cs with
  | [] => False
  | p :: rest => List.last (p :: rest) p = p
  end.

Definition is_valid_control_count (cs : list Point) : Prop :=
  cs = [] \/
  (Nat.Odd (length cs) /\ (3 <= length cs)%nat) \/
  (length cs = 4%nat /\ cs_first_eq_last cs).

(* -------------------------------------------------------------------------- *)
(* §2  The three witnesses: even+closed, even+open, odd still valid.           *)
(* -------------------------------------------------------------------------- *)

Definition abca_ring : list Point :=
  [mkPoint (-5) 0; mkPoint 0 5; mkPoint 5 0; mkPoint (-5) 0].

Definition open_even : list Point :=
  [mkPoint 0 0; mkPoint 1 1; mkPoint 2 0; mkPoint 3 1].

Definition odd_closed : list Point :=
  [mkPoint (-5) 0; mkPoint 0 5; mkPoint 5 0; mkPoint 0 (-5); mkPoint (-5) 0].

Lemma odd_controls_valid :
  forall cs,
    Nat.Odd (length cs) -> (3 <= length cs)%nat ->
    is_valid_control_count cs.
Proof.
  intros cs Hodd Hle.
  unfold is_valid_control_count.
  right. left. split; assumption.
Qed.

Lemma closed_four_valid :
  forall cs,
    length cs = 4%nat -> cs_first_eq_last cs ->
    is_valid_control_count cs.
Proof.
  intros cs Hlen Hcl.
  unfold is_valid_control_count.
  right. right. split; assumption.
Qed.

Lemma even_open_four_invalid :
  forall cs,
    length cs = 4%nat -> ~ cs_first_eq_last cs ->
    ~ is_valid_control_count cs.
Proof.
  intros cs Hlen Hopen [He | [[Hodd _] | [_ Hcl]]].
  - subst cs. discriminate.
  - rewrite Hlen in Hodd. inversion Hodd. lia.
  - exact (Hopen Hcl).
Qed.

Theorem circularstring_abca_valid :
  is_valid_control_count abca_ring.
Proof.
  apply closed_four_valid; reflexivity.
Qed.

Theorem circularstring_open_even_invalid :
  ~ is_valid_control_count open_even.
Proof.
  apply even_open_four_invalid; [reflexivity |].
  unfold cs_first_eq_last, open_even.
  intros H. injection H as Hx Hy. lra.
Qed.

Theorem circularstring_odd_closed_valid :
  is_valid_control_count odd_closed.
Proof.
  apply odd_controls_valid.
  - exists 2%nat. reflexivity.
  - simpl. lia.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Audit footprint.                                                       *)
(* -------------------------------------------------------------------------- *)

Print Assumptions circularstring_abca_valid.
Print Assumptions circularstring_open_even_invalid.
Print Assumptions circularstring_odd_closed_valid.

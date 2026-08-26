(* ============================================================================
   NetTopologySuite.Proofs.CircularStringOddCount
   ----------------------------------------------------------------------------
   EX-CS-4: PostGIS / ISO/IEC 13249-3 odd control count. Four-item
   CIRCULARSTRING(A,B,C,A) is not a valid stored list.

   JTS pin 81c2e996 (`CircularString.isValidControlCount` after #124):
     empty                        → valid
     odd n ≥ 3                    → valid
     n = 4 (even, closed or open) → invalid

   V-CS / CircularStringValid.v remains the historical JTS 2b56b1a4 pin
   (closed-4 accepted). This file does not reuse claimId V-CS.
   Not H-CC area `50 + 12.5 acos(0.6)`. Year-1 circular only.

   topic: arc
   claimId: EX-CS-4
   witness: circularstring-abca-rejected

   (* WITNESS {"claimId":"EX-CS-4","topic":"arc","lemma":"circularstring_abca_postgis_invalid","title":"Four-item CIRCULARSTRING(A,B,C,A) is not a PostGIS control count","witness":"circularstring-abca-rejected","file":"theories/CircularStringOddCount.v","board":"#124"} *)

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.6
   ========================================================================== *)

From Stdlib Require Import Reals List Lia.
From NTS.Proofs Require Import Distance.

Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  PostGIS / JTS 81c2e996 control-count predicate.                         *)
(* -------------------------------------------------------------------------- *)

Definition postgis_valid_control_count (cs : list Point) : Prop :=
  cs = [] \/
  (Nat.Odd (length cs) /\ (3 <= length cs)%nat).

(* -------------------------------------------------------------------------- *)
(* §2  Witnesses: closed-4 rejected, open-4 rejected, odd-5 still valid.       *)
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
    postgis_valid_control_count cs.
Proof.
  intros cs Hodd Hle.
  unfold postgis_valid_control_count.
  right. split; assumption.
Qed.

Lemma even_four_invalid :
  forall cs,
    length cs = 4%nat ->
    ~ postgis_valid_control_count cs.
Proof.
  intros cs Hlen [He | [Hodd _]].
  - subst cs. discriminate.
  - rewrite Hlen in Hodd.
    destruct Hodd as [m Hm]. lia.
Qed.

Theorem circularstring_abca_postgis_invalid :
  ~ postgis_valid_control_count abca_ring.
Proof.
  apply even_four_invalid. reflexivity.
Qed.

Theorem circularstring_open_even_postgis_invalid :
  ~ postgis_valid_control_count open_even.
Proof.
  apply even_four_invalid. reflexivity.
Qed.

Theorem circularstring_odd_closed_postgis_valid :
  postgis_valid_control_count odd_closed.
Proof.
  apply odd_controls_valid.
  - exists 2%nat. reflexivity.
  - simpl. lia.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Audit footprint.                                                       *)
(* -------------------------------------------------------------------------- *)

Print Assumptions circularstring_abca_postgis_invalid.
Print Assumptions circularstring_open_even_postgis_invalid.
Print Assumptions circularstring_odd_closed_postgis_valid.

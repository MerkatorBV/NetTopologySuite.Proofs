(* ============================================================================
   NetTopologySuite.Proofs.RelateEdgePosSort
   ----------------------------------------------------------------------------
   The exact edge-position comparator is a strict TOTAL ORDER, and sorting an
   edge's intersection points by it yields a monotone (rounding-free) sequence.

   RelateEdgePosOrder.v gave the pairwise comparator `pos_compare` and its
   correctness; RelateEdgeInterParam.v attached it to real intersection
   geometry.  Noding, however, does not compare two points -- it SORTS all the
   intersection points on an edge into one monotone chain.  A sort is only
   meaningful if the comparison is a strict total order.  This module proves it.

   An edge position is a rational `pnum / pden` with a POSITIVE denominator
   (`EPos`).  The strict order is the cross-multiply

       a < b   :=   pnum a * pden b  <  pnum b * pden a.

   The load-bearing fact is TRANSITIVITY: it is NOT a consequence of integer
   `<` alone -- it needs the positivity of all three denominators and a
   nonlinear (degree-3) cancellation.  With that, `eplt` is a `StrictOrder`
   (irreflexive + transitive), is trichotomous (total), and -- via
   `pos_lt_iff_cross` -- coincides with the true real-number order of the
   ratios.  Hence any list `Sorted` by the exact integer comparator is `Sorted`
   by real position: the noding sequence is monotone, with zero rounding.

   The order theory (`eplt_trans`, `eplt_irrefl`, trichotomy, `epcompare_spec`)
   is pure `Z` (0 axioms); only the real-order agreement and the monotone-sort
   corollary touch `R` (classical-reals trio).

   No `Admitted`, no `Axiom`, no `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import ZArith Lia Reals Lra List RelationClasses.
From Stdlib Require Import Sorting.Sorted.
From NTS.Proofs Require Import RelateEdgePosOrder.

Local Open Scope Z_scope.

(* -------------------------------------------------------------------------- *)
(* §1  Edge positions and the cross-multiply strict order.                    *)
(* -------------------------------------------------------------------------- *)

(* An edge position: a rational with a positive denominator (the sign of the
   orientation determinant that plays the denominator is normalised into the
   numerator, so `pden > 0` is a WLOG normal form). *)
Record EPos : Type := mkEPos { pnum : Z; pden : Z; pden_pos : 0 < pden }.

(* Strict order by cross-multiply (division-free). *)
Definition eplt (a b : EPos) : Prop := pnum a * pden b < pnum b * pden a.

(* Irreflexivity: x < x is x*dx < x*dx, absurd. *)
Lemma eplt_irrefl : forall a, ~ eplt a a.
Proof. intros a. unfold eplt. lia. Qed.

(* TRANSITIVITY (the crux): positive denominators + degree-3 cancellation. *)
Lemma eplt_trans : forall a b c, eplt a b -> eplt b c -> eplt a c.
Proof.
  intros [na da Hda] [nb db Hdb] [nc dc Hdc]. unfold eplt; simpl.
  intros H1 H2.
  (* H1: na*db < nb*da ; H2: nb*dc < nc*db ; goal: na*dc < nc*da. *)
  (* Scale H1 by dc>0 and H2 by da>0, chain, then cancel db>0. *)
  assert (K1 : na * db * dc < nb * da * dc) by nia.
  assert (K2 : nb * dc * da < nc * db * da) by nia.
  nia.
Qed.

Instance eplt_StrictOrder : StrictOrder eplt.
Proof.
  constructor.
  - intros a Ha. exact (eplt_irrefl a Ha).
  - intros a b c. exact (eplt_trans a b c).
Qed.

(* Totality: trichotomy of the cross-multiply. *)
Lemma eplt_trichotomy :
  forall a b, eplt a b \/ pnum a * pden b = pnum b * pden a \/ eplt b a.
Proof.
  intros a b. unfold eplt.
  destruct (Z.lt_trichotomy (pnum a * pden b) (pnum b * pden a)) as [H | [H | H]].
  - left; exact H.
  - right; left; exact H.
  - right; right; exact H.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  A decidable comparator (reusing pos_compare) consistent with eplt.     *)
(* -------------------------------------------------------------------------- *)

Definition epcompare (a b : EPos) : comparison :=
  pos_compare (pnum a) (pden a) (pnum b) (pden b).

Lemma epcompare_spec :
  forall a b,
    match epcompare a b with
    | Lt => eplt a b
    | Eq => pnum a * pden b = pnum b * pden a
    | Gt => eplt b a
    end.
Proof.
  intros a b. unfold epcompare, pos_compare, eplt.
  destruct (Z.compare_spec (pnum a * pden b) (pnum b * pden a)) as [He | Hl | Hg].
  - exact He.
  - exact Hl.
  - exact Hg.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Agreement with the true real-number order of the ratios.              *)
(* -------------------------------------------------------------------------- *)

Definition epval (a : EPos) : R := (IZR (pnum a) / IZR (pden a))%R.

(* The integer comparator IS the real ratio order (positive denominators). *)
Lemma eplt_iff_R : forall a b, eplt a b <-> (epval a < epval b)%R.
Proof.
  intros a b. unfold eplt, epval.
  symmetry. apply pos_lt_iff_cross; [ apply pden_pos | apply pden_pos ].
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Sorting: a comparator-sorted edge is monotone in real position.        *)
(* -------------------------------------------------------------------------- *)

(* Sortedness is preserved when the order relation is weakened pointwise. *)
Lemma Sorted_impl :
  forall (A : Type) (R R' : A -> A -> Prop),
    (forall x y, R x y -> R' x y) ->
    forall l, Sorted R l -> Sorted R' l.
Proof.
  intros A R R' Himp l Hs.
  induction Hs as [| a l Hstail IH Hhd].
  - constructor.
  - constructor.
    + exact IH.
    + destruct Hhd; constructor. apply Himp; assumption.
Qed.

(* PAYOFF: a list sorted by the exact integer comparator `eplt` is sorted by
   true real position -- the noding sequence is monotone, with zero rounding. *)
Theorem sorted_eplt_monotone :
  forall l, Sorted eplt l -> Sorted (fun a b => (epval a < epval b)%R) l.
Proof.
  apply Sorted_impl. intros x y H. apply eplt_iff_R. exact H.
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  Audit footprint.                                                       *)
(* -------------------------------------------------------------------------- *)

Print Assumptions eplt_trans.
Print Assumptions eplt_trichotomy.
Print Assumptions epcompare_spec.
Print Assumptions sorted_eplt_monotone.

(* ============================================================================
   nts-eval micro unit — claimId 423-a (RED)
   Red planted 2026-08-02 · Green pending
   ----------------------------------------------------------------------------
   DIRECTED DISCRETE HAUSDORFF distance on finite point lists
   (Huttenlocher-Klanderman-Rucklidge 1993, the h(A,B) of JTS/NTS
   DiscreteHausdorffDistance):

       h(A,B) = max_{a in A} min_{b in B} d(a,b).

   Squared-distance convention (corpus rational-witness discipline: sqrt
   is monotone, so the max-min STRUCTURE is identical in either reading;
   the plan's metric-units expectations 1 / 2 / 3 read 1 / 4 / 9 here).
   The adjacent corpus surface, Linearise.hausdorff_le, is an eps-BOUND
   predicate on continuous Shapes -- there is no discrete max-min VALUE,
   and no attainment fact, anywhere in the corpus: that is the gap.

   RED SURFACE.  The headline spec is STATED below
   (`directed_discrete_hausdorff_claim`) and deliberately NOT proved in
   this unit -- no `Admitted`, no `Axiom`; the claim is a named
   `Definition ... : Prop`, so the Eval -> Qed matcher reports 423-a red.
   The spec pins the computed value h = directed_hausdorff_sq A B from
   both sides on nonempty lists:
     (cover)  every a in A has some b in B with dist_sq a b <= h;
     (attain) some a in A has dist_sq a b >= h against EVERY b in B.
   Together these say h is exactly the attained max-min.
   Green target:
     Lemma directed_discrete_hausdorff_max_min :
       directed_discrete_hausdorff_claim.
   with the production home suggested as theories/HausdorffDiscrete.v
   (list induction over Rmin/Rmax; no sqrt anywhere), same WITNESS tag.

   What IS Qed here: rational witness pins fixing the intended
   max-min/direction semantics --
     - the plan's pair example A = [(0,0);(1,0)], B = [(0,1);(1,1)]:
       h_sq(A,B) = 1 and h_sq(B,A) = 1 (metric h = 1 both ways);
     - the asymmetric example A' = [(0,0)], B' = [(0,2);(3,0)]:
       h_sq(A',B') = 4  -- MIN selected inside (a max-inside reading
                          would give 9);
       h_sq(B',A') = 9  -- MAX selected outside (a min-outside reading
                          would give 4);
       and 4 <> 9 kills any symmetrised reading (h is DIRECTED).

   WITNESS claimId: 423-a
   Lemma (Green target): directed_discrete_hausdorff_max_min
   ========================================================================== *)

(* WITNESS {"claimId":"423-a","topic":"metric","lemma":"directed_discrete_hausdorff_max_min","title":"Directed discrete Hausdorff = attained max-min over finite point lists"} *)

From Stdlib Require Import Reals Lra List.
Import ListNotations.
Local Open Scope R_scope.

Record Point : Type := mkPoint { px : R; py : R }.

Definition dist_sq (p q : Point) : R :=
  (px p - px q) * (px p - px q) + (py p - py q) * (py p - py q).

(* Innermost aggregate: squared distance from a to its nearest point of B.
   The [] sentinel 0 is outside the claim's domain (B <> nil required). *)
Fixpoint min_dist_sq_to (a : Point) (B : list Point) : R :=
  match B with
  | [] => 0
  | [b] => dist_sq a b
  | b :: B' => Rmin (dist_sq a b) (min_dist_sq_to a B')
  end.

(* The directed discrete Hausdorff value (squared convention):
   max over a in A of min_dist_sq_to a B. *)
Fixpoint directed_hausdorff_sq (A B : list Point) : R :=
  match A with
  | [] => 0
  | [a] => min_dist_sq_to a B
  | a :: A' => Rmax (min_dist_sq_to a B) (directed_hausdorff_sq A' B)
  end.

(* -------------------------------------------------------------------------- *)
(* The 423-a claim (RED: stated, not closed).                                 *)
(* h = directed_hausdorff_sq A B is exactly the attained max-min:             *)
(*   (cover)  h is big enough  -- every A-point is within h of B;             *)
(*   (attain) h is tight       -- some A-point is at distance >= h from       *)
(*                                every point of B.                           *)
(* -------------------------------------------------------------------------- *)

Definition directed_discrete_hausdorff_claim : Prop :=
  forall (A B : list Point),
    A <> nil ->
    B <> nil ->
    (forall a, In a A ->
       exists b, In b B /\ dist_sq a b <= directed_hausdorff_sq A B) /\
    (exists a, In a A /\
       forall b, In b B -> directed_hausdorff_sq A B <= dist_sq a b).

(* RED: no proof of the claim in this unit or in production.  Green must Qed
   `directed_discrete_hausdorff_max_min` with this statement (micro-kernel)
   and a production mirror (suggested theories/HausdorffDiscrete.v). *)

(* -------------------------------------------------------------------------- *)
(* Rational witness pins (Qed at Red).                                        *)
(* -------------------------------------------------------------------------- *)

(* All concrete computations reduce to Rmin/Rmax on rational literals;
   destructing the underlying Rle_dec closes every branch by lra. *)
Ltac crunch :=
  unfold Rmax, Rmin;
  repeat match goal with
         | |- context [Rle_dec ?x ?y] => destruct (Rle_dec x y)
         end;
  lra.

(* The plan's pair example: h = 1 in both directions (metric units 1). *)
Definition wA : list Point := [mkPoint 0 0; mkPoint 1 0].
Definition wB : list Point := [mkPoint 0 1; mkPoint 1 1].

Lemma w_pair_forward : directed_hausdorff_sq wA wB = 1.
Proof. unfold wA, wB; simpl; unfold dist_sq; simpl; crunch. Qed.

Lemma w_pair_backward : directed_hausdorff_sq wB wA = 1.
Proof. unfold wA, wB; simpl; unfold dist_sq; simpl; crunch. Qed.

(* The plan's asymmetric example: A' = [(0,0)], B' = [(0,2);(3,0)]
   (metric units: h(A',B') = 2, h(B',A') = 3; squared: 4 and 9). *)
Definition wA' : list Point := [mkPoint 0 0].
Definition wB' : list Point := [mkPoint 0 2; mkPoint 3 0].

(* MIN selected inside: the single A'-point takes its NEAREST B'-point
   (min(4,9) = 4).  A max-inside misreading would give 9. *)
Lemma w_asym_forward : directed_hausdorff_sq wA' wB' = 4.
Proof. unfold wA', wB'; simpl; unfold dist_sq; simpl; crunch. Qed.

(* MAX selected outside: the farther of the two B'-points dominates
   (max(4,9) = 9).  A min-outside misreading would give 4. *)
Lemma w_asym_backward : directed_hausdorff_sq wB' wA' = 9.
Proof. unfold wA', wB'; simpl; unfold dist_sq; simpl; crunch. Qed.

(* MISMATCH PROBE: the directed value is NOT symmetric -- refutes any
   symmetrised (max of both directions folded in, or swapped-argument)
   reading of the DIRECTED distance. *)
Lemma w_directed_not_symmetric :
  directed_hausdorff_sq wA' wB' <> directed_hausdorff_sq wB' wA'.
Proof. rewrite w_asym_forward, w_asym_backward. lra. Qed.

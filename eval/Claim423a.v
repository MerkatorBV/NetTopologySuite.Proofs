(* ============================================================================
   nts-eval micro unit — claimId 423-a (GREEN)
   Red planted 2026-08-02 (dbc6a00) · Green closed 2026-08-02
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

   GREEN.  The headline spec is stated
   (`directed_discrete_hausdorff_claim`) and CLOSED in this unit
   (`directed_discrete_hausdorff_max_min`, Qed).  The spec pins the
   computed value h = directed_hausdorff_sq A B from both sides on
   nonempty lists:
     (cover)  every a in A has some b in B with dist_sq a b <= h;
     (attain) some a in A has dist_sq a b >= h against EVERY b in B.
   Together these say h is exactly the attained max-min.  The proof is
   four list inductions over Rmin/Rmax (min attained / min lower bound /
   max upper bound / max attained); no sqrt anywhere.  Production home:
   `theories/HausdorffDiscrete.v` over the corpus Point/dist_sq
   vocabulary, same WITNESS tag.  Red history: claim planted 2026-08-02
   with only the witness pins Qed; Green closed it the same day.

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
   topic: metric
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

(* GREEN: the claim is closed here (self-contained) and mirrored in
   production over the corpus Point/dist_sq vocabulary
   (theories/HausdorffDiscrete.v, same WITNESS tag). *)

(* One-step unfolding equations (by conversion), so the cons cases can be
   opened without disturbing the folded inner calls. *)
Lemma min_dist_sq_to_step : forall a b0 b1 B'',
    min_dist_sq_to a (b0 :: b1 :: B'')
    = Rmin (dist_sq a b0) (min_dist_sq_to a (b1 :: B'')).
Proof. reflexivity. Qed.

Lemma ddh_step : forall a0 a1 A'' B,
    directed_hausdorff_sq (a0 :: a1 :: A'') B
    = Rmax (min_dist_sq_to a0 B) (directed_hausdorff_sq (a1 :: A'') B).
Proof. reflexivity. Qed.

(* The inner min is a lower bound on every candidate distance. *)
Lemma min_dist_sq_to_le : forall a B b,
    In b B -> min_dist_sq_to a B <= dist_sq a b.
Proof.
  intros a B. induction B as [ | b0 B' IH ]; intros b Hin.
  - destruct Hin.
  - destruct Hin as [-> | Hin].
    + destruct B' as [ | b1 B'' ]; [ apply Rle_refl | ].
      rewrite min_dist_sq_to_step. apply Rmin_l.
    + destruct B' as [ | b1 B'' ]; [ destruct Hin | ].
      rewrite min_dist_sq_to_step.
      eapply Rle_trans; [ apply Rmin_r | ]. apply IH. exact Hin.
Qed.

(* ... and it is attained on a nonempty list. *)
Lemma min_dist_sq_to_attained : forall a B,
    B <> nil -> exists b, In b B /\ min_dist_sq_to a B = dist_sq a b.
Proof.
  intros a B. induction B as [ | b0 B' IH ]; intros Hne.
  - congruence.
  - destruct B' as [ | b1 B'' ].
    + exists b0. split; [ left; reflexivity | reflexivity ].
    + destruct IH as [b [Hb Heq]]; [ discriminate | ].
      rewrite min_dist_sq_to_step.
      destruct (Rle_dec (dist_sq a b0) (min_dist_sq_to a (b1 :: B'')))
        as [Hle | Hgt].
      * exists b0. split; [ left; reflexivity | ].
        rewrite Rmin_left; [ reflexivity | exact Hle ].
      * apply Rnot_le_lt in Hgt.
        exists b. split; [ right; exact Hb | ].
        rewrite Rmin_right; [ exact Heq | lra ].
Qed.

(* The outer max dominates every per-point min. *)
Lemma ddh_ge_component : forall A B a,
    In a A -> min_dist_sq_to a B <= directed_hausdorff_sq A B.
Proof.
  intros A B. induction A as [ | a0 A' IH ]; intros a Hin.
  - destruct Hin.
  - destruct Hin as [-> | Hin].
    + destruct A' as [ | a1 A'' ]; [ apply Rle_refl | ].
      rewrite ddh_step. apply Rmax_l.
    + destruct A' as [ | a1 A'' ]; [ destruct Hin | ].
      rewrite ddh_step.
      eapply Rle_trans; [ apply IH; exact Hin | apply Rmax_r ].
Qed.

(* ... and it is attained on a nonempty list. *)
Lemma ddh_attained : forall A B,
    A <> nil ->
    exists a, In a A /\ directed_hausdorff_sq A B = min_dist_sq_to a B.
Proof.
  intros A B. induction A as [ | a0 A' IH ]; intros Hne.
  - congruence.
  - destruct A' as [ | a1 A'' ].
    + exists a0. split; [ left; reflexivity | reflexivity ].
    + destruct IH as [a [Ha Heq]]; [ discriminate | ].
      rewrite ddh_step.
      destruct (Rle_dec (directed_hausdorff_sq (a1 :: A'') B)
                        (min_dist_sq_to a0 B)) as [Hle | Hgt].
      * exists a0. split; [ left; reflexivity | ].
        rewrite Rmax_left; [ reflexivity | exact Hle ].
      * apply Rnot_le_lt in Hgt.
        exists a. split; [ right; exact Ha | ].
        rewrite Rmax_right; [ exact Heq | lra ].
Qed.

Lemma directed_discrete_hausdorff_max_min :
  directed_discrete_hausdorff_claim.
Proof.
  unfold directed_discrete_hausdorff_claim.
  intros A B HA HB. split.
  - (* cover: route each a through its attained nearest b *)
    intros a Hin.
    destruct (min_dist_sq_to_attained a B HB) as [b [Hb Heq]].
    exists b. split; [ exact Hb | ].
    rewrite <- Heq. apply ddh_ge_component. exact Hin.
  - (* attain: the arg-max vertex beats every b in B *)
    destruct (ddh_attained A B HA) as [a [Ha Heq]].
    exists a. split; [ exact Ha | ].
    intros b Hb. rewrite Heq. apply min_dist_sq_to_le. exact Hb.
Qed.

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

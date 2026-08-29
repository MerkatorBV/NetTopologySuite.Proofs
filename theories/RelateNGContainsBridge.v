(* ============================================================================
   NetTopologySuite.Proofs.RelateNGContainsBridge
   ----------------------------------------------------------------------------
   Issue #567 / #522 claimId 522-a remaining core slice: the detector →
   predicate bridge for TPR_Contains.

   `contains_b` (RelateNGCore) is a strict-vertex detector that guards only
   A's orientation.  `triangle_a_contains_b` (RelateMatrixTriangle) is
   CLOSED containment of B's filled region in A's, with BOTH triangles
   guarded CCW.  #579 deliberately left the implication unclaimed.

   Green (all Qed):
     - honesty pin: `contains_b` alone does NOT imply
       `triangle_a_contains_b`.  A = (0,0)(4,0)(0,4) CCW vs
       B = (1,1)(1,2)(2,1) CW: every B-vertex is strictly interior to A,
       so the detector fires, but B fails the predicate's CCW guard.
     - bridge: `contains_b` plus B CCW (`0 < gdbl B`) imply
       `triangle_a_contains_b`.  A point of B's closed region has
       nonnegative barycentric weights summing to `gdbl B > 0`; each
       edge slack of A is affine, so the three slacks at that point are
       the same-weight averages of the slacks at B's vertices; those
       vertices sit in A's closed region by `contains_b`.  This is the
       3-point convexity lift (`Convex.is_convex` is 2-point only).

   Not claimed:
     - `TPR_TouchEdge` exclusivity vs the four gtri predicates
       (still "not a cheap consequence"; later #567 leftover)
     - a remint of `aa_matrix_contains` / IB dim (open in
       RelateNGContains)
     - classifier-order changes, leftover certificates, ADR-0004

   Frozen anchors untouched.  Not an ADR-0004 remint.  `522-a` is the
   existing #567 ticket id (same letter as #579; this is the deferred
   slice, not a new letter).

   WITNESS topic: relate · claimId: 522-a · witness: 522-a-contains-bridge
   macro: relate
   lane: proofs
   issue: #567 / #522
   ADR-0004: not a remint. 522-a is the existing #567 ticket id.

   No `Admitted`, no `Axiom`, no `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Agent
   ========================================================================== *)

(* WITNESS {"claimId":"522-a","topic":"relate","lemma":"contains_b_ccw_implies_closed_containment","title":"contains_b plus B CCW lifts to closed triangle_a_contains_b","file":"theories/RelateNGContainsBridge.v","witness":"522-a-contains-bridge","board":"#567"} *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import Distance
  GeneralTriangleSeparation
  RelateMatrixTriangle
  RelateNGCore.

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* Detector unpack / pack.                                                    *)
(* -------------------------------------------------------------------------- *)

Lemma contains_b_unpack :
  forall ax ay bx by_ cx cy dx dy ex ey fx fy,
    contains_b ax ay bx by_ cx cy dx dy ex ey fx fy = true ->
    0 < gdbl ax ay bx by_ cx cy /\
    0 < gtri ax ay bx by_ cx cy (mkPoint dx dy) /\
    0 < gtri ax ay bx by_ cx cy (mkPoint ex ey) /\
    0 < gtri ax ay bx by_ cx cy (mkPoint fx fy).
Proof.
  intros ax ay bx by_ cx cy dx dy ex ey fx fy Hc.
  unfold contains_b in Hc.
  destruct (Rlt_dec 0 (gdbl ax ay bx by_ cx cy)) as [HA | _]; [ | discriminate ].
  destruct (Rlt_dec 0 (gtri ax ay bx by_ cx cy (mkPoint dx dy))) as [Hd | _]; [ | discriminate ].
  destruct (Rlt_dec 0 (gtri ax ay bx by_ cx cy (mkPoint ex ey))) as [He | _]; [ | discriminate ].
  destruct (Rlt_dec 0 (gtri ax ay bx by_ cx cy (mkPoint fx fy))) as [Hf | _]; [ | discriminate ].
  repeat split; assumption.
Qed.

Lemma contains_b_of_strict :
  forall ax ay bx by_ cx cy dx dy ex ey fx fy,
    0 < gdbl ax ay bx by_ cx cy ->
    0 < gtri ax ay bx by_ cx cy (mkPoint dx dy) ->
    0 < gtri ax ay bx by_ cx cy (mkPoint ex ey) ->
    0 < gtri ax ay bx by_ cx cy (mkPoint fx fy) ->
    contains_b ax ay bx by_ cx cy dx dy ex ey fx fy = true.
Proof.
  intros ax ay bx by_ cx cy dx dy ex ey fx fy HA Hd He Hf.
  unfold contains_b.
  destruct (Rlt_dec 0 (gdbl ax ay bx by_ cx cy)) as [_ | Hn]; [ | contradiction ].
  destruct (Rlt_dec 0 (gtri ax ay bx by_ cx cy (mkPoint dx dy))) as [_ | Hn]; [ | contradiction ].
  destruct (Rlt_dec 0 (gtri ax ay bx by_ cx cy (mkPoint ex ey))) as [_ | Hn]; [ | contradiction ].
  destruct (Rlt_dec 0 (gtri ax ay bx by_ cx cy (mkPoint fx fy))) as [_ | Hn]; [ | contradiction ].
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Honesty pin: the detector does not by itself entail the predicate.         *)
(*                                                                            *)
(* A = (0,0)(4,0)(0,4) CCW.  B = (1,1)(1,2)(2,1) CW.  Each B-vertex has       *)
(* gtri A = 4 > 0, so `contains_b` fires.  `triangle_a_contains_b` fails on    *)
(* the B-side CCW guard (`gdbl B = -1`).  The geometric inclusion of B's      *)
(* `{0 <= gtri}` region in A is then vacuous (three slacks summing to a       *)
(* negative area cannot all be nonnegative), which is exactly why the guard   *)
(* is there.                                                                  *)
(* -------------------------------------------------------------------------- *)

Lemma cw_B_inside_A_contains_b :
  contains_b 0 0 4 0 0 4 1 1 1 2 2 1 = true.
Proof.
  apply contains_b_of_strict.
  - unfold gdbl; lra.
  - apply gtri_pos_iff; unfold gsA, gsB, gsC; cbn [px py]; repeat split; lra.
  - apply gtri_pos_iff; unfold gsA, gsB, gsC; cbn [px py]; repeat split; lra.
  - apply gtri_pos_iff; unfold gsA, gsB, gsC; cbn [px py]; repeat split; lra.
Qed.

Lemma cw_B_inside_A_not_closed_containment :
  ~ triangle_a_contains_b
      (mkPoint 0 0) (mkPoint 4 0) (mkPoint 0 4)
      (mkPoint 1 1) (mkPoint 1 2) (mkPoint 2 1).
Proof.
  intros [HA [HB _]].
  unfold tri_ccw, gdbl in HB. cbn [px py] in HB. lra.
Qed.

Theorem contains_b_not_enough_for_closed_containment :
  contains_b 0 0 4 0 0 4 1 1 1 2 2 1 = true /\
  ~ triangle_a_contains_b
      (mkPoint 0 0) (mkPoint 4 0) (mkPoint 0 4)
      (mkPoint 1 1) (mkPoint 1 2) (mkPoint 2 1).
Proof.
  split.
  - exact cw_B_inside_A_contains_b.
  - exact cw_B_inside_A_not_closed_containment.
Qed.

(* -------------------------------------------------------------------------- *)
(* Affine 3-point identities for A's edge slacks, against B's barycentric     *)
(* weights.  `g_baryx` / `g_baryy` / `g_sum` on B say                        *)
(*   pt = (gsB_B · D + gsC_B · E + gsA_B · F) / gdbl B                       *)
(* and each slack of A is affine in (px, py), so the slack at pt is the       *)
(* same-weight average of the slacks at D, E, F.                              *)
(* -------------------------------------------------------------------------- *)

Lemma gsA_barycentric :
  forall ax ay bx by_ dx dy ex ey fx fy pt,
    gsA ax ay bx by_ pt * gdbl dx dy ex ey fx fy
    = gsB ex ey fx fy pt * gsA ax ay bx by_ (mkPoint dx dy)
    + gsC dx dy fx fy pt * gsA ax ay bx by_ (mkPoint ex ey)
    + gsA dx dy ex ey pt * gsA ax ay bx by_ (mkPoint fx fy).
Proof.
  intros ax ay bx by_ dx dy ex ey fx fy pt.
  unfold gsA, gsB, gsC, gdbl. cbn [px py]. ring.
Qed.

Lemma gsB_barycentric :
  forall bx by_ cx cy dx dy ex ey fx fy pt,
    gsB bx by_ cx cy pt * gdbl dx dy ex ey fx fy
    = gsB ex ey fx fy pt * gsB bx by_ cx cy (mkPoint dx dy)
    + gsC dx dy fx fy pt * gsB bx by_ cx cy (mkPoint ex ey)
    + gsA dx dy ex ey pt * gsB bx by_ cx cy (mkPoint fx fy).
Proof.
  intros bx by_ cx cy dx dy ex ey fx fy pt.
  unfold gsA, gsB, gsC, gdbl. cbn [px py]. ring.
Qed.

Lemma gsC_barycentric :
  forall ax ay cx cy dx dy ex ey fx fy pt,
    gsC ax ay cx cy pt * gdbl dx dy ex ey fx fy
    = gsB ex ey fx fy pt * gsC ax ay cx cy (mkPoint dx dy)
    + gsC dx dy fx fy pt * gsC ax ay cx cy (mkPoint ex ey)
    + gsA dx dy ex ey pt * gsC ax ay cx cy (mkPoint fx fy).
Proof.
  intros ax ay cx cy dx dy ex ey fx fy pt.
  unfold gsA, gsB, gsC, gdbl. cbn [px py]. ring.
Qed.

Lemma Rmult_nonneg_reg_pos :
  forall a b, 0 < b -> 0 <= a * b -> 0 <= a.
Proof. intros a b Hb Hab; nra. Qed.

(* Closed B ⊂ closed A, once B is CCW (so its closed region is the convex
   hull of its vertices) and those vertices lie in closed A. *)
Lemma closed_A_of_closed_B_vertices :
  forall ax ay bx by_ cx cy dx dy ex ey fx fy pt,
    0 < gdbl dx dy ex ey fx fy ->
    0 <= gtri ax ay bx by_ cx cy (mkPoint dx dy) ->
    0 <= gtri ax ay bx by_ cx cy (mkPoint ex ey) ->
    0 <= gtri ax ay bx by_ cx cy (mkPoint fx fy) ->
    0 <= gtri dx dy ex ey fx fy pt ->
    0 <= gtri ax ay bx by_ cx cy pt.
Proof.
  intros ax ay bx by_ cx cy dx dy ex ey fx fy pt HB Hd He Hf Hpt.
  apply gtri_nonneg_iff in Hd as [HdA [HdB HdC]].
  apply gtri_nonneg_iff in He as [HeA [HeB HeC]].
  apply gtri_nonneg_iff in Hf as [HfA [HfB HfC]].
  apply gtri_nonneg_iff in Hpt as [HpA [HpB HpC]].
  apply gtri_nonneg_iff.
  pose proof (gsA_barycentric ax ay bx by_ dx dy ex ey fx fy pt) as EA.
  pose proof (gsB_barycentric bx by_ cx cy dx dy ex ey fx fy pt) as EB.
  pose proof (gsC_barycentric ax ay cx cy dx dy ex ey fx fy pt) as EC.
  repeat split.
  - apply (Rmult_nonneg_reg_pos _ _ HB). rewrite EA. nra.
  - apply (Rmult_nonneg_reg_pos _ _ HB). rewrite EB. nra.
  - apply (Rmult_nonneg_reg_pos _ _ HB). rewrite EC. nra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Headline: detector + B CCW ⇒ closed-containment predicate.                 *)
(* -------------------------------------------------------------------------- *)

Theorem contains_b_ccw_implies_closed_containment :
  forall ax ay bx by_ cx cy dx dy ex ey fx fy,
    contains_b ax ay bx by_ cx cy dx dy ex ey fx fy = true ->
    0 < gdbl dx dy ex ey fx fy ->
    triangle_a_contains_b
      (mkPoint ax ay) (mkPoint bx by_) (mkPoint cx cy)
      (mkPoint dx dy) (mkPoint ex ey) (mkPoint fx fy).
Proof.
  intros ax ay bx by_ cx cy dx dy ex ey fx fy Hc HB.
  apply contains_b_unpack in Hc as [HA [Hd [He Hf]]].
  unfold triangle_a_contains_b, tri_ccw, in_tri_closure.
  cbn [px py].
  split; [ exact HA | split; [ exact HB | ] ].
  intros pt Hpt.
  exact (closed_A_of_closed_B_vertices ax ay bx by_ cx cy dx dy ex ey fx fy pt
           HB (Rlt_le _ _ Hd) (Rlt_le _ _ He) (Rlt_le _ _ Hf) Hpt).
Qed.

Print Assumptions contains_b_not_enough_for_closed_containment.
Print Assumptions contains_b_ccw_implies_closed_containment.

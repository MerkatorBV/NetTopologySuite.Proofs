(* ============================================================================
   NetTopologySuite.Proofs.DelaunayFlipWitness
   ----------------------------------------------------------------------------
   Issue #68 ask #2 (RGR pivot from ask #1): the sign-algebra layer under the
   witness-sound flip.  `inCircle_R` is, up to the fixed translation-to-P
   convention documented in `ArcOrient.v`, the 4x4 lifted-paraboloid
   determinant of (A, B, C, P) in row order (Shewchuk 1997 / Guibas-Stolfi);
   a determinant is fully alternating under row transposition, so
   `inCircle_R` is fully antisymmetric under transposing ANY two of its four
   point arguments -- not just the three "triangle" arguments (mirroring
   `Orientation.cross`'s swap/cyclic lemmas on 3 points), but also swapping
   the distinguished 4th ("test point") argument with any of the first
   three.

   That last family is the one with real content for flip reasoning: it is
   exactly what lets you relate "is D inside circle(A,B,C)" to "is C inside
   circle(A,B,D)" -- the two candidate triangles of a shared-edge quad -- as
   a SINGLE algebraic fact, regardless of which triangle you nominally test
   from.

   RGR round 2: composing the test-point swap with the A/B swap cancels the
   double negation, sharpening "related by a sign flip" into flatly EQUAL --
   `inCircle_R A B C D = inCircle_R B A D C` unconditionally, no orientation
   hypothesis needed.  This is the algebraic core of "the flip test doesn't
   care which of the two candidate triangles you evaluate it from".

   Scope note (mirrors `DelaunayEmptyCircle.v`'s own deferral): this file is
   pure sign algebra, `ring`-closed, with no orientation (`triangle_ccw`)
   hypotheses anywhere.  Turning the swap identity into a genuine geometric
   "flip refutes Delaunayhood" statement needs the CCW bookkeeping for BOTH
   triangles of the shared-edge quad and is deliberately left as follow-up
   work, not attempted here.

   No `Admitted`, no `Axiom`, no `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals.
From Stdlib Require Import Lra.
From NTS.Proofs Require Import Distance ArcOrient.

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* Antisymmetry / cyclic invariance among the three "triangle" arguments,     *)
(* mirroring `Orientation.cross_swap_first_two` / `cross_antisymmetric` /     *)
(* `cross_cyclic`.                                                            *)
(* -------------------------------------------------------------------------- *)

Lemma inCircle_R_swap_AB : forall A B C P,
  inCircle_R A B C P = - inCircle_R B A C P.
Proof. intros. unfold inCircle_R. ring. Qed.

Lemma inCircle_R_swap_BC : forall A B C P,
  inCircle_R A B C P = - inCircle_R A C B P.
Proof. intros. unfold inCircle_R. ring. Qed.

Lemma inCircle_R_swap_AC : forall A B C P,
  inCircle_R A B C P = - inCircle_R C B A P.
Proof. intros. unfold inCircle_R. ring. Qed.

Lemma inCircle_R_cyclic : forall A B C P,
  inCircle_R A B C P = inCircle_R B C A P.
Proof. intros. unfold inCircle_R. ring. Qed.

(* -------------------------------------------------------------------------- *)
(* The deep swap: transposing the test point with a triangle vertex.          *)
(* -------------------------------------------------------------------------- *)

Lemma inCircle_R_swap_CP : forall A B C P,
  inCircle_R A B C P = - inCircle_R A B P C.
Proof. intros. unfold inCircle_R. ring. Qed.

(* -------------------------------------------------------------------------- *)
(* The witness: for the shared-edge quad (A, B fixed; C, D the two           *)
(* candidate opposite vertices), a strict empty-circle violation from one    *)
(* triangle's perspective pins the sign of the OTHER triangle's test         *)
(* exactly -- not just "the two tests can disagree", but the precise value   *)
(* the swap forces.  (`0 < inCircle_R A B C D` is exactly what               *)
(* `DelaunayEmptyCircle.in_circle_test A B C D` unfolds to; stated directly  *)
(* here to keep this file's `theories/` layer independent of the Flocq-      *)
(* bridged `theories-flocq/DelaunayEmptyCircle.v`.)                          *)
(* -------------------------------------------------------------------------- *)

Corollary inCircle_R_flip_witness : forall A B C D,
  0 < inCircle_R A B C D -> inCircle_R A B D C < 0.
Proof.
  intros A B C D H.
  rewrite inCircle_R_swap_CP in H.
  lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* RGR pivot (round 2): composing `inCircle_R_swap_CP` with `inCircle_R_swap_AB`  *)
(* cancels the double negation, for a SHARPER, unconditional fact -- not just  *)
(* related-by-sign-flip but flatly EQUAL: testing D against circle(A,B,C) is  *)
(* the exact same value as testing C against circle(B,A,D).  Read as: the     *)
(* flip test is well-defined regardless of which of the two candidate         *)
(* triangles, in its own CCW listing, you evaluate it from.  Still zero       *)
(* orientation hypotheses, still `ring`-closed.                              *)
(* -------------------------------------------------------------------------- *)

Lemma inCircle_R_double_swap : forall A B C D,
  inCircle_R A B C D = inCircle_R B A D C.
Proof. intros. unfold inCircle_R. ring. Qed.

Corollary inCircle_R_flip_witness_iff : forall A B C D,
  0 < inCircle_R A B C D <-> 0 < inCircle_R B A D C.
Proof. intros. rewrite inCircle_R_double_swap. tauto. Qed.
Print Assumptions inCircle_R_double_swap.
Print Assumptions inCircle_R_flip_witness_iff.

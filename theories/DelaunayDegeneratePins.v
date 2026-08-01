(* ============================================================================
   NetTopologySuite.Proofs.DelaunayDegeneratePins
   ----------------------------------------------------------------------------
   Degenerate-case adversarial pins for the Delaunay lane (#68, round-2
   item 2): the single-triangle input of JTS#1190 and the 4-point
   cocircular input of JTS#1039, as concrete Qed instances over the exact
   in-circle determinant `inCircle_R` (ArcOrient.v).

   WHY THESE TWO.  They are the two degeneracies JTS/NTS triangulation
   actually stumbles on in the field:

     - JTS#1190: ConformingDelaunayTriangulationBuilder produces a poor
       triangulation when the input is a SINGLE TRIANGLE.  The discrete
       truth the implementation must respect: a lone triangle is
       unconditionally Delaunay over its own vertex set -- each vertex lies
       ON (never strictly inside) the circumcircle.  We prove the general
       algebraic fact behind that (`inCircle_R` vanishes whenever the query
       point is one of the triangle's vertices -- a pure ring identity, no
       hypotheses) and package it as the no-violation statement.

     - JTS#1039: incorrect Voronoi for 4 points.  The hard configuration is
       COCIRCULAR points: the in-circle determinant is exactly 0, both
       diagonal choices of the quad are ties, and the flip decision is
       genuinely arbitrary -- floating-point implementations near this
       knife edge disagree with themselves.  We pin the square
       (0,0),(2,0),(2,2),(0,2): determinant exactly 0 for BOTH diagonals,
       the strict flip-witness precondition (`0 < inCircle_R`, the guard of
       DelaunayFlipWitness/DelaunayFlipGeometric) correctly EXCLUDES the
       tie, and the tie is knife-edge: moving the fourth point in by 1/2
       gives +3, out by 1/2 gives -5.

   These are the adversarial vectors the `INCIRCLE_SIGN` /
   `DELAUNAY_WITNESS` oracle modes should carry: exact rational inputs
   whose certified signs (+, 0, -) bracket the degeneracy.

   No `Admitted`, no `Axiom`, no `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import Distance Orientation ArcOrient.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  The general fact behind JTS#1190: a triangle's own vertices are ON     *)
(*     its circumcircle -- the in-circle determinant vanishes identically     *)
(*     when the query point is a vertex.  Pure ring identities.               *)
(* -------------------------------------------------------------------------- *)

Lemma inCircle_R_at_vertex_A : forall A B C, inCircle_R A B C A = 0.
Proof. intros. unfold inCircle_R. ring. Qed.

Lemma inCircle_R_at_vertex_B : forall A B C, inCircle_R A B C B = 0.
Proof. intros. unfold inCircle_R. ring. Qed.

Lemma inCircle_R_at_vertex_C : forall A B C, inCircle_R A B C C = 0.
Proof. intros. unfold inCircle_R. ring. Qed.

(* JTS#1190 pin, general form: over its own vertex set, a single triangle
   admits NO strict empty-circle violation -- it is unconditionally
   Delaunay.  (The builder's job on such input is to return the triangle
   unchanged; any "improvement" it attempts is working against a zero.) *)
Theorem single_triangle_delaunay :
  forall A B C P,
    (P = A \/ P = B \/ P = C) ->
    ~ 0 < inCircle_R A B C P.
Proof.
  intros A B C P [-> | [-> | ->]].
  - rewrite inCircle_R_at_vertex_A. lra.
  - rewrite inCircle_R_at_vertex_B. lra.
  - rewrite inCircle_R_at_vertex_C. lra.
Qed.

(* Concrete nondegenerate instance for the oracle gallery: the 4-0-4 right
   triangle is genuinely a triangle (CCW, cross = 16), so the theorem above
   is not vacuous on it. *)
Example single_triangle_pin_1190 :
  cross (mkPoint 0 0) (mkPoint 4 0) (mkPoint 0 4) = 16 /\
  inCircle_R (mkPoint 0 0) (mkPoint 4 0) (mkPoint 0 4) (mkPoint 0 0) = 0 /\
  inCircle_R (mkPoint 0 0) (mkPoint 4 0) (mkPoint 0 4) (mkPoint 4 0) = 0 /\
  inCircle_R (mkPoint 0 0) (mkPoint 4 0) (mkPoint 0 4) (mkPoint 0 4) = 0.
Proof.
  unfold cross, inCircle_R; simpl. repeat split; lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  JTS#1039 pin: the 4-point cocircular tie.                              *)
(*                                                                            *)
(* Square corners A=(0,0), B=(2,0), C=(2,2), D=(0,2), all on the circle       *)
(* centred (1,1).  The quad's two triangulations differ by the diagonal       *)
(* choice; the in-circle determinant is EXACTLY zero for both, so neither     *)
(* flip direction is justified -- the configuration every implementation      *)
(* must treat as a tie, not a signal.                                         *)
(* -------------------------------------------------------------------------- *)

Definition p1039_A : Point := mkPoint 0 0.
Definition p1039_B : Point := mkPoint 2 0.
Definition p1039_C : Point := mkPoint 2 2.
Definition p1039_D : Point := mkPoint 0 2.

(* The square is a genuine CCW quad (both triangles nondegenerate). *)
Example cocircular_square_ccw :
  cross p1039_A p1039_B p1039_C = 4 /\
  cross p1039_A p1039_C p1039_D = 4.
Proof.
  unfold cross, p1039_A, p1039_B, p1039_C, p1039_D; simpl.
  split; lra.
Qed.

(* The tie itself: determinant exactly 0 for BOTH diagonal choices. *)
Theorem cocircular_square_tie_1039 :
  inCircle_R p1039_A p1039_B p1039_C p1039_D = 0 /\
  inCircle_R p1039_A p1039_B p1039_D p1039_C = 0.
Proof.
  unfold inCircle_R, p1039_A, p1039_B, p1039_C, p1039_D; simpl.
  split; lra.
Qed.

(* The strict flip-witness guard (0 < inCircle_R, as consumed by
   DelaunayFlipWitness / DelaunayFlipGeometric) correctly EXCLUDES the tie:
   on cocircular input no flip is certified in either direction.  JTS#1039's
   failure mode lives exactly on this boundary -- a float implementation
   that resolves the 0 to a tiny nonzero sign flips arbitrarily. *)
Corollary cocircular_tie_no_flip_witness :
  ~ 0 < inCircle_R p1039_A p1039_B p1039_C p1039_D /\
  ~ 0 < inCircle_R p1039_A p1039_B p1039_D p1039_C.
Proof.
  destruct cocircular_square_tie_1039 as [H1 H2].
  rewrite H1, H2. split; lra.
Qed.

(* The tie is knife-edge: perturbing the fourth point by 1/2 in either
   radial direction produces certified nonzero signs.  D_in = (0, 3/2) is
   strictly inside (+3); D_out = (0, 5/2) is strictly outside (-5).  These
   bracket the degeneracy for the oracle's adversarial vectors. *)
Theorem cocircular_tie_is_knife_edge :
  inCircle_R p1039_A p1039_B p1039_C (mkPoint 0 (3/2)) = 3 /\
  inCircle_R p1039_A p1039_B p1039_C (mkPoint 0 (5/2)) = -5.
Proof.
  unfold inCircle_R, p1039_A, p1039_B, p1039_C; simpl.
  split; lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Audit footprint.                                                       *)
(* -------------------------------------------------------------------------- *)

(* WITNESS {"claimId":"68-c","topic":"mesh","lemma":"cocircular_square_tie_1039","title":"Degenerate pins: single-triangle no-violation + cocircular tie (JTS#1190/#1039)","file":"theories/DelaunayDegeneratePins.v"} *)

Print Assumptions single_triangle_delaunay.
Print Assumptions cocircular_square_tie_1039.
Print Assumptions cocircular_tie_is_knife_edge.

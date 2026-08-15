(* ============================================================================
   NetTopologySuite.Proofs.Flocq.DelaunayEmptyCircle
   ----------------------------------------------------------------------------
   Issue #68 ask #1: the empty-circle (Delaunay) predicate, and its bridge to
   the discrete `b64_inCircle_exact` decision layer.

   Sign convention (per `ArcOrient.v`'s documented Shewchuk 1997 / Guibas-Stolfi
   convention): for a CCW-oriented triangle (A, B, C) -- i.e.
   `0 < area2 (mkTriangle A B C)` -- `inCircle_R A B C P` is positive exactly
   when P lies inside the circumscribed circle.  `in_circle_test` names that
   sign condition directly; `triangle_ccw` names the orientation hypothesis
   under which "empty circle" is the correct reading of a positive sign
   (ties into `Triangle.v`'s signed-area algebra, as the issue's recommended
   first slice asks).  This file does not attempt the (much larger) geometric
   proof that the sign literally characterises circle membership -- that is
   future work; here we only fix the predicate and connect it to the already
   Qed-closed discrete oracle `b64_inCircle_exact_sound` (#64, PR #146).

   No `Admitted`, no `Axiom`, no `Parameter`.

   Reference: J.R. Shewchuk, "Adaptive Precision Floating-Point Arithmetic
   and Fast Robust Geometric Predicates", Discrete & Computational Geometry
   18(3), 1997, §3 (the `incircle` predicate).

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   topic: mesh
   claimId: 68-a
   witness: empty-circle
   ========================================================================== *)

From Stdlib Require Import Reals ZArith.
From NTS.Proofs        Require Import Distance Orientation Triangle ArcOrient.
From NTS.Proofs.Flocq  Require Import Validate_binary64 Intersect_b64
                                      InCircle_b64_exact.

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* The empty-circle sign predicate and its orientation precondition.          *)
(* -------------------------------------------------------------------------- *)

Definition in_circle_test (A B C P : Point) : Prop :=
  0 < inCircle_R A B C P.

Definition triangle_ccw (A B C : Point) : Prop :=
  0 < area2 (mkTriangle A B C).

(* -------------------------------------------------------------------------- *)
(* Bridge to the discrete decision layer: the R-side sign trichotomy of       *)
(* `inCircle_R` on BPoint-decoded vertices agrees with `b64_inCircle_exact`'s *)
(* Z.sgn trichotomy, for any finite input octuple.  Direct transport of       *)
(* `b64_inCircle_exact_sound` along `inCircle_R_BP_eq_inCircle_BP2P`.         *)
(* -------------------------------------------------------------------------- *)

Theorem inCircle_R_BP2P_sign_char :
  forall A B C P : BPoint,
    all_finite8 A B C P ->
    (0 < inCircle_R (BP2P A) (BP2P B) (BP2P C) (BP2P P)
       <-> b64_inCircle_exact A B C P = 1%Z) /\
    (inCircle_R (BP2P A) (BP2P B) (BP2P C) (BP2P P) < 0
       <-> b64_inCircle_exact A B C P = (-1)%Z) /\
    (inCircle_R (BP2P A) (BP2P B) (BP2P C) (BP2P P) = 0
       <-> b64_inCircle_exact A B C P = 0%Z).
Proof.
  intros A B C P Hfin.
  rewrite <- !inCircle_R_BP_eq_inCircle_BP2P.
  exact (b64_inCircle_exact_sound A B C P Hfin).
Qed.

Theorem in_circle_test_iff_b64_inCircle_exact_pos :
  forall A B C P : BPoint,
    all_finite8 A B C P ->
    in_circle_test (BP2P A) (BP2P B) (BP2P C) (BP2P P)
      <-> b64_inCircle_exact A B C P = 1%Z.
Proof.
  intros A B C P Hfin.
  unfold in_circle_test.
  apply (inCircle_R_BP2P_sign_char A B C P Hfin).
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)
Print Assumptions inCircle_R_BP2P_sign_char.
Print Assumptions in_circle_test_iff_b64_inCircle_exact_pos.

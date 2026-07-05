(* ============================================================================
   NetTopologySuite.Proofs.DelaunayFlipGeometric
   ----------------------------------------------------------------------------
   Issue #68 ask #2, geometric layer: `DelaunayFlipWitness.v` proved the flip
   test's sign algebra is well-defined regardless of which candidate triangle
   evaluates it (`inCircle_R_flip_witness_iff`), but deliberately deferred
   turning that into a genuine geometric fact -- it needed CCW bookkeeping for
   BOTH triangles of the shared-edge quad, which that file's own scope note
   explicitly left as follow-up work.  This file closes that gap.

   Setup: two triangles ABC and ABD share edge AB, with C and D the two
   candidate opposite vertices, strictly on opposite sides of AB (`opposite_sides`,
   reused read-only from the parallel #67 RelateNG track's
   `theories/RelateMatrixTriangle.v` -- a two-line Prop, `cross p1 p2 p *
   cross p1 p2 q < 0`; not modified here, just imported).  Given ABC is CCW
   (`0 < cross A B C`) and D violates ABC's empty-circle test
   (`0 < inCircle_R A B C D`, i.e. `DelaunayEmptyCircle.in_circle_test A B C D`
   unfolded), the headline shows this is not a one-sided fact: BAD is CCW too,
   and C simultaneously violates BAD's own empty-circle test.  Both candidate
   triangles fail to be locally Delaunay at once -- the real content behind
   "the flip is required".

   No new machinery: `opposite_sides` (RelateMatrixTriangle.v) plus one `nra`
   step recovers the sign of `cross A B D` from `cross A B C`'s positivity;
   `cross_swap_first_two` (Orientation.v) converts that into BAD's own CCW
   witness; `inCircle_R_flip_witness_iff` (DelaunayFlipWitness.v) transports
   the violation across the flip for free.

   Scope note: kept in `theories/`, not `theories-flocq/`, matching
   `DelaunayFlipWitness.v`'s own choice to stay Flocq-independent -- stated in
   raw `cross`/`inCircle_R` terms, not the `in_circle_test`/`triangle_ccw`
   names.  A `theories-flocq/` corollary bridging to those named Props, the
   symmetric mirror-direction theorem, and a `~(both locally Delaunay)`
   corollary are all cheap follow-ups, deliberately not attempted here.

   No `Admitted`, no `Axiom`, no `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals.
From Stdlib Require Import Lra.
From NTS.Proofs Require Import Distance Orientation ArcOrient RelateMatrixTriangle
                               DelaunayFlipWitness.

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* CCW-transport across the shared edge: if ABC is CCW and C, D are on        *)
(* opposite sides of AB, then BAD is CCW too.                                 *)
(* -------------------------------------------------------------------------- *)

Lemma cross_BAD_ccw_of_opposite_sides : forall A B C D,
  0 < cross A B C ->
  opposite_sides A B C D ->
  0 < cross B A D.
Proof.
  intros A B C D Hccw Hopp.
  unfold opposite_sides in Hopp; cbv zeta in Hopp.
  assert (Hcabd : cross A B D < 0) by nra.
  rewrite (cross_swap_first_two A B D) in Hcabd.
  lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* The headline: composing the CCW-transport with the already-Qed'd           *)
(* `inCircle_R_flip_witness_iff`.  Both candidate triangles of the            *)
(* shared-edge quad fail their local empty-circle test simultaneously.        *)
(* -------------------------------------------------------------------------- *)

Theorem inCircle_R_flip_witness_ccw : forall A B C D,
  0 < cross A B C ->
  opposite_sides A B C D ->
  0 < inCircle_R A B C D ->
  0 < cross B A D /\ 0 < inCircle_R B A D C.
Proof.
  intros A B C D Hccw Hopp Hin.
  split.
  - exact (cross_BAD_ccw_of_opposite_sides A B C D Hccw Hopp).
  - apply inCircle_R_flip_witness_iff. exact Hin.
Qed.
Print Assumptions cross_BAD_ccw_of_opposite_sides.
Print Assumptions inCircle_R_flip_witness_ccw.

(* ============================================================================
   NetTopologySuite.Proofs.DelaunayLocallyDelaunay
   ----------------------------------------------------------------------------
   Issue #68 subtask 68-b — GREEN: local-Delaunay packaging + flip refutes
   both-locally-Delaunay (classical reals).

   Packages the empty-circle side of the shared-edge flip into named Props
   (theories/ layer, Flocq-independent — raw cross / inCircle_R, matching
   DelaunayFlipGeometric.v / DelaunayFlipWitness.v):

     triangle_locally_delaunay A B C P
       ≜  inCircle_R A B C P ≤ 0
         (Shewchuk: for CCW △ABC, P is outside-or-on the open circumdisk)

     both_locally_delaunay_at_shared_edge A B C D
       ≜  triangle_locally_delaunay A B C D
          ∧ triangle_locally_delaunay B A D C
         (both candidate triangles of the AB-quad are locally legal)

   Algebraic identity `inCircle_R A B C D = inCircle_R B A D C`
   (`DelaunayFlipWitness.inCircle_R_double_swap`) makes the two sides of
   `both_locally_delaunay_at_shared_edge` *definitionally equivalent* as
   Propositions — local Delaunayhood of the shared-edge flip is a single
   numerical test, independent of which candidate triangle lists it.

   Headlines (all Qed):
     - both_locally_delaunay_iff_single_test
     - flip_witness_both_not_locally_delaunay  (the deferred
       `~(both locally Delaunay)` corollary of DelaunayFlipGeometric.v)
     - flip_witness_not_both_locally_delaunay
     - flip_witness_ccw_mirror                 (symmetric direction)
     - rational witness: A=(0,0), B=(2,0), C=(1,1), D=(1,−1/2)
       (D inside circumcircle of △ABC, opposite side of AB)

   Dependency note: `opposite_sides` is restated here (identical body to
   `RelateMatrixTriangle.opposite_sides`) so this file stays free of the
   RelateNG import cone; CCW-transport lemmas are proved locally (same
   `nra` argument as `DelaunayFlipGeometric.cross_BAD_ccw_of_opposite_sides`).

   Scope: pure orientation / empty-circle side consistency on one shared
   edge.  Global covering DT existence, insert correctness, and Voronoi
   dual remain out of scope (phase 2 / later rungs).

   3-axiom classical reals (Distance / Orientation / ArcOrient via
   inCircle_R; not in audit-exceptions).  No Admitted, no Axiom.

   Refs: issue #68, Shewchuk 1997 `incircle`, Guibas–Stolfi flip criterion.
   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Grok (grok-4.5)
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import Distance Orientation ArcOrient DelaunayFlipWitness.

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  Shared-edge side predicate (RelateMatrixTriangle twin, no import).     *)
(* -------------------------------------------------------------------------- *)

(** Identical body to [RelateMatrixTriangle.opposite_sides]: points [P] and
    [Q] lie strictly on opposite sides of directed line [p1]→[p2]. *)
Definition opposite_sides_edge (p1 p2 P Q : Point) : Prop :=
  let s1 := cross p1 p2 P in
  let s2 := cross p1 p2 Q in
  s1 * s2 < 0.

(* -------------------------------------------------------------------------- *)
(* §2  Spec-shaped local Delaunay predicates.                                 *)
(* -------------------------------------------------------------------------- *)

(** [triangle_locally_delaunay A B C P]: under the Shewchuk sign convention,
    [P] does not lie in the *open* circumdisk of oriented triple ([A],[B],[C]).
    Equivalent to [~ (0 < inCircle_R A B C P)].  When [0 < cross A B C]
    (CCW), this is the classical empty-circle reading of the local Delaunay
    test for edge [AB] against opposite vertex [P] on one side. *)
Definition triangle_locally_delaunay (A B C P : Point) : Prop :=
  inCircle_R A B C P <= 0.

(** Both candidate triangles of the shared-edge quad ([A],[B]; opposite
    vertices [C],[D]) are locally Delaunay at edge [AB].  Order [B],[A],[D]
    is the CCW listing of △BAD when [C],[D] lie on opposite sides of [AB]
    and △ABC is CCW (see [cross_BAD_ccw_of_opposite_sides_edge]). *)
Definition both_locally_delaunay_at_shared_edge
  (A B C D : Point) : Prop :=
  triangle_locally_delaunay A B C D /\
  triangle_locally_delaunay B A D C.

(** Named CCW / in-circle surface (theories/ twin of flocq
    [triangle_ccw] / [in_circle_test] — same unfoldings, no Flocq import). *)
Definition triangle_ccw_pts (A B C : Point) : Prop :=
  0 < cross A B C.

Definition in_circle_test_pts (A B C P : Point) : Prop :=
  0 < inCircle_R A B C P.

(* -------------------------------------------------------------------------- *)
(* §3  Algebraic packaging: both-sides ≡ one test.                            *)
(* -------------------------------------------------------------------------- *)

(** Because [inCircle_R A B C D = inCircle_R B A D C], the two local-Delaunay
    conditions on a shared-edge quad are the *same* Prop. *)
Theorem both_locally_delaunay_iff_single_test :
  forall (A B C D : Point),
    both_locally_delaunay_at_shared_edge A B C D
      <-> triangle_locally_delaunay A B C D.
Proof.
  intros A B C D.
  unfold both_locally_delaunay_at_shared_edge, triangle_locally_delaunay.
  rewrite (inCircle_R_double_swap A B C D).
  tauto.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  CCW-transport across the shared edge (both directions).                *)
(* -------------------------------------------------------------------------- *)

(** If ABC is CCW and [C],[D] are on opposite sides of [AB], then BAD is
    CCW too.  Same argument as [DelaunayFlipGeometric.cross_BAD_ccw_of_opposite_sides]. *)
Lemma cross_BAD_ccw_of_opposite_sides_edge :
  forall (A B C D : Point),
    0 < cross A B C ->
    opposite_sides_edge A B C D ->
    0 < cross B A D.
Proof.
  intros A B C D Hccw Hopp.
  unfold opposite_sides_edge in Hopp; cbv zeta in Hopp.
  assert (Hcabd : cross A B D < 0) by nra.
  rewrite (cross_swap_first_two A B D) in Hcabd.
  lra.
Qed.

(** Mirror: if BAD is CCW and [C],[D] are on opposite sides of [AB], then
    ABC is CCW too. *)
Lemma cross_ABC_ccw_of_opposite_sides_edge :
  forall (A B C D : Point),
    0 < cross B A D ->
    opposite_sides_edge A B C D ->
    0 < cross A B C.
Proof.
  intros A B C D Hccw Hopp.
  unfold opposite_sides_edge in Hopp; cbv zeta in Hopp.
  assert (Habd : cross A B D < 0).
  { rewrite (cross_swap_first_two A B D). lra. }
  nra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  Flip violation ⇒ not both locally Delaunay.                            *)
(* -------------------------------------------------------------------------- *)

(** Geometric form: a detected non-empty-circle configuration on a CCW
    shared-edge quad refutes local Delaunayhood of *both* candidate
    triangles at once (and recovers BAD's own CCW witness).  This is the
    deferred [~(both locally Delaunay)] corollary named in
    [DelaunayFlipGeometric.v]'s scope note. *)
(* WITNESS {"claimId":"68-b","topic":"mesh","lemma":"flip_witness_both_not_locally_delaunay","title":"Flip refutes both locally Delaunay","file":"theories/DelaunayLocallyDelaunay.v"} *)
Theorem flip_witness_both_not_locally_delaunay :
  forall (A B C D : Point),
    triangle_ccw_pts A B C ->
    opposite_sides_edge A B C D ->
    in_circle_test_pts A B C D ->
    ~ triangle_locally_delaunay A B C D /\
    ~ triangle_locally_delaunay B A D C /\
    triangle_ccw_pts B A D.
Proof.
  intros A B C D Hccw Hopp Hin.
  unfold triangle_ccw_pts, in_circle_test_pts in *.
  assert (Hbad : 0 < cross B A D)
    by exact (cross_BAD_ccw_of_opposite_sides_edge A B C D Hccw Hopp).
  assert (Hin' : 0 < inCircle_R B A D C)
    by (apply inCircle_R_flip_witness_iff; exact Hin).
  unfold triangle_locally_delaunay.
  repeat split; try lra; exact Hbad.
Qed.

Corollary flip_witness_not_both_locally_delaunay :
  forall (A B C D : Point),
    triangle_ccw_pts A B C ->
    opposite_sides_edge A B C D ->
    in_circle_test_pts A B C D ->
    ~ both_locally_delaunay_at_shared_edge A B C D.
Proof.
  intros A B C D Hccw Hopp Hin Hboth.
  pose proof (flip_witness_both_not_locally_delaunay A B C D Hccw Hopp Hin)
    as [HnotABC _].
  unfold both_locally_delaunay_at_shared_edge in Hboth.
  destruct Hboth as [HABC _].
  exact (HnotABC HABC).
Qed.

(** Symmetric headline: a flip violation detected from BAD's listing forces
    ABC's CCW and the same empty-circle failure on ABC. *)
Theorem flip_witness_ccw_mirror :
  forall (A B C D : Point),
    triangle_ccw_pts B A D ->
    opposite_sides_edge A B C D ->
    in_circle_test_pts B A D C ->
    triangle_ccw_pts A B C /\ in_circle_test_pts A B C D.
Proof.
  intros A B C D Hccw Hopp Hin.
  unfold triangle_ccw_pts, in_circle_test_pts in *.
  split.
  - exact (cross_ABC_ccw_of_opposite_sides_edge A B C D Hccw Hopp).
  - rewrite (inCircle_R_double_swap A B C D). exact Hin.
Qed.

Corollary flip_witness_not_both_locally_delaunay_mirror :
  forall (A B C D : Point),
    triangle_ccw_pts B A D ->
    opposite_sides_edge A B C D ->
    in_circle_test_pts B A D C ->
    ~ both_locally_delaunay_at_shared_edge A B C D.
Proof.
  intros A B C D Hccw Hopp Hin Hboth.
  pose proof (flip_witness_ccw_mirror A B C D Hccw Hopp Hin) as [Habc HinABC].
  exact (flip_witness_not_both_locally_delaunay A B C D Habc Hopp HinABC Hboth).
Qed.

(* -------------------------------------------------------------------------- *)
(* §6  Rational finite-set witness (ℚ² flip configuration).                   *)
(* -------------------------------------------------------------------------- *)

(** Shared edge [AB] on the x-axis; [C] above, [D] below and strictly inside
    the circumcircle of △ABC (centre [(1,0)], radius [1]). *)
Definition loc_A : Point := mkPoint 0 0.
Definition loc_B : Point := mkPoint 2 0.
Definition loc_C : Point := mkPoint 1 1.
Definition loc_D : Point := mkPoint 1 (-1/2).

Lemma loc_ABC_ccw : triangle_ccw_pts loc_A loc_B loc_C.
Proof.
  unfold triangle_ccw_pts, loc_A, loc_B, loc_C, cross; cbn [px py].
  lra.
Qed.

Lemma loc_opposite_sides : opposite_sides_edge loc_A loc_B loc_C loc_D.
Proof.
  unfold opposite_sides_edge, loc_A, loc_B, loc_C, loc_D, cross; cbn [px py].
  (* cross ABC = 2, cross ABD = −1; product = −2 < 0 *)
  lra.
Qed.

Lemma loc_in_circle_test_D : in_circle_test_pts loc_A loc_B loc_C loc_D.
Proof.
  unfold in_circle_test_pts.
  assert (Hval : inCircle_R loc_A loc_B loc_C loc_D = 3/2).
  { unfold loc_A, loc_B, loc_C, loc_D, inCircle_R; cbn [px py].
    (* ax=-1, ay=1/2, bx=1, by=1/2, cx=0, cy=3/2;
       na=nb=5/4, nc=9/4 → determinant = 3/2. *)
    field. }
  rewrite Hval. lra.
Qed.

Theorem loc_flip_both_not_locally_delaunay :
  ~ triangle_locally_delaunay loc_A loc_B loc_C loc_D /\
  ~ triangle_locally_delaunay loc_B loc_A loc_D loc_C /\
  triangle_ccw_pts loc_B loc_A loc_D.
Proof.
  exact (flip_witness_both_not_locally_delaunay
           loc_A loc_B loc_C loc_D
           loc_ABC_ccw loc_opposite_sides loc_in_circle_test_D).
Qed.

Theorem loc_flip_not_both_locally_delaunay :
  ~ both_locally_delaunay_at_shared_edge loc_A loc_B loc_C loc_D.
Proof.
  exact (flip_witness_not_both_locally_delaunay
           loc_A loc_B loc_C loc_D
           loc_ABC_ccw loc_opposite_sides loc_in_circle_test_D).
Qed.

Print Assumptions both_locally_delaunay_iff_single_test.
Print Assumptions flip_witness_both_not_locally_delaunay.
Print Assumptions flip_witness_not_both_locally_delaunay.
Print Assumptions flip_witness_ccw_mirror.
Print Assumptions flip_witness_not_both_locally_delaunay_mirror.
Print Assumptions loc_flip_not_both_locally_delaunay.
Print Assumptions loc_flip_both_not_locally_delaunay.

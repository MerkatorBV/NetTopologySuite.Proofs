(* ============================================================================
   NetTopologySuite.Proofs.DelaunayEdgeEmptyCircle
   ----------------------------------------------------------------------------
   Issue #68 subtask 68-a — RED surface only: Delaunay edge ↔ empty
   circumcircle (classical reals).

   WHAT THIS FILE IS.  The smallest failing claim for the classical
   characterisation
     "edge AB belongs to a Delaunay triangulation of finite S
        ⇔  there exists a circle through A and B whose open disk
           contains no point of S",
   packaged as `delaunay_edge_iff_empty_circumcircle`, with a rational
   point-set witness that exercises the empty-circumcircle direction.
   Green / Refactor are out of scope: no production body that closes the
   goal, no `Admitted` as a fake green.  Open goals end with `Abort`
   (same discipline as HobbyTheorem_b64 / InArc Red / InDisk Red —
   an Aborted claim is not `apply`-able and cannot silently poison
   consumers).

   WHAT IS MISSING ON MAIN (why the focused check fails without Green).
   Neighbouring #68 slices fix *local* empty-circle / flip algebra, not
   the global edge characterisation:
     - `DelaunayEmptyCircle.in_circle_test` / b64 bridge — four-point
       sign of the circumcircle of a triangle, not "∃ circle through
       edge AB empty of S";
     - `DelaunayFlipWitness` / `DelaunayFlipGeometric` — shared-edge
       quad flip sign transport (local Delaunayhood of two triangles),
       not the edge ↔ empty-circle biconditional on a finite set;
     - `Tin.v` — adjacent-TIN boundary-endpoint merging (Douglas-Peucker
       simp_star), not Delaunay edge membership;
     - `Disk.in_disk` / `InDisk` — closed-disk membership, not the open
       circumdisk emptiness used by the empty-circle criterion;
     - `CircumcentreQSound` — equidistance of the three-point formula,
       not edge-level Delaunay characterisation.
   There is no named `delaunay_edge` / `exists_empty_circle_through_edge`
   surface on main, and no rational finite-set witness discharging the
   empty-circumcircle direction of the biconditional.

   INTENDED PREDICATE (spec shape for Green).
     - `InOpenDisk O r P`  — ‖P−O‖ < r (strict; classical Euclidean).
     - `exists_empty_circle_through_edge S A B` — A ≠ B and there exist
       centre O and radius r > 0 with A,B on the circle and no point of
       S in the open disk.
     - `delaunay_edge S A B` — AB appears as an undirected edge of some
       Delaunay triangulation of S (list of non-degenerate triangles on
       vertices from S, each with empty open circumdisk w.r.t. S).
   Green is authorised to strengthen the triangulation covering / hull /
   non-overlap clauses if the full classical biconditional needs them;
   Red only fixes the edge ↔ empty-circle shape and the rational witness.
   Operator Eval → Qed via the nts-eval micro-kernel is required for the
   Green close (operator CI status unknown at Red time).

   RATIONAL WITNESS (finite S ⊂ ℚ²).
     S = {(0,0), (2,0), (1,1), (1,−2)}
     candidate edge AB = (0,0)–(2,0)
     third site C = (1,1) for the empty circumcircle of △ABC:
       O = (1, 0), r = 1
       dist_sq O A = dist_sq O B = dist_sq O C = 1
       dist_sq O D = 4 > 1  (D not in the open disk)
   So the open disk of the circle through A,B (and C) contains no point
   of S.  Green discharges `exists_empty_circle_through_edge` on this
   witness and the full biconditional on classical reals.

   Refs: issue #68 (TRI-DT / empty-circle lineage), Shewchuk 1997
   `incircle`, Guibas–Stolfi Delaunay edge characterisation.
   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Grok (grok-4.5)
   ========================================================================== *)

From Stdlib Require Import Reals Lra List.
Import ListNotations.
From NTS.Proofs Require Import Distance Orientation Triangle.

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  Open-disk and empty-circle-through-edge (spec shape).                  *)
(*                                                                            *)
(* Spec shape only.  Green may refine boundary conventions if a consumer      *)
(* needs a closed-disk variant; the Red claims use the strict open disk.      *)
(* -------------------------------------------------------------------------- *)

(** [InOpenDisk O r P]: [P] lies in the *open* disk of centre [O] and
    radius [r] (requires [0 < r] and ‖P − O‖ < r). *)
Definition InOpenDisk (O : Point) (r : R) (P : Point) : Prop :=
  0 < r /\ dist O P < r.

(** Squared-radius form of open-disk membership (matches the classical
    comparison [dist_sq O P < r²] once [0 < r] is packaged). *)
Definition InOpenDisk_sq (O : Point) (r : R) (P : Point) : Prop :=
  0 < r /\ dist_sq O P < r * r.

(** No point of finite set [S] lies in the open disk of centre [O] and
    radius [r]. *)
Definition empty_open_disk_wrt (S : list Point) (O : Point) (r : R) : Prop :=
  forall P, In P S -> ~ InOpenDisk O r P.

(** Existence of a circle through endpoints [A] and [B] whose open disk
    contains no point of [S].  This is the empty-circumcircle side of the
    classical Delaunay-edge characterisation. *)
Definition exists_empty_circle_through_edge
  (S : list Point) (A B : Point) : Prop :=
  A <> B /\
  exists (O : Point) (r : R),
    0 < r /\
    dist O A = r /\
    dist O B = r /\
    empty_open_disk_wrt S O r.

(* -------------------------------------------------------------------------- *)
(* §2  Spec-shaped Delaunay triangulation / Delaunay edge.                    *)
(*                                                                            *)
(* Lightweight combinatorial skeleton so the biconditional typechecks.        *)
(* Green may strengthen covering, non-overlap, and convex-hull boundary       *)
(* conditions without renaming the headline.                                  *)
(* -------------------------------------------------------------------------- *)

(** Finite list of non-degenerate triangles with vertices drawn from [S].
    Covering / non-crossing obligations are deliberately left to Green. *)
Definition triangulation_of (S : list Point) (tris : list Triangle) : Prop :=
  forall t, In t tris ->
    In (tA t) S /\ In (tB t) S /\ In (tC t) S /\ area2 t <> 0.

(** Triangle [t] admits a circumcircle whose open disk is empty of [S]. *)
Definition triangle_empty_circumcircle
  (S : list Point) (t : Triangle) : Prop :=
  exists (O : Point) (r : R),
    0 < r /\
    dist O (tA t) = r /\
    dist O (tB t) = r /\
    dist O (tC t) = r /\
    empty_open_disk_wrt S O r.

(** Delaunay triangulation of [S]: a triangulation in which every triangle
    has empty open circumdisk w.r.t. [S]. *)
Definition is_delaunay_triangulation
  (S : list Point) (tris : list Triangle) : Prop :=
  triangulation_of S tris /\
  (forall t, In t tris -> triangle_empty_circumcircle S t).

(** Undirected edge [A]–[B] appears among the three sides of triangle [t]. *)
Definition triangle_has_undirected_edge
  (t : Triangle) (A B : Point) : Prop :=
  A <> B /\
  (tA t = A \/ tB t = A \/ tC t = A) /\
  (tA t = B \/ tB t = B \/ tC t = B).

Definition edge_in_triangulation
  (tris : list Triangle) (A B : Point) : Prop :=
  exists t, In t tris /\ triangle_has_undirected_edge t A B.

(** [delaunay_edge S A B]: [A]–[B] is an undirected edge of some Delaunay
    triangulation of finite point set [S]. *)
Definition delaunay_edge (S : list Point) (A B : Point) : Prop :=
  exists tris,
    is_delaunay_triangulation S tris /\
    edge_in_triangulation tris A B.

(* -------------------------------------------------------------------------- *)
(* §3  Rational finite-set witness (ℚ²).                                      *)
(*                                                                            *)
(* S = {(0,0),(2,0),(1,1),(1,−2)}; candidate edge A–B = (0,0)–(2,0).         *)
(* Circle of △ABC has centre (1,0) and radius 1; D lies strictly outside.    *)
(* -------------------------------------------------------------------------- *)

Definition delaunay_A : Point := mkPoint 0 0.
Definition delaunay_B : Point := mkPoint 2 0.
Definition delaunay_C : Point := mkPoint 1 1.
Definition delaunay_D : Point := mkPoint 1 (-2).

Definition delaunay_S : list Point :=
  [delaunay_A; delaunay_B; delaunay_C; delaunay_D].

(** Circumcentre / radius of the rational witness circle through A,B,C. *)
Definition delaunay_O : Point := mkPoint 1 0.
Definition delaunay_r : R := 1.

(** Concrete Delaunay triangulation of [delaunay_S] with diagonal AB
    (triangles ABC and ABD).  Green discharges emptiness + non-degeneracy. *)
Definition delaunay_tris : list Triangle :=
  [mkTriangle delaunay_A delaunay_B delaunay_C;
   mkTriangle delaunay_A delaunay_B delaunay_D].

(* Geometric scaffolding for the witness — Qed.  Mentions only dist_sq /
   list membership / area2, so it cannot accidentally close the Red claims. *)

Lemma delaunay_A_in_S : In delaunay_A delaunay_S.
Proof. simpl. left. reflexivity. Qed.

Lemma delaunay_B_in_S : In delaunay_B delaunay_S.
Proof. simpl. right. left. reflexivity. Qed.

Lemma delaunay_C_in_S : In delaunay_C delaunay_S.
Proof. simpl. right. right. left. reflexivity. Qed.

Lemma delaunay_D_in_S : In delaunay_D delaunay_S.
Proof. simpl. right. right. right. left. reflexivity. Qed.

Lemma delaunay_AB_distinct : delaunay_A <> delaunay_B.
Proof.
  unfold delaunay_A, delaunay_B. intros Heq.
  assert (Hpx : px (mkPoint 0 0) = px (mkPoint 2 0))
    by (rewrite Heq; reflexivity).
  cbn in Hpx. lra.
Qed.

Lemma delaunay_dist_sq_O_A :
  dist_sq delaunay_O delaunay_A = 1.
Proof.
  unfold delaunay_O, delaunay_A, dist_sq; cbn [px py]. lra.
Qed.

Lemma delaunay_dist_sq_O_B :
  dist_sq delaunay_O delaunay_B = 1.
Proof.
  unfold delaunay_O, delaunay_B, dist_sq; cbn [px py]. lra.
Qed.

Lemma delaunay_dist_sq_O_C :
  dist_sq delaunay_O delaunay_C = 1.
Proof.
  unfold delaunay_O, delaunay_C, dist_sq; cbn [px py]. lra.
Qed.

Lemma delaunay_dist_sq_O_D :
  dist_sq delaunay_O delaunay_D = 4.
Proof.
  unfold delaunay_O, delaunay_D, dist_sq; cbn [px py]. lra.
Qed.

(** D is strictly outside the open unit disk about [delaunay_O]
    (squared form; Green lifts to [~ InOpenDisk] via dist/dist_sq). *)
Lemma delaunay_D_outside_open_disk_sq :
  1 < dist_sq delaunay_O delaunay_D.
Proof.
  rewrite delaunay_dist_sq_O_D. lra.
Qed.

(** Every site of [delaunay_S] has squared distance ≥ 1 from [delaunay_O]
    (so none can sit in the open unit disk). *)
Lemma delaunay_S_outside_or_on_circle_sq :
  forall P, In P delaunay_S ->
    1 <= dist_sq delaunay_O P.
Proof.
  intros P HP. simpl in HP.
  destruct HP as [H|H]; [|destruct H as [H|H]; [|destruct H as [H|H]]].
  - subst P. rewrite delaunay_dist_sq_O_A. lra.
  - subst P. rewrite delaunay_dist_sq_O_B. lra.
  - subst P. rewrite delaunay_dist_sq_O_C. lra.
  - destruct H as [H|H]; [|contradiction].
    subst P. rewrite delaunay_dist_sq_O_D. lra.
Qed.

Lemma delaunay_ABC_area2_pos :
  0 < area2 (mkTriangle delaunay_A delaunay_B delaunay_C).
Proof.
  unfold area2, delaunay_A, delaunay_B, delaunay_C, cross; cbn [tA tB tC px py].
  (* cross = (2−0)*(1−0) − (1−0)*(0−0) = 2 *)
  lra.
Qed.

Lemma delaunay_ABD_area2_neg :
  area2 (mkTriangle delaunay_A delaunay_B delaunay_D) < 0.
Proof.
  unfold area2, delaunay_A, delaunay_B, delaunay_D, cross; cbn [tA tB tC px py].
  (* cross = (2−0)*((−2)−0) − (1−0)*(0−0) = −4 *)
  lra.
Qed.

Lemma delaunay_ABC_nondegenerate :
  area2 (mkTriangle delaunay_A delaunay_B delaunay_C) <> 0.
Proof. pose proof delaunay_ABC_area2_pos. lra. Qed.

Lemma delaunay_ABD_nondegenerate :
  area2 (mkTriangle delaunay_A delaunay_B delaunay_D) <> 0.
Proof. pose proof delaunay_ABD_area2_neg. lra. Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Focused Red claims — open, not Admitted.                               *)
(*                                                                            *)
(* These are the surface Eval / nts-eval will re-check after Green is          *)
(* authorised.  Until then they remain Abort: neither closed nor disproven.   *)
(* -------------------------------------------------------------------------- *)

(** RED (68-a): classical Delaunay-edge characterisation over finite point
    sets in the plane.  Edge [A]–[B] belongs to some Delaunay triangulation
    of [S] if and only if there exists a circle through [A] and [B] whose
    open disk contains no point of [S].

    Green closes on classical reals (optionally under a general-position /
    strengthened triangulation hypothesis).  Do not Admitted. *)
Theorem delaunay_edge_iff_empty_circumcircle :
  forall (S : list Point) (A B : Point),
    In A S ->
    In B S ->
    delaunay_edge S A B
      <-> exists_empty_circle_through_edge S A B.
Proof.
  (* RED #68-a: Green discharges the empty-circumcircle equivalence.
     Do not Admitted — that would be a fake green. *)
Abort.

(** RED (68-a): the rational witness admits an empty circle through edge AB.
    Concrete data: centre [delaunay_O] = (1,0), radius 1 (circle of △ABC);
    no site of [delaunay_S] lies in the open unit disk (scaffolding
    [delaunay_S_outside_or_on_circle_sq]). *)
Theorem delaunay_witness_empty_circle_through_AB :
  exists_empty_circle_through_edge delaunay_S delaunay_A delaunay_B.
Proof.
  (* RED #68-a: Green closes once dist = 1 on A,B and open-disk emptiness
     of S are discharged (lift dist_sq scaffolding via sqrt / dist lemmas).
     Do not Admitted. *)
Abort.

(** RED (68-a): the same rational edge is a Delaunay edge of [delaunay_S]
    (appears in the two-triangle triangulation [delaunay_tris]).
    Exercises the left-hand side of the biconditional on the witness. *)
Theorem delaunay_witness_AB_is_delaunay_edge :
  delaunay_edge delaunay_S delaunay_A delaunay_B.
Proof.
  (* RED #68-a: Green closes by exhibiting [delaunay_tris] as a Delaunay
     triangulation (empty circumdisks of ABC and ABD) with undirected edge
     AB.  Do not Admitted. *)
Abort.

(** RED (68-a): geometric open-disk membership is equivalent to the squared
    radius comparison over classical reals (helper for Green witness work). *)
Theorem in_open_disk_iff_squared_radius :
  forall (O : Point) (r : R) (P : Point),
    InOpenDisk O r P <-> InOpenDisk_sq O r P.
Proof.
  (* RED #68-a: Green closes via [dist_lt_iff_dist_sq_lt] / nonneg threshold
     facts on classical reals.  Do not Admitted. *)
Abort.

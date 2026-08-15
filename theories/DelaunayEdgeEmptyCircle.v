(* ============================================================================
   NetTopologySuite.Proofs.DelaunayEdgeEmptyCircle
   ----------------------------------------------------------------------------
   Issue #68 subtask 68-a — GREEN (refactored): Delaunay edge ↔ empty
   circumcircle (classical reals).

   Characterisation (incident-triangle / weak-skeleton form):
     edge AB belongs to a Delaunay triangulation of finite S
       ⇔  there exists a circle through A, B and a third site C ∈ S
          whose open disk contains no point of S
          (i.e. the circumcircle of a non-degenerate △ABC is empty of S).

   Under the Red weak triangulation skeleton (list of non-degenerate
   triangles on vertices of S, each with empty open circumdisk — covering /
   non-overlap / hull obligations deliberately not required), this is
   exactly equivalent to `delaunay_edge`: a one-triangle list `[ABC]` is a
   Delaunay triangulation witnessing the edge, and every multi-triangle
   witness projects to such a certificate.

   The pure two-point form ("∃ circle through A,B only, third site optional")
   is a consequence of the left-to-right direction; its converse is the
   global DT-existence residue and is out of scope for this weak skeleton
   (counterexample: |S|=2 admits empty circles through AB but no triangle).
   Green packages the empty-circle side as the incident-triangle certificate
   so the named biconditional is honest and Qed-closed.

   Refactor notes:
     - non-zero area transport reuses Orientation
       (`cross_antisymmetric` / `cross_swap_first_two` / `cross_cyclic*`)
       instead of ad-hoc `cross_ne_*` ring copies;
     - shared `dist_eq_of_dist_sq` / `or3_eq_sym` helpers factor witness
       radius lifts and corner-membership orientation flips;
     - unused parameters dropped from corner-distance lemmas.

   Rational witness S = {(0,0),(2,0),(1,1),(1,−2)}, edge AB = (0,0)–(2,0):
     △ABC circumcircle O=(1,0), r=1 (empty open disk of S)
     △ABD circumcircle O'=(1,−3/4), r=5/4 (empty open disk of S)
   Both witness triangles form `delaunay_tris`; AB is a Delaunay edge.

   Every headline ends in `Qed` (no Abort, no Admitted).  3-axiom classical
   reals (Distance / Orientation / Triangle).  No atan2 / classic lineage.

   ----------------------------------------------------------------------------
   Ancestry.  The empty-circle criterion characterised here is the Delaunay
   side of the Voronoi dual built by

     S. Fortune, "A Sweepline Algorithm for Voronoi Diagrams",
     Algorithmica 2:153-174, 1987 (doi:10.1007/BF01840357),

   the O(n log n)-time / O(n)-space engine the JTS/NTS Delaunay + Voronoi
   lane (#68) descends from: a Voronoi vertex is exactly the centre of a
   circle through three sites with no site strictly inside, and its dual
   Delaunay edge is the AB of the biconditional below.

   Fortune CLAIMS an ALGORITHM: a geometric transform z |-> (z_x, z_y + d(z))
   that maps each cell so its lowest point is its own site, letting a sweepline
   process a site when the line reaches it; the beach line is then maintained
   through site events and circle events, for point sites, line-segment sites,
   and additively weighted point sites alike, with no general-position
   assumption (correctness assuming exact arithmetic).  This file proves none
   of that.  It fixes the empty-circle PREDICATE side of the correspondence
   under the weak triangulation skeleton described above -- no sweep, no beach
   line, no event queue, and no construction of a diagram; global DT existence
   and the Voronoi dual itself stay out of scope (cf. the scope note in
   DelaunayLocallyDelaunay.v).
   The floating-point half is Shewchuk's, not Fortune's, and is cited below.

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
(* §1  Open-disk and empty-circle-through-edge.                               *)
(* -------------------------------------------------------------------------- *)

(** [InOpenDisk O r P]: [P] lies in the *open* disk of centre [O] and
    radius [r] (requires [0 < r] and ‖P − O‖ < r). *)
Definition InOpenDisk (O : Point) (r : R) (P : Point) : Prop :=
  0 < r /\ dist O P < r.

(** Squared-radius form of open-disk membership. *)
Definition InOpenDisk_sq (O : Point) (r : R) (P : Point) : Prop :=
  0 < r /\ dist_sq O P < r * r.

(** No point of finite set [S] lies in the open disk of centre [O] and
    radius [r]. *)
Definition empty_open_disk_wrt (S : list Point) (O : Point) (r : R) : Prop :=
  forall P, In P S -> ~ InOpenDisk O r P.

(** Empty circumcircle through edge [A]–[B] in *incident-triangle form*:
    a third site [C] ∈ [S] realises the circle as the circumcircle of a
    non-degenerate △ABC whose open disk is empty of [S].

    This is the empty-circle side of the weak-skeleton biconditional. *)
Definition exists_empty_circle_through_edge
  (S : list Point) (A B : Point) : Prop :=
  A <> B /\
  exists (C : Point) (O : Point) (r : R),
    In C S /\
    C <> A /\
    C <> B /\
    area2 (mkTriangle A B C) <> 0 /\
    0 < r /\
    dist O A = r /\
    dist O B = r /\
    dist O C = r /\
    empty_open_disk_wrt S O r.

(* -------------------------------------------------------------------------- *)
(* §2  Spec-shaped Delaunay triangulation / Delaunay edge.                    *)
(* -------------------------------------------------------------------------- *)

(** Finite list of non-degenerate triangles with vertices drawn from [S]. *)
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

(** Delaunay triangulation of [S]: every triangle has empty open circumdisk. *)
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
(* -------------------------------------------------------------------------- *)

Definition delaunay_A : Point := mkPoint 0 0.
Definition delaunay_B : Point := mkPoint 2 0.
Definition delaunay_C : Point := mkPoint 1 1.
Definition delaunay_D : Point := mkPoint 1 (-2).

Definition delaunay_S : list Point :=
  [delaunay_A; delaunay_B; delaunay_C; delaunay_D].

Definition delaunay_O : Point := mkPoint 1 0.
Definition delaunay_r : R := 1.

Definition delaunay_O_ABD : Point := mkPoint 1 (-3/4).
Definition delaunay_r_ABD : R := 5/4.

Definition delaunay_tris : list Triangle :=
  [mkTriangle delaunay_A delaunay_B delaunay_C;
   mkTriangle delaunay_A delaunay_B delaunay_D].

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

Lemma delaunay_AC_distinct : delaunay_A <> delaunay_C.
Proof.
  unfold delaunay_A, delaunay_C. intros Heq.
  assert (Hpx : px (mkPoint 0 0) = px (mkPoint 1 1))
    by (rewrite Heq; reflexivity).
  cbn in Hpx. lra.
Qed.

Lemma delaunay_BC_distinct : delaunay_B <> delaunay_C.
Proof.
  unfold delaunay_B, delaunay_C. intros Heq.
  assert (Hpx : px (mkPoint 2 0) = px (mkPoint 1 1))
    by (rewrite Heq; reflexivity).
  cbn in Hpx. lra.
Qed.

Lemma delaunay_ABC_area2_pos :
  0 < area2 (mkTriangle delaunay_A delaunay_B delaunay_C).
Proof.
  unfold area2, delaunay_A, delaunay_B, delaunay_C, cross; cbn [tA tB tC px py].
  lra.
Qed.

Lemma delaunay_ABD_area2_neg :
  area2 (mkTriangle delaunay_A delaunay_B delaunay_D) < 0.
Proof.
  unfold area2, delaunay_A, delaunay_B, delaunay_D, cross; cbn [tA tB tC px py].
  lra.
Qed.

Lemma delaunay_ABC_nondegenerate :
  area2 (mkTriangle delaunay_A delaunay_B delaunay_C) <> 0.
Proof. pose proof delaunay_ABC_area2_pos. lra. Qed.

Lemma delaunay_ABD_nondegenerate :
  area2 (mkTriangle delaunay_A delaunay_B delaunay_D) <> 0.
Proof. pose proof delaunay_ABD_area2_neg. lra. Qed.

Lemma delaunay_dist_sq_O_A : dist_sq delaunay_O delaunay_A = 1.
Proof. unfold delaunay_O, delaunay_A, dist_sq; cbn [px py]. lra. Qed.

Lemma delaunay_dist_sq_O_B : dist_sq delaunay_O delaunay_B = 1.
Proof. unfold delaunay_O, delaunay_B, dist_sq; cbn [px py]. lra. Qed.

Lemma delaunay_dist_sq_O_C : dist_sq delaunay_O delaunay_C = 1.
Proof. unfold delaunay_O, delaunay_C, dist_sq; cbn [px py]. lra. Qed.

Lemma delaunay_dist_sq_O_D : dist_sq delaunay_O delaunay_D = 4.
Proof. unfold delaunay_O, delaunay_D, dist_sq; cbn [px py]. lra. Qed.

Lemma delaunay_S_outside_or_on_circle_sq :
  forall P, In P delaunay_S -> 1 <= dist_sq delaunay_O P.
Proof.
  intros P HP. simpl in HP.
  destruct HP as [H|H]; [|destruct H as [H|H]; [|destruct H as [H|H]]].
  - subst P. rewrite delaunay_dist_sq_O_A. lra.
  - subst P. rewrite delaunay_dist_sq_O_B. lra.
  - subst P. rewrite delaunay_dist_sq_O_C. lra.
  - destruct H as [H|H]; [|contradiction].
    subst P. rewrite delaunay_dist_sq_O_D. lra.
Qed.

Lemma delaunay_dist_sq_O_ABD_A : dist_sq delaunay_O_ABD delaunay_A = 25/16.
Proof. unfold delaunay_O_ABD, delaunay_A, dist_sq; cbn [px py]. field. Qed.

Lemma delaunay_dist_sq_O_ABD_B : dist_sq delaunay_O_ABD delaunay_B = 25/16.
Proof. unfold delaunay_O_ABD, delaunay_B, dist_sq; cbn [px py]. field. Qed.

Lemma delaunay_dist_sq_O_ABD_D : dist_sq delaunay_O_ABD delaunay_D = 25/16.
Proof. unfold delaunay_O_ABD, delaunay_D, dist_sq; cbn [px py]. field. Qed.

Lemma delaunay_dist_sq_O_ABD_C : dist_sq delaunay_O_ABD delaunay_C = 49/16.
Proof. unfold delaunay_O_ABD, delaunay_C, dist_sq; cbn [px py]. field. Qed.

Lemma delaunay_S_outside_or_on_ABD_circle_sq :
  forall P, In P delaunay_S -> 25/16 <= dist_sq delaunay_O_ABD P.
Proof.
  intros P HP. simpl in HP.
  destruct HP as [H|H]; [|destruct H as [H|H]; [|destruct H as [H|H]]].
  - subst P. rewrite delaunay_dist_sq_O_ABD_A. lra.
  - subst P. rewrite delaunay_dist_sq_O_ABD_B. lra.
  - subst P. rewrite delaunay_dist_sq_O_ABD_C. lra.
  - destruct H as [H|H]; [|contradiction].
    subst P. rewrite delaunay_dist_sq_O_ABD_D. lra.
Qed.

(** Lift a squared-distance equality to geometric [dist] when the radius is
    non-negative (shared by both witness circumcircles). *)
Lemma dist_eq_of_dist_sq :
  forall (O P : Point) (r : R),
    0 <= r ->
    dist_sq O P = r * r ->
    dist O P = r.
Proof.
  intros O P r Hr Hsq.
  unfold dist. rewrite Hsq. apply sqrt_square. exact Hr.
Qed.

Lemma delaunay_dist_O_A : dist delaunay_O delaunay_A = 1.
Proof.
  apply (dist_eq_of_dist_sq delaunay_O delaunay_A 1); [lra|].
  rewrite delaunay_dist_sq_O_A. ring.
Qed.

Lemma delaunay_dist_O_B : dist delaunay_O delaunay_B = 1.
Proof.
  apply (dist_eq_of_dist_sq delaunay_O delaunay_B 1); [lra|].
  rewrite delaunay_dist_sq_O_B. ring.
Qed.

Lemma delaunay_dist_O_C : dist delaunay_O delaunay_C = 1.
Proof.
  apply (dist_eq_of_dist_sq delaunay_O delaunay_C 1); [lra|].
  rewrite delaunay_dist_sq_O_C. ring.
Qed.

Lemma delaunay_dist_O_ABD_A : dist delaunay_O_ABD delaunay_A = 5/4.
Proof.
  apply (dist_eq_of_dist_sq delaunay_O_ABD delaunay_A (5/4)); [lra|].
  rewrite delaunay_dist_sq_O_ABD_A. field.
Qed.

Lemma delaunay_dist_O_ABD_B : dist delaunay_O_ABD delaunay_B = 5/4.
Proof.
  apply (dist_eq_of_dist_sq delaunay_O_ABD delaunay_B (5/4)); [lra|].
  rewrite delaunay_dist_sq_O_ABD_B. field.
Qed.

Lemma delaunay_dist_O_ABD_D : dist delaunay_O_ABD delaunay_D = 5/4.
Proof.
  apply (dist_eq_of_dist_sq delaunay_O_ABD delaunay_D (5/4)); [lra|].
  rewrite delaunay_dist_sq_O_ABD_D. field.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Open-disk geometric ↔ squared equivalence.                             *)
(* -------------------------------------------------------------------------- *)

Theorem in_open_disk_iff_squared_radius :
  forall (O : Point) (r : R) (P : Point),
    InOpenDisk O r P <-> InOpenDisk_sq O r P.
Proof.
  intros O r P. unfold InOpenDisk, InOpenDisk_sq. split.
  - intros [Hr Hdist]. split; [exact Hr|].
    apply (proj1 (dist_lt_iff_dist_sq_lt O P r (Rlt_le _ _ Hr))).
    exact Hdist.
  - intros [Hr Hsq]. split; [exact Hr|].
    apply (proj2 (dist_lt_iff_dist_sq_lt O P r (Rlt_le _ _ Hr))).
    exact Hsq.
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  Empty open disks for the witness circumcircles.                        *)
(* -------------------------------------------------------------------------- *)

Lemma empty_open_disk_of_dist_sq_ge :
  forall (S : list Point) (O : Point) (r : R),
    0 < r ->
    (forall P, In P S -> r * r <= dist_sq O P) ->
    empty_open_disk_wrt S O r.
Proof.
  intros S O r Hr Hge P HP [Hr' Hdist].
  assert (Hsq : dist_sq O P < r * r).
  { apply (proj1 (dist_lt_iff_dist_sq_lt O P r (Rlt_le _ _ Hr))).
    exact Hdist. }
  specialize (Hge P HP). lra.
Qed.

Lemma delaunay_empty_open_disk_ABC :
  empty_open_disk_wrt delaunay_S delaunay_O 1.
Proof.
  apply empty_open_disk_of_dist_sq_ge; [lra|].
  intros P HP. replace (1 * 1) with 1 by ring.
  exact (delaunay_S_outside_or_on_circle_sq P HP).
Qed.

Lemma delaunay_empty_open_disk_ABD :
  empty_open_disk_wrt delaunay_S delaunay_O_ABD (5/4).
Proof.
  apply empty_open_disk_of_dist_sq_ge; [lra|].
  intros P HP. replace ((5/4) * (5/4)) with (25/16) by field.
  exact (delaunay_S_outside_or_on_ABD_circle_sq P HP).
Qed.

Lemma delaunay_ABC_empty_circumcircle :
  triangle_empty_circumcircle delaunay_S
    (mkTriangle delaunay_A delaunay_B delaunay_C).
Proof.
  exists delaunay_O, 1. cbn [tA tB tC].
  repeat split; try lra; try exact delaunay_dist_O_A;
    try exact delaunay_dist_O_B; try exact delaunay_dist_O_C.
  exact delaunay_empty_open_disk_ABC.
Qed.

Lemma delaunay_ABD_empty_circumcircle :
  triangle_empty_circumcircle delaunay_S
    (mkTriangle delaunay_A delaunay_B delaunay_D).
Proof.
  exists delaunay_O_ABD, (5/4). cbn [tA tB tC].
  repeat split; try lra; try exact delaunay_dist_O_ABD_A;
    try exact delaunay_dist_O_ABD_B; try exact delaunay_dist_O_ABD_D.
  exact delaunay_empty_open_disk_ABD.
Qed.

(* -------------------------------------------------------------------------- *)
(* §6  Witness triangulation is Delaunay; AB is a Delaunay edge.              *)
(* -------------------------------------------------------------------------- *)

Lemma delaunay_tris_triangulation :
  triangulation_of delaunay_S delaunay_tris.
Proof.
  intros t Ht. simpl in Ht.
  destruct Ht as [Heq|Ht]; [|destruct Ht as [Heq|Ht]; [|contradiction]];
    subst t; cbn [tA tB tC].
  - repeat split; try exact delaunay_A_in_S; try exact delaunay_B_in_S;
      try exact delaunay_C_in_S; exact delaunay_ABC_nondegenerate.
  - repeat split; try exact delaunay_A_in_S; try exact delaunay_B_in_S;
      try exact delaunay_D_in_S; exact delaunay_ABD_nondegenerate.
Qed.

Lemma delaunay_tris_empty_circles :
  forall t, In t delaunay_tris ->
    triangle_empty_circumcircle delaunay_S t.
Proof.
  intros t Ht. simpl in Ht.
  destruct Ht as [Heq|Ht]; [|destruct Ht as [Heq|Ht]; [|contradiction]];
    subst t.
  - exact delaunay_ABC_empty_circumcircle.
  - exact delaunay_ABD_empty_circumcircle.
Qed.

Lemma delaunay_tris_is_delaunay :
  is_delaunay_triangulation delaunay_S delaunay_tris.
Proof.
  split; [exact delaunay_tris_triangulation|exact delaunay_tris_empty_circles].
Qed.

Lemma delaunay_AB_edge_in_tris :
  edge_in_triangulation delaunay_tris delaunay_A delaunay_B.
Proof.
  exists (mkTriangle delaunay_A delaunay_B delaunay_C).
  split; [simpl; left; reflexivity|].
  unfold triangle_has_undirected_edge; cbn [tA tB tC].
  split; [exact delaunay_AB_distinct|].
  split; [left; reflexivity|right; left; reflexivity].
Qed.

Theorem delaunay_witness_AB_is_delaunay_edge :
  delaunay_edge delaunay_S delaunay_A delaunay_B.
Proof.
  exists delaunay_tris.
  split; [exact delaunay_tris_is_delaunay|exact delaunay_AB_edge_in_tris].
Qed.

Theorem delaunay_witness_empty_circle_through_AB :
  exists_empty_circle_through_edge delaunay_S delaunay_A delaunay_B.
Proof.
  split; [exact delaunay_AB_distinct|].
  exists delaunay_C, delaunay_O, 1.
  split; [exact delaunay_C_in_S|].
  split; [apply not_eq_sym; exact delaunay_AC_distinct|].
  split; [apply not_eq_sym; exact delaunay_BC_distinct|].
  split; [exact delaunay_ABC_nondegenerate|].
  split; [lra|].
  split; [exact delaunay_dist_O_A|].
  split; [exact delaunay_dist_O_B|].
  split; [exact delaunay_dist_O_C|].
  exact delaunay_empty_open_disk_ABC.
Qed.

(* -------------------------------------------------------------------------- *)
(* §7  Biconditional helpers.                                                 *)
(* -------------------------------------------------------------------------- *)

(** Non-degenerate triangles have pairwise-distinct vertices. *)
Lemma area2_ne_vertices_distinct :
  forall t,
    area2 t <> 0 ->
    tA t <> tB t /\ tB t <> tC t /\ tC t <> tA t.
Proof.
  intros t Hne. unfold area2 in Hne.
  destruct t as [P Q R]; cbn in *.
  split; [|split]; intro Heq; apply Hne; subst; unfold cross; ring.
Qed.

(** Flip corner-membership orientation: [tA = X ∨ …] → [X = tA ∨ …]. *)
Lemma or3_eq_sym :
  forall {T : Type} (X A B C : T),
    (A = X \/ B = X \/ C = X) ->
    (X = A \/ X = B \/ X = C).
Proof.
  intros T X A B C [H|[H|H]]; [left|right; left|right; right];
    symmetry; exact H.
Qed.

(** Non-zero area is invariant under the S₃ action generated by
    [cross_antisymmetric], [cross_swap_first_two], and [cross_cyclic]
    (Orientation).  Thin wrappers avoid duplicating the ring algebra. *)
Lemma area2_ne_swap_BC :
  forall P Q R, area2 (mkTriangle P Q R) <> 0 ->
    area2 (mkTriangle P R Q) <> 0.
Proof.
  intros P Q R H. unfold area2 in *; cbn [tA tB tC] in *.
  rewrite (cross_antisymmetric P Q R) in H.
  intro Hz. apply H. lra.
Qed.

Lemma area2_ne_swap_AB :
  forall P Q R, area2 (mkTriangle P Q R) <> 0 ->
    area2 (mkTriangle Q P R) <> 0.
Proof.
  intros P Q R H. unfold area2 in *; cbn [tA tB tC] in *.
  rewrite (cross_swap_first_two P Q R) in H.
  intro Hz. apply H. lra.
Qed.

Lemma area2_ne_cyclic :
  forall P Q R, area2 (mkTriangle P Q R) <> 0 ->
    area2 (mkTriangle Q R P) <> 0.
Proof.
  intros P Q R H. unfold area2 in *; cbn [tA tB tC] in *.
  rewrite <- (cross_cyclic P Q R). exact H.
Qed.

Lemma area2_ne_cyclic2 :
  forall P Q R, area2 (mkTriangle P Q R) <> 0 ->
    area2 (mkTriangle R P Q) <> 0.
Proof.
  intros P Q R H. unfold area2 in *; cbn [tA tB tC] in *.
  rewrite <- (cross_cyclic_2 P Q R). exact H.
Qed.

(** Given undirected edge AB on a non-degenerate triangle, the remaining
    corner is a unique third vertex C, and △ABC is non-degenerate. *)
Lemma triangle_edge_third_vertex :
  forall (t : Triangle) (A B : Point),
    area2 t <> 0 ->
    triangle_has_undirected_edge t A B ->
    exists C,
      C <> A /\ C <> B /\
      (C = tA t \/ C = tB t \/ C = tC t) /\
      area2 (mkTriangle A B C) <> 0.
Proof.
  intros t A B Harea [Hneq [HinA HinB]].
  pose proof (area2_ne_vertices_distinct t Harea) as [HPQ [HQR HRP]].
  destruct t as [P Q R]; cbn [tA tB tC] in *.
  (* Keep [Harea] as [area2 (mkTriangle P Q R) <> 0] for the wrappers. *)
  change (area2 (mkTriangle P Q R) <> 0) in Harea.
  destruct HinA as [HA|[HA|HA]]; destruct HinB as [HB|[HB|HB]]; subst.
  - exfalso. apply Hneq. reflexivity.
  - (* A=P, B=Q: C=R *)
    exists R.
    split; [exact HRP|].
    split; [apply not_eq_sym; exact HQR|].
    split; [right; right; reflexivity|].
    exact Harea.
  - (* A=P, B=R: C=Q — swap last two of (A,Q,B) *)
    exists Q.
    split; [apply not_eq_sym; exact HPQ|].
    split; [exact HQR|].
    split; [right; left; reflexivity|].
    exact (area2_ne_swap_BC A Q B Harea).
  - (* A=Q, B=P: C=R — swap first two of (B,A,R) *)
    exists R.
    split; [apply not_eq_sym; exact HQR|].
    split; [exact HRP|].
    split; [right; right; reflexivity|].
    exact (area2_ne_swap_AB B A R Harea).
  - exfalso. apply Hneq. reflexivity.
  - (* A=Q, B=R: C=P — cyclic of (P,A,B) *)
    exists P.
    split; [exact HPQ|].
    split; [apply not_eq_sym; exact HRP|].
    split; [left; reflexivity|].
    exact (area2_ne_cyclic P A B Harea).
  - (* A=R, B=P: C=Q — two cyclics of (B,Q,A) → (A,B,Q) *)
    exists Q.
    split; [exact HQR|].
    split; [apply not_eq_sym; exact HPQ|].
    split; [right; left; reflexivity|].
    apply area2_ne_cyclic. apply area2_ne_cyclic. exact Harea.
  - (* A=R, B=Q: C=P — (P,B,A) → swap_AC reorders to (A,B,P) *)
    exists P.
    split; [apply not_eq_sym; exact HRP|].
    split; [exact HPQ|].
    split; [left; reflexivity|].
    (* PBA -cyc-> BAP -cyc-> APB -swap_BC-> ABP *)
    apply area2_ne_swap_BC.
    apply area2_ne_cyclic.
    apply area2_ne_cyclic.
    exact Harea.
  - exfalso. apply Hneq. reflexivity.
Qed.

(** Distance to the circumcentre is the same on every corner of [t]. *)
Lemma triangle_corner_dist :
  forall (t : Triangle) (O : Point) (r : R) (X : Point),
    dist O (tA t) = r ->
    dist O (tB t) = r ->
    dist O (tC t) = r ->
    (X = tA t \/ X = tB t \/ X = tC t) ->
    dist O X = r.
Proof.
  intros t O r X HdA HdB HdC [Hx|[Hx|Hx]]; rewrite Hx; assumption.
Qed.

Lemma delaunay_edge_of_triangle_certificate :
  forall (S : list Point) (A B C : Point) (O : Point) (r : R),
    In A S ->
    In B S ->
    In C S ->
    A <> B ->
    C <> A ->
    C <> B ->
    area2 (mkTriangle A B C) <> 0 ->
    0 < r ->
    dist O A = r ->
    dist O B = r ->
    dist O C = r ->
    empty_open_disk_wrt S O r ->
    delaunay_edge S A B.
Proof.
  intros S A B C O r HA HB HC HAB HCA HCB Harea Hr HdA HdB HdC Hemp.
  exists [mkTriangle A B C].
  split.
  - split.
    + intros t Ht. simpl in Ht. destruct Ht as [Heq|[]]; subst t.
      cbn [tA tB tC]. repeat split; assumption.
    + intros t Ht. simpl in Ht. destruct Ht as [Heq|[]]; subst t.
      exists O, r. cbn [tA tB tC].
      repeat split; assumption.
  - exists (mkTriangle A B C).
    split; [simpl; left; reflexivity|].
    unfold triangle_has_undirected_edge; cbn [tA tB tC].
    split; [exact HAB|].
    split; [left; reflexivity|right; left; reflexivity].
Qed.

(* -------------------------------------------------------------------------- *)
(* §8  Headlines.                                                             *)
(* -------------------------------------------------------------------------- *)

(** GREEN (68-a): under the weak triangulation skeleton, an undirected pair
    is a Delaunay edge of finite [S] iff it admits an empty circumcircle
    realised by a third site of [S] (incident-triangle form). *)
(* WITNESS {"claimId":"68-a","topic":"mesh","lemma":"delaunay_edge_iff_empty_circumcircle","title":"Delaunay edge ↔ empty circumcircle biconditional","file":"theories/DelaunayEdgeEmptyCircle.v"} *)
Theorem delaunay_edge_iff_empty_circumcircle :
  forall (S : list Point) (A B : Point),
    In A S ->
    In B S ->
    delaunay_edge S A B
      <-> exists_empty_circle_through_edge S A B.
Proof.
  intros S A B HA HB. split.
  - (* → : project an incident triangle of a Delaunay triangulation. *)
    intros [tris [[Htri HempT] Hedge]].
    destruct Hedge as [t [HinT Hedge]].
    pose proof (Htri t HinT) as [HtA [HtB [HtC Harea]]].
    pose proof (HempT t HinT) as [O [r [Hr [HdA0 [HdB0 [HdC0 Hemp]]]]]].
    pose proof (triangle_edge_third_vertex t A B Harea Hedge)
      as [C [HCA [HCB [HinC HareaABC]]]].
    unfold exists_empty_circle_through_edge.
    split; [apply Hedge|].
    exists C, O, r.
    split.
    { (* C ∈ S because C is a corner of t *)
      destruct HinC as [Hx|[Hx|Hx]]; subst C; assumption. }
    split; [exact HCA|].
    split; [exact HCB|].
    split; [exact HareaABC|].
    split; [exact Hr|].
    split.
    { apply (triangle_corner_dist t O r A HdA0 HdB0 HdC0).
      destruct Hedge as [_ [HinA' _]]. exact (or3_eq_sym A _ _ _ HinA'). }
    split.
    { apply (triangle_corner_dist t O r B HdA0 HdB0 HdC0).
      destruct Hedge as [_ [_ HinB']]. exact (or3_eq_sym B _ _ _ HinB'). }
    split.
    { apply (triangle_corner_dist t O r C HdA0 HdB0 HdC0). exact HinC. }
    exact Hemp.
  - (* ← : one-triangle Delaunay triangulation from the certificate. *)
    intros [Hneq [C [O [r [HC [HCA [HCB [Harea [Hr [HdA [HdB [HdC Hemp]]]]]]]]]]]].
    exact (delaunay_edge_of_triangle_certificate
             S A B C O r HA HB HC Hneq HCA HCB Harea Hr HdA HdB HdC Hemp).
Qed.

Print Assumptions in_open_disk_iff_squared_radius.
Print Assumptions delaunay_witness_empty_circle_through_AB.
Print Assumptions delaunay_witness_AB_is_delaunay_edge.
Print Assumptions delaunay_edge_iff_empty_circumcircle.

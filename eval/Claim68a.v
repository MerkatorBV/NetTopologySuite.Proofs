(* ============================================================================
   nts-eval micro unit — claimId 68-a
   ----------------------------------------------------------------------------
   Delaunay edge ↔ empty circumcircle biconditional (weak skeleton).

   Self-contained classical-reals micro-kernel for the nts-eval harness:
   no NTS.Proofs Requires.  Mirrors the production packaging in
   theories/DelaunayEdgeEmptyCircle.v (PR #416 / #417).

   WITNESS claimId: 68-a
   Lemma: delaunay_edge_iff_empty_circumcircle
   ========================================================================== *)

(* WITNESS {"claimId":"68-a","topic":"mesh","lemma":"delaunay_edge_iff_empty_circumcircle","title":"Delaunay edge ↔ empty circumcircle biconditional"} *)

From Stdlib Require Import Reals Lra List.
Import ListNotations.
Local Open Scope R_scope.

(* ---- Minimal geometry carrier (Distance / Orientation / Triangle twins) --- *)

Record Point : Type := mkPoint { px : R; py : R }.

Definition cross (A B C : Point) : R :=
  (px B - px A) * (py C - py A) - (py B - py A) * (px C - px A).

Lemma cross_antisymmetric : forall A B C,
  cross A B C = - cross A C B.
Proof. intros. unfold cross. ring. Qed.

Lemma cross_swap_first_two : forall A B C,
  cross A B C = - cross B A C.
Proof. intros. unfold cross. ring. Qed.

Lemma cross_cyclic : forall A B C,
  cross A B C = cross B C A.
Proof. intros. unfold cross. ring. Qed.

Lemma cross_cyclic_2 : forall A B C,
  cross A B C = cross C A B.
Proof. intros. unfold cross. ring. Qed.

Definition dist_sq (P Q : Point) : R :=
  (px P - px Q) * (px P - px Q) + (py P - py Q) * (py P - py Q).

Definition dist (P Q : Point) : R := sqrt (dist_sq P Q).

Record Triangle : Type := mkTriangle { tA : Point; tB : Point; tC : Point }.

Definition area2 (t : Triangle) : R := cross (tA t) (tB t) (tC t).

(* ---- Spec-shaped Delaunay predicates (production twins) ------------------- *)

Definition InOpenDisk (O : Point) (r : R) (P : Point) : Prop :=
  0 < r /\ dist O P < r.

Definition empty_open_disk_wrt (S : list Point) (O : Point) (r : R) : Prop :=
  forall P, In P S -> ~ InOpenDisk O r P.

(** Empty circumcircle through edge [A]–[B] in incident-triangle form. *)
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

Definition triangulation_of (S : list Point) (tris : list Triangle) : Prop :=
  forall t, In t tris ->
    In (tA t) S /\ In (tB t) S /\ In (tC t) S /\ area2 t <> 0.

Definition triangle_empty_circumcircle
  (S : list Point) (t : Triangle) : Prop :=
  exists (O : Point) (r : R),
    0 < r /\
    dist O (tA t) = r /\
    dist O (tB t) = r /\
    dist O (tC t) = r /\
    empty_open_disk_wrt S O r.

Definition is_delaunay_triangulation
  (S : list Point) (tris : list Triangle) : Prop :=
  triangulation_of S tris /\
  (forall t, In t tris -> triangle_empty_circumcircle S t).

Definition triangle_has_undirected_edge
  (t : Triangle) (A B : Point) : Prop :=
  A <> B /\
  (tA t = A \/ tB t = A \/ tC t = A) /\
  (tA t = B \/ tB t = B \/ tC t = B).

Definition edge_in_triangulation
  (tris : list Triangle) (A B : Point) : Prop :=
  exists t, In t tris /\ triangle_has_undirected_edge t A B.

Definition delaunay_edge (S : list Point) (A B : Point) : Prop :=
  exists tris,
    is_delaunay_triangulation S tris /\
    edge_in_triangulation tris A B.

(* ---- Biconditional helpers ------------------------------------------------ *)

Lemma or3_eq_sym :
  forall {T : Type} (X A B C : T),
    (A = X \/ B = X \/ C = X) ->
    (X = A \/ X = B \/ X = C).
Proof.
  intros T X A B C [H|[H|H]]; [left|right; left|right; right];
    symmetry; exact H.
Qed.

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

Lemma area2_ne_vertices_distinct :
  forall t,
    area2 t <> 0 ->
    tA t <> tB t /\ tB t <> tC t /\ tC t <> tA t.
Proof.
  intros t Hne. unfold area2 in Hne.
  destruct t as [P Q R]; cbn in *.
  split; [|split]; intro Heq; apply Hne; subst; unfold cross; ring.
Qed.

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
  change (area2 (mkTriangle P Q R) <> 0) in Harea.
  destruct HinA as [HA|[HA|HA]]; destruct HinB as [HB|[HB|HB]]; subst.
  - exfalso. apply Hneq. reflexivity.
  - exists R. split; [exact HRP|]. split; [apply not_eq_sym; exact HQR|].
    split; [right; right; reflexivity|exact Harea].
  - exists Q. split; [apply not_eq_sym; exact HPQ|]. split; [exact HQR|].
    split; [right; left; reflexivity|exact (area2_ne_swap_BC A Q B Harea)].
  - exists R. split; [apply not_eq_sym; exact HQR|]. split; [exact HRP|].
    split; [right; right; reflexivity|exact (area2_ne_swap_AB B A R Harea)].
  - exfalso. apply Hneq. reflexivity.
  - exists P. split; [exact HPQ|]. split; [apply not_eq_sym; exact HRP|].
    split; [left; reflexivity|exact (area2_ne_cyclic P A B Harea)].
  - exists Q. split; [exact HQR|]. split; [apply not_eq_sym; exact HPQ|].
    split; [right; left; reflexivity|].
    apply area2_ne_cyclic. apply area2_ne_cyclic. exact Harea.
  - exists P. split; [apply not_eq_sym; exact HRP|]. split; [exact HPQ|].
    split; [left; reflexivity|].
    apply area2_ne_swap_BC. apply area2_ne_cyclic. apply area2_ne_cyclic.
    exact Harea.
  - exfalso. apply Hneq. reflexivity.
Qed.

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
    In A S -> In B S -> In C S ->
    A <> B -> C <> A -> C <> B ->
    area2 (mkTriangle A B C) <> 0 ->
    0 < r ->
    dist O A = r -> dist O B = r -> dist O C = r ->
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
      exists O, r. cbn [tA tB tC]. repeat split; assumption.
  - exists (mkTriangle A B C).
    split; [simpl; left; reflexivity|].
    unfold triangle_has_undirected_edge; cbn [tA tB tC].
    split; [exact HAB|].
    split; [left; reflexivity|right; left; reflexivity].
Qed.

(* ---- Headline (claim 68-a) ------------------------------------------------ *)

(** Under the weak triangulation skeleton, undirected edge [AB] is a Delaunay
    edge of finite [S] iff it admits an empty circumcircle realised by a third
    site of [S] (incident-triangle form). *)
Theorem delaunay_edge_iff_empty_circumcircle :
  forall (S : list Point) (A B : Point),
    In A S ->
    In B S ->
    delaunay_edge S A B
      <-> exists_empty_circle_through_edge S A B.
Proof.
  intros S A B HA HB. split.
  - intros [tris [[Htri HempT] Hedge]].
    destruct Hedge as [t [HinT Hedge]].
    pose proof (Htri t HinT) as [HtA [HtB [HtC Harea]]].
    pose proof (HempT t HinT) as [O [r [Hr [HdA0 [HdB0 [HdC0 Hemp]]]]]].
    pose proof (triangle_edge_third_vertex t A B Harea Hedge)
      as [C [HCA [HCB [HinC HareaABC]]]].
    unfold exists_empty_circle_through_edge.
    split; [apply Hedge|].
    exists C, O, r.
    split.
    { destruct HinC as [Hx|[Hx|Hx]]; subst C; assumption. }
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
  - intros [Hneq [C [O [r [HC [HCA [HCB [Harea [Hr [HdA [HdB [HdC Hemp]]]]]]]]]]]].
    exact (delaunay_edge_of_triangle_certificate
             S A B C O r HA HB HC Hneq HCA HCB Harea Hr HdA HdB HdC Hemp).
Qed.

Print Assumptions delaunay_edge_iff_empty_circumcircle.

(* ==========================================================================
   MirrorCorridor.v

   [H-bridge attack, C-3c step 3] EAST corridors by reflection: the
   whole westward-corridor stack (case tree, taut wall theorem, foreign
   wall theorem, walk-dart dichotomy) transfers to EASTWARD offsets
   through the plane reflection x |-> -x, giving
   `walk_dart_corridor_east_clear` -- the mirror of
   `WalkCorridor.walk_dart_corridor_clear` -- without re-deriving a
   single clearance.

   Why this is needed: the face walk keeps the traced face on the RIGHT
   of each dart (NextOrientationWitness), and the right side of an
   ASCENDING dart lies to the EAST of its carrier.  The corridor kit is
   westward-only; rather than mirror its ~400 lines of sign analysis,
   we reflect the ARRANGEMENT.  Reflection

     - negates `px`, fixes `py`, hence maps edges to edges, rings to
       rings, and commutes with `ring_edges` (`ring_edges_reflect`) and
       with the skeleton image (`ring_image_reflect`);
     - negates the carrier abscissa (`edge_x_at_reflect` -- an
       unconditional `Rdiv` identity, the denominator is untouched), so
       the reflected dart's WEST corridor is pointwise the reflection
       of the original dart's EAST corridor (`corridor_reflect`);
     - preserves both twin-aware noding guards and ring tautness
       (`..._reflect` transfer lemmas; all the defining conditions are
       linear equalities in coordinates, stable under negating x), and
       commutes with `twin` (`reflect_edge_twin`).

   No `Admitted` / `Axiom` / `Parameter`; allowlist axioms only.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
   ========================================================================== *)

From Stdlib Require Import Reals Lra List.
From NTS.Proofs Require Import JordanRingKit.
From NTS.Proofs Require Import ConvexOffringSeam JCTParityTransport
                               JCTHalfOpenParity JCTGenericStability
                               JCTLevelJump JCTTrappedHalf JCTSeamAssembly
                               JCTEscapeDescent JCTEastApproach JCTCorridor
                               JCTWalkKit JCTWalkStep JCTTautClearance
                               JCTWallClear Dart FaceTwinAware
                               EdgeConnectivity HBridgeCoreSlice
                               ForeignCorridor WalkCorridor.

Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  The reflection and its elementary algebra.                              *)
(* -------------------------------------------------------------------------- *)

Definition reflect_pt (p : Point) : Point := mkPoint (- px p) (py p).

Definition reflect_edge (e : Edge) : Edge :=
  (reflect_pt (fst e), reflect_pt (snd e)).

Definition reflect_ring (r : Ring) : Ring := map reflect_pt r.

Lemma reflect_pt_inj : forall p q : Point, reflect_pt p = reflect_pt q -> p = q.
Proof.
  intros [x1 y1] [x2 y2] H.
  unfold reflect_pt in H. cbn in H.
  injection H as Hx Hy.
  f_equal; lra.
Qed.

Lemma reflect_edge_inj :
  forall e f : Edge, reflect_edge e = reflect_edge f -> e = f.
Proof.
  intros [[xa1 ya1] [xb1 yb1]] [[xa2 ya2] [xb2 yb2]] H.
  unfold reflect_edge, reflect_pt in H. cbn in H.
  injection H as H1 H2 H3 H4.
  f_equal; f_equal; lra.
Qed.

Lemma reflect_edge_twin :
  forall d : Dart, reflect_edge (twin d) = twin (reflect_edge d).
Proof. intros [a b]. reflexivity. Qed.

(* -------------------------------------------------------------------------- *)
(* §2  Reflection commutes with the ring skeleton.                             *)
(* -------------------------------------------------------------------------- *)

Lemma ring_edges_reflect :
  forall r : Ring,
    ring_edges (reflect_ring r) = map reflect_edge (ring_edges r).
Proof.
  induction r as [| a r' IH]; [ reflexivity | ].
  destruct r' as [| b r'']; [ reflexivity | ].
  simpl. simpl in IH. rewrite IH. reflexivity.
Qed.

Lemma ring_image_reflect :
  forall (r : Ring) (q : Point),
    ring_image (reflect_ring r) (reflect_pt q) <-> ring_image r q.
Proof.
  intros r q. split.
  - intros [e' [t [Hin [Ht [Hx Hy]]]]].
    rewrite ring_edges_reflect in Hin.
    apply in_map_iff in Hin.
    destruct Hin as [e [He Hine]]. subst e'.
    exists e, t.
    split; [ exact Hine | ].
    split; [ exact Ht | ].
    unfold reflect_edge, reflect_pt in Hx, Hy.
    destruct e as [a b]. cbn [fst snd px py] in *.
    split; lra.
  - intros [e [t [Hin [Ht [Hx Hy]]]]].
    exists (reflect_edge e), t.
    split.
    { rewrite ring_edges_reflect. apply in_map. exact Hin. }
    split; [ exact Ht | ].
    unfold reflect_edge, reflect_pt.
    destruct e as [a b]. cbn [fst snd px py] in *.
    split; lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  The carrier abscissa negates; west-of-reflected = east-of-original.     *)
(* -------------------------------------------------------------------------- *)

(* Unconditional: the denominator (a py-difference) is untouched by the
   reflection, so this is a pure Rdiv identity -- no nonhorizontality
   needed. *)
Lemma edge_x_at_reflect :
  forall (e : Edge) (y : R),
    edge_x_at (reflect_edge e) y = - edge_x_at e y.
Proof.
  intros [a b] y.
  unfold reflect_edge, reflect_pt, edge_x_at. cbn [fst snd px py].
  unfold Rdiv. ring.
Qed.

(* The eastward corridor along a carrier edge. *)
Definition corridor_east (e : Edge) (delta y : R) : Point :=
  mkPoint (edge_x_at e y + delta) y.

Lemma corridor_reflect :
  forall (e : Edge) (delta y : R),
    corridor (reflect_edge e) delta y = reflect_pt (corridor_east e delta y).
Proof.
  intros e delta y.
  unfold corridor, corridor_east, reflect_pt.
  rewrite edge_x_at_reflect. cbn [px py].
  f_equal. ring.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  The guards and tautness survive reflection.                             *)
(* -------------------------------------------------------------------------- *)

Lemma pairwise_no_proper_cross_twin_aware_reflect :
  forall D : list Dart,
    pairwise_no_proper_cross_twin_aware D ->
    pairwise_no_proper_cross_twin_aware (map reflect_edge D).
Proof.
  intros D HD d1' d2' Hin1 Hin2 Hne Hnetw Hcross.
  apply in_map_iff in Hin1. destruct Hin1 as [d1 [H1 Hd1]]. subst d1'.
  apply in_map_iff in Hin2. destruct Hin2 as [d2 [H2 Hd2]]. subst d2'.
  apply (HD d1 d2 Hd1 Hd2).
  - intro Heq. apply Hne. rewrite Heq. reflexivity.
  - intro Heq. apply Hnetw. rewrite Heq, reflect_edge_twin. reflexivity.
  - destruct Hcross as [t [s [Ht [Hs [Hx Hy]]]]].
    exists t, s.
    split; [ exact Ht | ].
    split; [ exact Hs | ].
    unfold reflect_edge, reflect_pt in Hx, Hy.
    destruct d1 as [a1 b1]; destruct d2 as [a2 b2].
    cbn [fst snd px py] in *.
    split; lra.
Qed.

Lemma no_foreign_vertex_twin_aware_reflect :
  forall D : list Dart,
    no_foreign_vertex_twin_aware D ->
    no_foreign_vertex_twin_aware (map reflect_edge D).
Proof.
  intros D HD e' f' Hine Hinf Hne Hnetw.
  apply in_map_iff in Hine. destruct Hine as [e [He Hde]]. subst e'.
  apply in_map_iff in Hinf. destruct Hinf as [f [Hf Hdf]]. subst f'.
  assert (Hne0 : e <> f)
    by (intro Heq; apply Hne; rewrite Heq; reflexivity).
  assert (Hnetw0 : e <> twin f)
    by (intro Heq; apply Hnetw; rewrite Heq, reflect_edge_twin; reflexivity).
  destruct (HD e f Hde Hdf Hne0 Hnetw0) as [Hfst Hsnd].
  split.
  - intros [t [Ht [Hx Hy]]].
    apply Hfst. exists t.
    split; [ exact Ht | ].
    unfold reflect_edge, reflect_pt in Hx, Hy.
    destruct e as [a b]; destruct f as [c d].
    cbn [fst snd px py] in *.
    split; lra.
  - intros [t [Ht [Hx Hy]]].
    apply Hsnd. exists t.
    split; [ exact Ht | ].
    unfold reflect_edge, reflect_pt in Hx, Hy.
    destruct e as [a b]; destruct f as [c d].
    cbn [fst snd px py] in *.
    split; lra.
Qed.

Lemma ring_taut_reflect :
  forall r : Ring, ring_taut r -> ring_taut (reflect_ring r).
Proof.
  intros r Htaut e' f' Hine Hinf t s Ht Hs Hx Hy.
  rewrite ring_edges_reflect in Hine, Hinf.
  apply in_map_iff in Hine. destruct Hine as [e [He Hre]]. subst e'.
  apply in_map_iff in Hinf. destruct Hinf as [f [Hf Hrf]]. subst f'.
  assert (Hx0 : (1 - t) * px (fst e) + t * px (snd e)
                  = (1 - s) * px (fst f) + s * px (snd f)).
  { unfold reflect_edge, reflect_pt in Hx.
    destruct e as [a b]; destruct f as [c d].
    cbn [fst snd px py] in *. lra. }
  assert (Hy0 : (1 - t) * py (fst e) + t * py (snd e)
                  = (1 - s) * py (fst f) + s * py (snd f)).
  { unfold reflect_edge, reflect_pt in Hy.
    destruct e as [a b]; destruct f as [c d].
    cbn [fst snd px py] in *. lra. }
  destruct (Htaut e f Hre Hrf t s Ht Hs Hx0 Hy0) as [Hends | [H1 H2]].
  - left. exact Hends.
  - right.
    unfold reflect_edge. cbn [fst snd].
    rewrite H1, H2. split; reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  Headline: the eastward walk-dart corridor is ring-free.                 *)
(* -------------------------------------------------------------------------- *)

Theorem walk_dart_corridor_east_clear :
  forall (D : list Dart) (r : Ring) (x : Dart) (ylo yhi : R),
    ring_taut r ->
    pairwise_no_proper_cross_twin_aware D ->
    no_foreign_vertex_twin_aware D ->
    In x D ->
    (forall f, In f (ring_edges r) -> In f D) ->
    ((py (fst x) < ylo /\ yhi < py (snd x)) \/
     (py (snd x) < ylo /\ yhi < py (fst x))) ->
    ylo <= yhi ->
    exists delta0, 0 < delta0 /\
      forall delta, 0 < delta < delta0 ->
        forall y, ylo <= y <= yhi ->
          ~ ring_image r (corridor_east x delta y).
Proof.
  intros D r x ylo yhi Htaut Hcross Hforeign Hx HringD Hspan Hle.
  destruct (walk_dart_corridor_clear
              (map reflect_edge D) (reflect_ring r) (reflect_edge x)
              ylo yhi
              (ring_taut_reflect r Htaut)
              (pairwise_no_proper_cross_twin_aware_reflect D Hcross)
              (no_foreign_vertex_twin_aware_reflect D Hforeign))
    as [delta0 [Hd0 Hclear]].
  - apply in_map. exact Hx.
  - intros f' Hf'.
    rewrite ring_edges_reflect in Hf'.
    apply in_map_iff in Hf'. destruct Hf' as [f [Hf Hrf]]. subst f'.
    apply in_map. exact (HringD f Hrf).
  - unfold reflect_edge, reflect_pt.
    destruct x as [a b]. cbn [fst snd px py] in *.
    exact Hspan.
  - exact Hle.
  - exists delta0. split; [ exact Hd0 | ].
    intros delta Hd y Hw Himg.
    apply (Hclear delta Hd y Hw).
    rewrite corridor_reflect.
    apply ring_image_reflect.
    exact Himg.
Qed.

(* -------------------------------------------------------------------------- *)
(* Axiom audit.  Pure reflection transfer; allowlist axioms only.              *)
(* -------------------------------------------------------------------------- *)

Print Assumptions ring_image_reflect.
Print Assumptions walk_dart_corridor_east_clear.

(* ==========================================================================
   WalkVertexPack.v

   [H-bridge attack, C-3f discharge rung D-4a(i)] PER-VERTEX PACKAGING,
   the OFF-RING case: at a walk vertex in the ring complement, the D-2
   corner threshold holds with NO incident-edge bookkeeping at all.

   The trick: `walk_corner_threshold` parameterizes the two pruned
   slots by points `a`, `b`; choosing `a := b := v` makes
     - the pruned-clearance hypothesis VACUOUSLY total: `v` is off
       EVERY ring edge because it is in the complement
       (`off_ring_vertex_clearance` -- an on-edge witness would be a
       `ring_image` witness);
     - both germ-exclusion hypotheses free: `point_diff v v = vzero`,
       and the zero vector is never strictly inside an open sector
       (`vzero_not_in_sector`, both certificate crosses vanish).
   So the only remaining input is the gap nondegeneracy
   `vcross u1 u2 <> 0`, which the walk supplies from `fan_ok`'s
   pairwise nonparallelism (`cross_nonzero`).

   The ON-RING case -- identifying the two incident chain edges at a
   cycle vertex and discharging the pruned clearance from the
   twin-aware guards -- is D-4a(ii), the next rung.

   No `Admitted` / `Axiom` / `Parameter`; allowlist axioms only.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
   ========================================================================== *)

From Stdlib Require Import Reals Lra List.
From Stdlib Require Import Permutation.
From NTS.Proofs Require Import JordanRingKit.
From NTS.Proofs Require Import OverlayGraph Vec Azimuth Direction Dart
                               DartAngularOrder JCTHugStep RingClearance
                               SectorPath CornerSamples CornerConnector
                               FanGapSector FanCorner WalkCorners DartPath
                               RingExtract CycleRing GeneralTautBridge.

Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  The two vacuous inputs.                                                 *)
(* -------------------------------------------------------------------------- *)

(* A complement vertex is off EVERY ring edge -- the pruned-clearance
   hypothesis holds for any slot choice. *)
Lemma off_ring_vertex_clearance :
  forall (r : Ring) (v a b : Point),
    ring_complement r v ->
    forall f, In f (ring_edges r) -> f <> (a, v) -> f <> (v, b) ->
      ~ on_edge f v.
Proof.
  intros r v a b Hcomp f Hf _ _ [s [Hs [Hx Hy]]].
  apply Hcomp.
  exists f, s.
  split; [ exact Hf | ].
  split; [ exact Hs | ].
  split; [ exact Hx | exact Hy ].
Qed.

(* The zero vector is never strictly inside an open sector: both
   certificate crosses vanish. *)
Lemma vzero_not_in_sector :
  forall u1 u2 : Vec, ~ in_open_sector u1 u2 vzero.
Proof.
  intros u1 u2 Hin.
  unfold in_open_sector in Hin.
  rewrite vcross_zero_l, vcross_zero_r in Hin.
  destruct Hin as [[_ [H1 _]] | [_ [H1 | H1]]]; lra.
Qed.

Lemma point_diff_self : forall v : Point, point_diff v v = vzero.
Proof.
  intros [x y]. unfold point_diff, vzero. cbn. f_equal; ring.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  The off-ring corner threshold.                                          *)
(* -------------------------------------------------------------------------- *)

Theorem off_ring_corner_threshold :
  forall (r : Ring) (v : Point) (u1 u2 : Vec),
    no_horizontal_edges r ->
    ring_complement r v ->
    vcross u1 u2 <> 0 ->
    exists t rho_factor : R,
      0 < t /\ 0 < rho_factor /\
      forall delta, 0 < delta < t ->
        connected_in_complement_cont r
          (point_at v (corner_sample_in u1 (rho_factor * delta) delta))
          (point_at v (corner_sample_out u2 (rho_factor * delta) delta)).
Proof.
  intros r v u1 u2 Hnoh Hcomp Hcne.
  apply (walk_corner_threshold r v v v u1 u2 Hnoh).
  - exact (off_ring_vertex_clearance r v v v Hcomp).
  - rewrite point_diff_self. apply vzero_not_in_sector.
  - rewrite point_diff_self. apply vzero_not_in_sector.
  - exact Hcne.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  The ON-RING case: clearance at a cycle vertex.  [D-4a(ii)]              *)
(* -------------------------------------------------------------------------- *)

Lemma nodup_map_eq :
  forall (A B : Type) (g : A -> B) (l : list A) (x y : A),
    NoDup (map g l) -> In x l -> In y l -> g x = g y -> x = y.
Proof.
  intros A B g l.
  induction l as [| a l IH]; intros x y Hnd Hx Hy Hg; [ destruct Hx | ].
  cbn [map] in Hnd. inversion Hnd as [| ? ? Hnotin Hnd']; subst.
  destruct Hx as [-> | Hx]; destruct Hy as [-> | Hy].
  - reflexivity.
  - exfalso. apply Hnotin. rewrite Hg. apply in_map. exact Hy.
  - exfalso. apply Hnotin. rewrite <- Hg. apply in_map. exact Hx.
  - apply IH; assumption.
Qed.

Lemma point_eq_of_coords :
  forall p q : Point, px p = px q -> py p = py q -> p = q.
Proof.
  intros [x1 y1] [x2 y2]. cbn. intros -> ->. reflexivity.
Qed.

(* At a vertex-simple cycle vertex, every ring edge OTHER than the two
   incident chain edges avoids the vertex: an endpoint hit would break
   the NoDup trace (tips are the trace, bases its rotation), and an
   interior hit is a foreign-vertex violation. *)
Theorem on_ring_vertex_clearance :
  forall (D : list Dart) (d : Dart) (c : list Dart) (v : Point)
         (e_in e_out : Dart),
    dpath D (dtip d) (dbase d) c ->
    NoDup (dtip d :: map dtip c) ->
    ring_no_vertex_on_foreign_edge_interior (ring_of_chain (d :: c)) ->
    ring_edges (ring_of_chain (d :: c)) = d :: c ->
    In e_in (d :: c) -> In e_out (d :: c) ->
    dtip e_in = v -> dbase e_out = v ->
    forall f, In f (ring_edges (ring_of_chain (d :: c))) ->
      f <> e_in -> f <> e_out ->
      ~ on_edge f v.
Proof.
  intros D d c v e_in e_out Hp Hnd Hnfv Hedges Hin Hout Htip Hbase
         f Hf Hne1 Hne2 [s [Hs [Hx Hy]]].
  rewrite Hedges in Hf.
  assert (Htips : NoDup (map dtip (d :: c))) by (cbn [map]; exact Hnd).
  assert (Hbases : NoDup (map dbase (d :: c))).
  { cbn [map].
    pose proof (dpath_base_trace D (dtip d) (dbase d) c Hp) as Htr.
    eapply Permutation_NoDup.
    - apply Permutation_sym.
      apply (Permutation_cons_append (map dbase c) (dbase d)).
    - rewrite Htr. exact Hnd. }
  destruct (Rle_lt_or_eq_dec 0 s (proj1 Hs)) as [Hs0 | Hs0].
  - destruct (Rle_lt_or_eq_dec s 1 (proj2 Hs)) as [Hs1 | Hs1].
    + (* INTERIOR: v = snd e_in sits inside the foreign edge f *)
      assert (HinR : In e_in (ring_edges (ring_of_chain (d :: c))))
        by (rewrite Hedges; exact Hin).
      assert (HfR : In f (ring_edges (ring_of_chain (d :: c))))
        by (rewrite Hedges; exact Hf).
      destruct (Hnfv f e_in HfR HinR Hne1) as [_ Hsnd].
      apply Hsnd. exists s. split; [ lra | ].
      unfold dtip in Htip. rewrite Htip.
      split; [ exact Hx | exact Hy ].
    + (* s = 1: v IS the tip of f, so f = e_in by trace NoDup *)
      subst s.
      assert (Hveq : v = dtip f).
      { apply point_eq_of_coords.
        - rewrite Hx. unfold dtip. ring.
        - rewrite Hy. unfold dtip. ring. }
      apply Hne1.
      apply (nodup_map_eq _ _ dtip (d :: c) f e_in Htips Hf Hin).
      rewrite <- Hveq. exact (eq_sym Htip).
  - (* s = 0: v IS the base of f, so f = e_out by the rotated trace *)
    subst s.
    assert (Hveq : v = dbase f).
    { apply point_eq_of_coords.
      - rewrite Hx. unfold dbase. ring.
      - rewrite Hy. unfold dbase. ring. }
    apply Hne2.
    apply (nodup_map_eq _ _ dbase (d :: c) f e_out Hbases Hf Hout).
    rewrite <- Hveq. exact (eq_sym Hbase).
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  The on-ring corner threshold.                                           *)
(* -------------------------------------------------------------------------- *)

(* The incident chain edges fill the pruned slots; the germ exclusions
   stay caller-side (discharged at the walk from `fan_gap_uncertified`:
   the incident chain darts' germ-darts are fan members at v). *)
Theorem on_ring_corner_threshold :
  forall (D : list Dart) (d : Dart) (c : list Dart) (v a b : Point)
         (u1 u2 : Vec),
    no_horizontal_edges (ring_of_chain (d :: c)) ->
    dpath D (dtip d) (dbase d) c ->
    NoDup (dtip d :: map dtip c) ->
    ring_no_vertex_on_foreign_edge_interior (ring_of_chain (d :: c)) ->
    ring_edges (ring_of_chain (d :: c)) = d :: c ->
    In ((a, v) : Dart) (d :: c) ->
    In ((v, b) : Dart) (d :: c) ->
    ~ in_open_sector u1 u2 (point_diff a v) ->
    ~ in_open_sector u1 u2 (point_diff b v) ->
    vcross u1 u2 <> 0 ->
    exists t rho_factor : R,
      0 < t /\ 0 < rho_factor /\
      forall delta, 0 < delta < t ->
        connected_in_complement_cont (ring_of_chain (d :: c))
          (point_at v (corner_sample_in u1 (rho_factor * delta) delta))
          (point_at v (corner_sample_out u2 (rho_factor * delta) delta)).
Proof.
  intros D d c v a b u1 u2 Hnoh Hp Hnd Hnfv Hedges Hin Hout Hma Hmb Hcne.
  apply (walk_corner_threshold _ v a b u1 u2 Hnoh); try assumption.
  apply (on_ring_vertex_clearance D d c v (a, v) (v, b) Hp Hnd Hnfv Hedges
           Hin Hout); reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Axiom audit.  Per-vertex packaging; allowlist axioms only.                  *)
(* -------------------------------------------------------------------------- *)

Print Assumptions off_ring_vertex_clearance.
Print Assumptions off_ring_corner_threshold.
Print Assumptions on_ring_vertex_clearance.
Print Assumptions on_ring_corner_threshold.

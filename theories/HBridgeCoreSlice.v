(* ==========================================================================
   HBridgeCoreSlice.v

   [H-bridge attack, RUNG D core slice] The Euler-free reduction:
   `EdgeFaceBridge.H_bridge_premise` follows from ONE precisely-shaped
   face-transport premise -- everything else of rung D is proven here
   outright, with no `Admitted` and no Euler input.

   THE ARGUMENT (contrapositive).  Suppose `same_face (darts_of E) d
   (twin d)` and, for contradiction, `reachable (E_minus E d) (dtip d)
   (dbase d)`.  Rungs A/B (`DartPath.v`, `CycleRing.v`) produce a
   vertex-simple cycle `d :: c` whose ring `r` is simple, core-NoDup, and
   edge-faithful.  Under the two E-level generic-position guards defined
   here (`no_horizontal_darts`, `no_foreign_vertex_twin_aware` -- the
   twin-aware analogues of the JCT strand's standing guards, transferred
   to `r` through the twin-free cycle window), rung C-1/C-2's
   `straddle_side_core` produces, at a generic ray height, the CONCRETE
   pair `(edge_x_at d my - ef, my)` / `(edge_x_at d my + ef, my)` with
   OPPOSITE point-in-ring parity.  The named premise
   `face_transport_premise` asserts EQUAL parity for exactly that pair
   whenever `d` and `twin d` share a face -- the face-walk transport
   content that the remaining C-3 rungs (corner connectors, along-edge
   corridors, orbit induction) are building; it is carried as a
   hypothesis in the corpus's named-premise discipline (exactly how
   `H_bridge_premise` itself is carried), never asserted.  The two parity
   facts contradict intuitionistically.

   HEADLINE: `H_bridge_premise_of_transport` -- the first Euler-free
   derivation of the full `H_bridge_premise` shape (both orientation
   conjuncts, the mirror side via `same_face_sym` at `twin d`), from the
   transport premise plus standing combinatorial/noding hypotheses.
   Together with `EulerCoreInduction.euler_core_reduction`, this pins the
   entire remaining distance to the unconditional Euler formula onto the
   single transport premise.

   No `Admitted` / `Axiom` / `Parameter`; allowlist axioms only.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
   ========================================================================== *)

From Stdlib Require Import Reals Lra List Arith Lia.
From NTS.Proofs Require Import Distance Overlay OverlayGraph Dart
                               DartAngularOrder DartNextSpec DartFace
                               FaceOrbitSep EdgeConnectivity EdgeFaceBridge
                               ArrangementEMinus DartPath CycleRing
                               RingExtract PointInRingTangents
                               PointInRingCorrect JCTHalfOpenParity
                               JCTGenericStability JCTEscapeDescent
                               JCTHugStep JCTCorridor
                               JCTTautClearance GeneralTautBridge
                               EdgeCrossParity FaceTwinAware
                               StraddlePair StraddleSides.

Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  The two E-level generic-position guards (twin-aware).                   *)
(* -------------------------------------------------------------------------- *)

(* No dart of the arrangement is horizontal (the JCT strand's standing
   ray-casting guard, at the dart level; twins are horizontal together, so
   stating it on `darts_of E` is self-consistent). *)
Definition no_horizontal_darts (D : list Dart) : Prop :=
  forall x : Dart, In x D -> py (fst x) <> py (snd x).

(* No endpoint of one dart lies in the OPEN interior of a distinct,
   non-twin dart -- the twin-aware no-T-junction condition, mirroring
   `FaceTwinAware.pairwise_no_proper_cross_twin_aware`.  Like that
   predicate (and like `no_horizontal_darts` above), it is a NODING /
   general-position input carried from the arrangement pipeline, not
   derivable from the combinatorial hypotheses; the final Euler assembly
   supplies it from the same snap-rounding guarantees that discharge the
   pairwise no-crossing predicate. *)
Definition no_foreign_vertex_twin_aware (D : list Dart) : Prop :=
  forall e f : Dart,
    In e D -> In f D -> e <> f -> e <> twin f ->
    (~ exists t : R, 0 < t < 1 /\
         px (fst f) = (1 - t) * px (fst e) + t * px (snd e) /\
         py (fst f) = (1 - t) * py (fst e) + t * py (snd e))
    /\
    (~ exists t : R, 0 < t < 1 /\
         px (snd f) = (1 - t) * px (fst e) + t * px (snd e) /\
         py (snd f) = (1 - t) * py (fst e) + t * py (snd e)).

(* -------------------------------------------------------------------------- *)
(* §2  The named face-transport premise (the remaining rung-C content).        *)
(* -------------------------------------------------------------------------- *)

(* Whenever `d` shares a face with `twin d`, the two concrete straddle
   samples of `d` on the non-cut cycle ring have EQUAL parity.  This is
   exactly what walking the face orbit from `d` to `twin d` on the
   face side transports (the corner connectors and along-edge corridors
   of rung C-3 are its building blocks); it is the ONLY unproven content
   this file consumes. *)
Definition face_transport_premise (E : list Edge) : Prop :=
  forall (d : Dart) (c : list Dart) (my ef : R),
    In d E -> ~ In (twin d) E ->
    dbase d <> dtip d ->
    same_face (darts_of E) d (twin d) ->
    dpath (darts_of (E_minus E d)) (dtip d) (dbase d) c ->
    NoDup (dtip d :: map dtip c) ->
    (2 <= length c)%nat ->
    (forall v, In v (ring_of_chain (d :: c)) -> my <> py v) ->
    (exists t, 0 < t < 1 /\
       edge_x_at d my = (1 - t) * px (fst d) + t * px (snd d) /\
       my = (1 - t) * py (fst d) + t * py (snd d)) ->
    0 < ef ->
    ray_avoids_vertices (mkPoint (edge_x_at d my - ef) my)
                        (ring_of_chain (d :: c)) ->
    ray_avoids_vertices (mkPoint (edge_x_at d my + ef) my)
                        (ring_of_chain (d :: c)) ->
    ring_complement (ring_of_chain (d :: c))
                    (mkPoint (edge_x_at d my - ef) my) ->
    ring_complement (ring_of_chain (d :: c))
                    (mkPoint (edge_x_at d my + ef) my) ->
    (point_in_ring (mkPoint (edge_x_at d my - ef) my) (ring_of_chain (d :: c))
       <-> point_in_ring (mkPoint (edge_x_at d my + ef) my)
                         (ring_of_chain (d :: c))).

(* C-3e-4 connectivity discharge lives downstream in CornerCorridorBridge.v
   (`face_transport_premise_foreign_straddle_connected`, `corridor_safe_for_ef`);
   this file defines the premise only — Corner imports HBridge, not vice versa. *)

(* -------------------------------------------------------------------------- *)
(* §3  The one-sided core: same face + transport => not reachable.             *)
(* -------------------------------------------------------------------------- *)

(* Shared tail of the two orientation branches: once a generic height and
   the per-eps one-edge flip are in hand, `straddle_side_core` yields the
   OPPOSITE-parity pair, the transport premise yields EQUAL parity for the
   same two points, and the two clash intuitionistically. *)
Lemma straddle_transport_clash :
  forall (E : list Edge) (a0 b0 : Point) (c : list Dart) (my : R),
    face_transport_premise E ->
    In (a0, b0) E ->
    ~ In (twin (a0, b0)) E ->
    dbase (a0, b0) <> dtip (a0, b0) ->
    same_face (darts_of E) (a0, b0) (twin (a0, b0)) ->
    dpath (darts_of (E_minus E (a0, b0))) (dtip (a0, b0)) (dbase (a0, b0)) c ->
    NoDup (dtip (a0, b0) :: map dtip c) ->
    (2 <= length c)%nat ->
    ring_taut (ring_of_chain ((a0, b0) :: c)) ->
    no_horizontal_edges (ring_of_chain ((a0, b0) :: c)) ->
    ring_edges (ring_of_chain ((a0, b0) :: c)) = [] ++ (a0, b0) :: c ->
    ~ In (a0, b0) ([] ++ c) ->
    (forall v, In v (ring_of_chain ((a0, b0) :: c)) -> my <> py v) ->
    (exists t0, 0 < t0 < 1 /\
       edge_x_at (a0, b0) my
         = (1 - t0) * px (fst (a0, b0)) + t0 * px (snd (a0, b0)) /\
       my = (1 - t0) * py (fst (a0, b0)) + t0 * py (snd (a0, b0))) ->
    (forall eps, 0 < eps ->
       edge_crosses_ray_ho (mkPoint (edge_x_at (a0, b0) my - eps) my)
                           (a0, b0) /\
       ~ edge_crosses_ray_ho (mkPoint (edge_x_at (a0, b0) my + eps) my)
                             (a0, b0)) ->
    False.
Proof.
  intros E a0 b0 c my Hprem HdE Hntwin Hproper Hsf Hp Hnd Hlen
         Htaut Hnoh_r Hsplit Hdnotc Hgen Hint Hflip.
  set (r := ring_of_chain ((a0, b0) :: c)) in *.
  destruct (straddle_side_core r [] c (a0, b0) my Htaut Hnoh_r Hsplit
              Hdnotc Hgen Hint Hflip)
    as [ef [p1 [p2 [Hef [Hp1 [Hp2 [Hav1 [Hav2 [Hc1 [Hc2 Hiff]]]]]]]]]].
  rewrite Hp1 in Hav1, Hc1. rewrite Hp2 in Hav2, Hc2.
  rewrite Hp1, Hp2 in Hiff.
  pose proof (Hprem (a0, b0) c my ef HdE Hntwin Hproper Hsf Hp Hnd Hlen
                Hgen Hint Hef Hav1 Hav2 Hc1 Hc2) as Hpar.
  fold r in Hpar.
  assert (HnB : ~ point_in_ring (mkPoint (edge_x_at (a0, b0) my + ef) my) r)
    by (intro HB; exact (proj1 Hiff (proj2 Hpar HB) HB)).
  exact (HnB (proj1 Hpar (proj2 Hiff HnB))).
Qed.

Lemma same_face_not_reachable_core :
  forall (E : list Edge) (d : Dart),
    pairwise_no_proper_cross_twin_aware (darts_of E) ->
    no_horizontal_darts (darts_of E) ->
    no_foreign_vertex_twin_aware (darts_of E) ->
    face_transport_premise E ->
    In d E -> ~ In (twin d) E ->
    dbase d <> dtip d ->
    same_face (darts_of E) d (twin d) ->
    ~ reachable (E_minus E d) (dtip d) (dbase d).
Proof.
  intros E d Hpw Hnh Hnfv Hprem HdE Hntwin Hproper Hsf Hreach.
  destruct (non_cut_edge_cycle_ring E d Hpw HdE Hntwin Hproper Hreach)
    as [c [Hp [Hlen [Hnd [Hcc [Hclosed [Hmin [Hcore [Hsimple Hedges]]]]]]]]].
  set (r := ring_of_chain (d :: c)) in *.
  (* the cycle window is twin-free and drawn from darts_of E *)
  assert (Hwtf : forall x, In x (d :: c) -> ~ In (twin x) (d :: c))
    by (exact (cycle_window_twin_free (darts_of (E_minus E d)) d c
                 Hp Hnd Hlen Hproper)).
  assert (HWD : forall x, In x (d :: c) -> In x (darts_of E)).
  { intros x [Hxd | Hxc].
    - rewrite <- Hxd. apply in_darts_of_orig. exact HdE.
    - apply (incl_darts_of_E_minus E d).
      exact (dpath_darts_in _ _ _ _ Hp x Hxc). }
  (* generic-position guards transfer to the cycle ring *)
  assert (Hnoh_r : no_horizontal_edges r).
  { intros g Hg. rewrite Hedges in Hg. exact (Hnh g (HWD g Hg)). }
  assert (Hnfv_r : ring_no_vertex_on_foreign_edge_interior r).
  { intros e f He Hf Hne.
    rewrite Hedges in He, Hf.
    apply (Hnfv e f (HWD e He) (HWD f Hf) Hne).
    intro Hetf. apply (Hwtf f Hf). rewrite <- Hetf. exact He. }
  assert (Htaut : ring_taut r)
    by (exact (ring_taut_of_simple_and_no_foreign_vertex r Hsimple Hnfv_r)).
  (* the deleted dart is not on the surviving path *)
  assert (Hdnotc : ~ In d ([] ++ c)).
  { cbn [app]. intro Hdc.
    pose proof (dpath_darts_in _ _ _ _ Hp d Hdc) as HdD.
    destruct (proj1 (in_darts_of_E_minus_iff E d d Hntwin) HdD)
      as [_ [Hdd _]].
    exact (Hdd eq_refl). }
  assert (Hsplit : ring_edges r = [] ++ d :: c) by (cbn [app]; exact Hedges).
  (* the dart is non-horizontal *)
  assert (Hnh0 : py (fst d) <> py (snd d))
    by (exact (Hnh d (in_darts_of_orig E d HdE))).
  destruct d as [a0 b0].
  cbn [fst snd] in Hnh0.
  destruct (Rtotal_order (py a0) (py b0)) as [Hasc | [Heq | Hdesc]];
    [ | exfalso; exact (Hnh0 Heq) | ].
  - (* ascending dart *)
    destruct (avoid_finite_in_interval (map py r) (py a0) (py b0) Hasc)
      as [my [Hmy Hav]].
    assert (Hgen : forall v, In v r -> my <> py v)
      by (intros v Hv; exact (Hav (py v) (in_map py r v Hv))).
    set (t := (my - py a0) / (py b0 - py a0)).
    assert (Htd : t * (py b0 - py a0) = my - py a0)
      by (unfold t; field; lra).
    assert (Ht : 0 < t < 1) by nra.
    assert (Hint : exists t0, 0 < t0 < 1 /\
              edge_x_at (a0, b0) my
                = (1 - t0) * px (fst (a0, b0)) + t0 * px (snd (a0, b0)) /\
              my = (1 - t0) * py (fst (a0, b0)) + t0 * py (snd (a0, b0))).
    { exists t. split; [ exact Ht | ]. cbn [fst snd]. split.
      - unfold edge_x_at, t. field. lra.
      - nra. }
    assert (Hflip : forall eps, 0 < eps ->
              edge_crosses_ray_ho (mkPoint (edge_x_at (a0, b0) my - eps) my)
                                  (a0, b0) /\
              ~ edge_crosses_ray_ho (mkPoint (edge_x_at (a0, b0) my + eps) my)
                                    (a0, b0)).
    { intros eps Heps.
      exact (cross_ho_straddle_zero_asc a0 b0 my (edge_x_at (a0, b0) my) eps
               Hasc ltac:(lra) (edge_x_at_zero_asc a0 b0 my Hasc) Heps). }
    exact (straddle_transport_clash E a0 b0 c my Hprem HdE Hntwin Hproper
             Hsf Hp Hnd Hlen Htaut Hnoh_r Hsplit Hdnotc Hgen Hint Hflip).
  - (* descending dart: mirror.  Note the parameter t := (my - py a0) /
       (py b0 - py a0) is a quotient of two NEGATIVES here (my < py a0 is
       false -- my lies in (py b0, py a0) -- and the denominator is
       negative), so t is again strictly in (0,1) and `edge_x_at`'s affine
       formula is orientation-agnostic; only the straddle-crossing lemma
       needs the descending variant. *)
    destruct (avoid_finite_in_interval (map py r) (py b0) (py a0) Hdesc)
      as [my [Hmy Hav]].
    assert (Hgen : forall v, In v r -> my <> py v)
      by (intros v Hv; exact (Hav (py v) (in_map py r v Hv))).
    set (t := (my - py a0) / (py b0 - py a0)).
    assert (Htd : t * (py b0 - py a0) = my - py a0)
      by (unfold t; field; lra).
    assert (Ht : 0 < t < 1) by nra.
    assert (Hint : exists t0, 0 < t0 < 1 /\
              edge_x_at (a0, b0) my
                = (1 - t0) * px (fst (a0, b0)) + t0 * px (snd (a0, b0)) /\
              my = (1 - t0) * py (fst (a0, b0)) + t0 * py (snd (a0, b0))).
    { exists t. split; [ exact Ht | ]. cbn [fst snd]. split.
      - unfold edge_x_at, t. field. lra.
      - nra. }
    assert (Hflip : forall eps, 0 < eps ->
              edge_crosses_ray_ho (mkPoint (edge_x_at (a0, b0) my - eps) my)
                                  (a0, b0) /\
              ~ edge_crosses_ray_ho (mkPoint (edge_x_at (a0, b0) my + eps) my)
                                    (a0, b0)).
    { intros eps Heps.
      exact (cross_ho_straddle_zero_desc a0 b0 my (edge_x_at (a0, b0) my) eps
               Hdesc ltac:(lra) (edge_x_at_zero_desc a0 b0 my Hdesc) Heps). }
    exact (straddle_transport_clash E a0 b0 c my Hprem HdE Hntwin Hproper
             Hsf Hp Hnd Hlen Htaut Hnoh_r Hsplit Hdnotc Hgen Hint Hflip).
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Headline: the full H_bridge_premise, Euler-free, from the transport.    *)
(* -------------------------------------------------------------------------- *)

Theorem H_bridge_premise_of_transport :
  forall E : list Edge,
    (forall v : Point, fan_ok (outgoing v (darts_of E))) ->
    pairwise_no_proper_cross_twin_aware (darts_of E) ->
    no_horizontal_darts (darts_of E) ->
    no_foreign_vertex_twin_aware (darts_of E) ->
    face_transport_premise E ->
    H_bridge_premise E.
Proof.
  intros E Hfan Hpw Hnh Hnfv Hprem d HdD Hsf Hde.
  assert (Hproper : dbase d <> dtip d)
    by (apply dart_endpoints_neE; exact Hde).
  split.
  - intros HdE Hntwin.
    exact (same_face_not_reachable_core E d Hpw Hnh Hnfv Hprem
             HdE Hntwin Hproper Hsf).
  - intros HtwinE Hnd.
    assert (Hok : arrangement_ok (darts_of E))
      by (split; [ exact (darts_of_closed_under_twin E) | exact Hfan ]).
    assert (Hsf' : same_face (darts_of E) (twin d) (twin (twin d))).
    { rewrite twin_involutive.
      exact (same_face_sym (darts_of E) Hok d (twin d) HdD Hsf). }
    assert (Hntwin' : ~ In (twin (twin d)) E)
      by (rewrite twin_involutive; exact Hnd).
    assert (Hproper' : dbase (twin d) <> dtip (twin d)).
    { rewrite dbase_twin, dtip_twin.
      intro Hc. apply Hproper. symmetry. exact Hc. }
    pose proof (same_face_not_reachable_core E (twin d) Hpw Hnh Hnfv Hprem
                  HtwinE Hntwin' Hproper' Hsf') as Hnr.
    rewrite dtip_twin, dbase_twin in Hnr.
    exact Hnr.
Qed.

(* -------------------------------------------------------------------------- *)
(* Axiom audit.  Euler-free assembly; allowlist axioms only.                   *)
(* -------------------------------------------------------------------------- *)

Print Assumptions same_face_not_reachable_core.
Print Assumptions H_bridge_premise_of_transport.

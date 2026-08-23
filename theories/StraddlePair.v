(* ==========================================================================
   StraddlePair.v

   [H-bridge attack, rung C-1] The straddle pair: the two sides of any edge
   of a simple (taut, generically positioned) ring carry OPPOSITE
   point-in-ring parity.

   Rungs A/B (`DartPath.v`, `CycleRing.v`) produced, for a non-cut edge
   `d`, a vertex-simple cycle whose ring is `ring_simple` + core-NoDup.
   The eventual Euler-free discharge of `EdgeFaceBridge.H_bridge_premise`
   needs that ring to SEPARATE the two sides of `d`.  This rung banks the
   separation seed in full generality:

     for any edge `e0` of a ring that is simple, T-junction-free
     (`ring_no_vertex_on_foreign_edge_interior`), and horizontal-edge-free,
     there are two points `p1`, `p2` -- just left and just right of `e0`'s
     crossing abscissa at a generic ray height -- with
     `point_in_ring p1 r <-> ~ point_in_ring p2 r`.

   Assembly (all ingredients pre-existing, none previously connected):
     - `avoid_finite_in_interval` (new): a generic ray height exists --
       inside `e0`'s y-span, avoiding the finitely many vertex heights
       (interval-halving induction, no measure theory);
     - `ring_taut` (`JCTTautClearance`, via `GeneralTautBridge`'s bridge):
       an interior point of `e0` lies on NO other ring edge
       (`interior_point_off_other_edges`, new);
     - `ho_cross_stable_generic` (`JCTGenericStability`): each other
       edge's crossing status is locally constant at that interior point;
       `ho_cross_agree_ball` (new) assembles the finite minimum;
     - `cross_ho_straddle_zero_asc`/`_desc` (`EdgeCrossParity`): the
       straddled edge itself flips between `X - eps` and `X + eps`;
     - `point_in_ring_flip_one_edge` (`EdgeCrossParity`): agree-off +
       flip-on => opposite parity.

   The hypotheses are exactly `GeneralTautBridge.
   parity_seam_offring_of_simple`'s (minus `ring_core_nodup`, plus the
   split witness `~ In e0 (pre ++ suf)`, which core-NoDup supplies
   downstream) -- rung B delivers all of them for the non-cut-edge cycle
   ring except the two generic-position guards (no-T-junction,
   no-horizontal), which the corpus's JCT strand carries everywhere.

   Pure-R + list combinatorics; no `Admitted` / `Axiom` / `Parameter`;
   allowlist axioms only.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
   ========================================================================== *)

From Stdlib Require Import Reals Lra List Arith Lia.
From NTS.Proofs Require Import JctSeamPack.
From NTS.Proofs Require Import RingExtract JCTEscapeDescent EdgeCrossParity
                               JCTCorridor JCTTautClearance
                               GeneralTautBridge JCTHugStep.

Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  A generic value exists in any interval, avoiding a finite list.         *)
(* -------------------------------------------------------------------------- *)

(* Interval-halving induction: each avoided value can spoil at most one of
   the two half-interval candidates. *)
Lemma avoid_finite_in_interval :
  forall (L : list R) (lo hi : R),
    lo < hi ->
    exists y, lo < y < hi /\ (forall z, In z L -> y <> z).
Proof.
  induction L as [| z L IH]; intros lo hi Hlt.
  - exists ((lo + hi) / 2). split; [ lra | intros w [] ].
  - destruct (IH lo ((lo + hi) / 2) ltac:(lra)) as [y1 [Hy1 Hav1]].
    destruct (IH ((lo + hi) / 2) hi ltac:(lra)) as [y2 [Hy2 Hav2]].
    destruct (Req_dec y1 z) as [Heq | Hne].
    + exists y2. split; [ lra | ].
      intros w [Hw | Hw]; [ subst w; lra | exact (Hav2 w Hw) ].
    + exists y1. split; [ lra | ].
      intros w [Hw | Hw]; [ subst w; exact Hne | exact (Hav1 w Hw) ].
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  Ring-edge endpoints are ring vertices; generic height avoids the ray.   *)
(* -------------------------------------------------------------------------- *)

Lemma ring_edge_endpoints_in_ring :
  forall (r : Ring) (e : Edge),
    In e (ring_edges r) -> In (fst e) r /\ In (snd e) r.
Proof.
  intros r. induction r as [| a r IH]; intros e He.
  - destruct He.
  - destruct r as [| b r'].
    + destruct He.
    + rewrite ring_edges_cons2 in He.
      destruct He as [He | He].
      * subst e. cbn [fst snd].
        split; [ left; reflexivity | right; left; reflexivity ].
      * destruct (IH e He) as [H1 H2]. split; right; assumption.
Qed.

Lemma ray_avoids_vertices_of_generic_height :
  forall (r : Ring) (p : Point),
    (forall v, In v r -> py p <> py v) ->
    ray_avoids_vertices p r.
Proof.
  intros r p Hgen v Hv [Hpy _].
  exact (Hgen v Hv (eq_sym Hpy)).
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Finite assembly: one ball where every listed edge's status is shared.   *)
(* -------------------------------------------------------------------------- *)

Lemma ho_cross_agree_ball :
  forall (m : Point) (es : list Edge),
    (forall e, In e es ->
       exists eps, 0 < eps /\
         forall q' : Point,
           Rabs (px q' - px m) < eps -> Rabs (py q' - py m) < eps ->
           (edge_crosses_ray_ho q' e <-> edge_crosses_ray_ho m e)) ->
    exists eps, 0 < eps /\
      forall (q1 q2 : Point),
        Rabs (px q1 - px m) < eps -> Rabs (py q1 - py m) < eps ->
        Rabs (px q2 - px m) < eps -> Rabs (py q2 - py m) < eps ->
        forall e, In e es ->
          (edge_crosses_ray_ho q1 e <-> edge_crosses_ray_ho q2 e).
Proof.
  intros m es Hst. induction es as [| e es IH].
  - exists 1. split; [ lra | ]. intros q1 q2 _ _ _ _ e' [].
  - destruct (Hst e (or_introl eq_refl)) as [e1 [He1 Hb1]].
    destruct (IH (fun e' He' => Hst e' (or_intror He'))) as [e2 [He2 Hb2]].
    exists (Rmin e1 e2). split; [ apply Rmin_glb_lt; lra | ].
    intros q1 q2 Hx1 Hy1 Hx2 Hy2 e' [He' | He'].
    + subst e'.
      assert (Hq1x : Rabs (px q1 - px m) < e1)
        by (eapply Rlt_le_trans; [ exact Hx1 | apply Rmin_l ]).
      assert (Hq1y : Rabs (py q1 - py m) < e1)
        by (eapply Rlt_le_trans; [ exact Hy1 | apply Rmin_l ]).
      assert (Hq2x : Rabs (px q2 - px m) < e1)
        by (eapply Rlt_le_trans; [ exact Hx2 | apply Rmin_l ]).
      assert (Hq2y : Rabs (py q2 - py m) < e1)
        by (eapply Rlt_le_trans; [ exact Hy2 | apply Rmin_l ]).
      pose proof (Hb1 q1 Hq1x Hq1y).
      pose proof (Hb1 q2 Hq2x Hq2y).
      tauto.
    + assert (Hq1x : Rabs (px q1 - px m) < e2)
        by (eapply Rlt_le_trans; [ exact Hx1 | apply Rmin_r ]).
      assert (Hq1y : Rabs (py q1 - py m) < e2)
        by (eapply Rlt_le_trans; [ exact Hy1 | apply Rmin_r ]).
      assert (Hq2x : Rabs (px q2 - px m) < e2)
        by (eapply Rlt_le_trans; [ exact Hx2 | apply Rmin_r ]).
      assert (Hq2y : Rabs (py q2 - py m) < e2)
        by (eapply Rlt_le_trans; [ exact Hy2 | apply Rmin_r ]).
      exact (Hb2 q1 q2 Hq1x Hq1y Hq2x Hq2y e' He').
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Tautness: an interior point of one ring edge is off every other edge.   *)
(* -------------------------------------------------------------------------- *)

Lemma interior_point_off_other_edges :
  forall (r : Ring) (e0 f : Edge) (t : R) (q : Point),
    ring_taut r ->
    In e0 (ring_edges r) -> In f (ring_edges r) -> f <> e0 ->
    0 < t < 1 ->
    px q = (1 - t) * px (fst e0) + t * px (snd e0) ->
    py q = (1 - t) * py (fst e0) + t * py (snd e0) ->
    ~ (exists s, 0 <= s <= 1 /\
         px q = (1 - s) * px (fst f) + s * px (snd f) /\
         py q = (1 - s) * py (fst f) + s * py (snd f)).
Proof.
  intros r e0 f t q Htaut He0 Hf Hne Ht Hqx Hqy [s [Hs [Hsx Hsy]]].
  destruct (Htaut e0 f He0 Hf t s ltac:(lra) Hs
              (eq_trans (eq_sym Hqx) Hsx) (eq_trans (eq_sym Hqy) Hsy))
    as [[H0 | H1] | [Hff Hss]]; [ lra | lra | ].
  apply Hne.
  destruct e0 as [a0 b0]; destruct f as [af bf]; cbn [fst snd] in *.
  rewrite Hff, Hss. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  The crossing-abscissa zero forms (feeding the straddle lemmas).         *)
(* -------------------------------------------------------------------------- *)

Lemma edge_x_at_zero_asc : forall (a b : Point) (my : R),
  py a < py b ->
  (py b - py a) * (px a - edge_x_at (a, b) my)
    + (px b - px a) * (my - py a) = 0.
Proof.
  intros a b my Hab. unfold edge_x_at. field. lra.
Qed.

Lemma edge_x_at_zero_desc : forall (a b : Point) (my : R),
  py b < py a ->
  (py a - py b) * (px b - edge_x_at (a, b) my)
    + (px a - px b) * (my - py b) = 0.
Proof.
  intros a b my Hab. unfold edge_x_at. field. lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §6  The shared core: generic height + interior abscissa + per-eps flip      *)
(*     ==> a straddle pair with opposite parity.                               *)
(* -------------------------------------------------------------------------- *)

Lemma straddle_pair_core :
  forall (r : Ring) (pre suf : list Edge) (e0 : Edge) (my X : R),
    ring_taut r ->
    ring_edges r = pre ++ e0 :: suf ->
    ~ In e0 (pre ++ suf) ->
    (forall v, In v r -> my <> py v) ->
    (exists t, 0 < t < 1 /\
       X = (1 - t) * px (fst e0) + t * px (snd e0) /\
       my = (1 - t) * py (fst e0) + t * py (snd e0)) ->
    (forall eps, 0 < eps ->
       edge_crosses_ray_ho (mkPoint (X - eps) my) e0 /\
       ~ edge_crosses_ray_ho (mkPoint (X + eps) my) e0) ->
    exists p1 p2 : Point,
      ray_avoids_vertices p1 r /\
      ray_avoids_vertices p2 r /\
      (point_in_ring p1 r <-> ~ point_in_ring p2 r).
Proof.
  intros r pre suf e0 my X Htaut Hsplit Hnotin Hgen Hint Hflip.
  assert (He0in : In e0 (ring_edges r))
    by (rewrite Hsplit; apply in_or_app; right; left; reflexivity).
  set (m := mkPoint X my).
  (* every OTHER edge's crossing status is locally constant at m *)
  assert (Hstab : forall e, In e (pre ++ suf) ->
    exists eps, 0 < eps /\
      forall q' : Point,
        Rabs (px q' - px m) < eps -> Rabs (py q' - py m) < eps ->
        (edge_crosses_ray_ho q' e <-> edge_crosses_ray_ho m e)).
  { intros e He.
    assert (HeIn : In e (ring_edges r)).
    { rewrite Hsplit. apply in_app_or in He. apply in_or_app.
      destruct He as [He | He]; [ left; exact He | right; right; exact He ]. }
    assert (Hnee0 : e <> e0)
      by (intro Hc; apply Hnotin; rewrite <- Hc; exact He).
    destruct (ring_edge_endpoints_in_ring r e HeIn) as [Hfa Hfb].
    destruct e as [a b]. cbn [fst snd] in Hfa, Hfb.
    assert (Hoff : ~ (exists s, 0 <= s <= 1 /\
              px m = (1 - s) * px a + s * px b /\
              py m = (1 - s) * py a + s * py b)).
    { destruct Hint as [t [Ht [HX Hmy]]].
      pose proof (interior_point_off_other_edges r e0 (a, b) t m
                    Htaut He0in HeIn Hnee0 Ht) as Haux.
      cbn [fst snd] in Haux.
      apply Haux; cbn [px py]; assumption. }
    apply (ho_cross_stable_generic a b m Hoff); cbn [py].
    - exact (Hgen a Hfa).
    - exact (Hgen b Hfb). }
  destruct (ho_cross_agree_ball m (pre ++ suf) Hstab) as [eps [Heps Hball]].
  set (ef := eps / 2).
  set (p1 := mkPoint (X - ef) my).
  set (p2 := mkPoint (X + ef) my).
  assert (Hb1x : Rabs (px p1 - px m) < eps).
  { unfold p1, m. cbn [px].
    replace (X - ef - X) with (- ef) by lra.
    rewrite Rabs_Ropp, Rabs_right; unfold ef; lra. }
  assert (Hb2x : Rabs (px p2 - px m) < eps).
  { unfold p2, m. cbn [px].
    replace (X + ef - X) with ef by lra.
    rewrite Rabs_right; unfold ef; lra. }
  assert (Hb1y : Rabs (py p1 - py m) < eps).
  { unfold p1, m. cbn [py].
    unfold Rminus. rewrite Rplus_opp_r, Rabs_R0. lra. }
  assert (Hb2y : Rabs (py p2 - py m) < eps).
  { unfold p2, m. cbn [py].
    unfold Rminus. rewrite Rplus_opp_r, Rabs_R0. lra. }
  assert (Hav1 : ray_avoids_vertices p1 r).
  { apply ray_avoids_vertices_of_generic_height.
    intros v Hv. unfold p1. cbn [py]. exact (Hgen v Hv). }
  assert (Hav2 : ray_avoids_vertices p2 r).
  { apply ray_avoids_vertices_of_generic_height.
    intros v Hv. unfold p2. cbn [py]. exact (Hgen v Hv). }
  destruct (Hflip ef ltac:(unfold ef; lra)) as [Hc1 Hnc2].
  exists p1, p2.
  split; [ exact Hav1 | split; [ exact Hav2 | ] ].
  apply (point_in_ring_flip_one_edge p1 p2 r pre suf e0 Hsplit Hav1 Hav2).
  - intros e He. exact (Hball p1 p2 Hb1x Hb1y Hb2x Hb2y e He).
  - split; [ intros _; exact Hnc2 | intros _; exact Hc1 ].
Qed.

(* -------------------------------------------------------------------------- *)
(* §7  Headline: any edge of a simple, taut, generic ring separates parity.    *)
(* -------------------------------------------------------------------------- *)

Theorem straddle_pair_opposite_parity :
  forall (r : Ring) (pre suf : list Edge) (e0 : Edge),
    ring_simple r ->
    ring_no_vertex_on_foreign_edge_interior r ->
    no_horizontal_edges r ->
    ring_edges r = pre ++ e0 :: suf ->
    ~ In e0 (pre ++ suf) ->
    exists p1 p2 : Point,
      ray_avoids_vertices p1 r /\
      ray_avoids_vertices p2 r /\
      (point_in_ring p1 r <-> ~ point_in_ring p2 r).
Proof.
  intros r pre suf e0 Hsimple Hnov Hnoh Hsplit Hnotin.
  pose proof (ring_taut_of_simple_and_no_foreign_vertex r Hsimple Hnov)
    as Htaut.
  assert (He0in : In e0 (ring_edges r))
    by (rewrite Hsplit; apply in_or_app; right; left; reflexivity).
  destruct e0 as [a0 b0].
  assert (Hnh0 : py a0 <> py b0)
    by (pose proof (Hnoh (a0, b0) He0in) as H; cbn [fst snd] in H; exact H).
  destruct (Rtotal_order (py a0) (py b0)) as [Hasc | [Heq | Hdesc]];
    [ | exfalso; exact (Hnh0 Heq) | ].
  - (* ascending edge: pick a generic height inside (py a0, py b0) *)
    destruct (avoid_finite_in_interval (map py r) (py a0) (py b0) Hasc)
      as [my [Hmy Hav]].
    assert (Hgen : forall v, In v r -> my <> py v)
      by (intros v Hv; exact (Hav (py v) (in_map py r v Hv))).
    set (X := edge_x_at (a0, b0) my).
    set (t := (my - py a0) / (py b0 - py a0)).
    assert (Htd : t * (py b0 - py a0) = my - py a0)
      by (unfold t; field; lra).
    assert (Ht : 0 < t < 1) by nra.
    apply (straddle_pair_core r pre suf (a0, b0) my X Htaut Hsplit Hnotin Hgen).
    + exists t. split; [ exact Ht | ]. cbn [fst snd]. split.
      * unfold X, edge_x_at, t. field. lra.
      * nra.
    + intros eps Heps.
      exact (cross_ho_straddle_zero_asc a0 b0 my X eps Hasc
               ltac:(lra) (edge_x_at_zero_asc a0 b0 my Hasc) Heps).
  - (* descending edge: mirror, height inside (py b0, py a0) *)
    destruct (avoid_finite_in_interval (map py r) (py b0) (py a0) Hdesc)
      as [my [Hmy Hav]].
    assert (Hgen : forall v, In v r -> my <> py v)
      by (intros v Hv; exact (Hav (py v) (in_map py r v Hv))).
    set (X := edge_x_at (a0, b0) my).
    set (t := (my - py a0) / (py b0 - py a0)).
    assert (Htd : t * (py b0 - py a0) = my - py a0)
      by (unfold t; field; lra).
    assert (Ht : 0 < t < 1) by nra.
    apply (straddle_pair_core r pre suf (a0, b0) my X Htaut Hsplit Hnotin Hgen).
    + exists t. split; [ exact Ht | ]. cbn [fst snd]. split.
      * unfold X, edge_x_at, t. field. lra.
      * nra.
    + intros eps Heps.
      exact (cross_ho_straddle_zero_desc a0 b0 my X eps Hdesc
               ltac:(lra) (edge_x_at_zero_desc a0 b0 my Hdesc) Heps).
Qed.

(* -------------------------------------------------------------------------- *)
(* Axiom audit.  Pure-R + combinatorial wiring; allowlist axioms only.         *)
(* -------------------------------------------------------------------------- *)

Print Assumptions straddle_pair_opposite_parity.

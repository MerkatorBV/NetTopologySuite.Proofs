(* ==========================================================================
   StraddleSides.v

   [H-bridge attack, rung C-2] The straddle pair, GEOMETRICALLY LABELLED:
   a strictly-left and a strictly-right sample of any ring edge, both OFF
   the ring skeleton, with opposite point-in-ring parity.

   Rung C-1 (`StraddlePair.v`) produced two opposite-parity points
   straddling an edge's crossing abscissa, but said nothing about (a)
   which of them is on which SIDE of the directed edge, or (b) whether
   they avoid the ring skeleton itself (`ring_complement`) -- both needed
   before any face-side transport can consume the pair.  This rung adds
   both, still with NO analysis:

     - `dart_side` / `left_of_dart` / `right_of_dart`: the corpus's own
       orientation primitive (`Azimuth.turn_sign`, positive = CCW = left)
       applied to a directed edge and a query point;
     - `dart_side_straddle`: from the crossing-form zero, the west sample
       has side exactly `(py b - py a) * ef` and the east sample its
       negation -- so ascending edges put west on the LEFT, descending
       edges put west on the RIGHT, uniformly nonzero;
     - `on_edge_at_height_x`: on a non-horizontal edge, a point's height
       determines its abscissa (`edge_x_at`) -- so a sample lies ON some
       ring edge only if its offset `ef` hits one of finitely many
       abscissa gaps; choosing `ef` by `avoid_finite_in_interval` over
       that list gives `ring_complement` for free (no clearance analysis);
     - `opposite_parity_sym`: the parity biconditional can be read from
       either side (via the half-open parity decider under ray
       avoidance), so the left/right labelling can swap the pair;
     - `straddle_pair_sides` (headline): any edge of a simple,
       T-junction-free, horizontal-edge-free ring has a strictly-left and
       a strictly-right off-ring sample with opposite parity.

   Pure-R + list combinatorics; no `Admitted` / `Axiom` / `Parameter`;
   allowlist axioms only.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
   ========================================================================== *)

From Stdlib Require Import Reals Lra List Arith Lia.
From NTS.Proofs Require Import JctSeamPack.
From NTS.Proofs Require Import Vec Azimuth Dart RingExtract
                               JCTEscapeDescent EdgeCrossParity
                               JCTCorridor JCTTautClearance
                               GeneralTautBridge JCTHugStep StraddlePair
                               EdgeConnectivity RingClearance.
(* EdgeConnectivity (edge_eq_dec) and RingClearance (on_edge + the
   clearance-ball kit) import cleanly: both sit strictly below this file
   in the dependency order (RingClearance imports only Distance/Overlay/
   PointInRingTangents/JCTHugStep) -- checked cycle-free. *)

Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  Sides of a directed edge, in the corpus's own orientation primitive.    *)
(* -------------------------------------------------------------------------- *)

Definition dart_side (x : Dart) (p : Point) : R :=
  turn_sign (point_diff (dtip x) (dbase x)) (point_diff p (dbase x)).

Definition left_of_dart (x : Dart) (p : Point) : Prop := 0 < dart_side x p.
Definition right_of_dart (x : Dart) (p : Point) : Prop := dart_side x p < 0.

(* The ascending-shaped crossing-form zero holds for ANY non-horizontal
   edge (the `field` proof needs only a nonzero denominator) -- the
   orientation-agnostic feed for `dart_side_straddle`. *)
Lemma edge_x_at_zero_line : forall (a b : Point) (my : R),
  py a <> py b ->
  (py b - py a) * (px a - edge_x_at (a, b) my)
    + (px b - px a) * (my - py a) = 0.
Proof.
  intros a b my Hab. unfold edge_x_at. field. lra.
Qed.

(* From the crossing-form zero at abscissa X, the two straddle samples'
   sides are exactly +/- (py b - py a) * ef. *)
Lemma dart_side_straddle : forall (a0 b0 : Point) (my X ef : R),
  (py b0 - py a0) * (px a0 - X) + (px b0 - px a0) * (my - py a0) = 0 ->
  dart_side (a0, b0) (mkPoint (X - ef) my) = (py b0 - py a0) * ef /\
  dart_side (a0, b0) (mkPoint (X + ef) my) = - ((py b0 - py a0) * ef).
Proof.
  intros a0 b0 my X ef Hzero.
  unfold dart_side, turn_sign, vcross, point_diff, dtip, dbase.
  cbn [fst snd vx vy px py].
  split; nra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  On a non-horizontal edge, height determines abscissa.                   *)
(* -------------------------------------------------------------------------- *)

Lemma on_edge_at_height_x : forall (f : Edge) (q : Point) (s : R),
  py (fst f) <> py (snd f) ->
  px q = (1 - s) * px (fst f) + s * px (snd f) ->
  py q = (1 - s) * py (fst f) + s * py (snd f) ->
  px q = edge_x_at f (py q).
Proof.
  intros [fa fb] q s Hnh Hx Hy. cbn [fst snd] in *.
  unfold edge_x_at. rewrite Hx, Hy. field. lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  The parity biconditional reads from either side.                        *)
(* -------------------------------------------------------------------------- *)

Lemma opposite_parity_sym : forall (r : Ring) (p q : Point),
  ray_avoids_vertices q r ->
  (point_in_ring p r <-> ~ point_in_ring q r) ->
  (point_in_ring q r <-> ~ point_in_ring p r).
Proof.
  intros r p q Havq Hiff. split.
  - intros Hq Hp. exact (proj1 Hiff Hp Hq).
  - intros Hnp.
    rewrite <- (point_in_ring_ho_agrees q r Havq).
    unfold point_in_ring_ho.
    destruct (ho_parity_dec q (ring_edges r)) as [Ho | He]; [ exact Ho | ].
    exfalso. apply Hnp. apply (proj2 Hiff).
    intro Hq.
    rewrite <- (point_in_ring_ho_agrees q r Havq) in Hq.
    unfold point_in_ring_ho in Hq.
    exact (ho_parity_excl q (ring_edges r) Hq He).
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  The strengthened core: an offset avoiding every crossing abscissa.      *)
(* -------------------------------------------------------------------------- *)

Lemma straddle_side_core :
  forall (r : Ring) (pre suf : list Edge) (e0 : Edge) (my : R),
    ring_taut r ->
    no_horizontal_edges r ->
    ring_edges r = pre ++ e0 :: suf ->
    ~ In e0 (pre ++ suf) ->
    (forall v, In v r -> my <> py v) ->
    (exists t, 0 < t < 1 /\
       edge_x_at e0 my = (1 - t) * px (fst e0) + t * px (snd e0) /\
       my = (1 - t) * py (fst e0) + t * py (snd e0)) ->
    (forall eps, 0 < eps ->
       edge_crosses_ray_ho (mkPoint (edge_x_at e0 my - eps) my) e0 /\
       ~ edge_crosses_ray_ho (mkPoint (edge_x_at e0 my + eps) my) e0) ->
    exists (ef : R) (p1 p2 : Point),
      0 < ef /\
      p1 = mkPoint (edge_x_at e0 my - ef) my /\
      p2 = mkPoint (edge_x_at e0 my + ef) my /\
      ray_avoids_vertices p1 r /\
      ray_avoids_vertices p2 r /\
      ring_complement r p1 /\
      ring_complement r p2 /\
      (point_in_ring p1 r <-> ~ point_in_ring p2 r) /\
      (forall (q : Point) (f : Edge),
         In f (ring_edges r) -> f <> e0 ->
         py q = my -> Rabs (px q - edge_x_at e0 my) <= ef ->
         ~ on_edge f q).
Proof.
  intros r pre suf e0 my Htaut Hnoh Hsplit Hnotin Hgen Hint Hflip.
  assert (He0in : In e0 (ring_edges r))
    by (rewrite Hsplit; apply in_or_app; right; left; reflexivity).
  set (X := edge_x_at e0 my).
  set (m := mkPoint X my).
  (* every OTHER edge's crossing status is locally constant at m
     (same construction as StraddlePair's core) *)
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
      apply Haux; cbn [px py]; unfold X; assumption. }
    apply (ho_cross_stable_generic a b m Hoff); cbn [py].
    - exact (Hgen a Hfa).
    - exact (Hgen b Hfb). }
  destruct (ho_cross_agree_ball m (pre ++ suf) Hstab) as [eps [Heps Hball]].
  (* A pruned clearance ball around m, OFF every ring edge except e0.
     WHY eps2 > 0 IS AVAILABLE: m is an interior point of e0 (the
     `Hint` t-witness, 0 < t < 1), so `interior_point_off_other_edges`
     -- powered by `ring_taut` -- keeps m strictly off every OTHER
     ring edge; `off_edge_ball` (per edge, needs `no_horizontal_edges`)
     and `off_edges_ball_list` (the finite fold) then produce a
     POSITIVE sup-radius.  No new geometric input: tautness of the
     cycle ring is exactly what rung D's core slice already derives. *)
  set (keep := fun f : Edge => if edge_eq_dec f e0 then false else true).
  assert (Hkeep : forall f, In f (filter keep (ring_edges r)) <->
                    (In f (ring_edges r) /\ f <> e0)).
  { intro f. rewrite filter_In. unfold keep. split.
    - intros [Hf Hb]. split; [ exact Hf | ].
      destruct (edge_eq_dec f e0) as [He | Hne]; [ discriminate | exact Hne ].
    - intros [Hf Hne]. split; [ exact Hf | ].
      destruct (edge_eq_dec f e0); [ contradiction | reflexivity ]. }
  destruct (off_edges_ball_list (filter keep (ring_edges r)) m)
    as [eps2 [Heps2 Hball2]].
  { intros f Hf. apply Hkeep in Hf. destruct Hf as [HfIn Hne].
    apply off_edge_ball; [ exact (Hnoh f HfIn) | ].
    destruct Hint as [t [Ht [HXt Hmyt]]].
    apply (interior_point_off_other_edges r e0 f t m
             Htaut He0in HfIn Hne Ht).
    - unfold m. cbn [px]. unfold X. exact HXt.
    - unfold m. cbn [py]. exact Hmyt. }
  (* choose the offset avoiding every crossing abscissa at height my,
     inside BOTH balls *)
  assert (Hepsm : 0 < Rmin eps eps2) by (apply Rmin_glb_lt; assumption).
  destruct (avoid_finite_in_interval
              (map (fun f => X - edge_x_at f my) (ring_edges r)
               ++ map (fun f => edge_x_at f my - X) (ring_edges r))
              0 (Rmin eps eps2) Hepsm)
    as [ef [Hef Hefav]].
  pose proof (Rmin_l eps eps2) as Hml.
  pose proof (Rmin_r eps eps2) as Hmr.
  set (p1 := mkPoint (X - ef) my).
  set (p2 := mkPoint (X + ef) my).
  (* ball bounds *)
  assert (Hb1x : Rabs (px p1 - px m) < eps).
  { unfold p1, m. cbn [px].
    replace (X - ef - X) with (- ef) by lra.
    rewrite Rabs_Ropp, Rabs_right; lra. }
  assert (Hb2x : Rabs (px p2 - px m) < eps).
  { unfold p2, m. cbn [px].
    replace (X + ef - X) with ef by lra.
    rewrite Rabs_right; lra. }
  assert (Hb1y : Rabs (py p1 - py m) < eps).
  { unfold p1, m. cbn [py].
    unfold Rminus. rewrite Rplus_opp_r, Rabs_R0. lra. }
  assert (Hb2y : Rabs (py p2 - py m) < eps).
  { unfold p2, m. cbn [py].
    unfold Rminus. rewrite Rplus_opp_r, Rabs_R0. lra. }
  (* ray avoidance *)
  assert (Hav1 : ray_avoids_vertices p1 r).
  { apply ray_avoids_vertices_of_generic_height.
    intros v Hv. unfold p1. cbn [py]. exact (Hgen v Hv). }
  assert (Hav2 : ray_avoids_vertices p2 r).
  { apply ray_avoids_vertices_of_generic_height.
    intros v Hv. unfold p2. cbn [py]. exact (Hgen v Hv). }
  (* complement membership: a sample on some ring edge would pin ef to a
     forbidden abscissa gap *)
  assert (Hcomp1 : ring_complement r p1).
  { intros [f [t [HfIn [Ht [Hx Hy]]]]].
    assert (Hnh : py (fst f) <> py (snd f)) by (exact (Hnoh f HfIn)).
    pose proof (on_edge_at_height_x f p1 t Hnh Hx Hy) as Habs.
    unfold p1 in Habs. cbn [px py] in Habs.
    apply (Hefav (X - edge_x_at f my)).
    - apply in_or_app. left. exact (in_map (fun f => X - edge_x_at f my) _ f HfIn).
    - lra. }
  assert (Hcomp2 : ring_complement r p2).
  { intros [f [t [HfIn [Ht [Hx Hy]]]]].
    assert (Hnh : py (fst f) <> py (snd f)) by (exact (Hnoh f HfIn)).
    pose proof (on_edge_at_height_x f p2 t Hnh Hx Hy) as Habs.
    unfold p2 in Habs. cbn [px py] in Habs.
    apply (Hefav (edge_x_at f my - X)).
    - apply in_or_app. right. exact (in_map (fun f => edge_x_at f my - X) _ f HfIn).
    - lra. }
  (* the flip *)
  destruct (Hflip ef ltac:(lra)) as [Hc1 Hnc2].
  exists ef, p1, p2.
  split; [ lra | split; [ reflexivity | split; [ reflexivity |
    split; [ exact Hav1 | split; [ exact Hav2 |
    split; [ exact Hcomp1 | split; [ exact Hcomp2 | split ] ] ] ] ] ] ].
  - apply (point_in_ring_flip_one_edge p1 p2 r pre suf e0 Hsplit Hav1 Hav2).
    + intros e He. exact (Hball p1 p2 Hb1x Hb1y Hb2x Hb2y e He).
    + split; [ intros _; exact Hnc2 | intros _; exact Hc1 ].
  - (* THE STRIP SITS INSIDE THE PRUNED BALL.  The ball is 2-D with
       sup-radius eps2 around m = (X, my); the strip is its
       intersection with the line y = my, restricted to half-width
       ef.  Horizontally |px q - X| <= ef < Rmin eps eps2 <= eps2
       (strict, so the CLOSED strip fits in the OPEN ball); vertically
       py q = my = py m exactly, so the offset is 0 < eps2.  Both
       bounds below are those two facts verbatim. *)
    intros q f HfIn Hne Hqy Hqx.
    assert (HBX : Rabs (px q - px m) < eps2).
    { unfold m. cbn [px].
      eapply Rle_lt_trans; [ exact Hqx | lra ]. }
    assert (HBY : Rabs (py q - py m) < eps2).
    { unfold m. cbn [py]. rewrite Hqy.
      unfold Rminus. rewrite Rplus_opp_r, Rabs_R0. lra. }
    apply (Hball2 q HBX HBY f).
    apply Hkeep. split; assumption.
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  Headline: a strictly-left and a strictly-right off-ring sample with     *)
(*     opposite parity, for any edge of a simple/taut/generic ring.            *)
(* -------------------------------------------------------------------------- *)

Theorem straddle_pair_sides :
  forall (r : Ring) (pre suf : list Edge) (e0 : Edge),
    ring_simple r ->
    ring_no_vertex_on_foreign_edge_interior r ->
    no_horizontal_edges r ->
    ring_edges r = pre ++ e0 :: suf ->
    ~ In e0 (pre ++ suf) ->
    exists pL pR : Point,
      left_of_dart e0 pL /\
      right_of_dart e0 pR /\
      ray_avoids_vertices pL r /\
      ray_avoids_vertices pR r /\
      ring_complement r pL /\
      ring_complement r pR /\
      (point_in_ring pL r <-> ~ point_in_ring pR r).
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
  - (* ascending edge: west sample is LEFT *)
    destruct (avoid_finite_in_interval (map py r) (py a0) (py b0) Hasc)
      as [my [Hmy Hav]].
    assert (Hgen : forall v, In v r -> my <> py v)
      by (intros v Hv; exact (Hav (py v) (in_map py r v Hv))).
    set (t := (my - py a0) / (py b0 - py a0)).
    assert (Htd : t * (py b0 - py a0) = my - py a0)
      by (unfold t; field; lra).
    assert (Ht : 0 < t < 1) by nra.
    destruct (straddle_side_core r pre suf (a0, b0) my Htaut Hnoh Hsplit
                Hnotin Hgen)
      as [ef [p1 [p2 [Hef [Hp1 [Hp2 [Hav1 [Hav2 [Hc1 [Hc2 [Hiff _]]]]]]]]]]].
    + exists t. split; [ exact Ht | ]. cbn [fst snd]. split.
      * unfold edge_x_at, t. field. lra.
      * nra.
    + intros eps Heps.
      exact (cross_ho_straddle_zero_asc a0 b0 my (edge_x_at (a0, b0) my) eps
               Hasc ltac:(lra) (edge_x_at_zero_asc a0 b0 my Hasc) Heps).
    + destruct (dart_side_straddle a0 b0 my (edge_x_at (a0, b0) my) ef
                  (edge_x_at_zero_line a0 b0 my Hnh0)) as [Hs1 Hs2].
      rewrite <- Hp1 in Hs1. rewrite <- Hp2 in Hs2.
      exists p1, p2.
      split; [ unfold left_of_dart; rewrite Hs1; nra | ].
      split; [ unfold right_of_dart; rewrite Hs2; nra | ].
      split; [ exact Hav1 | split; [ exact Hav2 | ] ].
      split; [ exact Hc1 | split; [ exact Hc2 | exact Hiff ] ].
  - (* descending edge: west sample is RIGHT -- swap the pair *)
    destruct (avoid_finite_in_interval (map py r) (py b0) (py a0) Hdesc)
      as [my [Hmy Hav]].
    assert (Hgen : forall v, In v r -> my <> py v)
      by (intros v Hv; exact (Hav (py v) (in_map py r v Hv))).
    set (t := (my - py a0) / (py b0 - py a0)).
    assert (Htd : t * (py b0 - py a0) = my - py a0)
      by (unfold t; field; lra).
    assert (Ht : 0 < t < 1) by nra.
    destruct (straddle_side_core r pre suf (a0, b0) my Htaut Hnoh Hsplit
                Hnotin Hgen)
      as [ef [p1 [p2 [Hef [Hp1 [Hp2 [Hav1 [Hav2 [Hc1 [Hc2 [Hiff _]]]]]]]]]]].
    + exists t. split; [ exact Ht | ]. cbn [fst snd]. split.
      * unfold edge_x_at, t. field. lra.
      * nra.
    + intros eps Heps.
      exact (cross_ho_straddle_zero_desc a0 b0 my (edge_x_at (a0, b0) my) eps
               Hdesc ltac:(lra) (edge_x_at_zero_desc a0 b0 my Hdesc) Heps).
    + destruct (dart_side_straddle a0 b0 my (edge_x_at (a0, b0) my) ef
                  (edge_x_at_zero_line a0 b0 my Hnh0)) as [Hs1 Hs2].
      rewrite <- Hp1 in Hs1. rewrite <- Hp2 in Hs2.
      exists p2, p1.
      split; [ unfold left_of_dart; rewrite Hs2; nra | ].
      split; [ unfold right_of_dart; rewrite Hs1; nra | ].
      split; [ exact Hav2 | split; [ exact Hav1 | ] ].
      split; [ exact Hc2 | split; [ exact Hc1 | ] ].
      exact (opposite_parity_sym r p1 p2 Hav2 Hiff).
Qed.

(* -------------------------------------------------------------------------- *)
(* Axiom audit.  Pure-R + combinatorial wiring; allowlist axioms only.         *)
(* -------------------------------------------------------------------------- *)

Print Assumptions straddle_pair_sides.

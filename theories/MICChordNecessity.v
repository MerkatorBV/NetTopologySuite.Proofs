(* ============================================================================
   NetTopologySuite.Proofs.MICChordNecessity
   ----------------------------------------------------------------------------
   THE QUESTION (as posed): prove or give a counterexample — "MIC can only
   be made performant with chord approximation."

   The corpus never adjudicates wall-clock performance (that is the engine
   lane's perf gate).  What it CAN adjudicate is the mathematical content
   the necessity claim rests on, and that content is REFUTED in both
   directions:

   H-CHORD (refuted): "the MIC branch-and-bound certificate — JTS
   Cell.getMaxDistance soundness, the fact that makes grid pruning
   correct — requires linearizing curved boundaries into chords."

     - POSITIVE HALF: the certificate is metric-agnostic.
       `cell_achievable_radius_bound` (CellRadiusBound.v, 9004-d) is two
       triangle steps over an ABSTRACT obstacle region; instantiating its
       obstacle point at the attaining point of the exact arc metric
       (`arc_dist_exact`, LECArcRow.v) yields the bound with the exact
       curved boundary and the computable closed-form callback on the
       right-hand side (`mic_cell_bound_exact_arc`):

           r' <= arc_dist a c + sqrt 2 * h.

       No chord anywhere.  The same instantiation works for segment
       facets (`mic_cell_bound_exact_seg`) — the certificate never cared
       which row supplies the metric, only that the metric is EXACT
       (lower bound + attained), which is precisely what the typed rows
       proved.  The 1-Lipschitz certificates (`arc_dist_lipschitz`,
       `seg_dist_lipschitz`) fall out of the same exactness pair.

     - NEGATIVE HALF: chords are not merely unnecessary — a chord swap is
       NEVER exact at the disc's optimum.  Every chord of a circle
       strictly understates the clearance at the centre
       (`chord_strictly_understates`, via the parallelogram law: the
       chord's midpoint sits at squared distance r² − |AB|²/4 < r²), and
       in particular the arc's OWN chord — the segment linearization
       substitutes for it — understates the exact clearance
       (`chord_of_arc_understates_at_centre`).  The integer 3-4-5
       instance pins the gap exactly: arc (3,4)→(5,0)→(3,−4) about
       centre (0,0), exact clearance 5, chord clearance 3
       (`mic345_chord_gap`).  No refinement of a chord approximation
       ever closes this from inside a single chord — refining only
       shrinks the gap by adding MORE chords, i.e. more metric rows,
       never reaching the arc row's single exact evaluation.

   So the honest answer to the question: COUNTEREXAMPLE.  The exact-arc
   metric supports the identical branch-and-bound certificate with a
   closed-form per-evaluation callback (one radial formula + one sector
   gate — the same cost class as a chord row; the OBSTACLE_DISTANCE
   oracle prices both), while chord approximation is structurally inexact
   at any finite resolution.  What stays engine-side: constant factors
   and wall-clock (perf gate, JTS PR #8).

   WAYPOINT (failed/parked path, recorded per lane discipline): the
   O(n log n) CANDIDATE-WALK half for curved boundaries is NOT settled by
   this module.  The F8/F9 improvement kernels fix their sites: the
   kernel hypothesis names a per-site away-vector p − s with s CONSTANT,
   but an arc obstacle's nearest point a*(p) moves with p, so the
   two-nearest supplier does not instantiate as-stated.  The attempted
   reduction (treat a*(p) as a frozen point site per step) fails to close
   the kernel's tie case: the frozen site's distance is only a lower
   bound off-foot, and the strict-improvement conclusion needs the true
   arc distance.  Candidate completeness over arc obstacles — bisectors
   of arcs are conic loci — remains an open rung; the branch-and-bound
   certificate above is what the shipped MIC actually runs, and it is
   chord-free.

   No `Admitted`, no `Axiom`, no `Parameter`; classical-reals trio only.
   topic: metric

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude (Fable)
   ============================================================================ *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import Distance CurveGeometry ArcChordApprox
  CurveRingSimple ArcPointDistance LargestEmptyCircle CellRadiusBound
  LECSegmentRow LECArcRow LECCandidateComplete LECCandidateWeighted.

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  Lipschitz certificates from exactness.                                 *)
(* -------------------------------------------------------------------------- *)

(** The exact arc metric is 1-Lipschitz: exactness (lower + attained) is
    all the branch-and-bound stability argument ever needs. *)
Lemma arc_dist_lipschitz :
  forall (a : CircularArc) (P Q : Point),
    valid_arc a ->
    arc_dist a P <= dist P Q + arc_dist a Q.
Proof.
  intros a P Q Hva.
  destruct (arc_dist_exact a Q Hva) as [_ [X [HX Hd]]].
  destruct (arc_dist_exact a P Hva) as [Hlow _].
  specialize (Hlow X HX).
  pose proof (dist_triangle P Q X) as Htri.
  lra.
Qed.

Lemma seg_dist_lipschitz :
  forall (A B P Q : Point),
    seg_dist A B P <= dist P Q + seg_dist A B Q.
Proof.
  intros A B P Q.
  destruct (seg_dist_attained A B Q) as [X [HX Hd]].
  pose proof (seg_dist_lower A B P X HX) as Hlow.
  pose proof (dist_triangle P Q X) as Htri.
  lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  The exact-arc cell certificate: JTS Cell.getMaxDistance soundness      *)
(*     holds VERBATIM with exact curved boundaries.                           *)
(* -------------------------------------------------------------------------- *)

(** The branch-and-bound pruning bound with the exact arc callback: an
    empty radius achievable anywhere in a square cell is at most the
    centre's EXACT arc distance plus the cell circumradius.  One
    instantiation of the metric-agnostic 9004-d bound at the attaining
    arc point — no linearization. *)
Theorem mic_cell_bound_exact_arc :
  forall (a : CircularArc) (c p : Point) (h r' : R),
    valid_arc a ->
    0 <= h ->
    in_cell c h p ->
    empty_disk (on_arc a) p r' ->
    r' <= arc_dist a c + sqrt 2 * h.
Proof.
  intros a c p h r' Hva Hh Hcell Hemp.
  destruct (arc_dist_exact a c Hva) as [_ [X [HX Hd]]].
  pose proof (cell_achievable_radius_bound (on_arc a) c p h r' X
                Hh Hcell Hemp HX) as Hb.
  lra.
Qed.

(** The same certificate for a segment facet — the bound never cared
    which typed row supplies the metric. *)
Theorem mic_cell_bound_exact_seg :
  forall (A B c p : Point) (h r' : R),
    0 <= h ->
    in_cell c h p ->
    empty_disk (on_seg A B) p r' ->
    r' <= seg_dist A B c + sqrt 2 * h.
Proof.
  intros A B c p h r' Hh Hcell Hemp.
  destruct (seg_dist_attained A B c) as [X [HX Hd]].
  pose proof (cell_achievable_radius_bound (on_seg A B) c p h r' X
                Hh Hcell Hemp HX) as Hb.
  lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Chords strictly understate at the centre: the parallelogram law.       *)
(* -------------------------------------------------------------------------- *)

(** A chord's midpoint sits strictly inside the circle: squared distance
    r² − |AB|²/4 (parallelogram law), and |AB|² > 0 once A ≠ B. *)
Lemma chord_midpoint_strictly_inside :
  forall (O A B : Point) (r : R),
    0 < r ->
    dist O A = r -> dist O B = r -> A <> B ->
    dist O (seg_point A B (1 / 2)) < r.
Proof.
  intros O A B r Hr HA HB Hne.
  pose proof (dist_sq_of_dist O A r HA) as HsA.
  pose proof (dist_sq_of_dist O B r HB) as HsB.
  assert (HAB : 0 < dist_sq A B).
  { destruct A as [ax ay], B as [bx by_].
    unfold dist_sq. simpl.
    destruct (Req_EM_T ax bx) as [Ex | Ex];
      destruct (Req_EM_T ay by_) as [Ey | Ey].
    - exfalso. apply Hne. subst. reflexivity.
    - pose proof (Rsqr_pos_lt _ (Rminus_eq_contra _ _ Ey)) as Hp.
      pose proof (Rle_0_sqr (ax - bx)) as Hq.
      unfold Rsqr in Hp, Hq. lra.
    - pose proof (Rsqr_pos_lt _ (Rminus_eq_contra _ _ Ex)) as Hp.
      pose proof (Rle_0_sqr (ay - by_)) as Hq.
      unfold Rsqr in Hp, Hq. lra.
    - pose proof (Rsqr_pos_lt _ (Rminus_eq_contra _ _ Ex)) as Hp.
      pose proof (Rle_0_sqr (ay - by_)) as Hq.
      unfold Rsqr in Hp, Hq. lra. }
  apply dist_lt_of_sq_lt; [lra |].
  assert (Hpar : 4 * dist_sq O (seg_point A B (1 / 2))
                 = 2 * dist_sq O A + 2 * dist_sq O B - dist_sq A B)
    by (unfold dist_sq, seg_point; simpl; field).
  lra.
Qed.

(** EVERY chord of the circle strictly understates the clearance at the
    centre: the segment metric dips to at most the midpoint's depth. *)
Theorem chord_strictly_understates :
  forall (O A B : Point) (r : R),
    0 < r ->
    dist O A = r -> dist O B = r -> A <> B ->
    seg_dist A B O < r.
Proof.
  intros O A B r Hr HA HB Hne.
  assert (Hmid : on_seg A B (seg_point A B (1 / 2))).
  { exists (1 / 2). split; [lra | reflexivity]. }
  pose proof (seg_dist_lower A B O _ Hmid) as Hlow.
  pose proof (chord_midpoint_strictly_inside O A B r Hr HA HB Hne) as Hin.
  lra.
Qed.

(** The exact clearance at the circumcentre is the radius, on the nose. *)
Lemma arc_dist_centre :
  forall (a : CircularArc),
    valid_arc a ->
    arc_dist a (arc_center a) = arc_radius a.
Proof.
  intros a Hva.
  destruct (arc_dist_exact a (arc_center a) Hva) as [_ [X [HX Hd]]].
  pose proof (point_to_arc_dist_centre_is_r a (arc_center a) X Hva
                (dist_refl _) HX) as Hr.
  lra.
Qed.

(** THE COUNTEREXAMPLE, general form: the arc's OWN chord — the segment
    the linearization substitutes — strictly understates the exact
    clearance at the centre. *)
Theorem chord_of_arc_understates_at_centre :
  forall (a : CircularArc),
    valid_arc a ->
    arc_start a <> arc_end a ->
    0 < arc_radius a ->
    seg_dist (arc_start a) (arc_end a) (arc_center a)
      < arc_dist a (arc_center a).
Proof.
  intros a Hva Hne Hr.
  rewrite arc_dist_centre by exact Hva.
  apply chord_strictly_understates; [exact Hr | | | exact Hne].
  - reflexivity.
  - destruct (arc_center_equidistant a Hva) as [_ Hse].
    unfold arc_radius, dist. rewrite Hse. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  The integer 3-4-5 instance: exact clearance 5, chord clearance 3.      *)
(* -------------------------------------------------------------------------- *)

Definition mic345_arc : CircularArc :=
  mkCircularArc (mkPoint 3 4) (mkPoint 5 0) (mkPoint 3 (-4)).

Lemma mic345_valid : valid_arc mic345_arc.
Proof. unfold valid_arc. simpl. intro H. lra. Qed.

Lemma mic345_centre : arc_center mic345_arc = mkPoint 0 0.
Proof.
  unfold arc_center. simpl.
  assert (Hx : (3 * 3 + 4 * 4) * (0 - -4) + (5 * 5 + 0 * 0) * (-4 - 4)
               + (3 * 3 + (-4) * (-4)) * (4 - 0) = 0) by ring.
  assert (Hy : (3 * 3 + 4 * 4) * (3 - 5) + (5 * 5 + 0 * 0) * (3 - 3)
               + (3 * 3 + (-4) * (-4)) * (5 - 3) = 0) by ring.
  rewrite Hx, Hy. unfold Rdiv. rewrite !Rmult_0_l. reflexivity.
Qed.

Lemma mic345_radius : arc_radius mic345_arc = 5.
Proof.
  unfold arc_radius. rewrite mic345_centre.
  apply dist_of_sq; [lra |].
  unfold dist_sq. simpl. ring.
Qed.

(** The pinned gap: the exact metric answers 5 at the centre, the chord
    answers 3 — both on the nose, all integers. *)
Theorem mic345_chord_gap :
  seg_dist (mkPoint 3 4) (mkPoint 3 (-4)) (mkPoint 0 0) = 3 /\
  arc_dist mic345_arc (mkPoint 0 0) = 5.
Proof.
  split.
  - (* the chord x = 3: foot (3, 0), distance exactly 3 *)
    assert (Hup : seg_dist (mkPoint 3 4) (mkPoint 3 (-4)) (mkPoint 0 0)
                  <= 3).
    { assert (Hmid : on_seg (mkPoint 3 4) (mkPoint 3 (-4))
                       (seg_point (mkPoint 3 4) (mkPoint 3 (-4)) (1 / 2))).
      { exists (1 / 2). split; [lra | reflexivity]. }
      pose proof (seg_dist_lower (mkPoint 3 4) (mkPoint 3 (-4))
                    (mkPoint 0 0) _ Hmid) as Hlow.
      assert (Hd : dist (mkPoint 0 0)
                     (seg_point (mkPoint 3 4) (mkPoint 3 (-4)) (1 / 2)) = 3).
      { apply dist_of_sq; [lra |].
        unfold dist_sq, seg_point. simpl. field. }
      lra. }
    assert (Hdown : 3 <= seg_dist (mkPoint 3 4) (mkPoint 3 (-4))
                           (mkPoint 0 0)).
    { destruct (seg_dist_attained (mkPoint 3 4) (mkPoint 3 (-4))
                  (mkPoint 0 0)) as [X [[t [Ht ->]] Hd]].
      rewrite <- Hd.
      assert (Hsq : dist_sq (mkPoint 0 0)
                      (seg_point (mkPoint 3 4) (mkPoint 3 (-4)) t)
                    = 9 + (4 - 8 * t) * (4 - 8 * t))
        by (unfold dist_sq, seg_point; simpl; ring).
      assert (Hge : 9 <= dist_sq (mkPoint 0 0)
                           (seg_point (mkPoint 3 4) (mkPoint 3 (-4)) t)).
      { rewrite Hsq.
        pose proof (Rle_0_sqr (4 - 8 * t)) as Hs.
        unfold Rsqr in Hs. lra. }
      unfold dist.
      assert (Hs9 : sqrt 9 = 3).
      { replace 9 with (3 * 3) by ring. apply sqrt_square. lra. }
      apply Rle_trans with (sqrt 9).
      { rewrite Hs9. lra. }
      apply sqrt_le_1_alt. lra. }
    lra.
  - (* the exact metric at the centre is the radius *)
    rewrite <- mic345_centre.
    rewrite (arc_dist_centre mic345_arc mic345_valid).
    exact mic345_radius.
Qed.

(** The instance-level understatement, read off the pinned pair. *)
Corollary mic345_understates :
  seg_dist (mkPoint 3 4) (mkPoint 3 (-4)) (mkPoint 0 0)
    < arc_dist mic345_arc (mkPoint 0 0).
Proof.
  destruct mic345_chord_gap as [Hs Ha]. rewrite Hs, Ha. lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions arc_dist_lipschitz.
Print Assumptions seg_dist_lipschitz.
Print Assumptions mic_cell_bound_exact_arc.
Print Assumptions mic_cell_bound_exact_seg.
Print Assumptions chord_midpoint_strictly_inside.
Print Assumptions chord_strictly_understates.
Print Assumptions arc_dist_centre.
Print Assumptions chord_of_arc_understates_at_centre.
Print Assumptions mic345_valid.
Print Assumptions mic345_centre.
Print Assumptions mic345_radius.
Print Assumptions mic345_chord_gap.
Print Assumptions mic345_understates.

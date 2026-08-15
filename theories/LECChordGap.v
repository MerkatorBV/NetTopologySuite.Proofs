(* ============================================================================
   NetTopologySuite.Proofs.LECChordGap
   ----------------------------------------------------------------------------
   The LEC chord-path hypothesis, prove-or-disprove — GREEN (Qed-closed
   headline; Red surface planted and witnessed in the previous commit).

   HYPOTHESIS UNDER TEST (JTS OverlayNGCurve PERF-GATE, LEC row —
   name gate NTSC0001: never OverlayNGCurved):

     "LargestEmptyCircle stays on the chord path — no cheaper
      construction beat densify-then-LEC."

   VERDICT: **DISPROVED**, as an exactness claim, on the
   single-circle-obstacle cell — the LEC analogue of the two-disc cell
   that R1.5 (`CircularDiscOverlay` / `DISC_OVERLAY`) carved out of the
   overlay chord path.  Witness-scoped, fully explicit:

     - obstacle  = the full circle of radius 2 about the origin (the
       curved shoreline, every point of it);
     - domain    = the closed disk it bounds;
     - the EXACT answer is a CLOSED FORM: the largest empty disk is
       (centre, 2) — no densification, no search (the laser).  The
       maximality argument is the radial-projection construction: from
       any candidate centre O' at distance d from the origin, the
       nearest shoreline point along the ray through O' is at distance
       exactly 2 − d, so no candidate beats the origin;
     - the CHORD PATH at the 4-chord densification (vertices (±2,0),
       (0,±2), chords between adjacent vertices) has exact answer
       (centre, √2): each chord point is at least √2 from the origin
       (per-chord identity dist² = 2 + 2(2t−1)²), and in each quadrant
       the chord MIDPOINT (±1,±1) caps every candidate at √2 (via
       x² ≤ 2x on the quadrant-disk).  So densify-then-LEC computes √2
       where the truth is 2 — an underestimate by the factor cos(π/4);
       at a general chord step θ the same construction underestimates
       by cos(θ/2), CONVERGING but never exact.

   Headline (Qed):

     `lec_chord_hypothesis_refuted` :
        largest_empty_disk circle_obstacle disk_dom centre 2
        /\ largest_empty_disk chorded_obstacle disk_dom centre (sqrt 2)
        /\ sqrt 2 < 2.

   A cheaper construction therefore exists and beats densify-then-LEC
   on this cell in the only sense the corpus can adjudicate: it is
   exact where every finite densification is not.  The mismatch probe
   `exact_disk_not_chord_empty` pins the failure mode: the chord path
   cannot even CERTIFY the true disk — (centre, 2) is not empty of the
   chorded obstacle, its own chord midpoint (1,1) sits at distance √2
   inside it.

   CLAIMS vs PROVES.  The PERF-GATE hypothesis is a RUNTIME claim
   (median laser time vs chainsaw time); that half stays engine-side —
   this file proves the EXACTNESS half only: the closed form exists, is
   Qed-correct, and disagrees with the chord path's answer at the
   witness tolerance.  Whether JTS wires the closed form (as R1.5 did
   for two-disc overlay) is a product decision the perf gate can now
   make against a proven target.  General obstacle sets, arcs shorter
   than the full circle, and the general-θ cos(θ/2) law are next rungs.

   No `Admitted`, no `Axiom`, no `Parameter`; 3-axiom classical-reals
   footprint.

   Registered in `_CoqProject.full` only: it imports
   LargestEmptyCircle.v (MaximumInscribedCircle/InDisk lineage), so
   `make host` does not see it.

   Refs: docs/oracle-wishlist.md (OV-DISC / DISC_OVERLAY — the overlay
   twin of this refutation); siblings LargestEmptyCircle.v (empty_disk /
   largest_empty_disk / sq-bound helpers), MaximumInscribedCircle.v
   (#9004), PlaneConnected.v (seg), OverlayNGCurve.v (Phase-0: crossing
   cells never collapse algebraically — closed forms are per-shape).
   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import Distance PlaneConnected
  MaximumInscribedCircle LargestEmptyCircle.

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  The witness cell: circle obstacle, disk domain, 4-chord densification. *)
(* -------------------------------------------------------------------------- *)

Definition centre : Point := mkPoint 0 0.

(** The exact curved shoreline: EVERY point of the radius-2 circle. *)
Definition circle_obstacle : Region :=
  fun P => dist_sq centre P = 4.

(** The domain: the closed disk the shoreline bounds. *)
Definition disk_dom : Region :=
  fun P => dist_sq centre P <= 4.

(** The 4-chord densification vertices (the inscribed square). *)
Definition cv1 : Point := mkPoint 2 0.
Definition cv2 : Point := mkPoint 0 2.
Definition cv3 : Point := mkPoint (-2) 0.
Definition cv4 : Point := mkPoint 0 (-2).

(** A chord as a point set: the segment between two vertices. *)
Definition on_chord (A B : Point) (P : Point) : Prop :=
  exists t : R, 0 <= t <= 1 /\ P = seg A B t.

(** Densify-then-LEC's obstacle: the four chords of the inscribed
    square — what the chord path measures clearance against. *)
Definition chorded_obstacle : Region :=
  fun P => on_chord cv1 cv2 P \/ on_chord cv2 cv3 P \/
           on_chord cv3 cv4 P \/ on_chord cv4 cv1 P.

(* -------------------------------------------------------------------------- *)
(* §2  Square-root bridges.                                                   *)
(* -------------------------------------------------------------------------- *)

Lemma sqrt4_eq_2 : sqrt 4 = 2.
Proof.
  replace 4 with (Rsqr 2) by (unfold Rsqr; ring).
  apply sqrt_Rsqr. lra.
Qed.

Lemma sqrt2_sq : sqrt 2 * sqrt 2 = 2.
Proof. apply sqrt_sqrt. lra. Qed.

Lemma sqrt2_lt_2 : sqrt 2 < 2.
Proof.
  pose proof sqrt2_sq as Hs.
  pose proof (sqrt_pos 2) as Hp.
  nra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  The laser: the exact LEC of the circle obstacle is the closed          *)
(*     form (centre, 2).                                                      *)
(* -------------------------------------------------------------------------- *)

Lemma circle_empty : empty_disk circle_obstacle centre 2.
Proof.
  split; [lra |].
  intros P HP. unfold circle_obstacle in HP.
  unfold dist. rewrite HP. rewrite sqrt4_eq_2. lra.
Qed.

(** Radial projection: any domain candidate at distance d from the
    origin sees a shoreline point at exactly 2 − d, capping its radius. *)
Lemma circle_max :
  forall (O' : Point) (r' : R),
    disk_dom O' -> empty_disk circle_obstacle O' r' -> r' <= 2.
Proof.
  intros O' r' Hdom [Hr' He].
  unfold disk_dom, dist_sq, centre in Hdom. cbn [px py] in Hdom.
  assert (Hd2 : px O' * px O' + py O' * py O' <= 4) by nra.
  destruct (Rle_lt_dec (px O' * px O' + py O' * py O') 0) as [Hz | Hpos].
  - (* the candidate IS the origin: cap by the shoreline point (2,0) *)
    assert (Hx0 : px O' * px O' = 0)
      by (pose proof (Rle_0_sqr (px O')) as Hs; unfold Rsqr in Hs;
          pose proof (Rle_0_sqr (py O')) as Ht; unfold Rsqr in Ht; lra).
    assert (Hy0 : py O' * py O' = 0)
      by (pose proof (Rle_0_sqr (px O')) as Hs; unfold Rsqr in Hs;
          pose proof (Rle_0_sqr (py O')) as Ht; unfold Rsqr in Ht; lra).
    assert (Hx : px O' = 0)
      by (destruct (Rmult_integral _ _ Hx0); assumption).
    assert (Hy : py O' = 0)
      by (destruct (Rmult_integral _ _ Hy0); assumption).
    assert (Hob : circle_obstacle (mkPoint 2 0)).
    { unfold circle_obstacle, dist_sq, centre. cbn [px py]. lra. }
    pose proof (He (mkPoint 2 0) Hob) as Hle.
    assert (Hd : dist O' (mkPoint 2 0) = 2).
    { unfold dist.
      replace (dist_sq O' (mkPoint 2 0)) with 4.
      2:{ unfold dist_sq. cbn [px py]. rewrite Hx, Hy. ring. }
      exact sqrt4_eq_2. }
    lra.
  - (* the candidate is off-centre: project radially onto the circle *)
    set (d := sqrt (px O' * px O' + py O' * py O')).
    assert (Hdpos : 0 < d) by (unfold d; apply sqrt_lt_R0; exact Hpos).
    assert (Hdd : d * d = px O' * px O' + py O' * py O')
      by (unfold d; apply sqrt_sqrt; lra).
    assert (Hdle : d <= 2).
    { destruct (Rle_lt_dec d 2) as [| Hgt]; [assumption | exfalso; nra]. }
    set (Pstar := mkPoint (2 / d * px O') (2 / d * py O')).
    assert (Hne : d <> 0) by lra.
    assert (Hob : circle_obstacle Pstar).
    { unfold circle_obstacle, dist_sq, centre, Pstar. cbn [px py].
      replace ((0 - 2 / d * px O') * (0 - 2 / d * px O') +
               (0 - 2 / d * py O') * (0 - 2 / d * py O'))
        with (4 * ((px O' * px O' + py O' * py O') / (d * d)))
        by (field; exact Hne).
      rewrite Hdd. field. lra. }
    pose proof (He Pstar Hob) as Hle.
    assert (Hdist : dist O' Pstar = 2 - d).
    { unfold dist.
      assert (Hsq : dist_sq O' Pstar = (2 - d) * (2 - d)).
      { unfold dist_sq, Pstar. cbn [px py].
        replace ((px O' - 2 / d * px O') * (px O' - 2 / d * px O') +
                 (py O' - 2 / d * py O') * (py O' - 2 / d * py O'))
          with (((2 - d) * (2 - d)) *
                ((px O' * px O' + py O' * py O') / (d * d)))
          by (field; exact Hne).
        rewrite Hdd. field. lra. }
      rewrite Hsq.
      replace ((2 - d) * (2 - d)) with (Rsqr (2 - d)) by (unfold Rsqr; ring).
      apply sqrt_Rsqr. lra. }
    lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  The chainsaw: the exact LEC of the 4-chord densification is            *)
(*     (centre, √2).                                                          *)
(* -------------------------------------------------------------------------- *)

(** Every chord point is at least √2 from the origin: per chord,
    dist² = 2 + 2(2t−1)² ≥ 2. *)
Lemma chorded_empty : empty_disk chorded_obstacle centre (sqrt 2).
Proof.
  split; [apply sqrt_pos |].
  intros P HP.
  apply dist_ge_of_dist_sq_ge; [apply sqrt_pos |].
  rewrite sqrt2_sq.
  destruct HP as [H | [H | [H | H]]]; destruct H as [t [Ht ->]];
    unfold dist_sq, centre, seg, cv1, cv2, cv3, cv4; cbn [px py];
    pose proof (Rle_0_sqr (2*t - 1)) as Hsq; unfold Rsqr in Hsq; nra.
Qed.

(** In each quadrant the chord midpoint (±1,±1) caps every candidate:
    on the quadrant-disk, x² ≤ 2x and y² ≤ 2y give
    (x∓1)² + (y∓1)² ≤ 2. *)
Lemma chorded_max :
  forall (O' : Point) (r' : R),
    disk_dom O' -> empty_disk chorded_obstacle O' r' -> r' <= sqrt 2.
Proof.
  intros O' r' Hdom Hemp.
  pose proof (proj1 Hemp) as Hr'.
  unfold disk_dom, dist_sq, centre in Hdom. cbn [px py] in Hdom.
  assert (Hd2 : px O' * px O' + py O' * py O' <= 4) by nra.
  assert (Hx2 : px O' <= 2) by nra.
  assert (Hxm : -2 <= px O') by nra.
  assert (Hy2 : py O' <= 2) by nra.
  assert (Hym : -2 <= py O') by nra.
  pose proof sqrt2_sq as Hs2.
  pose proof (sqrt_pos 2) as Hs0.
  destruct (Rle_dec 0 (px O')) as [Hx | Hx];
    destruct (Rle_dec 0 (py O')) as [Hy | Hy].
  - (* quadrant ++ : midpoint (1,1) of chord cv1—cv2 *)
    assert (Hm : chorded_obstacle (mkPoint 1 1)).
    { left. exists (1/2). split; [lra |].
      unfold seg, cv1, cv2. cbn [px py].
      replace (2 + 1/2 * (0 - 2)) with 1 by lra.
      replace (0 + 1/2 * (2 - 0)) with 1 by lra.
      reflexivity. }
    pose proof (empty_disk_sq_bound chorded_obstacle O' r'
                  (mkPoint 1 1) Hemp Hm) as Hb.
    unfold dist_sq in Hb. cbn [px py] in Hb.
    nra.
  - (* quadrant +− : midpoint (1,−1) of chord cv4—cv1 *)
    assert (Hm : chorded_obstacle (mkPoint 1 (-1))).
    { right. right. right. exists (1/2). split; [lra |].
      unfold seg, cv4, cv1. cbn [px py].
      replace (0 + 1/2 * (2 - 0)) with 1 by lra.
      replace (-2 + 1/2 * (0 - -2)) with (-1) by lra.
      reflexivity. }
    pose proof (empty_disk_sq_bound chorded_obstacle O' r'
                  (mkPoint 1 (-1)) Hemp Hm) as Hb.
    unfold dist_sq in Hb. cbn [px py] in Hb.
    nra.
  - (* quadrant −+ : midpoint (−1,1) of chord cv2—cv3 *)
    assert (Hm : chorded_obstacle (mkPoint (-1) 1)).
    { right. left. exists (1/2). split; [lra |].
      unfold seg, cv2, cv3. cbn [px py].
      replace (0 + 1/2 * (-2 - 0)) with (-1) by lra.
      replace (2 + 1/2 * (0 - 2)) with 1 by lra.
      reflexivity. }
    pose proof (empty_disk_sq_bound chorded_obstacle O' r'
                  (mkPoint (-1) 1) Hemp Hm) as Hb.
    unfold dist_sq in Hb. cbn [px py] in Hb.
    nra.
  - (* quadrant −− : midpoint (−1,−1) of chord cv3—cv4 *)
    assert (Hm : chorded_obstacle (mkPoint (-1) (-1))).
    { right. right. left. exists (1/2). split; [lra |].
      unfold seg, cv3, cv4. cbn [px py].
      replace (-2 + 1/2 * (0 - -2)) with (-1) by lra.
      replace (0 + 1/2 * (-2 - 0)) with (-1) by lra.
      reflexivity. }
    pose proof (empty_disk_sq_bound chorded_obstacle O' r'
                  (mkPoint (-1) (-1)) Hemp Hm) as Hb.
    unfold dist_sq in Hb. cbn [px py] in Hb.
    nra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  Headline — GREEN: the hypothesis is refuted on this cell.              *)
(* -------------------------------------------------------------------------- *)

Theorem lec_chord_hypothesis_refuted :
  largest_empty_disk circle_obstacle disk_dom centre 2 /\
  largest_empty_disk chorded_obstacle disk_dom centre (sqrt 2) /\
  sqrt 2 < 2.
Proof.
  split; [| split].
  - split; [| split].
    + unfold disk_dom, dist_sq, centre. cbn [px py]. nra.
    + exact circle_empty.
    + exact circle_max.
  - split; [| split].
    + unfold disk_dom, dist_sq, centre. cbn [px py]. nra.
    + exact chorded_empty.
    + exact chorded_max.
  - exact sqrt2_lt_2.
Qed.

(** Projections for consumers. *)
Corollary lec_circle_closed_form :
  largest_empty_disk circle_obstacle disk_dom centre 2.
Proof. exact (proj1 lec_chord_hypothesis_refuted). Qed.

Corollary lec_chorded_answer :
  largest_empty_disk chorded_obstacle disk_dom centre (sqrt 2).
Proof. exact (proj1 (proj2 lec_chord_hypothesis_refuted)). Qed.

(* -------------------------------------------------------------------------- *)
(* §6  Pins and the mismatch probe.                                           *)
(* -------------------------------------------------------------------------- *)

(** The chainsaw's binding point: the chord midpoint (1,1) is a chorded
    obstacle point at squared distance exactly 2 from the centre. *)
Lemma chord_midpoint_witness :
  chorded_obstacle (mkPoint 1 1) /\ dist_sq centre (mkPoint 1 1) = 2.
Proof.
  split.
  - left. exists (1/2). split; [lra |].
    unfold seg, cv1, cv2. cbn [px py].
    replace (2 + 1/2 * (0 - 2)) with 1 by lra.
    replace (0 + 1/2 * (2 - 0)) with 1 by lra.
    reflexivity.
  - unfold dist_sq, centre. cbn [px py]. lra.
Qed.

(** Mismatch probe: the chord path cannot certify the TRUE disk — the
    exact answer (centre, 2) is not empty of the chorded obstacle. *)
Lemma exact_disk_not_chord_empty :
  ~ empty_disk chorded_obstacle centre 2.
Proof.
  intros [_ He].
  destruct chord_midpoint_witness as [Hm Hd].
  pose proof (He (mkPoint 1 1) Hm) as Hle.
  unfold dist in Hle. rewrite Hd in Hle.
  pose proof sqrt2_lt_2. lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.  3-axiom classical reals.                                 *)
(* -------------------------------------------------------------------------- *)

Print Assumptions lec_chord_hypothesis_refuted.
Print Assumptions circle_max.
Print Assumptions chorded_max.
Print Assumptions exact_disk_not_chord_empty.

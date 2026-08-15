(* ============================================================================
   NetTopologySuite.Proofs.LECObstacleDistance
   ----------------------------------------------------------------------------
   The typed obstacle-distance metric for LargestEmptyCircle — GREEN
   (Qed-closed headline).

   JTS/NTS twin: the package-private `ObstacleDistance` next to
   `algorithm.construct.LargestEmptyCircle` (jts-curve perf-gate lane): the
   engine now types each obstacle component and evaluates its clearance by
   the matching CLOSED-FORM metric instead of densifying — filled disc
   (CurvePolygon) at max(0, |p−c| − r), full-circle CircularString ring at
   ||p−c| − r|, collections flattened and folded by min.

   Why this file exists.  LECChordGap.v disproved the chord path as an
   exactness claim; the replacement is the typed metric, and the corpus
   said nothing about WHY a per-component closed form is the distance to
   the whole (infinite) obstacle point set.  This file supplies that
   bridge, on the two curved rows the engine added, in the corpus's own
   LEC vocabulary:

     `disc_dist`  = max(0, dist c P − r)   the filled-disc row
     `ring_dist`  = |dist c P − r|         the full-circle-ring row

     `empty_disk_disc_iff` / `empty_disk_ring_iff`
        emptiness against EVERY point of the disc/ring  ⟺  ONE
        closed-form comparison (each metric is both a lower bound —
        reverse triangle — and ATTAINED, by the radial projection);
     `empty_disk_union_iff` + `empty_disk_two_discs_iff`
        the flatten row: emptiness of a union is emptiness of each
        part, so clearance of a collection is the min of the parts;
     `min_disc_dist_weighted`
        the Apollonius reduction: min of clamped disc distances is the
        CLAMPED min of additively-weighted point distances
        max(0, min_i (|p−c_i| − r_i)) — LEC over discs is the weighted
        LEC over their centres, the O(n log n) candidate-enumeration
        target.

   The witness cell (fully rational, 3-4-5): discs of radius 3 at
   (±4, 0), domain the rectangle [−4,4] × [−3,3].  The LEC is centre
   (0, 3), radius 2 (`lec_two_discs`), and the maximisers are EXACTLY
   (0, ±3) (`lec_two_discs_maximisers`) — on the DOMAIN BOUNDARY and on
   the two-disc bisector, equidistant from both discs.

   FAILED PATHS (hypotheses refuted on this cell — each a guide toward
   the optimal algorithm; prose ledger: docs/lec-optimal-path.md):

     H-CORNER `corner_sampling_hypothesis_refuted`: "a radius achievable
       in a cell is achievable at a cell corner" — the sampling shortcut
       that would let branch-and-bound skip CellRadiusBound.v's √2·h
       slack.  REFUTED: all four rectangle corners TOUCH the discs
       (clearance 0) while the rectangle centre clears 1.  With 9004-d
       (slack sound, and not droppable at the centre) this closes the
       pincer: the Lipschitz slack is sound AND necessary; vertex
       sampling alone is unsound.

     H-INTERIOR `interior_maximiser_hypothesis_refuted`: "the optimum
       may be searched among interior points" (e.g. only at interior
       equidistant/Voronoi vertices).  REFUTED: every maximiser of this
       cell sits on the domain boundary py = ±3.  An optimal candidate
       enumeration must include bisector × boundary crossings — exactly
       the Voronoi-edge/boundary intersections of the classical
       O(n log n) LEC.

   CLAIMS vs PROVES.  This file proves the EXACTNESS of the typed metric
   and the witness-cell optimum; the engine-side runtime half (the perf
   gate's 15% slack vs the linearised chainsaw) and the arc rows
   (point-to-arc per 3-control window, CompoundCurve min) stay
   engine-side / next rungs.  No `Admitted`, no `Axiom`, no `Parameter`;
   3-axiom classical-reals footprint.

   Registered in `_CoqProject.full` only: it imports
   LargestEmptyCircle.v (MaximumInscribedCircle/InDisk lineage), so
   `make host` does not see it.

   Refs: siblings LargestEmptyCircle.v (empty_disk / largest_empty_disk),
   LECChordGap.v (the chord-path disproof this metric replaces),
   CellRadiusBound.v (9004-d cell pruning bound), Disk.v (in_disk),
   Distance.v (dist_triangle, dist_le_iff_dist_sq_le).
   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import Distance Disk MaximumInscribedCircle
  LargestEmptyCircle.

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  The typed rows: obstacle regions and their closed-form metrics.        *)
(* -------------------------------------------------------------------------- *)

(** The filled-disc obstacle (CurvePolygon row): every point of the closed
    disk, reusing Disk.v's [in_disk]. *)
Definition disc_obstacle (c : Point) (r : R) : Region :=
  in_disk (mkDisk c r).

(** The full-circle ring obstacle (closed CircularString row): every point
    of the circle itself, the shell without its interior. *)
Definition ring_obstacle (c : Point) (r : R) : Region :=
  fun P => dist_sq c P = r * r.

(** The typed metrics — the `ObstacleDistance` rows the engine computes. *)
Definition disc_dist (c : Point) (r : R) (P : Point) : R :=
  Rmax 0 (dist c P - r).

Definition ring_dist (c : Point) (r : R) (P : Point) : R :=
  Rabs (dist c P - r).

(** The flatten row: a collection obstacle is the union of its parts. *)
Definition runion (A B : Region) : Region := fun P => A P \/ B P.

(* -------------------------------------------------------------------------- *)
(* §2  Comparison bridges.                                                    *)
(* -------------------------------------------------------------------------- *)

Lemma dist_eq_of_dist_sq : forall (P Q : Point) (t : R),
  0 <= t -> dist_sq P Q = t * t -> dist P Q = t.
Proof.
  intros P Q t Ht Hsq. unfold dist. rewrite Hsq.
  replace (t * t) with (Rsqr t) by (unfold Rsqr; ring).
  apply sqrt_Rsqr. exact Ht.
Qed.

Lemma disc_dist_nonneg : forall c r P, 0 <= disc_dist c r P.
Proof. intros c r P. unfold disc_dist. apply Rmax_l. Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Metric correctness: each closed form is a LOWER bound on the distance  *)
(*     to every obstacle point (reverse triangle), and is ATTAINED by the     *)
(*     radial projection — the laser is exact, not just safe.                 *)
(* -------------------------------------------------------------------------- *)

(** One comparison certifies clearance against the WHOLE disc. *)
Lemma disc_dist_lower : forall c r P Q,
  0 <= r -> disc_obstacle c r Q -> disc_dist c r P <= dist P Q.
Proof.
  intros c r P Q Hr HQ.
  unfold disc_obstacle, in_disk in HQ; cbn [dcentre dradius] in HQ.
  assert (HcQ : dist c Q <= r)
    by (apply (proj2 (dist_le_iff_dist_sq_le c Q r Hr)); exact HQ).
  unfold disc_dist. apply Rmax_lub.
  - apply dist_nonneg.
  - pose proof (dist_triangle c Q P) as Ht.
    rewrite (dist_sym Q P) in Ht. lra.
Qed.

(** The bound is attained: the disc point nearest [P] is [P] itself (inside)
    or the radial projection of [P] onto the bounding circle (outside). *)
Lemma disc_dist_attained : forall c r P,
  0 <= r -> exists Q, disc_obstacle c r Q /\ dist P Q = disc_dist c r P.
Proof.
  intros c r P Hr.
  destruct (Rle_dec (dist c P) r) as [Hin | Hout].
  - exists P. split.
    + unfold disc_obstacle, in_disk; cbn [dcentre dradius].
      apply (proj1 (dist_le_iff_dist_sq_le c P r Hr)). exact Hin.
    + rewrite dist_refl. unfold disc_dist. symmetry.
      apply Rmax_left. lra.
  - apply Rnot_le_lt in Hout.
    assert (Hd0 : 0 < dist c P) by lra.
    set (d := dist c P).
    set (k := r / d).
    set (Q := mkPoint (px c + k * (px P - px c)) (py c + k * (py P - py c))).
    assert (Hdd : d * d = dist_sq c P) by (unfold d; apply dist_mul_self).
    assert (Hne : d <> 0) by (unfold d; lra).
    assert (HQc : dist_sq c Q = r * r).
    { unfold Q, dist_sq; cbn [px py].
      replace ((px c - (px c + k * (px P - px c)))
                 * (px c - (px c + k * (px P - px c)))
               + (py c - (py c + k * (py P - py c)))
                 * (py c - (py c + k * (py P - py c))))
        with (k * k * ((px c - px P) * (px c - px P)
                       + (py c - py P) * (py c - py P))) by ring.
      change ((px c - px P) * (px c - px P) + (py c - py P) * (py c - py P))
        with (dist_sq c P).
      rewrite <- Hdd. unfold k. field. exact Hne. }
    assert (HPQ : dist P Q = d - r).
    { apply dist_eq_of_dist_sq; [unfold d in *; lra |].
      unfold Q, dist_sq; cbn [px py].
      replace ((px P - (px c + k * (px P - px c)))
                 * (px P - (px c + k * (px P - px c)))
               + (py P - (py c + k * (py P - py c)))
                 * (py P - (py c + k * (py P - py c))))
        with ((1 - k) * (1 - k) * ((px c - px P) * (px c - px P)
                                   + (py c - py P) * (py c - py P))) by ring.
      change ((px c - px P) * (px c - px P) + (py c - py P) * (py c - py P))
        with (dist_sq c P).
      rewrite <- Hdd. unfold k. field. exact Hne. }
    exists Q. split.
    + unfold disc_obstacle, in_disk; cbn [dcentre dradius]. rewrite HQc. lra.
    + rewrite HPQ. unfold disc_dist. symmetry.
      apply Rmax_right. unfold d in *; lra.
Qed.

(** One comparison certifies clearance against the WHOLE ring. *)
Lemma ring_dist_lower : forall c r P Q,
  0 <= r -> ring_obstacle c r Q -> ring_dist c r P <= dist P Q.
Proof.
  intros c r P Q Hr HQ.
  assert (HcQ : dist c Q = r) by (apply dist_eq_of_dist_sq; assumption).
  unfold ring_dist. apply Rabs_le. split.
  - pose proof (dist_triangle c P Q) as Ht. lra.
  - pose proof (dist_triangle c Q P) as Ht.
    rewrite (dist_sym Q P) in Ht. lra.
Qed.

(** Attained on the ring: the radial projection again — and from the very
    centre, any circle point (the shell keeps distance r from c). *)
Lemma ring_dist_attained : forall c r P,
  0 <= r -> exists Q, ring_obstacle c r Q /\ dist P Q = ring_dist c r P.
Proof.
  intros c r P Hr.
  destruct (Req_dec (dist c P) 0) as [H0 | Hpos].
  - assert (Hsq0 : dist_sq c P = 0)
      by (rewrite <- (dist_mul_self c P); rewrite H0; ring).
    destruct (proj1 (dist_sq_zero_iff_eq c P) Hsq0) as [Hpx Hpy].
    exists (mkPoint (px c + r) (py c)). split.
    + unfold ring_obstacle, dist_sq; cbn [px py]. ring.
    + unfold ring_dist. rewrite H0.
      rewrite Rabs_left1 by lra.
      replace (- (0 - r)) with r by ring.
      apply dist_eq_of_dist_sq; [exact Hr |].
      unfold dist_sq; cbn [px py]. rewrite Hpx, Hpy. ring.
  - assert (Hd0 : 0 < dist c P)
      by (pose proof (dist_nonneg c P); lra).
    set (d := dist c P).
    set (k := r / d).
    set (Q := mkPoint (px c + k * (px P - px c)) (py c + k * (py P - py c))).
    assert (Hdd : d * d = dist_sq c P) by (unfold d; apply dist_mul_self).
    assert (Hne : d <> 0) by (unfold d; lra).
    assert (HQc : dist_sq c Q = r * r).
    { unfold Q, dist_sq; cbn [px py].
      replace ((px c - (px c + k * (px P - px c)))
                 * (px c - (px c + k * (px P - px c)))
               + (py c - (py c + k * (py P - py c)))
                 * (py c - (py c + k * (py P - py c))))
        with (k * k * ((px c - px P) * (px c - px P)
                       + (py c - py P) * (py c - py P))) by ring.
      change ((px c - px P) * (px c - px P) + (py c - py P) * (py c - py P))
        with (dist_sq c P).
      rewrite <- Hdd. unfold k. field. exact Hne. }
    assert (HPQ : dist P Q = Rabs (d - r)).
    { unfold dist.
      assert (Hsq : dist_sq P Q = (d - r) * (d - r)).
      { unfold Q, dist_sq; cbn [px py].
        replace ((px P - (px c + k * (px P - px c)))
                   * (px P - (px c + k * (px P - px c)))
                 + (py P - (py c + k * (py P - py c)))
                   * (py P - (py c + k * (py P - py c))))
          with ((1 - k) * (1 - k) * ((px c - px P) * (px c - px P)
                                     + (py c - py P) * (py c - py P))) by ring.
        change ((px c - px P) * (px c - px P) + (py c - py P) * (py c - py P))
          with (dist_sq c P).
        rewrite <- Hdd. unfold k. field. exact Hne. }
      rewrite Hsq.
      replace ((d - r) * (d - r)) with (Rsqr (d - r)) by (unfold Rsqr; ring).
      apply sqrt_Rsqr_abs. }
    exists Q. split.
    + unfold ring_obstacle. exact HQc.
    + rewrite HPQ. unfold ring_dist. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  The emptiness bridges: testing an empty disk against an INFINITE       *)
(*     obstacle point set collapses to one closed-form comparison — and       *)
(*     collections flatten by min (the engine's fold).                        *)
(* -------------------------------------------------------------------------- *)

Theorem empty_disk_disc_iff : forall (c : Point) (r : R) (O : Point) (rho : R),
  0 <= r ->
  (empty_disk (disc_obstacle c r) O rho <-> 0 <= rho /\ rho <= disc_dist c r O).
Proof.
  intros c r O rho Hr. split.
  - intros [Hrho He].
    destruct (disc_dist_attained c r O Hr) as [Q [HQ Hd]].
    split; [exact Hrho |]. rewrite <- Hd. exact (He Q HQ).
  - intros [Hrho Hle]. split; [exact Hrho |].
    intros Q HQ. pose proof (disc_dist_lower c r O Q Hr HQ). lra.
Qed.

Theorem empty_disk_ring_iff : forall (c : Point) (r : R) (O : Point) (rho : R),
  0 <= r ->
  (empty_disk (ring_obstacle c r) O rho <-> 0 <= rho /\ rho <= ring_dist c r O).
Proof.
  intros c r O rho Hr. split.
  - intros [Hrho He].
    destruct (ring_dist_attained c r O Hr) as [Q [HQ Hd]].
    split; [exact Hrho |]. rewrite <- Hd. exact (He Q HQ).
  - intros [Hrho Hle]. split; [exact Hrho |].
    intros Q HQ. pose proof (ring_dist_lower c r O Q Hr HQ). lra.
Qed.

(** Emptiness against a union is emptiness against each part — the
    soundness of flattening a collection obstacle. *)
Lemma empty_disk_union_iff : forall (A B : Region) (O : Point) (rho : R),
  empty_disk (runion A B) O rho <-> empty_disk A O rho /\ empty_disk B O rho.
Proof.
  intros A B O rho. unfold empty_disk, runion. split.
  - intros [Hrho He]. split; (split; [exact Hrho |]);
      intros P HP; apply He; [left | right]; exact HP.
  - intros [[Hrho HeA] [_ HeB]]. split; [exact Hrho |].
    intros P [HP | HP]; [apply HeA | apply HeB]; exact HP.
Qed.

(** The two-disc collection: clearance is the MIN of the two typed rows. *)
Corollary empty_disk_two_discs_iff :
  forall (c1 : Point) (r1 : R) (c2 : Point) (r2 : R) (O : Point) (rho : R),
  0 <= r1 -> 0 <= r2 ->
  (empty_disk (runion (disc_obstacle c1 r1) (disc_obstacle c2 r2)) O rho <->
   0 <= rho /\ rho <= Rmin (disc_dist c1 r1 O) (disc_dist c2 r2 O)).
Proof.
  intros c1 r1 c2 r2 O rho Hr1 Hr2. split.
  - intros H.
    apply (proj1 (empty_disk_union_iff _ _ _ _)) in H.
    destruct H as [H1 H2].
    apply (proj1 (empty_disk_disc_iff c1 r1 O rho Hr1)) in H1.
    apply (proj1 (empty_disk_disc_iff c2 r2 O rho Hr2)) in H2.
    destruct H1 as [Hrho Hd1]. destruct H2 as [_ Hd2].
    split; [exact Hrho | apply Rmin_glb; assumption].
  - intros [Hrho Hm].
    pose proof (Rmin_l (disc_dist c1 r1 O) (disc_dist c2 r2 O)).
    pose proof (Rmin_r (disc_dist c1 r1 O) (disc_dist c2 r2 O)).
    apply (proj2 (empty_disk_union_iff _ _ _ _)).
    split; [apply (proj2 (empty_disk_disc_iff c1 r1 O rho Hr1))
           | apply (proj2 (empty_disk_disc_iff c2 r2 O rho Hr2))];
      split; lra.
Qed.

(** The Apollonius reduction: clamping commutes with min, so the min of
    clamped disc distances IS the clamped min of additively-weighted point
    distances — LEC over discs is the weighted LEC over their centres. *)
Lemma rmin_rmax0 : forall x y : R,
  Rmin (Rmax 0 x) (Rmax 0 y) = Rmax 0 (Rmin x y).
Proof.
  intros x y. unfold Rmax, Rmin.
  destruct (Rle_dec 0 x); destruct (Rle_dec 0 y);
    repeat match goal with
           | |- context [Rle_dec ?a ?b] => destruct (Rle_dec a b)
           end; lra.
Qed.

Lemma min_disc_dist_weighted :
  forall (c1 : Point) (r1 : R) (c2 : Point) (r2 : R) (P : Point),
  Rmin (disc_dist c1 r1 P) (disc_dist c2 r2 P)
  = Rmax 0 (Rmin (dist c1 P - r1) (dist c2 P - r2)).
Proof. intros. unfold disc_dist. apply rmin_rmax0. Qed.

(* -------------------------------------------------------------------------- *)
(* §5  The witness cell: two 3-4-5 discs over a rectangle.  Fully rational —  *)
(*     the LEC is (0, 3) radius 2, and the maximisers are exactly (0, ±3).    *)
(* -------------------------------------------------------------------------- *)

Definition cL : Point := mkPoint (-4) 0.
Definition cR : Point := mkPoint 4 0.

Definition two_discs : Region :=
  runion (disc_obstacle cL 3) (disc_obstacle cR 3).

Definition rect_dom : Region :=
  fun P => -4 <= px P <= 4 /\ -3 <= py P <= 3.

(** The two-disc clearance the engine's fold computes on this cell. *)
Definition clearance (P : Point) : R :=
  Rmin (disc_dist cL 3 P) (disc_dist cR 3 P).

(** [clearance] IS the LEC objective on this cell: an empty radius is
    exactly a radius below the typed clearance. *)
Corollary clearance_is_lec_objective : forall (P : Point) (rho : R),
  empty_disk two_discs P rho <-> 0 <= rho /\ rho <= clearance P.
Proof.
  intros P rho. unfold two_discs, clearance.
  apply empty_disk_two_discs_iff; lra.
Qed.

(** 3-4-5 pins: the witness centre is at distance 5 from both disc centres. *)
Lemma dist_cL_witness : dist cL (mkPoint 0 3) = 5.
Proof.
  apply dist_eq_of_dist_sq; [lra |].
  unfold dist_sq, cL; cbn [px py]. lra.
Qed.

Lemma dist_cR_witness : dist cR (mkPoint 0 3) = 5.
Proof.
  apply dist_eq_of_dist_sq; [lra |].
  unfold dist_sq, cR; cbn [px py]. lra.
Qed.

(** Equidistance pin: the witness centre clears both discs at exactly 2 —
    it sits ON the two-disc bisector. *)
Lemma lec_two_discs_equidistant :
  disc_dist cL 3 (mkPoint 0 3) = 2 /\ disc_dist cR 3 (mkPoint 0 3) = 2.
Proof.
  unfold disc_dist. rewrite dist_cL_witness, dist_cR_witness.
  replace (5 - 3) with 2 by ring.
  rewrite (Rmax_right 0 2) by lra. split; reflexivity.
Qed.

(** The LEC of the two discs over the rectangle: centre (0, 3), radius 2. *)
Theorem lec_two_discs :
  largest_empty_disk two_discs rect_dom (mkPoint 0 3) 2.
Proof.
  assert (H3 : (0:R) <= 3) by lra.
  split; [| split].
  - unfold rect_dom; cbn [px py]. repeat split; lra.
  - apply (proj2 (empty_disk_two_discs_iff cL 3 cR 3 (mkPoint 0 3) 2 H3 H3)).
    split; [lra |].
    unfold disc_dist. rewrite dist_cL_witness, dist_cR_witness.
    replace (5 - 3) with 2 by ring.
    rewrite (Rmax_right 0 2) by lra.
    rewrite Rmin_left by lra. lra.
  - intros O' r' Hdom Hemp.
    apply (proj1 (empty_disk_two_discs_iff cL 3 cR 3 O' r' H3 H3)) in Hemp.
    destruct Hemp as [Hr' Hle].
    destruct Hdom as [[Hx1 Hx2] [Hy1 Hy2]].
    destruct (Rle_dec 0 (px O')) as [Hx | Hx].
    + assert (Hd5 : dist cR O' <= 5).
      { assert (H05 : (0:R) <= 5) by lra.
        apply (proj2 (dist_le_iff_dist_sq_le cR O' 5 H05)).
        unfold dist_sq, cR; cbn [px py]. nra. }
      assert (Hcap : disc_dist cR 3 O' <= 2).
      { unfold disc_dist. apply Rmax_lub; lra. }
      pose proof (Rmin_r (disc_dist cL 3 O') (disc_dist cR 3 O')). lra.
    + apply Rnot_le_lt in Hx.
      assert (Hd5 : dist cL O' <= 5).
      { assert (H05 : (0:R) <= 5) by lra.
        apply (proj2 (dist_le_iff_dist_sq_le cL O' 5 H05)).
        unfold dist_sq, cL; cbn [px py]. nra. }
      assert (Hcap : disc_dist cL 3 O' <= 2).
      { unfold disc_dist. apply Rmax_lub; lra. }
      pose proof (Rmin_l (disc_dist cL 3 O') (disc_dist cR 3 O')). lra.
Qed.

(** The maximisers, characterised: an empty radius of 2 pins the centre to
    exactly (0, 3) or (0, −3) — the bisector × boundary crossings. *)
Theorem lec_two_discs_maximisers : forall P : Point,
  rect_dom P -> empty_disk two_discs P 2 ->
  P = mkPoint 0 3 \/ P = mkPoint 0 (-3).
Proof.
  intros P Hdom Hemp.
  assert (H3 : (0:R) <= 3) by lra.
  apply (proj1 (empty_disk_two_discs_iff cL 3 cR 3 P 2 H3 H3)) in Hemp.
  destruct Hemp as [_ Hle].
  pose proof (Rmin_l (disc_dist cL 3 P) (disc_dist cR 3 P)) as HmL.
  pose proof (Rmin_r (disc_dist cL 3 P) (disc_dist cR 3 P)) as HmR.
  assert (HL : 2 <= disc_dist cL 3 P) by lra.
  assert (HR : 2 <= disc_dist cR 3 P) by lra.
  clear Hle HmL HmR.
  revert HL HR. unfold disc_dist, Rmax.
  destruct (Rle_dec 0 (dist cL P - 3)) as [HdL | HdL];
    destruct (Rle_dec 0 (dist cR P - 3)) as [HdR | HdR];
    intros HL HR; try (exfalso; lra).
  assert (HL5 : 5 <= dist cL P) by lra.
  assert (HR5 : 5 <= dist cR P) by lra.
  assert (HLsq : 25 <= dist_sq cL P).
  { rewrite <- (dist_mul_self cL P). nra. }
  assert (HRsq : 25 <= dist_sq cR P).
  { rewrite <- (dist_mul_self cR P). nra. }
  destruct P as [x y].
  unfold dist_sq, cL, cR in HLsq, HRsq; cbn [px py] in HLsq, HRsq.
  destruct Hdom as [[Hx1 Hx2] [Hy1 Hy2]]; cbn [px py] in Hx1, Hx2, Hy1, Hy2.
  assert (Hyy : y * y <= 9) by nra.
  (* right disc: (4−x)² ≥ 16 ⇒ x(x−8) ≥ 0 ⇒ x ≤ 0 (as x ≤ 4 < 8) *)
  assert (HfR : x * (x - 8) >= 0) by nra.
  assert (Hxle : x <= 0) by nra.
  (* left disc: (−4−x)² ≥ 16 ⇒ x(x+8) ≥ 0 ⇒ 0 ≤ x (as −8 < −4 ≤ x) *)
  assert (HfL : x * (x + 8) >= 0) by nra.
  assert (Hxge : 0 <= x) by nra.
  assert (Hx0 : x = 0) by lra.
  subst x.
  assert (Hy9 : y * y = 9) by nra.
  assert (Hy33 : (y - 3) * (y + 3) = 0) by nra.
  destruct (Rmult_integral _ _ Hy33) as [Hy3 | Hy3].
  - left. f_equal; lra.
  - right. f_equal; lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §6  Failed paths — the refuted hypotheses (each with its guide).           *)
(* -------------------------------------------------------------------------- *)

Definition rect_corners (P : Point) : Prop :=
  P = mkPoint (-4) (-3) \/ P = mkPoint (-4) 3 \/
  P = mkPoint 4 (-3) \/ P = mkPoint 4 3.

(** Every rectangle corner TOUCHES a disc: clearance exactly 0. *)
Lemma corner_clearance_zero : forall C : Point,
  rect_corners C -> clearance C = 0.
Proof.
  assert (HL : forall b : R, b * b = 9 ->
            dist cL (mkPoint (-4) b) = 3).
  { intros b Hb. apply dist_eq_of_dist_sq; [lra |].
    unfold dist_sq, cL; cbn [px py]. nra. }
  assert (HR : forall b : R, b * b = 9 ->
            dist cR (mkPoint 4 b) = 3).
  { intros b Hb. apply dist_eq_of_dist_sq; [lra |].
    unfold dist_sq, cR; cbn [px py]. nra. }
  intros C [-> | [-> | [-> | ->]]]; unfold clearance, disc_dist.
  - rewrite (HL (-3)) by lra.
    replace (3 - 3) with 0 by ring.
    rewrite (Rmax_left 0 0) by lra.
    apply Rmin_left. apply Rmax_l.
  - rewrite (HL 3) by lra.
    replace (3 - 3) with 0 by ring.
    rewrite (Rmax_left 0 0) by lra.
    apply Rmin_left. apply Rmax_l.
  - rewrite (HR (-3)) by lra.
    replace (3 - 3) with 0 by ring.
    rewrite (Rmax_left 0 0) by lra.
    apply Rmin_right. apply Rmax_l.
  - rewrite (HR 3) by lra.
    replace (3 - 3) with 0 by ring.
    rewrite (Rmax_left 0 0) by lra.
    apply Rmin_right. apply Rmax_l.
Qed.

(** The rectangle centre clears 1. *)
Lemma centre_clearance_one : clearance (mkPoint 0 0) = 1.
Proof.
  assert (HdL : dist cL (mkPoint 0 0) = 4)
    by (apply dist_eq_of_dist_sq;
        [lra | unfold dist_sq, cL; cbn [px py]; lra]).
  assert (HdR : dist cR (mkPoint 0 0) = 4)
    by (apply dist_eq_of_dist_sq;
        [lra | unfold dist_sq, cR; cbn [px py]; lra]).
  unfold clearance, disc_dist. rewrite HdL, HdR.
  replace (4 - 3) with 1 by ring.
  rewrite (Rmax_right 0 1) by lra.
  apply Rmin_left. lra.
Qed.

(** H-CORNER, REFUTED: "a radius achievable in a cell is achievable at a
    cell corner."  The centre achieves 1; every corner caps at 0.  Vertex
    sampling cannot upper-bound a cell — the √2·h Lipschitz slack of
    CellRadiusBound.v (9004-d) is not just sound but NECESSARY. *)
Theorem corner_sampling_hypothesis_refuted :
  ~ (forall (P : Point) (rho : R),
       rect_dom P -> empty_disk two_discs P rho ->
       exists C, rect_corners C /\ empty_disk two_discs C rho).
Proof.
  intros H.
  assert (Hdom : rect_dom (mkPoint 0 0))
    by (unfold rect_dom; cbn [px py]; repeat split; lra).
  assert (Hemp : empty_disk two_discs (mkPoint 0 0) 1).
  { apply (proj2 (clearance_is_lec_objective (mkPoint 0 0) 1)).
    rewrite centre_clearance_one. lra. }
  destruct (H (mkPoint 0 0) 1 Hdom Hemp) as [C [HC HempC]].
  apply (proj1 (clearance_is_lec_objective C 1)) in HempC.
  destruct HempC as [_ HleC].
  rewrite (corner_clearance_zero C HC) in HleC. lra.
Qed.

(** H-INTERIOR, REFUTED: "the optimum may be searched among interior
    points."  Every maximiser of this cell sits on the domain boundary
    (py = ±3), on the two-disc bisector — the candidate set of an optimal
    algorithm must include bisector × boundary crossings. *)
Theorem interior_maximiser_hypothesis_refuted :
  ~ (exists P : Point,
       rect_dom P /\ empty_disk two_discs P 2 /\
       -4 < px P < 4 /\ -3 < py P < 3).
Proof.
  intros [P [Hdom [Hemp [Hx Hy]]]].
  destruct (lec_two_discs_maximisers P Hdom Hemp) as [-> | ->];
    cbn [px py] in Hy; lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §7  Headline — GREEN: the typed metric is exact and the witness cell is    *)
(*     closed.                                                                *)
(* -------------------------------------------------------------------------- *)

Theorem obstacle_distance_headline :
  (forall (c : Point) (r : R) (O : Point) (rho : R), 0 <= r ->
     (empty_disk (disc_obstacle c r) O rho <->
      0 <= rho /\ rho <= disc_dist c r O)) /\
  (forall (c : Point) (r : R) (O : Point) (rho : R), 0 <= r ->
     (empty_disk (ring_obstacle c r) O rho <->
      0 <= rho /\ rho <= ring_dist c r O)) /\
  largest_empty_disk two_discs rect_dom (mkPoint 0 3) 2.
Proof.
  split; [exact empty_disk_disc_iff
         | split; [exact empty_disk_ring_iff | exact lec_two_discs]].
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.  3-axiom classical reals.                                 *)
(* -------------------------------------------------------------------------- *)

Print Assumptions obstacle_distance_headline.
Print Assumptions empty_disk_disc_iff.
Print Assumptions empty_disk_ring_iff.
Print Assumptions empty_disk_two_discs_iff.
Print Assumptions min_disc_dist_weighted.
Print Assumptions lec_two_discs.
Print Assumptions lec_two_discs_maximisers.
Print Assumptions corner_sampling_hypothesis_refuted.
Print Assumptions interior_maximiser_hypothesis_refuted.

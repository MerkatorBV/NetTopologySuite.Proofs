(* ============================================================================
   NetTopologySuite.Proofs.RelateNGRingInclusion
   ----------------------------------------------------------------------------
   Issue #568 / #522 claimId 522-g: half-open ring-inclusion groundwork
   for per-cell matrix claims (relate bar 2).

   Per-cell statements such as "the interior of A meets the exterior of B
   in dimension 2" need an open-disk neighbourhood of a strict-`gtri`
   point, and "the boundary carries dimension 1" needs two distinct
   points on a segment.  This module supplies those enablers.  It does
   not remint a matrix fill: `aa_matrix_disjoint` still has empty IE
   (`None`).  Nine gtri cells of FF2FF1212 are #573 / 522-d;
   the classifier pointer remint is #575.

   Green (all Qed):
     - a strict-`gtri` point has an explicit open disk of strict points
       (Lipschitz of each affine slack; radius = |gtri p| / gtri_lip;
       no topology library)
     - a nondegenerate boundary segment carries a dim-1 witness
     - the #530 / #571 sentinel pair
         A = (0,0)(1,0)(0,1), B = (2,0)(3,0)(2,1)
       has IE dim-2 content: the open disk of radius 1/8 about (1/4,1/4)
       lies in {0 < gtri A} ∩ {gtri B < 0}

   Not claimed:
     - `cell_ok (im_ie aa_matrix_disjoint)` (the fill is empty)
     - unguarded `point_in_ring ↔ 0 < gtri` (ADR-0003; do not wire ray
       parity)
     - II / BB / EI / EE cell fills, or a full DE-9IM bar-2 matrix
     - a T-junction or obtuse-at-v certificate (leftover letters stay
       unused)

   Classifier order is unchanged.  Frozen anchors untouched.
   Not an ADR-0004 remint.  `522-g` is the existing #568 ticket id.

   WITNESS topic: relate · claimId: 522-g · witness: 522-g-ring-inclusion
   macro: relate
   lane: proofs
   issue: #568 / #522
   ADR-0004: not a remint. 522-g is the existing #568 ticket id.

   No `Admitted`, no `Axiom`, no `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Agent
   ========================================================================== *)

(* WITNESS {"claimId":"522-g","topic":"relate","lemma":"sentinel_ie_has_dim2","title":"IE of the #530 sentinel pair has dim-2 content: an open disk in int(A) ∩ ext(B)","file":"theories/RelateNGRingInclusion.v","witness":"522-g-ring-inclusion","board":"#568"} *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import Distance Segment
  GeneralTriangleSeparation
  DE9IM RelateLineLine RelateAreaArea.

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* Coordinate Lipschitz of Euclidean distance (local copies; do not import    *)
(* RelateNGMatrixEqual).                                                      *)
(* -------------------------------------------------------------------------- *)

Lemma Rabs_mul_self : forall x, Rabs x * Rabs x = x * x.
Proof.
  intros x. rewrite <- Rabs_mult. apply Rabs_pos_eq. apply Rle_0_sqr.
Qed.

Lemma sq_monotone_nonneg :
  forall x y, 0 <= x -> 0 <= y -> (x <= y <-> x * x <= y * y).
Proof.
  intros x y Hx Hy. split; intros H.
  - apply Rmult_le_compat; lra.
  - destruct (Rle_or_lt x y) as [Hle|Hlt]; [exact Hle|].
    exfalso. assert (y * y < x * x) by (apply Rmult_le_0_lt_compat; lra). lra.
Qed.

Lemma abs_coord_le_dist_x : forall p q, Rabs (px p - px q) <= dist p q.
Proof.
  intros p q.
  pose proof (dist_sq_nonneg p q) as Hnn.
  unfold dist.
  apply (proj2 (sq_monotone_nonneg (Rabs (px p - px q))
                   (sqrt (dist_sq p q)) (Rabs_pos _) (sqrt_pos _))).
  rewrite sqrt_sqrt by exact Hnn.
  rewrite Rabs_mul_self.
  unfold dist_sq. pose proof (Rle_0_sqr (py p - py q)); unfold Rsqr in *. lra.
Qed.

Lemma abs_coord_le_dist_y : forall p q, Rabs (py p - py q) <= dist p q.
Proof.
  intros p q.
  pose proof (dist_sq_nonneg p q) as Hnn.
  unfold dist.
  apply (proj2 (sq_monotone_nonneg (Rabs (py p - py q))
                   (sqrt (dist_sq p q)) (Rabs_pos _) (sqrt_pos _))).
  rewrite sqrt_sqrt by exact Hnn.
  rewrite Rabs_mul_self.
  unfold dist_sq. pose proof (Rle_0_sqr (px p - px q)); unfold Rsqr in *. lra.
Qed.

Lemma Rabs_lt_between : forall x r, Rabs x < r -> - r < x < r.
Proof.
  intros x r H. unfold Rabs in H. destruct (Rcase_abs x); lra.
Qed.

Lemma Rabs_ge_minus : forall x, - Rabs x <= x.
Proof.
  intros x. unfold Rabs. destruct (Rcase_abs x); lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Affine slack Lipschitz.  |Δgs| ≤ (|Δx_edge| + |Δy_edge|) · dist.           *)
(* -------------------------------------------------------------------------- *)

Definition edge_lip (x0 y0 x1 y1 : R) : R :=
  Rabs (x1 - x0) + Rabs (y1 - y0).

Lemma edge_lip_nonneg : forall x0 y0 x1 y1, 0 <= edge_lip x0 y0 x1 y1.
Proof. intros. unfold edge_lip. pose proof (Rabs_pos (x1 - x0)). pose proof (Rabs_pos (y1 - y0)). lra. Qed.

Lemma affine_cross_lipschitz :
  forall ux uy (p q : Point),
    Rabs (ux * (py q - py p) - uy * (px q - px p))
    <= (Rabs ux + Rabs uy) * dist p q.
Proof.
  intros ux uy p q.
  pose proof (abs_coord_le_dist_x p q) as Hx.
  pose proof (abs_coord_le_dist_y p q) as Hy.
  rewrite (Rabs_minus_sym (px p) (px q)) in Hx.
  rewrite (Rabs_minus_sym (py p) (py q)) in Hy.
  apply Rle_trans with
    (Rabs (ux * (py q - py p)) + Rabs (uy * (px q - px p))).
  { replace (ux * (py q - py p) - uy * (px q - px p))
      with (ux * (py q - py p) + - (uy * (px q - px p))) by ring.
    pose proof (Rabs_triang (ux * (py q - py p)) (- (uy * (px q - px p)))) as Ht.
    rewrite Rabs_Ropp in Ht. exact Ht. }
  rewrite !Rabs_mult.
  apply Rle_trans with (Rabs ux * dist p q + Rabs uy * dist p q).
  { apply Rplus_le_compat.
    - apply Rmult_le_compat_l; [apply Rabs_pos|exact Hy].
    - apply Rmult_le_compat_l; [apply Rabs_pos|exact Hx]. }
  lra.
Qed.

Lemma gsA_lipschitz :
  forall ax ay bx by_ p q,
    Rabs (gsA ax ay bx by_ q - gsA ax ay bx by_ p)
    <= edge_lip ax ay bx by_ * dist p q.
Proof.
  intros ax ay bx by_ p q.
  unfold gsA, edge_lip.
  replace ((bx - ax) * (py q - ay) - (by_ - ay) * (px q - ax)
           - ((bx - ax) * (py p - ay) - (by_ - ay) * (px p - ax)))
    with ((bx - ax) * (py q - py p) - (by_ - ay) * (px q - px p)) by ring.
  apply affine_cross_lipschitz.
Qed.

Lemma gsB_lipschitz :
  forall bx by_ cx cy p q,
    Rabs (gsB bx by_ cx cy q - gsB bx by_ cx cy p)
    <= edge_lip bx by_ cx cy * dist p q.
Proof.
  intros bx by_ cx cy p q.
  unfold gsB, edge_lip.
  replace ((cx - bx) * (py q - by_) - (cy - by_) * (px q - bx)
           - ((cx - bx) * (py p - by_) - (cy - by_) * (px p - bx)))
    with ((cx - bx) * (py q - py p) - (cy - by_) * (px q - px p)) by ring.
  apply affine_cross_lipschitz.
Qed.

Lemma gsC_lipschitz :
  forall ax ay cx cy p q,
    Rabs (gsC ax ay cx cy q - gsC ax ay cx cy p)
    <= edge_lip cx cy ax ay * dist p q.
Proof.
  intros ax ay cx cy p q.
  unfold gsC, edge_lip.
  replace ((ax - cx) * (py q - cy) - (ay - cy) * (px q - cx)
           - ((ax - cx) * (py p - cy) - (ay - cy) * (px p - cx)))
    with ((ax - cx) * (py q - py p) - (ay - cy) * (px q - px p)) by ring.
  apply affine_cross_lipschitz.
Qed.

Lemma gsA_lower :
  forall ax ay bx by_ p q,
    gsA ax ay bx by_ p - edge_lip ax ay bx by_ * dist p q
    <= gsA ax ay bx by_ q.
Proof.
  intros ax ay bx by_ p q.
  pose proof (gsA_lipschitz ax ay bx by_ p q) as Hlip.
  pose proof (Rabs_ge_minus (gsA ax ay bx by_ q - gsA ax ay bx by_ p)) as Hm.
  lra.
Qed.

Lemma gsB_lower :
  forall bx by_ cx cy p q,
    gsB bx by_ cx cy p - edge_lip bx by_ cx cy * dist p q
    <= gsB bx by_ cx cy q.
Proof.
  intros bx by_ cx cy p q.
  pose proof (gsB_lipschitz bx by_ cx cy p q) as Hlip.
  pose proof (Rabs_ge_minus (gsB bx by_ cx cy q - gsB bx by_ cx cy p)) as Hm.
  lra.
Qed.

Lemma gsC_lower :
  forall ax ay cx cy p q,
    gsC ax ay cx cy p - edge_lip cx cy ax ay * dist p q
    <= gsC ax ay cx cy q.
Proof.
  intros ax ay cx cy p q.
  pose proof (gsC_lipschitz ax ay cx cy p q) as Hlip.
  pose proof (Rabs_ge_minus (gsC ax ay cx cy q - gsC ax ay cx cy p)) as Hm.
  lra.
Qed.

Lemma gsA_upper :
  forall ax ay bx by_ p q,
    gsA ax ay bx by_ q
    <= gsA ax ay bx by_ p + edge_lip ax ay bx by_ * dist p q.
Proof.
  intros ax ay bx by_ p q.
  pose proof (gsA_lipschitz ax ay bx by_ p q) as Hlip.
  pose proof (Rle_abs (gsA ax ay bx by_ q - gsA ax ay bx by_ p)) as Hp.
  lra.
Qed.

Lemma gsB_upper :
  forall bx by_ cx cy p q,
    gsB bx by_ cx cy q
    <= gsB bx by_ cx cy p + edge_lip bx by_ cx cy * dist p q.
Proof.
  intros bx by_ cx cy p q.
  pose proof (gsB_lipschitz bx by_ cx cy p q) as Hlip.
  pose proof (Rle_abs (gsB bx by_ cx cy q - gsB bx by_ cx cy p)) as Hp.
  lra.
Qed.

Lemma gsC_upper :
  forall ax ay cx cy p q,
    gsC ax ay cx cy q
    <= gsC ax ay cx cy p + edge_lip cx cy ax ay * dist p q.
Proof.
  intros ax ay cx cy p q.
  pose proof (gsC_lipschitz ax ay cx cy p q) as Hlip.
  pose proof (Rle_abs (gsC ax ay cx cy q - gsC ax ay cx cy p)) as Hp.
  lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Explicit radius: |gtri p| / (1 + Σ edge lips).  The +1 keeps the           *)
(* denominator positive even for a degenerate triple.                         *)
(* -------------------------------------------------------------------------- *)

Definition gtri_lip (ax ay bx by_ cx cy : R) : R :=
  1 + edge_lip ax ay bx by_ + edge_lip bx by_ cx cy + edge_lip cx cy ax ay.

Lemma gtri_lip_pos : forall ax ay bx by_ cx cy, 0 < gtri_lip ax ay bx by_ cx cy.
Proof.
  intros. unfold gtri_lip.
  pose proof (edge_lip_nonneg ax ay bx by_).
  pose proof (edge_lip_nonneg bx by_ cx cy).
  pose proof (edge_lip_nonneg cx cy ax ay).
  lra.
Qed.

Lemma edge_lip_A_lt_gtri_lip :
  forall ax ay bx by_ cx cy,
    edge_lip ax ay bx by_ < gtri_lip ax ay bx by_ cx cy.
Proof.
  intros. unfold gtri_lip.
  pose proof (edge_lip_nonneg bx by_ cx cy).
  pose proof (edge_lip_nonneg cx cy ax ay).
  lra.
Qed.

Lemma edge_lip_B_lt_gtri_lip :
  forall ax ay bx by_ cx cy,
    edge_lip bx by_ cx cy < gtri_lip ax ay bx by_ cx cy.
Proof.
  intros. unfold gtri_lip.
  pose proof (edge_lip_nonneg ax ay bx by_).
  pose proof (edge_lip_nonneg cx cy ax ay).
  lra.
Qed.

Lemma edge_lip_C_lt_gtri_lip :
  forall ax ay bx by_ cx cy,
    edge_lip cx cy ax ay < gtri_lip ax ay bx by_ cx cy.
Proof.
  intros. unfold gtri_lip.
  pose proof (edge_lip_nonneg ax ay bx by_).
  pose proof (edge_lip_nonneg bx by_ cx cy).
  lra.
Qed.

Definition gtri_strict_radius (ax ay bx by_ cx cy : R) (p : Point) : R :=
  Rabs (gtri ax ay bx by_ cx cy p) / gtri_lip ax ay bx by_ cx cy.

Lemma gtri_le_gsA :
  forall ax ay bx by_ cx cy p,
    gtri ax ay bx by_ cx cy p <= gsA ax ay bx by_ p.
Proof.
  intros. unfold gtri.
  apply Rle_trans with (Rmin (gsA ax ay bx by_ p) (gsB bx by_ cx cy p)).
  - apply Rmin_l.
  - apply Rmin_l.
Qed.

Lemma gtri_le_gsB :
  forall ax ay bx by_ cx cy p,
    gtri ax ay bx by_ cx cy p <= gsB bx by_ cx cy p.
Proof.
  intros. unfold gtri.
  apply Rle_trans with (Rmin (gsA ax ay bx by_ p) (gsB bx by_ cx cy p)).
  - apply Rmin_l.
  - apply Rmin_r.
Qed.

Lemma gtri_le_gsC :
  forall ax ay bx by_ cx cy p,
    gtri ax ay bx by_ cx cy p <= gsC ax ay cx cy p.
Proof. intros. unfold gtri. apply Rmin_r. Qed.

Lemma gtri_hits_component :
  forall ax ay bx by_ cx cy p,
    gtri ax ay bx by_ cx cy p = gsA ax ay bx by_ p
    \/ gtri ax ay bx by_ cx cy p = gsB bx by_ cx cy p
    \/ gtri ax ay bx by_ cx cy p = gsC ax ay cx cy p.
Proof.
  intros ax ay bx by_ cx cy p.
  unfold gtri.
  destruct (Rle_dec (Rmin (gsA ax ay bx by_ p) (gsB bx by_ cx cy p))
                    (gsC ax ay cx cy p)) as [Hle|Hn].
  - rewrite (Rmin_left _ _ Hle).
    destruct (Rle_dec (gsA ax ay bx by_ p) (gsB bx by_ cx cy p)) as [Hab|Hab].
    + left. rewrite (Rmin_left _ _ Hab). reflexivity.
    + right. left. rewrite Rmin_right; [reflexivity|lra].
  - right. right. rewrite Rmin_right; [reflexivity|lra].
Qed.

Lemma lip_dist_lt_slack :
  forall lip L slack d,
    0 < slack ->
    0 < L ->
    0 <= lip ->
    lip < L ->
    d < slack / L ->
    lip * d < slack.
Proof.
  intros lip L slack d Hs HL Hlip Hlt Hd.
  destruct (Req_dec lip 0) as [Hz|Hnz].
  - rewrite Hz. nra.
  - apply Rlt_le_trans with (lip * (slack / L)).
    + apply Rmult_lt_compat_l; lra.
    + apply Rmult_le_reg_r with L; [lra|].
      replace (lip * (slack / L) * L) with (lip * slack) by (field; lra).
      nra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Headline: a strict-positive gtri point has a neighbourhood of the same.    *)
(* -------------------------------------------------------------------------- *)

Theorem gtri_strict_pos_open_disk :
  forall ax ay bx by_ cx cy p q,
    0 < gtri ax ay bx by_ cx cy p ->
    dist p q < gtri_strict_radius ax ay bx by_ cx cy p ->
    0 < gtri ax ay bx by_ cx cy q.
Proof.
  intros ax ay bx by_ cx cy p q Hp Hq.
  unfold gtri_strict_radius in Hq.
  rewrite (Rabs_right (gtri ax ay bx by_ cx cy p)) in Hq by lra.
  pose proof (gtri_lip_pos ax ay bx by_ cx cy) as HL.
  apply (proj2 (gtri_pos_iff ax ay bx by_ cx cy q)).
  assert (HradA : edge_lip ax ay bx by_ * dist p q
                    < gtri ax ay bx by_ cx cy p).
  { apply (lip_dist_lt_slack (edge_lip ax ay bx by_)
             (gtri_lip ax ay bx by_ cx cy)
             (gtri ax ay bx by_ cx cy p) (dist p q));
      try lra; try apply edge_lip_nonneg; apply edge_lip_A_lt_gtri_lip. }
  assert (HradB : edge_lip bx by_ cx cy * dist p q
                    < gtri ax ay bx by_ cx cy p).
  { apply (lip_dist_lt_slack (edge_lip bx by_ cx cy)
             (gtri_lip ax ay bx by_ cx cy)
             (gtri ax ay bx by_ cx cy p) (dist p q));
      try lra; try apply edge_lip_nonneg; apply edge_lip_B_lt_gtri_lip. }
  assert (HradC : edge_lip cx cy ax ay * dist p q
                    < gtri ax ay bx by_ cx cy p).
  { apply (lip_dist_lt_slack (edge_lip cx cy ax ay)
             (gtri_lip ax ay bx by_ cx cy)
             (gtri ax ay bx by_ cx cy p) (dist p q));
      try lra; try apply edge_lip_nonneg; apply edge_lip_C_lt_gtri_lip. }
  split; [|split].
  - pose proof (gsA_lower ax ay bx by_ p q).
    pose proof (gtri_le_gsA ax ay bx by_ cx cy p). lra.
  - pose proof (gsB_lower bx by_ cx cy p q).
    pose proof (gtri_le_gsB ax ay bx by_ cx cy p). lra.
  - pose proof (gsC_lower ax ay cx cy p q).
    pose proof (gtri_le_gsC ax ay bx by_ cx cy p). lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* A strict-negative gtri point has a neighbourhood that stays negative.      *)
(* -------------------------------------------------------------------------- *)

Theorem gtri_strict_neg_open_disk :
  forall ax ay bx by_ cx cy p q,
    gtri ax ay bx by_ cx cy p < 0 ->
    dist p q < gtri_strict_radius ax ay bx by_ cx cy p ->
    gtri ax ay bx by_ cx cy q < 0.
Proof.
  intros ax ay bx by_ cx cy p q Hp Hq.
  unfold gtri_strict_radius in Hq.
  rewrite (Rabs_left (gtri ax ay bx by_ cx cy p)) in Hq by lra.
  pose proof (gtri_lip_pos ax ay bx by_ cx cy) as HL.
  destruct (gtri_hits_component ax ay bx by_ cx cy p) as [HA | [HB | HC]].
  - assert (Hrad : edge_lip ax ay bx by_ * dist p q
                     < - gtri ax ay bx by_ cx cy p).
    { apply (lip_dist_lt_slack (edge_lip ax ay bx by_)
               (gtri_lip ax ay bx by_ cx cy)
               (- gtri ax ay bx by_ cx cy p) (dist p q));
        try lra; try apply edge_lip_nonneg; apply edge_lip_A_lt_gtri_lip. }
    pose proof (gsA_upper ax ay bx by_ p q).
    apply Rle_lt_trans with (gsA ax ay bx by_ q).
    + apply gtri_le_gsA.
    + lra.
  - assert (Hrad : edge_lip bx by_ cx cy * dist p q
                     < - gtri ax ay bx by_ cx cy p).
    { apply (lip_dist_lt_slack (edge_lip bx by_ cx cy)
               (gtri_lip ax ay bx by_ cx cy)
               (- gtri ax ay bx by_ cx cy p) (dist p q));
        try lra; try apply edge_lip_nonneg; apply edge_lip_B_lt_gtri_lip. }
    pose proof (gsB_upper bx by_ cx cy p q).
    apply Rle_lt_trans with (gsB bx by_ cx cy q).
    + apply gtri_le_gsB.
    + lra.
  - assert (Hrad : edge_lip cx cy ax ay * dist p q
                     < - gtri ax ay bx by_ cx cy p).
    { apply (lip_dist_lt_slack (edge_lip cx cy ax ay)
               (gtri_lip ax ay bx by_ cx cy)
               (- gtri ax ay bx by_ cx cy p) (dist p q));
        try lra; try apply edge_lip_nonneg; apply edge_lip_C_lt_gtri_lip. }
    pose proof (gsC_upper ax ay cx cy p q).
    apply Rle_lt_trans with (gsC ax ay cx cy q).
    + apply gtri_le_gsC.
    + lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Dimension-1 stratum witness on a nondegenerate segment.                    *)
(* -------------------------------------------------------------------------- *)

Definition dim1_on_segment (P0 P1 : Point) : Prop :=
  exists q r : Point, between P0 P1 q /\ between P0 P1 r /\ q <> r.

Lemma dim1_on_nondeg_segment :
  forall P0 P1, P0 <> P1 -> dim1_on_segment P0 P1.
Proof.
  intros P0 P1 Hne.
  exists (mkPoint ((2 * px P0 + px P1) / 3) ((2 * py P0 + py P1) / 3)).
  exists (mkPoint ((px P0 + 2 * px P1) / 3) ((py P0 + 2 * py P1) / 3)).
  split.
  { exists (1 / 3). repeat split; try lra; simpl; field. }
  split.
  { exists (2 / 3). repeat split; try lra; simpl; field. }
  intros Heq. apply Hne.
  injection Heq as Hx Hy.
  destruct P0 as [x0 y0]; destruct P1 as [x1 y1]; simpl in Hx, Hy.
  f_equal; lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Sentinel pair (#530 / #571): A left of B, both CCW unit-ish triangles.     *)
(* IE disk: centre (1/4,1/4), radius 1/8 — tighter than the Lipschitz         *)
(* radius, proved by coordinate bounds.                                       *)
(* -------------------------------------------------------------------------- *)

Definition sentinel_ie_center : Point := mkPoint (1 / 4) (1 / 4).
Definition sentinel_ie_radius : R := 1 / 8.

Definition ie_open_disk
    (ax ay bx by_ cx cy dx dy ex ey fx fy : R)
    (c : Point) (r : R) : Prop :=
  0 < r /\
  (forall q, dist c q < r ->
     0 < gtri ax ay bx by_ cx cy q /\
     gtri dx dy ex ey fx fy q < 0).

Lemma sentinel_A_gs :
  forall q,
    gsA 0 0 1 0 q = py q /\
    gsB 1 0 0 1 q = 1 - px q - py q /\
    gsC 0 0 0 1 q = px q.
Proof. intros q; unfold gsA, gsB, gsC; split; [|split]; lra. Qed.

Lemma sentinel_B_gs :
  forall q,
    gsA 2 0 3 0 q = py q /\
    gsB 3 0 2 1 q = 3 - px q - py q /\
    gsC 2 0 2 1 q = px q - 2.
Proof. intros q; unfold gsA, gsB, gsC; split; [|split]; lra. Qed.

Lemma sentinel_disk_coord_box :
  forall q,
    dist sentinel_ie_center q < sentinel_ie_radius ->
    1 / 8 < px q < 3 / 8 /\ 1 / 8 < py q < 3 / 8.
Proof.
  intros q Hq.
  unfold sentinel_ie_center, sentinel_ie_radius in Hq.
  pose proof (abs_coord_le_dist_x (mkPoint (1 / 4) (1 / 4)) q) as Hx.
  pose proof (abs_coord_le_dist_y (mkPoint (1 / 4) (1 / 4)) q) as Hy.
  simpl in Hx, Hy.
  assert (Hx' : Rabs (1 / 4 - px q) < 1 / 8) by lra.
  assert (Hy' : Rabs (1 / 4 - py q) < 1 / 8) by lra.
  apply Rabs_lt_between in Hx'.
  apply Rabs_lt_between in Hy'.
  lra.
Qed.

Lemma sentinel_A_strict_in_disk :
  forall q,
    dist sentinel_ie_center q < sentinel_ie_radius ->
    0 < gtri 0 0 1 0 0 1 q.
Proof.
  intros q Hq.
  apply sentinel_disk_coord_box in Hq.
  destruct (sentinel_A_gs q) as [HA [HB HC]].
  apply (proj2 (gtri_pos_iff 0 0 1 0 0 1 q)).
  rewrite HA, HB, HC. lra.
Qed.

Lemma sentinel_B_strict_out_disk :
  forall q,
    dist sentinel_ie_center q < sentinel_ie_radius ->
    gtri 2 0 3 0 2 1 q < 0.
Proof.
  intros q Hq.
  apply sentinel_disk_coord_box in Hq.
  destruct (sentinel_B_gs q) as [HA [HB HC]].
  apply Rle_lt_trans with (gsC 2 0 2 1 q).
  - apply (gtri_le_gsC 2 0 3 0 2 1 q).
  - rewrite HC. lra.
Qed.

(* WITNESS topic: relate · claimId: 522-g · witness: 522-g-ring-inclusion *)
(* WITNESS {"claimId":"522-g","topic":"relate","lemma":"sentinel_ie_has_dim2","title":"IE of the #530 sentinel pair has dim-2 content: an open disk in int(A) ∩ ext(B)","file":"theories/RelateNGRingInclusion.v","witness":"522-g-ring-inclusion","board":"#568"} *)
Theorem sentinel_ie_has_dim2 :
  ie_open_disk 0 0 1 0 0 1 2 0 3 0 2 1
    sentinel_ie_center sentinel_ie_radius.
Proof.
  unfold ie_open_disk, sentinel_ie_radius.
  split; [lra|].
  intros q Hq. split.
  - apply sentinel_A_strict_in_disk; exact Hq.
  - apply sentinel_B_strict_out_disk; exact Hq.
Qed.

Theorem sentinel_A_base_dim1 :
  dim1_on_segment (mkPoint 0 0) (mkPoint 1 0).
Proof.
  apply dim1_on_nondeg_segment.
  intros H. inversion H. lra.
Qed.

(* The current disjoint fill still has empty IE.  Geometric dim-2 above is
   the bar-2 gap, not a remint of `aa_matrix_disjoint`.  That fill is #573. *)
Lemma disjoint_fill_ie_empty :
  im_ie aa_matrix_disjoint = None.
Proof.
  unfold aa_matrix_disjoint, ll_matrix_disjoint. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions gtri_strict_pos_open_disk.
Print Assumptions gtri_strict_neg_open_disk.
Print Assumptions dim1_on_nondeg_segment.
Print Assumptions sentinel_ie_has_dim2.
Print Assumptions sentinel_A_base_dim1.
Print Assumptions disjoint_fill_ie_empty.

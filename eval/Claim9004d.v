(* ============================================================================
   nts-eval micro unit — claimId 9004-d
   ----------------------------------------------------------------------------
   Cell pruning bound: an empty radius achievable anywhere in a square cell
   is at most the centre's distance to every obstacle plus the cell
   circumradius sqrt(2)·h.

   Self-contained classical-reals micro-kernel for the nts-eval harness:
   no NTS.Proofs Requires (the triangle inequality is proved locally via
   the Lagrange identity).  Mirrors the production packaging in
   theories/CellRadiusBound.v (board #9004 subtask 9004-d, epic #813;
   Zhai et al. 2026 "Polycenter", doi:10.1080/13658816.2025.2514056 —
   the JTS Cell.getMaxDistance soundness shared by
   MaximumInscribedCircle and LargestEmptyCircle).

   Rational pins: the cell corner realises the circumradius bound with
   equality (dist_sq((0,0),(1,1)) = 2·1²); the bound instance 3 ≤ 2 + √2
   holds on the probe configuration.  Mismatch probe: the SLACK-FREE
   misreading — "an empty radius in the cell is bounded by the centre
   clearance alone" — is refuted by obstacle X = (2,0), cell centre
   (0,0), half-side 1, probe point p = (−1,0): the empty radius 3 at p
   exceeds dist(c, X) = 2.

   WITNESS claimId: 9004-d
   Lemma: cell_achievable_radius_bound
   ========================================================================== *)

(* WITNESS {"claimId":"9004-d","topic":"construct","lemma":"cell_achievable_radius_bound","title":"Cell pruning bound: empty radius in a cell <= centre-to-obstacle distance + sqrt(2)*h"} *)

From Stdlib Require Import Reals Lra.
Local Open Scope R_scope.

(* ---- Minimal geometry carrier (Distance twins) ---------------------------- *)

Record Point : Type := mkPoint { px : R; py : R }.

Definition dist_sq (P Q : Point) : R :=
  (px P - px Q) * (px P - px Q) + (py P - py Q) * (py P - py Q).

Definition dist (P Q : Point) : R := sqrt (dist_sq P Q).

Lemma sqr_nonneg : forall x : R, 0 <= x * x.
Proof. intros x. nra. Qed.

Lemma dist_sq_nonneg : forall P Q, 0 <= dist_sq P Q.
Proof.
  intros P Q. unfold dist_sq.
  pose proof (sqr_nonneg (px P - px Q)).
  pose proof (sqr_nonneg (py P - py Q)).
  lra.
Qed.

Lemma dist_nonneg : forall P Q, 0 <= dist P Q.
Proof. intros P Q. apply sqrt_pos. Qed.

Lemma dist_mul_self : forall P Q, dist P Q * dist P Q = dist_sq P Q.
Proof. intros P Q. unfold dist. apply sqrt_sqrt. apply dist_sq_nonneg. Qed.

Lemma dist_sym : forall P Q, dist P Q = dist Q P.
Proof.
  intros P Q. unfold dist.
  replace (dist_sq P Q) with (dist_sq Q P) by (unfold dist_sq; ring).
  reflexivity.
Qed.

Lemma dist_le_iff_dist_sq_le : forall P Q t,
  0 <= t -> (dist P Q <= t <-> dist_sq P Q <= t * t).
Proof.
  intros P Q t Ht. unfold dist. split.
  - intros H.
    rewrite <- (sqrt_sqrt (dist_sq P Q) (dist_sq_nonneg P Q)).
    apply Rmult_le_compat; try apply sqrt_pos; assumption.
  - intros H.
    apply Rle_trans with (sqrt (t * t)).
    + apply sqrt_le_1; [apply dist_sq_nonneg | nra | exact H].
    + replace (t * t) with (Rsqr t) by (unfold Rsqr; ring).
      rewrite sqrt_Rsqr; [lra | exact Ht].
Qed.

(* Triangle inequality, self-contained: Cauchy–Schwarz via the Lagrange
   identity (ux·vy − uy·vx)² ≥ 0, then compare squares.                       *)
Lemma dist_triangle : forall P Q S : Point,
  dist P S <= dist P Q + dist Q S.
Proof.
  intros P Q S.
  assert (Hdot : (px Q - px P) * (px S - px Q) + (py Q - py P) * (py S - py Q)
                 <= dist P Q * dist Q S).
  { apply Rle_trans with
      (Rabs ((px Q - px P) * (px S - px Q) + (py Q - py P) * (py S - py Q)));
      [apply Rle_abs |].
    rewrite <- sqrt_Rsqr_abs. unfold Rsqr, dist.
    rewrite <- (sqrt_mult (dist_sq P Q) (dist_sq Q S)
                  (dist_sq_nonneg P Q) (dist_sq_nonneg Q S)).
    apply sqrt_le_1.
    - apply sqr_nonneg.
    - apply Rmult_le_pos; apply dist_sq_nonneg.
    - unfold dist_sq.
      pose proof (sqr_nonneg ((px Q - px P) * (py S - py Q)
                              - (py Q - py P) * (px S - px Q))).
      nra. }
  assert (Hsq : dist P S * dist P S
                <= (dist P Q + dist Q S) * (dist P Q + dist Q S)).
  { replace ((dist P Q + dist Q S) * (dist P Q + dist Q S))
      with (dist P Q * dist P Q + 2 * (dist P Q * dist Q S)
            + dist Q S * dist Q S) by ring.
    rewrite !dist_mul_self.
    unfold dist_sq in *. nra. }
  pose proof (dist_nonneg P S).
  pose proof (dist_nonneg P Q).
  pose proof (dist_nonneg Q S).
  nra.
Qed.

(* ---- Production twins: obstacles, empty disks, square cells --------------- *)

Definition Region : Type := Point -> Prop.

(** The disk (O, r) is empty of the obstacle set (LargestEmptyCircle twin). *)
Definition empty_disk (obs : Region) (O : Point) (r : R) : Prop :=
  0 <= r /\ forall P : Point, obs P -> r <= dist O P.

(** The closed axis-aligned square cell: centre c, half-side h. *)
Definition in_cell (c : Point) (h : R) (p : Point) : Prop :=
  px c - h <= px p <= px c + h /\ py c - h <= py p <= py c + h.

(* ---- Cell circumradius ----------------------------------------------------- *)

Lemma cell_dist_sq_bound : forall (c : Point) (h : R) (p : Point),
  0 <= h -> in_cell c h p -> dist_sq c p <= 2 * (h * h).
Proof.
  intros c h p Hh [[Hx0 Hx1] [Hy0 Hy1]].
  unfold dist_sq. nra.
Qed.

Lemma sqrt2_h_sq : forall h : R,
  (sqrt 2 * h) * (sqrt 2 * h) = 2 * (h * h).
Proof.
  intros h.
  assert (H2 : sqrt 2 * sqrt 2 = 2) by (apply sqrt_sqrt; lra).
  replace ((sqrt 2 * h) * (sqrt 2 * h))
    with ((sqrt 2 * sqrt 2) * (h * h)) by ring.
  rewrite H2. ring.
Qed.

Lemma cell_circumradius : forall (c : Point) (h : R) (p : Point),
  0 <= h -> in_cell c h p -> dist c p <= sqrt 2 * h.
Proof.
  intros c h p Hh Hcell.
  assert (Ht : 0 <= sqrt 2 * h).
  { apply Rmult_le_pos; [apply sqrt_pos | exact Hh]. }
  apply (proj2 (dist_le_iff_dist_sq_le c p (sqrt 2 * h) Ht)).
  rewrite sqrt2_h_sq.
  apply cell_dist_sq_bound; assumption.
Qed.

(* ---- Headline (9004-d) ----------------------------------------------------- *)

Theorem cell_achievable_radius_bound :
  forall (obs : Region) (c p : Point) (h r' : R) (X : Point),
    0 <= h ->
    in_cell c h p ->
    empty_disk obs p r' ->
    obs X ->
    r' <= dist c X + sqrt 2 * h.
Proof.
  intros obs c p h r' X Hh Hcell [Hr' He] HX.
  pose proof (He X HX) as HpX.
  pose proof (dist_triangle p c X) as Htri.
  rewrite (dist_sym p c) in Htri.
  pose proof (cell_circumradius c h p Hh Hcell) as Hcr.
  lra.
Qed.

(* ---- Rational pins ---------------------------------------------------------- *)

(** The cell corner realises the circumradius bound with equality:
    dist_sq((0,0),(1,1)) = 2·1². *)
Lemma cell_corner_dist_sq_pin :
  dist_sq (mkPoint 0 0) (mkPoint 1 1) = 2 * (1 * 1).
Proof. unfold dist_sq. simpl. lra. Qed.

(* The probe configuration: obstacle X = (2,0); cell centre c = (0,0),
   half-side 1; probe point p = (−1,0), a cell corner-edge point.            *)

Lemma probe_dist_p_X : dist (mkPoint (-1) 0) (mkPoint 2 0) = 3.
Proof.
  unfold dist.
  replace (dist_sq (mkPoint (-1) 0) (mkPoint 2 0)) with 9
    by (unfold dist_sq; simpl; lra).
  replace 9 with (Rsqr 3) by (unfold Rsqr; lra).
  apply sqrt_Rsqr. lra.
Qed.

Lemma probe_dist_c_X : dist (mkPoint 0 0) (mkPoint 2 0) = 2.
Proof.
  unfold dist.
  replace (dist_sq (mkPoint 0 0) (mkPoint 2 0)) with 4
    by (unfold dist_sq; simpl; lra).
  replace 4 with (Rsqr 2) by (unfold Rsqr; lra).
  apply sqrt_Rsqr. lra.
Qed.

Definition probe_obs : Region := fun P : Point => P = mkPoint 2 0.

Lemma probe_empty_disk_at_p :
  empty_disk probe_obs (mkPoint (-1) 0) 3.
Proof.
  split; [lra |].
  intros P ->. rewrite probe_dist_p_X. lra.
Qed.

Lemma probe_p_in_cell : in_cell (mkPoint 0 0) 1 (mkPoint (-1) 0).
Proof. unfold in_cell. simpl. lra. Qed.

(** Positive pin: the bound holds on the probe with the √2·h slack —
    3 ≤ 2 + √2·1 (via 1 = √1 ≤ √2). *)
Lemma probe_bound_holds_with_slack : 3 <= 2 + sqrt 2 * 1.
Proof.
  assert (H1 : sqrt 1 <= sqrt 2) by (apply sqrt_le_1; lra).
  rewrite sqrt_1 in H1. lra.
Qed.

(* ---- Mismatch probe: the slack-free misreading is FALSE -------------------- *)

(** Dropping the √2·h slack — bounding a cell point's empty radius by the
    centre clearance alone — is refuted: the empty radius 3 at p = (−1,0)
    exceeds dist(c, X) = 2. *)
Lemma slack_free_bound_fails :
  ~ (forall (obs : Region) (c p : Point) (h r' : R) (X : Point),
       0 <= h -> in_cell c h p -> empty_disk obs p r' -> obs X ->
       r' <= dist c X).
Proof.
  intros H.
  pose proof (H probe_obs (mkPoint 0 0) (mkPoint (-1) 0) 1 3 (mkPoint 2 0)
                ltac:(lra) probe_p_in_cell probe_empty_disk_at_p eq_refl)
    as Hbad.
  rewrite probe_dist_c_X in Hbad. lra.
Qed.

Print Assumptions cell_achievable_radius_bound.
Print Assumptions slack_free_bound_fails.

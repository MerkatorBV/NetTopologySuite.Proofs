(* ============================================================================
   NetTopologySuite.Proofs.LECSegmentRow
   ----------------------------------------------------------------------------
   The SEGMENT row of the typed LEC obstacle-distance table (the ledger's
   open rung "Segment/facet row" — closed): the clamped-projection
   point-to-segment distance, priced EXACT.

   The engine's LineString facet metric (JTS `LineSegment.distance`, the
   `ObstacleDistance` row behind every straight edge) computes
       t  = (P - A)·(B - A) / |B - A|^2      (the supporting-line foot)
       t* = clamp(t, 0, 1)                   (pull the foot into the segment)
       d  = |P - (A + t*(B - A))|
   This module proves that closed form is the exact set distance to
       on_seg A B := { A + t(B - A) | 0 <= t <= 1 }:
   lower bound on EVERY segment point (the clamped quadratic
   f(t) = |P - A - t(B-A)|^2 is minimised over [0,1] at t*, by branch:
   interior branch L·(f(t) - f(t0)) = (L·t - s)^2, endpoint branches by
   sign) AND attained (the clamp point is itself on the segment — so
   attainment is definitional).  `seg_dist` is TOTAL: a degenerate segment
   (A = B, |B - A|^2 = 0) takes t* = 0 and collapses to the POINT row
   dist P A (`seg_dist_degenerate`) — no validity hypothesis needed, the
   engine's l2 = 0 guard is the same collapse.

   Failed path F6 (ledger): "the segment distance is the distance to the
   supporting LINE's foot" — the unclamped projection an implementer gets
   by dropping the clamp.  REFUTED (`seg_line_foot_hypothesis_refuted`):
   for A=(0,0), B=(4,0), P=(7,4) the foot lands at (7,0) giving 4, but the
   true nearest segment point is the ENDPOINT B=(4,0) at distance 5 (a
   3-4-5 witness).  The clamp is not an optimisation — it is the row.

   Downstream: LECFlattenRow.v slots `on_seg`/`seg_dist` in as the fifth
   typed row (TSeg), so the min-fold flatten prices segments into
   collections with no new work.  Oracle: OBSTACLE_DISTANCE's SEG member
   row twins the closed form (one division + one sqrt), §H pins.

   Pure math on R.  Classical-reals trio only (see Print Assumptions).

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import Distance MaximumInscribedCircle
  LargestEmptyCircle LECObstacleDistance.

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  The segment, its parameterisation, and the clamped closed form.         *)
(* -------------------------------------------------------------------------- *)

Definition seg_point (A B : Point) (t : R) : Point :=
  mkPoint (px A + t * (px B - px A)) (py A + t * (py B - py A)).

(** Segment membership: the engine's facet as a point set. *)
Definition on_seg (A B : Point) (Q : Point) : Prop :=
  exists t, 0 <= t <= 1 /\ Q = seg_point A B t.

(** The projection numerator (P - A)·(B - A). *)
Definition seg_dot (A B P : Point) : R :=
  (px P - px A) * (px B - px A) + (py P - py A) * (py B - py A).

(** The clamped parameter — TOTAL: a degenerate segment takes t* = 0. *)
Definition seg_t (A B P : Point) : R :=
  match Req_EM_T (dist_sq A B) 0 with
  | left _  => 0
  | right _ => Rmax 0 (Rmin 1 (seg_dot A B P / dist_sq A B))
  end.

(** The row value: distance to the clamp point. *)
Definition seg_dist (A B P : Point) : R :=
  dist P (seg_point A B (seg_t A B P)).

Lemma seg_t_range : forall A B P, 0 <= seg_t A B P <= 1.
Proof.
  intros A B P. unfold seg_t.
  destruct (Req_EM_T (dist_sq A B) 0); [lra |]. split.
  - apply Rmax_l.
  - apply Rmax_lub; [lra | apply Rmin_l].
Qed.

(** The quadratic expansion under the fold: |P - (A + t(B-A))|^2 in t. *)
Lemma seg_point_dist_sq :
  forall (A B P : Point) (t : R),
    dist_sq P (seg_point A B t)
    = dist_sq P A - 2 * t * seg_dot A B P + t * t * dist_sq A B.
Proof.
  intros A B P t. unfold dist_sq, seg_point, seg_dot. cbn [px py]. ring.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  The clamp point minimises the quadratic over [0,1].                     *)
(* -------------------------------------------------------------------------- *)

Lemma seg_dist_sq_lower :
  forall (A B P : Point) (t : R),
    0 <= t <= 1 ->
    dist_sq P (seg_point A B (seg_t A B P)) <= dist_sq P (seg_point A B t).
Proof.
  intros A B P t Ht.
  rewrite !seg_point_dist_sq.
  unfold seg_t. destruct (Req_EM_T (dist_sq A B) 0) as [H0 | Hne].
  - (* degenerate: the direction vector is zero, so the dot is zero and the
       quadratic is constant *)
    destruct (proj1 (dist_sq_zero_iff_eq A B) H0) as [Hpx Hpy].
    assert (Hd : seg_dot A B P = 0)
      by (unfold seg_dot; rewrite Hpx, Hpy; ring).
    rewrite H0, Hd. lra.
  - assert (Hpos : 0 < dist_sq A B)
      by (pose proof (dist_sq_nonneg A B); lra).
    set (L := dist_sq A B) in *.
    set (s := seg_dot A B P) in *.
    set (q := s / L) in *.
    assert (HsL : s = q * L) by (unfold q; field; lra).
    clearbody q.
    rewrite HsL.
    destruct (Rle_dec q 0) as [Hle0 | Hgt0].
    + (* foot before A: clamp to 0; f(t) - f(0) = t(tL - 2qL) >= 0 *)
      rewrite Rmin_right by lra. rewrite Rmax_left by lra.
      assert (HqL : q * L <= 0) by nra.
      assert (HtqL : t * (q * L) <= 0) by nra.
      assert (Hsq : 0 <= t * t) by nra.
      assert (HtL : 0 <= t * t * L) by nra.
      nra.
    + destruct (Rle_dec 1 q) as [Hge1 | Hlt1].
      * (* foot past B: clamp to 1; f(t) - f(1) = L(1-t)(2q-1-t) >= 0 *)
        rewrite Rmin_left by lra. rewrite Rmax_right by lra.
        assert (Hprod : 0 <= (1 - t) * (2 * q - 1 - t)) by nra.
        assert (HL : 0 <= L * ((1 - t) * (2 * q - 1 - t))) by nra.
        nra.
      * (* interior foot: t* = q; f(t) - f(q) = L(t-q)^2 >= 0 *)
        rewrite Rmin_right by lra. rewrite Rmax_right by lra.
        pose proof (Rle_0_sqr (t - q)) as Hsq. unfold Rsqr in Hsq.
        assert (HL : 0 <= L * ((t - q) * (t - q)))
          by (apply Rmult_le_pos; lra).
        replace (dist_sq P A - 2 * t * (q * L) + t * t * L)
          with ((dist_sq P A - 2 * q * (q * L) + q * q * L)
                + L * ((t - q) * (t - q))) by ring.
        lra.
Qed.

(** The row's two halves, in the table's standard orientation. *)
Lemma seg_dist_lower :
  forall (A B P Q : Point), on_seg A B Q -> seg_dist A B P <= dist P Q.
Proof.
  intros A B P Q [t [Ht ->]].
  unfold seg_dist, dist. apply sqrt_le_1_alt.
  apply seg_dist_sq_lower. exact Ht.
Qed.

Lemma seg_dist_attained :
  forall (A B P : Point),
    exists Q, on_seg A B Q /\ dist P Q = seg_dist A B P.
Proof.
  intros A B P. exists (seg_point A B (seg_t A B P)). split.
  - exists (seg_t A B P). split; [apply seg_t_range | reflexivity].
  - reflexivity.
Qed.

(** Totality at the degenerate end: A = B collapses to the POINT row. *)
Lemma seg_dist_degenerate :
  forall (A B P : Point), dist_sq A B = 0 -> seg_dist A B P = dist P A.
Proof.
  intros A B P H0.
  unfold seg_dist, seg_t.
  destruct (Req_EM_T (dist_sq A B) 0) as [_ | Hne]; [| contradiction].
  unfold dist. f_equal. unfold dist_sq, seg_point. cbn [px py]. ring.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  The empty-disk row: the segment's emptiness threshold.                  *)
(* -------------------------------------------------------------------------- *)

Theorem empty_disk_seg_iff :
  forall (A B O : Point) (rho : R),
    empty_disk (on_seg A B) O rho <-> (0 <= rho /\ rho <= seg_dist A B O).
Proof.
  intros A B O rho. unfold empty_disk. split.
  - intros [Hr He]. split; [exact Hr |].
    destruct (seg_dist_attained A B O) as [Q [HQ Ha]].
    rewrite <- Ha. apply He. exact HQ.
  - intros [Hr Hle]. split; [exact Hr |]. intros P HP.
    eapply Rle_trans; [exact Hle | apply seg_dist_lower; exact HP].
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Ledger F6 — "the supporting line's foot suffices" (REFUTED).            *)
(*                                                                            *)
(* Dropping the clamp projects onto the LINE through A,B.  Beyond an          *)
(* endpoint that understates the distance: the segment is not its line.       *)
(* -------------------------------------------------------------------------- *)

Definition line_foot_dist (A B P : Point) : R :=
  dist P (seg_point A B (seg_dot A B P / dist_sq A B)).

Theorem seg_line_foot_hypothesis_refuted :
  ~ (forall A B P : Point, seg_dist A B P = line_foot_dist A B P).
Proof.
  intro H.
  specialize (H (mkPoint 0 0) (mkPoint 4 0) (mkPoint 7 4)).
  (* the true row: the foot t0 = 7/4 clamps to the endpoint B, distance 5 *)
  assert (Hseg : seg_dist (mkPoint 0 0) (mkPoint 4 0) (mkPoint 7 4) = 5).
  { unfold seg_dist, seg_t.
    destruct (Req_EM_T (dist_sq (mkPoint 0 0) (mkPoint 4 0)) 0) as [He | _].
    - exfalso. unfold dist_sq in He. cbn [px py] in He. lra.
    - assert (Hq : seg_dot (mkPoint 0 0) (mkPoint 4 0) (mkPoint 7 4)
                   / dist_sq (mkPoint 0 0) (mkPoint 4 0) = 7 / 4).
      { unfold seg_dot, dist_sq. cbn [px py]. lra. }
      rewrite Hq. rewrite Rmin_left by lra. rewrite Rmax_right by lra.
      apply dist_eq_of_dist_sq; [lra |].
      unfold dist_sq, seg_point. cbn [px py]. lra. }
  (* the unclamped foot lands at (7,0), distance 4 *)
  assert (Hfoot : line_foot_dist (mkPoint 0 0) (mkPoint 4 0) (mkPoint 7 4) = 4).
  { unfold line_foot_dist.
    assert (Hq : seg_dot (mkPoint 0 0) (mkPoint 4 0) (mkPoint 7 4)
                 / dist_sq (mkPoint 0 0) (mkPoint 4 0) = 7 / 4).
    { unfold seg_dot, dist_sq. cbn [px py]. lra. }
    rewrite Hq.
    apply dist_eq_of_dist_sq; [lra |].
    unfold dist_sq, seg_point. cbn [px py]. lra. }
  rewrite Hseg, Hfoot in H. lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  Audit footprint (classical-reals trio only).                            *)
(* -------------------------------------------------------------------------- *)

Print Assumptions seg_dist_lower.
Print Assumptions seg_dist_attained.
Print Assumptions seg_dist_degenerate.
Print Assumptions empty_disk_seg_iff.
Print Assumptions seg_line_foot_hypothesis_refuted.

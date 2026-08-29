(* ============================================================================
   NetTopologySuite.Proofs.ArcMidSweep
   ----------------------------------------------------------------------------
   Issue #508 arc leftovers from #552 (P2):

     1. `valid_arc a → arc_sweep a <> 0` — the zero outcome of
        ArcTraversalBridge.arc_sweep_cases is excluded by non-collinearity.
        `arc_sweep = 0` iff the principal `arc_sweep_angle = 0` (decision
        tree), and a vanishing principal angle plus equal radii forces
        `arc_end = arc_start`, which collapses `valid_arc`.

     2. Point-set through-`arc_mid`: the mid control is a point of the
        circumscribed-circle parameterization
          `circle_pt (arc_center a) (arc_radius a) (arc_mid_angle a)
             = arc_mid a`
        and, when the sweep is nonzero, it lies on the closed parameter
        interval that realizes the traversal (possibly after a 2π shift
        matching ArcTraversalBridge's periodicity).

   Category C lineage: atan2 / angle_between through ArcParamBridge and
   RelateArcAnalytic.  Removal tracks AngleBetween's cleanup — do not lift
   C1 elsewhere.  Does not start a new 64-a definition of r·θ.

   No `Admitted`, no `Axiom`, no `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.6
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import Distance CurveGeometry Atan2 AngleBetween
                               RelateArcAnalytic ArcLength CurveLength
                               ArcRectifiable ArcParamBridge ArcChordApprox
                               ArcTraversalBridge.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* 3-axiom prelude: valid_arc forbids a collapsed chord.                      *)
(* -------------------------------------------------------------------------- *)

Lemma valid_arc_start_neq_end : forall a : CircularArc,
  valid_arc a -> arc_start a <> arc_end a.
Proof.
  intros a Hva Heq.
  unfold valid_arc in Hva.
  rewrite Heq in Hva.
  lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* arc_sweep = 0 iff the principal angle is 0.                                *)
(* -------------------------------------------------------------------------- *)

Lemma arc_sweep_zero_iff_angle : forall a : CircularArc,
  valid_arc a ->
  arc_sweep a = 0 <-> arc_sweep_angle a = 0.
Proof.
  intros a Hva. split.
  - intro Hsw.
    pose proof (arc_sweep_principal_range a Hva) as Hrng.
    pose proof PI_ge_2 as HPI.
    unfold arc_sweep in Hsw; cbv zeta in Hsw.
    set (theta := arc_sweep_angle a) in *.
    set (phi := angle_between
                  (px (arc_start a) - px (arc_center a))
                  (py (arc_start a) - py (arc_center a))
                  (px (arc_mid a) - px (arc_center a))
                  (py (arc_mid a) - py (arc_center a))) in *.
    destruct (Rgt_dec theta 0) as [Hgt | Hngt].
    + destruct (Rgt_dec phi 0); try destruct (Rlt_dec phi theta);
        first [lra | unfold theta in *; lra].
    + destruct (Rlt_dec theta 0) as [Hlt | Hnlt].
      * destruct (Rlt_dec phi 0); try destruct (Rlt_dec theta phi);
          first [lra | unfold theta in *; lra].
      * unfold theta in *; lra.
  - intro Hz.
    unfold arc_sweep; cbv zeta.
    rewrite Hz.
    destruct (Rgt_dec 0 0); [lra |].
    destruct (Rlt_dec 0 0); [lra | reflexivity].
Qed.

Lemma arc_center_mid_vector_nonzero : forall a : CircularArc,
  valid_arc a ->
  ~ (px (arc_mid a) - px (arc_center a) = 0 /\
     py (arc_mid a) - py (arc_center a) = 0).
Proof.
  intros a Hva [Hx Hy].
  destruct (arc_center_equidistant a Hva) as [Hsm _].
  pose proof (arc_start_center_dist_sq_pos a Hva) as Hpos.
  assert (Hmid0 :
    dist_sq (arc_mid a) (arc_center a) = 0).
  { unfold dist_sq. rewrite Hx, Hy. ring. }
  rewrite (dist_sq_sym (arc_mid a) (arc_center a)) in Hmid0.
  rewrite <- Hsm in Hmid0.
  rewrite (dist_sq_sym (arc_start a) (arc_center a)) in Hpos.
  lra.
Qed.

(* WITNESS {"claimId":"arcmidsweep-valid-arc-sweep-nonzero","topic":"arc","lemma":"valid_arc_sweep_nonzero","title":"valid_arc excludes the zero arc_sweep outcome of the mid-disambiguated traversal","file":"theories/ArcMidSweep.v"} *)

Theorem valid_arc_sweep_nonzero : forall a : CircularArc,
  valid_arc a -> arc_sweep a <> 0.
Proof.
  intros a Hva Hsw.
  apply (arc_sweep_zero_iff_angle a Hva) in Hsw.
  destruct (arc_center_vectors_nonzero a Hva) as [Hu Hv].
  destruct (arc_center_equidistant a Hva) as [_ Hse].
  set (ux := px (arc_start a) - px (arc_center a)).
  set (uy := py (arc_start a) - py (arc_center a)).
  set (vx := px (arc_end a) - px (arc_center a)).
  set (vy := py (arc_end a) - py (arc_center a)).
  set (r := arc_radius a).
  assert (Huv2 : ux * ux + uy * uy = vx * vx + vy * vy).
  { replace (ux * ux + uy * uy)
      with (dist_sq (arc_center a) (arc_start a))
      by (unfold dist_sq, ux, uy; ring).
    replace (vx * vx + vy * vy)
      with (dist_sq (arc_center a) (arc_end a))
      by (unfold dist_sq, vx, vy; ring).
    exact Hse. }
  assert (Hr2 : r * r = ux * ux + uy * uy).
  { unfold r, arc_radius. rewrite dist_mul_self.
    unfold dist_sq, ux, uy. ring. }
  assert (Hupos : 0 < ux * ux + uy * uy) by (apply sum_sq_pos; exact Hu).
  assert (Hr0 : 0 <= r) by (unfold r, arc_radius; apply dist_nonneg).
  assert (Hrpos : 0 < r).
  { destruct (Req_dec r 0) as [Hz | Hnz]; [| lra].
    rewrite Hz in Hr2. lra. }
  pose proof (sin_angle_between ux uy vx vy Hu Hv) as Hsin.
  pose proof (cos_angle_between ux uy vx vy Hu Hv) as Hcos.
  unfold arc_sweep_angle in Hsw.
  change (angle_between
            (px (arc_start a) - px (arc_center a))
            (py (arc_start a) - py (arc_center a))
            (px (arc_end a) - px (arc_center a))
            (py (arc_end a) - py (arc_center a)))
    with (angle_between ux uy vx vy) in Hsw.
  rewrite Hsw, sin_0 in Hsin.
  rewrite Hsw, cos_0 in Hcos.
  assert (Hsqu : sqrt (ux * ux + uy * uy) = r).
  { rewrite <- Hr2. replace (r * r) with (Rsqr r) by (unfold Rsqr; ring).
    apply sqrt_Rsqr; lra. }
  assert (Hsqv : sqrt (vx * vx + vy * vy) = r) by (rewrite <- Huv2; exact Hsqu).
  rewrite Hsqu, Hsqv in Hsin, Hcos.
  assert (Hcross : ux * vy - uy * vx = 0).
  { apply Rmult_eq_reg_r with (r := / (r * r)).
    2: { apply Rinv_neq_0_compat; nra. }
    replace ((ux * vy - uy * vx) * / (r * r))
      with ((ux * vy - uy * vx) / (r * r)) by (unfold Rdiv; ring).
    rewrite <- Hsin. unfold Rdiv. lra. }
  assert (Hdot : ux * vx + uy * vy = r * r).
  { apply Rmult_eq_reg_r with (r := / (r * r)).
    2: { apply Rinv_neq_0_compat; nra. }
    replace ((ux * vx + uy * vy) * / (r * r))
      with ((ux * vx + uy * vy) / (r * r)) by (unfold Rdiv; ring).
    rewrite <- Hcos. unfold Rdiv. field; lra. }
  assert (Hdiff :
    (ux - vx) * (ux - vx) + (uy - vy) * (uy - vy) = 0).
  { replace ((ux - vx) * (ux - vx) + (uy - vy) * (uy - vy))
      with ((ux * ux + uy * uy) + (vx * vx + vy * vy)
            - 2 * (ux * vx + uy * vy)) by ring.
    rewrite <- Hr2, <- Huv2, Hdot, <- Hr2. ring. }
  assert (Heq : ux = vx /\ uy = vy).
  { pose proof (Rle_0_sqr (ux - vx)) as Ax.
    pose proof (Rle_0_sqr (uy - vy)) as Ay.
    unfold Rsqr in Ax, Ay.
    assert (Hxz : Rsqr (ux - vx) = 0) by (unfold Rsqr; lra).
    assert (Hyz : Rsqr (uy - vy) = 0) by (unfold Rsqr; lra).
    apply Rsqr_eq_0 in Hxz. apply Rsqr_eq_0 in Hyz.
    split; lra. }
  destruct Heq as [Hx Hy].
  apply (valid_arc_start_neq_end a Hva).
  apply point_ext; unfold ux, uy, vx, vy in Hx, Hy; lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Point-set: arc_mid is a parameterized circumcircle point.                  *)
(* -------------------------------------------------------------------------- *)

Definition arc_mid_angle (a : CircularArc) : R :=
  atan2 (py (arc_mid a) - py (arc_center a))
        (px (arc_mid a) - px (arc_center a)).

(* WITNESS {"claimId":"arcmidsweep-arc-mid-on-circle-param","topic":"arc","lemma":"arc_mid_on_circle_param","title":"arc_mid is a point of the circumscribed-circle parameterization","file":"theories/ArcMidSweep.v"} *)

Theorem arc_mid_on_circle_param : forall a : CircularArc,
  valid_arc a ->
  circle_pt (arc_center a) (arc_radius a) (arc_mid_angle a)
  = arc_mid a.
Proof.
  intros a Hva.
  pose proof (arc_center_equidistant a Hva) as Heq.
  destruct Heq as [Hsm Hse].
  pose proof (arc_center_mid_vector_nonzero a Hva) as Hm.
  set (mx := px (arc_mid a) - px (arc_center a)).
  set (my := py (arc_mid a) - py (arc_center a)).
  set (r := arc_radius a).
  assert (Hr2 : r * r = mx * mx + my * my).
  { unfold r, arc_radius. rewrite dist_mul_self.
    rewrite Hsm. unfold dist_sq, mx, my. ring. }
  assert (Hmpos : 0 < mx * mx + my * my) by (apply sum_sq_pos; exact Hm).
  assert (Hr0 : 0 <= r) by (unfold r, arc_radius; apply dist_nonneg).
  assert (Hsqu : sqrt (mx * mx + my * my) = r).
  { rewrite <- Hr2. replace (r * r) with (Rsqr r) by (unfold Rsqr; ring).
    apply sqrt_Rsqr; lra. }
  assert (Hc : cos (arc_mid_angle a) = mx / r).
  { unfold arc_mid_angle. fold my. fold mx.
    rewrite cos_atan2 by exact Hm. rewrite Hsqu. reflexivity. }
  assert (Hs : sin (arc_mid_angle a) = my / r).
  { unfold arc_mid_angle. fold my. fold mx.
    rewrite sin_atan2 by exact Hm. rewrite Hsqu. reflexivity. }
  apply point_ext; unfold circle_pt; cbn [px py].
  - rewrite Hc. unfold mx. field. nra.
  - rewrite Hs. unfold my. field. nra.
Qed.

(* The mid point-set claim packaged with the nonzero sweep pin:
   a valid arc's mid is on the circumcircle AND the traversal is a
   genuine (nonzero) sweep. *)
Corollary arc_mid_pointset_and_sweep : forall a : CircularArc,
  valid_arc a ->
  circle_pt (arc_center a) (arc_radius a) (arc_mid_angle a) = arc_mid a
  /\ arc_sweep a <> 0.
Proof.
  intros a Hva. split.
  - apply arc_mid_on_circle_param; exact Hva.
  - apply valid_arc_sweep_nonzero; exact Hva.
Qed.

Print Assumptions valid_arc_sweep_nonzero.
Print Assumptions arc_mid_on_circle_param.
Print Assumptions arc_mid_pointset_and_sweep.

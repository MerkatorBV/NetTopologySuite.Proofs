(* ============================================================================
   NetTopologySuite.Proofs.LECCandidateWeighted
   ----------------------------------------------------------------------------
   LEC optimal-path ladder: candidate completeness, WEIGHTED (the Apollonius
   summit) — the maximiser classification for the additively-weighted
   clearance  min_i (dist(p, c_i) − r_i)  that `min_disc_dist_weighted`
   (LECObstacleDistance.v) reduces disc-site clearance to.

   The ledger predicted the shape exactly: the improvement kernel's shift
   expansion survives verbatim (a per-site radius is an additive constant,
   so it only moves the per-site LEVEL the distance must clear), but the
   two-nearest supplier does NOT survive.  With unequal norms
   |u1| ≠ |u2| (u_i = p − c_i at a weighted tie), the unweighted sum
   direction u1 + u2 can point INTO the nearer site:
   ⟨u1 + u2, u1⟩ = |u1|² + ⟨u1, u2⟩ goes negative.

     - F9 (RED): on the concrete weighted tie  p = (0,0),
       D1 = disc((−1,0), 1/2), D2 = disc((4,−3), 9/2)  — clearance 1/2
       on both, |u1| = 1, |u2| = 5 — the unweighted supplier direction
       u1 + u2 = (−3, 3) strictly WORSENS the clearance for every
       t ∈ (0, 1/3): dist² to c1 along it is 1 − 6t + 18t² < 1
       (`f9_sum_direction_worsens`, `f9_unweighted_supplier_refuted`).

     - GREEN: the repaired supplier is the WEIGHTED-BISECTOR NORMAL
       v := d2·u1 + d1·u2  (the angular-bisector direction scaled by
       d1·d2, so it needs no square roots).  The nonzero-square trick
       generalises: with  N := d1·d2 + ⟨u1, u2⟩,

           |v|² = 2·d1·d2·N,   ⟨v, u1⟩ = d1·N,   ⟨v, u2⟩ = d2·N,

       so one sign — N's — decides everything: N > 0 gives a strictly
       improving direction (`weighted_within_two_direction`), N = 0 is
       the antipodal ridge where the perpendicular is exactly tangent
       (same as the unweighted case), and N < 0 is impossible (it would
       make |v|² negative — Cauchy–Schwarz for free).  On the F9
       instance v = (1, 3) and both inner products are positive
       (`f9_weighted_supplier_improves`).

   With the new supplier the engine is unchanged: per-site levels
   L_D = w + r_D feed the same kernel (`weighted_improvement_kernel`),
   and the interior classification follows (`weighted_candidate_
   completeness_interior`, stated against a local-maximality hypothesis —
   no region plumbing).  With equal weights the weighted tie IS the
   unweighted tie and v is d·(u1 + u2) — the F8 supplier is the equal-
   weights slice (`equal_weights_tie_unweighted`).

   Honest scope: interior form only.  The edge-constrained weighted
   variant and the convex-polygon assembly remain open (ledger items),
   as does the runtime half (engine-side, perf gate).

   No `Admitted`, no `Axiom`, no `Parameter`; classical-reals trio only.
   topic: construct

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude (Fable)
   ============================================================================ *)

From Stdlib Require Import Reals Lra List.
Import ListNotations.
From NTS.Proofs Require Import Distance Disk LECObstacleDistance
                               LECCandidateComplete.

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §0  Weighted clearance: disc sites as additively-weighted point sites.      *)
(* -------------------------------------------------------------------------- *)

(** The additively-weighted distance to a disc site.  This is exactly the
    quantity `min_disc_dist_weighted` reduces the engine's disc-obstacle
    clearance to (up to the Rmax-0 clamp for points inside a disc). *)
Definition wdist (D : Disk) (p : Point) : R :=
  dist p (dcentre D) - dradius D.

(** The engine bridge: the typed disc metric is the clamped wdist. *)
Lemma wdist_engine_bridge :
  forall (D : Disk) (p : Point),
    disc_dist (dcentre D) (dradius D) p = Rmax 0 (wdist D p).
Proof.
  intros D p. unfold disc_dist, wdist.
  rewrite (dist_sym (dcentre D) p). reflexivity.
Qed.

(** With equal weights a weighted tie is an unweighted tie: F8's
    configuration is the equal-weights slice of this module. *)
Lemma equal_weights_tie_unweighted :
  forall (D1 D2 : Disk) (p : Point) (w : R),
    dradius D1 = dradius D2 ->
    wdist D1 p = w -> wdist D2 p = w ->
    dist p (dcentre D1) = dist p (dcentre D2).
Proof.
  intros D1 D2 p w He H1 H2. unfold wdist in *. lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §1  Finite-list glue, Disk-typed.                                          *)
(* -------------------------------------------------------------------------- *)

(** Finitely many per-site step bounds admit one uniform bound (the
    Disk-sited twin of LECCandidateComplete's `uniform_tau`). *)
Lemma uniform_tau_disks :
  forall (P : Disk -> R -> Prop) (l : list Disk),
    (forall D, In D l -> exists tau, 0 < tau /\
       forall t, 0 < t -> t < tau -> P D t) ->
    exists tau, 0 < tau /\
      forall D t, In D l -> 0 < t -> t < tau -> P D t.
Proof.
  intros P l. induction l as [| a tl IH]; intros H.
  - exists 1. split; [lra |]. intros D t [] _ _.
  - destruct (H a (in_eq a tl)) as [ta [Hta Ha]].
    destruct IH as [tt [Htt Htl]].
    { intros D HD. apply H, in_cons, HD. }
    exists (Rmin ta tt). split; [apply Rmin_glb_lt; assumption |].
    intros D t HD Ht Hlt. destruct (in_inv HD) as [-> | Hin].
    + apply Ha; [exact Ht |]. apply Rlt_le_trans with (Rmin ta tt);
        [exact Hlt | apply Rmin_l].
    + apply Htl; [exact Hin | exact Ht |].
      apply Rlt_le_trans with (Rmin ta tt); [exact Hlt | apply Rmin_r].
Qed.

(** Order transfers from squares to distances, downward. *)
Lemma dist_lt_of_sq_lt :
  forall (p q : Point) (r : R),
    0 <= r -> dist_sq p q < r * r -> dist p q < r.
Proof.
  intros p q r Hr Hlt.
  rewrite <- (sqrt_square r Hr). unfold dist.
  apply sqrt_lt_1_alt. split; [apply dist_sq_nonneg | exact Hlt].
Qed.

(** A known distance from a known square. *)
Lemma dist_of_sq :
  forall (p q : Point) (d : R),
    0 <= d -> dist_sq p q = d * d -> dist p q = d.
Proof.
  intros p q d Hd Hsq. unfold dist. rewrite Hsq.
  apply sqrt_square. exact Hd.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  The weighted improvement kernel: per-site levels, same engine.          *)
(* -------------------------------------------------------------------------- *)

(** The shift expansion survives verbatim: site D's radius only moves the
    LEVEL  L_D = w + dradius D  that `dist (shift p ...) (dcentre D)`
    must clear.  Hypotheses per site: strict slack, or a weighted tie
    with the direction pointing away-or-tangent. *)
Theorem weighted_improvement_kernel :
  forall (sites : list Disk) (p : Point) (w dx dy : R),
    (forall D, In D sites -> 0 < w + dradius D) ->
    0 < dx * dx + dy * dy ->
    (forall D, In D sites ->
       w < wdist D p \/
       (wdist D p = w /\
        0 <= dx * (px p - px (dcentre D)) + dy * (py p - py (dcentre D)))) ->
    exists tau, 0 < tau /\
      forall t, 0 < t -> t < tau ->
        forall D, In D sites -> w < wdist D (shift p dx dy t).
Proof.
  intros sites p w dx dy Hlev HL Hdir.
  assert (HsL : 0 < sqrt (dx * dx + dy * dy)) by (apply sqrt_lt_R0; exact HL).
  destruct (uniform_tau_disks
              (fun D t => w < wdist D (shift p dx dy t)) sites)
    as [tau [Htau Hall]].
  { intros D HD.
    specialize (Hlev D HD).
    destruct (Hdir D HD) as [Hfar | [Hnear Hip]];
      unfold wdist in *.
    - (* far site: the move is too short to eat the slack *)
      exists ((dist p (dcentre D) - (w + dradius D))
              / sqrt (dx * dx + dy * dy)). split.
      + apply Rdiv_lt_0_compat; lra.
      + intros t Ht Hlt.
        assert (Hmove : dist p (shift p dx dy t)
                        = t * sqrt (dx * dx + dy * dy))
          by (apply dist_shift_centre; lra).
        assert (Htri : dist p (dcentre D)
                       <= dist p (shift p dx dy t)
                          + dist (shift p dx dy t) (dcentre D))
          by apply dist_triangle.
        assert (Hfield : (dist p (dcentre D) - (w + dradius D))
                         / sqrt (dx * dx + dy * dy)
                         * sqrt (dx * dx + dy * dy)
                         = dist p (dcentre D) - (w + dradius D))
          by (field; lra).
        assert (Hstep : t * sqrt (dx * dx + dy * dy)
                        < dist p (dcentre D) - (w + dradius D)).
        { rewrite <- Hfield.
          apply Rmult_lt_compat_r; [exact HsL | exact Hlt]. }
        lra.
    - (* tied site: away-or-tangent, the quadratic term wins *)
      exists 1. split; [lra |].
      intros t Ht _.
      assert (Hgoal : w + dradius D < dist (shift p dx dy t) (dcentre D));
        [| lra].
      apply lt_dist_of_lt_sq; [lra |].
      rewrite dist_sq_shift.
      rewrite (dist_sq_of_dist p (dcentre D) (w + dradius D)) by lra.
      assert (H2 : 0 <= 2 * t * (dx * (px p - px (dcentre D))
                                 + dy * (py p - py (dcentre D))))
        by (apply Rmult_le_pos; lra).
      assert (H3 : 0 < t * t * (dx * dx + dy * dy))
        by (apply Rmult_lt_0_compat; [apply Rmult_lt_0_compat; lra | lra]).
      lra. }
  exists tau. split; [exact Htau |].
  intros t Ht Hlt D HD. apply Hall; assumption.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  The weighted-bisector supplier.                                        *)
(* -------------------------------------------------------------------------- *)

(** All weighted-nearest sites are covered by two named ones. *)
Definition weighted_nearest_within_two
    (sites : list Disk) (p : Point) (w : R) (D1 D2 : Disk) : Prop :=
  In D1 sites /\ In D2 sites /\ wdist D1 p = w /\ wdist D2 p = w /\
  forall D, In D sites -> wdist D p = w -> D = D1 \/ D = D2.

(** THE NEW SUPPLIER.  At a weighted two-site tie the away-vectors
    u_i = p − c_i have (generally unequal) norms d_i = w + r_i, and the
    kernel-ready direction is the weighted-bisector normal

        v = d2·u1 + d1·u2      (= d1·d2·(û1 + û2), but square-root-free).

    One polynomial identity runs the whole case split: with
    N = d1·d2 + ⟨u1,u2⟩,  |v|² = 2·d1·d2·N,  ⟨v,u1⟩ = d1·N,
    ⟨v,u2⟩ = d2·N.  N > 0 is the generic case, N = 0 the antipodal
    ridge (perpendicular direction, both inner products zero), and
    N < 0 cannot happen. *)
Lemma weighted_within_two_direction :
  forall (sites : list Disk) (p : Point) (w : R) (D1 D2 : Disk),
    (forall D, In D sites -> 0 < w + dradius D) ->
    (forall D, In D sites -> w <= wdist D p) ->
    weighted_nearest_within_two sites p w D1 D2 ->
    exists dx dy,
      0 < dx * dx + dy * dy /\
      forall D, In D sites ->
        w < wdist D p \/
        (wdist D p = w /\
         0 <= dx * (px p - px (dcentre D)) + dy * (py p - py (dcentre D))).
Proof.
  intros sites p w D1 D2 Hlev Hcl (Hin1 & Hin2 & Hw1 & Hw2 & Hcover).
  set (d1 := w + dradius D1). set (d2 := w + dradius D2).
  assert (Hd1 : 0 < d1) by (unfold d1; apply (Hlev D1 Hin1)).
  assert (Hd2 : 0 < d2) by (unfold d2; apply (Hlev D2 Hin2)).
  set (u1x := px p - px (dcentre D1)). set (u1y := py p - py (dcentre D1)).
  set (u2x := px p - px (dcentre D2)). set (u2y := py p - py (dcentre D2)).
  assert (Hsq1 : u1x * u1x + u1y * u1y = d1 * d1).
  { unfold u1x, u1y.
    replace ((px p - px (dcentre D1)) * (px p - px (dcentre D1))
             + (py p - py (dcentre D1)) * (py p - py (dcentre D1)))
      with (dist_sq p (dcentre D1)) by (unfold dist_sq; ring).
    apply dist_sq_of_dist. unfold d1. unfold wdist in Hw1. lra. }
  assert (Hsq2 : u2x * u2x + u2y * u2y = d2 * d2).
  { unfold u2x, u2y.
    replace ((px p - px (dcentre D2)) * (px p - px (dcentre D2))
             + (py p - py (dcentre D2)) * (py p - py (dcentre D2)))
      with (dist_sq p (dcentre D2)) by (unfold dist_sq; ring).
    apply dist_sq_of_dist. unfold d2. unfold wdist in Hw2. lra. }
  (* the per-site disjunction from the two cover cases *)
  assert (Hsite : forall dx dy,
             0 <= dx * u1x + dy * u1y ->
             0 <= dx * u2x + dy * u2y ->
             forall D, In D sites ->
               w < wdist D p \/
               (wdist D p = w /\
                0 <= dx * (px p - px (dcentre D))
                     + dy * (py p - py (dcentre D)))).
  { intros dx dy Hip1 Hip2 D HD.
    destruct (total_order_T w (wdist D p)) as [[Hlt | Heq] | Hgt].
    - left. exact Hlt.
    - right. split; [symmetry; exact Heq |].
      destruct (Hcover D HD (eq_sym Heq)) as [-> | ->].
      + exact Hip1.
      + exact Hip2.
    - exfalso. specialize (Hcl D HD). lra. }
  set (ip := u1x * u2x + u1y * u2y).
  set (N := d1 * d2 + ip).
  set (vx := d2 * u1x + d1 * u2x). set (vy := d2 * u1y + d1 * u2y).
  assert (Hvsq : vx * vx + vy * vy = 2 * (d1 * d2) * N).
  { unfold vx, vy, N, ip.
    replace ((d2 * u1x + d1 * u2x) * (d2 * u1x + d1 * u2x)
             + (d2 * u1y + d1 * u2y) * (d2 * u1y + d1 * u2y))
      with (d2 * d2 * (u1x * u1x + u1y * u1y)
            + d1 * d1 * (u2x * u2x + u2y * u2y)
            + 2 * (d1 * d2) * (u1x * u2x + u1y * u2y)) by ring.
    rewrite Hsq1, Hsq2. ring. }
  assert (Hvu1 : vx * u1x + vy * u1y = d1 * N).
  { unfold vx, vy, N, ip.
    replace ((d2 * u1x + d1 * u2x) * u1x + (d2 * u1y + d1 * u2y) * u1y)
      with (d2 * (u1x * u1x + u1y * u1y)
            + d1 * (u1x * u2x + u1y * u2y)) by ring.
    rewrite Hsq1. ring. }
  assert (Hvu2 : vx * u2x + vy * u2y = d2 * N).
  { unfold vx, vy, N, ip.
    replace ((d2 * u1x + d1 * u2x) * u2x + (d2 * u1y + d1 * u2y) * u2y)
      with (d1 * (u2x * u2x + u2y * u2y)
            + d2 * (u1x * u2x + u1y * u2y)) by ring.
    rewrite Hsq2. ring. }
  destruct (total_order_T 0 N) as [[HNpos | HNzero] | HNneg].
  - (* generic: v itself, both inner products strictly positive *)
    exists vx, vy. split.
    + rewrite Hvsq.
      apply Rmult_lt_0_compat; [| exact HNpos].
      apply Rmult_lt_0_compat; [lra |].
      apply Rmult_lt_0_compat; assumption.
    + apply Hsite.
      * rewrite Hvu1. left.
        apply Rmult_lt_0_compat; assumption.
      * rewrite Hvu2. left.
        apply Rmult_lt_0_compat; assumption.
  - (* antipodal ridge: d2·u1 = −d1·u2; the perpendicular is tangent *)
    assert (Hv0 : vx * vx + vy * vy = 0)
      by (rewrite Hvsq, <- HNzero; ring).
    assert (Hvx : vx = 0).
    { destruct (Req_EM_T vx 0) as [H0 | Hne0]; [exact H0 |].
      exfalso. pose proof (Rsqr_pos_lt _ Hne0) as Hp.
      pose proof (Rle_0_sqr vy) as Hq.
      unfold Rsqr in Hp, Hq. lra. }
    assert (Hvy : vy = 0).
    { destruct (Req_EM_T vy 0) as [H0 | Hne0]; [exact H0 |].
      exfalso. pose proof (Rsqr_pos_lt _ Hne0) as Hp.
      pose proof (Rle_0_sqr vx) as Hq.
      unfold Rsqr in Hp, Hq. lra. }
    assert (Hu2x : d1 * u2x = - d2 * u1x) by (unfold vx in Hvx; lra).
    assert (Hu2y : d1 * u2y = - d2 * u1y) by (unfold vy in Hvy; lra).
    exists (- u1y), u1x. split.
    + assert (HdL : - u1y * - u1y + u1x * u1x = u1x * u1x + u1y * u1y)
        by ring.
      rewrite HdL, Hsq1.
      apply Rmult_lt_0_compat; assumption.
    + apply Hsite.
      * assert (Hz : - u1y * u1x + u1x * u1y = 0) by ring. lra.
      * assert (Hd1ip : d1 * (- u1y * u2x + u1x * u2y) = 0).
        { replace (d1 * (- u1y * u2x + u1x * u2y))
            with (- u1y * (d1 * u2x) + u1x * (d1 * u2y)) by ring.
          rewrite Hu2x, Hu2y. ring. }
        assert (Hip0 : - u1y * u2x + u1x * u2y = 0).
        { destruct (Rmult_integral _ _ Hd1ip) as [Hc | Hc];
            [exfalso; lra | exact Hc]. }
        lra.
  - (* N < 0 would make |v|² negative: Cauchy–Schwarz for free *)
    exfalso.
    assert (Hd12 : 0 < d1 * d2) by (apply Rmult_lt_0_compat; assumption).
    assert (Hneg : 2 * (d1 * d2) * N < 0) by nra.
    pose proof (Rle_0_sqr vx) as Ha.
    pose proof (Rle_0_sqr vy) as Hb.
    unfold Rsqr in Ha, Hb. lra.
Qed.

(** THE POSITIVE IMPROVEMENT THEOREM, weighted interior form: at most two
    weighted-nearest sites  =>  an explicit strictly improving direction
    with a uniform step bound. *)
Theorem weighted_within_two_improvable :
  forall (sites : list Disk) (p : Point) (w : R) (D1 D2 : Disk),
    (forall D, In D sites -> 0 < w + dradius D) ->
    (forall D, In D sites -> w <= wdist D p) ->
    weighted_nearest_within_two sites p w D1 D2 ->
    exists dx dy tau,
      0 < dx * dx + dy * dy /\ 0 < tau /\
      forall t, 0 < t -> t < tau ->
        forall D, In D sites -> w < wdist D (shift p dx dy t).
Proof.
  intros sites p w D1 D2 Hlev Hcl Hw2.
  destruct (weighted_within_two_direction sites p w D1 D2 Hlev Hcl Hw2)
    as [dx [dy [HL Hdir]]].
  destruct (weighted_improvement_kernel sites p w dx dy Hlev HL Hdir)
    as [tau [Htau Himp]].
  exists dx, dy, tau. auto.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Interior candidate completeness, weighted.                             *)
(* -------------------------------------------------------------------------- *)

(** A local maximiser of weighted clearance in the open eps-ball can never
    have at most two weighted-nearest sites: three-way Apollonius ties
    (or boundary contact) are forced.  Stated against a bare local-
    maximality hypothesis — no region or domain plumbing needed. *)
Theorem weighted_candidate_completeness_interior :
  forall (sites : list Disk) (p : Point) (w eps : R),
    (forall D, In D sites -> 0 < w + dradius D) ->
    (forall D, In D sites -> w <= wdist D p) ->
    0 < eps ->
    (forall q, dist p q < eps ->
       ~ (forall D, In D sites -> w < wdist D q)) ->
    ~ (exists D1 D2, weighted_nearest_within_two sites p w D1 D2).
Proof.
  intros sites p w eps Hlev Hcl Heps Hmax [D1 [D2 Hw2]].
  destruct (weighted_within_two_improvable sites p w D1 D2 Hlev Hcl Hw2)
    as [dx [dy [tau [HL [Htau Himp]]]]].
  assert (HsL : 0 < sqrt (dx * dx + dy * dy)) by (apply sqrt_lt_R0; exact HL).
  set (t := Rmin (tau / 2) (eps / (2 * sqrt (dx * dx + dy * dy)))).
  assert (Ht : 0 < t).
  { unfold t. apply Rmin_glb_lt; [lra |].
    apply Rdiv_lt_0_compat; lra. }
  assert (Httau : t < tau).
  { unfold t. apply Rle_lt_trans with (tau / 2); [apply Rmin_l | lra]. }
  set (q := shift p dx dy t).
  assert (Hmove : dist p q < eps).
  { unfold q. rewrite dist_shift_centre by lra.
    assert (Hhalf : eps / (2 * sqrt (dx * dx + dy * dy))
                    * sqrt (dx * dx + dy * dy) = eps / 2)
      by (field; lra).
    apply Rle_lt_trans with (eps / 2); [| lra].
    rewrite <- Hhalf.
    apply Rmult_le_compat_r; [lra |].
    unfold t. apply Rmin_r. }
  apply (Hmax q Hmove).
  intros D HD. unfold q. apply Himp; assumption.
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  F9: the unweighted supplier direction is REFUTED at a weighted tie.    *)
(* -------------------------------------------------------------------------- *)

Definition f9_D1 : Disk := mkDisk (mkPoint (-1) 0) (1 / 2).
Definition f9_D2 : Disk := mkDisk (mkPoint 4 (-3)) (9 / 2).
Definition f9_sites : list Disk := [f9_D1; f9_D2].
Definition f9_p : Point := mkPoint 0 0.

Lemma f9_dist1 : dist f9_p (dcentre f9_D1) = 1.
Proof.
  apply dist_of_sq; [lra |].
  unfold dist_sq, f9_p, f9_D1. simpl. ring.
Qed.

Lemma f9_dist2 : dist f9_p (dcentre f9_D2) = 5.
Proof.
  apply dist_of_sq; [lra |].
  unfold dist_sq, f9_p, f9_D2. simpl. ring.
Qed.

(** Both sites tie at weighted clearance 1/2, with unequal norms 1 ≠ 5. *)
Lemma f9_tie1 : wdist f9_D1 f9_p = 1 / 2.
Proof. unfold wdist. rewrite f9_dist1. unfold f9_D1. simpl. lra. Qed.

Lemma f9_tie2 : wdist f9_D2 f9_p = 1 / 2.
Proof. unfold wdist. rewrite f9_dist2. unfold f9_D2. simpl. lra. Qed.

Lemma f9_within_two :
  weighted_nearest_within_two f9_sites f9_p (1 / 2) f9_D1 f9_D2.
Proof.
  split; [left; reflexivity |].
  split; [right; left; reflexivity |].
  split; [exact f9_tie1 |].
  split; [exact f9_tie2 |].
  intros D HD _. destruct HD as [HD | [HD | []]]; auto.
Qed.

(** THE RED HALF.  The unweighted supplier direction u1 + u2 = (−3, 3)
    (the F8 formula, blind to the weights) strictly WORSENS the weighted
    clearance for every t ∈ (0, 1/3): the squared distance to c1 along
    it is 1 − 6t + 18t² < 1. *)
Lemma f9_sum_direction_worsens :
  forall t, 0 < t -> t < 1 / 3 ->
    wdist f9_D1 (shift f9_p (-3) 3 t) < 1 / 2.
Proof.
  intros t Ht Hlt.
  assert (Hd : dist (shift f9_p (-3) 3 t) (dcentre f9_D1) < 1).
  { apply dist_lt_of_sq_lt; [lra |].
    rewrite dist_sq_shift.
    replace (dist_sq f9_p (dcentre f9_D1)) with 1
      by (unfold dist_sq, f9_p, f9_D1; simpl; ring).
    replace ((-3) * (px f9_p - px (dcentre f9_D1))
             + 3 * (py f9_p - py (dcentre f9_D1))) with (-3)
      by (unfold f9_p, f9_D1; simpl; ring).
    replace ((-3) * (-3) + 3 * 3) with 18 by ring.
    nra. }
  unfold wdist, f9_D1 in *. simpl in *. lra.
Qed.

(** F9, packaged: no step bound rescues the unweighted supplier here —
    the direction that within_two_direction would emit for point sites
    is NOT an improving direction for weighted sites. *)
Theorem f9_unweighted_supplier_refuted :
  ~ (exists tau, 0 < tau /\
       forall t, 0 < t -> t < tau ->
         forall D, In D f9_sites -> 1 / 2 < wdist D (shift f9_p (-3) 3 t)).
Proof.
  intros [tau [Htau Himp]].
  set (t := Rmin tau (1 / 3) / 2).
  assert (Hmin : 0 < Rmin tau (1 / 3)) by (apply Rmin_glb_lt; lra).
  assert (Ht : 0 < t) by (unfold t; lra).
  assert (Httau : t < tau).
  { unfold t.
    apply Rlt_le_trans with (Rmin tau (1 / 3)); [lra | apply Rmin_l]. }
  assert (Ht3 : t < 1 / 3).
  { unfold t.
    apply Rlt_le_trans with (Rmin tau (1 / 3)); [lra | apply Rmin_r]. }
  specialize (Himp t Ht Httau f9_D1 (or_introl eq_refl)).
  pose proof (f9_sum_direction_worsens t Ht Ht3). lra.
Qed.

(** THE GREEN HALF.  The weighted-bisector normal on the same instance is
    v = d2·u1 + d1·u2 = 5·(1,0) + 1·(−4,3) = (1,3): both away inner
    products are positive (1 and 5), so the kernel fires. *)
Lemma f9_weighted_direction_kernel_ready :
  forall D, In D f9_sites ->
    1 / 2 < wdist D f9_p \/
    (wdist D f9_p = 1 / 2 /\
     0 <= 1 * (px f9_p - px (dcentre D)) + 3 * (py f9_p - py (dcentre D))).
Proof.
  intros D [HD | [HD | []]]; subst D; right.
  - split; [exact f9_tie1 |]. unfold f9_p, f9_D1. simpl. lra.
  - split; [exact f9_tie2 |]. unfold f9_p, f9_D2. simpl. lra.
Qed.

Theorem f9_weighted_supplier_improves :
  exists tau, 0 < tau /\
    forall t, 0 < t -> t < tau ->
      forall D, In D f9_sites -> 1 / 2 < wdist D (shift f9_p 1 3 t).
Proof.
  apply weighted_improvement_kernel.
  - intros D [HD | [HD | []]]; subst D; simpl; lra.
  - lra.
  - exact f9_weighted_direction_kernel_ready.
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions wdist_engine_bridge.
Print Assumptions equal_weights_tie_unweighted.
Print Assumptions uniform_tau_disks.
Print Assumptions weighted_improvement_kernel.
Print Assumptions weighted_within_two_direction.
Print Assumptions weighted_within_two_improvable.
Print Assumptions weighted_candidate_completeness_interior.
Print Assumptions f9_sum_direction_worsens.
Print Assumptions f9_unweighted_supplier_refuted.
Print Assumptions f9_weighted_direction_kernel_ready.
Print Assumptions f9_weighted_supplier_improves.

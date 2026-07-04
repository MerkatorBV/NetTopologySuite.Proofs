(* ==========================================================================
   WalkResidualKit.v

   [H-bridge attack, C-3f discharge rung E-2a] THE PER-STEP KIT for the
   walk residual: what `walk_small_offset_connectivity`'s per-step
   wiring consumes, packaged as EXISTENTIAL THRESHOLDS at an arbitrary
   arrangement dart / walk vertex.

     - `range_family_fold` / `cap_family_fold`: choice-free folds of
       finitely many per-index thresholds into ONE.  The point of the
       formulation: the per-index data arrives as an EXISTENTIAL (one
       (t, rho_factor) or one cap per index), so no function-valued
       choice is available; the induction on the index bound keeps the
       existentials inside and combines with Rmin/Rmax, using that the
       E-1 band shape is monotone (shrinking t and growing rho_factor
       only strengthens the constraint set).

     - `walk_corner_range_at`: at the tip of ANY arrangement dart `x`,
       the E-1 range-form corner threshold holds for the walk's wall
       pair `(ddir (twin x), ddir (fstep D x))`, by the D-4b-1
       trichotomy.  A trace vertex routes through
       `trace_vertex_incident_pair` + `on_ring_vertex_clearance`, with
       BOTH germ exclusions discharged by `fan_gap_uncertified`: the
       slot germs are `ddir (twin e_in)` and `ddir e_out`, and both
       germ-darts are members of the fan at the vertex (twin closure
       resp. direct membership), so no case analysis on wall
       coincidence is needed -- the gap theorem covers walls too.  An
       off-trace vertex routes through `off_trace_vertex_complement`
       with both slots vacuous (D-4a).  The gap nondegeneracy comes
       from `no_spurs` (the successor is not the reversal) plus
       `fan_ok`'s pairwise nonparallelism.

     - `walk_ride_at`: ANY arrangement dart's base-to-tip sample ride
       (D-1) holds below an explicit delta cap.  The corridor-clearance
       window must be fixed BEFORE the clearance threshold exists, so
       it is pinned at the rho-fractions `[tip + rho2*span/2,
       base - rho1*span/2]` of the dart's y-span; the bridge heights
       land inside it once `delta * (|vx|+1) < rho_i * span / 2`, and
       the corridor offset `delta * (vx^2+vy^2) / span` drops below the
       clearance threshold for delta below an explicit linear cap.

   No `Admitted` / `Axiom` / `Parameter`; allowlist axioms only.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
   ========================================================================== *)

From Stdlib Require Import Reals Lra List Arith Lia.
From NTS.Proofs Require Import Distance Overlay OverlayGraph Vec Azimuth
                               Direction Dart DartAngularOrder DartNext
                               DartNextSpec DartFace NoShortFaces
                               FaceTwinAware PointInRingTangents
                               JordanCurveSeam JCT JCTHugStep RingClearance
                               JCTTautClearance SectorPath CornerSamples
                               CornerConnector FanGapSector FanCorner
                               WalkCorners WalkCornerRange DartPath
                               RingExtract CycleRing GeneralTautBridge
                               EdgeConnectivity ArrangementEMinus
                               HBridgeCoreSlice WalkVertexPack WalkFamilies
                               JCTCorridor JCTMinOpenStep WalkCorridor
                               MirrorCorridor DartSideKit
                               CornerCorridorBridge WalkStepChain WalkRides.

Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  Choice-free folds of per-index thresholds.                              *)
(* -------------------------------------------------------------------------- *)

(* Fold the E-1 band-form thresholds: each index below k has SOME
   (t, rho_factor) band; then ONE (t, rho_factor) band works for all of
   them.  Monotonicity does the combination: delta < Rmin caps every
   individual t, and rho >= Rmax rho_factors * delta caps every
   individual lower band edge. *)
Lemma range_family_fold :
  forall (k : nat) (P : nat -> R -> R -> Prop),
    (forall i, (i < k)%nat ->
       exists t rho_factor : R, 0 < t /\ 0 < rho_factor /\
         forall delta rho,
           0 < delta < t -> rho_factor * delta <= rho -> rho < t ->
           P i delta rho) ->
    exists t rho_factor : R, 0 < t /\ 0 < rho_factor /\
      forall i, (i < k)%nat ->
      forall delta rho,
        0 < delta < t -> rho_factor * delta <= rho -> rho < t ->
        P i delta rho.
Proof.
  induction k as [| k IH]; intros P Hall.
  - exists 1, 1. split; [ lra | split; [ lra | ] ].
    intros i Hi. lia.
  - destruct (IH P (fun i Hi => Hall i (Nat.lt_lt_succ_r _ _ Hi)))
      as [t0 [F0 [Ht0 [HF0 Hfold]]]].
    destruct (Hall k (Nat.lt_succ_diag_r k)) as [tk [Fk [Htk [HFk Hk]]]].
    exists (Rmin t0 tk), (Rmax F0 Fk).
    split; [ apply Rmin_glb_lt; assumption | ].
    split; [ apply (Rlt_le_trans _ F0); [ exact HF0 | apply Rmax_l ] | ].
    intros i Hi delta rho Hd Hlo Hhi.
    pose proof (Rmin_l t0 tk) as Hm1. pose proof (Rmin_r t0 tk) as Hm2.
    pose proof (Rmax_l F0 Fk) as HM1. pose proof (Rmax_r F0 Fk) as HM2.
    destruct (Nat.lt_ge_cases i k) as [Hik | Hik].
    + apply (Hfold i Hik); [ lra | | lra ].
      apply Rle_trans with (Rmax F0 Fk * delta); [ | exact Hlo ].
      apply Rmult_le_compat_r; lra.
    + assert (Hieq : i = k) by lia. subst i.
      apply Hk; [ lra | | lra ].
      apply Rle_trans with (Rmax F0 Fk * delta); [ | exact Hlo ].
      apply Rmult_le_compat_r; lra.
Qed.

(* Fold per-index delta caps: each index below k accepts every delta
   below SOME positive cap; then every delta below the Rmin of the caps
   works for all of them. *)
Lemma cap_family_fold :
  forall (k : nat) (Q : nat -> R -> Prop),
    (forall i, (i < k)%nat ->
       exists cap : R, 0 < cap /\ forall x, 0 < x < cap -> Q i x) ->
    exists cap : R, 0 < cap /\
      forall i, (i < k)%nat -> forall x, 0 < x < cap -> Q i x.
Proof.
  induction k as [| k IH]; intros Q Hall.
  - exists 1. split; [ lra | intros i Hi; lia ].
  - destruct (IH Q (fun i Hi => Hall i (Nat.lt_lt_succ_r _ _ Hi)))
      as [c0 [Hc0 Hfold]].
    destruct (Hall k (Nat.lt_succ_diag_r k)) as [ck [Hck Hk]].
    exists (Rmin c0 ck).
    split; [ apply Rmin_glb_lt; assumption | ].
    intros i Hi y Hy.
    pose proof (Rmin_l c0 ck) as Hm1. pose proof (Rmin_r c0 ck) as Hm2.
    destruct (Nat.lt_ge_cases i k) as [Hik | Hik].
    + apply (Hfold i Hik). lra.
    + assert (Hieq : i = k) by lia. subst i. apply Hk. lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  Direction coordinates.                                                  *)
(* -------------------------------------------------------------------------- *)

Lemma vy_ddir : forall x : Dart, vy (ddir x) = py (dtip x) - py (dbase x).
Proof. intros [a b]. reflexivity. Qed.

Lemma vx_ddir : forall x : Dart, vx (ddir x) = px (dtip x) - px (dbase x).
Proof. intros [a b]. reflexivity. Qed.

(* -------------------------------------------------------------------------- *)
(* §3  The per-vertex corner threshold at a walk dart's tip.                   *)
(* -------------------------------------------------------------------------- *)

Theorem walk_corner_range_at :
  forall (E : list Edge) (d0 : Dart) (c : list Dart) (x : Dart),
    (forall v : Point, fan_ok (outgoing v (darts_of E))) ->
    no_spurs (darts_of E) ->
    no_horizontal_darts (darts_of E) ->
    no_foreign_vertex_twin_aware (darts_of E) ->
    ring_no_vertex_on_foreign_edge_interior (ring_of_chain (d0 :: c)) ->
    dpath (darts_of (E_minus E d0)) (dtip d0) (dbase d0) c ->
    NoDup (dtip d0 :: map dtip c) ->
    ring_edges (ring_of_chain (d0 :: c)) = d0 :: c ->
    (forall f, In f (d0 :: c) -> In f (darts_of E)) ->
    In x (darts_of E) ->
    exists t rho_factor : R,
      0 < t /\ 0 < rho_factor /\
      forall delta rho,
        0 < delta < t -> rho_factor * delta <= rho -> rho < t ->
        connected_in_complement_cont (ring_of_chain (d0 :: c))
          (point_at (dtip x)
             (corner_sample_in (ddir (twin x)) rho delta))
          (point_at (dtip x)
             (corner_sample_out (ddir (fstep (darts_of E) x)) rho delta)).
Proof.
  intros E d0 c x Hfan Hns Hnh Hnfv Hnfv_r Hp Hnd Hedges HWD Hx.
  (* the fan at the tip contains both walls *)
  assert (Htwx : In (twin x) (darts_of E))
    by (apply darts_of_closed_under_twin; exact Hx).
  assert (HtwF : In (twin x) (outgoing (dtip x) (darts_of E)))
    by (apply twin_in_fan; exact Htwx).
  assert (HfF : fan_ok (outgoing (dtip x) (darts_of E))) by apply Hfan.
  assert (Hstep : fstep (darts_of E) x
                    = next (outgoing (dtip x) (darts_of E)) (twin x))
    by reflexivity.
  assert (HnF : In (fstep (darts_of E) x) (outgoing (dtip x) (darts_of E)))
    by (rewrite Hstep; apply next_in; exact HtwF).
  (* gap nondegeneracy: the successor is not the reversal (no_spurs),
     and fan directions are pairwise nonparallel *)
  assert (Hcne : vcross (ddir (twin x)) (ddir (fstep (darts_of E) x)) <> 0).
  { apply cross_nonzero.
    apply (proj2 HfF); [ exact HtwF | exact HnF | ].
    intro Heq. apply (Hns x Hx). symmetry. exact Heq. }
  (* ring-level horizontality guard *)
  assert (Hnoh_r : no_horizontal_edges (ring_of_chain (d0 :: c))).
  { intros g Hg. rewrite Hedges in Hg. exact (Hnh g (HWD g Hg)). }
  destruct (in_dec point_eq_dec (dtip x) (dtip d0 :: map dtip c))
    as [Hon | Hoff].
  - (* TRACE vertex: incident chain-edge pair fills the pruned slots *)
    destruct (trace_vertex_incident_pair _ d0 c (dtip x) Hp Hon)
      as [e_in [e_out [Hin [Hout [Htip Hbase]]]]].
    assert (Hein_eq : (dbase e_in, dtip x) = e_in).
    { rewrite <- Htip. symmetry. apply surjective_pairing. }
    assert (Heout_eq : (dtip x, dtip e_out) = e_out).
    { rewrite <- Hbase. symmetry. apply surjective_pairing. }
    (* both slot germ-darts are fan members at the vertex *)
    assert (HtwinF : In (twin e_in) (outgoing (dtip x) (darts_of E))).
    { apply in_outgoing. split.
      - apply darts_of_closed_under_twin. apply HWD. exact Hin.
      - rewrite dbase_twin. exact Htip. }
    assert (HoutF : In e_out (outgoing (dtip x) (darts_of E))).
    { apply in_outgoing. split; [ apply HWD; exact Hout | exact Hbase ]. }
    (* germ exclusions: the gap theorem covers members AND walls *)
    assert (Hma : ~ in_open_sector (ddir (twin x))
                    (ddir (fstep (darts_of E) x))
                    (point_diff (dbase e_in) (dtip x))).
    { assert (Hg : ddir (twin e_in) = point_diff (dbase e_in) (dtip x)).
      { unfold ddir. rewrite dtip_twin, dbase_twin, Htip. reflexivity. }
      rewrite <- Hg, Hstep.
      exact (fan_gap_uncertified _ (twin x) (twin e_in) HfF HtwF HtwinF). }
    assert (Hmb : ~ in_open_sector (ddir (twin x))
                    (ddir (fstep (darts_of E) x))
                    (point_diff (dtip e_out) (dtip x))).
    { assert (Hg : ddir e_out = point_diff (dtip e_out) (dtip x)).
      { unfold ddir. rewrite Hbase. reflexivity. }
      rewrite <- Hg, Hstep.
      exact (fan_gap_uncertified _ (twin x) e_out HfF HtwF HoutF). }
    apply (walk_corner_threshold_range (ring_of_chain (d0 :: c)) (dtip x)
             (dbase e_in) (dtip e_out)
             (ddir (twin x)) (ddir (fstep (darts_of E) x))
             Hnoh_r); [ | exact Hma | exact Hmb | exact Hcne ].
    intros f Hf Hne1 Hne2.
    apply (on_ring_vertex_clearance _ d0 c (dtip x) e_in e_out
             Hp Hnd Hnfv_r Hedges Hin Hout Htip Hbase f Hf).
    + intro Hfe. apply Hne1. rewrite Hfe. symmetry. exact Hein_eq.
    + intro Hfe. apply Hne2. rewrite Hfe. symmetry. exact Heout_eq.
  - (* OFF-TRACE vertex: complement membership makes both slots vacuous *)
    assert (Hcomp : ring_complement (ring_of_chain (d0 :: c)) (dtip x))
      by (apply (off_trace_vertex_complement E d0 c x
                   Hnfv Hp Hedges HWD Hx Hoff)).
    apply (walk_corner_threshold_range (ring_of_chain (d0 :: c)) (dtip x)
             (dtip x) (dtip x)
             (ddir (twin x)) (ddir (fstep (darts_of E) x))
             Hnoh_r); [ | | | exact Hcne ].
    + exact (off_ring_vertex_clearance _ (dtip x) (dtip x) (dtip x) Hcomp).
    + rewrite point_diff_self. apply vzero_not_in_sector.
    + rewrite point_diff_self. apply vzero_not_in_sector.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  The per-dart ride cap.                                                  *)
(* -------------------------------------------------------------------------- *)

Theorem walk_ride_at :
  forall (D : list Dart) (r : Ring) (x : Dart) (rho1 rho2 : R),
    ring_taut r ->
    pairwise_no_proper_cross_twin_aware D ->
    no_foreign_vertex_twin_aware D ->
    In x D ->
    (forall f, In f (ring_edges r) -> In f D) ->
    py (fst x) <> py (snd x) ->
    0 < rho1 -> 0 < rho2 -> rho1 + rho2 < 1 ->
    exists cap : R, 0 < cap /\
      forall delta, 0 < delta < cap ->
        connected_in_complement_cont r
          (point_at (dbase x) (corner_sample_out (ddir x) rho1 delta))
          (point_at (dtip x)
             (corner_sample_in (point_diff (dbase x) (dtip x)) rho2 delta)).
Proof.
  intros D r x rho1 rho2 Htaut Hpw Hnfv Hx Hsub Hnh Hr1 Hr2 Hsum.
  pose proof (vy_ddir x) as Hvy.
  pose proof (Rabs_pos (vx (ddir x))) as Habs.
  set (A := Rabs (vx (ddir x)) + 1).
  assert (HAeq : A = Rabs (vx (ddir x)) + 1) by reflexivity.
  assert (HA : 0 < A) by lra.
  assert (Hvyne : vy (ddir x) <> 0)
    by (rewrite Hvy; unfold dtip, dbase; lra).
  set (K := vx (ddir x) * vx (ddir x) + vy (ddir x) * vy (ddir x)).
  assert (HKeq : K = vx (ddir x) * vx (ddir x) + vy (ddir x) * vy (ddir x))
    by reflexivity.
  assert (HK : 0 < K) by nra.
  destruct (Rtotal_order (vy (ddir x)) 0) as [Hdesc | [Heq0 | Hasc]];
    [ | exact (False_ind _ (Hvyne Heq0)) | ].
  - (* DESCENDING: west corridor *)
    set (span := - vy (ddir x)).
    assert (Hspeq : span = - vy (ddir x)) by reflexivity.
    assert (Hspan : 0 < span) by lra.
    set (ylo := py (dtip x) + rho2 * span / 2).
    set (yhi := py (dbase x) - rho1 * span / 2).
    assert (Hyloeq : ylo = py (dtip x) + rho2 * span / 2) by reflexivity.
    assert (Hyhieq : yhi = py (dbase x) - rho1 * span / 2) by reflexivity.
    assert (Hspanhyp : (py (fst x) < ylo /\ yhi < py (snd x)) \/
                       (py (snd x) < ylo /\ yhi < py (fst x))).
    { right.
      change (snd x) with (dtip x). change (fst x) with (dbase x).
      split; nra. }
    assert (Hyle : ylo <= yhi) by nra.
    destruct (walk_dart_corridor_clear D r x ylo yhi
                Htaut Hpw Hnfv Hx Hsub Hspanhyp Hyle)
      as [delta0 [Hd0 Hclear]].
    set (cap := Rmin (delta0 * span / K)
                     (Rmin (rho1 * span / (2 * A)) (rho2 * span / (2 * A)))).
    assert (Hcap : 0 < cap).
    { apply Rmin_glb_lt.
      - apply Rdiv_lt_0_compat; [ nra | exact HK ].
      - apply Rmin_glb_lt; apply Rdiv_lt_0_compat; nra. }
    exists cap. split; [ exact Hcap | ].
    intros delta [Hdpos Hdlt].
    pose proof (Rmin_l (delta0 * span / K)
                  (Rmin (rho1 * span / (2 * A)) (rho2 * span / (2 * A)))) as Hc1.
    pose proof (Rmin_r (delta0 * span / K)
                  (Rmin (rho1 * span / (2 * A)) (rho2 * span / (2 * A)))) as Hc23.
    pose proof (Rmin_l (rho1 * span / (2 * A)) (rho2 * span / (2 * A))) as Hc2.
    pose proof (Rmin_r (rho1 * span / (2 * A)) (rho2 * span / (2 * A))) as Hc3.
    fold cap in Hc1, Hc23.
    assert (Hdc1 : delta < delta0 * span / K) by lra.
    assert (Hdc2 : delta < rho1 * span / (2 * A)) by lra.
    assert (Hdc3 : delta < rho2 * span / (2 * A)) by lra.
    assert (Hbnd1 : Rabs (delta * vx (ddir x)) < rho1 * span / 2).
    { rewrite Rabs_mult. rewrite (Rabs_right delta); [ | lra ].
      apply Rlt_trans with (delta * A).
      - apply Rmult_lt_compat_l; lra.
      - pose proof (Rmult_lt_compat_r A delta (rho1 * span / (2 * A))
                      HA Hdc2) as HdA.
        replace (rho1 * span / (2 * A) * A) with (rho1 * span / 2) in HdA
          by (field; lra).
        exact HdA. }
    assert (Hbnd2 : Rabs (delta * vx (ddir x)) < rho2 * span / 2).
    { rewrite Rabs_mult. rewrite (Rabs_right delta); [ | lra ].
      apply Rlt_trans with (delta * A).
      - apply Rmult_lt_compat_l; lra.
      - pose proof (Rmult_lt_compat_r A delta (rho2 * span / (2 * A))
                      HA Hdc3) as HdA.
        replace (rho2 * span / (2 * A) * A) with (rho2 * span / 2) in HdA
          by (field; lra).
        exact HdA. }
    apply Rabs_def2 in Hbnd1. apply Rabs_def2 in Hbnd2.
    apply (along_dart_ride_west r x rho1 rho2 delta Hdesc).
    + (* the two bridge heights are ordered *)
      nra.
    + intros y [Hy1 Hy2].
      change (delta * (vx (ddir x) * vx (ddir x) + vy (ddir x) * vy (ddir x))
                / (- vy (ddir x)))
        with (delta * K / span).
      apply (Hclear (delta * K / span)).
      * split.
        -- unfold Rdiv. apply Rmult_lt_0_compat; [ nra | ].
           apply Rinv_0_lt_compat. exact Hspan.
        -- apply (Rmult_lt_reg_r span); [ exact Hspan | ].
           unfold Rdiv. rewrite Rmult_assoc, Rinv_l; [ | lra ].
           rewrite Rmult_1_r.
           pose proof (Rmult_lt_compat_r K delta (delta0 * span / K)
                         HK Hdc1) as Hm.
           replace (delta0 * span / K * K) with (delta0 * span) in Hm
             by (field; lra).
           lra.
      * split.
        -- apply Rle_trans with
             (py (dtip x) + (- rho2 * vy (ddir x) - delta * vx (ddir x)));
             [ | exact Hy1 ].
           nra.
        -- apply Rle_trans with
             (py (dbase x) + (rho1 * vy (ddir x) - delta * vx (ddir x)));
             [ exact Hy2 | ].
           nra.
  - (* ASCENDING: east corridor *)
    set (span := vy (ddir x)).
    assert (Hspeq : span = vy (ddir x)) by reflexivity.
    assert (Hspan : 0 < span) by lra.
    set (ylo := py (dbase x) + rho1 * span / 2).
    set (yhi := py (dtip x) - rho2 * span / 2).
    assert (Hyloeq : ylo = py (dbase x) + rho1 * span / 2) by reflexivity.
    assert (Hyhieq : yhi = py (dtip x) - rho2 * span / 2) by reflexivity.
    assert (Hspanhyp : (py (fst x) < ylo /\ yhi < py (snd x)) \/
                       (py (snd x) < ylo /\ yhi < py (fst x))).
    { left.
      change (snd x) with (dtip x). change (fst x) with (dbase x).
      split; nra. }
    assert (Hyle : ylo <= yhi) by nra.
    destruct (walk_dart_corridor_east_clear D r x ylo yhi
                Htaut Hpw Hnfv Hx Hsub Hspanhyp Hyle)
      as [delta0 [Hd0 Hclear]].
    set (cap := Rmin (delta0 * span / K)
                     (Rmin (rho1 * span / (2 * A)) (rho2 * span / (2 * A)))).
    assert (Hcap : 0 < cap).
    { apply Rmin_glb_lt.
      - apply Rdiv_lt_0_compat; [ nra | exact HK ].
      - apply Rmin_glb_lt; apply Rdiv_lt_0_compat; nra. }
    exists cap. split; [ exact Hcap | ].
    intros delta [Hdpos Hdlt].
    pose proof (Rmin_l (delta0 * span / K)
                  (Rmin (rho1 * span / (2 * A)) (rho2 * span / (2 * A)))) as Hc1.
    pose proof (Rmin_r (delta0 * span / K)
                  (Rmin (rho1 * span / (2 * A)) (rho2 * span / (2 * A)))) as Hc23.
    pose proof (Rmin_l (rho1 * span / (2 * A)) (rho2 * span / (2 * A))) as Hc2.
    pose proof (Rmin_r (rho1 * span / (2 * A)) (rho2 * span / (2 * A))) as Hc3.
    fold cap in Hc1, Hc23.
    assert (Hdc1 : delta < delta0 * span / K) by lra.
    assert (Hdc2 : delta < rho1 * span / (2 * A)) by lra.
    assert (Hdc3 : delta < rho2 * span / (2 * A)) by lra.
    assert (Hbnd1 : Rabs (delta * vx (ddir x)) < rho1 * span / 2).
    { rewrite Rabs_mult. rewrite (Rabs_right delta); [ | lra ].
      apply Rlt_trans with (delta * A).
      - apply Rmult_lt_compat_l; lra.
      - pose proof (Rmult_lt_compat_r A delta (rho1 * span / (2 * A))
                      HA Hdc2) as HdA.
        replace (rho1 * span / (2 * A) * A) with (rho1 * span / 2) in HdA
          by (field; lra).
        exact HdA. }
    assert (Hbnd2 : Rabs (delta * vx (ddir x)) < rho2 * span / 2).
    { rewrite Rabs_mult. rewrite (Rabs_right delta); [ | lra ].
      apply Rlt_trans with (delta * A).
      - apply Rmult_lt_compat_l; lra.
      - pose proof (Rmult_lt_compat_r A delta (rho2 * span / (2 * A))
                      HA Hdc3) as HdA.
        replace (rho2 * span / (2 * A) * A) with (rho2 * span / 2) in HdA
          by (field; lra).
        exact HdA. }
    apply Rabs_def2 in Hbnd1. apply Rabs_def2 in Hbnd2.
    apply (along_dart_ride_east r x rho1 rho2 delta Hasc).
    + nra.
    + intros y [Hy1 Hy2].
      change (delta * (vx (ddir x) * vx (ddir x) + vy (ddir x) * vy (ddir x))
                / vy (ddir x))
        with (delta * K / span).
      apply (Hclear (delta * K / span)).
      * split.
        -- unfold Rdiv. apply Rmult_lt_0_compat; [ nra | ].
           apply Rinv_0_lt_compat. exact Hspan.
        -- apply (Rmult_lt_reg_r span); [ exact Hspan | ].
           unfold Rdiv. rewrite Rmult_assoc, Rinv_l; [ | lra ].
           rewrite Rmult_1_r.
           pose proof (Rmult_lt_compat_r K delta (delta0 * span / K)
                         HK Hdc1) as Hm.
           replace (delta0 * span / K * K) with (delta0 * span) in Hm
             by (field; lra).
           lra.
      * split.
        -- apply Rle_trans with
             (py (dbase x) + (rho1 * vy (ddir x) - delta * vx (ddir x)));
             [ | exact Hy1 ].
           nra.
        -- apply Rle_trans with
             (py (dtip x) + (- rho2 * vy (ddir x) - delta * vx (ddir x)));
             [ exact Hy2 | ].
           nra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Axiom audit.  Per-step kit; allowlist axioms only.                          *)
(* -------------------------------------------------------------------------- *)

(* Used by: the E-2 residual discharge (`walk_small_offset_connectivity`'s
   headline) -- `range_family_fold` collapses the per-vertex corners of
   the orbit chain, `cap_family_fold` its per-dart ride caps, and the
   two `_at` theorems supply the per-index data at `x := iter (fstep
   (darts_of E)) i d`. *)

Print Assumptions range_family_fold.
Print Assumptions cap_family_fold.
Print Assumptions walk_corner_range_at.
Print Assumptions walk_ride_at.

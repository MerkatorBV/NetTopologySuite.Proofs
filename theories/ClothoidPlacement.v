(* ============================================================================
   NetTopologySuite.Proofs.ClothoidPlacement
   ----------------------------------------------------------------------------
   Curvature of a placed clothoid. A placement is o + M p with M a 2x2
   linear map. For a curve with derivatives v, a the placed curve has
   derivatives M v, M a (placed_deriv), so

     curvature = det M * cross(v, a) / |M v|^3      (signed_curv_lin)

   For a similarity M = lam * R (lam > 0, R a rotation) this is
   kappa / lam (signed_curv_similarity, cloth_similarity_curvature).
   For a reflection-similarity it is - kappa / lam
   (signed_curv_reflection). For a general linear M it is not kappa / lam
   and not the constructive t / A^2 (cloth_placed_curvature).

   GEOS #1566 (libgeos/geos PR, head 6eb13d1): Clothoid::curvatureOf
   returns direction * t / A^2 when the frame is not a similarity. The
   oracle case "sheared placement" (u = (2, 0), v = (1/2, 1), A = 5,
   t0 = 1, t1 = 12) gives 1/25 = 0.04 at the start. Here the placed
   start curvature lies in (0.00985, 0.00986)
   (geos_shear_curvature_enclosure), so it is not 1/25
   (geos_shear_curvature_ne_naive). The GEOS test table lists
   0.009855916895262518 for that case; that value is inside the
   enclosure, and it is not proved here beyond the enclosure.
   The rational side of the enclosure is the Q twin geos_shear_q_check:
   Taylor bounds of cos and sin at 1/50, the squared speed, and four
   comparisons, decided by vm_compute and transported to R with Qreals.

   Parked: an error bound for far-field Fresnel quadrature (GEOS uses
   fixed 0.5-wide 16-point Gauss-Legendre panels past the series
   window). LipInt is a dyadic Riemann integral; there is no
   Gauss-Legendre remainder theorem in the corpus, so no bound is
   stated.

   claimId: none new. No claim row. No WITNESS.
   3-axiom host. No Admitted / Axiom / Parameter.
   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted; human review pending.
   ========================================================================== *)

From Stdlib Require Import Reals Lra QArith Qreals Ranalysis1.
From NTS.Proofs Require Import Distance SheetHenClothoidCore ClothoidNorm2
  SignedCurvature SheetHenClothoidFrames SheetHenClothoidBounds ClothoidTraversal.
Local Open Scope R_scope.

Record Lin2 : Type := mkLin2 { l11 : R; l12 : R; l21 : R; l22 : R }.

Definition lin_ap (M : Lin2) (p : Point) : Point :=
  mkPoint (l11 M * px p + l12 M * py p) (l21 M * px p + l22 M * py p).

Definition lin_det (M : Lin2) : R := l11 M * l22 M - l12 M * l21 M.

Definition placed (o : Point) (M : Lin2) (p : Point) : Point :=
  mkPoint (px o + px (lin_ap M p)) (py o + py (lin_ap M p)).

Lemma curv_cross_lin : forall M v a,
  curv_cross (lin_ap M v) (lin_ap M a) = lin_det M * curv_cross v a.
Proof. intros. unfold curv_cross, lin_ap, lin_det. cbn. ring. Qed.

Lemma signed_curv_lin : forall M v a,
  signed_curv (lin_ap M v) (lin_ap M a)
    = lin_det M * curv_cross v a /
      (sqrt (curv_speed2 (lin_ap M v)) * sqrt (curv_speed2 (lin_ap M v))
       * sqrt (curv_speed2 (lin_ap M v))).
Proof. intros. unfold signed_curv. rewrite curv_cross_lin. reflexivity. Qed.

Definition lin_sim (lam co si : R) : Lin2 :=
  mkLin2 (lam * co) (- (lam * si)) (lam * si) (lam * co).

Definition lin_refl (lam co si : R) : Lin2 :=
  mkLin2 (lam * co) (lam * si) (lam * si) (- (lam * co)).

Lemma curv_speed2_nonneg : forall v, 0 <= curv_speed2 v.
Proof. intro v. unfold curv_speed2. nra. Qed.

Lemma lin_sim_speed2 : forall lam co si v, co * co + si * si = 1 ->
  curv_speed2 (lin_ap (lin_sim lam co si) v) = lam * lam * curv_speed2 v.
Proof.
  intros lam co si v H. unfold curv_speed2, lin_ap, lin_sim. cbn.
  replace ((lam * co * px v + - (lam * si) * py v) * (lam * co * px v + - (lam * si) * py v) +
           (lam * si * px v + lam * co * py v) * (lam * si * px v + lam * co * py v))
    with (lam * lam * (co * co + si * si) * (px v * px v + py v * py v)) by ring.
  rewrite H. ring.
Qed.

Lemma lin_refl_speed2 : forall lam co si v, co * co + si * si = 1 ->
  curv_speed2 (lin_ap (lin_refl lam co si) v) = lam * lam * curv_speed2 v.
Proof.
  intros lam co si v H. unfold curv_speed2, lin_ap, lin_refl. cbn.
  replace ((lam * co * px v + lam * si * py v) * (lam * co * px v + lam * si * py v) +
           (lam * si * px v + - (lam * co) * py v) * (lam * si * px v + - (lam * co) * py v))
    with (lam * lam * (co * co + si * si) * (px v * px v + py v * py v)) by ring.
  rewrite H. ring.
Qed.

Lemma lin_sim_det : forall lam co si, co * co + si * si = 1 ->
  lin_det (lin_sim lam co si) = lam * lam.
Proof.
  intros lam co si H. unfold lin_det, lin_sim. cbn.
  replace (lam * co * (lam * co) - - (lam * si) * (lam * si))
    with (lam * lam * (co * co + si * si)) by ring.
  rewrite H. ring.
Qed.

Lemma lin_refl_det : forall lam co si, co * co + si * si = 1 ->
  lin_det (lin_refl lam co si) = - (lam * lam).
Proof.
  intros lam co si H. unfold lin_det, lin_refl. cbn.
  replace (lam * co * - (lam * co) - lam * si * (lam * si))
    with (- (lam * lam * (co * co + si * si))) by ring.
  rewrite H. ring.
Qed.

Lemma sqrt_scale_sq : forall lam S, 0 < lam -> 0 <= S ->
  sqrt (lam * lam * S) = lam * sqrt S.
Proof.
  intros lam S Hl HS.
  rewrite sqrt_mult_alt by nra.
  rewrite sqrt_square by lra. reflexivity.
Qed.

Theorem signed_curv_similarity : forall lam co si v a,
  0 < lam -> co * co + si * si = 1 -> curv_speed2 v <> 0 ->
  signed_curv (lin_ap (lin_sim lam co si) v) (lin_ap (lin_sim lam co si) a)
    = signed_curv v a / lam.
Proof.
  intros lam co si v a Hl Hu Hv.
  rewrite signed_curv_lin, lin_sim_det, lin_sim_speed2 by exact Hu.
  rewrite sqrt_scale_sq by (try exact Hl; apply curv_speed2_nonneg).
  assert (Hs : 0 < sqrt (curv_speed2 v)).
  { apply sqrt_lt_R0. pose proof (curv_speed2_nonneg v). lra. }
  unfold signed_curv. field. split; lra.
Qed.

Theorem signed_curv_reflection : forall lam co si v a,
  0 < lam -> co * co + si * si = 1 -> curv_speed2 v <> 0 ->
  signed_curv (lin_ap (lin_refl lam co si) v) (lin_ap (lin_refl lam co si) a)
    = - (signed_curv v a / lam).
Proof.
  intros lam co si v a Hl Hu Hv.
  rewrite signed_curv_lin, lin_refl_det, lin_refl_speed2 by exact Hu.
  rewrite sqrt_scale_sq by (try exact Hl; apply curv_speed2_nonneg).
  assert (Hs : 0 < sqrt (curv_speed2 v)).
  { apply sqrt_lt_R0. pose proof (curv_speed2_nonneg v). lra. }
  unfold signed_curv. field. split; lra.
Qed.

Lemma placed_deriv : forall o M (f : R -> Point) t v,
  derivable_pt_lim (fun u => px (f u)) t (px v) ->
  derivable_pt_lim (fun u => py (f u)) t (py v) ->
  derivable_pt_lim (fun u => px (placed o M (f u))) t (px (lin_ap M v)) /\
  derivable_pt_lim (fun u => py (placed o M (f u))) t (py (lin_ap M v)).
Proof.
  intros o M f t v Hx Hy.
  assert (Gen : forall k a b, derivable_pt_lim
            (fun u => k + (a * px (f u) + b * py (f u))) t (a * px v + b * py v)).
  { intros k a b.
    apply derivable_pt_lim_ext with
      (f := plus_fct (fct_cte k)
              (plus_fct (mult_real_fct a (fun u => px (f u)))
                        (mult_real_fct b (fun u => py (f u))))).
    - intro u. reflexivity.
    - replace (a * px v + b * py v) with (0 + (a * px v + b * py v)) by ring.
      apply derivable_pt_lim_plus; [apply derivable_pt_lim_const|].
      apply derivable_pt_lim_plus; apply derivable_pt_lim_scal; assumption. }
  split; [apply (Gen (px o) (l11 M) (l12 M)) | apply (Gen (py o) (l21 M) (l22 M))].
Qed.

Lemma cloth_arc_cross : forall c s, cloth_h2 c <> 0 -> cloth_d c <> 0 ->
  curv_cross (cloth_arc_v c s) (cloth_arc_a c s)
    = cloth_tk0 c + (cloth_tk1 c - cloth_tk0 c) * s / cloth_tlen c.
Proof.
  intros c s Hh Hd.
  rewrite <- cloth_kappa_traversal_linear by exact Hd.
  rewrite <- cloth_arc_signed_curv by exact Hh.
  unfold signed_curv. rewrite cloth_arc_speed2, sqrt_1 by exact Hh. field.
Qed.

(* Any linear placement: curvature det M * kappa / |M v|^3. *)
Theorem cloth_placed_curvature : forall c o M s,
  cloth_A c <> 0 -> cloth_h2 c <> 0 -> cloth_d c <> 0 ->
  let V := lin_ap M (cloth_arc_v c s) in
  let Acc := lin_ap M (cloth_arc_a c s) in
  derivable_pt_lim (fun u => px (placed o M (cloth_arc c u))) s (px V) /\
  derivable_pt_lim (fun u => py (placed o M (cloth_arc c u))) s (py V) /\
  derivable_pt_lim (fun u => px (lin_ap M (cloth_arc_v c u))) s (px Acc) /\
  derivable_pt_lim (fun u => py (lin_ap M (cloth_arc_v c u))) s (py Acc) /\
  signed_curv V Acc
    = lin_det M * (cloth_tk0 c + (cloth_tk1 c - cloth_tk0 c) * s / cloth_tlen c)
      / (sqrt (curv_speed2 V) * sqrt (curv_speed2 V) * sqrt (curv_speed2 V)).
Proof.
  intros c o M s HA Hh Hd V Acc.
  destruct (cloth_arc_unit_speed_linear_curvature c s HA Hh Hd)
    as (Hx & Hy & Hvx & Hvy & _ & _).
  destruct (placed_deriv o M (cloth_arc c) s (cloth_arc_v c s) Hx Hy) as [P1 P2].
  destruct (placed_deriv (mkPoint 0 0) M (cloth_arc_v c) s (cloth_arc_a c s) Hvx Hvy)
    as [P3 P4].
  split; [exact P1|]. split; [exact P2|].
  split.
  - eapply derivable_pt_lim_ext; [|exact P3].
    intro u. unfold placed. cbn. ring.
  - split.
    + eapply derivable_pt_lim_ext; [|exact P4].
      intro u. unfold placed. cbn. ring.
    + unfold V, Acc. rewrite signed_curv_lin, cloth_arc_cross by assumption.
      reflexivity.
Qed.

(* Similarity placement: curvature kappa / lambda. *)
Theorem cloth_similarity_curvature : forall c o lam co si s,
  cloth_A c <> 0 -> cloth_h2 c <> 0 -> cloth_d c <> 0 ->
  0 < lam -> co * co + si * si = 1 ->
  signed_curv (lin_ap (lin_sim lam co si) (cloth_arc_v c s))
              (lin_ap (lin_sim lam co si) (cloth_arc_a c s))
    = (cloth_tk0 c + (cloth_tk1 c - cloth_tk0 c) * s / cloth_tlen c) / lam /\
  derivable_pt_lim (fun u => px (placed o (lin_sim lam co si) (cloth_arc c u))) s
    (px (lin_ap (lin_sim lam co si) (cloth_arc_v c s))) /\
  derivable_pt_lim (fun u => py (placed o (lin_sim lam co si) (cloth_arc c u))) s
    (py (lin_ap (lin_sim lam co si) (cloth_arc_v c s))).
Proof.
  intros c o lam co si s HA Hh Hd Hl Hu.
  destruct (cloth_placed_curvature c o (lin_sim lam co si) s HA Hh Hd)
    as (P1 & P2 & _ & _ & _).
  split; [| split; assumption].
  rewrite signed_curv_similarity by (try assumption; rewrite cloth_arc_speed2 by exact Hh; lra).
  rewrite cloth_arc_signed_curv by exact Hh.
  rewrite cloth_kappa_traversal_linear by exact Hd. reflexivity.
Qed.

(* GEOS #1566 oracle case "sheared placement": u = (2, 0), v = (1/2, 1),
   A = 5, t0 = 1, t1 = 12. *)
Definition geos_shear : Lin2 := mkLin2 2 (1 / 2) 0 1.

Definition geos_shear_egg : ClothoidEgg :=
  mk_cloth (place_east (mkPoint 3 4)) 5 1 12 None None.

Lemma geos_shear_det : lin_det geos_shear = 2.
Proof. unfold lin_det, geos_shear. cbn. ring. Qed.

Lemma geos_shear_sigma : cloth_sigma geos_shear_egg = 1.
Proof.
  unfold cloth_sigma, cloth_cross, geos_shear_egg, mk_cloth. cbn [cloth_place].
  rewrite east_cross. destruct (Rle_dec 0 1); [reflexivity | lra].
Qed.

Lemma geos_shear_frame :
  cloth_cos0 geos_shear_egg = 1 /\ cloth_sin0 geos_shear_egg = 0.
Proof.
  unfold cloth_cos0, cloth_sin0, cloth_hypot, cloth_h2, geos_shear_egg, mk_cloth.
  cbn [cloth_place aff_ref1 place_east px py].
  rewrite east_h2, sqrt_1. split; field.
Qed.

Lemma geos_shear_d : cloth_d geos_shear_egg = 11.
Proof. unfold cloth_d, geos_shear_egg, mk_cloth. cbn. ring. Qed.

Lemma geos_shear_dir : cloth_dir geos_shear_egg = 1.
Proof.
  unfold cloth_dir. rewrite geos_shear_d. destruct (Rle_dec 0 11); [reflexivity | lra].
Qed.

(* GEOS curvatureOf returns direction * t / A^2 for a non-similarity
   frame: 1 / 25 at the start. That is cloth_tk0 of the constructive egg. *)
Lemma geos_shear_naive_value : cloth_tk0 geos_shear_egg = 1 / 25.
Proof.
  unfold cloth_tk0, cloth_kappa. rewrite geos_shear_dir, geos_shear_sigma.
  unfold geos_shear_egg, mk_cloth. cbn [cloth_sd cloth_A]. field.
Qed.

Lemma geos_shear_tangent0 :
  cloth_vx geos_shear_egg (cloth_station geos_shear_egg 0) = cos (1 / 50) /\
  cloth_vy geos_shear_egg (cloth_station geos_shear_egg 0) = sin (1 / 50) /\
  cloth_kappa geos_shear_egg (cloth_station geos_shear_egg 0) = 1 / 25.
Proof.
  destruct geos_shear_frame as [Hc Hs].
  assert (Est : cloth_station geos_shear_egg 0 = 1).
  { unfold cloth_station. rewrite geos_shear_dir.
    unfold geos_shear_egg, mk_cloth. cbn. ring. }
  assert (Ep : cloth_psi geos_shear_egg 1 = 1 / 50).
  { unfold cloth_psi. rewrite geos_shear_sigma.
    unfold geos_shear_egg, mk_cloth. cbn [cloth_A]. field. }
  rewrite Est. unfold cloth_vx, cloth_vy. rewrite Hc, Hs, Ep.
  split; [ring|]. split; [ring|].
  unfold cloth_kappa. rewrite geos_shear_sigma.
  unfold geos_shear_egg, mk_cloth. cbn [cloth_A]. field.
Qed.

(* The Q twin: Taylor enclosures of cos and sin at 1/50, the squared speed
   N of the sheared tangent, and the four rational comparisons the real
   proof needs. Computed by vm_compute below, not written down. *)
Definition q_z : Q := 1 # 50.
Definition q_clo : Q := 1 - q_z * q_z * (1 # 2).
Definition q_chi : Q := 1 - q_z * q_z * (1 # 2) + q_z * q_z * q_z * q_z * (1 # 24).
Definition q_slo : Q := q_z - q_z * q_z * q_z * (1 # 6).
Definition q_shi : Q := q_z.
Definition q_N (a b : Q) : Q := (2 * a + b * (1 # 2)) * (2 * a + b * (1 # 2)) + b * b.
Definition q_rl : Q := 20096 # 10000.
Definition q_rh : Q := 20098 # 10000.
Definition q_kl : Q := 985 # 100000.
Definition q_kh : Q := 986 # 100000.
Definition q_cr : Q := 2 # 25.

Definition geos_shear_q_check : bool :=
  Qle_bool (q_rl * q_rl) (q_N q_clo q_slo) &&
  Qle_bool (q_N q_chi q_shi) (q_rh * q_rh) &&
  negb (Qle_bool (q_kh * (q_N q_clo q_slo * q_rl)) q_cr) &&
  negb (Qle_bool q_cr (q_kl * (q_N q_chi q_shi * q_rh))).

Lemma geos_shear_q_check_true : geos_shear_q_check = true.
Proof. vm_compute. reflexivity. Qed.

Lemma geos_q2r_lit : forall n d, Q2R (n # d) = IZR n / IZR (Zpos d).
Proof. intros. reflexivity. Qed.

Lemma geos_q2r_qN : forall a b,
  Q2R (q_N a b) = (2 * Q2R a + Q2R b * (1 / 2)) * (2 * Q2R a + Q2R b * (1 / 2))
                  + Q2R b * Q2R b.
Proof.
  intros a b. unfold q_N.
  rewrite !Q2R_plus, !Q2R_mult, Q2R_plus, !Q2R_mult.
  replace (Q2R 2) with 2 by (unfold Q2R; cbn; field).
  replace (Q2R (1 # 2)) with (1 / 2) by (unfold Q2R; cbn; field).
  reflexivity.
Qed.

Lemma geos_q2r_bounds :
  Q2R q_clo = 1 - (1 / 50) * (1 / 50) / 2 /\
  Q2R q_chi = 1 - (1 / 50) * (1 / 50) / 2
              + (1 / 50) * (1 / 50) * (1 / 50) * (1 / 50) / 24 /\
  Q2R q_slo = 1 / 50 - (1 / 50) * (1 / 50) * (1 / 50) / 6 /\
  Q2R q_shi = 1 / 50.
Proof.
  unfold q_clo, q_chi, q_slo, q_shi, q_z.
  rewrite !Q2R_minus, !Q2R_plus, !Q2R_minus, !Q2R_mult.
  unfold Q2R; cbn [Qnum Qden]. repeat split; field.
Qed.

Lemma geos_q_facts :
  Q2R q_rl * Q2R q_rl <= Q2R (q_N q_clo q_slo) /\
  Q2R (q_N q_chi q_shi) <= Q2R q_rh * Q2R q_rh /\
  Q2R q_cr < Q2R q_kh * (Q2R (q_N q_clo q_slo) * Q2R q_rl) /\
  Q2R q_kl * (Q2R (q_N q_chi q_shi) * Q2R q_rh) < Q2R q_cr.
Proof.
  pose proof geos_shear_q_check_true as H. unfold geos_shear_q_check in H.
  apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3].
  apply andb_prop in H as [H1 H2].
  apply Qle_bool_imp_le in H1. apply Qle_bool_imp_le in H2.
  apply negb_true_iff in H3. apply negb_true_iff in H4.
  assert (H3' : (q_cr < q_kh * (q_N q_clo q_slo * q_rl))%Q).
  { apply Qnot_le_lt. intro Hc. apply Qle_bool_iff in Hc. congruence. }
  assert (H4' : (q_kl * (q_N q_chi q_shi * q_rh) < q_cr)%Q).
  { apply Qnot_le_lt. intro Hc. apply Qle_bool_iff in Hc. congruence. }
  rewrite <- !Q2R_mult.
  split; [apply Qle_Rle; exact H1|].
  split; [apply Qle_Rle; exact H2|].
  split; apply Qlt_Rlt; assumption.
Qed.

Lemma geos_N_mono : forall a b c s,
  0 <= a -> a <= c -> 0 <= b -> b <= s ->
  (2 * a + b * (1 / 2)) * (2 * a + b * (1 / 2)) + b * b
    <= (2 * c + s * (1 / 2)) * (2 * c + s * (1 / 2)) + s * s.
Proof.
  intros a b c s Ha Hac Hb Hbs.
  assert (H1 : 0 <= 2 * a + b * (1 / 2)) by lra.
  assert (H2 : 2 * a + b * (1 / 2) <= 2 * c + s * (1 / 2)) by lra.
  apply Rplus_le_compat; apply Rmult_le_compat; lra.
Qed.

Theorem geos_shear_curvature_enclosure :
  let V := lin_ap geos_shear (cloth_arc_v geos_shear_egg 0) in
  let Acc := lin_ap geos_shear (cloth_arc_a geos_shear_egg 0) in
  985 / 100000 < signed_curv V Acc < 986 / 100000.
Proof.
  intros V Acc.
  assert (HA : cloth_A geos_shear_egg <> 0)
    by (unfold geos_shear_egg, mk_cloth; cbn; lra).
  assert (Hh : cloth_h2 geos_shear_egg <> 0).
  { unfold cloth_h2, geos_shear_egg, mk_cloth. cbn [cloth_place].
    rewrite east_h2. lra. }
  assert (Hd : cloth_d geos_shear_egg <> 0) by (rewrite geos_shear_d; lra).
  destruct geos_shear_tangent0 as (Ex & Ey & _).
  set (c := cos (1 / 50)). set (s := sin (1 / 50)).
  assert (Hz : - PI / 2 <= 1 / 50 <= PI / 2) by (pose proof PI2_bounds; lra).
  assert (Hc1 : 1 - (1 / 50) * (1 / 50) / 2 <= c)
    by (apply cos_ge_quad; lra).
  assert (Hc2 : c <= 1 - (1 / 50) * (1 / 50) / 2
                     + (1 / 50) * (1 / 50) * (1 / 50) * (1 / 50) / 24)
    by (apply cos_le_quart; lra).
  assert (Hs1 : 1 / 50 - (1 / 50) * (1 / 50) * (1 / 50) / 6 <= s)
    by (apply sin_ge_cubic; pose proof PI2_bounds; lra).
  assert (Hs2 : s <= 1 / 50) by (apply sin_le_arg; lra).
  destruct geos_q2r_bounds as (Qc1 & Qc2 & Qs1 & Qs2).
  destruct geos_q_facts as (F1 & F2 & F3 & F4).
  rewrite !geos_q2r_qN in F1, F2, F3, F4.
  rewrite Qc1, Qs1 in F1, F3. rewrite Qc2, Qs2 in F2, F4.
  set (N := curv_speed2 V).
  assert (EN : N = (2 * c + s * (1 / 2)) * (2 * c + s * (1 / 2)) + s * s).
  { unfold N, V, curv_speed2, lin_ap, cloth_arc_v, geos_shear.
    rewrite geos_shear_dir, Ex, Ey. cbn. fold c s. ring. }
  set (Nlo := (2 * (1 - 1 / 50 * (1 / 50) / 2) +
               (1 / 50 - 1 / 50 * (1 / 50) * (1 / 50) / 6) * (1 / 2)) *
              (2 * (1 - 1 / 50 * (1 / 50) / 2) +
               (1 / 50 - 1 / 50 * (1 / 50) * (1 / 50) / 6) * (1 / 2)) +
              (1 / 50 - 1 / 50 * (1 / 50) * (1 / 50) / 6) *
              (1 / 50 - 1 / 50 * (1 / 50) * (1 / 50) / 6)) in *.
  set (Nhi := (2 * (1 - 1 / 50 * (1 / 50) / 2 +
                    1 / 50 * (1 / 50) * (1 / 50) * (1 / 50) / 24) + 1 / 50 * (1 / 2)) *
              (2 * (1 - 1 / 50 * (1 / 50) / 2 +
                    1 / 50 * (1 / 50) * (1 / 50) * (1 / 50) / 24) + 1 / 50 * (1 / 2)) +
              1 / 50 * (1 / 50)) in *.
  assert (HNlo : Nlo <= N).
  { rewrite EN. unfold Nlo. apply geos_N_mono; lra. }
  assert (HNhi : N <= Nhi).
  { rewrite EN. unfold Nhi. apply geos_N_mono; lra. }
  set (rl := Q2R q_rl) in *. set (rh := Q2R q_rh) in *.
  assert (G1 : rl * rl <= Nlo) by (unfold Nlo in *; lra).
  assert (G2 : Nhi <= rh * rh) by (unfold Nhi in *; lra).
  assert (Erl : rl = 20096 / 10000) by reflexivity.
  assert (Erh : rh = 20098 / 10000) by reflexivity.
  set (r := sqrt N).
  assert (HN0 : 0 <= N) by apply curv_speed2_nonneg.
  assert (Hrl0 : 0 <= rl * rl) by (rewrite Erl; lra).
  assert (Hrl : rl <= r).
  { rewrite <- (sqrt_square rl) by (rewrite Erl; lra).
    apply sqrt_le_1; [exact Hrl0 | exact HN0 | lra]. }
  assert (Hrh : r <= rh).
  { rewrite <- (sqrt_square rh) by (rewrite Erh; lra).
    apply sqrt_le_1; [exact HN0 | rewrite Erh; lra | lra]. }
  assert (Er : r * r = N) by (apply sqrt_sqrt; exact HN0).
  set (X := r * r * r).
  assert (EX : X = N * r) by (unfold X; rewrite Er; reflexivity).
  assert (HX1 : Nlo * rl <= X).
  { rewrite EX. apply Rmult_le_compat; [lra | rewrite Erl; lra | lra | lra]. }
  assert (HX2 : X <= Nhi * rh).
  { assert (0 <= rl) by (rewrite Erl; lra).
    rewrite EX. apply Rmult_le_compat; lra. }
  assert (Hcr : Q2R q_cr = 2 / 25) by reflexivity.
  assert (Hkl : Q2R q_kl = 985 / 100000) by reflexivity.
  assert (Hkh : Q2R q_kh = 986 / 100000) by reflexivity.
  rewrite Hcr, Hkl, Hkh in *.
  assert (G3 : 2 / 25 < 986 / 100000 * (Nlo * rl)) by (unfold Nlo in *; lra).
  assert (G4 : 985 / 100000 * (Nhi * rh) < 2 / 25) by (unfold Nhi in *; lra).
  assert (Ek : signed_curv V Acc = 2 / 25 / X).
  { unfold V, Acc. rewrite signed_curv_lin, geos_shear_det.
    rewrite cloth_arc_cross by assumption.
    rewrite geos_shear_naive_value. fold V N r X.
    unfold Rdiv. ring. }
  rewrite Ek.
  assert (HXp : 0 < X).
  { apply Rlt_le_trans with (Nlo * rl); [|exact HX1].
    apply Rmult_lt_0_compat; [|rewrite Erl; lra].
    apply Rlt_le_trans with (rl * rl); [rewrite Erl; lra | exact G1]. }
  assert (EXX : 2 / 25 / X * X = 2 / 25) by (field; lra).
  split.
  - apply (Rmult_lt_reg_r X); [exact HXp|]. rewrite EXX.
    apply Rle_lt_trans with (985 / 100000 * (Nhi * rh)); [|exact G4].
    apply Rmult_le_compat_l; [lra | exact HX2].
  - apply (Rmult_lt_reg_r X); [exact HXp|]. rewrite EXX.
    apply Rlt_le_trans with (986 / 100000 * (Nlo * rl)); [exact G3|].
    apply Rmult_le_compat_l; [lra | exact HX1].
Qed.

Theorem geos_shear_curvature_ne_naive :
  signed_curv (lin_ap geos_shear (cloth_arc_v geos_shear_egg 0))
              (lin_ap geos_shear (cloth_arc_a geos_shear_egg 0))
    <> cloth_tk0 geos_shear_egg.
Proof.
  rewrite geos_shear_naive_value.
  pose proof geos_shear_curvature_enclosure as H. cbv zeta in H. lra.
Qed.

Print Assumptions curv_cross_lin.
Print Assumptions signed_curv_lin.
Print Assumptions curv_speed2_nonneg.
Print Assumptions lin_sim_speed2.
Print Assumptions lin_refl_speed2.
Print Assumptions lin_sim_det.
Print Assumptions lin_refl_det.
Print Assumptions sqrt_scale_sq.
Print Assumptions signed_curv_similarity.
Print Assumptions signed_curv_reflection.
Print Assumptions placed_deriv.
Print Assumptions cloth_arc_cross.
Print Assumptions cloth_placed_curvature.
Print Assumptions cloth_similarity_curvature.
Print Assumptions geos_shear_det.
Print Assumptions geos_shear_sigma.
Print Assumptions geos_shear_frame.
Print Assumptions geos_shear_d.
Print Assumptions geos_shear_dir.
Print Assumptions geos_shear_naive_value.
Print Assumptions geos_shear_tangent0.
Print Assumptions geos_shear_q_check_true.
Print Assumptions geos_q2r_lit.
Print Assumptions geos_q2r_qN.
Print Assumptions geos_q2r_bounds.
Print Assumptions geos_q_facts.
Print Assumptions geos_N_mono.
Print Assumptions geos_shear_curvature_enclosure.
Print Assumptions geos_shear_curvature_ne_naive.

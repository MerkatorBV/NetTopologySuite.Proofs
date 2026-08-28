(* ============================================================================
   NetTopologySuite.Proofs.ArcRectifiable
   ----------------------------------------------------------------------------
   Issue #508 (M-LEN-ZOO) arc rung: r·θ IS the metric length — the circular
   arc satisfies the corpus-canonical curve-length spec of CurveLength.v.

   Before this file, `ArcLength.arc_length r θ := r*θ` was a definition with
   sandwich companions (`chord_le_arc_length`); the reopened triage row
   (M-LEN-CS / M-LEN-CC) records exactly that gap.  Here the circle
   parameterization  t ↦ O + r·(cos t, sin t)  is proven RECTIFIABLE with

       is_curve_length (circle_param O r) a b (r * (b - a)),

   i.e. r·θ (θ = b − a) is the least upper bound of the inscribed-polyline
   lengths.  Upper half: every chain edge is a chord `2r·|sin(gap/2)| ≤ r·gap`
   (half-angle identity + the 3-axiom Taylor bound `sin_le_x`), telescoping
   to r·(b−a).  Least half: the uniform n-partition polyline is inscribed and
   `n · 2r·sin(θ/(2n)) ≥ rθ − rθ·h²/24` (lower Taylor envelope
   `pre_sin_bound`), and an archimedean choice of n forces any upper bound M
   up to rθ — epsilon-free, no limits library.  The squeeze is factored as
   `chord_envelope_lower`, generic in the envelope constant c: any curve
   whose chords dominate `2c·|sin(gap/2)|` has every inscribed-length upper
   bound ≥ c·(b−a).  The circle meets the envelope with equality (c = r);
   EllipseLength.v meets it with c = Rmin rx ry.  Alongside it lives the
   generic first-order-tight primitive engine `curve_length_of_primitive`:
   a chord modulus F that is ε-tight on fine gaps has F b − F a as THE
   metric length — the conditional-tier headline of every integral lane
   (ellipse at F = elliptic-E, clothoid at F = id).

   Deliberately NOT this file: the 3-point (start/mid/end) CircularArc model
   bridge — its sweep angle lives in the atan2 / `angle_between` 4-axiom
   exception lane (see ArcChordLength.v); connecting the two models is the
   next rung.  This file stays on the explicit parameterization and is
   3-axiom.

   No `Admitted`, no `Axiom`, no `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra Lia List Rtrigo_alt ZArith.
From NTS.Proofs Require Import Distance CurveLength ArcLength.
Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* The explicit circle parameterization.                                      *)
(* -------------------------------------------------------------------------- *)

Definition circle_pt (O : Point) (r t : R) : Point :=
  mkPoint (px O + r * cos t) (py O + r * sin t).

Definition circle_param (O : Point) (r : R) : Curve := circle_pt O r.

(* -------------------------------------------------------------------------- *)
(* The chord of a parameter gap, exactly: 2r·|sin(gap/2)|.                    *)
(* -------------------------------------------------------------------------- *)

Lemma circle_chord_dist : forall (O : Point) r s t,
  0 <= r ->
  dist (circle_pt O r s) (circle_pt O r t)
  = 2 * r * Rabs (sin ((t - s) / 2)).
Proof.
  intros O r s t Hr.
  unfold dist.
  assert (Hds : dist_sq (circle_pt O r s) (circle_pt O r t)
                = Rsqr (2 * r * sin ((t - s) / 2))).
  { unfold dist_sq, circle_pt; simpl.
    assert (Hcm : cos (t - s) = cos t * cos s + sin t * sin s)
      by apply cos_minus.
    assert (Hs2s : sin s * sin s + cos s * cos s = 1).
    { pose proof (sin2_cos2 s) as H; unfold Rsqr in H; lra. }
    assert (Hs2t : sin t * sin t + cos t * cos t = 1).
    { pose proof (sin2_cos2 t) as H; unfold Rsqr in H; lra. }
    assert (Hhalf : cos (t - s)
                    = 1 - 2 * sin ((t - s) / 2) * sin ((t - s) / 2)).
    { replace (t - s) with (2 * ((t - s) / 2)) at 1 by field.
      apply cos_2a_sin. }
    unfold Rsqr.
    replace ((px O + r * cos s - (px O + r * cos t))
             * (px O + r * cos s - (px O + r * cos t))
             + (py O + r * sin s - (py O + r * sin t))
             * (py O + r * sin s - (py O + r * sin t)))
      with (r * r * ((sin s * sin s + cos s * cos s)
                     + (sin t * sin t + cos t * cos t)
                     - 2 * (cos t * cos s + sin t * sin s))) by ring.
    rewrite Hs2s, Hs2t, <- Hcm, Hhalf. ring. }
  rewrite Hds, sqrt_Rsqr_abs, Rabs_mult.
  rewrite (Rabs_right (2 * r)) by lra.
  reflexivity.
Qed.

(* PI >= 2 without Classical_Prop.classic (Stdlib's PI2_1 drags it in):
   1 = sin (PI/2) <= PI/2 by the 3-axiom Taylor bound sin_le_x. *)
Lemma PI_ge_2 : 2 <= PI.
Proof.
  pose proof PI_RGT_0 as Hpi.
  assert (H : 1 <= PI / 2).
  { rewrite <- sin_PI2. apply sin_le_x. lra. }
  lra.
Qed.

(* |sin x| <= x for 0 <= x: 3-axiom via ArcLength.sin_le_x on [0, PI] and
   SIN_bound + PI >= 2 past PI. *)
Lemma Rabs_sin_le : forall x, 0 <= x -> Rabs (sin x) <= x.
Proof.
  intros x Hx.
  destruct (Rle_dec 0 (sin x)) as [Hs | Hs].
  - rewrite Rabs_right by lra. apply sin_le_x; exact Hx.
  - rewrite Rabs_left by lra.
    destruct (Rle_dec x PI) as [Hxpi | Hxpi].
    + exfalso. pose proof (sin_ge_0 x Hx Hxpi). lra.
    + pose proof (SIN_bound x) as [Hlo _].
      pose proof PI_ge_2. lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Upper half: chords never beat r·gap, and inscribed polylines telescope.    *)
(* -------------------------------------------------------------------------- *)

Lemma circle_edge_le : forall (O : Point) r s t,
  0 <= r -> s <= t ->
  dist (circle_param O r s) (circle_param O r t) <= r * (t - s).
Proof.
  intros O r s t Hr Hst.
  unfold circle_param.
  rewrite circle_chord_dist by exact Hr.
  assert (H2 : 0 <= (t - s) / 2) by lra.
  pose proof (Rabs_sin_le ((t - s) / 2) H2) as Habs.
  assert (Hm : 2 * r * Rabs (sin ((t - s) / 2)) <= 2 * r * ((t - s) / 2)).
  { apply Rmult_le_compat_l; lra. }
  lra.
Qed.

Lemma circle_polyline_le : forall (O : Point) r ts t b,
  0 <= r -> chain t ts b ->
  polyline_len (circle_param O r) t (ts ++ [b]) <= r * (b - t).
Proof.
  intros O r ts t b Hr Hch.
  replace (r * (b - t)) with (r * b - r * t) by ring.
  apply (polyline_le_of_chord_modulus (circle_param O r) (fun x => r * x)
           t b ts t).
  - intros s u Hts Hsu Hub. cbv beta.
    pose proof (circle_edge_le O r s u Hr Hsu). lra.
  - lra.
  - exact Hch.
Qed.

(* -------------------------------------------------------------------------- *)
(* Least half plumbing: uniform partitions and their exact polyline value.    *)
(* -------------------------------------------------------------------------- *)

Fixpoint uniform_tail (t0 h : R) (m : nat) : list R :=
  match m with
  | O => []
  | S k => (t0 + h) :: uniform_tail (t0 + h) h k
  end.

Lemma uniform_tail_snoc : forall m t0 h,
  uniform_tail t0 h (S m) = uniform_tail t0 h m ++ [t0 + INR (S m) * h].
Proof.
  induction m as [|k IH]; intros t0 h.
  - cbn [uniform_tail app]. do 2 f_equal. rewrite S_INR. simpl. ring.
  - change (uniform_tail t0 h (S (S k)))
      with ((t0 + h) :: uniform_tail (t0 + h) h (S k)).
    rewrite IH.
    change (uniform_tail t0 h (S k))
      with ((t0 + h) :: uniform_tail (t0 + h) h k).
    cbn [app].
    replace (t0 + h + INR (S k) * h) with (t0 + INR (S (S k)) * h)
      by (rewrite !S_INR; ring).
    reflexivity.
Qed.

Lemma uniform_tail_chain : forall m t0 h hi,
  0 <= h -> t0 + INR m * h <= hi ->
  chain t0 (uniform_tail t0 h m) hi.
Proof.
  induction m as [|k IH]; intros t0 h hi Hh Hle; cbn [uniform_tail chain].
  - simpl in Hle. lra.
  - rewrite S_INR in Hle. split.
    + lra.
    + apply IH; [exact Hh | lra].
Qed.

Lemma uniform_polyline_val : forall (g : Curve) m t0 h e,
  (forall t, dist (g t) (g (t + h)) = e) ->
  polyline_len g t0 (uniform_tail t0 h m) = INR m * e.
Proof.
  intros g m; induction m as [|k IH]; intros t0 h e He;
    cbn [uniform_tail polyline_len].
  - simpl. ring.
  - rewrite He, (IH (t0 + h) h e He), S_INR. ring.
Qed.

Lemma uniform_polyline_ge : forall (g : Curve) m t0 h c,
  (forall t, c <= dist (g t) (g (t + h))) ->
  INR m * c <= polyline_len g t0 (uniform_tail t0 h m).
Proof.
  intros g m; induction m as [|k IH]; intros t0 h c Hc;
    cbn [uniform_tail polyline_len].
  - simpl. lra.
  - pose proof (Hc t0) as He0.
    specialize (IH (t0 + h) h c Hc).
    rewrite S_INR. lra.
Qed.

(* The lower Taylor envelope: sin x >= x - x^3/6 on [0, 4]. *)
Lemma sin_approx_1 : forall a : R, sin_approx a 1 = a - a ^ 3 / 6.
Proof.
  intros a.
  unfold sin_approx, sin_term.
  simpl.
  unfold Rdiv.
  field.
Qed.

Lemma sin_lower_taylor : forall x, 0 <= x -> x <= 4 -> x - x ^ 3 / 6 <= sin x.
Proof.
  intros x Hx H4.
  destruct (pre_sin_bound x 0 Hx H4) as [Hlb _].
  change (2 * 0 + 1)%nat with 1%nat in Hlb.
  rewrite sin_approx_1 in Hlb.
  exact Hlb.
Qed.

(* Archimedean choice of a partition count. *)
Lemma exists_nat_gt : forall x : R, exists n : nat, x < INR n.
Proof.
  intro x.
  destruct (archimed x) as [H1 _].
  destruct (Z.le_gt_cases (up x) 0) as [Hz | Hz].
  - exists 1%nat. simpl.
    pose proof (IZR_le _ _ Hz). lra.
  - exists (Z.to_nat (up x)).
    rewrite INR_IZR_INZ, Z2Nat.id by lia.
    lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* The generic least-half squeeze: any curve whose chords dominate the        *)
(* half-angle envelope 2c·|sin(gap/2)| forces every inscribed-length upper    *)
(* bound up to c·(b−a).  The uniform n-partition polyline is                  *)
(* ≥ c·(b−a) − c·(b−a)·h²/24 (lower Taylor envelope), and an archimedean      *)
(* choice of n does the rest — epsilon-free, no limits library.  The circle   *)
(* meets the envelope with equality; the ellipse meets it with c = Rmin.      *)
(*                                                                            *)
(* The envelope premise is deliberately `forall s t`, NOT `s <= t`: the       *)
(* |sin| makes it direction-free, and the squeeze instantiates it at t and    *)
(* t + h.  A future instance that "helpfully" adds s <= t to its chord        *)
(* lemma will not fit — keep the instance direction-free too.                 *)
(* -------------------------------------------------------------------------- *)

Lemma chord_envelope_lower : forall (g : Curve) (c a b M : R),
  0 <= c -> a <= b ->
  (forall s t, 2 * c * Rabs (sin ((t - s) / 2)) <= dist (g s) (g t)) ->
  is_upper_bound (inscribed_len g a b) M ->
  c * (b - a) <= M.
Proof.
  intros g c a b M Hc Hab Henv Hub.
  destruct (Rle_dec (c * (b - a)) M) as [Hok | Hbad]. { exact Hok. }
  exfalso.
  set (th := b - a).
  assert (Hth : 0 <= th) by (unfold th; lra).
  set (dlt := c * th - M).
  assert (Hdlt : 0 < dlt) by (unfold dlt, th; lra).
  (* M bounds the chord, so M >= 0 and c*th = dlt + M > 0 *)
  assert (Hchord := Hub _ (inscribed_chord g a b Hab)).
  pose proof (dist_nonneg (g a) (g b)) as Hd0.
  assert (Hcthpos : 0 < c * th) by (unfold dlt in Hdlt; lra).
  (* choose n beyond both demands *)
  destruct (exists_nat_gt (Rmax th (th * (c * th) / (24 * dlt))))
    as [n Hn].
  assert (Hnth : th < INR n)
    by (eapply Rle_lt_trans; [apply Rmax_l | exact Hn]).
  assert (Hnq : th * (c * th) / (24 * dlt) < INR n)
    by (eapply Rle_lt_trans; [apply Rmax_r | exact Hn]).
  assert (Hnpos : 0 < INR n) by lra.
  set (h := th / INR n).
  assert (Hh0 : 0 <= h) by (unfold h; apply Rle_mult_inv_pos; lra).
  assert (Hnh : INR n * h = th) by (unfold h; field; lra).
  assert (Hh1 : h < 1).
  { apply Rmult_lt_reg_l with (INR n); [lra |].
    rewrite Hnh, Rmult_1_r; lra. }
  (* n = S k, so the uniform partition has a nonempty snoc form *)
  destruct n as [|k]. { simpl in Hnpos. lra. }
  assert (Hb : b = a + INR (S k) * h) by (rewrite Hnh; unfold th; ring).
  (* per-edge lower bound from the envelope + the lower Taylor envelope *)
  assert (Hsin0 : 0 <= sin (h / 2)).
  { apply sin_ge_0; [lra |]. pose proof PI_ge_2. lra. }
  assert (Htay : h / 2 - (h / 2) ^ 3 / 6 <= sin (h / 2))
    by (apply sin_lower_taylor; lra).
  assert (He : forall t, c * h - c * h ^ 3 / 24 <= dist (g t) (g (t + h))).
  { intro t.
    pose proof (Henv t (t + h)) as Hcg.
    replace ((t + h - t) / 2) with (h / 2) in Hcg by field.
    rewrite Rabs_right in Hcg by lra.
    eapply Rle_trans; [| exact Hcg].
    assert (Hstep : 2 * c * (h / 2 - (h / 2) ^ 3 / 6)
                    <= 2 * c * sin (h / 2))
      by (apply Rmult_le_compat_l; lra).
    eapply Rle_trans; [| exact Hstep].
    right. field. }
  (* the uniform partition is inscribed and its value is bounded below *)
  set (ln := polyline_len g a (uniform_tail a h (S k))).
  assert (Hln_lb : INR (S k) * (c * h - c * h ^ 3 / 24) <= ln).
  { unfold ln. apply uniform_polyline_ge. exact He. }
  assert (Hins : inscribed_len g a b ln).
  { exists (uniform_tail a h k). split.
    - apply uniform_tail_chain; [exact Hh0 |].
      rewrite Hb, !S_INR.
      assert (0 <= h) by exact Hh0. nra.
    - unfold ln. rewrite uniform_tail_snoc, <- Hb. reflexivity. }
  specialize (Hub _ Hins).
  assert (Hval : c * th - c * th * h ^ 2 / 24 <= ln).
  { eapply Rle_trans; [| exact Hln_lb].
    right. rewrite <- Hnh. field. }
  (* the error term is < dlt *)
  assert (Herr : c * th * h ^ 2 / 24 < dlt).
  { assert (H24 : th * (c * th) < 24 * dlt * INR (S k)).
    { apply Rmult_lt_reg_r with (/ (24 * dlt)).
      { apply Rinv_0_lt_compat. lra. }
      replace (24 * dlt * INR (S k) * / (24 * dlt)) with (INR (S k))
        by (field; lra).
      unfold Rdiv in Hnq. exact Hnq. }
    assert (Hrh : c * th * h < 24 * dlt).
    { apply Rmult_lt_reg_l with (INR (S k)); [lra |].
      replace (INR (S k) * (c * th * h))
        with (th * (c * th)) by (rewrite <- Hnh; ring).
      lra. }
    assert (Hsq : c * th * h ^ 2 <= c * th * h).
    { replace (c * th * h ^ 2) with ((c * th * h) * h) by ring.
      replace (c * th * h) with ((c * th * h) * 1) at 2 by ring.
      apply Rmult_le_compat_l; [| lra].
      assert (0 <= c * th) by lra. nra. }
    lra. }
  unfold dlt in Herr. lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* The generic first-order-tight PRIMITIVE engine: if F is a chord modulus    *)
(* on [a, b] (every chord within the window ≤ its F-increment) that is        *)
(* first-order TIGHT on fine gaps within the window (the increment exceeds    *)
(* the chord by at most ε·gap), then F b − F a IS the metric length — the     *)
(* conditional-tier headline every integral lane instantiates: the ellipse    *)
(* at F = elliptic-E, the clothoid at F = id.  Upper half: the chord-modulus  *)
(* telescoping.  Least half: uniform partitions, instantiating the            *)
(* tightness at ε = slack/(b−a+1) where slack is the lub gap being refuted    *)
(* — epsilon-free of limits machinery.                                        *)
(*                                                                            *)
(* Both premises are deliberately WINDOWED to [a, b]: a curve can meet the    *)
(* contract on every compact window without meeting it globally (the Euler    *)
(* spiral wraps toward its asymptotic point, so no global δ exists for it),   *)
(* and the proof only ever samples chords inside the window.                  *)
(* -------------------------------------------------------------------------- *)

Lemma uniform_lower_primitive : forall (g : Curve) (F : R -> R) (a b h eps : R),
  0 <= h ->
  (forall t, a <= t -> t + h <= b ->
     F (t + h) - F t - dist (g t) (g (t + h)) <= eps * h) ->
  forall m t0,
    a <= t0 -> t0 + INR m * h <= b ->
    F (t0 + INR m * h) - F t0 - eps * (INR m * h)
    <= polyline_len g t0 (uniform_tail t0 h m).
Proof.
  intros g F a b h eps Hh Hedge.
  induction m as [|k IH]; intros t0 Hat0 Htop; cbn [uniform_tail polyline_len].
  - simpl. replace (t0 + 0 * h) with t0 by ring. lra.
  - rewrite S_INR in Htop.
    replace (t0 + (INR k + 1) * h) with (t0 + h + INR k * h) in Htop by ring.
    assert (Hk0 : 0 <= INR k * h) by (pose proof (pos_INR k); nra).
    assert (Hth : t0 + h <= b) by lra.
    assert (Ha1 : a <= t0 + h) by lra.
    specialize (IH (t0 + h) Ha1 Htop).
    rewrite S_INR.
    pose proof (Hedge t0 Hat0 Hth) as He0.
    replace (t0 + h + INR k * h) with (t0 + (INR k + 1) * h) in IH by ring.
    lra.
Qed.

Theorem curve_length_of_primitive : forall (g : Curve) (F : R -> R) a b,
  (forall s t, a <= s -> s <= t -> t <= b -> dist (g s) (g t) <= F t - F s) ->
  (forall eps, 0 < eps ->
     exists delta, 0 < delta /\
       forall s t, a <= s -> s <= t -> t <= b -> t - s < delta ->
         F t - F s - dist (g s) (g t) <= eps * (t - s)) ->
  a <= b -> is_curve_length g a b (F b - F a).
Proof.
  intros g F a b Hchord Happrox Hab. split.
  - intros l (ts & Hch & Hl). subst l.
    apply (polyline_le_of_chord_modulus g F a b ts a).
    + exact Hchord.
    + lra.
    + exact Hch.
  - intros M HM.
    destruct (Rle_dec (F b - F a) M) as [Hok | Hbad]. { exact Hok. }
    exfalso.
    set (dlt := F b - F a - M).
    assert (Hdlt : 0 < dlt) by (unfold dlt; lra).
    set (eps := dlt / (b - a + 1)).
    assert (Heps : 0 < eps).
    { unfold eps. apply Rdiv_lt_0_compat; lra. }
    destruct (Happrox eps Heps) as (delta & Hdpos & Hd).
    destruct (exists_nat_gt ((b - a) / delta)) as [n0 Hn0].
    assert (Hnpos : 0 < INR (S n0))
      by (rewrite S_INR; pose proof (pos_INR n0); lra).
    assert (Hngt : (b - a) / delta < INR (S n0))
      by (rewrite S_INR; lra).
    set (h := (b - a) / INR (S n0)).
    assert (Hh0 : 0 <= h) by (unfold h; apply Rle_mult_inv_pos; lra).
    assert (Hnh : INR (S n0) * h = b - a) by (unfold h; field; lra).
    assert (Hhd : h < delta).
    { apply Rmult_lt_reg_l with (INR (S n0)); [lra |].
      rewrite Hnh.
      pose proof (Rmult_lt_compat_l delta _ _ Hdpos Hngt) as Hm.
      replace (delta * ((b - a) / delta)) with (b - a) in Hm
        by (field; lra).
      lra. }
    assert (Hedge : forall t, a <= t -> t + h <= b ->
      F (t + h) - F t - dist (g t) (g (t + h)) <= eps * h).
    { intros t Hat Htb.
      assert (Ht := Hd t (t + h)).
      replace (t + h - t) with h in Ht by ring.
      apply Ht; lra. }
    assert (Hins : inscribed_len g a b
                     (polyline_len g a (uniform_tail a h n0 ++ [b]))).
    { exists (uniform_tail a h n0). split; [| reflexivity].
      apply uniform_tail_chain; [exact Hh0 |].
      assert (Hb' : b = a + INR (S n0) * h) by (rewrite Hnh; ring).
      rewrite Hb', S_INR.
      pose proof (pos_INR n0). nra. }
    specialize (HM _ Hins).
    assert (Hb : b = a + INR (S n0) * h) by (rewrite Hnh; ring).
    assert (Hval : F b - F a - eps * (b - a)
                   <= polyline_len g a (uniform_tail a h n0 ++ [b])).
    { replace (uniform_tail a h n0 ++ [b])
        with (uniform_tail a h (S n0))
        by (rewrite Hb; apply uniform_tail_snoc).
      rewrite <- Hnh.
      rewrite Hb at 1.
      apply (uniform_lower_primitive g F a b h eps Hh0 Hedge (S n0) a).
      - lra.
      - rewrite Hnh. lra. }
    assert (Hlt : eps * (b - a) < dlt).
    { assert (H1 : eps * (b - a + 1) = dlt) by (unfold eps; field; lra).
      nra. }
    unfold dlt in Hlt. lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Headline: r·θ satisfies the CurveLength spec.                              *)
(* -------------------------------------------------------------------------- *)

Theorem arc_r_theta_is_curve_length : forall (O : Point) r a b,
  0 <= r -> a <= b ->
  is_curve_length (circle_param O r) a b (r * (b - a)).
Proof.
  intros O r a b Hr Hab.
  split.
  - (* upper bound: telescoping chord bounds *)
    intros l (ts & Hch & Hl). subst l.
    pose proof (circle_polyline_le O r ts a b Hr Hch). lra.
  - (* least upper bound: circle chords MEET the half-angle envelope *)
    intros M HM.
    apply (chord_envelope_lower (circle_param O r) r a b M Hr Hab); [| exact HM].
    intros s t. unfold circle_param.
    rewrite circle_chord_dist by exact Hr.
    apply Rle_refl.
Qed.

Corollary arc_rectifiable : forall (O : Point) r a b,
  0 <= r -> a <= b -> rectifiable (circle_param O r) a b.
Proof.
  intros O r a b Hr Hab.
  exists (r * (b - a)).
  apply arc_r_theta_is_curve_length; assumption.
Qed.

(* r·θ agrees with ArcLength.arc_length on the shared regime. *)
Corollary arc_length_meets_spec : forall (O : Point) r a b,
  0 <= r -> a <= b ->
  is_curve_length (circle_param O r) a b (arc_length r (b - a)).
Proof.
  intros O r a b Hr Hab.
  unfold arc_length.
  apply arc_r_theta_is_curve_length; assumption.
Qed.

Print Assumptions arc_r_theta_is_curve_length.

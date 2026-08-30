(* ============================================================================
   NetTopologySuite.Proofs.SpeedIntegral
   ----------------------------------------------------------------------------
   Issue #561 / claimId 508-c: the generic layer that turns "F is an
   integral of the speed" into the two windowed premises of
   ArcRectifiable.curve_length_of_primitive, once.

   Spike decision (Route 1, in-corpus).  Heine–Cantor is NOT imported —
   stdlib compactness on a closed interval typically pulls extra classical
   structure past the 3-axiom allowlist, so uniform continuity of the speed
   is a hypothesis of the pack (constant and Lipschitz speeds discharge it
   by an explicit δ).  Coquelicot / RInt (Route 2) is gated off this letter:
   host-lane metric files stay 3-axiom; the clothoid-halley-coq bridge
   remains the 508-e discharge carrier if that letter wants RInt facts.
   508-d / 508-e instantiate the pack; they do not remint it.

   The pack, over a window [a, b]:

     uniformly_continuous_on σ
     increment_squeezed F σ     (F increment is squeezed by any pair of
                                 σ-bounds — the integral remainder, MVT or
                                 Riemann, without constructing � (F increment is squeezed by any pair of
                                 σ-bounds — the integral remainder, MVT or
                                 Riemann, without constructing ∫)
     chord_rate_tight g σ       (on fine gaps the chord is within ε of
                                 σ(left)·gap — first-order speed)

   Tagged partitions (chain + one tag per gap, Riemann sum Σ σ(tag)·Δt)
   are first-class.  Chord modulus is the triangle inequality along a
   fine left-tagged uniform partition: dist ≤ polyline ≤ Riemann + ε·span
   and Riemann ≤ F-increment + ε·span, so dist ≤ F b − F a after ε → 0.
   Tightness is local: UC + increment sandwich + chord-rate, no further
   partition.  Then curve_length_of_primitive gives

     speed_integral_premises g σ F a b
       → is_curve_length g a b (F b − F a).

   Witness: the circle speed is constantly r, F(t) = r·t, and the
   existing envelope headline

     is_curve_length (circle_param O r) a b (r·(b−a))

   is re-derived through the pack (same statement, second proof path).
   curve_length_unique pins the two paths to the same L.

   No CurveSegment growth, no ADR-0004 remint, no new 64-a r·θ.
   No `Admitted`, no `Axiom`, no `Parameter`.  3-axiom.

   WITNESS topic: metric · claimId: 508-c · witness: 508-c-speed-integral
   macro: metric
   lane: proofs
   issue: #561 / #508

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.6
   ========================================================================== *)

From Stdlib Require Import Reals Lra Lia List.
From NTS.Proofs Require Import Distance CurveLength ArcRectifiable.
Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* Premise pack.                                                              *)
(* -------------------------------------------------------------------------- *)

Definition uniformly_continuous_on (f : R -> R) (a b : R) : Prop :=
  forall eps, 0 < eps ->
    exists d, 0 < d /\
      forall s t, a <= s -> s <= t -> t <= b -> t - s < d ->
        Rabs (f t - f s) < eps.

(* F increment is squeezed by any pair of bounds that trap σ on [s, t].
   Consumers get this from derivable_pt_lim + MVT, or from a Riemann
   characterization — the pack does not pick. *)
Definition increment_squeezed (F σ : R -> R) (a b : R) : Prop :=
  forall s t lo hi,
    a <= s -> s <= t -> t <= b ->
    (forall u, s <= u -> u <= t -> lo <= σ u <= hi) ->
    lo * (t - s) <= F t - F s <= hi * (t - s).

(* On fine gaps the chord realizes the left-endpoint speed to first order. *)
Definition chord_rate_tight (g : Curve) (σ : R -> R) (a b : R) : Prop :=
  forall eps, 0 < eps ->
    exists d, 0 < d /\
      forall s t, a <= s -> s <= t -> t <= b -> t - s < d ->
        Rabs (dist (g s) (g t) - σ s * (t - s)) <= eps * (t - s).

Definition speed_integral_premises
    (g : Curve) (σ F : R -> R) (a b : R) : Prop :=
  a <= b /\
  (forall t, a <= t -> t <= b -> 0 <= σ t) /\
  uniformly_continuous_on σ a b /\
  increment_squeezed F σ a b /\
  chord_rate_tight g σ a b.

(* -------------------------------------------------------------------------- *)
(* Tagged partitions over the existing chain type.                            *)
(* -------------------------------------------------------------------------- *)

Fixpoint tags_in_chain (lo : R) (ts : list R) (hi : R)
    (tags : list R) : Prop :=
  match ts with
  | [] =>
      match tags with
      | [c] => lo <= c /\ c <= hi
      | _ => False
      end
  | u :: us =>
      match tags with
      | c :: cs => lo <= c /\ c <= u /\ tags_in_chain u us hi cs
      | [] => False
      end
  end.

Definition tagged_chain (lo : R) (ts : list R) (hi : R)
    (tags : list R) : Prop :=
  chain lo ts hi /\ tags_in_chain lo ts hi tags.

Fixpoint riemann_sum (σ : R -> R) (lo : R) (ts : list R) (hi : R)
    (tags : list R) : R :=
  match ts with
  | [] =>
      match tags with
      | [c] => σ c * (hi - lo)
      | _ => 0
      end
  | u :: us =>
      match tags with
      | c :: cs => σ c * (u - lo) + riemann_sum σ u us hi cs
      | [] => 0
      end
  end.

(* Left-endpoint tags: one tag per gap, including the final gap to hi. *)
Fixpoint left_tags (t0 : R) (ts : list R) : list R :=
  match ts with
  | [] => [t0]
  | u :: us => t0 :: left_tags u us
  end.

Lemma left_tags_in_chain : forall ts lo hi,
  chain lo ts hi ->
  tags_in_chain lo ts hi (left_tags lo ts).
Proof.
  induction ts as [|u us IH]; intros lo hi Hch; cbn [left_tags tags_in_chain].
  - cbn [chain] in Hch. split; lra.
  - cbn [chain] in Hch. destruct Hch as [Hlu Hrest].
    split; [lra | split; [exact Hlu | apply IH; exact Hrest]].
Qed.

Lemma left_tags_tagged : forall ts lo hi,
  chain lo ts hi ->
  tagged_chain lo ts hi (left_tags lo ts).
Proof.
  intros ts lo hi Hch. split; [exact Hch | apply left_tags_in_chain; exact Hch].
Qed.

(* -------------------------------------------------------------------------- *)
(* Triangle: the single chord never beats a refinement.                       *)
(* -------------------------------------------------------------------------- *)

Lemma dist_le_polyline : forall (g : Curve) ts t b,
  dist (g t) (g b) <= polyline_len g t (ts ++ [b]).
Proof.
  intros g ts; induction ts as [|u us IH]; intros t b.
  - cbn [app polyline_len]. lra.
  - cbn [app polyline_len].
    pose proof (dist_triangle (g t) (g u) (g b)) as Htr.
    pose proof (IH u b) as Hind.
    lra.
Qed.

Lemma dist_le_uniform_polyline : forall (g : Curve) m t0 h,
  dist (g t0) (g (t0 + INR m * h))
  <= polyline_len g t0 (uniform_tail t0 h m).
Proof.
  intros g m; induction m as [|k IH]; intros t0 h;
    cbn [uniform_tail polyline_len].
  - simpl.
    replace (t0 + 0 * h) with t0 by ring.
    rewrite dist_refl. lra.
  - pose proof (IH (t0 + h) h) as Hind.
    rewrite S_INR.
    replace (t0 + (INR k + 1) * h) with (t0 + h + INR k * h) by ring.
    pose proof (dist_triangle (g t0) (g (t0 + h))
                              (g (t0 + h + INR k * h))) as Htr.
    lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Local increment / chord-rate on a fine gap.                                *)
(* -------------------------------------------------------------------------- *)

Lemma sigma_near_left :
  forall σ a b eps d s t,
    (forall s' t', a <= s' -> s' <= t' -> t' <= b -> t' - s' < d ->
       Rabs (σ t' - σ s') < eps) ->
    a <= s -> s <= t -> t <= b -> t - s < d ->
    forall u, s <= u -> u <= t ->
      σ s - eps <= σ u <= σ s + eps.
Proof.
  intros σ a b eps d s t Huc Has Hst Htb Hdt u Hus Hut.
  assert (Habs : Rabs (σ u - σ s) < eps).
  { apply Huc; lra. }
  apply Rabs_def2 in Habs. lra.
Qed.

Lemma rabs_le_both : forall x e, Rabs x <= e -> - e <= x <= e.
Proof.
  intros x e H.
  destruct (Rle_dec 0 x) as [Hx | Hx].
  - rewrite Rabs_right in H by lra. lra.
  - rewrite Rabs_left in H by lra. lra.
Qed.

Lemma increment_near_left :
  forall F σ a b eps d s t,
    increment_squeezed F σ a b ->
    (forall s' t', a <= s' -> s' <= t' -> t' <= b -> t' - s' < d ->
       Rabs (σ t' - σ s') < eps) ->
    a <= s -> s <= t -> t <= b -> t - s < d ->
    (σ s - eps) * (t - s) <= F t - F s <= (σ s + eps) * (t - s).
Proof.
  intros F σ a b eps d s t Hsq Huc Has Hst Htb Hdt.
  apply (Hsq s t (σ s - eps) (σ s + eps) Has Hst Htb).
  intros u Hus Hut.
  apply (sigma_near_left σ a b eps d s t Huc Has Hst Htb Hdt u Hus Hut).
Qed.

(* -------------------------------------------------------------------------- *)
(* Fine left-tagged uniform mesh: Riemann ↔ F and polyline ↔ Riemann.         *)
(* -------------------------------------------------------------------------- *)

Lemma uniform_riemann_le_F :
  forall (σ F : R -> R) a b eps d h,
    increment_squeezed F σ a b ->
    (forall s t, a <= s -> s <= t -> t <= b -> t - s < d ->
       Rabs (σ t - σ s) < eps) ->
    0 < h -> h < d ->
    forall m t0,
      a <= t0 -> t0 + INR m * h <= b ->
      riemann_sum σ t0 (uniform_tail t0 h m) (t0 + INR m * h)
                  (left_tags t0 (uniform_tail t0 h m))
      <= F (t0 + INR m * h) - F t0 + eps * (INR m * h).
Proof.
  intros σ F a b eps d h Hsq Huc Hh0 Hhd.
  induction m as [|k IH]; intros t0 Hat0 Htop.
  - cbn [uniform_tail left_tags riemann_sum].
    change (INR 0) with 0.
    replace (t0 + 0 * h) with t0 by ring.
    replace (σ t0 * (t0 - t0)) with 0 by ring.
    replace (F t0 - F t0 + eps * (0 * h)) with 0 by ring.
    apply Rle_refl.
  - cbn [uniform_tail left_tags riemann_sum].
    rewrite S_INR in Htop.
    replace (t0 + (INR k + 1) * h) with (t0 + h + INR k * h) in Htop by ring.
    assert (Hth : t0 + h <= b).
    { pose proof (pos_INR k). nra. }
    assert (Ha1 : a <= t0 + h) by lra.
    specialize (IH (t0 + h) Ha1 Htop).
    rewrite S_INR.
    replace (t0 + (INR k + 1) * h) with (t0 + h + INR k * h) by ring.
    assert (Hgap : t0 + h - t0 < d) by (replace (t0 + h - t0) with h by ring; exact Hhd).
    pose proof (increment_near_left F σ a b eps d t0 (t0 + h)
                  Hsq Huc Hat0 ltac:(lra) Hth Hgap) as Hinc.
    replace (t0 + h - t0) with h in Hinc by ring.
    lra.
Qed.

Lemma uniform_polyline_le_riemann :
  forall (g : Curve) (σ : R -> R) a b eps d h,
    (forall s t, a <= s -> s <= t -> t <= b -> t - s < d ->
       Rabs (dist (g s) (g t) - σ s * (t - s)) <= eps * (t - s)) ->
    0 < h -> h < d ->
    forall m t0,
      a <= t0 -> t0 + INR m * h <= b ->
      polyline_len g t0 (uniform_tail t0 h m)
      <= riemann_sum σ t0 (uniform_tail t0 h m) (t0 + INR m * h)
                     (left_tags t0 (uniform_tail t0 h m))
         + eps * (INR m * h).
Proof.
  intros g σ a b eps d h Hrate Hh0 Hhd.
  induction m as [|k IH]; intros t0 Hat0 Htop.
  - cbn [uniform_tail left_tags riemann_sum polyline_len].
    change (INR 0) with 0.
    replace (t0 + 0 * h) with t0 by ring.
    replace (σ t0 * (t0 - t0)) with 0 by ring.
    replace (eps * (0 * h)) with 0 by ring.
    lra.
  - cbn [uniform_tail left_tags riemann_sum polyline_len].
    rewrite S_INR in Htop.
    replace (t0 + (INR k + 1) * h) with (t0 + h + INR k * h) in Htop by ring.
    assert (Hth : t0 + h <= b).
    { pose proof (pos_INR k). nra. }
    assert (Ha1 : a <= t0 + h) by lra.
    specialize (IH (t0 + h) Ha1 Htop).
    rewrite S_INR.
    replace (t0 + (INR k + 1) * h) with (t0 + h + INR k * h) by ring.
    assert (Hgap : t0 + h - t0 < d) by (replace (t0 + h - t0) with h by ring; exact Hhd).
    pose proof (Hrate t0 (t0 + h) Hat0 ltac:(lra) Hth Hgap) as Hch.
    replace (t0 + h - t0) with h in Hch by ring.
    apply rabs_le_both in Hch.
    lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* The two engine premises.                                                   *)
(* -------------------------------------------------------------------------- *)

Lemma speed_integral_tightness :
  forall (g : Curve) (σ F : R -> R) a b,
    speed_integral_premises g σ F a b ->
    forall eps, 0 < eps ->
      exists delta, 0 < delta /\
        forall s t, a <= s -> s <= t -> t <= b -> t - s < delta ->
          F t - F s - dist (g s) (g t) <= eps * (t - s).
Proof.
  intros g σ F a b [Hab [_ [Huc [Hsq Hrate]]]] eps Heps.
  set (eps2 := eps / 2).
  assert (Heps2 : 0 < eps2) by (unfold eps2; lra).
  destruct (Huc eps2 Heps2) as (d1 & Hd1 & Huc').
  destruct (Hrate eps2 Heps2) as (d2 & Hd2 & Hrate').
  exists (Rmin d1 d2).
  split; [apply Rmin_glb_lt; assumption |].
  intros s t Has Hst Htb Hdt.
  assert (Hdt1 : t - s < d1).
  { eapply Rlt_le_trans; [exact Hdt | apply Rmin_l]. }
  assert (Hdt2 : t - s < d2).
  { eapply Rlt_le_trans; [exact Hdt | apply Rmin_r]. }
  pose proof (increment_near_left F σ a b eps2 d1 s t
                Hsq Huc' Has Hst Htb Hdt1) as Hinc.
  pose proof (Hrate' s t Has Hst Htb Hdt2) as Hch.
  apply rabs_le_both in Hch.
  unfold eps2 in *.
  lra.
Qed.

Lemma speed_integral_chord_modulus :
  forall (g : Curve) (σ F : R -> R) a b,
    speed_integral_premises g σ F a b ->
    forall s t, a <= s -> s <= t -> t <= b ->
      dist (g s) (g t) <= F t - F s.
Proof.
  intros g σ F a b [Hab [_ [Huc [Hsq Hrate]]]] s t Has Hst Htb.
  destruct (Req_dec s t) as [Heq | Hne].
  { subst t. rewrite dist_refl. lra. }
  assert (Hst' : s < t) by lra.
  assert (Happrox : forall eps, 0 < eps ->
      dist (g s) (g t) <= F t - F s + (2 * eps) * (t - s)).
  { intros eps Heps.
    destruct (Huc eps Heps) as (d1 & Hd1 & Huc').
    destruct (Hrate eps Heps) as (d2 & Hd2 & Hrate').
    set (dlt := Rmin d1 d2).
    assert (Hdpos : 0 < dlt) by (unfold dlt; apply Rmin_glb_lt; assumption).
    destruct (exists_nat_gt ((t - s) / dlt)) as [n0 Hn0].
    assert (Hnpos : 0 < INR (S n0))
      by (rewrite S_INR; pose proof (pos_INR n0); lra).
    assert (Hngt : (t - s) / dlt < INR (S n0))
      by (rewrite S_INR; lra).
    set (h := (t - s) / INR (S n0)).
    assert (Hh0 : 0 < h).
    { unfold h. apply Rdiv_lt_0_compat; lra. }
    assert (Hnh : INR (S n0) * h = t - s) by (unfold h; field; lra).
    assert (Hhdlt : h < dlt).
    { apply Rmult_lt_reg_l with (INR (S n0)); [lra |].
      rewrite Hnh.
      pose proof (Rmult_lt_compat_l dlt _ _ Hdpos Hngt) as Hm.
      replace (dlt * ((t - s) / dlt)) with (t - s) in Hm
        by (field; lra).
      lra. }
    assert (Hhd1 : h < d1).
    { eapply Rlt_le_trans; [exact Hhdlt | unfold dlt; apply Rmin_l]. }
    assert (Hhd2 : h < d2).
    { eapply Rlt_le_trans; [exact Hhdlt | unfold dlt; apply Rmin_r]. }
    assert (Hend : s + INR (S n0) * h = t) by (rewrite Hnh; ring).
    assert (Htop : s + INR (S n0) * h <= b) by (rewrite Hend; exact Htb).
    pose proof (uniform_riemann_le_F σ F a b eps d1 h Hsq Huc'
                  Hh0 Hhd1 (S n0) s Has Htop) as Hri.
    pose proof (uniform_polyline_le_riemann g σ a b eps d2 h Hrate'
                  Hh0 Hhd2 (S n0) s Has Htop) as Hpl.
    pose proof (dist_le_uniform_polyline g (S n0) s h) as Htri.
    rewrite Hend in Hri, Hpl, Htri.
    rewrite Hnh in Hri, Hpl.
    lra. }
  destruct (Rle_dec (dist (g s) (g t)) (F t - F s)) as [Hok | Hbad].
  { exact Hok. }
  exfalso.
  set (slack := dist (g s) (g t) - (F t - F s)).
  assert (Hsl : 0 < slack) by (unfold slack; lra).
  set (eps := slack / (4 * (t - s))).
  assert (Heps : 0 < eps).
  { unfold eps. apply Rdiv_lt_0_compat; lra. }
  specialize (Happrox eps Heps).
  unfold slack, eps in *.
  lra.
Qed.

(* WITNESS {"claimId":"508-c","topic":"metric","lemma":"speed_integral_is_curve_length","title":"Speed-integral premises imply metric length F b - F a","file":"theories/SpeedIntegral.v","witness":"508-c-speed-integral","board":"#561"} *)
Theorem speed_integral_is_curve_length :
  forall (g : Curve) (σ F : R -> R) a b,
    speed_integral_premises g σ F a b ->
    is_curve_length g a b (F b - F a).
Proof.
  intros g σ F a b Hsip.
  apply curve_length_of_primitive.
  - intros s t Has Hst Htb.
    apply (speed_integral_chord_modulus g σ F a b Hsip s t Has Hst Htb).
  - apply (speed_integral_tightness g σ F a b Hsip).
  - apply (proj1 Hsip).
Qed.

(* Constant speed: UC and the increment sandwich are free.  508-e
   instantiates this at c = 1 after a Fresnel chord-rate. *)
Lemma increment_squeezed_const : forall c a b,
  increment_squeezed (fun t => c * t) (fun _ => c) a b.
Proof.
  intros c a b s t lo hi Has Hst Htb Hbd.
  assert (Hc : lo <= c <= hi) by (apply (Hbd s); lra).
  nra.
Qed.

Lemma uniformly_continuous_const : forall c a b,
  uniformly_continuous_on (fun _ => c) a b.
Proof.
  intros c a b eps Heps.
  exists 1. split; [lra |].
  intros s t _ _ _ _.
  rewrite Rminus_diag_eq by reflexivity.
  rewrite Rabs_R0. lra.
Qed.

Lemma constant_speed_premises : forall (g : Curve) c a b,
  a <= b ->
  0 <= c ->
  chord_rate_tight g (fun _ => c) a b ->
  speed_integral_premises g (fun _ => c) (fun t => c * t) a b.
Proof.
  intros g c a b Hab Hc Hrate.
  repeat split.
  - exact Hab.
  - intros t _ _. exact Hc.
  - apply uniformly_continuous_const.
  - apply increment_squeezed_const.
  - exact Hrate.
Qed.

(* -------------------------------------------------------------------------- *)
(* Witness: circle speed is constantly r — same statement as the envelope.    *)
(* -------------------------------------------------------------------------- *)

Definition circle_speed (r : R) : R -> R := fun _ => r.
Definition circle_prim (r : R) : R -> R := fun t => r * t.

Lemma circle_chord_rate : forall (O : Point) r a b,
  0 <= r ->
  chord_rate_tight (circle_param O r) (circle_speed r) a b.
Proof.
  intros O r a b Hr eps Heps.
  destruct (Req_dec r 0) as [Hr0 | Hrnz].
  - exists 1. split; [lra |].
    intros s t _ Hst _ _.
    subst r. unfold circle_speed.
    pose proof (circle_edge_le O 0 s t (Rle_refl 0) Hst) as Hch.
    pose proof (dist_nonneg (circle_param O 0 s) (circle_param O 0 t)) as Hnn.
    replace (0 * (t - s)) with 0 in Hch by ring.
    assert (Hd0 : dist (circle_param O 0 s) (circle_param O 0 t) = 0) by lra.
    rewrite Hd0. rewrite Rminus_diag_eq by ring.
    rewrite Rabs_R0. nra.
  - assert (Hrpos : 0 < r) by lra.
    set (delta := Rmin 2 (sqrt (24 * eps / r))).
    exists delta.
    assert (Hdpos : 0 < delta).
    { unfold delta. apply Rmin_glb_lt; [lra |].
      apply sqrt_lt_R0. apply Rdiv_lt_0_compat; [nra | exact Hrpos]. }
    split; [exact Hdpos |].
    intros s t _ Hst _ Hdlt.
    unfold circle_speed.
    set (gap := t - s).
    assert (Hgap0 : 0 <= gap) by (unfold gap; lra).
    assert (Hgap2 : gap < 2).
    { unfold gap. eapply Rlt_le_trans; [exact Hdlt |].
      unfold delta. apply Rmin_l. }
    pose proof (circle_edge_le O r s t Hr Hst) as Hup.
    assert (Habs :
      Rabs (dist (circle_param O r s) (circle_param O r t) - r * (t - s))
      = r * (t - s) - dist (circle_param O r s) (circle_param O r t)).
    { rewrite Rabs_minus_sym.
      rewrite Rabs_right by lra.
      reflexivity. }
    rewrite Habs.
    unfold circle_param.
    rewrite circle_chord_dist by exact Hr.
    assert (Hsinpos : 0 <= sin ((t - s) / 2)).
    { apply sin_ge_0; [lra |]. pose proof PI_ge_2. lra. }
    rewrite (Rabs_right (sin ((t - s) / 2))) by lra.
    assert (Hx : 0 <= gap / 2) by lra.
    assert (Hx4 : gap / 2 <= 4) by lra.
    pose proof (sin_lower_taylor (gap / 2) Hx Hx4) as Htaylor.
    assert (Hcalc :
      r * gap - 2 * r * sin (gap / 2)
      <= r * gap - 2 * r * (gap / 2 - (gap / 2) ^ 3 / 6)).
    { apply Rplus_le_compat_l, Ropp_le_contravar.
      apply Rmult_le_compat_l; [lra | exact Htaylor]. }
    unfold gap.
    eapply Rle_trans.
    { replace (t - s) with gap by reflexivity.
      replace (2 * r * sin ((t - s) / 2)) with (2 * r * sin (gap / 2))
        by (unfold gap; reflexivity).
      exact Hcalc. }
    replace (r * gap - 2 * r * (gap / 2 - (gap / 2) ^ 3 / 6))
      with (r * (gap * gap * gap) / 24) by (unfold Rdiv; simpl; field).
    destruct (Req_dec gap 0) as [Hg0 | Hgnz].
    { rewrite Hg0. nra. }
    assert (Hgappos : 0 < gap) by lra.
    apply (Rmult_le_reg_r (/ gap)); [apply Rinv_0_lt_compat; exact Hgappos |].
    replace (r * (gap * gap * gap) / 24 * / gap)
      with (r * (gap * gap) / 24) by (unfold Rdiv; field; lra).
    replace (eps * gap * / gap) with eps by (field; lra).
    assert (Hgd : gap < delta) by (unfold gap; exact Hdlt).
    assert (Hgapsq : gap * gap < delta * delta) by nra.
    assert (Hbound : delta * delta <= 24 * eps / r).
    { unfold delta.
      pose proof (Rmin_r 2 (sqrt (24 * eps / r))) as Hm.
      assert (Hsqrt : 0 <= sqrt (24 * eps / r)) by apply sqrt_pos.
      assert (Hmin0 : 0 <= Rmin 2 (sqrt (24 * eps / r)))
        by (apply Rmin_glb; lra).
      apply Rsqr_incr_1 in Hm; [| exact Hmin0 | exact Hsqrt].
      unfold Rsqr in Hm.
      rewrite sqrt_sqrt in Hm
        by (apply Rlt_le, Rdiv_lt_0_compat; [nra | exact Hrpos]).
      exact Hm. }
    apply Rmult_le_reg_r with (r := 24); [lra |].
    replace (r * (gap * gap) / 24 * 24) with (r * (gap * gap))
      by (field; lra).
    replace (eps * 24) with (24 * eps) by ring.
    apply Rmult_le_reg_r with (r := / r); [apply Rinv_0_lt_compat; exact Hrpos |].
    replace (r * (gap * gap) * / r) with (gap * gap) by (field; lra).
    replace (24 * eps * / r) with (24 * eps / r) by (unfold Rdiv; ring).
    apply Rlt_le.
    eapply Rlt_le_trans; [exact Hgapsq | exact Hbound].
Qed.

Theorem arc_r_theta_via_speed_integral : forall (O : Point) r a b,
  0 <= r -> a <= b ->
  is_curve_length (circle_param O r) a b (r * (b - a)).
Proof.
  intros O r a b Hr Hab.
  replace (r * (b - a)) with (circle_prim r b - circle_prim r a)
    by (unfold circle_prim; ring).
  apply (speed_integral_is_curve_length (circle_param O r)
           (circle_speed r) (circle_prim r) a b).
  apply (constant_speed_premises (circle_param O r) r a b Hab Hr).
  apply circle_chord_rate; exact Hr.
Qed.

(* WITNESS {"claimId":"508-c","topic":"arc,metric","lemma":"arc_quarter_via_speed_integral","title":"Quarter circle exact tier re-derived through the speed-integral pack","file":"theories/SpeedIntegral.v","witness":"508-c-speed-integral","board":"#561"} *)
Corollary arc_quarter_via_speed_integral : forall (O : Point) r,
  0 <= r ->
  is_curve_length (circle_param O r) 0 (PI / 2) (r * PI / 2).
Proof.
  intros O r Hr.
  pose proof PI_RGT_0 as Hpi.
  assert (Hab : 0 <= PI / 2) by lra.
  replace (r * PI / 2) with (r * (PI / 2 - 0)) by field.
  apply arc_r_theta_via_speed_integral; assumption.
Qed.

(* The envelope path and the speed-integral path name the same L. *)
Corollary arc_speed_matches_envelope : forall (O : Point) r a b L,
  0 <= r -> a <= b ->
  is_curve_length (circle_param O r) a b L ->
  L = r * (b - a).
Proof.
  intros O r a b L Hr Hab HL.
  apply (curve_length_unique (circle_param O r) a b L (r * (b - a)) HL).
  apply arc_r_theta_via_speed_integral; assumption.
Qed.

Print Assumptions speed_integral_is_curve_length.
Print Assumptions arc_quarter_via_speed_integral.
Print Assumptions arc_speed_matches_envelope.

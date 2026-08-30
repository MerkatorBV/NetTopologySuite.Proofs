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
                                 Riemann, without constructing an integral)
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

(* One-sided on the window: the modulus is stated for `s ≤ t` only.
   Enough for a packed increment on [a, b]. 508-d must not reuse this
   as a two-sided modulus. *)
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

(* |x − y| = y − x when x ≤ y.  Pass the two sides explicitly —
   keyed unification after `unfold circle_speed` cannot find
   `Rabs (dist … − r·(t−s))` against `(fun _ => r) s`. *)
Lemma rabs_of_deficit : forall x y, x <= y -> Rabs (x - y) = y - x.
Proof.
  intros x y Hxy.
  rewrite Rabs_minus_sym.
  apply Rabs_right.
  lra.
Qed.

(* Apply-form: unification picks the goal's actual subtraction,
   so keyed rewrite does not have to match `r` against `(fun _ => r) s`. *)
Lemma rabs_deficit_le : forall x y e,
  x <= y ->
  y - x <= e ->
  Rabs (x - y) <= e.
Proof.
  intros x y e Hxy Hle.
  rewrite (rabs_of_deficit x y Hxy).
  exact Hle.
Qed.

(* After `rewrite S_INR` the mesh end is `t0 + h + INR k · h`. *)
Lemma plus_nonneg_tail_le : forall t0 h (k : nat) b,
  0 <= h ->
  t0 + h + INR k * h <= b ->
  t0 + h <= b.
Proof.
  intros t0 h k b Hh Htop.
  pose proof (Rmult_le_pos (INR k) h (pos_INR k) Hh) as Hkh.
  apply (Rle_trans (t0 + h) (t0 + h + INR k * h) b); [| exact Htop].
  rewrite <- (Rplus_0_r (t0 + h)) at 1.
  apply Rplus_le_compat_l.
  exact Hkh.
Qed.

Lemma twenty_four_eps_pos : forall eps, 0 < eps -> 0 < 24 * eps.
Proof.
  intros eps Heps.
  apply Rmult_lt_0_compat; [lra | exact Heps].
Qed.

Lemma pos_lt_sq : forall x y, 0 <= x -> x < y -> x * x < y * y.
Proof.
  intros x y Hx Hxy.
  assert (Hy : 0 < y) by (apply Rle_lt_trans with x; [exact Hx | exact Hxy]).
  apply Rle_lt_trans with (r2 := x * y).
  - apply Rmult_le_compat_l; [exact Hx | apply Rlt_le; exact Hxy].
  - apply Rmult_lt_compat_r; [exact Hy | exact Hxy].
Qed.

Lemma rmin_sqrt_sq_bound : forall a b,
  0 <= a ->
  0 <= b ->
  Rmin a (sqrt b) * Rmin a (sqrt b) <= b.
Proof.
  intros a b Ha Hb.
  pose proof (Rmin_r a (sqrt b)) as Hm.
  assert (Hsqrt : 0 <= sqrt b) by apply sqrt_pos.
  assert (Hmin0 : 0 <= Rmin a (sqrt b))
    by (apply Rmin_glb; [exact Ha | exact Hsqrt]).
  apply Rsqr_incr_1 in Hm; [| exact Hmin0 | exact Hsqrt].
  unfold Rsqr in Hm.
  rewrite sqrt_sqrt in Hm by exact Hb.
  exact Hm.
Qed.

(* Taylor remainder of the circle chord: r·gap − 2r·sin(gap/2) ≤ r·gap³/24
   on 0 ≤ gap/2 ≤ 4.  Isolated so circle_chord_rate does not nra. *)
Lemma circle_chord_taylor_slack : forall r gap,
  0 <= r ->
  0 <= gap ->
  gap / 2 <= 4 ->
  r * gap - 2 * r * sin (gap / 2)
  <= r * (gap * gap * gap) / 24.
Proof.
  intros r gap Hr Hg Hx4.
  assert (Hx : 0 <= gap / 2) by lra.
  pose proof (sin_lower_taylor (gap / 2) Hx Hx4) as Htaylor.
  apply Rle_trans with
    (r2 := r * gap - 2 * r * (gap / 2 - (gap / 2) ^ 3 / 6)).
  - apply Rplus_le_compat_l.
    apply Ropp_le_contravar.
    apply Rmult_le_compat_l; [apply Rmult_le_pos; lra | exact Htaylor].
  - apply Req_le.
    replace ((gap / 2) ^ 3) with (gap * gap * gap / 8)
      by (unfold Rdiv; simpl; field).
    unfold Rdiv. field.
Qed.

Lemma cubic_over_gap : forall r gap,
  gap <> 0 ->
  r * (gap * gap * gap) / 24 * / gap = r * (gap * gap) / 24.
Proof.
  intros r gap Hnz.
  unfold Rdiv. field. exact Hnz.
Qed.

Lemma eps_gap_cancel : forall eps gap,
  gap <> 0 ->
  eps * gap * / gap = eps.
Proof.
  intros eps gap Hnz. field. exact Hnz.
Qed.

Lemma r_gap2_times_24 : forall r gap,
  r * (gap * gap) / 24 * 24 = r * (gap * gap).
Proof.
  intros r gap. unfold Rdiv. field.
Qed.

Lemma r_gap2_over_r : forall r gap,
  r <> 0 ->
  r * (gap * gap) * / r = gap * gap.
Proof.
  intros r gap Hnz. field. exact Hnz.
Qed.

Lemma half_gap_lt_one : forall s t,
  t - s < 2 ->
  (t - s) / 2 < 1.
Proof.
  intros s t H.
  apply (Rmult_lt_reg_r 2); [lra |].
  replace ((t - s) / 2 * 2) with (t - s) by field.
  replace (1 * 2) with 2 by ring.
  exact H.
Qed.

Lemma half_gap_le_PI : forall s t,
  t - s < 2 ->
  (t - s) / 2 <= PI.
Proof.
  intros s t H.
  pose proof PI_ge_2 as Hpi2.
  apply Rlt_le.
  apply Rlt_le_trans with 1.
  - apply half_gap_lt_one; exact H.
  - apply (Rle_trans 1 2 PI); [lra | exact Hpi2].
Qed.

(* Pinned flocq stdlib has no Rdiv_le_0_compat. *)
Lemma half_nonneg : forall x, 0 <= x -> 0 <= x / 2.
Proof.
  intros x Hx.
  unfold Rdiv.
  apply Rmult_le_pos; [exact Hx |].
  apply Rlt_le, Rinv_0_lt_compat.
  lra.
Qed.

Lemma sin_half_gap_nonneg : forall s t,
  s <= t ->
  t - s < 2 ->
  0 <= sin ((t - s) / 2).
Proof.
  intros s t Hst Hgap.
  apply sin_ge_0.
  - apply half_nonneg; lra.
  - apply half_gap_le_PI; exact Hgap.
Qed.

Lemma cubic_slack_le_eps_gap : forall r gap delta eps,
  0 < r ->
  0 <= gap ->
  gap < delta ->
  delta * delta <= 24 * eps / r ->
  r * (gap * gap * gap) / 24 <= eps * gap.
Proof.
  intros r gap delta eps Hr Hg Hgd Hbound.
  destruct (Req_dec gap 0) as [Hg0 | Hgnz].
  - rewrite Hg0.
    replace (r * (0 * 0 * 0) / 24) with 0 by (unfold Rdiv; ring).
    rewrite Rmult_0_r. apply Rle_refl.
  - assert (Hgappos : 0 < gap) by lra.
    apply (Rmult_le_reg_r (/ gap)); [apply Rinv_0_lt_compat; exact Hgappos |].
    rewrite (cubic_over_gap r gap Hgnz).
    rewrite (eps_gap_cancel eps gap Hgnz).
    apply (Rmult_le_reg_r 24); [lra |].
    rewrite r_gap2_times_24.
    replace (eps * 24) with (24 * eps) by ring.
    apply (Rmult_le_reg_r (/ r)); [apply Rinv_0_lt_compat; exact Hr |].
    rewrite (r_gap2_over_r r gap); [| lra].
    replace (24 * eps * / r) with (24 * eps / r) by (unfold Rdiv; ring).
    apply Rlt_le.
    eapply Rlt_le_trans; [| exact Hbound].
    apply pos_lt_sq; [exact Hg | exact Hgd].
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
    { apply (plus_nonneg_tail_le t0 h k b); [lra | exact Htop]. }
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
    { apply (plus_nonneg_tail_le t0 h k b); [lra | exact Htop]. }
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

(* Named combination: dist ≤ polyline ≤ Riemann + ε·span ≤ ΔF + 2ε·span.
   Do not fold this into a 12-hypothesis lra after INR / field rewrites —
   the flocq container could not find that witness. *)
Lemma dist_le_dF_plus_two_eps_span :
  forall dgt poly riemann dF eps span,
    dgt <= poly ->
    poly <= riemann + eps * span ->
    riemann <= dF + eps * span ->
    dgt <= dF + (2 * eps) * span.
Proof.
  intros dgt poly riemann dF eps span Htri Hpl Hri.
  apply (Rle_trans dgt poly (dF + (2 * eps) * span)); [exact Htri|].
  apply (Rle_trans poly (riemann + eps * span) (dF + (2 * eps) * span));
    [exact Hpl|].
  replace (dF + (2 * eps) * span) with (dF + eps * span + eps * span)
    by ring.
  apply Rplus_le_compat_r. exact Hri.
Qed.

Lemma slack_half_contradiction :
  forall dgt dF span,
    0 < span ->
    dF < dgt ->
    dgt <= dF + (2 * ((dgt - dF) / (4 * span))) * span ->
    False.
Proof.
  intros dgt dF span Hspan Hgt Happrox.
  replace (2 * ((dgt - dF) / (4 * span)) * span)
    with ((dgt - dF) / 2) in Happrox by (field; lra).
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
    exact (dist_le_dF_plus_two_eps_span
             (dist (g s) (g t))
             (polyline_len g s (uniform_tail s h (S n0)))
             (riemann_sum σ s (uniform_tail s h (S n0)) t
                (left_tags s (uniform_tail s h (S n0))))
             (F t - F s) eps (t - s) Htri Hpl Hri). }
  destruct (Rle_dec (dist (g s) (g t)) (F t - F s)) as [Hok | Hbad].
  { exact Hok. }
  exfalso.
  set (slack := dist (g s) (g t) - (F t - F s)).
  assert (Hsl : 0 < slack) by (unfold slack; lra).
  set (eps := slack / (4 * (t - s))).
  assert (Heps : 0 < eps) by (unfold eps; apply Rdiv_lt_0_compat; lra).
  specialize (Happrox eps Heps).
  unfold slack, eps in Happrox.
  apply (slack_half_contradiction (dist (g s) (g t)) (F t - F s) (t - s));
    [lra | lra | exact Happrox].
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
  replace (c * t - c * s) with (c * (t - s)) by ring.
  split.
  - apply Rmult_le_compat_r; lra.
  - apply Rmult_le_compat_r; lra.
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
  refine (conj Hab (conj _ (conj _ (conj _ Hrate)))).
  - intros t _ _. exact Hc.
  - apply uniformly_continuous_const.
  - apply increment_squeezed_const.
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
    subst r.
    change (circle_speed 0 s) with 0.
    pose proof (circle_edge_le O 0 s t (Rle_refl 0) Hst) as Hch.
    pose proof (dist_nonneg (circle_param O 0 s) (circle_param O 0 t)) as Hnn.
    replace (0 * (t - s)) with 0 in Hch by ring.
    assert (Hd0 : dist (circle_param O 0 s) (circle_param O 0 t) = 0)
      by (apply Rle_antisym; [exact Hch | exact Hnn]).
    rewrite Hd0. rewrite Rminus_diag_eq by ring.
    rewrite Rabs_R0.
    apply Rmult_le_pos; lra.
  - assert (Hrpos : 0 < r) by lra.
    set (delta := Rmin 2 (sqrt (24 * eps / r))).
    exists delta.
    assert (H24 : 0 < 24 * eps) by (apply twenty_four_eps_pos; exact Heps).
    assert (Hdpos : 0 < delta).
    { unfold delta. apply Rmin_glb_lt; [lra |].
      apply sqrt_lt_R0.
      apply Rdiv_lt_0_compat; [exact H24 | exact Hrpos]. }
    split; [exact Hdpos |].
    intros s t _ Hst _ Hdlt.
    set (gap := t - s).
    assert (Hgap0 : 0 <= gap) by (unfold gap; lra).
    assert (Hgap2 : gap < 2).
    { unfold gap. eapply Rlt_le_trans; [exact Hdlt |].
      unfold delta. apply Rmin_l. }
    apply rabs_deficit_le.
    { replace (circle_speed r s * (t - s)) with (r * (t - s))
        by (unfold circle_speed; reflexivity).
      apply circle_edge_le; [exact Hr | exact Hst]. }
    { replace (circle_speed r s * (t - s)) with (r * (t - s))
        by (unfold circle_speed; reflexivity).
      unfold circle_param.
      rewrite circle_chord_dist by exact Hr.
      assert (Hsinpos : 0 <= sin ((t - s) / 2)).
      { apply sin_half_gap_nonneg; [exact Hst |].
        unfold gap in Hgap2; exact Hgap2. }
      rewrite (Rabs_right (sin ((t - s) / 2)))
        by (apply Rle_ge; exact Hsinpos).
      fold gap.
      assert (Hx4 : gap / 2 <= 4) by lra.
      pose proof (circle_chord_taylor_slack r gap Hr Hgap0 Hx4) as Hcalc.
      eapply Rle_trans; [exact Hcalc |].
      apply (cubic_slack_le_eps_gap r gap delta eps Hrpos Hgap0).
      { unfold gap; exact Hdlt. }
      { unfold delta.
        apply rmin_sqrt_sq_bound; [lra |].
        apply Rlt_le.
        apply Rdiv_lt_0_compat; [exact H24 | exact Hrpos]. } }
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

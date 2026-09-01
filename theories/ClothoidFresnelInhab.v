(* ============================================================================
   NetTopologySuite.Proofs.ClothoidFresnelInhab
   ----------------------------------------------------------------------------
   Issue #564 / claimId 508-e: Fresnel inhabitant — the curved unconditional
   clothoid window that #650's conditional pack left open.

   Does NOT remint ClothoidFresnel.v. Reuses fresnel_vx / fresnel_vy /
   fresnel_curve / fresnel_primitives / fresnel_is_curve_length.

   Constructs the genuine Euler-spiral parameterization

     Cx(t) = ∫₀ᵗ cos(u²/2) du
     Cy(t) = ∫₀ᵗ sin(u²/2) du

   via Stdlib RiemannInt (Route 1 / in-corpus; #561 chose Route 1, so
   ADR-0001 Coquelicot lane stays consumer-gated for Halley — this
   letter only needs the integral comparison that discharges
   increment_squeezed, not parametric differentiation under the
   integral). Then

     fresnel_primitives fresnel_Cx fresnel_Cy a b
       (unconditional for every a ≤ b)

   and the [0,1] window has metric length exactly 1.

   Category C: Stdlib RiemannInt / continuity_implies_RiemannInt pulls
   Classical_Prop.classic (same exception discipline as the atan
   lineage; documented in docs/audit-exceptions.txt). Host-lane
   ClothoidFresnel.v stays 3-axiom. No Admitted, no Axiom, no Parameter.
   Windowing stays — do not strengthen to all of ℝ.
   No CurveSegment growth, no ADR-0004 remint, no TRIAGE flip of the
   park paperwork beyond citing the inhabitant.

   Oracle cross-check (informational only): K-token LENGTH_UNIFIED on
   window [sd,ed] emits |ed−sd|; for [0,1] that is 1, matching the
   theorem below.

   WITNESS topic: metric · claimId: 508-e · witness: 508-e-fresnel-inhab
   board: #564

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Auto
   ========================================================================== *)

From Stdlib Require Import Reals RiemannInt Ranalysis1 Ranalysis_reg Lra.
From Stdlib.Logic Require Import FunctionalExtensionality.
From NTS.Proofs Require Import Distance CurveLength SpeedIntegral
                               ClothoidFresnel.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* Continuity of the Fresnel integrands (3-axiom; no RiemannInt yet).         *)
(* -------------------------------------------------------------------------- *)

Lemma fresnel_heading_as_scal :
  fresnel_heading = mult_real_fct (/ 2) (id * id)%F.
Proof.
  apply functional_extensionality; intros t.
  unfold fresnel_heading, mult_real_fct, id, Rdiv.
  apply Rmult_comm.
Qed.

Lemma fresnel_heading_continuity_pt : forall x,
  continuity_pt fresnel_heading x.
Proof.
  intros x.
  rewrite fresnel_heading_as_scal.
  apply derivable_continuous_pt.
  apply derivable_pt_scal.
  apply derivable_pt_mult; apply derivable_pt_id.
Qed.

Lemma fresnel_vx_continuity_pt : forall x,
  continuity_pt fresnel_vx x.
Proof.
  intros x. unfold fresnel_vx.
  change (fun t => cos (fresnel_heading t)) with (comp cos fresnel_heading).
  apply continuity_pt_comp.
  - apply fresnel_heading_continuity_pt.
  - apply continuity_cos.
Qed.

Lemma fresnel_vy_continuity_pt : forall x,
  continuity_pt fresnel_vy x.
Proof.
  intros x. unfold fresnel_vy.
  change (fun t => sin (fresnel_heading t)) with (comp sin fresnel_heading).
  apply continuity_pt_comp.
  - apply fresnel_heading_continuity_pt.
  - apply continuity_sin.
Qed.

(* -------------------------------------------------------------------------- *)
(* Oriented continuous integral ∫_a^b σ, and the Fresnel primitives.          *)
(* -------------------------------------------------------------------------- *)

Definition RInt_cont (σ : R -> R)
    (Hcont : forall x, continuity_pt σ x) (a b : R) : R.
Proof.
  destruct (Rle_dec a b) as [Hab | Hn].
  - refine (RiemannInt _).
    apply (@continuity_implies_RiemannInt σ a b Hab).
    intros x _. exact (Hcont x).
  - refine (- RiemannInt _).
    apply (@continuity_implies_RiemannInt σ b a).
    + apply Rlt_le. apply Rnot_le_lt. exact Hn.
    + intros x _. exact (Hcont x).
Defined.

Definition fresnel_Cx (t : R) : R :=
  RInt_cont fresnel_vx fresnel_vx_continuity_pt 0 t.

Definition fresnel_Cy (t : R) : R :=
  RInt_cont fresnel_vy fresnel_vy_continuity_pt 0 t.

Definition fresnel_param : Curve :=
  fresnel_curve fresnel_Cx fresnel_Cy.

Lemma RInt_cont_le : forall σ Hcont a b (Hab : a <= b)
    (pr : Riemann_integrable σ a b),
  RInt_cont σ Hcont a b = RiemannInt pr.
Proof.
  intros σ Hcont a b Hab pr.
  unfold RInt_cont.
  destruct (Rle_dec a b) as [H|H]; [|elim H; exact Hab].
  apply RiemannInt_P5.
Qed.

Lemma RInt_cont_gt : forall σ Hcont a b (Hba : b <= a)
    (pr : Riemann_integrable σ b a),
  a <> b ->
  RInt_cont σ Hcont a b = - RiemannInt pr.
Proof.
  intros σ Hcont a b Hba pr Hne.
  unfold RInt_cont.
  destruct (Rle_dec a b) as [Hab|Hn].
  - assert (a = b) by lra. contradiction.
  - f_equal. apply RiemannInt_P5.
Qed.

Lemma RInt_cont_diff_nonneg : forall σ Hcont s t,
  s <= t ->
  forall (pr : Riemann_integrable σ s t),
    RInt_cont σ Hcont 0 t - RInt_cont σ Hcont 0 s = RiemannInt pr.
Proof.
  intros σ Hcont s t Hst pr.
  destruct (Rle_dec 0 s) as [Hs0 | Hs0n].
  - assert (Ht0 : 0 <= t) by lra.
    assert (pr0s : Riemann_integrable σ 0 s).
    { apply (@continuity_implies_RiemannInt σ 0 s Hs0).
      intros x _. exact (Hcont x). }
    assert (pr0t : Riemann_integrable σ 0 t).
    { apply (@continuity_implies_RiemannInt σ 0 t Ht0).
      intros x _. exact (Hcont x). }
    rewrite (RInt_cont_le σ Hcont 0 t Ht0 pr0t).
    rewrite (RInt_cont_le σ Hcont 0 s Hs0 pr0s).
    pose proof (RiemannInt_P26 pr0s pr pr0t) as Hadd.
    lra.
  - assert (Hs0' : s < 0) by (apply Rnot_le_lt; exact Hs0n).
    destruct (Rle_dec 0 t) as [Ht0 | Ht0n].
    + assert (prs0 : Riemann_integrable σ s 0).
      { apply (@continuity_implies_RiemannInt σ s 0 (Rlt_le _ _ Hs0')).
        intros x _. exact (Hcont x). }
      assert (pr0t : Riemann_integrable σ 0 t).
      { apply (@continuity_implies_RiemannInt σ 0 t Ht0).
        intros x _. exact (Hcont x). }
      rewrite (RInt_cont_le σ Hcont 0 t Ht0 pr0t).
      rewrite (RInt_cont_gt σ Hcont 0 s (Rlt_le _ _ Hs0') prs0); [|lra].
      pose proof (RiemannInt_P26 prs0 pr0t pr) as Hadd.
      lra.
    + assert (Ht0' : t < 0) by (apply Rnot_le_lt; exact Ht0n).
      assert (prs0 : Riemann_integrable σ s 0).
      { apply (@continuity_implies_RiemannInt σ s 0 (Rlt_le _ _ Hs0')).
        intros x _. exact (Hcont x). }
      assert (prt0 : Riemann_integrable σ t 0).
      { apply (@continuity_implies_RiemannInt σ t 0 (Rlt_le _ _ Ht0')).
        intros x _. exact (Hcont x). }
      rewrite (RInt_cont_gt σ Hcont 0 t (Rlt_le _ _ Ht0') prt0); [|lra].
      rewrite (RInt_cont_gt σ Hcont 0 s (Rlt_le _ _ Hs0') prs0); [|lra].
      pose proof (RiemannInt_P26 pr prt0 prs0) as Hadd.
      lra.
Qed.

Lemma RInt_cont_increment_squeezed : forall σ Hcont a b,
  a <= b ->
  increment_squeezed (fun t => RInt_cont σ Hcont 0 t) σ a b.
Proof.
  intros σ Hcont a b Hab s t lo hi Has Hst Htb Hbd.
  assert (pr : Riemann_integrable σ s t).
  { apply (@continuity_implies_RiemannInt σ s t Hst).
    intros x _. exact (Hcont x). }
  rewrite (RInt_cont_diff_nonneg σ Hcont s t Hst pr).
  apply RiemannInt_const_bound; [exact Hst|].
  intros u [Hsu Hut].
  apply Hbd; lra.
Qed.

Lemma fresnel_Cx_squeezed : forall a b,
  a <= b ->
  increment_squeezed fresnel_Cx fresnel_vx a b.
Proof.
  intros a b Hab. unfold fresnel_Cx.
  apply RInt_cont_increment_squeezed; exact Hab.
Qed.

Lemma fresnel_Cy_squeezed : forall a b,
  a <= b ->
  increment_squeezed fresnel_Cy fresnel_vy a b.
Proof.
  intros a b Hab. unfold fresnel_Cy.
  apply RInt_cont_increment_squeezed; exact Hab.
Qed.

Lemma fresnel_primitives_inhab : forall a b,
  a <= b ->
  fresnel_primitives fresnel_Cx fresnel_Cy a b.
Proof.
  intros a b Hab.
  split.
  - apply fresnel_Cx_squeezed; exact Hab.
  - apply fresnel_Cy_squeezed; exact Hab.
Qed.

(* -------------------------------------------------------------------------- *)
(* Unconditional headlines.                                                   *)
(* -------------------------------------------------------------------------- *)

(* WITNESS {"claimId":"508-e","topic":"metric","lemma":"fresnel_param_is_curve_length","title":"Concrete Fresnel Cx,Cy yield metric length b-a on any window","file":"theories/ClothoidFresnelInhab.v","witness":"508-e-fresnel-inhab","board":"#564"} *)

Theorem fresnel_param_is_curve_length : forall a b,
  a <= b ->
  is_curve_length fresnel_param a b (b - a).
Proof.
  intros a b Hab.
  unfold fresnel_param.
  apply fresnel_is_curve_length; [exact Hab|].
  apply fresnel_primitives_inhab; exact Hab.
Qed.

(* WITNESS {"claimId":"508-e-unit-window-inhab","topic":"metric","lemma":"fresnel_unit_window_length_inhab","title":"[0,1] Fresnel inhabitant has metric length exactly 1","file":"theories/ClothoidFresnelInhab.v","witness":"508-e-fresnel-inhab","board":"#564"} *)

Corollary fresnel_unit_window_length_inhab :
  is_curve_length fresnel_param 0 1 1.
Proof.
  pose proof (fresnel_param_is_curve_length 0 1 ltac:(lra)) as Hlen.
  rewrite Rminus_0_r in Hlen.
  exact Hlen.
Qed.

(* WITNESS {"claimId":"508-e-clothoid-contract-inhab","topic":"metric","lemma":"fresnel_discharges_clothoid_window_inhab","title":"Concrete Fresnel discharges the windowed K-token contract","file":"theories/ClothoidFresnelInhab.v","witness":"508-e-fresnel-inhab","board":"#564"} *)

Theorem fresnel_discharges_clothoid_window_inhab : forall a b,
  a <= b ->
  is_curve_length fresnel_param a b (b - a).
Proof.
  intros a b Hab.
  unfold fresnel_param.
  apply fresnel_discharges_clothoid_window; [exact Hab|].
  apply fresnel_primitives_inhab; exact Hab.
Qed.

Print Assumptions fresnel_param_is_curve_length.
Print Assumptions fresnel_unit_window_length_inhab.
Print Assumptions fresnel_discharges_clothoid_window_inhab.
Print Assumptions fresnel_primitives_inhab.

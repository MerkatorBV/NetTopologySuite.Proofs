(* ============================================================================
   NetTopologySuite.Proofs.Flocq.OrientHybridPackage
   ----------------------------------------------------------------------------
   Formal hypothesis package for binary64 orientation filters (Flocq model).

   Setting.  `orient(P,Q,R)` is the mathematical sign of
       (Qx-Px)(Ry-Py) - (Qy-Py)(Rx-Px)
   i.e. `cross_R_BP`.  `orient_b64` is any pure binary64 evaluation of the
   same DAG; the corpus ships `b64_orient2d` / `b64_orient_sign_naive`.
   A filter F : BPoint^3 -> {Pos,Neg,Zero,Uncertain,Nan} may inspect only
   binary64 operations.  All claims below are restricted to finite
   coordinates (`all_finite`); B2R of NaN/∞ is not a geometric model.

   HYPOTHESIS A  —  Pure float is insufficient.
     Concrete underflow witness (already in Orient_b64_underflow_unsound.v):
         P0 = (0, 0),  P1 = (2^-200, 0),  Q = (2^-200, 2^-900).
     True product 2^-1100 > 0; binary64 underflows to +0.  This file
     restates the disagreement at the *naive* DAG (`b64_orient2d` /
     `b64_orient_sign_naive`), not only at the Stage A filter.

   COROLLARY A1  —  Pure-float winding / PIP cannot be total.
     A single wrong orientation inverts a strict CCW winding test.  On the
     CCW triangle (P0, P1, C) with C = (0, 2^-200) and interior query
         QΔ = (2^-201, 2^-900)
     the three mathematical crosses are strictly positive, but naive
     orientation of the base edge underflows to Zero, so the naive
     all-positive winding test returns false.

   HYPOTHESIS B  —  A sound hybrid exists.
     The combinator that *trusts* a filter's Pos/Neg/Zero and falls back
     to an exact decoder on Uncertain/Nan is sound whenever the filter
     itself is sound.  Existence: the constantly-Uncertain filter plus
     `b64_orient_sign_intexact` (Qed over the whole finite plane).
     Instantiating the same combinator with Stage A is *unsound*: Stage A
     returns a confident Zero on the underflow witness (already proved).
     The corrected decoder `b64_orient_sign_stage_d_safe` is the
     don't-trust-Zero wiring; its Pos/Neg fast path is still only proved
     in the integer regime (open Stage A error-bound).

   HYPOTHESIS C  —  Near-optimality / information-theoretic lower bound.
     Closed instance: any filter whose verdict is a function of
     `(b64_orient2d, b64_orient2d_detsum)` alone cannot return a definite
     Pos/Neg/Zero on the underflow class.  The witness and the origin
     triple (0,0),(0,0),(0,0) share observation (0, 0) but have different
     true signs, so a sound det-only filter must return Uncertain or Nan.
     NOT claimed: the general C·ε·M² bound, nor soundness / near-optimality
     of Ozaki et al. or Bartels–Fisikopoulos–Weiser.  Ozaki remains
     ADR-0004 cold (docs/jts-1093-orient-lane-2026-08.md); do not add an
     Ozaki FFI until a named claim is proved.

   OPTIONAL  —  Hybrid triangle membership off the mathematical boundary.
     Integer-exact all-positive winding agrees with mathematical strict
     CCW interior for every finite triple of edges.  Combined with A1,
     this is the triangle-scale hybrid PIP lift.  A general binary64
     point-in-ring statement is not in this file.

   No `Admitted`.  Residuals are documented, not stubbed.

topic: binary64
claimId: none
witness: none

   Intentionally off-board: this is the Phase 0 filter-hypothesis package,
   not a minted micro-RGR / ADR-0004 teaching card.  Ozaki stays cold.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.6
   ============================================================================ *)

From Stdlib Require Import Reals.
From Stdlib Require Import ZArith.

From Flocq Require Import IEEE754.Binary.

From NTS.Proofs.Flocq Require Import Validate_binary64.
From NTS.Proofs.Flocq Require Import Orientation_b64.
From NTS.Proofs.Flocq Require Import Orient_b64_sound.
From NTS.Proofs.Flocq Require Import Orient_b64_exact_full.
From NTS.Proofs.Flocq Require Import Orient_b64_underflow_unsound.
From NTS.Proofs.Flocq Require Import Orient_b64_underflow_recovery.

Local Open Scope R_scope.

(* ========================================================================== *)
(* Shared vocabulary.                                                         *)
(* ========================================================================== *)

Definition orient_ok (s : orient_sign_robust) (P Q R : BPoint) : Prop :=
  match s with
  | OrientRPos       => 0 < cross_R_BP P Q R
  | OrientRNeg       => cross_R_BP P Q R < 0
  | OrientRZero      => cross_R_BP P Q R = 0
  | OrientRNan       => True
  | OrientRUncertain => True
  end.

Definition filter_sound
    (F : BPoint -> BPoint -> BPoint -> orient_sign_robust) : Prop :=
  forall P Q R : BPoint, all_finite P Q R -> orient_ok (F P Q R) P Q R.

(* The user's hybrid: trust a definite filter verdict; exact fallback
   only on Uncertain (and Nan, which the five-valued corpus sign adds). *)
Definition hybrid_trust_zero
    (F exact : BPoint -> BPoint -> BPoint -> orient_sign_robust)
    (P Q R : BPoint) : orient_sign_robust :=
  match F P Q R with
  | OrientRPos => OrientRPos
  | OrientRNeg => OrientRNeg
  | OrientRZero => OrientRZero
  | OrientRNan | OrientRUncertain => exact P Q R
  end.

(* ========================================================================== *)
(* Hypothesis A — naive binary64 evaluation disagrees with the true sign.     *)
(* ========================================================================== *)

Theorem hypothesis_A_naive_underflow :
  b64_orient_sign_naive uP0 uP1 uQ = OrientZero
  /\ Binary.B2R prec emax (b64_orient2d uP0 uP1 uQ) = 0
  /\ 0 < cross_R_BP uP0 uP1 uQ.
Proof.
  split; [vm_compute; reflexivity |].
  split; [vm_compute; reflexivity |].
  exact uWitness_true_cross_pos.
Qed.

(* Stage A is the same witness one layer up; recorded so the package
   names both the naive DAG and the filter. *)
Theorem hypothesis_A_stage_a_underflow :
  b64_orient_sign_filtered uP0 uP1 uQ = OrientRZero
  /\ 0 < cross_R_BP uP0 uP1 uQ.
Proof.
  split; [exact uWitness_filter_says_zero | exact uWitness_true_cross_pos].
Qed.

(* ========================================================================== *)
(* Corollary A1 — a wrong orientation breaks strict CCW winding / PIP.        *)
(* ========================================================================== *)

(* 2^-201 = 2^52 * 2^-253, exactly representable. *)
Definition b64_2pow_m201 : binary64 :=
  Binary.B754_finite prec emax false 4503599627370496 (-253) eq_refl.

(* CCW right triangle on the underflow scale:
     A = (0, 0),  B = (2^-200, 0),  C = (0, 2^-200).
   Query strictly inside:
     QΔ = (2^-201, 2^-900).
   Mathematical crosses:
     orient(A,B,QΔ) = 2^-200 * 2^-900           = 2^-1100 > 0
     orient(B,C,QΔ) = 2^-200 * (2^-201 - 2^-900) > 0
     orient(C,A,QΔ) = 2^-401                       > 0
   Float: the first product underflows, so naive winding is not all-Pos. *)
Definition tA : BPoint := uP0.
Definition tB : BPoint := uP1.
Definition tC : BPoint := mkBP b64_zero b64_2pow_m200.
Definition tQ : BPoint := mkBP b64_2pow_m201 b64_2pow_m900.

Definition math_strict_ccw_in (A B C Q : BPoint) : Prop :=
  0 < cross_R_BP A B Q /\ 0 < cross_R_BP B C Q /\ 0 < cross_R_BP C A Q.

Definition naive_strict_ccw_in (A B C Q : BPoint) : bool :=
  match b64_orient_sign_naive A B Q,
        b64_orient_sign_naive B C Q,
        b64_orient_sign_naive C A Q with
  | OrientPos, OrientPos, OrientPos => true
  | _, _, _ => false
  end.

Definition robust_strict_ccw_in
    (sign : BPoint -> BPoint -> BPoint -> orient_sign_robust)
    (A B C Q : BPoint) : bool :=
  match sign A B Q, sign B C Q, sign C A Q with
  | OrientRPos, OrientRPos, OrientRPos => true
  | _, _, _ => false
  end.

Lemma tABQ_all_finite : all_finite tA tB tQ.
Proof. unfold all_finite. vm_compute. repeat split; reflexivity. Qed.

Lemma tBCQ_all_finite : all_finite tB tC tQ.
Proof. unfold all_finite. vm_compute. repeat split; reflexivity. Qed.

Lemma tCAQ_all_finite : all_finite tC tA tQ.
Proof. unfold all_finite. vm_compute. repeat split; reflexivity. Qed.

Lemma tABQ_exact_pos : b64_orient2d_exact tA tB tQ = 1%Z.
Proof. vm_compute. reflexivity. Qed.

Lemma tBCQ_exact_pos : b64_orient2d_exact tB tC tQ = 1%Z.
Proof. vm_compute. reflexivity. Qed.

Lemma tCAQ_exact_pos : b64_orient2d_exact tC tA tQ = 1%Z.
Proof. vm_compute. reflexivity. Qed.

Lemma tABQ_true_pos : 0 < cross_R_BP tA tB tQ.
Proof.
  pose proof (b64_orient2d_exact_sound tA tB tQ tABQ_all_finite) as (Hpos & _ & _).
  apply (proj2 Hpos). exact tABQ_exact_pos.
Qed.

Lemma tBCQ_true_pos : 0 < cross_R_BP tB tC tQ.
Proof.
  pose proof (b64_orient2d_exact_sound tB tC tQ tBCQ_all_finite) as (Hpos & _ & _).
  apply (proj2 Hpos). exact tBCQ_exact_pos.
Qed.

Lemma tCAQ_true_pos : 0 < cross_R_BP tC tA tQ.
Proof.
  pose proof (b64_orient2d_exact_sound tC tA tQ tCAQ_all_finite) as (Hpos & _ & _).
  apply (proj2 Hpos). exact tCAQ_exact_pos.
Qed.

Theorem triangle_math_strict_ccw_in :
  math_strict_ccw_in tA tB tC tQ.
Proof.
  unfold math_strict_ccw_in.
  split; [exact tABQ_true_pos |].
  split; [exact tBCQ_true_pos | exact tCAQ_true_pos].
Qed.

(* The base-edge naive evaluation is the underflow Zero of Hypothesis A,
   now at QΔ rather than the original on-vertical Q. *)
Lemma triangle_naive_base_zero :
  b64_orient_sign_naive tA tB tQ = OrientZero.
Proof. vm_compute. reflexivity. Qed.

Theorem corollary_A1_naive_winding_misses_interior :
  math_strict_ccw_in tA tB tC tQ
  /\ naive_strict_ccw_in tA tB tC tQ = false.
Proof.
  split; [exact triangle_math_strict_ccw_in |].
  unfold naive_strict_ccw_in.
  rewrite triangle_naive_base_zero.
  reflexivity.
Qed.

(* ========================================================================== *)
(* Hypothesis B — sound hybrid = sound filter + exact fallback.               *)
(* ========================================================================== *)

Theorem hybrid_trust_zero_preserves_soundness :
  forall (F exact : BPoint -> BPoint -> BPoint -> orient_sign_robust),
    filter_sound F ->
    filter_sound exact ->
    filter_sound (hybrid_trust_zero F exact).
Proof.
  intros F exact HF Hex P Q R Hfin.
  unfold hybrid_trust_zero, orient_ok.
  pose proof (HF P Q R Hfin) as HFv.
  destruct (F P Q R); try exact HFv.
  all: apply Hex; exact Hfin.
Qed.

Definition filter_uncertain
    : BPoint -> BPoint -> BPoint -> orient_sign_robust :=
  fun _ _ _ => OrientRUncertain.

Lemma filter_uncertain_sound : filter_sound filter_uncertain.
Proof. intros P Q R _. exact I. Qed.

Lemma intexact_filter_sound : filter_sound b64_orient_sign_intexact.
Proof. exact b64_orient_sign_intexact_sound. Qed.

(* Existence witness for Hypothesis B: refuse every float commit, always
   fall back to the integer-mantissa exact decoder.  The filter inspects
   no binary64 arithmetic (vacuously allowed). *)
Theorem hypothesis_B_exists_hybrid :
  exists F exact : BPoint -> BPoint -> BPoint -> orient_sign_robust,
    filter_sound F
    /\ filter_sound exact
    /\ filter_sound (hybrid_trust_zero F exact)
    /\ (forall P Q R : BPoint,
          hybrid_trust_zero F exact P Q R <> OrientRNan
          /\ hybrid_trust_zero F exact P Q R <> OrientRUncertain).
Proof.
  exists filter_uncertain, b64_orient_sign_intexact.
  split; [exact filter_uncertain_sound |].
  split; [exact intexact_filter_sound |].
  split.
  - apply hybrid_trust_zero_preserves_soundness;
      [exact filter_uncertain_sound | exact intexact_filter_sound].
  - intros P Q R.
    unfold hybrid_trust_zero, filter_uncertain.
    apply b64_orient_sign_intexact_never_indefinite.
Qed.

(* The user's combinator instantiated with Stage A *trusts* the underflow
   Zero and is therefore unsound — this is Hypothesis A at the hybrid
   layer, and the reason `b64_orient_sign_stage_d_safe` does not trust
   Zero. *)
Theorem hypothesis_B_stage_a_trust_zero_unsound :
  let H := hybrid_trust_zero b64_orient_sign_filtered
                             b64_orient_sign_intexact in
  H uP0 uP1 uQ = OrientRZero
  /\ 0 < cross_R_BP uP0 uP1 uQ.
Proof.
  split.
  - unfold hybrid_trust_zero.
    rewrite uWitness_filter_says_zero.
    reflexivity.
  - exact uWitness_true_cross_pos.
Qed.

Theorem stage_a_not_filter_sound :
  ~ filter_sound b64_orient_sign_filtered.
Proof.
  intros HF.
  pose proof (HF uP0 uP1 uQ uWitness_all_finite) as Hs.
  rewrite uWitness_filter_says_zero in Hs.
  pose proof uWitness_true_cross_pos as Hp.
  rewrite Hs in Hp.
  apply (Rlt_irrefl 0 Hp).
Qed.

(* ========================================================================== *)
(* Optional strengthening — hybrid (intexact) winding on triangles.           *)
(* ========================================================================== *)

Lemma intexact_pos_iff :
  forall P0 P1 Q : BPoint,
    all_finite P0 P1 Q ->
    (b64_orient_sign_intexact P0 P1 Q = OrientRPos
     <-> 0 < cross_R_BP P0 P1 Q).
Proof.
  intros P0 P1 Q Hfin.
  pose proof (b64_orient2d_exact_sound P0 P1 Q Hfin) as (Hpos & _ & _).
  unfold b64_orient_sign_intexact.
  split.
  - intro E.
    destruct (Z.eqb_spec (b64_orient2d_exact P0 P1 Q) 1) as [E1 | N1].
    + apply (proj2 Hpos). exact E1.
    + destruct (Z.eqb_spec (b64_orient2d_exact P0 P1 Q) (-1)); discriminate.
  - intro Hlt.
    apply (proj1 Hpos) in Hlt.
    destruct (Z.eqb_spec (b64_orient2d_exact P0 P1 Q) 1) as [E1 | N1].
    + reflexivity.
    + congruence.
Qed.

Theorem intexact_strict_ccw_in_iff :
  forall A B C Q : BPoint,
    all_finite A B Q ->
    all_finite B C Q ->
    all_finite C A Q ->
    robust_strict_ccw_in b64_orient_sign_intexact A B C Q = true
    <-> math_strict_ccw_in A B C Q.
Proof.
  intros A B C Q HAB HBC HCA.
  unfold robust_strict_ccw_in, math_strict_ccw_in.
  split.
  - intro Hw.
    destruct (b64_orient_sign_intexact A B Q) eqn:EAB;
      try (simpl in Hw; discriminate).
    destruct (b64_orient_sign_intexact B C Q) eqn:EBC;
      try (simpl in Hw; discriminate).
    destruct (b64_orient_sign_intexact C A Q) eqn:ECA;
      try (simpl in Hw; discriminate).
    split; [apply (proj1 (intexact_pos_iff A B Q HAB)); exact EAB |].
    split; [apply (proj1 (intexact_pos_iff B C Q HBC)); exact EBC |].
    apply (proj1 (intexact_pos_iff C A Q HCA)). exact ECA.
  - intros (HABP & HBCP & HCAP).
    apply (proj2 (intexact_pos_iff A B Q HAB)) in HABP.
    apply (proj2 (intexact_pos_iff B C Q HBC)) in HBCP.
    apply (proj2 (intexact_pos_iff C A Q HCA)) in HCAP.
    rewrite HABP, HBCP, HCAP.
    reflexivity.
Qed.

(* On the A1 triangle the exact winding recovers the true interior, which
   the naive winding missed. *)
Theorem hybrid_triangle_recovers_A1_interior :
  robust_strict_ccw_in b64_orient_sign_intexact tA tB tC tQ = true
  /\ naive_strict_ccw_in tA tB tC tQ = false.
Proof.
  split.
  - apply (proj2 (intexact_strict_ccw_in_iff tA tB tC tQ
                    tABQ_all_finite tBCQ_all_finite tCAQ_all_finite)).
    exact triangle_math_strict_ccw_in.
  - apply (proj2 corollary_A1_naive_winding_misses_interior).
Qed.

(* ========================================================================== *)
(* Hypothesis C — det-only filters are forced Uncertain on the underflow     *)
(* observation class.                                                         *)
(* ========================================================================== *)

Definition det_obs (P Q R : BPoint) : binary64 * binary64 :=
  (b64_orient2d P Q R, b64_orient2d_detsum P Q R).

Definition filter_det_only
    (F : BPoint -> BPoint -> BPoint -> orient_sign_robust) : Prop :=
  forall P Q R P' Q' R' : BPoint,
    det_obs P Q R = det_obs P' Q' R' ->
    F P Q R = F P' Q' R'.

Lemma uP0_triple_all_finite : all_finite uP0 uP0 uP0.
Proof. unfold all_finite. vm_compute. repeat split; reflexivity. Qed.

Lemma uP0_triple_cross_zero : cross_R_BP uP0 uP0 uP0 = 0.
Proof. vm_compute. ring. Qed.

Lemma underflow_obs_eq_origin :
  det_obs uP0 uP1 uQ = det_obs uP0 uP0 uP0.
Proof. vm_compute. reflexivity. Qed.

(* Two finite triples that a det-only filter cannot tell apart, with
   incompatible true signs, force Uncertain/Nan. *)
Theorem det_only_sound_uncertain_on_collision :
  forall (F : BPoint -> BPoint -> BPoint -> orient_sign_robust)
         (P Q R P' Q' R' : BPoint),
    filter_det_only F ->
    filter_sound F ->
    all_finite P Q R ->
    all_finite P' Q' R' ->
    det_obs P Q R = det_obs P' Q' R' ->
    (0 < cross_R_BP P Q R /\ ~ (0 < cross_R_BP P' Q' R'))
    \/ (cross_R_BP P Q R < 0 /\ ~ (cross_R_BP P' Q' R' < 0))
    \/ (cross_R_BP P Q R = 0 /\ cross_R_BP P' Q' R' <> 0) ->
    F P Q R = OrientRUncertain \/ F P Q R = OrientRNan.
Proof.
  intros F P Q R P' Q' R' Honly Hsound Hfin Hfin' Hobs Hsign.
  assert (HeqF : F P Q R = F P' Q' R') by (apply Honly; exact Hobs).
  pose proof (Hsound P Q R Hfin) as HS.
  pose proof (Hsound P' Q' R' Hfin') as HS'.
  destruct (F P Q R) eqn:Hf;
    try (left; reflexivity); try (right; reflexivity).
  - (* Pos. destruct substitutes in HeqF / HS. *)
    cbn in HS.
    rewrite <- HeqF in HS'. cbn in HS'.
    destruct Hsign as [[_ Hn] | [[Hp _] | [Hz _]]].
    + contradiction.
    + exfalso. apply (Rlt_asym _ _ HS Hp).
    + rewrite Hz in HS. exfalso. apply (Rlt_irrefl 0 HS).
  - cbn in HS.
    rewrite <- HeqF in HS'. cbn in HS'.
    destruct Hsign as [[Hp _] | [[_ Hn] | [Hz _]]].
    + exfalso. apply (Rlt_asym _ _ Hp HS).
    + contradiction.
    + rewrite Hz in HS. exfalso. apply (Rlt_irrefl 0 HS).
  - cbn in HS.
    rewrite <- HeqF in HS'. cbn in HS'.
    destruct Hsign as [[Hp _] | [[Hn _] | [_ Hnz]]].
    + rewrite HS in Hp. exfalso. apply (Rlt_irrefl 0 Hp).
    + rewrite HS in Hn. exfalso. apply (Rlt_irrefl 0 Hn).
    + contradiction.
Qed.

(* The proof above of the Pos/Neg branches is a bit clumsy because the
   collision hypothesis is a three-way disjunction.  The concrete
   underflow-vs-origin instance is the claim we actually need, and its
   case analysis is direct. *)
Theorem hypothesis_C_det_only_must_uncertain_underflow_class :
  forall F : BPoint -> BPoint -> BPoint -> orient_sign_robust,
    filter_det_only F ->
    filter_sound F ->
    F uP0 uP1 uQ = OrientRUncertain \/ F uP0 uP1 uQ = OrientRNan.
Proof.
  intros F Honly Hsound.
  pose proof (Honly uP0 uP1 uQ uP0 uP0 uP0 underflow_obs_eq_origin) as HeqF.
  pose proof (Hsound uP0 uP1 uQ uWitness_all_finite) as HS.
  pose proof (Hsound uP0 uP0 uP0 uP0_triple_all_finite) as HS0.
  destruct (F uP0 uP1 uQ) eqn:Hf;
    try (left; reflexivity); try (right; reflexivity).
  - (* Pos: correct on the witness, wrong on the origin. *)
    rewrite <- HeqF in HS0. cbn in HS0.
    rewrite uP0_triple_cross_zero in HS0.
    exfalso. apply (Rlt_irrefl 0 HS0).
  - (* Neg: wrong on the witness. *)
    cbn in HS.
    pose proof uWitness_true_cross_pos as Hp.
    exfalso. exact (Rlt_asym _ _ Hp HS).
  - (* Zero: wrong on the witness. *)
    cbn in HS.
    pose proof uWitness_true_cross_pos as Hp.
    rewrite HS in Hp.
    exfalso. apply (Rlt_irrefl 0 Hp).
Qed.

(* Residual C-general / Ozaki / Bartels.  The package does *not* introduce
   an Ozaki filter, an automatically generated Bartels–Fisikopoulos–Weiser
   filter, or a theorem of the shape

       |orient(P,Q,R)| ≤ C · ε · M²  →  F P Q R = Uncertain

   for a DAG-sharp C.  That is the next named residual.  The instance
   above is the information-theoretic core that any such proof must
   contain: when the binary64 observation class is ambiguous, a sound
   filter cannot commit. *)

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions hypothesis_A_naive_underflow.
Print Assumptions corollary_A1_naive_winding_misses_interior.
Print Assumptions hypothesis_B_exists_hybrid.
Print Assumptions hypothesis_B_stage_a_trust_zero_unsound.
Print Assumptions hypothesis_C_det_only_must_uncertain_underflow_class.
Print Assumptions intexact_strict_ccw_in_iff.
Print Assumptions hybrid_triangle_recovers_A1_interior.
Print Assumptions stage_a_not_filter_sound.
Print Assumptions det_only_sound_uncertain_on_collision.

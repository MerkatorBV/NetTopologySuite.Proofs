(* ============================================================================
   NetTopologySuite.Proofs.Flocq.OrientStratifiedAPF
   ----------------------------------------------------------------------------
   Stratified Adaptive Precision Filter (APF) for the orient2d predicate used
   throughout RelateNG's robust geometry (JTS `RobustDeterminant` /
   `Algorithm.Orientation.Index`).

   The design is a two-stratum hybrid:

     Stratum A  -- the ulp-bounded fast filter `b64_orient_sign_filtered`
                   (Shewchuk Stage A error bound `(3 + 16*eps)*eps`), a pure
                   binary64 computation that maps 1:1 onto SIMD `+.`/`-.`/`*.`
                   under the native-float extraction (see the `_extract`
                   companion and `docs/orient-stratified-apf.md`).  Commits to
                   Pos/Neg/Zero only when `|det|` strictly clears the bound;
                   otherwise it declines (Uncertain / Nan).

     Stratum D  -- the certified expansion switch
                   `b64_orient2d_expansion_sign`, a Shewchuk fast-expansion-sum
                   determinant whose sign is exact.  Fires exactly when the
                   filter declines.

   This file's contribution over the already-shipped `b64_orient_sign_stage_d`
   (Orient_b64_stage_d.v) is threefold:

     X (filter + switch lemmas).  `b64_orient_sign_stage_d_sound` in
       Orient_b64_stage_d.v is stated *under* the hypothesis
       `fast_expansion_sum_strong_nonoverlap_headline` -- the general Shewchuk
       Theorem-13 property that is FALSE as stated and therefore carried as an
       assumption there.  Here we re-derive soundness of the SAME composed
       decoder in the integer regime with that hypothesis DISCHARGED, routing
       through the unconditional `b64_orient2d_expansion_int_sign_correct_coords`
       (Orient_b64_int_safe_coords.v).  We also add the unconditional
       decisiveness fact (the stratified decoder never returns Nan/Uncertain)
       and the sharp "decides orientation" bi-implication.

     Y (witness algebra).  A provenance-carrying certificate `apf_witness`
       records which stratum decided each call, with a `decode`/`run` pair
       satisfying `decode (run ...) = b64_orient_sign_stage_d ...`, a
       decidable provenance characterisation, and an algebra: a sign
       involution that `decode` is a homomorphism for, connected to the
       geometric antisymmetry of the exact spec `cross_R_BP` (a `ring`
       identity) to obtain argument-swap antisymmetry of the whole decoder.

     Z (extraction + benchmark).  Stratum A (`b64_orient_sign_filtered`)
       already extracts to native binary64 in the shipped oracle
       (`Validate_binary64_extract.v`).  `b64_orient_apf` / `apf_run` are plain
       binary64 recursion on top of it; the residual step for a native
       exact-fallback harness (an `Extract Constant` for the B2R-based
       `sign_of_expansion`) and the NTS benchmark protocol (ulp-hit-rate vs
       `RobustDeterminant` / `Orientation.Index`) are written up in
       `docs/orient-stratified-apf.md`.

   No `Admitted`, no `Axiom`, no `Parameter`.  All proofs `Qed`-closed.  Pure
   Flocq (binary64); the assumption footprint matches the Orient_b64_* stack.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals ZArith Lia Lra.
From Flocq Require Import IEEE754.Binary Core.
From NTS.Proofs.Flocq Require Import Validate_binary64.
From NTS.Proofs.Flocq Require Import Orientation_b64.
From NTS.Proofs.Flocq Require Import Orient_b64_sound.
From NTS.Proofs.Flocq Require Import Orient_b64_exact.
From NTS.Proofs.Flocq Require Import B64_Expansion.
From NTS.Proofs.Flocq Require Import Orient_b64_expansion.
From NTS.Proofs.Flocq Require Import Orient_b64_int_safe_coords.
From NTS.Proofs.Flocq Require Import Orient_b64_stage_d.

Local Open Scope R_scope.

(* ========================================================================== *)
(* §0  The stratified decoder (reusing the shipped composition).              *)
(* ========================================================================== *)

(* `b64_orient_apf` IS the shipped `b64_orient_sign_stage_d`: filter first,   *)
(* fall back to the certified expansion sign when the filter declines.  We    *)
(* give it a stable APF-facing name (and, below, a witness-carrying variant)  *)
(* so the extraction target and the benchmark harness have a fixed handle.    *)
Definition b64_orient_apf (P0 P1 Q : BPoint) : orient_sign_robust :=
  b64_orient_sign_stage_d P0 P1 Q.

Lemma b64_orient_apf_unfold :
  forall P0 P1 Q,
    b64_orient_apf P0 P1 Q =
      match b64_orient_sign_filtered P0 P1 Q with
      | OrientRPos       => OrientRPos
      | OrientRNeg       => OrientRNeg
      | OrientRZero      => OrientRZero
      | OrientRUncertain => b64_orient_sign_exact P0 P1 Q
      | OrientRNan       => b64_orient_sign_exact P0 P1 Q
      end.
Proof. reflexivity. Qed.

(* ========================================================================== *)
(* §1  Track X -- filter + switch lemmas.                                     *)
(* ========================================================================== *)

(* -------------------------------------------------------------------------- *)
(* X.1  Fast-path: whenever Stratum A commits, the switch is not consulted    *)
(* and the decoder returns the filter's verdict verbatim.  (No override.)     *)
(* -------------------------------------------------------------------------- *)

Lemma b64_orient_apf_fast_path :
  forall P0 P1 Q,
    b64_orient_sign_filtered P0 P1 Q <> OrientRNan ->
    b64_orient_sign_filtered P0 P1 Q <> OrientRUncertain ->
    b64_orient_apf P0 P1 Q = b64_orient_sign_filtered P0 P1 Q.
Proof.
  intros P0 P1 Q Hnan Hunc.
  unfold b64_orient_apf, b64_orient_sign_stage_d.
  destruct (b64_orient_sign_filtered P0 P1 Q); congruence.
Qed.

(* -------------------------------------------------------------------------- *)
(* X.2  Decisiveness -- UNCONDITIONAL.  The stratified decoder never returns  *)
(* Nan or Uncertain: the exact fallback always commits to Pos/Neg/Zero, so    *)
(* the two indefinite verdicts are structurally unreachable.  The shipped     *)
(* stack only has the *conditional* `tiny_regime_decisive`; this is the       *)
(* hypothesis-free strengthening.                                             *)
(* -------------------------------------------------------------------------- *)

Lemma b64_orient_apf_decisive :
  forall P0 P1 Q,
    b64_orient_apf P0 P1 Q = OrientRPos \/
    b64_orient_apf P0 P1 Q = OrientRNeg \/
    b64_orient_apf P0 P1 Q = OrientRZero.
Proof.
  intros P0 P1 Q.
  unfold b64_orient_apf, b64_orient_sign_stage_d, b64_orient_sign_exact,
         expansion_sign_to_orient_robust.
  destruct (b64_orient_sign_filtered P0 P1 Q);
    try (destruct (b64_orient2d_expansion_sign P0 P1 Q)); auto.
Qed.

Corollary b64_orient_apf_never_nan :
  forall P0 P1 Q, b64_orient_apf P0 P1 Q <> OrientRNan.
Proof.
  intros P0 P1 Q.
  destruct (b64_orient_apf_decisive P0 P1 Q) as [H | [H | H]];
    rewrite H; discriminate.
Qed.

Corollary b64_orient_apf_never_uncertain :
  forall P0 P1 Q, b64_orient_apf P0 P1 Q <> OrientRUncertain.
Proof.
  intros P0 P1 Q.
  destruct (b64_orient_apf_decisive P0 P1 Q) as [H | [H | H]];
    rewrite H; discriminate.
Qed.

(* -------------------------------------------------------------------------- *)
(* X.3  Soundness of the certified expansion switch in the integer regime,    *)
(* WITHOUT the `fast_expansion_sum_strong_nonoverlap_headline` hypothesis.    *)
(* Routes through the unconditional integer-coordinate sign correctness.      *)
(* -------------------------------------------------------------------------- *)

Lemma b64_orient_sign_exact_sound_int :
  forall P0 P1 Q : BPoint,
    orient2d_inputs_int_safe P0 P1 Q ->
    b64_orient2d_expansion_safe P0 P1 Q ->
    match b64_orient_sign_exact P0 P1 Q with
    | OrientRPos       => 0 < cross_R_BP P0 P1 Q
    | OrientRNeg       => cross_R_BP P0 P1 Q < 0
    | OrientRZero      => cross_R_BP P0 P1 Q = 0
    | OrientRNan       => True
    | OrientRUncertain => True
    end.
Proof.
  intros P0 P1 Q Hint Hexp.
  unfold b64_orient_sign_exact, expansion_sign_to_orient_robust.
  pose proof (b64_orient2d_expansion_int_sign_correct_coords P0 P1 Q Hint Hexp)
    as Hsign.
  destruct (b64_orient2d_expansion_sign P0 P1 Q); exact Hsign.
Qed.

(* -------------------------------------------------------------------------- *)
(* X.4  HEADLINE: the stratified decoder is sound against the exact spec      *)
(* `cross_R_BP` in the integer regime, with NO reliance on the (false-as-     *)
(* stated) strong-nonoverlap headline.  This strictly strengthens             *)
(* `b64_orient_sign_stage_d_sound`, which carries that hypothesis.            *)
(* -------------------------------------------------------------------------- *)

Theorem b64_orient_apf_sound_int :
  forall P0 P1 Q : BPoint,
    orient2d_inputs_int_safe P0 P1 Q ->
    b64_orient2d_expansion_safe P0 P1 Q ->
    match b64_orient_apf P0 P1 Q with
    | OrientRPos       => 0 < cross_R_BP P0 P1 Q
    | OrientRNeg       => cross_R_BP P0 P1 Q < 0
    | OrientRZero      => cross_R_BP P0 P1 Q = 0
    | OrientRNan       => True
    | OrientRUncertain => True
    end.
Proof.
  intros P0 P1 Q Hint Hexp.
  unfold b64_orient_apf, b64_orient_sign_stage_d.
  pose proof (b64_orient_sign_filtered_sound_small_int P0 P1 Q Hint) as Hfilt.
  pose proof (b64_orient_sign_exact_sound_int P0 P1 Q Hint Hexp) as Hexact.
  destruct (b64_orient_sign_filtered P0 P1 Q);
    [exact Hfilt | exact Hfilt | exact Hfilt | exact Hexact | exact Hexact].
Qed.

(* -------------------------------------------------------------------------- *)
(* X.5  Sharp form: the decoder DECIDES orientation.  Each verdict is         *)
(* equivalent to the corresponding sign of the exact determinant.  Combines   *)
(* soundness (X.4) with decisiveness (X.2) and trichotomy of `cross_R_BP`.    *)
(* -------------------------------------------------------------------------- *)

Theorem b64_orient_apf_decides_int :
  forall P0 P1 Q : BPoint,
    orient2d_inputs_int_safe P0 P1 Q ->
    b64_orient2d_expansion_safe P0 P1 Q ->
       (b64_orient_apf P0 P1 Q = OrientRPos  <-> 0 < cross_R_BP P0 P1 Q)
    /\ (b64_orient_apf P0 P1 Q = OrientRNeg  <-> cross_R_BP P0 P1 Q < 0)
    /\ (b64_orient_apf P0 P1 Q = OrientRZero <-> cross_R_BP P0 P1 Q = 0).
Proof.
  intros P0 P1 Q Hint Hexp.
  pose proof (b64_orient_apf_sound_int P0 P1 Q Hint Hexp) as Hsound.
  pose proof (b64_orient_apf_decisive P0 P1 Q) as Hdec.
  (* Name the verdict; the three targets follow from the trichotomy of the   *)
  (* real determinant against the (mutually exclusive) verdict cases.        *)
  destruct Hdec as [Hv | [Hv | Hv]]; rewrite Hv in Hsound |- *;
    repeat split; intro H; try exact Hsound; try (exfalso; lra);
    try discriminate;
    (* remaining backward directions: the hypothesised real order forces the *)
    (* verdict, contradicting a different assumed verdict.                    *)
    exfalso; lra.
Qed.

(* ========================================================================== *)
(* §2  Track Y -- the witness algebra.                                        *)
(* ========================================================================== *)

(* -------------------------------------------------------------------------- *)
(* Y.1  Provenance certificate.  `apf_witness` records the deciding stratum   *)
(* together with its raw verdict; `apf_stratum` is the coarse provenance tag. *)
(* -------------------------------------------------------------------------- *)

Inductive apf_stratum : Type :=
| APF_FilterA        (* Stratum A -- the ulp-bounded fast filter committed.  *)
| APF_ExpansionD.    (* Stratum D -- the certified expansion switch fired.   *)

Inductive apf_witness : Type :=
| AWFilter    (s : orient_sign_robust)   (* filter's committed verdict.      *)
| AWExpansion (e : expansion_sign).      (* the exact expansion sign.        *)

Definition apf_stratum_of (w : apf_witness) : apf_stratum :=
  match w with
  | AWFilter _    => APF_FilterA
  | AWExpansion _ => APF_ExpansionD
  end.

Definition apf_decode (w : apf_witness) : orient_sign_robust :=
  match w with
  | AWFilter s    => s
  | AWExpansion e => expansion_sign_to_orient_robust e
  end.

Definition apf_run (P0 P1 Q : BPoint) : apf_witness :=
  match b64_orient_sign_filtered P0 P1 Q with
  | OrientRPos       => AWFilter OrientRPos
  | OrientRNeg       => AWFilter OrientRNeg
  | OrientRZero      => AWFilter OrientRZero
  | OrientRUncertain => AWExpansion (b64_orient2d_expansion_sign P0 P1 Q)
  | OrientRNan       => AWExpansion (b64_orient2d_expansion_sign P0 P1 Q)
  end.

(* -------------------------------------------------------------------------- *)
(* Y.2  Coherence: decoding the witness reproduces the stratified decoder.    *)
(* -------------------------------------------------------------------------- *)

Theorem apf_decode_run :
  forall P0 P1 Q,
    apf_decode (apf_run P0 P1 Q) = b64_orient_apf P0 P1 Q.
Proof.
  intros P0 P1 Q.
  unfold apf_decode, apf_run, b64_orient_apf, b64_orient_sign_stage_d,
         b64_orient_sign_exact.
  destruct (b64_orient_sign_filtered P0 P1 Q); reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Y.3  Decidable provenance: Stratum A is the decider EXACTLY when the       *)
(* filter committed; otherwise the certified expansion switch fired.          *)
(* -------------------------------------------------------------------------- *)

Theorem apf_stratum_filter_iff_committed :
  forall P0 P1 Q,
    apf_stratum_of (apf_run P0 P1 Q) = APF_FilterA
    <-> (   b64_orient_sign_filtered P0 P1 Q = OrientRPos
         \/ b64_orient_sign_filtered P0 P1 Q = OrientRNeg
         \/ b64_orient_sign_filtered P0 P1 Q = OrientRZero).
Proof.
  intros P0 P1 Q.
  unfold apf_stratum_of, apf_run.
  destruct (b64_orient_sign_filtered P0 P1 Q); split; intro H;
    try (now (left + (right; left) + (right; right)));
    try reflexivity;
    destruct H as [H | [H | H]]; discriminate.
Qed.

Theorem apf_stratum_switch_iff_indefinite :
  forall P0 P1 Q,
    apf_stratum_of (apf_run P0 P1 Q) = APF_ExpansionD
    <-> (   b64_orient_sign_filtered P0 P1 Q = OrientRUncertain
         \/ b64_orient_sign_filtered P0 P1 Q = OrientRNan).
Proof.
  intros P0 P1 Q.
  unfold apf_stratum_of, apf_run.
  destruct (b64_orient_sign_filtered P0 P1 Q); split; intro H;
    try (now (left + right));
    try reflexivity;
    destruct H as [H | H]; discriminate.
Qed.

(* -------------------------------------------------------------------------- *)
(* Y.4  Witness soundness: the decoded certificate meets the exact spec.      *)
(* -------------------------------------------------------------------------- *)

Theorem apf_run_sound_int :
  forall P0 P1 Q : BPoint,
    orient2d_inputs_int_safe P0 P1 Q ->
    b64_orient2d_expansion_safe P0 P1 Q ->
    match apf_decode (apf_run P0 P1 Q) with
    | OrientRPos       => 0 < cross_R_BP P0 P1 Q
    | OrientRNeg       => cross_R_BP P0 P1 Q < 0
    | OrientRZero      => cross_R_BP P0 P1 Q = 0
    | OrientRNan       => True
    | OrientRUncertain => True
    end.
Proof.
  intros P0 P1 Q Hint Hexp.
  rewrite apf_decode_run.
  apply b64_orient_apf_sound_int; assumption.
Qed.

(* -------------------------------------------------------------------------- *)
(* Y.5  The sign involutions and the homomorphism law.                        *)
(*                                                                            *)
(* Orientation flips sign when the first two arguments are swapped.  We give  *)
(* the negation as an involution on each verdict type and prove `apf_decode`  *)
(* a homomorphism for it: decoding commutes with negation.  This is the       *)
(* algebraic skeleton; Y.7 connects it to the geometry.                       *)
(* -------------------------------------------------------------------------- *)

Definition sign_robust_neg (s : orient_sign_robust) : orient_sign_robust :=
  match s with
  | OrientRPos       => OrientRNeg
  | OrientRNeg       => OrientRPos
  | OrientRZero      => OrientRZero
  | OrientRNan       => OrientRNan
  | OrientRUncertain => OrientRUncertain
  end.

Definition expansion_sign_neg (e : expansion_sign) : expansion_sign :=
  match e with
  | ExpPos  => ExpNeg
  | ExpNeg  => ExpPos
  | ExpZero => ExpZero
  end.

Definition apf_witness_neg (w : apf_witness) : apf_witness :=
  match w with
  | AWFilter s    => AWFilter (sign_robust_neg s)
  | AWExpansion e => AWExpansion (expansion_sign_neg e)
  end.

Lemma sign_robust_neg_involutive :
  forall s, sign_robust_neg (sign_robust_neg s) = s.
Proof. intros s; destruct s; reflexivity. Qed.

Lemma expansion_sign_neg_involutive :
  forall e, expansion_sign_neg (expansion_sign_neg e) = e.
Proof. intros e; destruct e; reflexivity. Qed.

Lemma apf_witness_neg_involutive :
  forall w, apf_witness_neg (apf_witness_neg w) = w.
Proof.
  intros [s | e]; simpl.
  - rewrite sign_robust_neg_involutive; reflexivity.
  - rewrite expansion_sign_neg_involutive; reflexivity.
Qed.

(* `apf_stratum_of` is invariant under negation: flipping a verdict never    *)
(* changes which stratum produced it.                                         *)
Lemma apf_stratum_of_neg :
  forall w, apf_stratum_of (apf_witness_neg w) = apf_stratum_of w.
Proof. intros [s | e]; reflexivity. Qed.

(* The homomorphism law: `apf_decode` intertwines the witness-level and       *)
(* verdict-level negations.                                                    *)
Theorem apf_decode_neg :
  forall w, apf_decode (apf_witness_neg w) = sign_robust_neg (apf_decode w).
Proof.
  intros [s | e]; simpl.
  - reflexivity.
  - destruct e; reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Y.6  Geometric antisymmetry of the exact spec -- a pure `ring` identity.   *)
(* -------------------------------------------------------------------------- *)

Lemma cross_R_BP_swap01 :
  forall P0 P1 Q, cross_R_BP P1 P0 Q = - cross_R_BP P0 P1 Q.
Proof. intros P0 P1 Q; unfold cross_R_BP; ring. Qed.

(* `orient2d_inputs_int_safe` is symmetric in P0/P1: it only asserts that the *)
(* six coordinates are integer-safe, and swapping P0,P1 permutes the six      *)
(* conjuncts.                                                                  *)
Lemma orient2d_inputs_int_safe_swap01 :
  forall P0 P1 Q,
    orient2d_inputs_int_safe P0 P1 Q ->
    orient2d_inputs_int_safe P1 P0 Q.
Proof. intros P0 P1 Q; unfold orient2d_inputs_int_safe; tauto. Qed.

(* -------------------------------------------------------------------------- *)
(* Y.7  Argument-swap antisymmetry of the decoder.  The witness-algebra       *)
(* involution (Y.5) is realised, on the decoded verdict, by swapping the      *)
(* first two arguments -- the geometric orientation flip.  Because the        *)
(* expansion-safety predicate is about a specific arithmetic chain, it is     *)
(* required for the swapped ordering too (it is not derivable from the        *)
(* original by symmetry).                                                      *)
(* -------------------------------------------------------------------------- *)

Theorem b64_orient_apf_antisym_int :
  forall P0 P1 Q : BPoint,
    orient2d_inputs_int_safe P0 P1 Q ->
    b64_orient2d_expansion_safe P0 P1 Q ->
    b64_orient2d_expansion_safe P1 P0 Q ->
    b64_orient_apf P1 P0 Q = sign_robust_neg (b64_orient_apf P0 P1 Q).
Proof.
  intros P0 P1 Q Hint Hexp Hexp'.
  pose proof (orient2d_inputs_int_safe_swap01 _ _ _ Hint) as Hint'.
  destruct (b64_orient_apf_decides_int P0 P1 Q Hint Hexp)
    as [Hpos [Hneg Hzero]].
  destruct (b64_orient_apf_decides_int P1 P0 Q Hint' Hexp')
    as [Hpos' [Hneg' Hzero']].
  pose proof (cross_R_BP_swap01 P0 P1 Q) as Hswap.
  (* Case on the (decisive) verdict for the original ordering. *)
  destruct (b64_orient_apf_decisive P0 P1 Q) as [Hv | [Hv | Hv]];
    rewrite Hv; simpl.
  - (* original Pos => 0 < cross(P0P1Q) => cross(P1P0Q) < 0 => swapped Neg. *)
    assert (Hc : 0 < cross_R_BP P0 P1 Q) by (apply Hpos; exact Hv).
    apply Hneg'. lra.
  - (* original Neg => cross(P0P1Q) < 0 => cross(P1P0Q) > 0 => swapped Pos. *)
    assert (Hc : cross_R_BP P0 P1 Q < 0) by (apply Hneg; exact Hv).
    apply Hpos'. lra.
  - (* original Zero => cross(P0P1Q) = 0 => cross(P1P0Q) = 0 => swapped Zero. *)
    assert (Hc : cross_R_BP P0 P1 Q = 0) by (apply Hzero; exact Hv).
    apply Hzero'. lra.
Qed.

(* ========================================================================== *)
(* §3  Track Z -- extraction handle + benchmark (see companion + docs).       *)
(* ========================================================================== *)

(* `b64_orient_apf` / `apf_run` are pure binary64 recursion.  Under the       *)
(* native-float extraction (`Extract Constant Bplus/Bminus/Bmult/Bcompare`,   *)
(* already set up in `Validate_binary64_extract.v`), Stratum A becomes three  *)
(* multiply / subtract ops plus one comparison -- the same code path the      *)
(* shipped oracle already extracts as `b64_orient_sign_filtered`.  Stratum D  *)
(* (the fast-expansion-sum path) additionally needs the B2R-based             *)
(* `sign_of_expansion` replaced by its native head-first component scan; that *)
(* Extract Constant, the oracle wiring, and the ulp-hit-rate benchmark        *)
(* protocol against NetTopologySuite `RobustDeterminant` / `Orientation.Index`*)
(* are documented in `docs/orient-stratified-apf.md`.                         *)

(* -------------------------------------------------------------------------- *)
(* Assumption audit.                                                          *)
(* -------------------------------------------------------------------------- *)

Print Assumptions b64_orient_apf_fast_path.
Print Assumptions b64_orient_apf_decisive.
Print Assumptions b64_orient_sign_exact_sound_int.
Print Assumptions b64_orient_apf_sound_int.
Print Assumptions b64_orient_apf_decides_int.
Print Assumptions apf_decode_run.
Print Assumptions apf_stratum_filter_iff_committed.
Print Assumptions apf_stratum_switch_iff_indefinite.
Print Assumptions apf_run_sound_int.
Print Assumptions apf_decode_neg.
Print Assumptions apf_witness_neg_involutive.
Print Assumptions b64_orient_apf_antisym_int.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)
Print Assumptions b64_orient_apf_unfold.
Print Assumptions b64_orient_apf_never_nan.
Print Assumptions b64_orient_apf_never_uncertain.
Print Assumptions sign_robust_neg_involutive.
Print Assumptions expansion_sign_neg_involutive.
Print Assumptions apf_stratum_of_neg.
Print Assumptions cross_R_BP_swap01.
Print Assumptions orient2d_inputs_int_safe_swap01.

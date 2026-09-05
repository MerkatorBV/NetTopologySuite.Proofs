(* ============================================================================
   NetTopologySuite.Proofs.Flocq.B64_Overlap_Hierarchy
   ----------------------------------------------------------------------------
   Shewchuk's nonoverlapping relation, the one-bit-slack relaxation Shewchuk
   attributes to Priest, and where the corpus's own predicate sits between
   them.

   CONTEXT.  `fast_expansion_sum_nonoverlap_shewchuk` is archived
   false-as-stated (RESOLVED-VIA-ABORT, Qed-closed disproof in
   B64_Shewchuk_Thm13_counterexample.v).  Its Abort note says: "To recover a
   TRUE general headline, weaken nonoverlap_strict to the bit-disjoint
   predicate and re-aim the pathA-OR-pathB obligations."

   A NAMING CORRECTION, deliberate.  That note says "bit-disjoint", but the
   relation Shewchuk actually defines is NOT disjointness of bit positions --
   it is a statement about bit RANGES.  Formally (1997 p. 309 n. 2):

     "x and y are nonoverlapping if there exist integers r and s such that
      x = r 2^s and |y| < 2^s, or y = r 2^s and |x| < 2^s."

   Take x = 2^8 + 1 and y = 2^4.  No bit position is shared, so they are
   bit-disjoint in the naive sense; but x is odd, forcing s = 0, and
   |y| = 16 < 2^0 fails.  They OVERLAP in Shewchuk's sense.  This module
   therefore uses `nonoverlapping`, matching the paper, and does not repeat
   the Abort note's wording.

   PHILOSOPHY (do not overclaim).  This file does NOT prove that
   `fast_expansion_sum` preserves anything; `fast_expansion_sum` does not
   appear in it.  The lane's stop condition (QED or QEX) is NOT met here --
   what is delivered is the predicate layer that a preservation attempt needs,
   plus the measured separations between the three predicates.  See
   docs/thm13-priest-route.md, which also records that obtaining Priest 1991
   is the first task on this route; it has not been obtained.

   Nor does this file reproduce Priest's theorem.  `overlap_within 1` is the
   corpus's reading of ONE SENTENCE of Shewchuk's prose about Priest, and
   docs/audit-phase3-overlay.md already records that Priest works in a
   different basis ("exponents differing by at least p").  A one-place slack
   on Shewchuk's footnote-2 exponent is a plausible rendering, not a derived
   one, and it is named `overlap_within 1` rather than anything with "Priest"
   in it for exactly that reason.

   What IS established, all Qed:

     strict_succ (half-ulp)  =>  nonoverlapping  =>  overlap_within 1
           corpus's own            Shewchuk n.2         one-bit slack

   with BOTH links shown strict by explicit witnesses:
     - (256, 1)   fails strict_succ, satisfies nonoverlapping
                  -- the pair that refuted the Theorem 13 headline;
     - (256, 256) fails nonoverlapping, satisfies overlap_within 1.

   AXIOM FOOTPRINT.  Audited by the `Print Assumptions` block at the end of
   this file, not by prose.  Results that touch the binary64 format layer
   carry `Classical_Prop.classic`; this is inherited, not introduced --
   `b64_format_B2R` (= Flocq's `generic_format_B2R`), `b64_ulp_FLT_0` and the
   existing `strict_succ_b64_256_1_false` each already carry it in this build.
   The module is listed in docs/audit-exceptions.txt for that reason.  The
   purely arithmetic results below are clean of it.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals ZArith Lia Lra List.
From Flocq Require Import IEEE754.Binary Core Ulp.
From NTS.Proofs.Flocq Require Import Validate_binary64 B64_lib
     B64_Expansion B64_Expansion_Shewchuk B64_Shewchuk_Thm13_counterexample.

Import ListNotations.
Open Scope R_scope.

(* --------------------------------------------------------------------------
   The relation, parameterised by how much slack is allowed.

   `k = 0` is Shewchuk's nonoverlapping; `k = 1` is the one-bit-slack form.
   One definition rather than two near-identical ones, so the rung lemma is
   monotonicity in `k` instead of a copied proof.

   Symmetric in x and y, as Shewchuk's is: the corpus's descending-magnitude
   convention decides which branch fires, not which one is meaningful.
   -------------------------------------------------------------------------- *)

Definition overlap_within (k : Z) (x y : R) : Prop :=
  (exists r s : Z, x = IZR r * bpow radix2 s /\ Rabs y < bpow radix2 (s + k))
  \/
  (exists r s : Z, y = IZR r * bpow radix2 s /\ Rabs x < bpow radix2 (s + k)).

Definition nonoverlapping_R (x y : R) : Prop := overlap_within 0 x y.

Definition nonoverlapping_b64 (a b : binary64) : Prop :=
  nonoverlapping_R (Binary.B2R prec emax a) (Binary.B2R prec emax b).

Definition overlap_within_b64 (k : Z) (a b : binary64) : Prop :=
  overlap_within k (Binary.B2R prec emax a) (Binary.B2R prec emax b).

(* Chain form, mirroring `nonoverlap_strict`'s shape and convention. *)
Fixpoint nonoverlapping_chain (e : b64_expansion) : Prop :=
  match e with
  | nil => True
  | _ :: nil => True
  | a :: (b :: _) as rest =>
      nonoverlapping_b64 a b /\ nonoverlapping_chain rest
  end.

(* Slack is monotone: more slack is a weaker requirement. *)
Lemma overlap_within_mono :
  forall (k1 k2 : Z) (x y : R),
    (k1 <= k2)%Z -> overlap_within k1 x y -> overlap_within k2 x y.
Proof.
  intros k1 k2 x y Hk [ [r [s [Hx Hy]]] | [r [s [Hy Hx]]] ].
  - left. exists r, s. split; [ exact Hx | ].
    eapply Rlt_le_trans; [ exact Hy | apply bpow_le; lia ].
  - right. exists r, s. split; [ exact Hy | ].
    eapply Rlt_le_trans; [ exact Hx | apply bpow_le; lia ].
Qed.

(* --------------------------------------------------------------------------
   RUNG 1 -- the corpus's half-ulp bound implies nonoverlapping.

   This is the relationship the whole Theorem 13 terminology confusion turned
   on, previously asserted only in a comment on `nonoverlap_strict`.

   Witness: every binary64 is a multiple of its own ulp, so take 2^s = ulp(a).
   The half-ulp bound then gives |b| <= 2^s/2 < 2^s.
   -------------------------------------------------------------------------- *)

Lemma strict_succ_b64_nonoverlapping :
  forall a b : binary64, strict_succ_b64 a b -> nonoverlapping_b64 a b.
Proof.
  intros a b Hss.
  unfold strict_succ_b64 in Hss.
  unfold nonoverlapping_b64, nonoverlapping_R, overlap_within.
  left.
  (* Case split via `total_order_T`, decidable from the Reals order axioms.
     This does not lower the module's footprint -- `classic` enters through
     the format layer regardless -- but the constructive form is the honest
     one where it costs nothing. *)
  assert (Hdec : Binary.B2R prec emax a = 0 \/ Binary.B2R prec emax a <> 0).
  { destruct (total_order_T (Binary.B2R prec emax a) 0) as [[H | H] | H];
      [ right; lra | left; exact H | right; lra ]. }
  destruct Hdec as [Ha0 | Han0].
  - (* a = 0: ulp(0) = bpow emin, and 0 = 0 * 2^emin.  Shewchuk p. 309:
       "The number zero does not overlap any number." *)
    exists 0%Z, b64_emin.
    rewrite Ha0 in *.
    change (ulp radix2 (SpecFloat.fexp prec emax) 0) with (b64_ulp 0) in Hss.
    rewrite b64_ulp_FLT_0 in Hss.
    rewrite Z.add_0_r.
    split.
    + simpl. lra.
    + pose proof (bpow_gt_0 radix2 b64_emin) as Hpos. lra.
  - (* a <> 0: a is a multiple of ulp(a) = bpow (cexp a). *)
    pose proof (b64_format_B2R a) as Hfmt.
    unfold b64_format, generic_format in Hfmt.
    exists (Ztrunc (scaled_mantissa radix2 b64_fexp (Binary.B2R prec emax a))),
           (cexp radix2 b64_fexp (Binary.B2R prec emax a)).
    rewrite Z.add_0_r.
    split.
    + rewrite Hfmt at 1. unfold F2R. simpl. reflexivity.
    + assert (Hulp : ulp radix2 (SpecFloat.fexp prec emax)
                       (Binary.B2R prec emax a)
                     = bpow radix2 (cexp radix2 b64_fexp
                                      (Binary.B2R prec emax a))).
      { apply ulp_neq_0. exact Han0. }
      rewrite Hulp in Hss.
      pose proof (bpow_gt_0 radix2
                    (cexp radix2 b64_fexp (Binary.B2R prec emax a))) as Hpos.
      lra.
Qed.

Lemma nonoverlap_strict_chain :
  forall e : b64_expansion,
    nonoverlap_strict e -> nonoverlapping_chain e.
Proof.
  induction e as [| a e' IH]; [ simpl; trivial | ].
  destruct e' as [| b e'']; [ simpl; trivial | ].
  intros [Hss Hrest].
  simpl. split.
  - apply strict_succ_b64_nonoverlapping. exact Hss.
  - apply IH. exact Hrest.
Qed.

(* --------------------------------------------------------------------------
   RUNG 2 -- nonoverlapping implies the one-bit-slack form.

   Immediate from monotonicity.  Kept as a named lemma because it is the rung
   the Priest route actually aims at, and because its STRICTNESS below is the
   part that carries content.
   -------------------------------------------------------------------------- *)

Lemma nonoverlapping_overlap_within_1 :
  forall a b : binary64,
    nonoverlapping_b64 a b -> overlap_within_b64 1 a b.
Proof.
  intros a b H.
  apply (overlap_within_mono 0 1); [ lia | exact H ].
Qed.

Lemma strict_succ_overlap_within_1 :
  forall a b : binary64,
    strict_succ_b64 a b -> overlap_within_b64 1 a b.
Proof.
  intros a b H.
  apply nonoverlapping_overlap_within_1, strict_succ_b64_nonoverlapping, H.
Qed.

(* --------------------------------------------------------------------------
   WITNESS 1 -- rung 1 is strict.

   (256, 1) is the pair the Theorem 13 counterexample produces: the output of
   `fast_expansion_sum` on valid inputs compresses to [256; 1], which fails
   `strict_succ_b64` (1 > ulp(256)/2 = 2^-45).  Under Shewchuk's definition
   it is perfectly nonoverlapping: 256 = 1 * 2^8 and |1| < 2^8.
   -------------------------------------------------------------------------- *)

Lemma nonoverlapping_b64_256_1 : nonoverlapping_b64 b256 b1.
Proof.
  unfold nonoverlapping_b64, nonoverlapping_R, overlap_within.
  left.
  exists 1%Z, 8%Z.
  rewrite b256_R, b1_R, Z.add_0_r.
  split.
  - simpl. rewrite Rmult_1_l. reflexivity.
  - rewrite Rabs_right.
    + apply bpow_lt. lia.
    + pose proof (bpow_gt_0 radix2 0) as H. lra.
Qed.

(* --------------------------------------------------------------------------
   WITNESS 2 -- rung 2 is strict.

   (256, 256) separates nonoverlapping from the one-bit-slack form.  It sits
   inside the slack (|256| < 2^9) but not inside nonoverlapping: writing
   256 = r * 2^s forces s <= 8 (r must be an integer), while |256| < 2^s
   forces s >= 9.

   Without this witness the two predicates could coincide and the "hierarchy"
   would be a chain of possible equalities.
   -------------------------------------------------------------------------- *)

Lemma b256_not_scaled_above_8 :
  forall r s : Z,
    bpow radix2 8 = IZR r * bpow radix2 s ->
    Rabs (bpow radix2 8) < bpow radix2 s ->
    False.
Proof.
  intros r s Heq Hlt.
  (* |2^8| = 2^8, so the bound says 2^8 < 2^s, hence 8 < s. *)
  rewrite Rabs_right in Hlt;
    [ | pose proof (bpow_gt_0 radix2 8) as H; lra ].
  assert (Hs : (8 < s)%Z) by (apply (lt_bpow radix2); exact Hlt).
  (* From the equation, IZR r = 2^(8-s), which lies strictly in (0,1). *)
  assert (Hr : IZR r = bpow radix2 (8 - s)).
  { pose proof (bpow_gt_0 radix2 s) as Hps.
    apply (Rmult_eq_reg_r (bpow radix2 s)); [ | lra ].
    rewrite <- bpow_plus.
    replace (8 - s + s)%Z with 8%Z by lia.
    lra. }
  assert (H0 : 0 < IZR r) by (rewrite Hr; apply bpow_gt_0).
  assert (H1 : IZR r < 1).
  { rewrite Hr. change 1 with (bpow radix2 0). apply bpow_lt. lia. }
  (* No integer lies strictly between 0 and 1. *)
  assert (Hr0 : (0 < r)%Z) by (apply lt_IZR; simpl; lra).
  assert (Hr1 : (r < 1)%Z) by (apply lt_IZR; simpl; lra).
  lia.
Qed.

Lemma nonoverlapping_b64_256_256_false : ~ nonoverlapping_b64 b256 b256.
Proof.
  unfold nonoverlapping_b64, nonoverlapping_R, overlap_within.
  rewrite b256_R.
  (* `s + 0` sits under the existential binder, so it is folded away in the
     hypothesis after intro rather than in the goal. *)
  intros [ [r [s [Heq Hlt]]] | [r [s [Heq Hlt]]] ];
    rewrite Z.add_0_r in Hlt;
    exact (b256_not_scaled_above_8 r s Heq Hlt).
Qed.

Lemma overlap_within_1_256_256 : overlap_within_b64 1 b256 b256.
Proof.
  unfold overlap_within_b64, overlap_within.
  left.
  exists 1%Z, 8%Z.
  rewrite b256_R.
  split.
  - simpl. rewrite Rmult_1_l. reflexivity.
  - rewrite Rabs_right;
      [ | pose proof (bpow_gt_0 radix2 8) as H; lra ].
    apply bpow_lt. lia.
Qed.

(* --------------------------------------------------------------------------
   The headline: the ordering holds and is strict at BOTH links.

   This is deliberately modest.  It says the Priest-side target is neither
   vacuous nor already implied by the corpus's predicate, and that the witness
   which killed the Shewchuk-side headline does not kill it.  It says nothing
   about `fast_expansion_sum`.
   -------------------------------------------------------------------------- *)

Theorem predicate_hierarchy_strict :
  (* the ordering *)
  (forall a b : binary64, strict_succ_b64 a b -> nonoverlapping_b64 a b)
  /\ (forall a b : binary64,
        nonoverlapping_b64 a b -> overlap_within_b64 1 a b)
  (* strict at link 1: the Theorem 13 witness *)
  /\ (~ strict_succ_b64 b256 b1) /\ nonoverlapping_b64 b256 b1
  (* strict at link 2 *)
  /\ (~ nonoverlapping_b64 b256 b256) /\ overlap_within_b64 1 b256 b256.
Proof.
  repeat split.
  - exact strict_succ_b64_nonoverlapping.
  - exact nonoverlapping_overlap_within_1.
  - exact strict_succ_b64_256_1_false.
  - exact nonoverlapping_b64_256_1.
  - exact nonoverlapping_b64_256_256_false.
  - exact overlap_within_1_256_256.
Qed.

(* The same fact over the expansion the counterexample actually produces. *)
Theorem thm13_witness_nonoverlapping :
  ~ nonoverlap_shewchuk [b256; b1] /\ nonoverlapping_chain [b256; b1].
Proof.
  split.
  - exact nonoverlap_shewchuk_256_1_false.
  - simpl. split; [ exact nonoverlapping_b64_256_1 | trivial ].
Qed.

(* --------------------------------------------------------------------------
   Assumption audit.

   House convention (see B64_Shewchuk_Thm13_counterexample.v): every headline
   emits its footprint so `scripts/audit_axioms.sh` reads it from the build
   log rather than from a comment.
   -------------------------------------------------------------------------- *)

Print Assumptions overlap_within_mono.
Print Assumptions nonoverlapping_overlap_within_1.
Print Assumptions nonoverlapping_b64_256_1.
Print Assumptions b256_not_scaled_above_8.
Print Assumptions nonoverlapping_b64_256_256_false.
Print Assumptions overlap_within_1_256_256.
Print Assumptions strict_succ_b64_nonoverlapping.
Print Assumptions nonoverlap_strict_chain.
Print Assumptions strict_succ_overlap_within_1.
Print Assumptions predicate_hierarchy_strict.
Print Assumptions thm13_witness_nonoverlapping.

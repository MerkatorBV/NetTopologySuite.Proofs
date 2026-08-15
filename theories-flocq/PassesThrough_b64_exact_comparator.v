(* ============================================================================
   NetTopologySuite.Proofs.Flocq.PassesThrough_b64_exact_comparator
   ----------------------------------------------------------------------------
   Issue #66 round 2, item 2, rung (a): the EXACT INTEGER-DETERMINANT
   comparator for Liang-Barsky rational t-bounds, replacing the forward-error
   ("gap beats the rounding band") argument that closed C1 unconditionally
   only up to the tight grid |n| <= 2^22 (PassesThrough_b64_grid_exact.v,
   slices 12-18) and is PROVABLY insufficient at the full coord_int_safe
   width |n| <= 2^25 (the determinant gap can fall to ~2^-54, below the
   rounding band ~2^-52 -- see docs/audit-rgr-comparison.md P6).

   THE POINT.  Every t-bound this file's LB algebra ever compares is an
   exact rational `IZR na / IZR da` for INTEGERS na, da (the `gridbound`
   witnesses already extracted in PassesThrough_b64_grid_exact.v's slices
   12-18, e.g. `m / (2 * n)` forms).  Comparing TWO such rationals by
   CROSS-MULTIPLICATION in Z is exact -- no rounding, no forward-error bound,
   no width limit at all.  `rat_le` below decides `na/da <= nb/db` this way,
   and `rat_le_iff` proves it correct UNCONDITIONALLY (for any nonzero
   denominators, any magnitude, any sign).

   WHAT THIS DOES NOT YET CLOSE.  The actual computational filter
   (`b64_passes_through_hot_pixel_compute`) does not run `rat_le` -- it
   rounds each t-bound to a binary64 via `b64_div` and compares the ROUNDED
   floats (`b64_le`).  By monotonicity of correctly-rounded division
   (`round` is order-preserving, `Flocq.Core.Generic_fmt.round_le`), the
   ONLY way `b64_le (b64_round a) (b64_round b)` can disagree with
   `rat_le`'s exact verdict on `a <= b` is a ROUNDING TIE: `a <> b` as exact
   reals yet `b64_round a = b64_round b` as binary64 values. Ruling that out
   for the specific achievable LB-quotient family at the full |n| <= 2^25
   width is the genuine remaining obligation (P6's "exact integer-determinant
   comparison" was never a synonym for "avoid computing with floats" -- it
   is this comparator PLUS a tie-freeness argument the comparator alone does
   not supply). An empirical sweep (~1.7M adversarially-constructed
   worst-case-gap trials at the theoretical minimum spacing `1/(4|na db|)`
   for denominators up to 2^27, plus a binade-boundary-targeted pass) found
   NO tie, but that is evidence, not a proof; this file does not claim the
   tie-freeness result and adds no `Admitted` for it. Re-deriving
   `b64_passes_through_grid_exact` (the |n| <= 2^22 headline) through this
   comparator instead of the forward-error route, and then widening, is
   future work gated on that lemma.

   No `Admitted` / `Axiom` / `Parameter`; allowlist axioms only.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
   ========================================================================== *)

From Stdlib Require Import Reals ZArith Lra Lia.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  The positive-denominator case: the textbook cross-multiplication.      *)
(* -------------------------------------------------------------------------- *)

Lemma Rdiv_le_iff_pos_denoms :
  forall a p c q : R, 0 < p -> 0 < q -> (a / p <= c / q <-> a * q <= c * p)%R.
Proof.
  intros a p c q Hp Hq.
  assert (Hpq : (0 < p * q)%R) by nra.
  split; intro H.
  - apply (Rmult_le_compat_r (p * q)) in H; [ | lra ].
    unfold Rdiv in H.
    replace (a * / p * (p * q))%R with (a * q * (/ p * p))%R in H by ring.
    replace (c * / q * (p * q))%R with (c * p * (/ q * q))%R in H by ring.
    rewrite Rinv_l in H by lra.
    rewrite Rinv_l in H by lra.
    lra.
  - apply (Rmult_le_reg_r (p * q)); [ exact Hpq | ].
    unfold Rdiv.
    replace (a * / p * (p * q))%R with (a * q * (/ p * p))%R by ring.
    replace (c * / q * (p * q))%R with (c * p * (/ q * q))%R by ring.
    rewrite Rinv_l by lra.
    rewrite Rinv_l by lra.
    lra.
Qed.

Lemma Rdiv_eq_mul_sq : forall a p : R, p <> 0%R -> (a / p = (a * p) / (p * p))%R.
Proof. intros a p Hp. unfold Rdiv. field. exact Hp. Qed.

(* -------------------------------------------------------------------------- *)
(* §2  General signs, via the always-positive squared denominators: reduce    *)
(* `na/da <= nb/db` to a single common-sign-factor inequality                 *)
(* `(da*db)*(na*db) <= (da*db)*(nb*da)`, then case on the sign of `da*db`.    *)
(* -------------------------------------------------------------------------- *)

Lemma cross_mult_step :
  forall na da nb db : Z,
    da <> 0%Z -> db <> 0%Z ->
    (IZR na / IZR da <= IZR nb / IZR db)%R
      <-> (IZR (da * db) * IZR (na * db) <= IZR (da * db) * IZR (nb * da))%R.
Proof.
  intros na da nb db Hda Hdb.
  assert (HdaR : IZR da <> 0%R) by (apply IZR_neq; exact Hda).
  assert (HdbR : IZR db <> 0%R) by (apply IZR_neq; exact Hdb).
  assert (Hdada : (0 < IZR da * IZR da)%R) by nra.
  assert (Hdbdb : (0 < IZR db * IZR db)%R) by nra.
  rewrite (Rdiv_eq_mul_sq (IZR na) (IZR da) HdaR).
  rewrite (Rdiv_eq_mul_sq (IZR nb) (IZR db) HdbR).
  rewrite (Rdiv_le_iff_pos_denoms (IZR na * IZR da) (IZR da * IZR da)
             (IZR nb * IZR db) (IZR db * IZR db) Hdada Hdbdb).
  rewrite !mult_IZR.
  split; intro H; nra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  The exact integer-determinant comparator.                              *)
(* -------------------------------------------------------------------------- *)

(* `na/da <= nb/db`, decided by cross-multiplication.  The direction of the
   cross-multiplied inequality flips exactly when `da*db < 0` (one
   denominator negative, the other positive); `Z.ltb 0 (da*db)` picks the
   right branch without needing the signs of `da`, `db` individually. *)
Definition rat_le (na da nb db : Z) : bool :=
  if Z.ltb 0%Z (da * db)%Z then Z.leb (na * db)%Z (nb * da)%Z
                            else Z.leb (nb * da)%Z (na * db)%Z.

Theorem rat_le_iff :
  forall na da nb db : Z,
    da <> 0%Z -> db <> 0%Z ->
    (rat_le na da nb db = true <-> (IZR na / IZR da <= IZR nb / IZR db)%R).
Proof.
  intros na da nb db Hda Hdb.
  pose proof (cross_mult_step na da nb db Hda Hdb) as Hcross.
  rewrite !mult_IZR in Hcross.
  unfold rat_le.
  destruct (Z.ltb_spec0 0%Z (da * db)%Z) as [Hpos | Hnonpos].
  - assert (HposR : (0 < IZR da * IZR db)%R)
      by (rewrite <- mult_IZR; apply IZR_lt; exact Hpos).
    rewrite Z.leb_le, Hcross.
    split; intro H.
    + apply IZR_le in H. rewrite !mult_IZR in H.
      apply Rmult_le_compat_l; [ lra | exact H ].
    + apply le_IZR. rewrite !mult_IZR.
      apply (Rmult_le_reg_l (IZR da * IZR db)); [ lra | exact H ].
  - assert (Hneg : (da * db < 0)%Z) by lia.
    assert (HnegR : (0 < - (IZR da * IZR db))%R)
      by (rewrite <- mult_IZR; apply IZR_lt in Hneg; lra).
    rewrite Z.leb_le, Hcross.
    split; intro H.
    + apply IZR_le in H. rewrite !mult_IZR in H.
      (* H : IZR nb * IZR da <= IZR na * IZR db; want
         (IZR da*IZR db) * (IZR na*IZR db) <= (IZR da*IZR db) * (IZR nb*IZR da),
         i.e. (-K)*A <= (-K)*B for K = -(IZR da*IZR db) > 0, A = IZR na*IZR db,
         B = IZR nb*IZR da, B <= A -- so K*B <= K*A by Rmult_le_compat_l. *)
      assert (H1 : (- (IZR da * IZR db)) * (IZR nb * IZR da)
                     <= (- (IZR da * IZR db)) * (IZR na * IZR db))
        by (apply Rmult_le_compat_l; lra).
      lra.
    + apply le_IZR. rewrite !mult_IZR.
      assert (H1 : (- (IZR da * IZR db)) * (IZR nb * IZR da)
                     <= (- (IZR da * IZR db)) * (IZR na * IZR db)) by lra.
      apply (Rmult_le_reg_l (- (IZR da * IZR db))); [ lra | exact H1 ].
Qed.

(* -------------------------------------------------------------------------- *)
(* Axiom audit.  Pure Z/R rational algebra; allowlist axioms only.            *)
(* -------------------------------------------------------------------------- *)

Print Assumptions cross_mult_step.
Print Assumptions rat_le_iff.

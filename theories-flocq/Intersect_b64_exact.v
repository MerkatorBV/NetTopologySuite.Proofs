(* ============================================================================
   NetTopologySuite.Proofs.Flocq.Intersect_b64_exact
   ----------------------------------------------------------------------------
   Phase 1 first slice (Scope A): first-stage bit-exactness for the binary64
   intersection-point computation -- the prefix of the Cramer-rule chain
   that lands BEFORE the dividing step.

   Honest scoping note: the headline
       B2R (b64_intersect_point_x ...) = intersect_x_R ...
   does NOT hold on the nose in the integer regime, because the Cramer
   parameter `s = qp0 / den` is generally a non-dyadic rational (e.g.
   `1/3` when `qp0 = 1, den = 3`).  Round-chain identity (Scope B) and
   forward-error bound (Scope C) are queued as follow-up slices and
   documented at the foot of the file.

   What this file ships:

     - Total binary64 projections `b64_intersect_point_x` /
       `b64_intersect_point_y` (return `binary64`, not `option binary64`).
     - Safety predicate `intersect_point_inputs_int_safe` extending the
       existing `intersect_inputs_int_safe` (eight `coord_int_safe`
       premises) with the R-side denominator-non-zero condition.
     - R-side reference expressions: `intersect_param_s`, `intersect_x_R`,
       `intersect_y_R`.
     - First-stage exactness: the two outer orient2d evaluations
       (`qp0`, `qp1`) and the two coordinate differences (`dx`, `dy`)
       are bit-exact integer-valued binary64.
     - `HasIntersect` typeclass + `BPoint` instance: a minimal interface
       (operations + safety predicate, no proof fields) that future
       curve primitives -- e.g. arc-arc intersection with 3-control-point
       triplets -- can implement without forking the predicate layer.

   What this file does NOT ship (deferred -- see footer):

     - Denominator finite + B2R non-zero.  Needs an explicit no-overflow
       bound on `b64_minus qp0 qp1` (the difference of two cross products
       can hit 2^54, just above the 2^prec=2^53 exact-integer subtraction
       range; a bpow-54 chain via `b64_round_abs_le_bpow` discharges it).
     - Round-chain identity for the full `b64_intersect_point_x/y`
       (Scope B).
     - Forward-error bound (Scope C).

   PROOF STATUS
   ============
   - `intersect_point_inputs_int_safe`  -- safety predicate.
   - `b64_intersect_qp0_R` / `qp1_R`    -- two outer orient2d calls are
                                           bit-exact (cross-product on R).
   - `b64_intersect_dx_R` / `dy_R`      -- two coord differences are
                                           bit-exact integers and finite.
   - `cross_R_BP_int_witness`           -- (Scope B.1) cross_R_BP is an
                                           integer of magnitude <= 2^53.
   - `cross_R_BP_abs_le_bpow_53`        -- (Scope B.1) Rabs <= bpow 53.
   - `b64_intersect_qp0_finite` / `qp1_finite`
                                        -- (Scope B.1) the two outer
                                           orient2d calls are finite.
   - `b64_intersect_den_safe`           -- (Scope B.1) the denominator
                                           subtraction is no-overflow safe.
   - `b64_intersect_den_R_round`        -- (Scope B.1) B2R of the
                                           denominator equals b64_round
                                           of the R cross-product
                                           difference; finite.
   - `b64_intersect_den_B2R_nonzero`    -- (Scope B.1) the denominator's
                                           B2R is non-zero, so
                                           b64_div_correct's R-side
                                           premise is discharged.
   - `HasIntersect` typeclass + `BPoint` instance -- curve-extension hook.

   No `Admitted`, no `Axiom`, no `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude (Opus-4.7)

   SPLIT (2026-08-16): the Scope A / B.1 / B.2 / C.2-tight / Session-6
   layers now live in five layered modules --
   Intersect_b64_exact_core (Scope A + B.1), _round_chain (C.2-prep +
   the Scope B.2 round-chain headline + polish), _forward_error
   (C.2-tight Sessions 1-5 + y mirror), _bridge (Session 6 reference
   bridge + HasIntersect / HasIntersect_sound typeclasses), _tight
   (the parallel tight chain).  This file is the Require Export
   umbrella: every name is re-exported, so importers are unaffected.
   topic: binary64
   claimId: none
   ============================================================================ *)

From NTS.Proofs.Flocq Require Export Intersect_b64_exact_core.
From NTS.Proofs.Flocq Require Export Intersect_b64_exact_round_chain.
From NTS.Proofs.Flocq Require Export Intersect_b64_exact_forward_error.
From NTS.Proofs.Flocq Require Export Intersect_b64_exact_bridge.
From NTS.Proofs.Flocq Require Export Intersect_b64_exact_tight.

(* -------------------------------------------------------------------------- *)
(* Phase 1 deliverable map                                                    *)
(* -------------------------------------------------------------------------- *)
(*                                                                            *)
(* SHIPPED                                                                    *)
(*                                                                            *)
(* 1. Scope B.1 (denominator triple): `b64_intersect_den_safe`,               *)
(*    `b64_intersect_den_R_round`, `b64_intersect_den_B2R_nonzero`,           *)
(*    + magnitude bounds `_abs_le_bpow_54` / `_abs_ge_1`.                     *)
(*                                                                            *)
(* 2. Scope B.2 (round-chain identity, full):                                 *)
(*    `b64_intersect_point_x_round_chain` / `_y_round_chain` give the exact   *)
(*    nested-round identity                                                   *)
(*       B2R(b64_intersect_point_x ...)                                       *)
(*     = b64_round (B2R(bx P0)                                                *)
(*                  + b64_round (b64_round (qp0_R                             *)
(*                                          / b64_round (qp0_R - qp1_R))      *)
(*                              * (B2R(bx P1) - B2R(bx P0)))).                *)
(*    Supporting per-op safety+B2R-round lemmas for div / mult / plus also   *)
(*    in place (see `b64_intersect_s_R_round`, `_mult_*_safe`, `_plus_*_safe`)*)
(*                                                                            *)
(* 3. Scope C (polish + corollaries):                                         *)
(*    `b64_intersect_point_x_finite` / `_y_finite`,                           *)
(*    `_abs_le_bpow_81` / `_y_abs_le_bpow_81` (coarse magnitude),             *)
(*    `b64_intersect_point_returns_some_when_point` (Some-commits under safe).*)
(*                                                                            *)
(* 4. Scope C.2-tight (forward-error decomposition, x + y coordinates):       *)
(*    Four-layer cascade landed in five sessions S1-S5 for x, mirrored to y  *)
(*    in the refactor pass:                                                   *)
(*      Layer 1 (den):     `b64_intersect_den_forward_error`                  *)
(*                         <= bpow 1                                          *)
(*      Layer 2 (s):       `b64_intersect_s_forward_error`                    *)
(*                         <= 1 + bpow 54 / |qp0_R - qp1_R|                   *)
(*      Layer 3 (s*d_):    `b64_intersect_mult_{x,y}_forward_error`           *)
(*                         <= bpow 27 + bpow 26 + bpow 80 / |qp0_R - qp1_R|   *)
(*      Layer 4 (final):   `b64_intersect_point_{x,y}_forward_error`          *)
(*                         <= bpow 29 + bpow 80 / |qp0_R - qp1_R|             *)
(*                                                                            *)
(* 5. Session 6 -- reference bridge + soundness typeclass:                    *)
(*    `b64_intersect_point_{x,y}_forward_error_vs_intersect_{x,y}_R`          *)
(*    state the same bound against the canonical `intersect_{x,y}_R          *)
(*    (BP2P P0) ... (BP2P Q1)` reference via `c2tight_ref_{x,y}_eq_           *)
(*    intersect_{x,y}_R` (bridges through `b64_intersect_d{x,y}_R` and        *)
(*    `cross_R_BP_eq_cross_BP2P`).                                            *)
(*                                                                            *)
(*    `HasIntersect_sound` typeclass layers on top of `HasIntersect` with     *)
(*    three fields (`intersect_ref_x`, `intersect_ref_y`,                     *)
(*    `intersect_error_bound`) and two soundness obligations.                 *)
(*    `HasIntersect_sound_BPoint` instance plugs in the C.2-tight headlines.  *)
(*                                                                            *)
(* OPTIONAL                                                                   *)
(*                                                                            *)
(* A. K * eps restatement.  Rewrite the layer-4 bound as                      *)
(*       |B2R(b64_intersect_point_x ...) - intersect_x_R (BP2P P0) ...|       *)
(*       <= K(|den_exact|) * eps                                              *)
(*    with `K(|d|) = bpow 82 + bpow 133 / |d|` and `eps = bpow(-prec)`.       *)
(*    Equivalent to the current bound; algebraic restatement only.            *)
(* -------------------------------------------------------------------------- *)

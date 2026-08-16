(* ============================================================================
   PassesThrough_b64_grid_exact.v
   ----------------------------------------------------------------------------
   Issue #66, the snap-rounding / passes-through RGR pivot (see
   docs/snap-rounding-rgr-pivot.md and docs/oracle-soundness-finding.md).

   GOAL (C1, "grid exactness").  On the integer / unit grid the ROUNDED compute
   filter agrees bit-for-bit with the EXACT R-spec:

       b64_on_grid P0 -> b64_on_grid P1 ->
         b64_passes_through_hot_pixel_compute P0 P1 C
           = b64_passes_through_hot_pixel P0 P1 C.

   This is the constructive payoff of the pivot: the compute filter is
   machine-checked UNSOUND off the grid (PassesThrough_b64_compute_unsound.v),
   but a snap-rounding noder only ever evaluates it on snapped (grid-aligned)
   coordinates -- and there it coincides with the exact spec, which is sound
   (HotPixel_b64.b64_passes_through_sound).  Strongly evidenced: 0 divergence in
   5,000,000 on-grid cases (docs/oracle-soundness-finding.md).

   THIS FILE lands the REDUCTION + EXACTNESS layers, Qed-closed:

     - Slice 1: on the grid the snap-consistency second conjunct of
       `passes_through` is vacuous (a grid point is a fixed point of `b64_snap`),
       so the full predicate collapses to a single Liang-Barsky touch -- for
       BOTH the rounded compute filter and the exact spec.  C1 therefore reduces
       to the single-touch equivalence
           b64_liang_barsky_touches_compute = b64_liang_barsky_touches (on grid).
     - Slices 3-5: the slab guard, the t-bound operands, and the max/min/clip
       composition all bridge bit-exactly between compute and spec on the grid.
     - Slice 6: the only place `b64_div` (which ROUNDS) enters is discharged of
       its safety precondition and rewritten so each compute t-bound equals the
       spec t-bound with each quotient INDIVIDUALLY ROUNDED.
     - Slices 7-8: rounding is monotone, so it commutes past Rmin/Rmax and the
       outer clip -- collapsing every compute t-bound, and the whole clipped
       tmin/tmax, into a single `b64_round` of the exact spec value.
     - Slice 9: ON-GRID COMPLETENESS, Qed -- one of C1's two directions is
       CLOSED.  `spec = true => compute = true` on the grid (the rounded filter
       never DROPS a pass; the noder-safe direction), free from monotonicity.
     - Slice 10: CONDITIONAL grid-exactness, Qed -- the full on-grid
       `compute = spec` equivalence certified modulo ONE named real hypothesis
       (the rounded clip comparison reflects the exact one).  Same honest shape
       as hobby_theorem_4_1_conditional; the gap is a Prop hypothesis, not an
       axiom.
     - Slice 11: rounding-reflection kernel, Qed -- since round-to-nearest moves
       each value by <= half a ulp, the rounded `<=` reflects the exact `<=`
       once the values are ordered or separated beyond the half-ulp band.  This
       discharges Slice 10's rounding hypothesis in favour of the PURE-REALS
       `clip_separated` (no rounding in the statement).
     - Slice 12: determinant-gap kernel, Qed -- two distinct rationals differ by
       >= 1/(|da| |db|) (`rational_gap`), and each grid t-bound is exactly such a
       ratio (`grid_quotient_ratio`).  The LOWER-bound (gap) half of
       `clip_separated`.
     - Slice 13: ulp UPPER bound, Qed -- `|x| <= 2^e => ulp(round x) <=
       2^(e+1-prec)` (`b64_ulp_round_le_bpow`), so bounds in [0,1] give
       ulp(round x) <= 2^-52 (`b64_ulp_round_le_unit`).  The UPPER-bound half of
       `clip_separated`.
     - Slice 14: the bricks COMBINE, Qed -- for two distinct ratios u, v in
       [-1,1] with denominators <= 2^24, `1/2 ulp(round u) + 1/2 ulp(round v)
       < |u - v|` (`grid_ratio_gap_exceeds_ulp_band`): band <= 2^-52 < 2^-48 <=
       gap.  This is EXACTLY `clip_separated`'s right disjunct for the binding
       pair -- the determinant-beats-rounding inequality, done.

   Slices 15-18 then CLOSE it: the relative ulp bound (15) removes the [-1,1]
   cap, the value-0 edge (16) completes the gap-beats-band family, the
   `gridbound` algebra (17) packages it, and exhibiting the exact clip bounds as
   `gridbound` (18) discharges `clip_separated` outright on the tight integer
   grid `|n| <= 2^22`.  (Why 2^22: it is the half-quotient `gridbound` limit --
   the t-bound numerators `2*ncc +/- 1 - 2*n0` then fit in 2^24 <= 2^25 and the
   runs `2*(n1 - n0)` in 2^24, the bounds `gridbound`/Slice-15 require.)
   RESULT: `b64_passes_through_grid_exact` --
   `compute = spec` UNCONDITIONALLY on the tight grid, Qed, no named hypotheses
   (soundness `b64_passes_through_sound_on_grid` + Slice 9 completeness).  The
   only remaining items are the WIDTH extension to the full `coord_int_safe`
   regime `|n| <= 2^25` (needs the exact integer-determinant comparison, not a
   forward-error bound) and the general-binary64 C2 -- see the OBLIGATION note.
   No `Admitted` anywhere; the file is Qed-clean.

   Corpus invariant preserved: no Admitted / Axiom / Parameter.
   topic: binary64

   SPLIT (2026-08-15): the 18 slices now live in five layered modules --
   PassesThrough_b64_grid_core (S1-5), _grid_bounds (S6-8),
   _grid_complete (S9-11), _grid_gap_kernel (S12-13; pure-R, off
   audit-exceptions per meso-audit B4; B4's exit corrected 2026-08-16 --
   the slice-13 ulp lemmas are C1-tainted via b64_round in their
   statements, so the module is re-listed), _grid_separation (S14-18).
   This file is the Require Export umbrella: every name is re-exported,
   so importers are unaffected.
   claimId: 66-c1
   witness: grid-unit
   ============================================================================ *)

From NTS.Proofs.Flocq Require Export PassesThrough_b64_grid_core.
From NTS.Proofs.Flocq Require Export PassesThrough_b64_grid_bounds.
From NTS.Proofs.Flocq Require Export PassesThrough_b64_grid_complete.
From NTS.Proofs.Flocq Require Export PassesThrough_b64_grid_gap_kernel.
From NTS.Proofs.Flocq Require Export PassesThrough_b64_grid_separation.

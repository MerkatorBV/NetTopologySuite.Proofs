(* ============================================================================
   NetTopologySuite.Proofs.Flocq.SnapRoundingGuardAudit
   ----------------------------------------------------------------------------
   Issue #66 guard-discharge audit (round 2, item 1): does the snap-rounding
   pipeline (HotPixel_b64 / PassesThrough_b64 / SnapRounding_b64) already
   PRODUCE the five geometric/noding guards -- `well_noded_darts`, `no_spurs`,
   `pairwise_no_proper_cross_twin_aware`, `no_horizontal_darts`,
   `no_foreign_vertex_twin_aware` -- for real noded output, the way
   `extract_rings_valid_of_guards` (OverlayBridgeUnconditional.v) needs to be
   usable with zero side conditions?

   THIS FILE'S FINDING, for `no_horizontal_darts`: NO, not for free, and not
   even under an input-side genericity assumption. `no_horizontal_darts D :=
   forall x, In x D -> py (fst x) <> py (snd x)` is a fact about the SNAPPED
   coordinates the noder actually emits, and snap-rounding to the integer grid
   (`b64_snap_coord = round-to-nearest-integer`, HotPixel_b64.v) can CREATE a
   horizontal dart from a strictly non-horizontal input segment: two distinct
   y-coordinates that straddle the same grid cell round to the identical
   integer. The witness below is the minimal case -- `0` and `1/2` (already
   distinct reals, `0 <> 1/2`) both round-to-nearest-even to `0`.

   So `no_horizontal_darts` cannot be "produced by the pipeline" as a
   structural fact about ARBITRARY input under snap-rounding; anywhere it is
   assumed downstream (`EulerUnconditional.v`, `WalkResidualDischarge.
   H_bridge_premise_holds`, `extract_rings_valid_of_guards`), it is a genuine
   NAMED hypothesis on the noded OUTPUT that must be separately verified per
   arrangement (e.g. by the noder rejecting/perturbing exact grid-ties), not
   a corollary of noding alone. This is the same "honest negative" shape as
   `ExtractFacesBridge.v`'s finding that `fully_intersected` does not deliver
   the (non-twin) pairwise-no-crossing guard, and `NodedGeneralPosition.v`'s
   note that the `fully_intersected` -> `noded_general_position` bridge is
   itself still open ("cross-lane plumbing", host-lane territory, not this
   file's scope). Pinning this down is exactly the "regime the width
   extension must cover" the round-2 assignment asks for: C1/C2 already
   operate ON THE GRID, i.e. downstream of exactly the collapse this file
   witnesses, so grid-tie coordinates are not a corner case C1 can ignore --
   they are the generic case post-snap.

   No `Admitted` / `Axiom` / `Parameter`; allowlist axioms only (none pulled
   here beyond what HotPixel_b64.v itself needs).

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
   ========================================================================== *)

From Flocq Require Import IEEE754.Binary Core.
From NTS.Proofs Require Import Distance.
From NTS.Proofs.Flocq Require Import Validate_binary64 HotPixel_b64.
From Stdlib Require Import Reals Lra.
Local Open Scope R_scope.

(* A concrete non-horizontal-but-snaps-horizontal pair on the y-axis: 0 and
   1/2. Both are exact in binary64; `b64_snap_coord` is round-to-nearest-even
   (`Bnearbyint mode_NE`), and 1/2 is the tie case, rounding to the EVEN
   integer 0 -- coinciding with `b64_snap_coord` of 0 itself. *)
Definition wy0 : binary64 := Binary.B754_zero prec emax false.
Definition wy1 : binary64 := b64_half.

Lemma B2R_wy0 : Binary.B2R prec emax wy0 = 0.
Proof. reflexivity. Qed.

(* Pre-snap: the two y-coordinates are genuinely distinct reals. *)
Lemma wy_distinct_pre_snap :
  Binary.B2R prec emax wy0 <> Binary.B2R prec emax wy1.
Proof. unfold wy1. rewrite B2R_wy0, B2R_b64_half. lra. Qed.

(* The snap step itself collapses them to the identical binary64 value
   (decided by computation: `Bnearbyint` is a total computable function). *)
Lemma wy_snap_coord_collapse : b64_snap_coord wy0 = b64_snap_coord wy1.
Proof. vm_compute. reflexivity. Qed.

(* Post-snap: therefore the identical real coordinate too -- a horizontal
   dart where the pre-snap input had none. *)
Theorem snap_can_introduce_horizontal_alignment :
  Binary.B2R prec emax wy0 <> Binary.B2R prec emax wy1 /\
  Binary.B2R prec emax (b64_snap_coord wy0) = Binary.B2R prec emax (b64_snap_coord wy1).
Proof.
  split.
  - exact wy_distinct_pre_snap.
  - now rewrite wy_snap_coord_collapse.
Qed.

(* Point-level restatement, in the exact shape `no_horizontal_darts` tests
   (`py (fst x) <> py (snd x)` on `BP2P`-bridged endpoints): a dart with
   x-coordinates 0/1 (any distinct values; the x-axis plays no role here)
   and these two y-coordinates is non-horizontal before snapping and
   horizontal after. *)
Definition waP0 : BPoint := mkBP wy0 wy0.
Definition waP1 : BPoint := mkBP b64_one wy1.

Corollary snap_can_introduce_horizontal_dart :
  py (BP2P waP0) <> py (BP2P waP1) /\
  py (BP2P (b64_snap waP0)) = py (BP2P (b64_snap waP1)).
Proof.
  unfold waP0, waP1, BP2P, b64_snap, py; cbn [px py].
  exact snap_can_introduce_horizontal_alignment.
Qed.

(* -------------------------------------------------------------------------- *)
(* Axiom audit.                                                               *)
(* -------------------------------------------------------------------------- *)

Print Assumptions snap_can_introduce_horizontal_alignment.
Print Assumptions snap_can_introduce_horizontal_dart.

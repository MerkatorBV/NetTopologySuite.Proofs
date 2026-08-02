(* ============================================================================
   NetTopologySuite.Proofs.CoverageGapOverlapCleaner
   ----------------------------------------------------------------------------
   Issue #425 subtask 425-a — RED surface only: polygonal coverage
   gap/overlap cleaner validity (classical reals).

   WHAT THIS FILE IS.  The smallest failing claim for the intended
   soundness of a CoverageCleaner-style map on polygonal coverages:
     after gap/overlap cleaning, the coverage is pairwise
     interior-disjoint (overlap-free) and its union matches the target
     region up to boundary null sets (gap-free),
   packaged as `coverage_gap_overlap_cleaner_valid`, with a rational
   two-cell overlap witness that pins positive-area interior intersection.
   Green / Refactor are out of scope: no production cleaner body that
   closes the goal, no `Admitted` as a fake green.  Open goals end with
   `Abort` (same discipline as HobbyTheorem_b64 / InArc Red / InDisk Red /
   DelaunayEdgeEmptyCircle Red / RelateNGBoundaryGraph Red — an Aborted
   claim is not `apply`-able and cannot silently poison consumers).

   WHAT IS MISSING ON MAIN (why the focused check fails without Green).
   Neighbouring epics cover pairwise overlay/noding and relate strata,
   not the set-of-polygons coverage invariants:
     - #66 overlay spine (`extract_rings_valid`, boolean_op) — pairwise
       extract, not multi-cell coverage validity / cleaner soundness;
     - #67 exact relate / DE-9IM — cell-level strata, not gap/overlap
       cleaning of a coverage collection;
     - `RingArea979` / hole nesting — sliver area and nesting, not
       CoverageCleaner obligations (JTS#1126 / NTS#810).
   There is no named `coverage_gap_overlap_cleaner_valid` /
   `coverage_overlap_free` surface on main, and no rational multi-cell
   witness discharging a positive-area overlap (or gap) defect.

   INTENDED PREDICATE (spec shape for Green).
     - `Coverage` — finite list of axis-aligned cells (Red carrier;
       Green may rebind to `list Polygon` / corpus Geometry).
     - `coverage_overlap_free cov` — pairwise open-interior disjoint.
     - `coverage_gap_free cov target` — every open-interior point of
       `target` lies in some (closed) cell of `cov` (union covers the
       target up to the boundary null set).
     - `coverage_same_union c1 c2` — open-interior point-sets coincide
       (union preserved; cleaner must not invent/drop area).
     - `coverage_gap_overlap_cleaner_valid clean` — for every coverage,
       `clean cov` is overlap-free and has the same union as `cov`
       (both JTS CoverageCleaner obligations rolled into one claim).
   Green is authorised to refine AABB → Polygon, half-open vs closed
   interiors, width-based gap tolerance (JTS#1122), and greedy merge
   order negatives; Red only fixes the claim shape and the rational
   overlap witness.  Operator Eval → Qed via the nts-eval micro-kernel
   is required for the Green close (operator CI status unknown at Red).

   RATIONAL WITNESS (two cells ⊂ ℚ² with positive-area overlap).
     cell A = [0,1]×[0,1]
     cell B = [1/2, 3/2]×[1/2, 3/2]
     overlap open square = (1/2,1)×(1/2,1)
     sample q = (3/4, 3/4)  ∈ open interior of A and of B
   So the raw two-cell coverage is not overlap-free; identity cannot be
   a valid cleaner.  Green exhibits a real cleaner that resolves the
   overlap (and any gap) while preserving union, and closes
   `coverage_gap_overlap_cleaner_valid` on classical reals.

   Refs: issue #425 (coverage validity / gap-overlap cleaning / union),
   JTS#1126 CoverageCleaner, NTS#810, JTS#1122 CoverageValidator.
   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Grok (grok-4.5)
   ========================================================================== *)

From Stdlib Require Import Reals Lra List.
Import ListNotations.
From NTS.Proofs Require Import Distance.

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  Spec shape — coverage cells, overlap-free, gap-free, cleaner valid.    *)
(*                                                                            *)
(* Red carrier is the axis-aligned box (AABB).  Green may rebind cells to     *)
(* corpus `Polygon` / `Geometry` once the cleaner is wired to Overlay.        *)
(* -------------------------------------------------------------------------- *)

(** Axis-aligned cell: closed geometric extent [min,max]×[min,max]. *)
Record Aabb : Type := mkAabb {
  amin_x : R;
  amax_x : R;
  amin_y : R;
  amax_y : R
}.

(** A polygonal coverage is a finite list of cells. *)
Definition Coverage : Type := list Aabb.

(** Strict (open) interior of an AABB — positive-area membership. *)
Definition in_open_aabb (a : Aabb) (p : Point) : Prop :=
  amin_x a < px p < amax_x a /\ amin_y a < py p < amax_y a.

(** Closed cell membership (includes boundary). *)
Definition in_closed_aabb (a : Aabb) (p : Point) : Prop :=
  amin_x a <= px p <= amax_x a /\ amin_y a <= py p <= amax_y a.

(** Pairwise interior-disjoint: no point lies in two open interiors. *)
Definition coverage_overlap_free (cov : Coverage) : Prop :=
  forall (c1 c2 : Aabb) (p : Point),
    In c1 cov ->
    In c2 cov ->
    c1 <> c2 ->
    ~ (in_open_aabb c1 p /\ in_open_aabb c2 p).

(** Open-interior union of a coverage. *)
Definition coverage_union_open (cov : Coverage) (p : Point) : Prop :=
  exists c, In c cov /\ in_open_aabb c p.

(** Gap-free relative to a target cell: every open-interior target point
    lies in some closed cell of the coverage (union covers the target up
    to the boundary null set). *)
Definition coverage_gap_free (cov : Coverage) (target : Aabb) : Prop :=
  forall p : Point,
    in_open_aabb target p ->
    exists c, In c cov /\ in_closed_aabb c p.

(** Union preserved (open-interior point-sets coincide). *)
Definition coverage_same_union (c1 c2 : Coverage) : Prop :=
  forall p : Point,
    coverage_union_open c1 p <-> coverage_union_open c2 p.

(** Cleaner soundness property of a candidate map (JTS CoverageCleaner
    obligations, Red shape): for every input coverage, the cleaned result
    is pairwise interior-disjoint and has the same open-interior union as
    the input (no invented / dropped positive-area region). *)
Definition is_valid_coverage_cleaner
  (clean : Coverage -> Coverage) : Prop :=
  forall cov : Coverage,
    coverage_overlap_free (clean cov) /\
    coverage_same_union (clean cov) cov.

(** The 425-a claim as a closed Prop (existence of a sound cleaner).
    Green closes a Lemma of this statement; Red only names it. *)
Definition coverage_gap_overlap_cleaner_valid_claim : Prop :=
  exists clean : Coverage -> Coverage, is_valid_coverage_cleaner clean.

(* -------------------------------------------------------------------------- *)
(* §2  Rational two-cell overlap witness (ℚ²).                                *)
(*                                                                            *)
(* cell A = [0,1]×[0,1], cell B = [1/2,3/2]×[1/2,3/2],                       *)
(* open overlap (1/2,1)×(1/2,1), sample q = (3/4,3/4).                        *)
(* -------------------------------------------------------------------------- *)

Definition cov_cell_A : Aabb := mkAabb 0 1 0 1.
Definition cov_cell_B : Aabb := mkAabb (1 / 2) (3 / 2) (1 / 2) (3 / 2).

(** Raw two-cell coverage with a positive-area overlap. *)
Definition cov_overlap_witness : Coverage := [cov_cell_A; cov_cell_B].

(** Interior sample of the open overlap square (1/2,1)×(1/2,1). *)
Definition cov_overlap_sample : Point := mkPoint (3 / 4) (3 / 4).

(** Bounding target for the two-cell arrangement (union envelope). *)
Definition cov_target_envelope : Aabb := mkAabb 0 (3 / 2) 0 (3 / 2).

(* Geometric scaffolding for the witness — Qed.  Mentions only open/closed
   AABB membership and list membership, so it cannot accidentally close the
   Red cleaner-validity claims. *)

Lemma cov_cell_A_B_distinct : cov_cell_A <> cov_cell_B.
Proof.
  unfold cov_cell_A, cov_cell_B. intros Heq.
  assert (Hx : amin_x (mkAabb 0 1 0 1) = amin_x (mkAabb (1 / 2) (3 / 2) (1 / 2) (3 / 2)))
    by (rewrite Heq; reflexivity).
  cbn in Hx. lra.
Qed.

Lemma cov_cell_A_in_witness : In cov_cell_A cov_overlap_witness.
Proof. unfold cov_overlap_witness. simpl. left. reflexivity. Qed.

Lemma cov_cell_B_in_witness : In cov_cell_B cov_overlap_witness.
Proof. unfold cov_overlap_witness. simpl. right. left. reflexivity. Qed.

(** Sample lies in the open interior of cell A. *)
Lemma cov_overlap_sample_in_A :
  in_open_aabb cov_cell_A cov_overlap_sample.
Proof.
  unfold in_open_aabb, cov_cell_A, cov_overlap_sample; cbn [px py amin_x amax_x amin_y amax_y].
  split; split; lra.
Qed.

(** Sample lies in the open interior of cell B. *)
Lemma cov_overlap_sample_in_B :
  in_open_aabb cov_cell_B cov_overlap_sample.
Proof.
  unfold in_open_aabb, cov_cell_B, cov_overlap_sample; cbn [px py amin_x amax_x amin_y amax_y].
  split; split; lra.
Qed.

(** Positive-area overlap pin: the sample is in both open interiors. *)
Lemma cov_overlap_sample_in_both :
  in_open_aabb cov_cell_A cov_overlap_sample /\
  in_open_aabb cov_cell_B cov_overlap_sample.
Proof.
  split; [exact cov_overlap_sample_in_A | exact cov_overlap_sample_in_B].
Qed.

(** The raw two-cell coverage is NOT overlap-free (identity cannot clean). *)
Lemma cov_overlap_witness_not_overlap_free :
  ~ coverage_overlap_free cov_overlap_witness.
Proof.
  unfold coverage_overlap_free.
  intros Hfree.
  specialize (Hfree cov_cell_A cov_cell_B cov_overlap_sample
                cov_cell_A_in_witness cov_cell_B_in_witness
                cov_cell_A_B_distinct).
  apply Hfree.
  exact cov_overlap_sample_in_both.
Qed.

(** Sample is in the open envelope target (union region pin). *)
Lemma cov_overlap_sample_in_target :
  in_open_aabb cov_target_envelope cov_overlap_sample.
Proof.
  unfold in_open_aabb, cov_target_envelope, cov_overlap_sample;
    cbn [px py amin_x amax_x amin_y amax_y].
  split; split; lra.
Qed.

(** Closed-membership pins: sample sits in both closed cells. *)
Lemma cov_overlap_sample_closed_A :
  in_closed_aabb cov_cell_A cov_overlap_sample.
Proof.
  unfold in_closed_aabb, cov_cell_A, cov_overlap_sample;
    cbn [px py amin_x amax_x amin_y amax_y].
  split; split; lra.
Qed.

Lemma cov_overlap_sample_closed_B :
  in_closed_aabb cov_cell_B cov_overlap_sample.
Proof.
  unfold in_closed_aabb, cov_cell_B, cov_overlap_sample;
    cbn [px py amin_x amax_x amin_y amax_y].
  split; split; lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Focused Red claims — open, not Admitted.                               *)
(*                                                                            *)
(* These are the surface Eval / nts-eval will re-check after Green is          *)
(* authorised.  Until then they remain Abort: neither closed nor disproven.   *)
(* -------------------------------------------------------------------------- *)

(** RED (425-a): CoverageCleaner soundness over classical reals.
    There exists a cleaner map that, for every polygonal coverage, yields
    an overlap-free result with the same open-interior union as the input
    (gap/overlap cleaning establishes validity while preserving the covered
    region up to boundary null sets).

    Green closes by exhibiting the real cleaner (merge/split cells) and
    discharging both conjuncts.  Do not Admitted. *)
Theorem coverage_gap_overlap_cleaner_valid :
  coverage_gap_overlap_cleaner_valid_claim.
Proof.
  (* RED #425-a: Green exhibits a CoverageCleaner-style map and proves
     overlap-freedom + union preservation on classical reals.
     Do not Admitted — that would be a fake green. *)
Abort.

(** RED (425-a): the same soundness, specialised to the rational overlap
    witness — cleaner must repair the positive-area overlap of
    [cov_overlap_witness] without changing the open union. *)
Theorem coverage_gap_overlap_cleaner_valid_on_witness :
  exists clean : Coverage -> Coverage,
    coverage_overlap_free (clean cov_overlap_witness) /\
    coverage_same_union (clean cov_overlap_witness) cov_overlap_witness.
Proof.
  (* RED #425-a: Green discharges cleaner on the two-cell overlap witness.
     Do not Admitted. *)
Abort.

(** RED (425-a): gap-free obligation relative to the union envelope — after
    cleaning, every open point of [cov_target_envelope] that was covered
    by the raw union remains covered (no residual positive-area gap in the
    envelope).  Green may refine the target to the exact open union. *)
Theorem coverage_cleaner_gap_free_on_envelope :
  exists clean : Coverage -> Coverage,
    coverage_gap_free (clean cov_overlap_witness) cov_target_envelope /\
    coverage_overlap_free (clean cov_overlap_witness).
Proof.
  (* RED #425-a.  Do not Admitted. *)
Abort.

(* WITNESS {"claimId":"425-a","topic":"coverage","lemma":"coverage_gap_overlap_cleaner_valid","title":"Coverage gap/overlap cleaner establishes valid coverage","file":"theories/CoverageGapOverlapCleaner.v"} *)

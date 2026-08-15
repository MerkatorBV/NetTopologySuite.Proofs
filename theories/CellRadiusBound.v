(* ============================================================================
   NetTopologySuite.Proofs.CellRadiusBound
   ----------------------------------------------------------------------------
   Board card #9004 subtask 9004-d — RED (unproved claim surface).

   Zhai, X. et al. (2026), "Polycenter: fast and precise polygon center
   identification", doi:10.1080/13658816.2025.2514056.  Epic #813.

   Why this file exists (9004-d).  Polycenter — like JTS/NTS
   MaximumInscribedCircle and LargestEmptyCircle, whose Cell machinery is
   shared code — is a branch-and-bound over square cells: a cell can be
   PRUNED when the radius achievable anywhere inside it cannot beat the
   incumbent.  The soundness of that pruning is the achievable-radius
   bound: the clearance at any point of a square cell exceeds the
   clearance at the cell's centre by at most the cell circumradius
   (JTS `Cell.getMaxDistance() = distanceToBoundary(centre) + radius`,
   with radius = h·√2 for half-side h).  The corpus (9004-a .. 9004-c and
   the LEC opener) states inscribed/empty disks and their maximisers, but
   nothing bounds what a CELL can achieve — without it, no subdivision
   step can ever be justified.  This file plants that surface:

     `in_cell`   the closed axis-aligned square cell: centre c, half-side h

   and states the headline on the LEC side (obstacle clearance), the form
   in which both JTS classes consume it:

     `cell_achievable_radius_bound` : if p lies in the cell of centre c,
       half-side h, and the disk (p, r') is empty of the obstacles, then
       for EVERY obstacle X:   r' <= dist c X + sqrt 2 * h.

   Reading: an empty radius achievable anywhere in the cell is at most the
   centre's distance to its (any, hence nearest) obstacle plus the cell
   circumradius — exactly the JTS getMaxDistance pruning bound.

   RED GATE.  The headline body is deliberately unproved.  `rocq c` on this
   file fails at `Qed` with "Attempt to save an incomplete proof": an
   unproved obligation, not a syntax error.  Everything above the headline
   elaborates cleanly, so the failing surface is exactly one goal.

   No `Admitted`, no `admit` tactic, no `Axiom`, no `Parameter`
   (scripts/check_admitted.sh stays green, and no registry entry is
   claimed).  Nothing here is added to docs/verified-claims.md — the claim
   is not verified yet.

   Deliberately NOT in scope on this rung:
     - the centre-shift (Lipschitz) lemmas and the inscribed-side dual
       (that is the Green rung, together with the proof);
     - the subdivision RECURSION itself (cell splitting, queue order,
       termination) — this rung is the per-cell bound only;
     - tolerance/termination arguments (JTS's tolerance loop);
     - polygonal or linear obstacles — point obstacles only.

   Registered in `_CoqProject.full` only: it imports LargestEmptyCircle.v
   (MaximumInscribedCircle.v / InDisk.v lineage), so `make host` does not
   see it.

   Refs: board #9004 (9004-d cell bound; 9004-a surface, 9004-c witness),
   epic #813; siblings MaximumInscribedCircle.v, LargestEmptyCircle.v.
   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import Distance Linearise InDisk
  MaximumInscribedCircle LargestEmptyCircle.

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  Square cells — the subdivision unit 9004-d is about.                   *)
(* -------------------------------------------------------------------------- *)

(** [in_cell c h p]: [p] lies in the closed axis-aligned square cell of
    centre [c] and half-side [h] (JTS Cell: centre + "half-side" extent;
    the circumradius is h·√2).  Stated as two-sided coordinate bounds —
    the `lra`-friendly form. *)
Definition in_cell (c : Point) (h : R) (p : Point) : Prop :=
  px c - h <= px p <= px c + h /\ py c - h <= py p <= py c + h.

(* -------------------------------------------------------------------------- *)
(* §2  Headline — RED, unproved.                                              *)
(* -------------------------------------------------------------------------- *)

(** The achievable-radius bound (JTS Cell.getMaxDistance soundness, LEC
    form): an empty radius achievable at any point of a square cell is at
    most the centre's distance to every obstacle plus the cell
    circumradius √2·h.

    True by two triangle steps: r' ≤ dist p X (emptiness) ≤ dist p c +
    dist c X, and dist p c ≤ √2·h since dist_sq p c ≤ 2h² in the cell.

    RED (9004-d): the body is intentionally left open.  Proving it is the
    Green rung and is out of scope here. *)
Theorem cell_achievable_radius_bound :
  forall (obs : Region) (c p : Point) (h r' : R) (X : Point),
    0 <= h ->
    in_cell c h p ->
    empty_disk obs p r' ->
    obs X ->
    r' <= dist c X + sqrt 2 * h.
Proof.
  (* RED — unproved obligation.  Do not close this with the `admit` tactic
     or with `Admitted`: the corpus invariant forbids both, and the Red gate
     wants `rocq c` to fail here with "Attempt to save an incomplete
     proof". *)
Qed.

(* ============================================================================
   NetTopologySuite.Proofs.CellRadiusBound
   ----------------------------------------------------------------------------
   Board card #9004 subtask 9004-d — GREEN (Qed-closed headline; Red
   surface planted and witnessed in the previous commit).

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

   GREEN (this rung).  The headline is two triangle steps
   (r' ≤ dist p X ≤ dist c p + dist c X, and dist c p ≤ √2·h from
   dist_sq ≤ 2h², `cell_circumradius`).  Beyond it, the rung delivers the
   machinery a subdivision step consumes, on BOTH sides of the #9004/LEC
   duality:

     - centre-shift (Lipschitz) lemmas: moving a disk's centre by d costs
       at most d of radius — `empty_disk_centre_shift` and
       `inscribed_disk_centre_shift`;
     - radius monotonicity: `empty_disk_radius_mono`,
       `inscribed_disk_radius_mono`;
     - the per-cell corollaries: whatever radius a cell point achieves,
       the cell centre achieves minus √2·h — `cell_empty_disk_at_centre`
       and `cell_inscribed_disk_at_centre`.

   The claim is indexed in docs/verified-claims.md and mirrored
   self-contained in eval/Claim9004d.v (WITNESS 9004-d, topic: construct;
   same marker below).

   No `Admitted`, no `Axiom`, no `Parameter`; 3-axiom classical-reals
   footprint (Distance / Linearise / InDisk lineage; not in
   audit-exceptions).

   Deliberately NOT in scope on this rung:
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

(* WITNESS {"claimId":"9004-d","topic":"construct","lemma":"cell_achievable_radius_bound","title":"Cell pruning bound: empty radius in a cell <= centre-to-obstacle distance + sqrt(2)*h","file":"theories/CellRadiusBound.v"} *)

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
(* §2  The cell circumradius: dist to any cell point is at most √2·h.         *)
(* -------------------------------------------------------------------------- *)

Lemma cell_dist_sq_bound : forall (c : Point) (h : R) (p : Point),
  0 <= h -> in_cell c h p -> dist_sq c p <= 2 * (h * h).
Proof.
  intros c h p Hh [[Hx0 Hx1] [Hy0 Hy1]].
  unfold dist_sq. nra.
Qed.

Lemma sqrt2_h_sq : forall h : R,
  (sqrt 2 * h) * (sqrt 2 * h) = 2 * (h * h).
Proof.
  intros h.
  assert (H2 : sqrt 2 * sqrt 2 = 2) by (apply sqrt_sqrt; lra).
  replace ((sqrt 2 * h) * (sqrt 2 * h))
    with ((sqrt 2 * sqrt 2) * (h * h)) by ring.
  rewrite H2. ring.
Qed.

Lemma cell_circumradius : forall (c : Point) (h : R) (p : Point),
  0 <= h -> in_cell c h p -> dist c p <= sqrt 2 * h.
Proof.
  intros c h p Hh Hcell.
  assert (Ht : 0 <= sqrt 2 * h).
  { apply Rmult_le_pos; [apply sqrt_pos | exact Hh]. }
  apply (proj2 (dist_le_iff_dist_sq_le c p (sqrt 2 * h) Ht)).
  rewrite sqrt2_h_sq.
  apply cell_dist_sq_bound; assumption.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Headline — GREEN.                                                      *)
(* -------------------------------------------------------------------------- *)

(** The achievable-radius bound (JTS Cell.getMaxDistance soundness, LEC
    form): an empty radius achievable at any point of a square cell is at
    most the centre's distance to every obstacle plus the cell
    circumradius √2·h.

    Two triangle steps: r' ≤ dist p X (emptiness) ≤ dist p c + dist c X,
    and dist p c ≤ √2·h since dist_sq p c ≤ 2h² in the cell. *)
Theorem cell_achievable_radius_bound :
  forall (obs : Region) (c p : Point) (h r' : R) (X : Point),
    0 <= h ->
    in_cell c h p ->
    empty_disk obs p r' ->
    obs X ->
    r' <= dist c X + sqrt 2 * h.
Proof.
  intros obs c p h r' X Hh Hcell [Hr' He] HX.
  pose proof (He X HX) as HpX.
  pose proof (dist_triangle p c X) as Htri.
  rewrite (dist_sym p c) in Htri.
  pose proof (cell_circumradius c h p Hh Hcell) as Hcr.
  lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Centre-shift (Lipschitz) lemmas — both duals — and radius              *)
(*     monotonicity.  Moving a disk's centre by d costs at most d of          *)
(*     radius, for emptiness and inscribedness alike.                         *)
(* -------------------------------------------------------------------------- *)

Lemma empty_disk_radius_mono :
  forall (obs : Region) (O : Point) (r r'' : R),
    0 <= r'' <= r -> empty_disk obs O r -> empty_disk obs O r''.
Proof.
  intros obs O r r'' [H0 Hle] [Hr He].
  split; [exact H0 |].
  intros X HX. pose proof (He X HX). lra.
Qed.

Lemma inscribed_disk_radius_mono :
  forall (Rg : Region) (O : Point) (r r'' : R),
    0 <= r'' <= r -> inscribed_disk Rg O r -> inscribed_disk Rg O r''.
Proof.
  intros Rg O r r'' [H0 Hle] [Hr Hincl].
  split; [exact H0 |].
  intros Q [HQr HQd].
  apply Hincl. split; [exact Hr | lra].
Qed.

Lemma empty_disk_centre_shift :
  forall (obs : Region) (p c : Point) (r' : R),
    empty_disk obs p r' -> 0 <= r' - dist c p ->
    empty_disk obs c (r' - dist c p).
Proof.
  intros obs p c r' [Hr' He] Hnn.
  split; [exact Hnn |].
  intros X HX.
  pose proof (He X HX) as HpX.
  pose proof (dist_triangle p c X) as Htri.
  rewrite (dist_sym p c) in Htri.
  lra.
Qed.

Lemma inscribed_disk_centre_shift :
  forall (Rg : Region) (p c : Point) (r' : R),
    inscribed_disk Rg p r' -> 0 <= r' - dist c p ->
    inscribed_disk Rg c (r' - dist c p).
Proof.
  intros Rg p c r' [Hr' Hincl] Hnn.
  split; [exact Hnn |].
  intros Q [HQr HQd].
  apply Hincl.
  split; [exact Hr' |].
  pose proof (dist_triangle p c Q) as Htri.
  rewrite (dist_sym p c) in Htri.
  lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  The per-cell corollaries: what a cell point achieves, the centre       *)
(*     nearly achieves — the exact shape a subdivision step consumes,         *)
(*     on both sides of the duality.                                          *)
(* -------------------------------------------------------------------------- *)

Corollary cell_empty_disk_at_centre :
  forall (obs : Region) (c p : Point) (h r' : R),
    0 <= h -> in_cell c h p ->
    empty_disk obs p r' -> 0 <= r' - sqrt 2 * h ->
    empty_disk obs c (r' - sqrt 2 * h).
Proof.
  intros obs c p h r' Hh Hcell Hemp Hnn.
  pose proof (cell_circumradius c h p Hh Hcell) as Hcr.
  pose proof (dist_nonneg c p) as Hd0.
  apply (empty_disk_radius_mono obs c (r' - dist c p)); [lra |].
  apply empty_disk_centre_shift; [exact Hemp | lra].
Qed.

Corollary cell_inscribed_disk_at_centre :
  forall (Rg : Region) (c p : Point) (h r' : R),
    0 <= h -> in_cell c h p ->
    inscribed_disk Rg p r' -> 0 <= r' - sqrt 2 * h ->
    inscribed_disk Rg c (r' - sqrt 2 * h).
Proof.
  intros Rg c p h r' Hh Hcell Hins Hnn.
  pose proof (cell_circumradius c h p Hh Hcell) as Hcr.
  pose proof (dist_nonneg c p) as Hd0.
  apply (inscribed_disk_radius_mono Rg c (r' - dist c p)); [lra |].
  apply inscribed_disk_centre_shift; [exact Hins | lra].
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions cell_achievable_radius_bound.
Print Assumptions cell_circumradius.
Print Assumptions empty_disk_centre_shift.
Print Assumptions inscribed_disk_centre_shift.
Print Assumptions cell_empty_disk_at_centre.
Print Assumptions cell_inscribed_disk_at_centre.

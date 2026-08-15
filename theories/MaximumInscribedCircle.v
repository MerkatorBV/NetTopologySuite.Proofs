(* ============================================================================
   NetTopologySuite.Proofs.MaximumInscribedCircle
   ----------------------------------------------------------------------------
   Board card #9004 — GREEN (Qed-closed headline on the 9004-a surface).

   Zhai, X. et al. (2026), "Polycenter: fast and precise polygon center
   identification", doi:10.1080/13658816.2025.2514056.  Epic #813.

   Paper CLAIMS: a fast, precise polygon-centre (MIC / visual-centre)
   identification algorithm via cell subdivision with an achievable-radius
   bound over a cell.  File PROVES: the inscribed / maximum-inscribed-disk
   SURFACE (9004-a) and the rational unit-square instance (9004-c) only —
   none of Polycenter's algorithmics (no cells, no radius bound; 9004-d).

   Why this file exists (9004-a).  The corpus can already say that a point
   lies *in* a disk — `Disk.in_disk` (squared-radius form on a `Disk` record)
   and `InDisk.InDisk` (geometric ‖P−O‖ ≤ r).  Neither says that a disk is
   *inscribed in a region*, and nothing anywhere quantifies **maximality** of
   the inscribed radius (9004-b: membership is not a maximiser).  So #813's
   MIC lane had no module to host a Polycenter cite.  This file is the
   smallest surface on which that cite can land:

     `Region`             a planar region as a point predicate
     `inscribed_disk`     the closed disk (O, r) is contained in the region
     `max_inscribed_disk` inscribed, and no inscribed disk has larger radius
     `unit_square`        the fully rational region [0,1]²

   and closes the rational headline (9004-c) on it:

     `mic_unit_square : max_inscribed_disk unit_square (1/2, 1/2) (1/2)`

   GREEN (this rung).  Both conjuncts are Qed, rational throughout, and
   sqrt-free beyond the `dist_le_iff_dist_sq_le` bridge:

     - containment: a point within distance 1/2 of the centre has
       (1/2 − x)² + (1/2 − y)² ≤ 1/4, so each coordinate lies in [0,1]
       (`nra` on the squared bound with the opposite square nonnegative);
     - maximality: for any inscribed (O', r'), the two horizontal probe
       points (ox' ± r', oy') are in the disk (their distance to O' is
       exactly r'), hence in the square, forcing 0 ≤ ox' − r' and
       ox' + r' ≤ 1, so 2r' ≤ 1 — exactly the argument the Red header
       promised.  Projections are exported as `mic_unit_square_inscribed`
       and `mic_unit_square_radius_maximal`.

   The claim is indexed in docs/verified-claims.md and mirrored
   self-contained in eval/Claim9004c.v (WITNESS 9004-c, topic: construct;
   same marker below).

   No `Admitted`, no `Axiom`, no `Parameter`; 3-axiom classical-reals
   footprint (Distance / InDisk lineage; not in audit-exceptions).

   Deliberately NOT in scope on this rung:
     - Polycenter's cell subdivision and the achievable-radius bound over a
       cell (9004-d) are untouched;
     - `InDisk.v` is reused as-is and not modified (9004-b);
     - no polygon-interior instantiation yet (that is #813's polygon rung);
     - no medial axis (that is #9006), no spherical pole of inaccessibility
       (that is #9005).

   Registered in `_CoqProject.full` only: it depends on `InDisk.v`, which is
   not part of the Stdlib-only host layer, so `make host` does not see it.

   Refs: board #9004 (9004-a claim surface, 9004-c rational witness),
   epic #813; siblings InDisk.v (64-d), Disk.v.
   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Red: Claude (claude-opus-5); Green: Claude.
   ========================================================================== *)

(* WITNESS {"claimId":"9004-c","topic":"construct","lemma":"mic_unit_square","title":"MIC of the unit square = centre (1/2,1/2), radius 1/2","file":"theories/MaximumInscribedCircle.v"} *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import Distance InDisk.

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  Regions and inscribed disks — the surface 9004-a was missing.          *)
(* -------------------------------------------------------------------------- *)

(** A planar region, as a point predicate.

    Deliberately weaker than a polygon record: the unit-square instance below
    needs nothing more, and the interior of a simple polygon will instantiate
    it directly once #813's polygon rung lands.  Keeping the region abstract
    is what makes this the *smallest* surface that can state a MIC fact. *)
Definition Region : Type := Point -> Prop.

(** [inscribed_disk Rg O r]: the closed disk of centre [O] and radius [r] is
    contained in the region [Rg].

    Membership is [InDisk.InDisk] verbatim — the existing brick (64-d).  What
    is new here is the *containment quantifier over the region*, which is
    precisely what 9004-b observes InDisk does not supply. *)
Definition inscribed_disk (Rg : Region) (O : Point) (r : R) : Prop :=
  0 <= r /\ forall P : Point, InDisk O r P -> Rg P.

(** [max_inscribed_disk Rg O r]: [(O, r)] is a *maximum* inscribed disk of
    [Rg] — it is inscribed, and no inscribed disk of [Rg] has a larger radius.

    This second conjunct is the maximiser.  No other definition in the corpus
    states it, which is why the Polycenter cite had no home before 9004-a. *)
Definition max_inscribed_disk (Rg : Region) (O : Point) (r : R) : Prop :=
  inscribed_disk Rg O r /\
  forall (O' : Point) (r' : R), inscribed_disk Rg O' r' -> r' <= r.

(* -------------------------------------------------------------------------- *)
(* §2  The rational unit-square instance (9004-c).                            *)
(* -------------------------------------------------------------------------- *)

(** The closed unit square [0,1]² as a region. *)
Definition unit_square : Region :=
  fun P : Point => 0 <= px P <= 1 /\ 0 <= py P <= 1.

(** Centre of the maximum inscribed circle of [unit_square]: (1/2, 1/2). *)
Definition mic_unit_square_centre : Point := mkPoint (1/2) (1/2).

(** Radius of the maximum inscribed circle of [unit_square]: 1/2. *)
Definition mic_unit_square_radius : R := 1/2.

(* -------------------------------------------------------------------------- *)
(* §3  Headline — GREEN.                                                      *)
(* -------------------------------------------------------------------------- *)

(** The closed disk of radius 1/2 about (1/2, 1/2) is a maximum inscribed
    disk of the unit square [0,1]².

    Rational throughout: containment holds because every point within 1/2 of
    the centre has both coordinates in [0,1]; maximality holds because an
    inscribed disk of radius r' contains the probes (ox' ± r', oy'), forcing
    0 ≤ ox' − r' and ox' + r' ≤ 1, hence 2r' ≤ 1. *)
Theorem mic_unit_square :
  max_inscribed_disk unit_square mic_unit_square_centre mic_unit_square_radius.
Proof.
  unfold max_inscribed_disk, mic_unit_square_radius.
  split.
  - (* Containment: the disk of radius 1/2 about (1/2, 1/2) is inscribed. *)
    unfold inscribed_disk. split; [lra |].
    intros P [_ Hd].
    assert (Hhalf : 0 <= 1/2) by lra.
    pose proof (proj1 (dist_le_iff_dist_sq_le mic_unit_square_centre P (1/2)
                         Hhalf) Hd) as Hsq.
    unfold dist_sq, mic_unit_square_centre in Hsq. simpl in Hsq.
    pose proof (sqr_nonneg (1/2 - px P)) as Hx2.
    pose proof (sqr_nonneg (1/2 - py P)) as Hy2.
    unfold unit_square. repeat split; nra.
  - (* Maximality: the horizontal probes (ox' ± r', oy') pin the radius. *)
    intros O' r' [Hr' Hincl].
    assert (HL : unit_square (mkPoint (px O' - r') (py O'))).
    { apply Hincl. split; [exact Hr' |].
      apply (proj2 (dist_le_iff_dist_sq_le
                      O' (mkPoint (px O' - r') (py O')) r' Hr')).
      unfold dist_sq. simpl. nra. }
    assert (HR : unit_square (mkPoint (px O' + r') (py O'))).
    { apply Hincl. split; [exact Hr' |].
      apply (proj2 (dist_le_iff_dist_sq_le
                      O' (mkPoint (px O' + r') (py O')) r' Hr')).
      unfold dist_sq. simpl. nra. }
    destruct HL as [[HL0 _] _].
    destruct HR as [[_ HR1] _].
    simpl in HL0, HR1.
    lra.
Qed.

(** Projection: the witness disk is inscribed (first conjunct). *)
Corollary mic_unit_square_inscribed :
  inscribed_disk unit_square mic_unit_square_centre mic_unit_square_radius.
Proof. exact (proj1 mic_unit_square). Qed.

(** Projection: no inscribed disk of the unit square beats radius 1/2
    (second conjunct — the maximiser 9004-b asked for). *)
Corollary mic_unit_square_radius_maximal :
  forall (O' : Point) (r' : R),
    inscribed_disk unit_square O' r' -> r' <= mic_unit_square_radius.
Proof. exact (proj2 mic_unit_square). Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions mic_unit_square.
Print Assumptions mic_unit_square_inscribed.
Print Assumptions mic_unit_square_radius_maximal.

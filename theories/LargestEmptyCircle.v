(* ============================================================================
   NetTopologySuite.Proofs.LargestEmptyCircle
   ----------------------------------------------------------------------------
   LEC lane opener — GREEN (Qed-closed headline).  Board card: PENDING
   (LEC has no in-repo card number; started on operator directive as the
   construct-lane sibling of #9004; Red surface planted and witnessed in
   the previous commit).  Epic #813.

   JTS/NTS twin: algorithm.construct.LargestEmptyCircle — the cell-
   subdivision sibling of MaximumInscribedCircle: given point OBSTACLES and
   a boundary DOMAIN, find a domain centre maximising the distance to the
   nearest obstacle.  Where the MIC maximises the radius of a disk INSIDE
   the region, the LEC maximises the radius of a disk whose interior AVOIDS
   the obstacles.

   Why this file exists.  The corpus (as of #9004) can say a disk is
   inscribed in a region and that its radius is maximal
   (MaximumInscribedCircle.inscribed_disk / max_inscribed_disk).  Nothing
   says a disk is EMPTY of an obstacle set, and nothing maximises an empty
   radius under a domain constraint — the LEC's defining quantifier.  This
   file plants that surface, reusing the 9004-a vocabulary:

     `empty_disk`          every obstacle is at distance >= r from O
     `largest_empty_disk`  centre in the domain, empty, and no domain
                           centre supports a larger empty radius
     `side_midpoints`      the four side midpoints of [0,1]², the fully
                           rational obstacle set

   and closes the rational headline on it:

     `lec_side_midpoints : largest_empty_disk side_midpoints unit_square
                             mic_unit_square_centre mic_unit_square_radius`

   — the LEC of the side midpoints over the unit square IS the MIC witness
   circle: centre (1/2, 1/2), radius 1/2.  The same rational circle is
   maximal from both sides (inscribed w.r.t. the square, empty w.r.t. the
   midpoints): `mic_lec_duality` packages the pair.

   GREEN (this rung).  Both directions are Qed, rational throughout, and
   sqrt-free beyond the Distance.v comparison bridges:

     - emptiness: each midpoint sits at squared distance exactly 1/4 from
       the centre (`dist_ge_of_dist_sq_ge` lifts the squared bound);
     - maximality: an empty radius is dominated squared-wise by the
       distance to EVERY obstacle (`empty_disk_sq_bound`); in the centre's
       quadrant the two adjacent midpoints give
       dist_sq₁ + dist_sq₂ ≤ 1/2 (each of t² + (t−1/2)² is at most 1/4 on
       a half-interval), so 2r'² ≤ 1/2 and r' ≤ 1/2 — the four-way
       `Rle_dec` quadrant split closes by `nra`.
     Projections are exported as `lec_side_midpoints_empty` and
     `lec_side_midpoints_radius_maximal`.

   The claim is indexed in docs/verified-claims.md (claimId pending the
   board card; no eval mirror is minted until the card id exists — no
   invented ancestry).

   No `Admitted`, no `Axiom`, no `Parameter`; 3-axiom classical-reals
   footprint (Distance / InDisk / MaximumInscribedCircle lineage; not in
   audit-exceptions).

   Deliberately NOT in scope on this rung:
     - JTS LargestEmptyCircle's cell subdivision, tolerance loop, and
       interior-point seeding are untouched;
     - polygonal/linear obstacles (JTS accepts geometries) — points only;
     - no medial axis (#9006), no spherical pole of inaccessibility (#9005).

   Registered in `_CoqProject.full` only: it imports
   MaximumInscribedCircle.v (full-only via InDisk.v), so `make host` does
   not see it.

   Refs: epic #813; siblings MaximumInscribedCircle.v (#9004), InDisk.v
   (64-d), Disk.v.
   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import Distance InDisk MaximumInscribedCircle.

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  Empty disks and the constrained maximiser — the LEC surface.           *)
(* -------------------------------------------------------------------------- *)

(** [empty_disk obs O r]: the disk of centre [O] and radius [r] is EMPTY of
    the obstacle set [obs] — every obstacle is at distance at least [r]
    from [O].  Closed form: obstacles ON the bounding circle are allowed
    (JTS: the circle touches its nearest obstacles).

    The obstacle set reuses [Region] (a point predicate); the quantifier
    direction is the dual of [inscribed_disk]: there the DISK's points must
    satisfy the region, here the REGION's points must avoid the disk's
    interior. *)
Definition empty_disk (obs : Region) (O : Point) (r : R) : Prop :=
  0 <= r /\ forall P : Point, obs P -> r <= dist O P.

(** [largest_empty_disk obs dom O r]: [(O, r)] is a LARGEST empty disk of
    [obs] with centre constrained to [dom] — the centre is in the domain,
    the disk is empty, and no domain centre supports a larger empty radius.

    This is the LEC's defining maximiser (JTS LargestEmptyCircle's
    objective), which no other corpus definition states. *)
Definition largest_empty_disk (obs dom : Region) (O : Point) (r : R) : Prop :=
  dom O /\ empty_disk obs O r /\
  forall (O' : Point) (r' : R),
    dom O' -> empty_disk obs O' r' -> r' <= r.

(* -------------------------------------------------------------------------- *)
(* §2  The rational obstacle set: the four side midpoints of [0,1]².          *)
(* -------------------------------------------------------------------------- *)

(** The four side midpoints of the unit square — the MIC witness circle's
    touch points (eval/Claim9004c.v pins), now playing obstacles. *)
Definition side_midpoints : Region :=
  fun P : Point =>
    P = mkPoint 0 (1/2) \/ P = mkPoint 1 (1/2) \/
    P = mkPoint (1/2) 0 \/ P = mkPoint (1/2) 1.

(* -------------------------------------------------------------------------- *)
(* §3  Headline — GREEN.                                                      *)
(* -------------------------------------------------------------------------- *)

(* Comparing at the squared level: an empty radius is dominated by the       *)
(* distance to every obstacle, hence its square by every squared distance.   *)
Lemma dist_ge_of_dist_sq_ge : forall (P Q : Point) (t : R),
  0 <= t -> t * t <= dist_sq P Q -> t <= dist P Q.
Proof.
  intros P Q t Ht Hsq.
  destruct (Rle_dec t (dist P Q)) as [H | H]; [exact H |].
  apply Rnot_le_lt in H.
  pose proof (proj1 (dist_lt_iff_dist_sq_lt P Q t Ht) H). lra.
Qed.

Lemma empty_disk_sq_bound :
  forall (obs : Region) (O : Point) (r : R) (P : Point),
    empty_disk obs O r -> obs P -> r * r <= dist_sq O P.
Proof.
  intros obs O r P [Hr He] HP.
  specialize (He P HP).
  rewrite <- (dist_mul_self O P).
  apply Rmult_le_compat; assumption.
Qed.

(** The LEC of the side midpoints over the unit square is the MIC witness
    circle: centre (1/2, 1/2), radius 1/2.

    Rational throughout: emptiness holds because each midpoint is at squared
    distance exactly 1/4 from the centre; maximality holds because a domain
    centre (x, y) has, in its quadrant, two adjacent midpoints with
    dist_sq₁ + dist_sq₂ ≤ 1/2 (each of x² + (x−1/2)² and y² + (y−1/2)² is at
    most 1/4 on the half-interval), so an empty radius r' has 2r'² ≤ 1/2,
    i.e. r' ≤ 1/2. *)
Theorem lec_side_midpoints :
  largest_empty_disk side_midpoints unit_square
    mic_unit_square_centre mic_unit_square_radius.
Proof.
  unfold largest_empty_disk, mic_unit_square_radius.
  split; [| split].
  - (* Domain: the centre lies in the unit square. *)
    unfold unit_square, mic_unit_square_centre. simpl.
    repeat split; lra.
  - (* Emptiness: each midpoint is at distance >= 1/2 from the centre. *)
    split; [lra |].
    intros P HP.
    apply dist_ge_of_dist_sq_ge; [lra |].
    destruct HP as [-> | [-> | [-> | ->]]];
      unfold dist_sq, mic_unit_square_centre; simpl; lra.
  - (* Maximality: quadrant pairing of adjacent midpoints. *)
    intros O' r' Hdom Hemp.
    pose proof (empty_disk_sq_bound side_midpoints O' r' (mkPoint 0 (1/2))
                  Hemp (or_introl eq_refl)) as HL.
    pose proof (empty_disk_sq_bound side_midpoints O' r' (mkPoint 1 (1/2))
                  Hemp (or_intror (or_introl eq_refl))) as HR.
    pose proof (empty_disk_sq_bound side_midpoints O' r' (mkPoint (1/2) 0)
                  Hemp (or_intror (or_intror (or_introl eq_refl)))) as HB.
    pose proof (empty_disk_sq_bound side_midpoints O' r' (mkPoint (1/2) 1)
                  Hemp (or_intror (or_intror (or_intror eq_refl)))) as HT.
    destruct Hemp as [Hr' _].
    destruct Hdom as [[Hx0 Hx1] [Hy0 Hy1]].
    unfold dist_sq in HL, HR, HB, HT. simpl in HL, HR, HB, HT.
    destruct (Rle_dec (px O') (1/2)) as [Hx | Hx];
      destruct (Rle_dec (py O') (1/2)) as [Hy | Hy].
    + (* x <= 1/2, y <= 1/2: pair left (0,1/2) with bottom (1/2,0). *)
      assert (Hxp : px O' * px O' + (px O' - 1/2) * (px O' - 1/2) <= 1/4)
        by nra.
      assert (Hyp : py O' * py O' + (py O' - 1/2) * (py O' - 1/2) <= 1/4)
        by nra.
      nra.
    + (* x <= 1/2, y > 1/2: pair left (0,1/2) with top (1/2,1). *)
      apply Rnot_le_lt in Hy.
      assert (Hxp : px O' * px O' + (px O' - 1/2) * (px O' - 1/2) <= 1/4)
        by nra.
      assert (Hyp : (py O' - 1/2) * (py O' - 1/2)
                    + (py O' - 1) * (py O' - 1) <= 1/4) by nra.
      nra.
    + (* x > 1/2, y <= 1/2: pair right (1,1/2) with bottom (1/2,0). *)
      apply Rnot_le_lt in Hx.
      assert (Hxp : (px O' - 1/2) * (px O' - 1/2)
                    + (px O' - 1) * (px O' - 1) <= 1/4) by nra.
      assert (Hyp : py O' * py O' + (py O' - 1/2) * (py O' - 1/2) <= 1/4)
        by nra.
      nra.
    + (* x > 1/2, y > 1/2: pair right (1,1/2) with top (1/2,1). *)
      apply Rnot_le_lt in Hx. apply Rnot_le_lt in Hy.
      assert (Hxp : (px O' - 1/2) * (px O' - 1/2)
                    + (px O' - 1) * (px O' - 1) <= 1/4) by nra.
      assert (Hyp : (py O' - 1/2) * (py O' - 1/2)
                    + (py O' - 1) * (py O' - 1) <= 1/4) by nra.
      nra.
Qed.

(** Projection: the witness disk is empty of the side midpoints. *)
Corollary lec_side_midpoints_empty :
  empty_disk side_midpoints mic_unit_square_centre mic_unit_square_radius.
Proof. exact (proj1 (proj2 lec_side_midpoints)). Qed.

(** Projection: no unit-square centre supports an empty radius above 1/2. *)
Corollary lec_side_midpoints_radius_maximal :
  forall (O' : Point) (r' : R),
    unit_square O' -> empty_disk side_midpoints O' r' ->
    r' <= mic_unit_square_radius.
Proof. exact (proj2 (proj2 lec_side_midpoints)). Qed.

(** The duality this configuration exhibits: ONE rational circle — centre
    (1/2, 1/2), radius 1/2 — is simultaneously the maximum disk inscribed
    in the unit square and the largest disk empty of the square's side
    midpoints.  (The midpoints are exactly where the inscribed disk touches
    the boundary: eval/Claim9004c.v's on-circle pins.) *)
Theorem mic_lec_duality :
  max_inscribed_disk unit_square
    mic_unit_square_centre mic_unit_square_radius /\
  largest_empty_disk side_midpoints unit_square
    mic_unit_square_centre mic_unit_square_radius.
Proof. split; [exact mic_unit_square | exact lec_side_midpoints]. Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions lec_side_midpoints.
Print Assumptions lec_side_midpoints_empty.
Print Assumptions lec_side_midpoints_radius_maximal.
Print Assumptions mic_lec_duality.

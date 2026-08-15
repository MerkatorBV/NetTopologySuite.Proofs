(* ============================================================================
   NetTopologySuite.Proofs.LargestEmptyCircle
   ----------------------------------------------------------------------------
   LEC lane opener — RED (unproved claim surface).  Board card: PENDING
   (LEC has no in-repo card number; started on operator directive as the
   construct-lane sibling of #9004).  Epic #813.

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

   and states the rational headline on it:

     `lec_side_midpoints : largest_empty_disk side_midpoints unit_square
                             mic_unit_square_centre mic_unit_square_radius`

   — the LEC of the side midpoints over the unit square IS the MIC witness
   circle: centre (1/2, 1/2), radius 1/2.  The same rational circle is
   maximal from both sides (inscribed w.r.t. the square, empty w.r.t. the
   midpoints), which is the duality this lane will exploit.

   RED GATE.  The headline body is deliberately unproved.  `rocq c` on this
   file fails at `Qed` with "Attempt to save an incomplete proof": an
   unproved obligation, not a syntax error.  Everything above the headline
   elaborates cleanly, so the failing surface is exactly one goal.

   No `Admitted`, no `admit` tactic, no `Axiom`, no `Parameter`
   (scripts/check_admitted.sh stays green, and no registry entry is
   claimed).  Nothing here is added to docs/verified-claims.md — the claim
   is not verified yet.

   Deliberately NOT in scope on this rung:
     - maximality is not proved (that is the Green rung);
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
(* §3  Headline — RED, unproved.                                              *)
(* -------------------------------------------------------------------------- *)

(** The LEC of the side midpoints over the unit square is the MIC witness
    circle: centre (1/2, 1/2), radius 1/2.

    True, and rational throughout: emptiness holds because each midpoint is
    at squared distance exactly 1/4 from the centre; maximality holds
    because a domain centre (x, y) has, in its quadrant, two adjacent
    midpoints with dist_sq₁ + dist_sq₂ ≤ 1/2 (each of x² + (x−1/2)² and
    y² + (y−1/2)² is at most 1/4 on the half-interval), so an empty radius
    r' has 2r'² ≤ 1/2, i.e. r' ≤ 1/2.

    RED: the body is intentionally left open.  Proving it is the Green rung
    and is out of scope here. *)
Theorem lec_side_midpoints :
  largest_empty_disk side_midpoints unit_square
    mic_unit_square_centre mic_unit_square_radius.
Proof.
  (* RED — unproved obligation.  Do not close this with the `admit` tactic
     or with `Admitted`: the corpus invariant forbids both, and the Red gate
     wants `rocq c` to fail here with "Attempt to save an incomplete
     proof". *)
Qed.

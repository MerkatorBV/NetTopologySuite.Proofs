(* ============================================================================
   NetTopologySuite.Proofs.MaximumInscribedCircle
   ----------------------------------------------------------------------------
   Board card #9004 subtask 9004-a — RED (unproved claim surface).

   Zhai, X. et al. (2026), "Polycenter: fast and precise polygon center
   identification", doi:10.1080/13658816.2025.2514056.  Epic #813.

   Why this file exists (9004-a).  The corpus can already say that a point
   lies *in* a disk — `Disk.in_disk` (squared-radius form on a `Disk` record)
   and `InDisk.InDisk` (geometric ‖P−O‖ ≤ r).  Neither says that a disk is
   *inscribed in a region*, and nothing anywhere quantifies **maximality** of
   the inscribed radius (9004-b: membership is not a maximiser).  So #813's
   MIC lane has no module to host a Polycenter cite.  This file plants the
   smallest surface on which that cite can land:

     `Region`             a planar region as a point predicate
     `inscribed_disk`     the closed disk (O, r) is contained in the region
     `max_inscribed_disk` inscribed, and no inscribed disk has larger radius
     `unit_square`        the fully rational region [0,1]²

   and states the rational headline (9004-c) on it:

     `mic_unit_square : max_inscribed_disk unit_square (1/2, 1/2) (1/2)`

   The witness is rational and exact — centre (1/2, 1/2), radius 1/2 — so the
   Green rung will need no irrational arithmetic.

   RED GATE.  The headline body is deliberately unproved.  `rocq c` on this
   file fails at `Qed` with "Attempt to save an incomplete proof": an
   unproved obligation, not a syntax error.  Everything above the headline
   elaborates cleanly, so the failing surface is exactly one goal.

   No `Admitted`, no `admit` tactic, no `Axiom`, no `Parameter`
   (scripts/check_admitted.sh stays green, and no registry entry is claimed).
   Nothing here is added to docs/verified-claims.md — the claim is not
   verified yet.

   Deliberately NOT in scope on this rung:
     - maximality is not proved (that is the Green rung);
     - Polycenter's cell subdivision and the achievable-radius bound over a
       cell (9004-d) are untouched;
     - `InDisk.v` is reused as-is and not modified (9004-b);
     - no medial axis (that is #9006), no spherical pole of inaccessibility
       (that is #9005).

   Registered in `_CoqProject.full` only: it depends on `InDisk.v`, which is
   not part of the Stdlib-only host layer, so `make host` does not see it.

   Refs: board #9004 (9004-a claim surface, 9004-c rational witness),
   epic #813; siblings InDisk.v (64-d), Disk.v.
   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude (claude-opus-5)
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import Distance InDisk.

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  Regions and inscribed disks — the surface 9004-a is missing.           *)
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

    This second conjunct is the maximiser.  No definition in the corpus
    currently states it, which is why the Polycenter cite has no home. *)
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
(* §3  Headline — RED, unproved.                                              *)
(* -------------------------------------------------------------------------- *)

(** The closed disk of radius 1/2 about (1/2, 1/2) is a maximum inscribed
    disk of the unit square [0,1]².

    True, and rational throughout: containment holds because every point
    within 1/2 of the centre has both coordinates in [0,1]; maximality holds
    because an inscribed disk of radius r' forces 0 ≤ ox − r' and
    ox + r' ≤ 1, hence 2r' ≤ 1.

    RED (9004-a / 9004-c): the body is intentionally left open.  Proving it
    is the Green rung and is out of scope here. *)
Theorem mic_unit_square :
  max_inscribed_disk unit_square mic_unit_square_centre mic_unit_square_radius.
Proof.
  (* RED — unproved obligation.  Do not close this with the `admit` tactic
     or with `Admitted`: the corpus invariant forbids both, and the Red gate
     wants `rocq c` to fail here with "Attempt to save an incomplete
     proof". *)
Qed.

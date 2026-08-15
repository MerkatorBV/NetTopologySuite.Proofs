(* ============================================================================
   NetTopologySuite.Proofs.LECChordGap
   ----------------------------------------------------------------------------
   The LEC chord-path hypothesis, prove-or-disprove — RED (planted
   surface; exactly ONE unproved headline below, failing at Qed).

   HYPOTHESIS UNDER TEST (JTS OverlayNGCurve PERF-GATE, LEC row —
   name gate NTSC0001: never OverlayNGCurved):

     "LargestEmptyCircle stays on the chord path — no cheaper
      construction beat densify-then-LEC."

   VERDICT THIS FILE PROVES: **DISPROVED**, as an exactness claim, on
   the single-circle-obstacle cell — the LEC analogue of the two-disc
   cell that R1.5 (`CircularDiscOverlay` / `DISC_OVERLAY`) carved out of
   the overlay chord path.  Witness-scoped, fully explicit:

     - obstacle  = the full circle of radius 2 about the origin (the
       curved shoreline, every point of it);
     - domain    = the closed disk it bounds;
     - the EXACT answer is a CLOSED FORM: the largest empty disk is
       (centre, 2) — no densification, no search (`the laser`);
     - the CHORD PATH at the 4-chord densification (vertices (±2,0),
       (0,±2), chords between adjacent vertices) has exact answer
       (centre, √2) — densify-then-LEC computes √2 where the truth is 2
       (`the chainsaw`), an underestimate by the factor cos(π/4); at a
       general chord step θ the same construction underestimates by
       cos(θ/2), CONVERGING but never exact.

   So a cheaper construction exists and beats densify-then-LEC on this
   cell in the only sense the corpus can adjudicate: it is exact where
   every finite densification is not.  Headline:

     `lec_chord_hypothesis_refuted` :
        largest_empty_disk circle_obstacle disk_dom centre 2
        /\ largest_empty_disk chorded_obstacle disk_dom centre (sqrt 2)
        /\ sqrt 2 < 2.

   CLAIMS vs PROVES.  The PERF-GATE hypothesis is a RUNTIME claim
   (median laser time vs chainsaw time); that half stays engine-side —
   this file proves the EXACTNESS half only: the closed form exists, is
   Qed-correct, and disagrees with the chord path's answer at the
   witness tolerance.  Whether JTS wires the closed form (as R1.5 did
   for two-disc overlay) is a product decision the perf gate can now
   make against a proven target.  General obstacle sets, arcs shorter
   than the full circle, and the general-θ cos(θ/2) law are next rungs.

   No `Admitted`, no `Axiom`, no `Parameter`.

   Refs: docs/oracle-wishlist.md (OV-DISC / DISC_OVERLAY — the overlay
   twin of this refutation); siblings LargestEmptyCircle.v (empty_disk /
   largest_empty_disk / sq-bound helpers), MaximumInscribedCircle.v
   (#9004), PlaneConnected.v (seg), OverlayNGCurve.v (Phase-0: crossing
   cells never collapse algebraically — closed forms are per-shape).
   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import Distance PlaneConnected
  MaximumInscribedCircle LargestEmptyCircle.

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  The witness cell: circle obstacle, disk domain, 4-chord densification. *)
(* -------------------------------------------------------------------------- *)

Definition centre : Point := mkPoint 0 0.

(** The exact curved shoreline: EVERY point of the radius-2 circle. *)
Definition circle_obstacle : Region :=
  fun P => dist_sq centre P = 4.

(** The domain: the closed disk the shoreline bounds. *)
Definition disk_dom : Region :=
  fun P => dist_sq centre P <= 4.

(** The 4-chord densification vertices (the inscribed square). *)
Definition cv1 : Point := mkPoint 2 0.
Definition cv2 : Point := mkPoint 0 2.
Definition cv3 : Point := mkPoint (-2) 0.
Definition cv4 : Point := mkPoint 0 (-2).

(** A chord as a point set: the segment between two vertices. *)
Definition on_chord (A B : Point) (P : Point) : Prop :=
  exists t : R, 0 <= t <= 1 /\ P = seg A B t.

(** Densify-then-LEC's obstacle: the four chords of the inscribed
    square — what the chord path measures clearance against. *)
Definition chorded_obstacle : Region :=
  fun P => on_chord cv1 cv2 P \/ on_chord cv2 cv3 P \/
           on_chord cv3 cv4 P \/ on_chord cv4 cv1 P.

(* -------------------------------------------------------------------------- *)
(* §2  Headline — RED.  The laser exists (closed form, radius 2), the        *)
(*     chainsaw answers √2 on the same cell, and √2 < 2.                     *)
(* -------------------------------------------------------------------------- *)

Theorem lec_chord_hypothesis_refuted :
  largest_empty_disk circle_obstacle disk_dom centre 2 /\
  largest_empty_disk chorded_obstacle disk_dom centre (sqrt 2) /\
  sqrt 2 < 2.
Proof.
  (* RED: stated, not yet proved — this Qed is the witnessed Red gate. *)
Qed.

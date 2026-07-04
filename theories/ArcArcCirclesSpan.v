(* ============================================================================
   NetTopologySuite.Proofs.ArcArcCirclesSpan
   ----------------------------------------------------------------------------
   Issue #64 ask #5b / JTS curve-awareness N-AA: promoting the radical-line
   BOTH-CIRCLES existence (`ArcArcCircles.arc_arc_circles_intersect`) to the
   full `arc_arc_intersects` predicate (both circles AND both spans).

   `ArcArcCircles.v` closes the "quartic arc-arc intersection coords" frontier
   named in the issue triage: `two_circles_radical_point` gives EXPLICIT
   closed-form coordinates (radical axis + sqrt-discriminant chord height) for
   a point on both circumcircles of two properly-intersecting circles -- no
   atan2, no Classic, three-axiom.  Its own header names exactly what remains:

     "DEFERRED (honest scope): `arc_span_contains` for the radical-line
      points: angular sector membership needs atan2 and stays deferred;
      `arc_arc_intersects` (requires both circles AND both spans)."

   This file closes that wiring gap the same way `ArcArcSound.v`'s conditional
   floor (`arc_arc_intersects_of_chord_cross_cond`) closed the analogous gap
   for the chord-cross route: bundle the missing atan2-dependent span facts as
   ONE named hypothesis on an arbitrary common-circle point X, so the
   headline is a straight composition of already-Qed algebra
   (`arc_arc_circles_intersect`) with that bundled hypothesis -- no new
   atan2/trig content, no re-derivation of the radical-line construction.

   Proved here (THREE-AXIOM, no `Classic`, no `Admitted`/`Axiom`/`Parameter`):
     `arc_arc_intersects_of_circles_and_span` -- proper circle intersection
       (the same `0 < d`, `|r1-r2| < d < r1+r2` hypotheses as
       `arc_arc_circles_intersect`) plus the bundled span hypothesis gives
       `arc_arc_intersects a1 a2` directly.

   DEFERRED (honest scope, unchanged): discharging the bundled span hypothesis
   itself for the EXPLICIT radical-line point (needs atan2 sector membership,
   the same frontier `ArcArcCircles.v` and `ArcChordSound.v` already name) is
   untouched here.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
   ========================================================================== *)

From Stdlib Require Import Reals.
From NTS.Proofs Require Import Distance CurveGeometry ArcOrient ArcIntersect
  ArcArcCircles.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  Both-circles-and-spans promotion (the N-AA existence headline).        *)
(* -------------------------------------------------------------------------- *)

Theorem arc_arc_intersects_of_circles_and_span :
  forall a1 a2 : CircularArc,
    valid_arc a1 ->
    valid_arc a2 ->
    0 < dist (arc_center a1) (arc_center a2) ->
    Rabs (arc_radius a1 - arc_radius a2) < dist (arc_center a1) (arc_center a2) ->
    dist (arc_center a1) (arc_center a2) < arc_radius a1 + arc_radius a2 ->
    (forall X : Point,
       inCircle_R (arc_start a1) (arc_mid a1) (arc_end a1) X = 0 ->
       inCircle_R (arc_start a2) (arc_mid a2) (arc_end a2) X = 0 ->
       arc_span_contains a1 X /\ arc_span_contains a2 X) ->
    arc_arc_intersects a1 a2.
Proof.
  intros a1 a2 Hva1 Hva2 Hdpos Hrabs Hdlt Hbridge.
  destruct (arc_arc_circles_intersect a1 a2 Hva1 Hva2 Hdpos Hrabs Hdlt)
    as [X [Hc1 Hc2]].
  destruct (Hbridge X Hc1 Hc2) as [Hs1 Hs2].
  exists X. split; [exact Hc1 | split; [exact Hc2 | split; [exact Hs1 | exact Hs2]]].
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  Audit footprint.                                                       *)
(* -------------------------------------------------------------------------- *)

Print Assumptions arc_arc_intersects_of_circles_and_span.

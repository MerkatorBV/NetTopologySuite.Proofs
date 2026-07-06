(* ============================================================================
   NetTopologySuite.Proofs.ArcArcQuartic
   ----------------------------------------------------------------------------
   Issue #64 round-2 open items ② and ④ (N-AA quartic coordinate identity and
   atan2 sector-membership discharge).

   The corpus already has:
     · `ArcArcCircles.radical_points_on_circles` — both named radical-line
       points lie on both circumcircles (`dist_sq Oi rp± = ri²`).
     · `ArcArcCirclesSpan.arc_arc_intersects_of_circles_and_radical_signs` —
       promotes proper-circle-intersection to `arc_arc_intersects` when the
       chord-sign span predicate holds at one of the two named points.
     · `ArcSpanAtan2.arc_span_contains_atan2_iff_chord_sign` — for a valid arc
       and any on-circumcircle point, the atan2 sector test is equivalent to
       the chord-sign test, unconditionally (every sweep, including reflex arcs).

   This file closes the two remaining gaps:

   §1  Vieta coordinate identities (item ④ — the quartic certificate).
       The two intersection candidate coordinates satisfy:
         px rp+ + px rp- = 2·(px O1 + a·ux)     (x Vieta sum)
         py rp+ + py rp- = 2·(py O1 + a·uy)     (y Vieta sum)
         px rp+ · px rp- = (px O1+a·ux)² − (h·uy)²   (x Vieta product)
         py rp+ · py rp- = (py O1+a·uy)² − (h·ux)²   (y Vieta product)
       These are the Vieta formulas for the degree-2 polynomial whose roots
       are the radical-line intersection x- (resp. y-) coordinates — the
       polynomial certificate that makes the "quartic" system reducible to a
       quadratic after the radical-axis substitution.  Pure `ring` proofs; no
       geometric hypotheses.

   §2  Span atan2 ↔ chord-sign for the explicit radical points (item ②).
       Four helper lemmas confirm each radical point lies on the correct
       circumcircle (`inCircle_R = 0`), enabling the iff bridge.  Each helper
       uses `radical_points_on_circles` + `inCircle_R_zero_of_equidistant`.

   §3  atan2-driven promotion to `arc_arc_intersects` (headline).
       `arc_arc_intersects_of_atan2_radical_span` — if the atan2 sector test
       holds for one of the two named radical points w.r.t. both arcs, then
       `arc_arc_intersects a1 a2` follows by converting via the §2 iff lemmas
       and applying `arc_arc_intersects_of_circles_and_radical_signs`.

   Proved here (4-AXIOM: inherits `Classical_Prop.classic` transitively via
   `ArcSpanAtan2`/`Atan2`/`AngleBetween` — same lineage and exemption as
   `ArcSpanAtan2.v`, see `docs/audit-exceptions.txt`).  No `Admitted`, no
   `Axiom`, no `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import Distance CurveGeometry ArcOrient ArcIntersect
  ArcChordApprox ArcOffsetThreePoint ArcArcCircles ArcArcCirclesSpan ArcSpanAtan2.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  Vieta coordinate identities (the quartic certificate).                 *)
(* -------------------------------------------------------------------------- *)

(* Sum of x-coordinates of the two radical-line intersection candidates.
   Proof: pure ring identity after unfolding the point constructors. *)
Lemma radical_point_x_sum :
  forall (O1 O2 : Point) (r1 r2 : R),
    px (radical_point_plus  O1 O2 r1 r2) +
    px (radical_point_minus O1 O2 r1 r2) =
    2 * (px O1 + radical_axis_a O1 O2 r1 r2 * radical_axis_ux O1 O2).
Proof.
  intros O1 O2 r1 r2.
  unfold radical_point_plus, radical_point_minus. cbn [px]. ring.
Qed.

(* Sum of y-coordinates. *)
Lemma radical_point_y_sum :
  forall (O1 O2 : Point) (r1 r2 : R),
    py (radical_point_plus  O1 O2 r1 r2) +
    py (radical_point_minus O1 O2 r1 r2) =
    2 * (py O1 + radical_axis_a O1 O2 r1 r2 * radical_axis_uy O1 O2).
Proof.
  intros O1 O2 r1 r2.
  unfold radical_point_plus, radical_point_minus. cbn [py]. ring.
Qed.

(* Product of x-coordinates: difference-of-squares identity. *)
Lemma radical_point_x_prod :
  forall (O1 O2 : Point) (r1 r2 : R),
    px (radical_point_plus  O1 O2 r1 r2) *
    px (radical_point_minus O1 O2 r1 r2) =
    (px O1 + radical_axis_a O1 O2 r1 r2 * radical_axis_ux O1 O2) *
    (px O1 + radical_axis_a O1 O2 r1 r2 * radical_axis_ux O1 O2) -
    (radical_axis_h O1 O2 r1 r2 * radical_axis_uy O1 O2) *
    (radical_axis_h O1 O2 r1 r2 * radical_axis_uy O1 O2).
Proof.
  intros O1 O2 r1 r2.
  unfold radical_point_plus, radical_point_minus. cbn [px]. ring.
Qed.

(* Product of y-coordinates: difference-of-squares identity. *)
Lemma radical_point_y_prod :
  forall (O1 O2 : Point) (r1 r2 : R),
    py (radical_point_plus  O1 O2 r1 r2) *
    py (radical_point_minus O1 O2 r1 r2) =
    (py O1 + radical_axis_a O1 O2 r1 r2 * radical_axis_uy O1 O2) *
    (py O1 + radical_axis_a O1 O2 r1 r2 * radical_axis_uy O1 O2) -
    (radical_axis_h O1 O2 r1 r2 * radical_axis_ux O1 O2) *
    (radical_axis_h O1 O2 r1 r2 * radical_axis_ux O1 O2).
Proof.
  intros O1 O2 r1 r2.
  unfold radical_point_plus, radical_point_minus. cbn [py]. ring.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  Each radical point lies on each circumcircle (inCircle_R = 0).         *)
(*                                                                            *)
(* Helper lemmas: four combinations of {plus, minus} × {a1, a2}.             *)
(* Proof chain (identical structure for each):                                *)
(*   1. radical_points_on_circles → dist_sq Oi rp± = ri²                    *)
(*   2. arc_radius_eq_sqrt + sqrt_sqrt + arc_radius_sq → ri² = dist_sq Oi S  *)
(*   3. inCircle_R_zero_of_equidistant closes the goal.                       *)
(* -------------------------------------------------------------------------- *)

Lemma radical_plus_on_circle_a1 :
  forall a1 a2 : CircularArc,
    valid_arc a1 -> valid_arc a2 ->
    0 < dist (arc_center a1) (arc_center a2) ->
    Rabs (arc_radius a1 - arc_radius a2) < dist (arc_center a1) (arc_center a2) ->
    dist (arc_center a1) (arc_center a2) < arc_radius a1 + arc_radius a2 ->
    inCircle_R (arc_start a1) (arc_mid a1) (arc_end a1)
      (radical_point_plus (arc_center a1) (arc_center a2)
                          (arc_radius a1) (arc_radius a2)) = 0.
Proof.
  intros a1 a2 Hva1 Hva2 Hdpos Hrabs Hdlt.
  destruct (radical_points_on_circles
              (arc_center a1) (arc_center a2) (arc_radius a1) (arc_radius a2)
              (arc_radius_pos a1 Hva1) (arc_radius_pos a2 Hva2)
              Hdpos Hrabs Hdlt)
    as [[HdP1 _] _].
  apply inCircle_R_zero_of_equidistant; [exact Hva1 |].
  assert (Hr1sq : arc_radius a1 * arc_radius a1
                  = dist_sq (arc_center a1) (arc_start a1)).
  { rewrite arc_radius_eq_sqrt. rewrite sqrt_sqrt; [| apply arc_radius_sq_nonneg].
    unfold arc_radius_sq. reflexivity. }
  lra.
Qed.

Lemma radical_plus_on_circle_a2 :
  forall a1 a2 : CircularArc,
    valid_arc a1 -> valid_arc a2 ->
    0 < dist (arc_center a1) (arc_center a2) ->
    Rabs (arc_radius a1 - arc_radius a2) < dist (arc_center a1) (arc_center a2) ->
    dist (arc_center a1) (arc_center a2) < arc_radius a1 + arc_radius a2 ->
    inCircle_R (arc_start a2) (arc_mid a2) (arc_end a2)
      (radical_point_plus (arc_center a1) (arc_center a2)
                          (arc_radius a1) (arc_radius a2)) = 0.
Proof.
  intros a1 a2 Hva1 Hva2 Hdpos Hrabs Hdlt.
  destruct (radical_points_on_circles
              (arc_center a1) (arc_center a2) (arc_radius a1) (arc_radius a2)
              (arc_radius_pos a1 Hva1) (arc_radius_pos a2 Hva2)
              Hdpos Hrabs Hdlt)
    as [[_ HdP2] _].
  apply inCircle_R_zero_of_equidistant; [exact Hva2 |].
  assert (Hr2sq : arc_radius a2 * arc_radius a2
                  = dist_sq (arc_center a2) (arc_start a2)).
  { rewrite arc_radius_eq_sqrt. rewrite sqrt_sqrt; [| apply arc_radius_sq_nonneg].
    unfold arc_radius_sq. reflexivity. }
  lra.
Qed.

Lemma radical_minus_on_circle_a1 :
  forall a1 a2 : CircularArc,
    valid_arc a1 -> valid_arc a2 ->
    0 < dist (arc_center a1) (arc_center a2) ->
    Rabs (arc_radius a1 - arc_radius a2) < dist (arc_center a1) (arc_center a2) ->
    dist (arc_center a1) (arc_center a2) < arc_radius a1 + arc_radius a2 ->
    inCircle_R (arc_start a1) (arc_mid a1) (arc_end a1)
      (radical_point_minus (arc_center a1) (arc_center a2)
                           (arc_radius a1) (arc_radius a2)) = 0.
Proof.
  intros a1 a2 Hva1 Hva2 Hdpos Hrabs Hdlt.
  destruct (radical_points_on_circles
              (arc_center a1) (arc_center a2) (arc_radius a1) (arc_radius a2)
              (arc_radius_pos a1 Hva1) (arc_radius_pos a2 Hva2)
              Hdpos Hrabs Hdlt)
    as [_ [HdM1 _]].
  apply inCircle_R_zero_of_equidistant; [exact Hva1 |].
  assert (Hr1sq : arc_radius a1 * arc_radius a1
                  = dist_sq (arc_center a1) (arc_start a1)).
  { rewrite arc_radius_eq_sqrt. rewrite sqrt_sqrt; [| apply arc_radius_sq_nonneg].
    unfold arc_radius_sq. reflexivity. }
  lra.
Qed.

Lemma radical_minus_on_circle_a2 :
  forall a1 a2 : CircularArc,
    valid_arc a1 -> valid_arc a2 ->
    0 < dist (arc_center a1) (arc_center a2) ->
    Rabs (arc_radius a1 - arc_radius a2) < dist (arc_center a1) (arc_center a2) ->
    dist (arc_center a1) (arc_center a2) < arc_radius a1 + arc_radius a2 ->
    inCircle_R (arc_start a2) (arc_mid a2) (arc_end a2)
      (radical_point_minus (arc_center a1) (arc_center a2)
                           (arc_radius a1) (arc_radius a2)) = 0.
Proof.
  intros a1 a2 Hva1 Hva2 Hdpos Hrabs Hdlt.
  destruct (radical_points_on_circles
              (arc_center a1) (arc_center a2) (arc_radius a1) (arc_radius a2)
              (arc_radius_pos a1 Hva1) (arc_radius_pos a2 Hva2)
              Hdpos Hrabs Hdlt)
    as [_ [_ HdM2]].
  apply inCircle_R_zero_of_equidistant; [exact Hva2 |].
  assert (Hr2sq : arc_radius a2 * arc_radius a2
                  = dist_sq (arc_center a2) (arc_start a2)).
  { rewrite arc_radius_eq_sqrt. rewrite sqrt_sqrt; [| apply arc_radius_sq_nonneg].
    unfold arc_radius_sq. reflexivity. }
  lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2b  atan2 span ↔ chord-sign span iff for each radical point / arc pair.  *)
(* -------------------------------------------------------------------------- *)

Lemma radical_plus_span_iff_a1 :
  forall a1 a2 : CircularArc,
    valid_arc a1 -> valid_arc a2 ->
    0 < dist (arc_center a1) (arc_center a2) ->
    Rabs (arc_radius a1 - arc_radius a2) < dist (arc_center a1) (arc_center a2) ->
    dist (arc_center a1) (arc_center a2) < arc_radius a1 + arc_radius a2 ->
    (arc_span_contains_atan2 a1
       (radical_point_plus (arc_center a1) (arc_center a2)
                           (arc_radius a1) (arc_radius a2))
     <->
     arc_span_contains a1
       (radical_point_plus (arc_center a1) (arc_center a2)
                           (arc_radius a1) (arc_radius a2))).
Proof.
  intros a1 a2 Hva1 Hva2 Hdpos Hrabs Hdlt.
  apply arc_span_contains_atan2_iff_chord_sign; [exact Hva1 |].
  exact (radical_plus_on_circle_a1 a1 a2 Hva1 Hva2 Hdpos Hrabs Hdlt).
Qed.

Lemma radical_plus_span_iff_a2 :
  forall a1 a2 : CircularArc,
    valid_arc a1 -> valid_arc a2 ->
    0 < dist (arc_center a1) (arc_center a2) ->
    Rabs (arc_radius a1 - arc_radius a2) < dist (arc_center a1) (arc_center a2) ->
    dist (arc_center a1) (arc_center a2) < arc_radius a1 + arc_radius a2 ->
    (arc_span_contains_atan2 a2
       (radical_point_plus (arc_center a1) (arc_center a2)
                           (arc_radius a1) (arc_radius a2))
     <->
     arc_span_contains a2
       (radical_point_plus (arc_center a1) (arc_center a2)
                           (arc_radius a1) (arc_radius a2))).
Proof.
  intros a1 a2 Hva1 Hva2 Hdpos Hrabs Hdlt.
  apply arc_span_contains_atan2_iff_chord_sign; [exact Hva2 |].
  exact (radical_plus_on_circle_a2 a1 a2 Hva1 Hva2 Hdpos Hrabs Hdlt).
Qed.

Lemma radical_minus_span_iff_a1 :
  forall a1 a2 : CircularArc,
    valid_arc a1 -> valid_arc a2 ->
    0 < dist (arc_center a1) (arc_center a2) ->
    Rabs (arc_radius a1 - arc_radius a2) < dist (arc_center a1) (arc_center a2) ->
    dist (arc_center a1) (arc_center a2) < arc_radius a1 + arc_radius a2 ->
    (arc_span_contains_atan2 a1
       (radical_point_minus (arc_center a1) (arc_center a2)
                            (arc_radius a1) (arc_radius a2))
     <->
     arc_span_contains a1
       (radical_point_minus (arc_center a1) (arc_center a2)
                            (arc_radius a1) (arc_radius a2))).
Proof.
  intros a1 a2 Hva1 Hva2 Hdpos Hrabs Hdlt.
  apply arc_span_contains_atan2_iff_chord_sign; [exact Hva1 |].
  exact (radical_minus_on_circle_a1 a1 a2 Hva1 Hva2 Hdpos Hrabs Hdlt).
Qed.

Lemma radical_minus_span_iff_a2 :
  forall a1 a2 : CircularArc,
    valid_arc a1 -> valid_arc a2 ->
    0 < dist (arc_center a1) (arc_center a2) ->
    Rabs (arc_radius a1 - arc_radius a2) < dist (arc_center a1) (arc_center a2) ->
    dist (arc_center a1) (arc_center a2) < arc_radius a1 + arc_radius a2 ->
    (arc_span_contains_atan2 a2
       (radical_point_minus (arc_center a1) (arc_center a2)
                            (arc_radius a1) (arc_radius a2))
     <->
     arc_span_contains a2
       (radical_point_minus (arc_center a1) (arc_center a2)
                            (arc_radius a1) (arc_radius a2))).
Proof.
  intros a1 a2 Hva1 Hva2 Hdpos Hrabs Hdlt.
  apply arc_span_contains_atan2_iff_chord_sign; [exact Hva2 |].
  exact (radical_minus_on_circle_a2 a1 a2 Hva1 Hva2 Hdpos Hrabs Hdlt).
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  atan2-driven promotion to `arc_arc_intersects` (the N-AA headline).   *)
(*                                                                            *)
(* Converts the atan2 span hypothesis to chord-sign form via the §2 iff      *)
(* lemmas, then applies the already-Qed promotion theorem from               *)
(* `ArcArcCirclesSpan`.  No new geometric content; the circle-intersection   *)
(* hypotheses are passed through unchanged.                                   *)
(*                                                                            *)
(* Why the disjunction is the right hypothesis shape: `arc_arc_intersects`   *)
(* is an existential -- it needs ONE point on both circumcircles AND in both  *)
(* spans.  `two_circles_radical_point_unique` (ArcArcCircles §5) guarantees  *)
(* every point on both circles equals `radical_point_plus` or `_minus`.  So  *)
(* the question reduces to: does `plus` lie in both spans, or does `minus`?  *)
(* Checking the two arcs against the SAME root is therefore the minimal       *)
(* sufficient condition -- a mixed hypothesis (plus for a1, minus for a2)     *)
(* would not witness a single shared point.                                   *)
(* -------------------------------------------------------------------------- *)

Theorem arc_arc_intersects_of_atan2_radical_span :
  forall a1 a2 : CircularArc,
    valid_arc a1 ->
    valid_arc a2 ->
    0 < dist (arc_center a1) (arc_center a2) ->
    Rabs (arc_radius a1 - arc_radius a2) < dist (arc_center a1) (arc_center a2) ->
    dist (arc_center a1) (arc_center a2) < arc_radius a1 + arc_radius a2 ->
    ((arc_span_contains_atan2 a1
        (radical_point_plus (arc_center a1) (arc_center a2)
                            (arc_radius a1) (arc_radius a2)) /\
      arc_span_contains_atan2 a2
        (radical_point_plus (arc_center a1) (arc_center a2)
                            (arc_radius a1) (arc_radius a2)))
     \/
     (arc_span_contains_atan2 a1
        (radical_point_minus (arc_center a1) (arc_center a2)
                             (arc_radius a1) (arc_radius a2)) /\
      arc_span_contains_atan2 a2
        (radical_point_minus (arc_center a1) (arc_center a2)
                             (arc_radius a1) (arc_radius a2)))) ->
    arc_arc_intersects a1 a2.
Proof.
  intros a1 a2 Hva1 Hva2 Hdpos Hrabs Hdlt Hatan2.
  apply (arc_arc_intersects_of_circles_and_radical_signs
           a1 a2 Hva1 Hva2 Hdpos Hrabs Hdlt).
  destruct Hatan2 as [[H1 H2] | [H1 H2]].
  - left. split.
    + apply (radical_plus_span_iff_a1 a1 a2 Hva1 Hva2 Hdpos Hrabs Hdlt).
      exact H1.
    + apply (radical_plus_span_iff_a2 a1 a2 Hva1 Hva2 Hdpos Hrabs Hdlt).
      exact H2.
  - right. split.
    + apply (radical_minus_span_iff_a1 a1 a2 Hva1 Hva2 Hdpos Hrabs Hdlt).
      exact H1.
    + apply (radical_minus_span_iff_a2 a1 a2 Hva1 Hva2 Hdpos Hrabs Hdlt).
      exact H2.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Audit footprint.                                                       *)
(* -------------------------------------------------------------------------- *)

Print Assumptions radical_point_x_sum.
Print Assumptions radical_point_y_sum.
Print Assumptions radical_point_x_prod.
Print Assumptions radical_point_y_prod.
Print Assumptions arc_arc_intersects_of_atan2_radical_span.

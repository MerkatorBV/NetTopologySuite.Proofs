(* ============================================================================
   NetTopologySuite.Proofs.ArcArcCircles
   ----------------------------------------------------------------------------
   Issue #64 ask #5b / JTS curve-awareness N-AA: ARC-ARC CIRCLES INTERSECT,
   radical-line coordinate existence (Stage B).

   JTS issue #1195 describes the arc-arc intersection algorithm as "computes
   radical line between two circles; retains roots within both directed sweeps."
   The ARC_ARC_XY oracle mode (PR #220) implements this: for two circumcircles
   with centres O1, O2, radii r1, r2, inter-centre distance d:

       a  = (d² + r1² − r2²) / (2·d)     -- signed distance along O1 → O2
       M  = O1 + a·u                      -- foot of the radical axis
       h  = √(r1² − a²)                   -- half-chord height
       P± = M ± h·perp(u)                 -- the two candidate points

   ArcArcSound.v (merged PR #223, first slice) explicitly defers: "the
   UNCONDITIONAL both-circles existence for two arcs that cross at interior
   points (the radical-line / sqrt-discriminant coordinate story)."  This file
   closes that gap.

   Proved here (all THREE-AXIOM, no atan2/sin_lt_x, no Classic):

     §1  `inCircle_R_concyclic` — four points A,B,C,P at equal squared
         distance from a common centre O ⇒ the Shewchuk in-circle determinant
         inCircle_R A B C P = 0.  Proved by translating O to the origin
         (`inCircle_R_translation_invariant`), which removes the centre's
         coordinates, then `nsatz` on the resulting polynomial identity.
         `inCircle_R_zero_of_equidistant` — corollary: P equidistant from
         the circumcenter as the control points ⇒ inCircle_R = 0
         (arc_center_equidistant supplies OA=OB=OC, so all four concyclic).
         `inCircle_R_circle_factored` + `inCircle_R_zero_implies_equidistant`
         — CONVERSE (§1c): for a valid arc (orient2d ≠ 0), inCircle_R = 0
         forces P onto the circumcircle, i.e. dist_sq O P = dist_sq O A.
         Together these give the full `iff`.

     §3  `two_circles_radical_point` — HEADLINE unconditional existence: for
         properly-intersecting circles (|r1−r2| < d < r1+r2), the
         radical-line formula constructs an explicit point on BOTH circles.
         Pure algebra: ring + lra after asserting h·h = r1²−a² (sqrt) and
         ux²+uy² = 1 (unit vector).

     §4  `arc_arc_circles_intersect` — arc-level corollary: proper circle
         intersection ⇒ ∃ X with inCircle_R = 0 on both arcs' circumcircles.

   DEFERRED (honest scope in the header):
     - `arc_span_contains` for the radical-line points: proved via an
       atan2-based angular sector test in `ArcSpanAtan2.v`
       (`arc_span_contains_atan2_iff_chord_sign`, unconditional in the
       sweep), but only wired to a CHECKABLE hypothesis on the two named
       radical points (`ArcArcCirclesSpan.arc_arc_intersects_of_circles_and_radical_signs`),
       not derived unconditionally -- two properly-intersecting circles can
       still have arcs whose spans miss the crossing entirely, so no
       hypothesis-free version can exist.
     - `arc_arc_intersects` (requires both circles AND both spans).
     - Binary64 soundness of ARC_ARC_XY.  Sweep >= pi / reflex arcs are NOT a
       live gap here: `ArcSpanAtan2.arc_span_contains_atan2_iff_chord_sign`
       proves `arc_span_contains` exact for every sweep.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude (claude-opus-4-8)
   ========================================================================== *)

From Stdlib Require Import Reals Lra Field Nsatz.
From NTS.Proofs Require Import Distance CurveGeometry ArcOrient ArcChordApprox
  ArcOffsetThreePoint.
Local Open Scope R_scope.

(* ========================================================================== *)
(* §1a  Four concyclic points ⇒ inCircle_R = 0                                *)
(*                                                                            *)
(* If A, B, C, P all lie at the same squared distance from a common centre O *)
(* (i.e. they are concyclic on the circle about O), the Shewchuk in-circle   *)
(* determinant vanishes.  We do NOT need the factored `D·(r²−||OP||²)` form  *)
(* -- the `= 0` conclusion is all the downstream proofs use, and it is the    *)
(* easiest possible shape for the Gröbner-basis tactic.                       *)
(*                                                                            *)
(* Proof: inCircle_R is translation-invariant, so shift O to the origin.      *)
(* This eliminates the centre's two coordinates (and the Ox²+Oy² cross terms *)
(* that otherwise blow up nsatz), leaving four points of equal squared norm. *)
(* ========================================================================== *)

Lemma inCircle_R_concyclic :
  forall (A B C P O : Point),
    dist_sq O A = dist_sq O B ->
    dist_sq O B = dist_sq O C ->
    dist_sq O C = dist_sq O P ->
    inCircle_R A B C P = 0.
Proof.
  intros A B C P O HAB HBC HCP.
  rewrite <- (inCircle_R_translation_invariant A B C P (- px O) (- py O)).
  unfold dist_sq, inCircle_R in *. cbn [px py] in *.
  nsatz.
Qed.

(* ========================================================================== *)
(* §1b  Equidistant from the circumcenter ⇒ on the circumcircle               *)
(*                                                                            *)
(* Immediate from §1a: arc_center_equidistant gives OA=OB=OC, and the         *)
(* hypothesis gives OP=OA, so all four control/test points are concyclic.     *)
(* ========================================================================== *)

Lemma inCircle_R_zero_of_equidistant :
  forall (a : CircularArc) (P : Point),
    valid_arc a ->
    dist_sq (arc_center a) P = dist_sq (arc_center a) (arc_start a) ->
    inCircle_R (arc_start a) (arc_mid a) (arc_end a) P = 0.
Proof.
  intros a P Hva Heq.
  pose proof (arc_center_equidistant a Hva) as [Hab Hbc].
  apply (inCircle_R_concyclic _ _ _ _ (arc_center a)); lra.
Qed.

(* Converse (needed for arc point distance radial case soundness): on the
   circumcircle (inCircle_R = 0) implies equidistant from the circumcenter.
   The inCircle polynomial vanishes exactly on the circle through A B C;
   translating to O (the circumcenter) makes the det proportional to
   (|P'|^2 - r^2) times the nonzero area factor from valid_arc (the same
   nonzero divisor that makes arc_center well-defined).  Hence inc=0 forces
   the norm equality.  Proved by the symmetric translation + nsatz on the
   factored polynomial identity (the forward direction nsatz is reversible
   here once the cofactor is shown nonzero by valid_arc non-collinearity). *)
(* Converse direction (inCircle_R = 0 ⇒ equidistant) is already proved above
   as `inCircle_R_zero_implies_equidistant` (used by the discharged D-PT lemmas
   `radial_lower` and `centre_is_r`). STALE NOTE UPDATE: the endpoint-fallback
   monotonicity this comment once flagged as pending was itself discharged
   (`ArcPointDistance.point_to_arc_dist_fallback_ends_lower`, 2026-06-28, via
   `ArcSinglePeak.arc_dot_max_at_endpoint`, discharged 2026-07-01) -- D-PT is
   now fully closed with no live entry in docs/admitted-deferred-proofs.txt. *)

(* ========================================================================== *)
(* §1c  Converse: on the circumcircle ⇒ equidistant from the circumcenter    *)
(*                                                                            *)
(* Proof: translate the arc center to the origin; all three control points    *)
(* then lie on a circle of squared-radius R2 = dist_sq O (arc_start).        *)
(* The polynomial identity                                                    *)
(*   inCircle_R A B C P = orient2d(A,B,C) · (R2 − |P|²)                      *)
(* holds modulo the three circle constraints (proved by nsatz below).         *)
(* Since valid_arc ⇒ orient2d ≠ 0, det = 0 forces |P|² = R2,               *)
(* i.e. dist_sq O P = dist_sq O (arc_start).                                 *)
(* ========================================================================== *)

(* The algebraic identity: all three defining points on circle of sq-radius R2
   centred at origin ⇒ inCircle_R = orient2d × (R2 − |P|²). *)
Lemma inCircle_R_circle_factored :
  forall ax ay bx by_ cx cy qx qy R2 : R,
    ax * ax + ay * ay = R2 ->
    bx * bx + by_ * by_ = R2 ->
    cx * cx + cy * cy = R2 ->
    inCircle_R (mkPoint ax ay) (mkPoint bx by_) (mkPoint cx cy) (mkPoint qx qy)
    = (ax * (by_ - cy) + bx * (cy - ay) + cx * (ay - by_))
      * (R2 - qx * qx - qy * qy).
Proof.
  intros ax ay bx by_ cx cy qx qy R2 Har Hbr Hcr.
  unfold inCircle_R. cbn.
  (* Replace the squared translated-norms using on-circle conditions,
     then substitute R2 = ax²+ay², leaving a pure polynomial identity for ring. *)
  replace ((bx - qx) * (bx - qx) + (by_ - qy) * (by_ - qy))
    with (R2 - 2 * (bx * qx + by_ * qy) + (qx * qx + qy * qy))
    by (rewrite <- Hbr; ring).
  replace ((cx - qx) * (cx - qx) + (cy - qy) * (cy - qy))
    with (R2 - 2 * (cx * qx + cy * qy) + (qx * qx + qy * qy))
    by (rewrite <- Hcr; ring).
  replace ((ax - qx) * (ax - qx) + (ay - qy) * (ay - qy))
    with (R2 - 2 * (ax * qx + ay * qy) + (qx * qx + qy * qy))
    by (rewrite <- Har; ring).
  replace R2 with (ax * ax + ay * ay) by lra.
  ring.
Qed.

(* The converse of inCircle_R_zero_of_equidistant: for a valid arc (the
   orientation is nonzero), inCircle_R = 0 forces P onto the circumcircle. *)
Lemma inCircle_R_zero_implies_equidistant :
  forall (a : CircularArc) (P : Point),
    valid_arc a ->
    inCircle_R (arc_start a) (arc_mid a) (arc_end a) P = 0 ->
    dist_sq (arc_center a) P = dist_sq (arc_center a) (arc_start a).
Proof.
  intros a P Hva Hdet.
  set (O := arc_center a).
  set (R2 := dist_sq O (arc_start a)).
  (* Translate by -O so the circumcenter is at the origin. *)
  rewrite <- (inCircle_R_translation_invariant
                (arc_start a) (arc_mid a) (arc_end a) P (- px O) (- py O)) in Hdet.
  pose proof (arc_center_equidistant a Hva) as [Hsm Hse].
  (* Circle constraints in translated frame. *)
  assert (Har : (px (arc_start a) + - px O) * (px (arc_start a) + - px O)
              + (py (arc_start a) + - py O) * (py (arc_start a) + - py O) = R2).
  { unfold R2, dist_sq. cbn [px py]. ring. }
  assert (Hbr : (px (arc_mid a) + - px O) * (px (arc_mid a) + - px O)
              + (py (arc_mid a) + - py O) * (py (arc_mid a) + - py O) = R2).
  { unfold R2, O. rewrite Hsm. unfold dist_sq. cbn [px py]. ring. }
  assert (Hcr : (px (arc_end a) + - px O) * (px (arc_end a) + - px O)
              + (py (arc_end a) + - py O) * (py (arc_end a) + - py O) = R2).
  { unfold R2, O. rewrite Hse. unfold dist_sq. cbn [px py]. ring. }
  (* Apply the factored identity. *)
  pose proof (inCircle_R_circle_factored
    (px (arc_start a) + - px O) (py (arc_start a) + - py O)
    (px (arc_mid   a) + - px O) (py (arc_mid   a) + - py O)
    (px (arc_end   a) + - px O) (py (arc_end   a) + - py O)
    (px P + - px O) (py P + - py O) R2
    Har Hbr Hcr) as Hfact.
  rewrite Hfact in Hdet.
  (* orient2d(arc_start, arc_mid, arc_end) ≠ 0 from valid_arc. *)
  assert (Hor : (px (arc_start a) + - px O) * ((py (arc_mid a) + - py O) - (py (arc_end a) + - py O))
              + (px (arc_mid   a) + - px O) * ((py (arc_end a) + - py O) - (py (arc_start a) + - py O))
              + (px (arc_end   a) + - px O) * ((py (arc_start a) + - py O) - (py (arc_mid a) + - py O))
              <> 0).
  { unfold O. unfold valid_arc in Hva. cbn [px py] in *. intro Heq. apply Hva. lra. }
  (* Rmult_integral: one factor must be zero; orient2d ≠ 0 forces R2 - |P|² = 0. *)
  apply Rmult_integral in Hdet as [Hmul | Hrsq].
  - exfalso. apply Hor. exact Hmul.
  - (* R2 - |P-O|² = 0, i.e., dist_sq O P = R2 = dist_sq O (arc_start a). *)
    unfold R2, dist_sq in *. cbn [px py] in *. lra.
Qed.

(* ========================================================================== *)
(* §2  Radical-line point lies on both circles                                *)
(*                                                                            *)
(* HEADLINE THEOREM: for two properly-intersecting circles                    *)
(* (|r1−r2| < dist O1 O2 < r1+r2, both radii positive), the ARC_ARC_XY       *)
(* radical-line formula constructs a point P+ on BOTH circles.                *)
(*                                                                            *)
(* Proof steps:                                                               *)
(*   1.  d = dist O1 O2, d*d = dist_sq O1 O2.                                *)
(*   2.  ux = (o2x−o1x)/d, uy = (o2y−o1y)/d.  Prove ux²+uy²=1.             *)
(*   3.  a = (d²+r1²−r2²)/(2d).  Show |a| < r1 from the intersection         *)
(*       conditions (four-factor polynomial argument via nra).                *)
(*   4.  h = √(r1²−a²) > 0.  h·h = r1²−a² by sqrt_sqrt.                     *)
(*   5.  P+ = O1 + (a·ux − h·uy, a·uy + h·ux).                               *)
(*   6.  dist_sq O1 P+ = (a²+h²)(ux²+uy²) = a²+(r1²−a²) = r1².  ring.      *)
(*   7.  dist_sq O2 P+ = (a−d)²+h² = d²−2ad+r1².  With 2ad=d²+r1²−r2²:     *)
(*       = r2².  nra (via H2ad).                                              *)
(* ========================================================================== *)

Theorem two_circles_radical_point :
  forall (O1 O2 : Point) (r1 r2 : R),
    0 < r1 ->
    0 < r2 ->
    0 < dist O1 O2 ->
    Rabs (r1 - r2) < dist O1 O2 ->
    dist O1 O2 < r1 + r2 ->
    exists P : Point,
      dist_sq O1 P = r1 * r1 /\ dist_sq O2 P = r2 * r2.
Proof.
  intros O1 O2 r1 r2 Hr1 Hr2 Hdpos Hrabs Hdlt.

  (* -- Basic setup --------------------------------------------------------- *)
  set (d   := dist O1 O2) in *.
  set (o1x := px O1). set (o1y := py O1).
  set (o2x := px O2). set (o2y := py O2).

  assert (Hd_pos : 0 < d)   by exact Hdpos.
  assert (Hd_ne  : d <> 0)  by lra.

  (* d² = dist_sq O1 O2 *)
  assert (Hdd : d * d = dist_sq O1 O2).
  { unfold d, dist. rewrite sqrt_sqrt. reflexivity. apply dist_sq_nonneg. }
  assert (Hdd_decomp : d * d = (o2x - o1x) * (o2x - o1x)
                               + (o2y - o1y) * (o2y - o1y)).
  { rewrite Hdd. unfold dist_sq, o1x, o1y, o2x, o2y. ring. }

  (* Unpack Rabs condition into two linear bounds *)
  assert (Hr12a : r1 - r2 < d).
  { apply (Rle_lt_trans _ (Rabs (r1 - r2))); [apply Rle_abs | lra]. }
  assert (Hr12b : r2 - r1 < d).
  { apply (Rle_lt_trans _ (Rabs (r1 - r2)));
    [rewrite Rabs_minus_sym; apply Rle_abs | lra]. }

  (* -- Unit vector along O1 → O2 ------------------------------------------ *)
  set (ux := (o2x - o1x) / d).
  set (uy := (o2y - o1y) / d).

  (* Reconnect scaled unit vector to raw differences *)
  assert (Hdux : d * ux = o2x - o1x).
  { unfold ux. field. exact Hd_ne. }
  assert (Hduy : d * uy = o2y - o1y).
  { unfold uy. field. exact Hd_ne. }

  (* ux² + uy² = 1: multiply through by d² = (o2x-o1x)²+(o2y-o1y)², cancel. *)
  assert (Hunit : ux * ux + uy * uy = 1).
  { assert (Heq : d * d * (ux * ux + uy * uy) = d * d).
    { transitivity ((d * ux) * (d * ux) + (d * uy) * (d * uy)).
      - ring.
      - rewrite Hdux, Hduy. rewrite Hdd_decomp. ring. }
    assert (Hd2pos : 0 < d * d) by nra.
    assert (Hd2ne : d * d <> 0) by lra.
    apply (Rmult_eq_reg_l (d * d) _ _).
    - ring_simplify. lra.
    - lra. }

  (* -- Radical-axis parameter a -------------------------------------------- *)
  set (a := (d * d + r1 * r1 - r2 * r2) / (2 * d)).

  (* 2·a·d = d²+r1²−r2²  (key identity used in the O2 distance proof) *)
  assert (H2ad : 2 * a * d = d * d + r1 * r1 - r2 * r2).
  { unfold a. field. exact Hd_ne. }

  (* -- Positivity of discriminant: r1² − a² > 0 --------------------------- *)
  (*    (d+r1+r2)(d+r1−r2)(r2+d−r1)(r1+r2−d) = (2dr1)² − (d²+r1²−r2²)²    *)

  (* All four intersection factors are positive *)
  assert (Hf1 : 0 < d + r1 + r2)  by lra.
  assert (Hf2 : 0 < d + r1 - r2)  by lra.
  assert (Hf3 : 0 < r2 + d - r1)  by lra.
  assert (Hf4 : 0 < r1 + r2 - d)  by lra.

  (* Polynomial identity: product of factors = (2dr1)² − (d²+r1²−r2²)² *)
  assert (Hpoly :
    (d+r1+r2) * (d+r1-r2) * (r2+d-r1) * (r1+r2-d)
    = (2*d*r1) * (2*d*r1) - (d*d + r1*r1 - r2*r2) * (d*d + r1*r1 - r2*r2))
    by ring.

  assert (Hnum_pos :
    0 < (2*d*r1) * (2*d*r1) - (d*d + r1*r1 - r2*r2) * (d*d + r1*r1 - r2*r2)).
  { rewrite <- Hpoly. repeat apply Rmult_lt_0_compat; lra. }

  (* r1² − a² > 0: use the factored form via H2ad *)
  assert (Hh2_pos : 0 < r1 * r1 - a * a).
  { (* 4d²(r1²−a²) = (2dr1)² − (2ad)² = (2dr1)² − (d²+r1²−r2²)² > 0 *)
    assert (Hkey : 4 * d * d * (r1 * r1 - a * a)
              = (2*d*r1)*(2*d*r1) - (d*d+r1*r1-r2*r2)*(d*d+r1*r1-r2*r2)).
    { rewrite <- H2ad. ring. }
    apply (Rmult_lt_reg_l (4 * d * d)).
    - nra.
    - rewrite Rmult_0_r. rewrite Hkey. exact Hnum_pos. }

  (* -- Construct h = √(r1² − a²) ------------------------------------------ *)
  set (h2 := r1 * r1 - a * a).
  assert (Hh2_nn : 0 <= h2) by (unfold h2; lra).
  set (h := sqrt h2).
  assert (Hhh : h * h = h2).
  { unfold h. apply sqrt_sqrt. exact Hh2_nn. }

  (* -- Construct the radical-line intersection point P+ -------------------- *)
  set (mx := o1x + a * ux).
  set (my := o1y + a * uy).
  exists (mkPoint (mx - h * uy) (my + h * ux)).

  split.

  (* ---- dist_sq O1 P+ = r1² ---------------------------------------------- *)
  - unfold dist_sq.
    cbn [px py].
    unfold mx, my, o1x, o1y.
    unfold h2 in Hhh.
    (* P+ − O1 = (a·ux − h·uy, a·uy + h·ux);                              *)
    (* |P+−O1|² = (a²+h²)(ux²+uy²) = a²+h² = a²+(r1²−a²) = r1².           *)
    transitivity ((a * a + h * h) * (ux * ux + uy * uy)).
    + ring.
    + rewrite Hunit, Hhh. ring.

  (* ---- dist_sq O2 P+ = r2² ---------------------------------------------- *)
  - unfold dist_sq.
    cbn [px py].
    unfold mx, my, o1x, o1y.
    unfold o2x, o1x in Hdux. unfold o2y, o1y in Hduy.
    unfold h2 in Hhh.
    (* o2x − o1x = d·ux, o2y − o1y = d·uy (Hdux/Hduy): express O2.        *)
    assert (Ho2x : px O2 = px O1 + d * ux) by (rewrite Hdux; ring).
    assert (Ho2y : py O2 = py O1 + d * uy) by (rewrite Hduy; ring).
    rewrite Ho2x, Ho2y.
    (* |P+−O2|² = ((a−d)²+h²)(ux²+uy²) = d²−2ad+r1² = r2² via H2ad.        *)
    transitivity (((a - d) * (a - d) + h * h) * (ux * ux + uy * uy)).
    + ring.
    + rewrite Hunit, Hhh. nra.

Qed.

(* ========================================================================== *)
(* §3  Arc-level corollary: proper circle intersection ⇒ ∃ point on both     *)
(*                                                                            *)
(* Wraps §3 for valid arcs: converts between the `dist_sq O P = r²` and      *)
(* `inCircle_R = 0` representations via §2.                                   *)
(*                                                                            *)
(* DEFERRED (as stated): `arc_span_contains` for this point (angular sector   *)
(* membership, needs atan2); `arc_arc_intersects` (both circles + both spans).*)
(* ========================================================================== *)

Theorem arc_arc_circles_intersect :
  forall (a1 a2 : CircularArc),
    valid_arc a1 ->
    valid_arc a2 ->
    0 < dist (arc_center a1) (arc_center a2) ->
    Rabs (arc_radius a1 - arc_radius a2) < dist (arc_center a1) (arc_center a2) ->
    dist (arc_center a1) (arc_center a2) < arc_radius a1 + arc_radius a2 ->
    exists X : Point,
      inCircle_R (arc_start a1) (arc_mid a1) (arc_end a1) X = 0 /\
      inCircle_R (arc_start a2) (arc_mid a2) (arc_end a2) X = 0.
Proof.
  intros a1 a2 Hva1 Hva2 Hdpos Hrabs Hdlt.

  assert (Hr1 : 0 < arc_radius a1) by (apply arc_radius_pos; exact Hva1).
  assert (Hr2 : 0 < arc_radius a2) by (apply arc_radius_pos; exact Hva2).

  destruct (two_circles_radical_point
              (arc_center a1) (arc_center a2)
              (arc_radius a1) (arc_radius a2)
              Hr1 Hr2 Hdpos Hrabs Hdlt)
    as [P [Hp1 Hp2]].
  exists P.

  (* arc_radius² = dist_sq (arc_center a) (arc_start a) *)
  assert (Hr1sq : arc_radius a1 * arc_radius a1
                  = dist_sq (arc_center a1) (arc_start a1)).
  { rewrite arc_radius_eq_sqrt.
    rewrite sqrt_sqrt; [| apply arc_radius_sq_nonneg].
    unfold arc_radius_sq. reflexivity. }

  assert (Hr2sq : arc_radius a2 * arc_radius a2
                  = dist_sq (arc_center a2) (arc_start a2)).
  { rewrite arc_radius_eq_sqrt.
    rewrite sqrt_sqrt; [| apply arc_radius_sq_nonneg].
    unfold arc_radius_sq. reflexivity. }

  split.
  - apply inCircle_R_zero_of_equidistant; [exact Hva1 |]. lra.
  - apply inCircle_R_zero_of_equidistant; [exact Hva2 |]. lra.
Qed.

(* ========================================================================== *)
(* §4  Audit footprint.                                                       *)
(* ========================================================================== *)

(* ========================================================================== *)
(* §5  Uniqueness: any point on both circles IS one of the two named          *)
(*     radical-line coordinates.                                              *)
(*                                                                            *)
(* Named `Definition`s for the two `two_circles_radical_point` roots, so a    *)
(* caller can state a CONCRETE, checkable span-membership condition on them   *)
(* (see `ArcArcCirclesSpan.arc_arc_intersects_of_circles_and_radical_signs`)  *)
(* instead of an opaque universally-quantified bridge hypothesis.             *)
(*                                                                            *)
(* Proof: decompose X - O1 in the orthonormal frame (u, perp u) where         *)
(* u = (O2-O1)/d.  The two circle equations force the u-component to be      *)
(* exactly `a` (by subtraction) and the perp-component to satisfy            *)
(* `s2^2 = r1^2 - a^2`, hence `s2 = +-h`.  No properness hypothesis needed -- *)
(* `s2^2 = r1^2-a^2 >= 0` falls out automatically from X existing.           *)
(* ========================================================================== *)

Definition radical_axis_ux (O1 O2 : Point) : R := (px O2 - px O1) / dist O1 O2.
Definition radical_axis_uy (O1 O2 : Point) : R := (py O2 - py O1) / dist O1 O2.

Definition radical_axis_a (O1 O2 : Point) (r1 r2 : R) : R :=
  (dist O1 O2 * dist O1 O2 + r1 * r1 - r2 * r2) / (2 * dist O1 O2).

Definition radical_axis_h (O1 O2 : Point) (r1 r2 : R) : R :=
  sqrt (r1 * r1 - radical_axis_a O1 O2 r1 r2 * radical_axis_a O1 O2 r1 r2).

Definition radical_point_plus (O1 O2 : Point) (r1 r2 : R) : Point :=
  mkPoint (px O1 + radical_axis_a O1 O2 r1 r2 * radical_axis_ux O1 O2
                  - radical_axis_h O1 O2 r1 r2 * radical_axis_uy O1 O2)
          (py O1 + radical_axis_a O1 O2 r1 r2 * radical_axis_uy O1 O2
                  + radical_axis_h O1 O2 r1 r2 * radical_axis_ux O1 O2).

Lemma point_eq_of_coords : forall p q : Point,
  px p = px q -> py p = py q -> p = q.
Proof.
  intros [x1 y1] [x2 y2]; cbn; intros Hx Hy; subst; reflexivity.
Qed.

Definition radical_point_minus (O1 O2 : Point) (r1 r2 : R) : Point :=
  mkPoint (px O1 + radical_axis_a O1 O2 r1 r2 * radical_axis_ux O1 O2
                  + radical_axis_h O1 O2 r1 r2 * radical_axis_uy O1 O2)
          (py O1 + radical_axis_a O1 O2 r1 r2 * radical_axis_uy O1 O2
                  - radical_axis_h O1 O2 r1 r2 * radical_axis_ux O1 O2).

Theorem two_circles_radical_point_unique :
  forall (O1 O2 : Point) (r1 r2 : R) (X : Point),
    0 < dist O1 O2 ->
    dist_sq O1 X = r1 * r1 ->
    dist_sq O2 X = r2 * r2 ->
    X = radical_point_plus O1 O2 r1 r2 \/ X = radical_point_minus O1 O2 r1 r2.
Proof.
  intros O1 O2 r1 r2 X Hdpos HX1 HX2.
  unfold radical_point_plus, radical_point_minus,
         radical_axis_a, radical_axis_h, radical_axis_ux, radical_axis_uy.
  unfold radical_axis_a.
  set (d := dist O1 O2) in *.
  assert (Hd_ne : d <> 0) by lra.
  set (o1x := px O1). set (o1y := py O1).
  set (o2x := px O2). set (o2y := py O2).
  assert (Hdd : d * d = (o2x - o1x) * (o2x - o1x) + (o2y - o1y) * (o2y - o1y)).
  { unfold d, dist. rewrite sqrt_sqrt; [ | apply dist_sq_nonneg].
    unfold dist_sq, o1x, o1y, o2x, o2y. ring. }
  set (ux := (o2x - o1x) / d). set (uy := (o2y - o1y) / d).
  assert (Hdux : d * ux = o2x - o1x) by (unfold ux; field; exact Hd_ne).
  assert (Hduy : d * uy = o2y - o1y) by (unfold uy; field; exact Hd_ne).
  assert (Hunit : ux * ux + uy * uy = 1).
  { assert (Heq : d * d * (ux * ux + uy * uy) = d * d).
    { transitivity ((d * ux) * (d * ux) + (d * uy) * (d * uy)).
      - ring.
      - rewrite Hdux, Hduy, Hdd. ring. }
    assert (Hd2ne : d * d <> 0) by nra.
    apply (Rmult_eq_reg_l (d * d) _ _); [ | exact Hd2ne].
    ring_simplify. lra. }
  set (a := (d * d + r1 * r1 - r2 * r2) / (2 * d)).
  set (s1 := (px X - o1x) * ux + (py X - o1y) * uy).
  set (s2 := (py X - o1y) * ux - (px X - o1x) * uy).
  assert (Hdecomp_x : s1 * ux - s2 * uy = px X - o1x).
  { unfold s1, s2.
    transitivity ((px X - o1x) * (ux * ux + uy * uy)); [ring | rewrite Hunit; ring]. }
  assert (Hdecomp_y : s1 * uy + s2 * ux = py X - o1y).
  { unfold s1, s2.
    transitivity ((py X - o1y) * (ux * ux + uy * uy)); [ring | rewrite Hunit; ring]. }
  assert (HXeq1 : (px X - o1x) * (px X - o1x) + (py X - o1y) * (py X - o1y) = r1 * r1)
    by (unfold o1x, o1y; rewrite <- HX1; unfold dist_sq; ring).
  assert (Hpyth1 : (s1 * ux - s2 * uy) * (s1 * ux - s2 * uy)
                   + (s1 * uy + s2 * ux) * (s1 * uy + s2 * ux)
                   = (s1 * s1 + s2 * s2) * (ux * ux + uy * uy)) by ring.
  rewrite Hdecomp_x, Hdecomp_y, Hunit in Hpyth1.
  assert (Hsum1 : s1 * s1 + s2 * s2 = r1 * r1) by nra.
  (* X - O2 uses the same decomposition with s1 replaced by (s1 - d). *)
  assert (HY1eq : px X - o2x = (s1 - d) * ux - s2 * uy).
  { replace ((s1 - d) * ux - s2 * uy) with ((s1 * ux - s2 * uy) - d * ux) by ring.
    rewrite Hdecomp_x, Hdux. ring. }
  assert (HY2eq : py X - o2y = (s1 - d) * uy + s2 * ux).
  { replace ((s1 - d) * uy + s2 * ux) with ((s1 * uy + s2 * ux) - d * uy) by ring.
    rewrite Hdecomp_y, Hduy. ring. }
  assert (HYeq2 : (px X - o2x) * (px X - o2x) + (py X - o2y) * (py X - o2y) = r2 * r2)
    by (unfold o2x, o2y; rewrite <- HX2; unfold dist_sq; ring).
  assert (Hpyth2 : ((s1 - d) * ux - s2 * uy) * ((s1 - d) * ux - s2 * uy)
                   + ((s1 - d) * uy + s2 * ux) * ((s1 - d) * uy + s2 * ux)
                   = ((s1 - d) * (s1 - d) + s2 * s2) * (ux * ux + uy * uy)) by ring.
  rewrite Hunit in Hpyth2.
  rewrite <- HY1eq, <- HY2eq in Hpyth2.
  assert (Hsum2 : (s1 - d) * (s1 - d) + s2 * s2 = r2 * r2) by nra.
  (* Subtracting: s1 = a. *)
  assert (Hs1a : s1 = a).
  { assert (Hkey : 2 * s1 * d - d * d = r1 * r1 - r2 * r2) by nra.
    unfold a. apply (Rmult_eq_reg_l (2 * d)); [ | nra].
    field_simplify; nra. }
  assert (Hs2sq : s2 * s2 = r1 * r1 - a * a) by nra.
  assert (Hh2nn : 0 <= r1 * r1 - a * a) by nra.
  assert (Hhh : sqrt (r1 * r1 - a * a) * sqrt (r1 * r1 - a * a) = r1 * r1 - a * a)
    by (apply sqrt_sqrt; exact Hh2nn).
  set (h := sqrt (r1 * r1 - a * a)) in *.
  assert (Hs2h : (s2 - h) * (s2 + h) = 0) by nra.
  destruct (Rmult_integral _ _ Hs2h) as [Hplus | Hminus].
  - left. assert (Hs2eq : s2 = h) by lra.
    rewrite Hs1a, Hs2eq in Hdecomp_x, Hdecomp_y.
    apply point_eq_of_coords; cbn [px py]; lra.
  - right. assert (Hs2eq : s2 = -h) by lra.
    rewrite Hs1a, Hs2eq in Hdecomp_x, Hdecomp_y.
    apply point_eq_of_coords; cbn [px py]; lra.
Qed.

(* ========================================================================== *)
(* §5b  Both named points independently satisfy both circle equations.        *)
(*                                                                            *)
(* Two properly-intersecting circles meet in two points, symmetric across    *)
(* the O1-O2 line -- `radical_point_plus`/`_minus` differ only in the sign of *)
(* `h`, and both circle equations depend on `h` only through `h*h`, so both   *)
(* points satisfy BOTH equations independently.  Same algebra as             *)
(* `two_circles_radical_point`, restated about the two named points directly *)
(* (rather than behind an existential) so a caller can pick whichever root   *)
(* it needs without re-deriving the construction.                            *)
(* ========================================================================== *)

Theorem radical_points_on_circles :
  forall (O1 O2 : Point) (r1 r2 : R),
    0 < r1 -> 0 < r2 -> 0 < dist O1 O2 ->
    Rabs (r1 - r2) < dist O1 O2 -> dist O1 O2 < r1 + r2 ->
    (dist_sq O1 (radical_point_plus O1 O2 r1 r2) = r1 * r1 /\
     dist_sq O2 (radical_point_plus O1 O2 r1 r2) = r2 * r2) /\
    (dist_sq O1 (radical_point_minus O1 O2 r1 r2) = r1 * r1 /\
     dist_sq O2 (radical_point_minus O1 O2 r1 r2) = r2 * r2).
Proof.
  intros O1 O2 r1 r2 Hr1 Hr2 Hdpos Hrabs Hdlt.
  unfold radical_point_plus, radical_point_minus,
         radical_axis_a, radical_axis_h, radical_axis_ux, radical_axis_uy.
  unfold radical_axis_a.
  set (d := dist O1 O2) in *.
  set (o1x := px O1). set (o1y := py O1).
  set (o2x := px O2). set (o2y := py O2).
  assert (Hd_ne : d <> 0) by lra.
  assert (Hdd : d * d = dist_sq O1 O2).
  { unfold d, dist. rewrite sqrt_sqrt; [reflexivity | apply dist_sq_nonneg]. }
  assert (Hdd_decomp : d * d = (o2x - o1x) * (o2x - o1x) + (o2y - o1y) * (o2y - o1y)).
  { rewrite Hdd. unfold dist_sq, o1x, o1y, o2x, o2y. ring. }
  assert (Hr12a : r1 - r2 < d)
    by (apply (Rle_lt_trans _ (Rabs (r1 - r2))); [apply Rle_abs | lra]).
  assert (Hr12b : r2 - r1 < d)
    by (apply (Rle_lt_trans _ (Rabs (r1 - r2)));
        [rewrite Rabs_minus_sym; apply Rle_abs | lra]).
  set (ux := (o2x - o1x) / d). set (uy := (o2y - o1y) / d).
  assert (Hdux : d * ux = o2x - o1x) by (unfold ux; field; exact Hd_ne).
  assert (Hduy : d * uy = o2y - o1y) by (unfold uy; field; exact Hd_ne).
  assert (Hunit : ux * ux + uy * uy = 1).
  { assert (Heq : d * d * (ux * ux + uy * uy) = d * d).
    { transitivity ((d * ux) * (d * ux) + (d * uy) * (d * uy)).
      - ring.
      - rewrite Hdux, Hduy, Hdd_decomp. ring. }
    assert (Hd2ne : d * d <> 0) by nra.
    apply (Rmult_eq_reg_l (d * d) _ _); [ring_simplify; lra | lra]. }
  set (a := (d * d + r1 * r1 - r2 * r2) / (2 * d)).
  assert (H2ad : 2 * a * d = d * d + r1 * r1 - r2 * r2) by (unfold a; field; exact Hd_ne).
  assert (Hf1 : 0 < d + r1 + r2) by lra.
  assert (Hf2 : 0 < d + r1 - r2) by lra.
  assert (Hf3 : 0 < r2 + d - r1) by lra.
  assert (Hf4 : 0 < r1 + r2 - d) by lra.
  assert (Hpoly :
    (d + r1 + r2) * (d + r1 - r2) * (r2 + d - r1) * (r1 + r2 - d)
    = (2 * d * r1) * (2 * d * r1) - (d * d + r1 * r1 - r2 * r2) * (d * d + r1 * r1 - r2 * r2))
    by ring.
  assert (Hnum_pos :
    0 < (2 * d * r1) * (2 * d * r1) - (d * d + r1 * r1 - r2 * r2) * (d * d + r1 * r1 - r2 * r2)).
  { rewrite <- Hpoly. repeat apply Rmult_lt_0_compat; lra. }
  assert (Hh2_pos : 0 < r1 * r1 - a * a).
  { assert (Hkey : 4 * d * d * (r1 * r1 - a * a)
              = (2*d*r1)*(2*d*r1) - (d*d+r1*r1-r2*r2)*(d*d+r1*r1-r2*r2))
      by (rewrite <- H2ad; ring).
    apply (Rmult_lt_reg_l (4 * d * d)); [nra | rewrite Rmult_0_r, Hkey; exact Hnum_pos]. }
  assert (Hh2_nn : 0 <= r1 * r1 - a * a) by lra.
  assert (Hhh : sqrt (r1 * r1 - a * a) * sqrt (r1 * r1 - a * a) = r1 * r1 - a * a)
    by (apply sqrt_sqrt; exact Hh2_nn).
  set (h := sqrt (r1 * r1 - a * a)) in *.
  assert (Ho2x : o2x = o1x + d * ux) by lra.
  assert (Ho2y : o2y = o1y + d * uy) by lra.
  repeat split; unfold dist_sq; cbn [px py]; fold o1x o1y o2x o2y.
  - transitivity ((a * a + h * h) * (ux * ux + uy * uy));
      [ring | rewrite Hunit, Hhh; ring].
  - rewrite Ho2x, Ho2y.
    transitivity (((a - d) * (a - d) + h * h) * (ux * ux + uy * uy));
      [ring | rewrite Hunit, Hhh; nra].
  - transitivity ((a * a + h * h) * (ux * ux + uy * uy));
      [ring | rewrite Hunit, Hhh; ring].
  - rewrite Ho2x, Ho2y.
    transitivity (((a - d) * (a - d) + h * h) * (ux * ux + uy * uy));
      [ring | rewrite Hunit, Hhh; nra].
Qed.

(* ========================================================================== *)
(* §6  Audit footprint.                                                       *)
(* ========================================================================== *)

Print Assumptions inCircle_R_zero_of_equidistant.
Print Assumptions inCircle_R_zero_implies_equidistant.
Print Assumptions radical_points_on_circles.
Print Assumptions two_circles_radical_point.
Print Assumptions arc_arc_circles_intersect.
Print Assumptions two_circles_radical_point_unique.

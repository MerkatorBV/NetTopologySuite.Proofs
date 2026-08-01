(* ============================================================================
   NetTopologySuite.Proofs.CompoundCurveKocJoin
   ----------------------------------------------------------------------------
   The compound-curve JOIN: modeling two directly-connected circular arcs of
   different radii, after

     W. Koc, "Modeling of Compound Curves on Railway Lines",
     Geomatics 5(2):21, MDPI, 2025 (doi:10.3390/geomatics5020021)

   -- the 2025 sequel to the 2015 Archives-of-Transport paper mechanised in
   CompoundCurveKoc.v / CompoundCurveKocFrame.v.

   THE REAL-WORLD PROBLEM.  Compound curves (two arcs of different radii
   pointing the same way, DIRECTLY connected -- no transition between them)
   survive on tramways and mountain railway lines; new ones are no longer
   built, so the task is to RECREATE (model) an existing layout well enough
   to correct it.  The 2025 paper's algorithm inscribes both arcs in one
   auxiliary frame, MIRRORS the second branch about the vertical through the
   junction (its Figure 4), and shifts it to restore continuity.  Everything
   hinges on one analytic fact: at the junction C both arcs must share the
   tangent direction -- a C^1 join.  Get the sign wrong and the modeled
   track has a kink at C; a maintenance machine lining to that model would
   try to bend rail through an angle, which is exactly the defect the
   modeling is meant to remove.

   WHAT IS MECHANISED (paper eq |-> lemma):

     (10),(11)  `koc25_circle_graph_deriv` -- the upper-semicircle graph
                y(x) = yS + sqrt(R^2 - (xS - x)^2) has derivative
                (xS - x)/sqrt(R^2 - (xS - x)^2) wherever the radicand is
                positive.  This is the paper's tangent-slope formula, here
                PROVEN as a `derivable_pt_lim`, not assumed.
     (after 11) `koc25_apex` -- the summit H = (xS, yS + R): on the graph
                with derivative ZERO.  (The paper uses H to bound where the
                junction may sit: x_C in (dxTC, 2 x_H - dxTC).)
     (15),(16)  `koc25_slope_at_prescribed_point` -- the point
                x = xS - s R/u has graph value yS + R/u and ANALYTIC slope
                exactly s.  This closes the loop with part 1's algebraic
                prescribed-slope point (perpendicularity of the radius):
                the algebra and the derivative agree.
     Figure 4   `koc25_mirror_negates_slope` -- mirroring about a vertical
                axis preserves radius lengths and negates tangent slopes:
                the reflection step of the modeling algorithm is sound.
     (16) core  `koc25_compound_join_C1` -- HEADLINE: placing both centres
                on the junction normal (S_i = C + (R_i/u)(s, -1)) puts C on
                BOTH circles with BOTH radii perpendicular to the same
                direction (1, s): the C^1 compound join, kink-free by
                construction.  `koc25_compound_centers_collinear`: the two
                centres and the junction are COLLINEAR -- the classical
                textbook characterisation of a compound curve (the paper's
                ref [17], Tonias & Tonias), obtained here as a corollary of
                the two perpendicularity conditions.
     (23),(24)  `koc25_vertex_case1` -- Case I vertex of the tangent lines
                through the system endpoints A1, A2;
     (25),(26)  `koc25_vertex_case2` -- Case II (system above the vertex);
                `koc25_case_duality` -- Case II IS Case I under y |-> -y:
                the two computational algorithms of the paper's §6 are one
                theorem and its mirror image.
     example    an exact 3-4-5-10 instance: junction C = (0,0), s = 3/4,
                u = 5/4, R1 = 5, R2 = 10 give centres S1 = (3,-4) and
                S2 = (6,-8) -- on one ray through C, dist^2 25 and 100.

   Sqrt appears ONLY where the paper's own object is a sqrt (the graph and
   its derivative); everything else stays sqrt-free via u > 0,
   u^2 = 1 + s^2, as in parts 1-2.  No `Admitted`, no `Axiom`, no
   `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra Ranalysis1.
From NTS.Proofs Require Import Distance Orientation CompoundCurveKoc.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  The circle graph and its derivative (Koc 2025 eqs (10),(11)).          *)
(* -------------------------------------------------------------------------- *)

Definition koc25_circle_graph (xS yS Rr x : R) : R :=
  yS + sqrt (Rr * Rr - (xS - x) * (xS - x)).

(* The tangent-slope formula (11), proven as a genuine derivative. *)
Theorem koc25_circle_graph_deriv :
  forall xS yS Rr x,
    0 < Rr * Rr - (xS - x) * (xS - x) ->
    derivable_pt_lim (koc25_circle_graph xS yS Rr) x
      ((xS - x) / sqrt (Rr * Rr - (xS - x) * (xS - x))).
Proof.
  intros xS yS Rr x Hpos.
  set (f := fun t : R => Rr * Rr - (xS - t) * (xS - t)).
  assert (Hf : derivable_pt_lim f x (2 * (xS - x))).
  { unfold f.
    (* d/dt [Rr*Rr - (xS-t)^2] = 0 - 2(xS-t)(-1) = 2(xS-t) *)
    assert (Hg : derivable_pt_lim (fun t : R => xS - t) x (-1)).
    { replace (-1) with (0 - 1) by ring.
      apply derivable_pt_lim_minus.
      - apply derivable_pt_lim_const.
      - apply derivable_pt_lim_id. }
    assert (Hgg : derivable_pt_lim (fun t : R => (xS - t) * (xS - t)) x
                    (- (2 * (xS - x)))).
    { replace (- (2 * (xS - x)))
        with ((-1) * (xS - x) + (xS - x) * (-1)) by ring.
      exact (derivable_pt_lim_mult (fun t => xS - t) (fun t => xS - t)
               x (-1) (-1) Hg Hg). }
    replace (2 * (xS - x)) with (0 - - (2 * (xS - x))) by ring.
    apply derivable_pt_lim_minus.
    - apply derivable_pt_lim_const.
    - exact Hgg. }
  assert (Hsq : derivable_pt_lim sqrt (f x) (/ (2 * sqrt (f x)))).
  { apply derivable_pt_lim_sqrt. exact Hpos. }
  assert (Hcomp : derivable_pt_lim (fun t => sqrt (f t)) x
                    (/ (2 * sqrt (f x)) * (2 * (xS - x)))).
  { exact (derivable_pt_lim_comp f sqrt x (2 * (xS - x))
             (/ (2 * sqrt (f x))) Hf Hsq). }
  assert (Hsum : derivable_pt_lim (fun t => yS + sqrt (f t)) x
                   (0 + / (2 * sqrt (f x)) * (2 * (xS - x)))).
  { apply derivable_pt_lim_plus; [ apply derivable_pt_lim_const | exact Hcomp ]. }
  assert (Hsqrt_pos : 0 < sqrt (f x)) by (apply sqrt_lt_R0; exact Hpos).
  unfold f in Hsum, Hsqrt_pos.
  replace ((xS - x) / sqrt (Rr * Rr - (xS - x) * (xS - x)))
    with (0 + / (2 * sqrt (Rr * Rr - (xS - x) * (xS - x))) * (2 * (xS - x)))
    by (field; lra).
  exact Hsum.
Qed.

(* The apex H = (xS, yS + R): highest point of the graph, slope zero
   (the paper's bound on where the junction may sit is phrased around H). *)
Theorem koc25_apex :
  forall xS yS Rr,
    0 < Rr ->
    koc25_circle_graph xS yS Rr xS = yS + Rr /\
    derivable_pt_lim (koc25_circle_graph xS yS Rr) xS 0.
Proof.
  intros xS yS Rr HR.
  split.
  - unfold koc25_circle_graph.
    replace (Rr * Rr - (xS - xS) * (xS - xS)) with (Rr * Rr) by ring.
    rewrite sqrt_square; [ reflexivity | lra ].
  - pose proof (koc25_circle_graph_deriv xS yS Rr xS) as H.
    assert (Hpos : 0 < Rr * Rr - (xS - xS) * (xS - xS)) by nra.
    specialize (H Hpos).
    replace 0 with ((xS - xS) / sqrt (Rr * Rr - (xS - xS) * (xS - xS))).
    + exact H.
    + replace (xS - xS) with 0 by ring. unfold Rdiv. ring.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  The prescribed-slope point has that ANALYTIC slope (eqs (15),(16)).    *)
(*                                                                            *)
(* Part 1 (`koc_slope_point_on_circle`) characterised the point x = xS -      *)
(* s R/u algebraically (radius perpendicular to (1,s)).  Here the loop        *)
(* closes: on the circle GRAPH that point has value yS + R/u and derivative   *)
(* exactly s.  The algebraic and analytic tangency notions agree -- so eq     *)
(* (16)'s placement of the second arc really equalises the slopes at C.      *)
(* -------------------------------------------------------------------------- *)

Theorem koc25_slope_at_prescribed_point :
  forall xS yS s Rr u,
    0 < Rr -> 0 < u -> u * u = 1 + s * s ->
    koc25_circle_graph xS yS Rr (xS - s * Rr / u) = yS + Rr / u /\
    derivable_pt_lim (koc25_circle_graph xS yS Rr) (xS - s * Rr / u) s.
Proof.
  intros xS yS s Rr u HR Hu Husq.
  assert (Hne : u <> 0) by lra.
  assert (Hrad : Rr * Rr - (xS - (xS - s * Rr / u)) * (xS - (xS - s * Rr / u))
                 = (Rr / u) * (Rr / u)).
  { transitivity (Rr * Rr * (u * u - s * s) / (u * u)).
    - field. exact Hne.
    - replace (u * u - s * s) with 1 by lra. field. exact Hne. }
  assert (Hru : 0 < Rr / u) by (apply Rdiv_lt_0_compat; lra).
  assert (Hsqrt : sqrt (Rr * Rr - (xS - (xS - s * Rr / u))
                                  * (xS - (xS - s * Rr / u))) = Rr / u).
  { rewrite Hrad. rewrite sqrt_square; [ reflexivity | lra ]. }
  split.
  - unfold koc25_circle_graph. rewrite Hsqrt. reflexivity.
  - pose proof (koc25_circle_graph_deriv xS yS Rr (xS - s * Rr / u)) as H.
    assert (Hpos : 0 < Rr * Rr - (xS - (xS - s * Rr / u))
                                 * (xS - (xS - s * Rr / u)))
      by (rewrite Hrad; nra).
    specialize (H Hpos).
    assert (Heq : (xS - (xS - s * Rr / u))
                  / sqrt (Rr * Rr - (xS - (xS - s * Rr / u))
                                    * (xS - (xS - s * Rr / u))) = s).
    { rewrite Hsqrt. field. split; lra. }
    rewrite Heq in H. exact H.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  The mirror step (paper Figure 4) is sound.                             *)
(*                                                                            *)
(* The algorithm reflects the TC2/CA2 branch about the vertical through the   *)
(* junction.  Reflection preserves radius lengths and NEGATES tangent         *)
(* slopes -- so a branch built with slope -s lands, after the mirror, with    *)
(* slope +s, matching the first branch at C.                                  *)
(* -------------------------------------------------------------------------- *)

Theorem koc25_mirror_negates_slope :
  forall xC (P S : Point) s,
    (px P - px S) * 1 + (py P - py S) * s = 0 ->
    let P' := mkPoint (2 * xC - px P) (py P) in
    let S' := mkPoint (2 * xC - px S) (py S) in
    dist_sq P' S' = dist_sq P S /\
    (px P' - px S') * 1 + (py P' - py S') * (- s) = 0.
Proof.
  intros xC P S s Hperp P' S'.
  unfold P', S', dist_sq; simpl.
  split; [ ring | lra ].
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  HEADLINE: the C^1 compound join, and collinear centres.                *)
(*                                                                            *)
(* Place both centres on the junction normal: S_i = C + (R_i/u)(s, -1).       *)
(* Then C lies on BOTH circles and BOTH radii are perpendicular to the same   *)
(* tangent direction (1, s): the arcs join with a common tangent -- no kink.  *)
(* The two perpendicularity conditions force S1, C, S2 collinear: the         *)
(* classical characterisation of a compound curve (a reverse curve is the     *)
(* same statement with R2 taken negative -- centre on the other side).        *)
(* -------------------------------------------------------------------------- *)

Theorem koc25_compound_join_C1 :
  forall xC yC s R1 R2 u,
    0 < u -> u * u = 1 + s * s ->
    let C  := mkPoint xC yC in
    let S1 := mkPoint (xC + s * R1 / u) (yC - R1 / u) in
    let S2 := mkPoint (xC + s * R2 / u) (yC - R2 / u) in
    dist_sq C S1 = R1 * R1 /\
    dist_sq C S2 = R2 * R2 /\
    (px C - px S1) * 1 + (py C - py S1) * s = 0 /\
    (px C - px S2) * 1 + (py C - py S2) * s = 0.
Proof.
  intros xC yC s R1 R2 u Hu Husq C S1 S2.
  assert (Hne : u <> 0) by lra.
  unfold C, S1, S2, dist_sq; simpl.
  repeat split.
  - transitivity (R1 * R1 * (1 + s * s) / (u * u)).
    + field. exact Hne.
    + rewrite <- Husq. field. exact Hne.
  - transitivity (R2 * R2 * (1 + s * s) / (u * u)).
    + field. exact Hne.
    + rewrite <- Husq. field. exact Hne.
  - field. exact Hne.
  - field. exact Hne.
Qed.

(* The junction and both centres are collinear -- pure algebra, no
   normalisation hypotheses needed at all. *)
Theorem koc25_compound_centers_collinear :
  forall xC yC s R1 R2 u,
    u <> 0 ->
    cross (mkPoint (xC + s * R1 / u) (yC - R1 / u))
          (mkPoint xC yC)
          (mkPoint (xC + s * R2 / u) (yC - R2 / u)) = 0.
Proof.
  intros xC yC s R1 R2 u Hne.
  unfold cross; simpl. field. exact Hne.
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  The endpoint vertex, Case I / Case II, and their duality               *)
(*     (Koc 2025 eqs (21)-(26)).                                              *)
(*                                                                            *)
(* From the system endpoints A1 = (0,0) and A2, two tangent lines at slopes   *)
(* +/- m (m = tan(alpha/2)) meet at the vertex W -- the origin of the local   *)
(* frame.  Case I (system below W) and Case II (above) get separate formula   *)
(* sets in the paper's §6; the duality lemma shows Case II is Case I under    *)
(* the reflection y |-> -y, so ONE algorithm suffices.                        *)
(* -------------------------------------------------------------------------- *)

Definition koc25_v1x (m xA2 yA2 : R) : R := (yA2 + m * xA2) / (2 * m).
Definition koc25_v1y (m xA2 yA2 : R) : R := (yA2 + m * xA2) / 2.

Definition koc25_v2x (m xA2 yA2 : R) : R := (- yA2 + m * xA2) / (2 * m).
Definition koc25_v2y (m xA2 yA2 : R) : R := (yA2 - m * xA2) / 2.

(* Case I (eqs (23),(24)): line y = m x through A1 meets
   y = yA2 - m (x - xA2) through A2 at exactly (v1x, v1y). *)
Theorem koc25_vertex_case1 :
  forall m xA2 yA2,
    m <> 0 ->
    m * koc25_v1x m xA2 yA2 = koc25_v1y m xA2 yA2 /\
    yA2 - m * (koc25_v1x m xA2 yA2 - xA2) = koc25_v1y m xA2 yA2.
Proof.
  intros m xA2 yA2 Hm.
  unfold koc25_v1x, koc25_v1y.
  split; field; lra.
Qed.

(* Case II (eqs (25),(26)): line y = - m x through A1 meets
   y = yA2 + m (x - xA2) through A2 at exactly (v2x, v2y). *)
Theorem koc25_vertex_case2 :
  forall m xA2 yA2,
    m <> 0 ->
    - m * koc25_v2x m xA2 yA2 = koc25_v2y m xA2 yA2 /\
    yA2 + m * (koc25_v2x m xA2 yA2 - xA2) = koc25_v2y m xA2 yA2.
Proof.
  intros m xA2 yA2 Hm.
  unfold koc25_v2x, koc25_v2y.
  split; field; lra.
Qed.

(* Duality: Case II is Case I reflected about the x-axis. The paper's two
   algorithm variants (its §6, Tables 1-2) are one theorem and its mirror. *)
Theorem koc25_case_duality :
  forall m xA2 yA2,
    koc25_v2x m xA2 yA2 = koc25_v1x m xA2 (- yA2) /\
    koc25_v2y m xA2 yA2 = - koc25_v1y m xA2 (- yA2).
Proof.
  intros m xA2 yA2.
  unfold koc25_v1x, koc25_v1y, koc25_v2x, koc25_v2y.
  split; unfold Rdiv; ring.
Qed.

(* -------------------------------------------------------------------------- *)
(* §6  Worked example: the 3-4-5-10 compound join.                            *)
(*                                                                            *)
(* Junction C = (0,0), slope s = 3/4 (u = 5/4), radii R1 = 5, R2 = 10.        *)
(* Centres: S1 = (3,-4), S2 = (6,-8) -- both on one ray through C, at         *)
(* squared distances 25 and 100.  A sharp-then-gentle compound (R2 = 2 R1)     *)
(* with every check closing in rational arithmetic.                           *)
(* -------------------------------------------------------------------------- *)

Example koc25_example_345_join :
  dist_sq (mkPoint 0 0) (mkPoint 3 (-4)) = 5 * 5 /\
  dist_sq (mkPoint 0 0) (mkPoint 6 (-8)) = 10 * 10 /\
  (0 - 3) * 1 + (0 - (-4)) * (3/4) = 0 /\
  (0 - 6) * 1 + (0 - (-8)) * (3/4) = 0 /\
  cross (mkPoint 3 (-4)) (mkPoint 0 0) (mkPoint 6 (-8)) = 0.
Proof.
  unfold dist_sq, cross; simpl. repeat split; lra.
Qed.

Example koc25_example_345_join_is_koc :
  mkPoint (0 + (3/4) * 5 / (5/4)) (0 - 5 / (5/4)) = mkPoint 3 (-4) /\
  mkPoint (0 + (3/4) * 10 / (5/4)) (0 - 10 / (5/4)) = mkPoint 6 (-8).
Proof.
  split; f_equal; lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §7  Audit footprint.                                                       *)
(* -------------------------------------------------------------------------- *)

Print Assumptions koc25_circle_graph_deriv.
Print Assumptions koc25_apex.
Print Assumptions koc25_slope_at_prescribed_point.
Print Assumptions koc25_mirror_negates_slope.
Print Assumptions koc25_compound_join_C1.
Print Assumptions koc25_compound_centers_collinear.
Print Assumptions koc25_case_duality.

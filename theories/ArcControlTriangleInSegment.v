(* ============================================================================
   NetTopologySuite.Proofs.ArcControlTriangleInSegment
   ----------------------------------------------------------------------------
   Issue #64 ask #4c / #3 V-CP: the single-arc "bulge-inclusion" building block
   toward TRUE-region soundness for `POINT_IN_CURVE_RING`.

   `CurvePolygonValid.v` documents, as an INFORMAL claim (not yet a lemma),
   that the inscribed control-polygon floor is a sound under-approximation of
   the true curved region: "`point_in_inscribed_ring p r n => p is in the true
   region`, but NOT conversely (a point in a bulge reads false)."  A survey of
   the corpus's Jordan/JCT toolkit (`RelateNG.point_set_characterises_
   geometric_interior`, `RelateCurveArcSegment`'s arc-segment-lens composition)
   found that toolkit is triangle-only and, for curves, only ever reasons
   about the CONTROL triangle itself -- it never touches the actual curved
   boundary, so it cannot discharge this claim.  Closing it in full (arbitrary
   multi-arc rings, holes, self-tangency) needs genuinely new ray-vs-arc
   crossing geometry -- the same class of hard work `WindingNumber.v` already
   defers.  That is out of scope here.

   This file closes the NARROW, self-contained sub-case that needs NO new
   Jordan-theorem content at all: for a single valid arc, every point
   affinely INTERIOR to its inscribed control triangle (start, mid, end) lies
   in the TRUE region the arc bounds together with its chord -- the circular
   segment `in_circular_segment`, defined directly (bulge side of the chord,
   inside the closed disk) with no ray-casting or Jordan machinery at all.

   Proved here (allowlist axioms only -- `Print Assumptions` shows just
   `sig_forall_dec` + `functional_extensionality_dep`, no `Classic`, no
   `Admitted`/`Axiom`/`Parameter`):
     §1  `in_arc_control_triangle` -- P is an affine combination
         `(1-beta-gamma)*S + beta*M + gamma*E` with `beta, gamma > 0` and
         `beta + gamma < 1` (equivalently all three barycentric weights > 0).
     §2  `in_circular_segment` -- P is on the arc's bulge side of the chord
         (`ArcOrient.arc_interior_side`) AND inside the closed disk bounded by
         the circumcircle (`dist_sq (arc_center a) P <= dist_sq (arc_center a)
         (arc_start a)`).
     §3  `arc_control_triangle_in_circular_segment` -- HEADLINE: for a valid
         arc, `in_arc_control_triangle a P -> in_circular_segment a P`.
         Chord-side half: `cross_R_pt` is affine in its third argument, and
         the chord endpoints S, E themselves contribute zero (they lie ON the
         chord line), so `arc_side_chord a P = beta * arc_side_chord a M`
         exactly (`ring`) -- same sign as M since `beta > 0` and (by
         `valid_arc`) `arc_side_chord a M <> 0`.  Disk half: P - O is the
         same affine combination of S-O, M-O, E-O (each of squared norm R2 by
         `arc_center_equidistant`); expanding `dist_sq O P` and bounding each
         pairwise dot product by R2 (from `(u-v)^2 >= 0`) gives
         `dist_sq O P <= (alpha+beta+gamma)^2 * R2 = R2`.

   DEFERRED (honest scope, unchanged): the converse (a point in the true
   region need not be in the control triangle -- the bulge itself); lifting
   this single-arc fact through a whole curve ring / `to_geometry` /
   `POINT_IN_CURVE_RING`'s ray-casting oracle, which is the genuinely open
   Jordan frontier this file does NOT attempt.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import Distance CurveGeometry ArcOrient ArcChordApprox.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  Affine interior of the arc's inscribed control triangle.               *)
(* -------------------------------------------------------------------------- *)

Definition in_arc_control_triangle (a : CircularArc) (P : Point) : Prop :=
  exists beta gamma : R,
    0 < beta /\ 0 < gamma /\ beta + gamma < 1 /\
    px P = (1 - beta - gamma) * px (arc_start a) + beta * px (arc_mid a)
            + gamma * px (arc_end a) /\
    py P = (1 - beta - gamma) * py (arc_start a) + beta * py (arc_mid a)
            + gamma * py (arc_end a).

(* -------------------------------------------------------------------------- *)
(* §2  The TRUE region bounded by the arc and its chord: bulge side of the    *)
(*     chord, inside the closed disk.  No ray-casting, no Jordan machinery.   *)
(* -------------------------------------------------------------------------- *)

Definition in_circular_segment (a : CircularArc) (P : Point) : Prop :=
  arc_interior_side a P /\
  dist_sq (arc_center a) P <= dist_sq (arc_center a) (arc_start a).

(* -------------------------------------------------------------------------- *)
(* §3  Headline: the control triangle's interior sits inside the segment.     *)
(* -------------------------------------------------------------------------- *)

Theorem arc_control_triangle_in_circular_segment :
  forall (a : CircularArc) (P : Point),
    valid_arc a ->
    in_arc_control_triangle a P ->
    in_circular_segment a P.
Proof.
  intros a P Hva [beta [gamma [Hb [Hg [Hbg [HPx HPy]]]]]].
  set (alpha := 1 - beta - gamma).
  assert (Ha : 0 < alpha) by (unfold alpha; lra).
  assert (Habg : alpha + beta + gamma = 1) by (unfold alpha; lra).
  split.

  (* ---- Chord-side half: same side as arc_mid. ---------------------------- *)
  - unfold arc_interior_side.
    assert (Hshape :
      arc_side_chord a P = beta * arc_side_chord a (arc_mid a)).
    { unfold arc_side_chord, cross_R_pt.
      rewrite HPx, HPy. unfold alpha in *. ring. }
    rewrite Hshape.
    pose proof (arc_side_chord_mid_nonzero a Hva) as Hnz.
    set (s := arc_side_chord a (arc_mid a)) in *.
    (* Goal: 0 < s * (beta * s), i.e. beta * s * s > 0 for s <> 0, beta > 0. *)
    assert (Hs2 : 0 < s * s).
    { destruct (Rtotal_order s 0) as [Hlt | [Heq | Hgt]].
      - assert (Hns : 0 < - s) by lra.
        replace (s * s) with ((- s) * (- s)) by ring.
        apply Rmult_lt_0_compat; exact Hns.
      - exfalso. apply Hnz. exact Heq.
      - apply Rmult_lt_0_compat; exact Hgt. }
    replace (s * (beta * s)) with (beta * (s * s)) by ring.
    apply Rmult_lt_0_compat; [exact Hb | exact Hs2].

  (* ---- Disk half: P stays inside the closed circumdisk. ------------------ *)
  - set (O := arc_center a). set (S := arc_start a).
    set (M := arc_mid a). set (E := arc_end a).
    set (R2 := dist_sq O S).
    destruct (arc_center_equidistant a Hva) as [HSM HSE].
    fold O S M E in HSM, HSE.
    assert (HR2M : dist_sq O M = R2) by (unfold R2; lra).
    assert (HR2E : dist_sq O E = R2) by (unfold R2; lra).
    set (ux := px S - px O). set (uy := py S - py O).
    set (vx := px M - px O). set (vy := py M - py O).
    set (wx := px E - px O). set (wy := py E - py O).
    assert (Huu : ux * ux + uy * uy = R2)
      by (unfold ux, uy, R2, dist_sq; ring).
    assert (Hvv : vx * vx + vy * vy = R2)
      by (unfold vx, vy; rewrite <- HR2M; unfold dist_sq; ring).
    assert (Hww : wx * wx + wy * wy = R2)
      by (unfold wx, wy; rewrite <- HR2E; unfold dist_sq; ring).
    (* Pairwise dot products are bounded above by R2, via (u-v)^2 >= 0. *)
    assert (Huv : ux * vx + uy * vy <= R2).
    { assert (Hsq : 0 <= (ux - vx) * (ux - vx) + (uy - vy) * (uy - vy)).
      { pose proof (sqr_nonneg (ux - vx)) as H1.
        pose proof (sqr_nonneg (uy - vy)) as H2. lra. }
      assert (Hexp : (ux - vx) * (ux - vx) + (uy - vy) * (uy - vy)
                     = (ux * ux + uy * uy) + (vx * vx + vy * vy)
                       - 2 * (ux * vx + uy * vy)) by ring.
      rewrite Hexp, Huu, Hvv in Hsq. lra. }
    assert (Huw : ux * wx + uy * wy <= R2).
    { assert (Hsq : 0 <= (ux - wx) * (ux - wx) + (uy - wy) * (uy - wy)).
      { pose proof (sqr_nonneg (ux - wx)) as H1.
        pose proof (sqr_nonneg (uy - wy)) as H2. lra. }
      assert (Hexp : (ux - wx) * (ux - wx) + (uy - wy) * (uy - wy)
                     = (ux * ux + uy * uy) + (wx * wx + wy * wy)
                       - 2 * (ux * wx + uy * wy)) by ring.
      rewrite Hexp, Huu, Hww in Hsq. lra. }
    assert (Hvw : vx * wx + vy * wy <= R2).
    { assert (Hsq : 0 <= (vx - wx) * (vx - wx) + (vy - wy) * (vy - wy)).
      { pose proof (sqr_nonneg (vx - wx)) as H1.
        pose proof (sqr_nonneg (vy - wy)) as H2. lra. }
      assert (Hexp : (vx - wx) * (vx - wx) + (vy - wy) * (vy - wy)
                     = (vx * vx + vy * vy) + (wx * wx + wy * wy)
                       - 2 * (vx * wx + vy * wy)) by ring.
      rewrite Hexp, Hvv, Hww in Hsq. lra. }
    (* dist_sq O P expands as the same affine combination of u, v, w. *)
    assert (Hexpand :
      dist_sq O P
      = alpha * alpha * (ux * ux + uy * uy)
        + beta * beta * (vx * vx + vy * vy)
        + gamma * gamma * (wx * wx + wy * wy)
        + 2 * alpha * beta * (ux * vx + uy * vy)
        + 2 * alpha * gamma * (ux * wx + uy * wy)
        + 2 * beta * gamma * (vx * wx + vy * wy)).
    { unfold dist_sq. rewrite HPx, HPy.
      unfold ux, uy, vx, vy, wx, wy, alpha in *.
      unfold O, S, M, E in *. ring. }
    rewrite Hexpand, Huu, Hvv, Hww.
    (* Scale each pairwise-dot bound by its nonnegative coefficient. *)
    assert (Hab_nn : 0 <= 2 * alpha * beta) by (apply Rmult_le_pos; lra).
    assert (Hac_nn : 0 <= 2 * alpha * gamma) by (apply Rmult_le_pos; lra).
    assert (Hbc_nn : 0 <= 2 * beta * gamma) by (apply Rmult_le_pos; lra).
    assert (Hcross1 : 2 * alpha * beta * (ux * vx + uy * vy) <= 2 * alpha * beta * R2)
      by (apply Rmult_le_compat_l; [exact Hab_nn | exact Huv]).
    assert (Hcross2 : 2 * alpha * gamma * (ux * wx + uy * wy) <= 2 * alpha * gamma * R2)
      by (apply Rmult_le_compat_l; [exact Hac_nn | exact Huw]).
    assert (Hcross3 : 2 * beta * gamma * (vx * wx + vy * wy) <= 2 * beta * gamma * R2)
      by (apply Rmult_le_compat_l; [exact Hbc_nn | exact Hvw]).
    (* (alpha+beta+gamma)^2 = 1, so the R2-scaled terms sum to exactly R2. *)
    assert (Hone2 : (alpha + beta + gamma) * (alpha + beta + gamma) = 1)
      by (rewrite Habg; ring).
    assert (Hsum2 :
      alpha * alpha * R2 + beta * beta * R2 + gamma * gamma * R2
      + 2 * alpha * beta * R2 + 2 * alpha * gamma * R2 + 2 * beta * gamma * R2
      = R2).
    { assert (Hfactor :
        alpha * alpha * R2 + beta * beta * R2 + gamma * gamma * R2
        + 2 * alpha * beta * R2 + 2 * alpha * gamma * R2 + 2 * beta * gamma * R2
        = (alpha + beta + gamma) * (alpha + beta + gamma) * R2) by ring.
      rewrite Hfactor, Hone2. ring. }
    lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Audit footprint.                                                       *)
(* -------------------------------------------------------------------------- *)

Print Assumptions arc_control_triangle_in_circular_segment.

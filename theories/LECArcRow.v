(* ============================================================================
   NetTopologySuite.Proofs.LECArcRow
   ----------------------------------------------------------------------------
   The ARC row of the typed LEC obstacle-distance table (the ledger's open
   rung "point-to-arc spec, chord-sign sector split, no atan2" — closed).

   The engine's typed obstacle metric (`ObstacleDistance`, JTS jts-curve
   typed-obstacle lane) prices a CircularString per 3-control window by
   point-to-arc distance.  The corpus already banked the analytic core:

     - ArcDistance.v          |dist O P − r| circle bound + radial foot
     - ArcPointDistance.v     radial lower/attainment, endpoint fallback
                              lower bound, centre case (all Qed)
     - ArcSinglePeak.v        the single-peak dot bound (Qed 2026-07-01)
     - ArcSpanAtan2.v         chord-sign test ⟺ atan2 sweep test

   What was missing — and what this module adds — is the GLUE that turns
   those case-conditioned lemmas into one certified row:

     1. `on_circle_side_zero_is_endpoint`: the circumcircle meets the chord
        LINE only at the chord endpoints (divisionless proof: the scalar
        q·(q − m) = 0 forces the chord parameter to 0 or 1).
     2. `arc_span_contains_iff_sign`: for on-circle points the span
        predicate IS the closed sign test
        0 <= side(mid) · side(X) — one multiplication, no atan2, no
        point-equality probes.  This is the decidable gate a total
        function needs.
     3. `arc_dist`: the TOTAL closed-form point-to-arc distance, exactly
        the oracle's ARC_DISTANCE decision tree (centre → nearer endpoint
        (= r); foot in span → |d − r|; else → nearer endpoint).
     4. `arc_dist_exact`: unconditional exactness — `arc_dist` is a lower
        bound on the distance to EVERY on-arc point and is attained by an
        on-arc point.  No case hypotheses survive in the statement.
     5. `empty_disk_arc_iff`: the LEC-table row, same iff shape as
        LECObstacleDistance.v's disc/ring/union rows: a candidate disk is
        empty of the arc iff its radius is at most `arc_dist`.  Together
        with `empty_disk_union_iff` this prices CompoundCurve windows.
     6. `query_side_sector_hypothesis_refuted` (ledger F4): the tempting
        shortcut "run the chord-sign sector gate on the QUERY POINT
        instead of its radial foot" is disproved on a rational witness.
        Arc (3,4)–(0,5)–(−3,4) on the r=5 circle about the origin; query
        P = (16,12).  P passes the naive gate (both P and the mid lie
        below the chord y = 4 in sign terms: product 288 > 0), so the
        naive row reports |20 − 5| = 15 — but the radial foot (4,3) is
        OUTSIDE the span and no arc point is nearer than sqrt 233 > 15.2.
        The naive value is a clearance the laser cannot have: the gate
        must test the FOOT, never the query.

   Witness arithmetic is fully rational (3-4-5 family): centre (0,0),
   r = 5, foot (4,3), naive product 288, foot product −36, endpoint
   distances sqrt 233 / sqrt 425.

   Pure math on R.  Classical-reals trio only (see Print Assumptions).

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import Distance CurveGeometry ArcOrient ArcIntersect
  ArcChordApprox ArcArcCircles ArcArcSound CurveRingSimple ArcDistance
  ArcPointDistance LargestEmptyCircle.

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  The circumcircle meets the chord line only at the chord endpoints.     *)
(*                                                                            *)
(* Divisionless route: write q := <X−S, E−S> and m := |E−S|².  The side      *)
(* condition transports m·(X−S) = q·(E−S) coordinatewise; the two circle     *)
(* equations then collapse to q·(q − m) = 0, i.e. the chord parameter        *)
(* t = q/m is 0 or 1 — without ever dividing.                                *)
(* -------------------------------------------------------------------------- *)

Lemma on_circle_side_zero_is_endpoint :
  forall (a : CircularArc) (X : Point),
    valid_arc a ->
    dist_sq (arc_center a) X = dist_sq (arc_center a) (arc_start a) ->
    arc_side_chord a X = 0 ->
    X = arc_start a \/ X = arc_end a.
Proof.
  intros a X Hva Hcirc Hside.
  set (ux := px (arc_end a) - px (arc_start a)).
  set (uy := py (arc_end a) - py (arc_start a)).
  set (m := ux * ux + uy * uy).
  set (q := (px X - px (arc_start a)) * ux + (py X - py (arc_start a)) * uy).
  (* S <> E, i.e. m > 0, from valid_arc (the ArcPointDistance.v pattern). *)
  assert (HSE : 0 < dist (arc_start a) (arc_end a)).
  { pose proof (dist_nonneg (arc_start a) (arc_end a)) as Hnn.
    destruct (Rle_lt_or_eq_dec 0 (dist (arc_start a) (arc_end a)) Hnn)
      as [Hlt | Heq0]; [ exact Hlt | exfalso ].
    symmetry in Heq0. apply dist_eq_zero_iff in Heq0.
    destruct Heq0 as [Hx Hy].
    unfold valid_arc in Hva. apply Hva. cbv zeta.
    rewrite <- Hx, <- Hy. ring. }
  assert (Hm : 0 < m).
  { pose proof (dist_mul_self (arc_start a) (arc_end a)) as Hms.
    assert (Hpos : 0 < dist (arc_start a) (arc_end a)
                       * dist (arc_start a) (arc_end a)) by nra.
    rewrite Hms in Hpos. unfold dist_sq in Hpos.
    unfold m, ux, uy. nra. }
  (* The side condition, normalised to the (ux, uy) frame. *)
  assert (Hz : ux * (py X - py (arc_start a)) - uy * (px X - px (arc_start a)) = 0).
  { assert (Hb : ux * (py X - py (arc_start a)) - uy * (px X - px (arc_start a))
                 = arc_side_chord a X)
      by (unfold arc_side_chord, cross_R_pt, ux, uy; ring).
    rewrite Hb. exact Hside. }
  (* Coordinatewise transport: m·(X − S) = q·(E − S). *)
  assert (HtxEq : m * (px X - px (arc_start a)) = q * ux).
  { assert (Hkey : q * ux - m * (px X - px (arc_start a))
                   = uy * (ux * (py X - py (arc_start a))
                           - uy * (px X - px (arc_start a))))
      by (unfold q, m; ring).
    rewrite Hz in Hkey. lra. }
  assert (HtyEq : m * (py X - py (arc_start a)) = q * uy).
  { assert (Hkey : q * uy - m * (py X - py (arc_start a))
                   = - ux * (ux * (py X - py (arc_start a))
                             - uy * (px X - px (arc_start a))))
      by (unfold q, m; ring).
    rewrite Hz in Hkey. lra. }
  (* Circle equations, rearranged about S. *)
  pose proof (arc_center_equidistant a Hva) as [_ Hse].
  assert (HG1 : 2 * ((px (arc_start a) - px (arc_center a)) * (px X - px (arc_start a))
                     + (py (arc_start a) - py (arc_center a)) * (py X - py (arc_start a)))
                + ((px X - px (arc_start a)) * (px X - px (arc_start a))
                   + (py X - py (arc_start a)) * (py X - py (arc_start a))) = 0).
  { unfold dist_sq in Hcirc. nra. }
  assert (HG2 : 2 * ((px (arc_start a) - px (arc_center a)) * ux
                     + (py (arc_start a) - py (arc_center a)) * uy) + m = 0).
  { unfold dist_sq in Hse. unfold m, ux, uy. nra. }
  (* The scalar collapse: q·(q − m) = 0. *)
  assert (Hq : q * (q - m) = 0).
  { assert (Hstep : q * (q - m)
      = m * (2 * ((px (arc_start a) - px (arc_center a)) * (px X - px (arc_start a))
                  + (py (arc_start a) - py (arc_center a)) * (py X - py (arc_start a)))
             + ((px X - px (arc_start a)) * (px X - px (arc_start a))
                + (py X - py (arc_start a)) * (py X - py (arc_start a))))
        - (2 * (px (arc_start a) - px (arc_center a)) + (px X - px (arc_start a)))
          * (m * (px X - px (arc_start a)) - q * ux)
        - (2 * (py (arc_start a) - py (arc_center a)) + (py X - py (arc_start a)))
          * (m * (py X - py (arc_start a)) - q * uy)
        - q * (2 * ((px (arc_start a) - px (arc_center a)) * ux
                    + (py (arc_start a) - py (arc_center a)) * uy) + m))
      by (unfold q, m; ring).
    assert (Zx : m * (px X - px (arc_start a)) - q * ux = 0) by lra.
    assert (Zy : m * (py X - py (arc_start a)) - q * uy = 0) by lra.
    rewrite HG1, HG2, Zx, Zy in Hstep. lra. }
  destruct (Rmult_integral _ _ Hq) as [Hq0 | Hq1].
  - left. apply point_eq_of_coords.
    + rewrite Hq0 in HtxEq. nra.
    + rewrite Hq0 in HtyEq. nra.
  - right.
    assert (Hqm : q = m) by lra.
    rewrite Hqm in HtxEq, HtyEq.
    apply point_eq_of_coords.
    + unfold ux in HtxEq. nra.
    + unfold uy in HtyEq. nra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  The span predicate is the closed sign test, on the circle.             *)
(*                                                                            *)
(* `arc_span_contains` carries two point-equality disjuncts (the endpoints).  *)
(* On the circumcircle those are exactly the zeros of the side product, so    *)
(* the whole predicate collapses to one closed inequality — the decidable     *)
(* gate the total function below (and the engine's window test) uses.        *)
(* -------------------------------------------------------------------------- *)

Lemma arc_span_contains_iff_sign :
  forall (a : CircularArc) (X : Point),
    valid_arc a ->
    dist_sq (arc_center a) X = dist_sq (arc_center a) (arc_start a) ->
    (arc_span_contains a X <->
     0 <= arc_side_chord a (arc_mid a) * arc_side_chord a X).
Proof.
  intros a X Hva Hcirc. split.
  - intros [Hint | [HS | HE]].
    + unfold arc_interior_side in Hint. lra.
    + rewrite HS.
      assert (Hz : arc_side_chord a (arc_start a) = 0)
        by (unfold arc_side_chord, cross_R_pt; ring).
      rewrite Hz, Rmult_0_r. lra.
    + rewrite HE.
      assert (Hz : arc_side_chord a (arc_end a) = 0)
        by (unfold arc_side_chord, cross_R_pt; ring).
      rewrite Hz, Rmult_0_r. lra.
  - intros Hge.
    destruct (Rle_lt_or_eq_dec 0 _ Hge) as [Hlt | Heq0].
    + left. exact Hlt.
    + symmetry in Heq0.
      destruct (Rmult_integral _ _ Heq0) as [HM0 | HX0].
      * exfalso.
        assert (Hlink : arc_side_chord a (arc_mid a)
                        = - ((px (arc_mid a) - px (arc_start a))
                             * (py (arc_end a) - py (arc_start a))
                             - (py (arc_mid a) - py (arc_start a))
                             * (px (arc_end a) - px (arc_start a))))
          by (unfold arc_side_chord, cross_R_pt; ring).
        rewrite HM0 in Hlink.
        unfold valid_arc in Hva. apply Hva. cbv zeta. lra.
      * destruct (on_circle_side_zero_is_endpoint a X Hva Hcirc HX0) as [HX | HX].
        -- right; left; exact HX.
        -- right; right; exact HX.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  The total closed-form row: `arc_dist`.                                 *)
(*                                                                            *)
(* Mirrors the oracle's ARC_DISTANCE decision tree.  The oracle always takes  *)
(* the min with the endpoint distances; in the radial branch that min IS the  *)
(* radial value (|d − r| <= each endpoint distance, both endpoints being on   *)
(* the circle), so the bare radial form below computes the same number.       *)
(* -------------------------------------------------------------------------- *)

Definition arc_dist (a : CircularArc) (P : Point) : R :=
  match Rle_dec (dist (arc_center a) P) 0 with
  | left _ => Rmin (dist P (arc_start a)) (dist P (arc_end a))
  | right _ =>
      match Rle_dec 0 (arc_side_chord a (arc_mid a)
                       * arc_side_chord a
                           (radial_foot (arc_center a) P (arc_radius a))) with
      | left _ => Rabs (dist (arc_center a) P - arc_radius a)
      | right _ => Rmin (dist P (arc_start a)) (dist P (arc_end a))
      end
  end.

(* The chord endpoints are on their own arc (circumcircle + span boundary). *)
Lemma on_arc_start : forall a : CircularArc, on_arc a (arc_start a).
Proof.
  intro a. split.
  - apply inCircle_R_arc_start_self.
  - apply arc_span_contains_start.
Qed.

Lemma on_arc_end : forall a : CircularArc, on_arc a (arc_end a).
Proof.
  intro a. split.
  - apply inCircle_R_arc_end_self.
  - apply arc_span_contains_end.
Qed.

Lemma arc_dist_nonneg : forall a P, 0 <= arc_dist a P.
Proof.
  intros a P. unfold arc_dist.
  destruct (Rle_dec (dist (arc_center a) P) 0).
  - apply Rmin_glb; apply dist_nonneg.
  - destruct (Rle_dec 0 (arc_side_chord a (arc_mid a)
              * arc_side_chord a (radial_foot (arc_center a) P (arc_radius a)))).
    + apply Rabs_pos.
    + apply Rmin_glb; apply dist_nonneg.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3b  Exactness: `arc_dist` is the set distance to the arc, unconditionally.*)
(* -------------------------------------------------------------------------- *)

Theorem arc_dist_exact :
  forall (a : CircularArc) (P : Point),
    valid_arc a ->
    (forall X, on_arc a X -> arc_dist a P <= dist P X)
    /\ (exists X, on_arc a X /\ dist P X = arc_dist a P).
Proof.
  intros a P Hva.
  unfold arc_dist.
  destruct (Rle_dec (dist (arc_center a) P) 0) as [Hc | Hc].
  - (* centre case: P is the circumcentre, every arc point is at r *)
    assert (Hc0 : dist (arc_center a) P = 0)
      by (pose proof (dist_nonneg (arc_center a) P); lra).
    pose proof (point_to_arc_dist_centre_is_r a P (arc_start a) Hva Hc0
                  (on_arc_start a)) as HS.
    pose proof (point_to_arc_dist_centre_is_r a P (arc_end a) Hva Hc0
                  (on_arc_end a)) as HE.
    split.
    + intros X HX.
      pose proof (point_to_arc_dist_centre_is_r a P X Hva Hc0 HX) as HXr.
      rewrite <- HS, <- HE. rewrite Rmin_left by lra. lra.
    + exists (arc_start a). split; [apply on_arc_start|].
      rewrite <- HS, <- HE. rewrite Rmin_left by lra. lra.
  - assert (Hd : 0 < dist (arc_center a) P)
      by (pose proof (dist_nonneg (arc_center a) P); lra).
    (* the radial foot lies on the circumcircle *)
    assert (HFc : dist_sq (arc_center a)
                    (radial_foot (arc_center a) P (arc_radius a))
                  = dist_sq (arc_center a) (arc_start a)).
    { pose proof (radial_foot_on_circle (arc_center a) P (arc_radius a) Hd
                    (arc_radius_nonneg a)) as HF.
      rewrite <- 2!dist_mul_self. rewrite HF. unfold arc_radius. reflexivity. }
    destruct (Rle_dec 0 (arc_side_chord a (arc_mid a)
              * arc_side_chord a (radial_foot (arc_center a) P (arc_radius a))))
      as [Hsig | Hsig].
    + (* radial branch: the sign gate admits the foot into the span *)
      assert (Hspan : arc_span_contains a
                        (radial_foot (arc_center a) P (arc_radius a)))
        by (apply (arc_span_contains_iff_sign a _ Hva HFc); exact Hsig).
      split.
      * intros X HX.
        exact (point_to_arc_dist_radial_lower a P X Hva HX Hd Hspan).
      * destruct (point_to_arc_attains_radial a P Hva Hd Hspan) as [Hon Hdist].
        exists (radial_foot (arc_center a) P (arc_radius a)).
        split; [exact Hon | exact Hdist].
    + (* fallback branch: foot rejected, nearer endpoint is the answer *)
      assert (Hnot : ~ arc_span_contains a
                       (radial_foot (arc_center a) P (arc_radius a))).
      { intro Hin. apply Hsig.
        apply (arc_span_contains_iff_sign a _ Hva HFc). exact Hin. }
      split.
      * intros X HX.
        pose proof (point_to_arc_dist_fallback_ends_lower a P X Hva HX Hd Hnot)
          as Hlow.
        eapply Rle_trans; [ | exact Hlow ].
        unfold point_to_arc_candidate_endpoints.
        rewrite (dist_sym (arc_start a) P), (dist_sym (arc_end a) P).
        unfold Rmin.
        destruct (Rle_dec (dist P (arc_start a)) (dist P (arc_end a))); lra.
      * destruct (Rle_dec (dist P (arc_start a)) (dist P (arc_end a)))
          as [Hle | Hgt].
        -- exists (arc_start a). split; [apply on_arc_start|].
           symmetry. apply Rmin_left. exact Hle.
        -- exists (arc_end a). split; [apply on_arc_end|].
           symmetry. apply Rmin_right. lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  The LEC-table row: emptiness against an arc obstacle is one            *)
(*     comparison against `arc_dist` — same shape as the disc/ring/union      *)
(*     rows of LECObstacleDistance.v.  With `empty_disk_union_iff` this       *)
(*     prices every CompoundCurve window of the typed obstacle table.         *)
(* -------------------------------------------------------------------------- *)

Theorem empty_disk_arc_iff :
  forall (a : CircularArc) (O : Point) (rho : R),
    valid_arc a ->
    (empty_disk (on_arc a) O rho <-> 0 <= rho /\ rho <= arc_dist a O).
Proof.
  intros a O rho Hva.
  destruct (arc_dist_exact a O Hva) as [Hlow [X0 [HX0 Hatt]]].
  split.
  - intros [Hr Hemp]. split; [exact Hr|].
    rewrite <- Hatt. apply Hemp. exact HX0.
  - intros [Hr Hle]. split; [exact Hr|].
    intros Q HQ. eapply Rle_trans; [exact Hle|]. apply Hlow. exact HQ.
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  Ledger F4 — "gate the sector on the query point" (REFUTED).            *)
(*                                                                            *)
(* The sign gate of §2 tests the radial FOOT.  Testing the query point P      *)
(* itself looks equivalent (same side, one projection cheaper) — it is not:   *)
(* P and its foot can straddle the chord line.  Witness: the minor arc        *)
(* (3,4)–(0,5)–(−3,4) of the r=5 circle about the origin, P = (16,12).       *)
(* P passes the naive gate, so the naive row reports |20 − 5| = 15; but the   *)
(* foot (4,3) is outside the span and every arc point is ≥ sqrt 233 > 15.2   *)
(* away.  The naive value is a clearance the laser cannot achieve.            *)
(* -------------------------------------------------------------------------- *)

Definition wS : Point := mkPoint 3 4.
Definition wM : Point := mkPoint 0 5.
Definition wE : Point := mkPoint (-3) 4.
Definition warc : CircularArc := mkCircularArc wS wM wE.
Definition wP : Point := mkPoint 16 12.

Lemma warc_valid : valid_arc warc.
Proof.
  unfold valid_arc, warc, wS, wM, wE.
  cbn [px py arc_start arc_mid arc_end]. lra.
Qed.

Lemma warc_center : arc_center warc = mkPoint 0 0.
Proof.
  unfold arc_center, warc, wS, wM, wE.
  cbn [px py arc_start arc_mid arc_end].
  apply point_eq_of_coords; cbn [px py]; unfold Rdiv; ring_simplify; lra.
Qed.

Lemma warc_radius : arc_radius warc = 5.
Proof.
  unfold arc_radius. rewrite warc_center.
  assert (H25 : dist_sq (mkPoint 0 0) (arc_start warc) = 5 * 5)
    by (unfold warc, wS, dist_sq; cbn [arc_start px py]; ring).
  unfold dist. rewrite H25.
  replace (5 * 5) with (Rsqr 5) by (unfold Rsqr; ring).
  apply sqrt_Rsqr. lra.
Qed.

Lemma warc_dist_OP : dist (arc_center warc) wP = 20.
Proof.
  rewrite warc_center.
  assert (H400 : dist_sq (mkPoint 0 0) wP = 20 * 20)
    by (unfold wP, dist_sq; cbn [px py]; ring).
  unfold dist. rewrite H400.
  replace (20 * 20) with (Rsqr 20) by (unfold Rsqr; ring).
  apply sqrt_Rsqr. lra.
Qed.

Lemma warc_foot : radial_foot (arc_center warc) wP (arc_radius warc)
                  = mkPoint 4 3.
Proof.
  unfold radial_foot.
  rewrite warc_radius, warc_dist_OP, warc_center.
  unfold wP. cbn [px py].
  apply point_eq_of_coords; cbn [px py]; lra.
Qed.

(* The naive gate PASSES at P: P is on the mid's side of the chord. *)
Lemma warc_naive_gate : arc_interior_side warc wP.
Proof.
  unfold arc_interior_side, arc_side_chord, cross_R_pt, warc, wS, wM, wE, wP.
  cbn [arc_start arc_mid arc_end px py]. nra.
Qed.

(* ... so the naive row prices the window at |20 − 5| = 15. *)
Lemma warc_naive_value :
  Rabs (dist (arc_center warc) wP - arc_radius warc) = 15.
Proof.
  rewrite warc_dist_OP, warc_radius.
  rewrite Rabs_right by lra. lra.
Qed.

(* ... but no on-arc point is within 15 + 1/5 of P. *)
Lemma warc_no_point_within_15 :
  forall X, on_arc warc X -> 15 + 1/5 <= dist wP X.
Proof.
  intros X HX.
  assert (Hd : 0 < dist (arc_center warc) wP) by (rewrite warc_dist_OP; lra).
  assert (Hnot : ~ arc_span_contains warc
                   (radial_foot (arc_center warc) wP (arc_radius warc))).
  { rewrite warc_foot. intros [Hint | [HS | HE]].
    - unfold arc_interior_side, arc_side_chord, cross_R_pt, warc, wS, wM, wE
        in Hint.
      cbn [arc_start arc_mid arc_end px py] in Hint. nra.
    - unfold warc, wS in HS. cbn [arc_start] in HS. inversion HS. lra.
    - unfold warc, wE in HE. cbn [arc_end] in HE. inversion HE. lra. }
  pose proof (point_to_arc_dist_fallback_ends_lower warc wP X warc_valid HX Hd
                Hnot) as Hlow.
  eapply Rle_trans; [ | exact Hlow ].
  unfold point_to_arc_candidate_endpoints.
  assert (HA : 15 + 1/5 <= dist (arc_start warc) wP).
  { assert (Hsq : dist_sq (arc_start warc) wP = 233)
      by (unfold warc, wS, wP, dist_sq; cbn [arc_start px py]; ring).
    unfold dist. rewrite Hsq.
    rewrite <- (sqrt_Rsqr (15 + 1/5)) by lra.
    apply sqrt_le_1_alt. unfold Rsqr. lra. }
  assert (HC : 15 + 1/5 <= dist (arc_end warc) wP).
  { assert (Hsq : dist_sq (arc_end warc) wP = 425)
      by (unfold warc, wE, wP, dist_sq; cbn [arc_end px py]; ring).
    unfold dist. rewrite Hsq.
    rewrite <- (sqrt_Rsqr (15 + 1/5)) by lra.
    apply sqrt_le_1_alt. unfold Rsqr. lra. }
  destruct (Rle_dec (dist (arc_start warc) wP) (dist (arc_end warc) wP)); lra.
Qed.

(* The CORRECT tree (gate on the foot) falls back to the nearer endpoint. *)
Lemma warc_arc_dist : arc_dist warc wP = dist wP (arc_start warc).
Proof.
  unfold arc_dist.
  destruct (Rle_dec (dist (arc_center warc) wP) 0) as [Hc | _].
  { exfalso. rewrite warc_dist_OP in Hc. lra. }
  rewrite warc_foot.
  assert (Hprod : arc_side_chord warc (arc_mid warc)
                  * arc_side_chord warc (mkPoint 4 3) = -36)
    by (unfold arc_side_chord, cross_R_pt, warc, wS, wM, wE;
        cbn [arc_start arc_mid arc_end px py]; ring).
  rewrite Hprod.
  destruct (Rle_dec 0 (-36)) as [H36 | _]; [lra|].
  apply Rmin_left.
  assert (E1 : dist wP (arc_start warc) = sqrt 233).
  { unfold dist. f_equal.
    unfold warc, wS, wP, dist_sq. cbn [arc_start px py]. ring. }
  assert (E2 : dist wP (arc_end warc) = sqrt 425).
  { unfold dist. f_equal.
    unfold warc, wE, wP, dist_sq. cbn [arc_end px py]. ring. }
  rewrite E1, E2. apply sqrt_le_1_alt. lra.
Qed.

(* The refutation bundle: gate passes, naive value 15, true clearance
   > 15.2, and the correct row strictly exceeds the naive one. *)
Theorem query_side_sector_hypothesis_refuted :
  arc_interior_side warc wP
  /\ Rabs (dist (arc_center warc) wP - arc_radius warc) = 15
  /\ (forall X, on_arc warc X -> 15 + 1/5 <= dist wP X)
  /\ Rabs (dist (arc_center warc) wP - arc_radius warc) < arc_dist warc wP.
Proof.
  split; [exact warc_naive_gate|].
  split; [exact warc_naive_value|].
  split; [exact warc_no_point_within_15|].
  rewrite warc_naive_value, warc_arc_dist.
  eapply Rlt_le_trans;
    [ | apply (warc_no_point_within_15 (arc_start warc) (on_arc_start warc)) ].
  lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §6  Audit footprint (classical-reals trio only).                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions on_circle_side_zero_is_endpoint.
Print Assumptions arc_span_contains_iff_sign.
Print Assumptions arc_dist_nonneg.
Print Assumptions arc_dist_exact.
Print Assumptions empty_disk_arc_iff.
Print Assumptions query_side_sector_hypothesis_refuted.

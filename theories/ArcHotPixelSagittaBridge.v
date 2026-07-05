(* ============================================================================
   NetTopologySuite.Proofs.ArcHotPixelSagittaBridge
   ----------------------------------------------------------------------------
   Issue #64 ask: the sagitta / hot-pixel bridge for arc-overlay chord
   approximation.

   `SpectreChordArcWitness.v` proves the BARE claim "chord touches a hot
   pixel implies the arc touches it" is FALSE (a shallow arc's straight
   chord can clip a pixel the actual arc entirely misses).  This file lands
   the CORRECTLY-QUALIFIED version: a sagitta-MARGIN-dilated bridge, proved
   for `arc_minor` arcs (subtended angle <= pi -- the "Option S" regime this
   corpus's chord-sign span test is designed for).

   THE CORE GEOMETRIC FACT (`arc_point_near_chord_segment`).  For a valid,
   `arc_minor` arc, every point Y on the arc (on-circumcircle, in-span) is
   within `sagitta a` of some point of the actual chord SEGMENT
   `[arc_start a, arc_end a]` -- not just the chord LINE, and not just the
   fixed chord midpoint (`ArcChordApprox.v` §6c already showed that weaker
   Chebyshev-to-midpoint claim is false in general).  The witness parameter
   is the perpendicular-projection fraction `t = alongS(Y) / W` where `W` is
   the squared chord length and `alongS(Y)` is Y's dot-product position
   along the chord from `arc_start`.

   PROOF SKETCH (pure algebra, no new trig/atan2, reuses
   `ArcChordApprox.OM_perp_chord` / `arc_radius_sq_pythagorean` /
   `sagitta_sq_inner_eq_centerline_sq`):
     - The 2-D Lagrange identity (`along(P)^2 + perp(P)^2 = W * dist_sq(P,Base)`,
       a pure `ring` fact for any base point) applied at base `arc_center a`
       gives the circle equation for Y, and applied at base
       `chord_midpoint a` (using `OM_perp_chord`'s perpendicularity) pins
       down `Q^2 = W * d^2` where `Q := arc_side_chord a (arc_center a)` and
       `d := dist (arc_center a) (chord_midpoint a)`.
     - `arc_minor` + `arc_span_contains` (via `arc_side_chord_mid_nonzero`
       for non-degeneracy) give the sign condition `Q * perp(Y) <= 0`
       (`perp(Y) := arc_side_chord a Y`).
     - Combining these gives `alongS(Y)^2 <= (W/2)^2` unconditionally (the
       foot lands inside the segment) and, via a case split on
       `Q = sqrt(W)*d \/ Q = -sqrt(W)*d`, `perp(Y)^2 <= W * sagitta(a)^2`.
     - `dist_sq(Y, segment_point S E t) = perp(Y)^2 / W` at the specific
       `t = alongS(Y)/W` (a standard projection identity), giving the bound.

   THE HOT-PIXEL BRIDGE.  Converting the Euclidean bound to per-axis via
   `Distance.v`'s decomposition gives the curved analogue of
   `HotPixel.segment_touches_implies_bb_overlap`'s cheap pre-filter pattern:
   a sound REJECTION filter (if even the sagitta-dilated chord misses the
   pixel, the arc provably misses it too) -- the honest, margin-corrected
   replacement for the bare claim `SpectreChordArcWitness.v` refutes.

   NOT closed here (deliberately, honest scope): `ArcOverlay.v`'s
   `H_A_bridge`/`H_B_bridge` need the OPPOSITE direction (a chord-region
   point implies a nearby arc point) for the chord-approximated OVERLAY
   headline -- a different, harder gap this file does not touch (see
   `ArcOverlay.v` §7's own note, updated to point here).

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import Distance CurveGeometry ArcOrient ArcIntersect
  ArcOffsetThreePoint ArcChordApprox ArcArcCircles HotPixel ArcHotPixel.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  sagitta = arc_radius - dist(center, chord_midpoint).                   *)
(* -------------------------------------------------------------------------- *)

Lemma sagitta_eq_radius_sub_centerline :
  forall a : CircularArc,
    valid_arc a ->
    sagitta a = arc_radius a - dist (arc_center a) (chord_midpoint a).
Proof.
  intros a Hva. unfold sagitta, dist.
  rewrite (sagitta_sq_inner_eq_centerline_sq a Hva).
  rewrite <- arc_radius_eq_sqrt.
  reflexivity.
Qed.

(* Small reusable real-analysis fact: bounding |x| by a nonnegative y from
   x^2 <= y^2.  Avoids repeating an ad hoc sign case-split at each use site. *)
Lemma sq_le_sq_bound : forall x y : R, x * x <= y * y -> 0 <= y -> - y <= x <= y.
Proof.
  intros x y Hsq Hy.
  destruct (Rle_or_lt 0 (y - x)) as [H1 | H1].
  - destruct (Rle_or_lt 0 (y + x)) as [H2 | H2].
    + split; nra.
    + exfalso. nra.
  - exfalso. nra.
Qed.

(* Converse (the easy direction): a value bracketed by [-y, y] has its
   square bounded by y^2.  Used to close the sagitta bound once perpY has
   been bracketed. *)
Lemma bound_sq_of_interval : forall x y : R, - y <= x -> x <= y -> x * x <= y * y.
Proof. intros x y H1 H2. nra. Qed.

(* -------------------------------------------------------------------------- *)
(* §2  The core geometric fact: every in-span on-circle point of an          *)
(*     arc_minor arc is within sagitta of a point of the chord SEGMENT.      *)
(* -------------------------------------------------------------------------- *)

Lemma arc_point_near_chord_segment :
  forall (a : CircularArc) (Y : Point),
    valid_arc a ->
    arc_minor a ->
    inCircle_R (arc_start a) (arc_mid a) (arc_end a) Y = 0 ->
    arc_span_contains a Y ->
    exists t : R,
      0 <= t <= 1 /\
      dist_sq Y (segment_point (arc_start a) (arc_end a) t)
      <= sagitta a * sagitta a.
Proof.
  intros a Y Hva Hminor Hcirc Hspan.
  set (S := arc_start a). set (E := arc_end a). set (M := arc_mid a).
  set (O := arc_center a). set (Ch := chord_midpoint a).
  set (wx := px E - px S). set (wy := py E - py S).
  set (W := wx * wx + wy * wy).
  set (Q := arc_side_chord a O).
  set (perpY := arc_side_chord a Y).
  set (perpM := arc_side_chord a M).
  set (AY := wx * (px Y - px O) + wy * (py Y - py O)).
  (* W = dist_sq S E, and W > 0 since S <> E. *)
  assert (HW : W = dist_sq S E) by (unfold W, wx, wy, dist_sq; ring).
  assert (HWpos : 0 < W).
  { rewrite HW. unfold dist_sq.
    destruct (Req_dec (px S) (px E)) as [Hx | Hx];
    destruct (Req_dec (py S) (py E)) as [Hy | Hy]; try (nra).
    exfalso. unfold valid_arc in Hva. apply Hva.
    unfold S, E, M in *. nra. }
  (* Cyclic decomposition: arc_side_chord a P, base-S formula and the
     constant shift when moving the base point. *)
  assert (Hside : forall P : Point,
    arc_side_chord a P = wx * (py P - py S) - wy * (px P - px S)).
  { intros P. unfold arc_side_chord, cross_R_pt, wx, wy, S, E. ring. }
  assert (Hshift : forall (Base P : Point),
    wx * (py P - py S) - wy * (px P - px S)
    = (wx * (py P - py Base) - wy * (px P - px Base))
      + (wx * (py Base - py S) - wy * (px Base - px S))).
  { intros. ring. }
  (* The 2-D Lagrange identity at base Base, general P: pure ring. *)
  assert (Lagrange : forall (Base P : Point),
    (wx * (px P - px Base) + wy * (py P - py Base)) *
    (wx * (px P - px Base) + wy * (py P - py Base)) +
    (wx * (py P - py Base) - wy * (px P - px Base)) *
    (wx * (py P - py Base) - wy * (px P - px Base))
    = W * dist_sq P Base).
  { intros Base P. unfold W, wx, wy, dist_sq. ring. }
  (* Y is on the circumcircle: dist_sq O Y = arc_radius_sq a. *)
  assert (HYcirc : dist_sq O Y = arc_radius_sq a).
  { unfold O, arc_radius_sq.
    apply (inCircle_R_zero_implies_equidistant a Y Hva).
    unfold S, M, E in Hcirc. exact Hcirc. }
  set (r := arc_radius a). set (d := dist O Ch).
  assert (Hr2 : arc_radius_sq a = r * r).
  { unfold r, arc_radius_sq, arc_radius, O, dist.
    rewrite sqrt_sqrt; [reflexivity | apply dist_sq_nonneg]. }
  (* Circle equation for Y, at base O: AY^2 + (perpY - Q)^2 = W * r^2. *)
  assert (HpQ : perpY - Q = wx * (py Y - py O) - wy * (px Y - px O)).
  { unfold perpY, Q. rewrite (Hside Y), (Hside O), (Hshift O Y). ring. }
  assert (Hcircle_eq : AY * AY + (perpY - Q) * (perpY - Q) = W * (r * r)).
  { rewrite <- Hr2, <- HYcirc, (dist_sq_sym O Y), <- (Lagrange O Y).
    unfold AY. rewrite HpQ. reflexivity. }
  (* Q^2 = W * d^2, via OM_perp_chord (base-Ch along-component of O is 0). *)
  assert (Hd2 : d * d = dist_sq O Ch)
    by (unfold d, dist; apply sqrt_sqrt; apply dist_sq_nonneg).
  assert (HalongChO : wx * (px O - px Ch) + wy * (py O - py Ch) = 0).
  { pose proof (OM_perp_chord a Hva) as Hperp.
    cbv zeta in Hperp.
    unfold wx, wy, O, Ch, S, E. nra. }
  assert (HQval : wx * (py O - py Ch) - wy * (px O - px Ch) = Q).
  { unfold Q. rewrite (Hside O), (Hshift Ch O).
    assert (Hz : wx * (py Ch - py S) - wy * (px Ch - px S) = 0).
    { unfold wx, wy, Ch, chord_midpoint, S, E. cbn [px py]. field. }
    nra. }
  assert (HQsq : Q * Q = W * (d * d)).
  { rewrite Hd2, <- (Lagrange Ch O), HalongChO, HQval. ring. }
  (* Non-degeneracy and the sign condition Q * perpY <= 0. *)
  assert (HpM_ne : perpM <> 0)
    by (unfold perpM, M; apply arc_side_chord_mid_nonzero; exact Hva).
  assert (HQraw : Q = arc_side_chord a (arc_center a)) by (unfold Q, O; reflexivity).
  assert (HpMraw : perpM = arc_side_chord a (arc_mid a)) by (unfold perpM, M; reflexivity).
  assert (HC : Q * perpY <= 0).
  { unfold arc_span_contains in Hspan.
    destruct Hspan as [Hint | [Heq | Heq]].
    - unfold arc_interior_side in Hint.
      unfold arc_minor in Hminor.
      rewrite <- HpMraw in Hint, Hminor.
      rewrite <- HQraw in Hminor.
      fold perpY in Hint.
      destruct (Rtotal_order perpM 0) as [HpM | [HpM | HpM]].
      + nra.
      + exfalso. apply HpM_ne. exact HpM.
      + nra.
    - unfold perpY. rewrite Heq. rewrite (Hside (arc_start a)). unfold wx, wy, S, E. nra.
    - unfold perpY. rewrite Heq. rewrite (Hside (arc_end a)). unfold wx, wy, S, E. nra.
  }
  (* Foot-in-segment bound: AY^2 <= (W/2)^2, unconditionally. *)
  assert (Hpyth : r * r = d * d + chord_half_length_sq a).
  { rewrite <- Hr2, Hd2. unfold r, d, O, Ch. apply arc_radius_sq_pythagorean. exact Hva. }
  assert (Hl2 : chord_half_length_sq a = W / 4)
    by (unfold chord_half_length_sq; rewrite HW; reflexivity).
  assert (Hkey1 : Q * Q <= (perpY - Q) * (perpY - Q)).
  { assert (Hh : 0 <= perpY * (perpY - 2 * Q)) by nra. nra. }
  assert (HAYbound : AY * AY <= (W / 2) * (W / 2)).
  { assert (Hstep : AY * AY <= W * (r * r) - Q * Q) by nra.
    nra. }
  (* Perpendicular-distance bound: perpY^2 <= W * sagitta^2. *)
  assert (Hdnn : 0 <= d) by (unfold d; apply dist_nonneg).
  assert (Hrpos : 0 < r) by (unfold r; apply arc_radius_pos; exact Hva).
  assert (Hsagitta : sagitta a = r - d)
    by (unfold r, d, O, Ch; apply sagitta_eq_radius_sub_centerline; exact Hva).
  set (n := sqrt W).
  assert (Hnnn : 0 <= n) by (unfold n; apply sqrt_pos).
  assert (Hnpos : 0 < n) by (unfold n; apply sqrt_lt_R0; lra).
  assert (Hnn : n * n = W) by (unfold n; apply sqrt_sqrt; lra).
  assert (HQfactor : (Q - n * d) * (Q + n * d) = 0).
  { assert (Hexp : (Q - n * d) * (Q + n * d) = Q * Q - n * n * (d * d)) by ring.
    rewrite Hexp, Hnn, HQsq. ring. }
  assert (Hchsnn := chord_half_length_sq_nonneg a).
  assert (Hddrr : d * d <= r * r) by nra.
  destruct (sq_le_sq_bound d r Hddrr (Rlt_le 0 r Hrpos)) as [_ Hrled].
  assert (HperpYbound : perpY * perpY <= W * (sagitta a * sagitta a)).
  { rewrite Hsagitta.
    assert (Hnrnn : 0 <= n * r) by nra.
    assert (Hb0 : (perpY - Q) * (perpY - Q) <= (n * r) * (n * r)) by nra.
    destruct (sq_le_sq_bound (perpY - Q) (n * r) Hb0 Hnrnn) as [Hlo Hhi].
    destruct (Rmult_integral _ _ HQfactor) as [HQeq | HQeq].
    - assert (HQ : Q = n * d) by lra.
      assert (HlowFinal : - (n * (r - d)) <= perpY) by nra.
      assert (HupFinal : perpY <= n * (r - d)).
      { destruct (Rle_lt_or_eq_dec 0 d Hdnn) as [Hdpos | Hd0].
        - assert (Hqpos : 0 < Q) by nra.
          assert (HpYnp : perpY <= 0) by nra. nra.
        - nra. }
      pose proof (bound_sq_of_interval perpY (n * (r - d)) HlowFinal HupFinal) as Hb.
      nra.
    - assert (HQ : Q = - (n * d)) by lra.
      assert (HupFinal : perpY <= n * (r - d)) by nra.
      assert (HlowFinal : - (n * (r - d)) <= perpY).
      { destruct (Rle_lt_or_eq_dec 0 d Hdnn) as [Hdpos | Hd0].
        - assert (Hqneg : Q < 0) by nra.
          assert (HpYnn : 0 <= perpY) by nra. nra.
        - nra. }
      pose proof (bound_sq_of_interval perpY (n * (r - d)) HlowFinal HupFinal) as Hb.
      nra.
  }
  (* Assemble the witness t = alongS(Y) / W. *)
  assert (Hne : W <> 0) by lra.
  set (alongSY := wx * (px Y - px S) + wy * (py Y - py S)).
  assert (HalongSY : alongSY = AY + W / 2).
  { unfold alongSY, AY.
    assert (HalongSO : wx * (px O - px S) + wy * (py O - py S) = W / 2).
    { assert (Hstep : wx * (px O - px S) + wy * (py O - py S)
                      = (wx * (px O - px Ch) + wy * (py O - py Ch))
                        + (wx * (px Ch - px S) + wy * (py Ch - py S)))
        by ring.
      rewrite Hstep.
      assert (HalongChO2 : wx * (px O - px Ch) + wy * (py O - py Ch) = 0)
        by exact HalongChO.
      rewrite HalongChO2.
      unfold Ch, chord_midpoint, S, E, wx, wy, W.
      unfold S, E, wx, wy, W.
      unfold S, E.
      cbn [px py]. field. }
    lra. }
  (* The key polynomial identity: with Nx, Ny the numerators of Y's offset
     from the foot (scaled by W), Nx = -wy*perpY and Ny = wx*perpY exactly,
     so Nx^2 + Ny^2 = W * perpY^2 -- pure `ring`, no case split. *)
  set (Nx := W * (px Y - px S) - alongSY * wx).
  set (Ny := W * (py Y - py S) - alongSY * wy).
  assert (HNsq : Nx * Nx + Ny * Ny = W * (perpY * perpY)).
  { unfold Nx, Ny, alongSY, W.
    unfold perpY. rewrite (Hside Y). ring. }
  assert (Hseg_eq : segment_point S E (alongSY / W)
                     = mkPoint (px S + (alongSY/W) * wx) (py S + (alongSY/W) * wy)).
  { unfold segment_point, wx, wy. f_equal; ring. }
  exists (alongSY / W).
  split.
  - split.
    + assert (Hb : - (W/2) <= AY) by nra.
      unfold Rdiv. apply Rmult_le_pos.
      * lra.
      * left. apply Rinv_0_lt_compat. lra.
    + assert (Hb : AY <= W/2) by nra.
      apply (Rmult_le_reg_r W); [lra |].
      unfold Rdiv. rewrite Rmult_assoc, Rinv_l; [lra | lra].
  - assert (Hdseq : dist_sq Y (segment_point S E (alongSY / W)) = perpY * perpY / W).
    { rewrite Hseg_eq. unfold dist_sq. cbn [px py].
      replace (px Y - (px S + alongSY / W * wx)) with (Nx / W)
        by (unfold Nx; field; exact Hne).
      replace (py Y - (py S + alongSY / W * wy)) with (Ny / W)
        by (unfold Ny; field; exact Hne).
      replace (Nx / W * (Nx / W) + Ny / W * (Ny / W))
        with ((Nx * Nx + Ny * Ny) / (W * W)) by (field; exact Hne).
      rewrite HNsq. field. exact Hne. }
    rewrite Hdseq.
    unfold Rdiv.
    apply (Rmult_le_reg_r W); [lra |].
    rewrite Rmult_assoc, Rinv_l; [| lra]. rewrite Rmult_1_r.
    lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Margin-dilated hot-pixel predicates.                                   *)
(* -------------------------------------------------------------------------- *)

Definition in_hot_pixel_margin (P C : Point) (scale marg : R) : Prop :=
  px C - (hot_pixel_radius scale + marg) <= px P < px C + (hot_pixel_radius scale + marg) /\
  py C - (hot_pixel_radius scale + marg) <= py P < py C + (hot_pixel_radius scale + marg).

Definition segment_touches_hot_pixel_margin (P Q C : Point) (scale marg : R) : Prop :=
  exists t : R, 0 <= t <= 1 /\ in_hot_pixel_margin (segment_point P Q t) C scale marg.

(* -------------------------------------------------------------------------- *)
(* §4  Tier 0: chord-endpoint touching is already unconditional (no sagitta   *)
(*     needed) -- isolates the slice `SpectreChordArcWitness.v` never        *)
(*     actually refuted.                                                     *)
(* -------------------------------------------------------------------------- *)

Corollary chord_endpoint_touches_implies_arc_touches :
  forall (a : CircularArc) (C : Point) (scale : R),
    in_hot_pixel (arc_start a) C scale \/ in_hot_pixel (arc_end a) C scale ->
    arc_touches_hot_pixel a C scale.
Proof.
  intros a C scale [Hs | He].
  - apply (arc_passes_through_hot_pixel_start_touches a C scale Hs).
  - apply (arc_passes_through_hot_pixel_end_touches a C scale He).
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  The headline bridge: arc touches the pixel ⟹ the chord touches the    *)
(*     sagitta-dilated pixel.  Sound rejection filter, its contrapositive.   *)
(* -------------------------------------------------------------------------- *)

Theorem arc_touches_implies_chord_touches_margin :
  forall (a : CircularArc) (C : Point) (scale : R),
    valid_arc a ->
    arc_minor a ->
    arc_touches_hot_pixel a C scale ->
    segment_touches_hot_pixel_margin (arc_start a) (arc_end a) C scale (sagitta a).
Proof.
  intros a C scale Hva Hminor [Y [HinY [Hcirc Hspan]]].
  destruct (arc_point_near_chord_segment a Y Hva Hminor Hcirc Hspan)
    as [t [Ht Hdist]].
  exists t. split; [exact Ht |].
  unfold in_hot_pixel_margin.
  unfold in_hot_pixel in HinY.
  destruct HinY as [[Hx1 Hx2] [Hy1 Hy2]].
  set (F := segment_point (arc_start a) (arc_end a) t).
  assert (Hsagnn := sagitta_nonneg a).
  unfold dist_sq in Hdist.
  fold F in Hdist.
  assert (Hxnn := sqr_nonneg (px Y - px F)).
  assert (Hynn := sqr_nonneg (py Y - py F)).
  assert (Hax : (px Y - px F) * (px Y - px F) <= sagitta a * sagitta a) by lra.
  assert (Hay : (py Y - py F) * (py Y - py F) <= sagitta a * sagitta a) by lra.
  destruct (sq_le_sq_bound (px Y - px F) (sagitta a) Hax Hsagnn) as [Hxlo Hxhi].
  destruct (sq_le_sq_bound (py Y - py F) (sagitta a) Hay Hsagnn) as [Hylo Hyhi].
  split; lra.
Qed.

(* Contrapositive form: the useful REJECTION filter for a candidate overlay
   pipeline -- if the sagitta-dilated chord misses the pixel, the arc
   provably misses it too, with zero false negatives. *)
Corollary chord_misses_margin_implies_arc_misses :
  forall (a : CircularArc) (C : Point) (scale : R),
    valid_arc a ->
    arc_minor a ->
    ~ segment_touches_hot_pixel_margin (arc_start a) (arc_end a) C scale (sagitta a) ->
    ~ arc_touches_hot_pixel a C scale.
Proof.
  intros a C scale Hva Hminor Hmiss Htouch.
  apply Hmiss.
  apply (arc_touches_implies_chord_touches_margin a C scale Hva Hminor Htouch).
Qed.

(* -------------------------------------------------------------------------- *)
(* §6  Audit footprint.                                                       *)
(* -------------------------------------------------------------------------- *)

Print Assumptions sagitta_eq_radius_sub_centerline.
Print Assumptions arc_point_near_chord_segment.
Print Assumptions chord_endpoint_touches_implies_arc_touches.
Print Assumptions arc_touches_implies_chord_touches_margin.
Print Assumptions chord_misses_margin_implies_arc_misses.

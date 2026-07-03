(* ==========================================================================
   HandoffWedge.v

   [H-bridge attack, C-3e step 2] The WEDGE CERTIFICATION for the
   corner<->corridor handoff: the chord from a corner sample to the
   adjacent corridor end hugs ONE sector wall, and every point of it is
   `in_open_sector`-certified -- so by `FanCorner.sector_point_off_edge_
   in`/`_out` the handoff avoids the OTHER incident ring edge at the
   vertex (the dart itself and its twin are already dead by the C-3e
   step-1 side kit; everything non-incident falls to the clearance
   ball in step 3).

   Two ingredient families, both linear:

     - `sector_chord_certified_wall1`/`_wall2`: if both chord endpoints
       carry the near-wall cross certificate, every chord point does
       (the cross is affine along the chord); in a REFLEX gap that
       alone is the certificate, in a CONVEX gap the far-wall cross is
       demanded at the endpoints and transports the same way.
     - the corridor-end OFFSET DECOMPOSITIONS: at a vertex ON the
       carrier, the vertex-relative offset of a corridor point is an
       along-carrier component plus the horizontal offset
       (`corridor_offset_tip`/`_base` and the east mirrors), whence the
       four near-wall certificates `corridor_end_cert_*`: at the TIP of
       a descending dart the west corridor end is strictly CCW of the
       reversal wall, at its BASE strictly CW of the dart wall -- and
       the ascending/east mirrors.  The along-carrier component is
       invisible to the wall cross (`vcross_self`), so the certificates
       are the explicit values `delta * |py-span component|`.

   No `Admitted` / `Axiom` / `Parameter`; allowlist axioms only.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
   ========================================================================== *)

From Stdlib Require Import Reals Lra List.
From NTS.Proofs Require Import Distance Overlay OverlayGraph Vec Azimuth
                               Direction Dart DartAngularOrder
                               PointInRingTangents JordanCurveSeam
                               JCTHugStep RingClearance SectorPath
                               CornerSamples CornerConnector
                               JCTCorridor StraddleSides MirrorCorridor
                               DartSideKit.

Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  Wall-hugging chords are sector-certified.                               *)
(* -------------------------------------------------------------------------- *)

Lemma sector_chord_certified_wall1 :
  forall (u1 u2 A B : Vec) (t : R),
    0 < vcross u1 A -> 0 < vcross u1 B ->
    (vcross u1 u2 < 0 \/
     (0 < vcross u1 u2 /\ 0 < vcross A u2 /\ 0 < vcross B u2)) ->
    0 <= t <= 1 ->
    in_open_sector u1 u2 (vaffine t A B).
Proof.
  intros u1 u2 A B t HA HB Hgap Ht.
  assert (Hw1 : 0 < vcross u1 (vaffine t A B))
    by (rewrite vcross_affine_r; nra).
  destruct Hgap as [Hneg | [Hpos [HA2 HB2]]].
  - right. split; [ exact Hneg | left; exact Hw1 ].
  - left. split; [ exact Hpos | split; [ exact Hw1 | ] ].
    rewrite vcross_affine_l. nra.
Qed.

Lemma sector_chord_certified_wall2 :
  forall (u1 u2 A B : Vec) (t : R),
    0 < vcross A u2 -> 0 < vcross B u2 ->
    (vcross u1 u2 < 0 \/
     (0 < vcross u1 u2 /\ 0 < vcross u1 A /\ 0 < vcross u1 B)) ->
    0 <= t <= 1 ->
    in_open_sector u1 u2 (vaffine t A B).
Proof.
  intros u1 u2 A B t HA HB Hgap Ht.
  assert (Hw2 : 0 < vcross (vaffine t A B) u2)
    by (rewrite vcross_affine_l; nra).
  destruct Hgap as [Hneg | [Hpos [HA1 HB1]]].
  - right. split; [ exact Hneg | right; exact Hw2 ].
  - left. split; [ exact Hpos | split; [ | exact Hw2 ] ].
    rewrite vcross_affine_r. nra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  Corridor ends as vertex-relative offsets.                               *)
(* -------------------------------------------------------------------------- *)

(* Reassembling a point from its vertex-relative offset. *)
Lemma point_at_diff :
  forall (p q : Point), point_at q (point_diff p q) = p.
Proof.
  intros [px1 py1] [qx qy].
  unfold point_at, point_diff. cbn. f_equal; ring.
Qed.

(* At the TIP (which is ON the carrier), a west-corridor point decomposes
   as along-the-reversal plus the westward offset. *)
Lemma corridor_offset_tip :
  forall (x : Dart) (delta y : R),
    py (fst x) <> py (snd x) ->
    point_diff (corridor x delta y) (dtip x)
      = vadd (vscale ((y - py (dtip x)) / (py (dbase x) - py (dtip x)))
                     (ddir (twin x)))
             (vscale delta (mkVec (-1) 0)).
Proof.
  intros [a b] delta y Hnh. cbn [fst snd] in Hnh.
  unfold corridor, point_diff, ddir, twin, dtip, dbase, edge_x_at,
         vadd, vscale.
  cbn. f_equal; field; lra.
Qed.

Lemma corridor_offset_base :
  forall (x : Dart) (delta y : R),
    py (fst x) <> py (snd x) ->
    point_diff (corridor x delta y) (dbase x)
      = vadd (vscale ((y - py (dbase x)) / (py (dtip x) - py (dbase x)))
                     (ddir x))
             (vscale delta (mkVec (-1) 0)).
Proof.
  intros [a b] delta y Hnh. cbn [fst snd] in Hnh.
  unfold corridor, point_diff, ddir, twin, dtip, dbase, edge_x_at,
         vadd, vscale.
  cbn. f_equal; field; lra.
Qed.

Lemma corridor_east_offset_tip :
  forall (x : Dart) (delta y : R),
    py (fst x) <> py (snd x) ->
    point_diff (corridor_east x delta y) (dtip x)
      = vadd (vscale ((y - py (dtip x)) / (py (dbase x) - py (dtip x)))
                     (ddir (twin x)))
             (vscale delta (mkVec 1 0)).
Proof.
  intros [a b] delta y Hnh. cbn [fst snd] in Hnh.
  unfold corridor_east, point_diff, ddir, twin, dtip, dbase, edge_x_at,
         vadd, vscale.
  cbn. f_equal; field; lra.
Qed.

Lemma corridor_east_offset_base :
  forall (x : Dart) (delta y : R),
    py (fst x) <> py (snd x) ->
    point_diff (corridor_east x delta y) (dbase x)
      = vadd (vscale ((y - py (dbase x)) / (py (dtip x) - py (dbase x)))
                     (ddir x))
             (vscale delta (mkVec 1 0)).
Proof.
  intros [a b] delta y Hnh. cbn [fst snd] in Hnh.
  unfold corridor_east, point_diff, ddir, twin, dtip, dbase, edge_x_at,
         vadd, vscale.
  cbn. f_equal; field; lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  The four near-wall certificates for corridor ends.                      *)
(* -------------------------------------------------------------------------- *)

(* DESCENDING dart, west corridor, TIP corner: the corridor end is
   strictly CCW of the arriving reversal wall `ddir (twin x)`. *)
Lemma corridor_end_cert_tip_west :
  forall (x : Dart) (delta y : R),
    py (dtip x) < py (dbase x) -> 0 < delta ->
    0 < vcross (ddir (twin x)) (point_diff (corridor x delta y) (dtip x)).
Proof.
  intros x delta y Hdesc Hd.
  assert (Hnh : py (fst x) <> py (snd x))
    by (unfold dtip, dbase in Hdesc; lra).
  rewrite (corridor_offset_tip x delta y Hnh).
  rewrite vcross_add_r, !vcross_scale_r, vcross_self.
  destruct x as [a b].
  unfold ddir, twin, point_diff, dtip, dbase, vcross in *. cbn in *.
  nra.
Qed.

(* DESCENDING dart, west corridor, BASE corner: the corridor end is
   strictly CW of the departing wall `ddir x`. *)
Lemma corridor_end_cert_base_west :
  forall (x : Dart) (delta y : R),
    py (dtip x) < py (dbase x) -> 0 < delta ->
    0 < vcross (point_diff (corridor x delta y) (dbase x)) (ddir x).
Proof.
  intros x delta y Hdesc Hd.
  assert (Hnh : py (fst x) <> py (snd x))
    by (unfold dtip, dbase in Hdesc; lra).
  rewrite (corridor_offset_base x delta y Hnh).
  rewrite vcross_add_l, !vcross_scale_l, vcross_self.
  destruct x as [a b].
  unfold ddir, point_diff, dtip, dbase, vcross in *. cbn in *.
  nra.
Qed.

(* ASCENDING dart, east corridor, TIP corner. *)
Lemma corridor_end_cert_tip_east :
  forall (x : Dart) (delta y : R),
    py (dbase x) < py (dtip x) -> 0 < delta ->
    0 < vcross (ddir (twin x))
               (point_diff (corridor_east x delta y) (dtip x)).
Proof.
  intros x delta y Hasc Hd.
  assert (Hnh : py (fst x) <> py (snd x))
    by (unfold dtip, dbase in Hasc; lra).
  rewrite (corridor_east_offset_tip x delta y Hnh).
  rewrite vcross_add_r, !vcross_scale_r, vcross_self.
  destruct x as [a b].
  unfold ddir, twin, point_diff, dtip, dbase, vcross in *. cbn in *.
  nra.
Qed.

(* ASCENDING dart, east corridor, BASE corner. *)
Lemma corridor_end_cert_base_east :
  forall (x : Dart) (delta y : R),
    py (dbase x) < py (dtip x) -> 0 < delta ->
    0 < vcross (point_diff (corridor_east x delta y) (dbase x)) (ddir x).
Proof.
  intros x delta y Hasc Hd.
  assert (Hnh : py (fst x) <> py (snd x))
    by (unfold dtip, dbase in Hasc; lra).
  rewrite (corridor_east_offset_base x delta y Hnh).
  rewrite vcross_add_l, !vcross_scale_l, vcross_self.
  destruct x as [a b].
  unfold ddir, point_diff, dtip, dbase, vcross in *. cbn in *.
  nra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Axiom audit.  Pure Vec/R algebra; allowlist axioms only.                    *)
(* -------------------------------------------------------------------------- *)

Print Assumptions sector_chord_certified_wall1.
Print Assumptions corridor_offset_tip.
Print Assumptions corridor_end_cert_base_east.

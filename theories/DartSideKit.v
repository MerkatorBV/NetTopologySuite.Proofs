(* ==========================================================================
   DartSideKit.v

   [H-bridge attack, C-3e step 1] The SIDE KIT for the corner<->corridor
   handoff: every connector piece the along-dart transport uses sits
   strictly on the FACE side (the right) of the walk dart, and a chord
   between two same-side points stays on that side -- so it can never
   meet the dart's own edge or its twin (both live on the carrier, where
   the side form vanishes).

   Contents, all pure coordinate algebra on C-2's `dart_side`:

     - `dart_side_at_base`/`_at_tip`: vertex-relative offsets read the
       side form as a single `vcross` against `ddir` (the tip version
       eats the along-carrier shift);
     - `corner_sample_out_base_side` / `corner_sample_in_tip_side`: the
       two corner samples that C-3b/C-3d park at a dart's endpoints are
       strictly right of the dart (their perpendicular component is the
       RIGHT perp, `vneg (vperpL u)` resp. `vperpL (vneg u)`);
     - `corridor_west_side` / `corridor_east_side`: the corridor points
       carry side value -/+ (py tip - py base) * delta, so the WEST
       corridor is right of a DESCENDING dart and the EAST corridor is
       right of an ASCENDING one (`corridor_right_of_descending`,
       `corridor_east_right_of_ascending`) -- the machine-checked
       face-on-the-right convention meets the corridor stack;
     - `dart_side_chord`: the side form is affine along chords, so
       `chord_right_side` keeps every chord point strictly right, and
       `chord_right_off_dart_edges` concludes: the chord meets neither
       the dart's edge nor its twin (`on_edge_dart_side`,
       `on_edge_twin_dart_side`: on-edge points have side 0).

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
                               JCTCorridor StraddleSides MirrorCorridor.

Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  Reading the side form at a dart's endpoints.                            *)
(* -------------------------------------------------------------------------- *)

Lemma dart_side_at_base :
  forall (x : Dart) (w : Vec),
    dart_side x (point_at (dbase x) w) = vcross (ddir x) w.
Proof.
  intros [a b] [wx wy].
  unfold dart_side, turn_sign, point_at, point_diff, ddir, dtip, dbase,
         vcross.
  cbn. ring.
Qed.

(* The along-carrier shift from base to tip is invisible to the side form. *)
Lemma dart_side_at_tip :
  forall (x : Dart) (w : Vec),
    dart_side x (point_at (dtip x) w) = vcross (ddir x) w.
Proof.
  intros [a b] [wx wy].
  unfold dart_side, turn_sign, point_at, point_diff, ddir, dtip, dbase,
         vcross.
  cbn. ring.
Qed.

Lemma ddir_twin : forall d : Dart, ddir (twin d) = vneg (ddir d).
Proof.
  intros [a b].
  unfold ddir, twin, point_diff, vneg, dtip, dbase. cbn.
  f_equal; ring.
Qed.

Lemma vperpL_neg : forall u : Vec, vperpL (vneg u) = vneg (vperpL u).
Proof.
  intros [ux uy]. unfold vperpL, vneg. cbn. f_equal; ring.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  The corner samples at a dart's two ends are strictly on its right.      *)
(* -------------------------------------------------------------------------- *)

(* The departing sample at the BASE (the corner connector's exit along x). *)
Lemma corner_sample_out_base_side :
  forall (x : Dart) (rho delta : R),
    ddir x <> vzero -> 0 < delta ->
    right_of_dart x (point_at (dbase x) (corner_sample_out (ddir x) rho delta)).
Proof.
  intros x rho delta Hu Hd.
  unfold right_of_dart.
  rewrite dart_side_at_base.
  pose proof (vperpL_cross_pos (ddir x) Hu) as Hpos.
  unfold corner_sample_out.
  rewrite vcross_add_r, !vcross_scale_r, vcross_self, vcross_neg_r.
  nra.
Qed.

(* The arriving sample at the TIP (the next corner connector's entry:
   its wall is the REVERSAL of x, so the sample offset is
   `corner_sample_in (ddir (twin x))`). *)
Lemma corner_sample_in_tip_side :
  forall (x : Dart) (rho delta : R),
    ddir x <> vzero -> 0 < delta ->
    right_of_dart x
      (point_at (dtip x) (corner_sample_in (ddir (twin x)) rho delta)).
Proof.
  intros x rho delta Hu Hd.
  unfold right_of_dart.
  rewrite dart_side_at_tip.
  pose proof (vperpL_cross_pos (ddir x) Hu) as Hpos.
  rewrite ddir_twin.
  unfold corner_sample_in.
  rewrite vperpL_neg.
  rewrite vcross_add_r, !vcross_scale_r, !vcross_neg_r, vcross_self.
  nra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  The corridors' side values, and the face-side classification.           *)
(* -------------------------------------------------------------------------- *)

Lemma corridor_west_side :
  forall (x : Dart) (delta y : R),
    py (fst x) <> py (snd x) ->
    dart_side x (corridor x delta y) = (py (snd x) - py (fst x)) * delta.
Proof.
  intros [a b] delta y Hnh. cbn [fst snd] in Hnh.
  pose proof (edge_x_at_zero_line a b y Hnh) as Hzero.
  destruct (dart_side_straddle a b y (edge_x_at (a, b) y) delta Hzero)
    as [HW _].
  unfold corridor. cbn [fst snd].
  exact HW.
Qed.

Lemma corridor_east_side :
  forall (x : Dart) (delta y : R),
    py (fst x) <> py (snd x) ->
    dart_side x (corridor_east x delta y)
      = - ((py (snd x) - py (fst x)) * delta).
Proof.
  intros [a b] delta y Hnh. cbn [fst snd] in Hnh.
  pose proof (edge_x_at_zero_line a b y Hnh) as Hzero.
  destruct (dart_side_straddle a b y (edge_x_at (a, b) y) delta Hzero)
    as [_ HE].
  unfold corridor_east. cbn [fst snd].
  exact HE.
Qed.

(* Face on the right: a DESCENDING dart's face side is WEST... *)
Corollary corridor_right_of_descending :
  forall (x : Dart) (delta y : R),
    py (snd x) < py (fst x) -> 0 < delta ->
    right_of_dart x (corridor x delta y).
Proof.
  intros x delta y Hdesc Hd.
  unfold right_of_dart.
  rewrite corridor_west_side by lra.
  nra.
Qed.

(* ... and an ASCENDING dart's face side is EAST. *)
Corollary corridor_east_right_of_ascending :
  forall (x : Dart) (delta y : R),
    py (fst x) < py (snd x) -> 0 < delta ->
    right_of_dart x (corridor_east x delta y).
Proof.
  intros x delta y Hasc Hd.
  unfold right_of_dart.
  rewrite corridor_east_side by lra.
  nra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Chords preserve the side; same-side chords miss the dart's edges.       *)
(* -------------------------------------------------------------------------- *)

Lemma dart_side_chord :
  forall (x : Dart) (A B : Point) (t : R),
    dart_side x (mkPoint ((1 - t) * px A + t * px B)
                         ((1 - t) * py A + t * py B))
      = (1 - t) * dart_side x A + t * dart_side x B.
Proof.
  intros [a b] A B t.
  unfold dart_side, turn_sign, vcross, point_diff, dtip, dbase.
  cbn. ring.
Qed.

Lemma chord_right_side :
  forall (x : Dart) (A B : Point) (t : R),
    right_of_dart x A -> right_of_dart x B ->
    0 <= t <= 1 ->
    right_of_dart x (mkPoint ((1 - t) * px A + t * px B)
                             ((1 - t) * py A + t * py B)).
Proof.
  intros x A B t HA HB Ht.
  unfold right_of_dart in *.
  rewrite dart_side_chord.
  nra.
Qed.

(* On-edge points sit ON the carrier: the side form vanishes. *)
Lemma on_edge_dart_side :
  forall (x : Dart) (q : Point),
    on_edge x q -> dart_side x q = 0.
Proof.
  intros [a b] q [s [Hs [Hx Hy]]].
  cbn [fst snd] in Hx, Hy.
  unfold dart_side, turn_sign, vcross, point_diff, dtip, dbase.
  cbn. rewrite Hx, Hy. ring.
Qed.

Lemma on_edge_twin_dart_side :
  forall (x : Dart) (q : Point),
    on_edge (twin x) q -> dart_side x q = 0.
Proof.
  intros [a b] q [s [Hs [Hx Hy]]].
  unfold twin in Hx, Hy. cbn [fst snd] in Hx, Hy.
  unfold dart_side, turn_sign, vcross, point_diff, dtip, dbase.
  cbn. rewrite Hx, Hy. ring.
Qed.

(* The headline: a same-side chord never meets the dart's edge or its
   twin -- the along-dart handoff chords are automatically clear of the
   carrier pair, leaving only the OTHER ring edges to the clearance
   ball and the sector certificates. *)
Theorem chord_right_off_dart_edges :
  forall (x : Dart) (A B : Point) (t : R),
    right_of_dart x A -> right_of_dart x B ->
    0 <= t <= 1 ->
    ~ on_edge x (mkPoint ((1 - t) * px A + t * px B)
                         ((1 - t) * py A + t * py B)) /\
    ~ on_edge (twin x) (mkPoint ((1 - t) * px A + t * px B)
                                ((1 - t) * py A + t * py B)).
Proof.
  intros x A B t HA HB Ht.
  pose proof (chord_right_side x A B t HA HB Ht) as Hside.
  unfold right_of_dart in Hside.
  split; intro Hon.
  - rewrite (on_edge_dart_side x _ Hon) in Hside. lra.
  - rewrite (on_edge_twin_dart_side x _ Hon) in Hside. lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Axiom audit.  Pure coordinate algebra; allowlist axioms only.               *)
(* -------------------------------------------------------------------------- *)

Print Assumptions corner_sample_in_tip_side.
Print Assumptions corridor_right_of_descending.
Print Assumptions chord_right_off_dart_edges.

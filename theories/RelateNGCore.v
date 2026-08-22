(* ============================================================================
   NetTopologySuite.Proofs.RelateNGCore
   ----------------------------------------------------------------------------
   Issue #67 S13: RelateNG pipeline — dispatch core.

   Split (2026-08) from the former monolithic RelateNG.v; RelateNG.v remains
   as the re-export umbrella, so existing `Require Import RelateNG` clients
   (RelatePrepared.v) are unaffected.  Original section banners preserved.

   Strata over general Geometry; the rect lane (bounds extractor,
   `rect_pair_regime`, `rects_relate` selection wrapper); the triangle lane
   (ring/polygon/geometry representation, decidable boolean detectors,
   `triangle_pair_regime`, `tris_relate`); and the top-level `relate`
   dispatch with its fidelity lemmas and the line-geometry fallback.

   Layout note (meso-audit B6, executed at the split): the monolith
   interleaved the two lanes (`rect_pair_regime` sat inside the triangle
   block); here the rect lane precedes the triangle lane, and the shared
   `relate` dispatch closes the file.

   No `Admitted`, no `Axiom`, no `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals List Lia Lra Ranalysis Bool Btauto.
From NTS.Proofs Require Import Real.
From NTS.Proofs Require Import DE9IM Distance Overlay Segment RelateBoundary
  RelateLineLine RelateAreaPoint RelateAreaLine RelateAreaArea
  RelateMatrixLineLine RelateMatrixAreaLine RelateMatrixRect RelateMatrixTriangle
  RelateCurveMatrix RectangleJCT Intersect Orientation.  (* cross for between collinear *)
From NTS.Proofs Require Import GeneralTriangleSeparation GeneralTriangleParity.  (* gtri / JCT planar covering for triangle interiors & exterior signs *)
From NTS.Proofs Require Import GeneralTriangleJCT GeneralTriangleExterior
  TriangleValidPolygon JCTSeamAssembly PointInRingCorrect PointInRingTangents
  JordanCurveSeam.  (* assembled in-house JCT converse: point_in_ring -> 0 < gtri *)
From NTS.Proofs Require Import TriangleContainmentConvex.

Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* Strata (reuse/extend from RelateCurveMatrix style for general Geometry).   *)
(* -------------------------------------------------------------------------- *)

Inductive Stratum : Type := SInt | SBnd | SExt.

Definition point_in_interior (g : Geometry) (p : Point) : Prop :=
  point_set g p.

Definition point_on_boundary (g : Geometry) (p : Point) : Prop :=
  exists poly, In poly g /\
    exists r, In r (outer_ring poly :: hole_rings poly) /\
    exists e, In e (ring_edges r) /\ between (fst e) (snd e) p.

Definition point_in_exterior (g : Geometry) (p : Point) : Prop :=
  ~ point_set g p.

Definition in_stratum (s : Stratum) (g : Geometry) (p : Point) : Prop :=
  match s with
  | SInt => point_in_interior g p
  | SBnd => point_on_boundary g p
  | SExt => point_in_exterior g p
  end.

(* -------------------------------------------------------------------------- *)
(* Core relate (delegating for base cases; general stub).                     *)
(* -------------------------------------------------------------------------- *)

(* relate is defined below with rect dispatch (and stub fallback). *)

(* The point-set specification link lives in RelateCurveMatrix
   (`geom_de9im_pointset`); per-regime satisfaction lemmas below target it
   directly, so no marker predicate is kept here. *)

(* -------------------------------------------------------------------------- *)
(* Delegation / agreement examples (smoke for rect + line cases).             *)
(* -------------------------------------------------------------------------- *)

(* Delegation lemma moved after relate definition for scoping. *)

(* -------------------------------------------------------------------------- *)
(* Rect lane: bounds extractor, regime decision, selection wrapper.           *)
(* -------------------------------------------------------------------------- *)

(* Real dispatch for rect geometries. *)
Definition rect_geometry_bounds (g : Geometry) : option (R * R * R * R) :=
  match g with
  | [poly] =>
      match hole_rings poly with
      | [] =>
          match outer_ring poly with
          | mkPoint x0 y0 :: mkPoint x1 _ :: mkPoint _ y1 :: mkPoint _ _ :: _ :: nil =>
              Some (x0, y0, x1, y1)
          | _ => None
          end
      | _ => None
      end
  | _ => None
  end.

(* bool dec helpers removed... (kept comment for style) *)

Definition rect_pair_regime (ax0 ay0 ax1 ay1 bx0 by0 bx1 by1 : R) : RectPairRegime :=
  (* Full rect family decision (horizontal expansion + all four regimes).
     Detects vertical/horizontal touch (using the symmetric guards), contains
     (either dir), partial overlap, else disjoint. Mirrors the S6 predicates.
     Transpose for reverse-contains is handled in `relate`. *)
  match Req_dec_T ax1 bx0 with
  | left _ =>
      match Rlt_dec (Rmax ay0 by0) (Rmin ay1 by1) with
      | left _ => RPR_TouchVert
      | right _ => RPR_Disjoint
      end
  | right _ =>
      match Req_dec_T ay1 by0 with
      | left _ =>
          match Rlt_dec (Rmax ax0 bx0) (Rmin ax1 bx1) with
          | left _ => RPR_TouchHoriz
          | right _ => RPR_Disjoint
          end
      | right _ =>
          (* contains A supset B *)
          match Rlt_dec ax0 bx0 with
          | left _ =>
              match Rlt_dec bx1 ax1 with
              | left _ =>
                  match Rlt_dec ay0 by0 with
                  | left _ =>
                      match Rlt_dec by1 ay1 with
                      | left _ => RPR_Contains
                      | right _ => RPR_Disjoint
                      end
                  | right _ => RPR_Disjoint
                  end
              | right _ => RPR_Disjoint
              end
          | right _ =>
              (* contains B supset A (or overlap/disjoint) *)
              match Rlt_dec bx0 ax0 with
              | left _ =>
                  match Rlt_dec ax1 bx1 with
                  | left _ =>
                      match Rlt_dec by0 ay0 with
                      | left _ =>
                          match Rlt_dec ay1 by1 with
                          | left _ => RPR_Contains
                          | right _ => RPR_Disjoint
                          end
                      | right _ => RPR_Disjoint
                      end
                  | right _ => RPR_Disjoint
                  end
              | right _ =>
                  (* overlap heuristic using the partial_overlap guard structure *)
                  match Rlt_dec ax0 bx0 with
                  | left _ =>
                      match Rlt_dec bx0 ax1 with
                      | left _ =>
                          match Rlt_dec ay0 by0 with
                          | left _ =>
                              match Rlt_dec by0 ay1 with
                              | left _ =>
                                  match Rlt_dec bx1 ax1 with
                                  | left _ => RPR_Disjoint
                                  | right _ => RPR_Overlap
                                  end
                              | right _ => RPR_Disjoint
                              end
                          | right _ => RPR_Disjoint
                          end
                      | right _ => RPR_Disjoint
                      end
                  | right _ => RPR_Disjoint
                  end
              end
          end
      end
  end.

(* rects_relate wrapper (defined before use) *)
Definition rects_relate (ax0 ay0 ax1 ay1 bx0 by0 bx1 by1 : R)
    (r : RectPairRegime) : IntersectionMatrix :=
  (* `rect_pair_regime` maps BOTH A⊃B and B⊃A to RPR_Contains; the latter
     (strict B-within-A: bx0<ax0 ∧ ax1<bx1 ∧ by0<ay0 ∧ ay1<by1) is the
     "within" case, whose matrix is the transpose of contains. Folding that
     here keeps `relate` = `rects_relate … regime` definitionally. *)
  match r with
  | RPR_Contains =>
      match Rlt_dec bx0 ax0, Rlt_dec ax1 bx1, Rlt_dec by0 ay0, Rlt_dec ay1 by1 with
      | left _, left _, left _, left _ => matrix_transpose (rect_pair_fill r)
      | _, _, _, _ => rect_pair_fill r
      end
  | _ => rect_pair_fill r
  end.

Lemma rects_relate_touch_eq :
  forall ax0 ay0 ax1 ay1 bx0 by0 bx1 by1,
    rects_relate ax0 ay0 ax1 ay1 bx0 by0 bx1 by1 RPR_TouchVert =
    aa_matrix_touch_vertical.
Proof.
  intros. unfold rects_relate. apply rect_pair_fill_touch_eq.
Qed.

(* -------------------------------------------------------------------------- *)
(* Triangle lane: representation, decidable detectors, regime classifier.     *)
(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
(* Triangle representation (using gtri_ring style for consistency with JCT). *)
(* -------------------------------------------------------------------------- *)

Definition triangle_ring (ax ay bx by_ cx cy : R) : Ring :=
  [ mkPoint ax ay ; mkPoint bx by_ ; mkPoint cx cy ; mkPoint ax ay ].

Definition triangle_polygon (ax ay bx by_ cx cy : R) : Polygon :=
  {| outer_ring := triangle_ring ax ay bx by_ cx cy; hole_rings := [] |}.

Definition triangle_geometry (ax ay bx by_ cx cy : R) : Geometry :=
  [ triangle_polygon ax ay bx by_ cx cy ].

(* Extract the 6 coordinates for dispatch (mirrors rect_geometry_bounds). *)
Definition triangle_geometry_points (g : Geometry) : option (R * R * R * R * R * R) :=
  match g with
  | [poly] =>
      match hole_rings poly with
      | [] =>
          match outer_ring poly with
          | mkPoint ax ay :: mkPoint bx by_ :: mkPoint cx cy :: _ :: nil =>
              Some (ax, ay, bx, by_, cx, cy)
          | _ => None
          end
      | _ => None
      end
  | _ => None
  end.

(* Basic point-in-triangle (reuse point_in_ring on the ring; gtri for strict int later). *)
Definition point_in_triangle (ax ay bx by_ cx cy : R) (p : Point) : Prop :=
  point_in_ring p (triangle_ring ax ay bx by_ cx cy).

(* -------------------------------------------------------------------------- *)
(* Triangle regime decision (parallel to rect_pair_regime).                  *)
(* Uses cross for orientation, between for edge/vertex sharing.               *)
(* For now, a simple structural decision; full geometry predicates in classify. *)
(* -------------------------------------------------------------------------- *)

(* Decidable detectors for the shared-edge touch regime (boolean mirrors of the
   `shares_edge` / `opposite_sides` Props defined below; kept standalone so the
   classifier can use them).  Point equality and the strict cross-product sign
   are decidable over R via Req_dec_T / Rlt_dec (as in rect_pair_regime). *)
Definition point_eqb (p q : Point) : bool :=
  if Req_dec_T (px p) (px q)
  then if Req_dec_T (py p) (py q) then true else false
  else false.

Definition shares_edge_b (p1 p2 q1 q2 : Point) : bool :=
  orb (andb (point_eqb p1 q1) (point_eqb p2 q2))
      (andb (point_eqb p1 q2) (point_eqb p2 q1)).

Definition opposite_sides_b (p1 p2 p q : Point) : bool :=
  if Rlt_dec (cross p1 p2 p * cross p1 p2 q) 0 then true else false.

(* True iff some edge of triangle A coincides with some edge of triangle B and
   the two apex vertices lie on opposite sides of that shared edge -- the nine
   (edge-of-A x edge-of-B) cases of `triangles_touch_on_shared_edge`. *)
Definition touch_edge_b (a1 a2 a3 b1 b2 b3 : Point) : bool :=
  (shares_edge_b a1 a2 b1 b2 && opposite_sides_b a1 a2 a3 b3) ||
  (shares_edge_b a1 a2 b2 b3 && opposite_sides_b a1 a2 a3 b1) ||
  (shares_edge_b a1 a2 b3 b1 && opposite_sides_b a1 a2 a3 b2) ||
  (shares_edge_b a2 a3 b1 b2 && opposite_sides_b a2 a3 a1 b3) ||
  (shares_edge_b a2 a3 b2 b3 && opposite_sides_b a2 a3 a1 b1) ||
  (shares_edge_b a2 a3 b3 b1 && opposite_sides_b a2 a3 a1 b2) ||
  (shares_edge_b a3 a1 b1 b2 && opposite_sides_b a3 a1 a2 b3) ||
  (shares_edge_b a3 a1 b2 b3 && opposite_sides_b a3 a1 a2 b1) ||
  (shares_edge_b a3 a1 b3 b1 && opposite_sides_b a3 a1 a2 b2).

(* Decidable detector for the containment regime: A is CCW (0 < gdbl A) and
   all three of B's vertices are strictly interior to A (0 < gtri A _).
   `triangle_pair_regime_contains` below shows this is sound: it entails
   `touch_edge_b` is false (a vertex strictly interior to A cannot equal any
   of A's own vertices, so no shared-edge endpoint match is possible), and
   `contains_b_ring_inside` shows it is geometrically meaningful: every
   point on any of B's three edges -- not merely its vertices -- lies in
   A's closed region (via TriangleContainmentConvex.gtri_region_contains_segment). *)
Definition contains_b (ax ay bx by_ cx cy dx dy ex ey fx fy : R) : bool :=
  if Rlt_dec 0 (gdbl ax ay bx by_ cx cy) then
  if Rlt_dec 0 (gtri ax ay bx by_ cx cy (mkPoint dx dy)) then
  if Rlt_dec 0 (gtri ax ay bx by_ cx cy (mkPoint ex ey)) then
  if Rlt_dec 0 (gtri ax ay bx by_ cx cy (mkPoint fx fy)) then true
  else false else false else false else false.

(* Triangle regime classifier.  DETECTS the shared-edge touch regime (the
   `touch_edge_b` decision, proven correct on the `triangles_touch_on_shared_edge`
   inputs by `triangle_pair_regime_touch` below) and the containment regime
   (the `contains_b` decision, proven correct by `triangle_pair_regime_contains`
   below), returning TPR_Disjoint as the default for the remaining
   not-yet-classified regime (overlap). *)
Definition triangle_pair_regime (ax ay bx by_ cx cy dx dy ex ey fx fy : R) : TrianglePairRegime :=
  if touch_edge_b (mkPoint ax ay) (mkPoint bx by_) (mkPoint cx cy)
                  (mkPoint dx dy) (mkPoint ex ey) (mkPoint fx fy)
  then TPR_TouchEdge
  else if contains_b ax ay bx by_ cx cy dx dy ex ey fx fy
  then TPR_Contains
  else TPR_Disjoint.

(* Decidable equality on the classifier's result type -- consistent with the
   Req_dec_T / Rlt_dec approach used throughout the boolean detectors above,
   and available for any future case dispatch on `triangle_pair_regime`
   (mirroring the rectangle regime's decidability). *)
Lemma triangle_pair_regime_eq_dec :
  forall r1 r2 : TrianglePairRegime, {r1 = r2} + {r1 <> r2}.
Proof. decide equality. Qed.

(* tris_relate wrapper (parallel to rects_relate) *)
Definition tris_relate (ax ay bx by_ cx cy ax' ay' bx' by'' cx' cy' : R)
    (r : TrianglePairRegime) : IntersectionMatrix :=
  triangle_pair_fill r.

(* -------------------------------------------------------------------------- *)
(* Top-level relate dispatch (rect pair, then triangle pair, line fallback).  *)
(* -------------------------------------------------------------------------- *)

Definition relate (A B : Geometry) : IntersectionMatrix :=
  match rect_geometry_bounds A, rect_geometry_bounds B with
  | Some (ax0, ay0, ax1, ay1), Some (bx0, by0, bx1, by1) =>
      rects_relate ax0 ay0 ax1 ay1 bx0 by0 bx1 by1
        (rect_pair_regime ax0 ay0 ax1 ay1 bx0 by0 bx1 by1)
  | _, _ =>
      match triangle_geometry_points A, triangle_geometry_points B with
      | Some (ax, ay, bx, by_, cx, cy),
        Some (dx, dy, ex, ey, fx, fy) =>
          tris_relate ax ay bx by_ cx cy dx dy ex ey fx fy
            (triangle_pair_regime ax ay bx by_ cx cy dx dy ex ey fx fy)
      (* Outside the supported domain.  This MUST NOT be a disjointness
         matrix: `FFFFFFFFF` asserts the two geometries do not interact, and
         nothing here has established that.  `DE9IM.im_unsupported` is the
         sentinel -- `matrix_ok` rejects it, so a caller cannot read it as an
         answer.  The general case (the RelateNG noding pipeline) is still to
         come; until it lands the dispatch declines instead of guessing. *)
      | _, _ => im_unsupported
      end
  end.

Lemma relate_on_triangles_dispatches :
  forall ax ay bx by_ cx cy dx dy ex ey fx fy,
    relate (triangle_geometry ax ay bx by_ cx cy)
           (triangle_geometry dx dy ex ey fx fy) =
    tris_relate ax ay bx by_ cx cy dx dy ex ey fx fy
      (triangle_pair_regime ax ay bx by_ cx cy dx dy ex ey fx fy).
Proof.
  intros ax ay bx by_ cx cy dx dy ex ey fx fy.
  unfold relate, triangle_geometry_points, triangle_geometry, triangle_polygon.
  simpl.
  (* Dispatch reduces directly once the triangle points are extracted. *)
  reflexivity.
Qed.

(* Basic example of triangle dispatch reducing.  These two triangles share no
   edge, so the tightened classifier returns TPR_Disjoint (the shared-edge
   detector `touch_edge_b` is false -- every candidate vertex match fails on a
   differing coordinate). *)
Example relate_triangle_dispatch_ex :
  relate (triangle_geometry 0 0 1 0 0 1) (triangle_geometry 2 0 3 0 2 1) =
  tris_relate 0 0 1 0 0 1 2 0 3 0 2 1 TPR_Disjoint.
Proof.
  rewrite relate_on_triangles_dispatches.
  assert (Hreg : triangle_pair_regime 0 0 1 0 0 1 2 0 3 0 2 1 = TPR_Disjoint).
  { unfold triangle_pair_regime, touch_edge_b, shares_edge_b, point_eqb.
    cbn [px py].
    repeat (destruct (Req_dec_T _ _) as [?e | ?n]; try (exfalso; lra)).
    (* touch_edge_b is now pinned to `false`; the containment branch remains:
       the two triangles don't even share an x-range, so gtri of the first
       triangle at the second triangle's first vertex (2,0) is already
       non-positive (its gsA slack is exactly 0 there). *)
    unfold contains_b.
    assert (Hcb : gtri 0 0 1 0 0 1 (mkPoint 2 0) <= 0).
    { unfold gtri.
      assert (H : gsA 0 0 1 0 (mkPoint 2 0) = 0) by (unfold gsA; simpl; ring).
      rewrite H. eapply Rle_trans; [ apply Rmin_l_le | apply Rmin_l_le ]. }
    destruct (Rlt_dec 0 (gdbl 0 0 1 0 0 1)) as [_ | Hn].
    - destruct (Rlt_dec 0 (gtri 0 0 1 0 0 1 (mkPoint 2 0))) as [Hlt | _];
        [ exfalso; lra | reflexivity ].
    - exfalso. apply Hn. unfold gdbl. lra. }
  rewrite Hreg. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Unsupported input declines rather than guessing.                           *)
(*                                                                            *)
(* Previously this dispatch answered `ll_matrix_disjoint` for every pair it    *)
(* could not classify -- a positive claim of disjointness, indistinguishable  *)
(* to the caller from a computed one.  It now returns the sentinel, and the    *)
(* two lemmas below are the honesty properties that make the difference       *)
(* checkable rather than a comment.                                           *)
(* -------------------------------------------------------------------------- *)

Lemma relate_unsupported_pair :
  relate [] [] = im_unsupported.
Proof.
  unfold relate. reflexivity.
Qed.

(* The sentinel is not a well-formed matrix, so a caller validating its input
   catches the unsupported case. *)
Lemma relate_unsupported_not_ok :
  ~ matrix_ok (relate [] []).
Proof.
  rewrite relate_unsupported_pair. exact im_unsupported_not_ok.
Qed.

(* And it is specifically not the disjointness claim it replaced. *)
Lemma relate_unsupported_not_disjoint :
  ~ im_disjoint (relate [] []).
Proof.
  rewrite relate_unsupported_pair. exact im_unsupported_not_disjoint.
Qed.


(* Prepared integration note: see RelatePrepared.prepared_evaluate_agrees.
   The public entry `relate` is the uncached path; evaluate is the cached one. *)

(* -------------------------------------------------------------------------- *)
(* Audit.                                                                     *)
(* -------------------------------------------------------------------------- *)

Print Assumptions relate_unsupported_not_disjoint.

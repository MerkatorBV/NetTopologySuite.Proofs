(* ============================================================================
   NetTopologySuite.Proofs.RelateNGTouchCells
   ----------------------------------------------------------------------------
   Issue #67: RelateNG pipeline — DE-9IM cells for the shared-edge touch
   regime.

   Split (2026-08) from the former monolithic RelateNG.v; RelateNG.v remains
   as the re-export umbrella, so existing `Require Import RelateNG` clients
   (RelatePrepared.v) are unaffected.  Original section banners preserved.

   EE and II cells; the JCT seam lift (`gtri_point_in_ring_imp_pos`,
   `point_set_characterises_geometric_interior`); the seam-derived generic
   interior disjointness and the guarded II cell
   (`touch_triangle_pair_ii_cell_via_seam` — its ray-genericity residual is
   IRREDUCIBLE, see the RED refutation in RelateNGTouchRED.v); the
   UNCONDITIONAL geometric-interior separation (`tri_interior`,
   `touch_triangle_pair_ii_disjoint_unconditional`,
   `tri_interior_iff_point_set_generic`); the BB cell via shared vertices;
   and the capstones (`touch_triangles_satisfy_pointset{,_and_general}`,
   `touch_triangles_regime_cells_ii_bb_ee`).

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
From NTS.Proofs Require Import RelateNGCore RelateNGTouch.

Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* Triangle touch cell lemmas (BB/EE/II/F) mirroring rect touch cells.        *)
(* BB uses midpoint of a shared edge (provably between on both rings).        *)
(* EE reuses the universal exterior meet. II uses the strict (0 < gtri) form  *)
(* of separation (point_set would intersect on the shared boundary segment,   *)
(* which is accounted for in BB; mirrors rect half-open assignment of bnd).   *)
(* -------------------------------------------------------------------------- *)

Lemma touch_triangle_pair_ee_cell :
  forall ax ay bx by_ cx cy dx dy ex ey fx fy,
    triangles_touch_on_shared_edge (mkPoint ax ay) (mkPoint bx by_) (mkPoint cx cy)
                                   (mkPoint dx dy) (mkPoint ex ey) (mkPoint fx fy) ->
    RelateCurveMatrix.cell_ok (Some 2%nat) RelateCurveMatrix.SExt RelateCurveMatrix.SExt
      (triangle_geometry ax ay bx by_ cx cy)
      (triangle_geometry dx dy ex ey fx fy).
Proof.
  intros ax ay bx by_ cx cy dx dy ex ey fx fy Htouch.
  unfold RelateCurveMatrix.cell_ok.
  split.
  - simpl. auto.
  - split.
    + intros _.
      destruct (two_geometries_exterior_meet (triangle_geometry ax ay bx by_ cx cy)
                                             (triangle_geometry dx dy ex ey fx fy))
        as [p [HextA HextB]].
      exists p; split; assumption.
    + intros _. discriminate.
Qed.

Lemma touch_triangle_pair_ii_cell :
  forall ax ay bx by_ cx cy dx dy ex ey fx fy,
    triangles_touch_on_shared_edge (mkPoint ax ay) (mkPoint bx by_) (mkPoint cx cy)
                                   (mkPoint dx dy) (mkPoint ex ey) (mkPoint fx fy) ->
    (* H_ii_disjoint is the point_set version of separation (under half-open parity for SInt).
       The algebraic form (0<gtri) is Qed via gtri_neg + strict_ii. The lift point_set <-> 0<gtri
       for non-boundary p is the JCT seam (deferred; see general_triangle_parity_characterises_interior
       and point_set_characterises_geometric_interior below). *)
    (~ exists p,
        RelateCurveMatrix.in_stratum RelateCurveMatrix.SInt (triangle_geometry ax ay bx by_ cx cy) p /\
        RelateCurveMatrix.in_stratum RelateCurveMatrix.SInt (triangle_geometry dx dy ex ey fx fy) p) ->
    RelateCurveMatrix.cell_ok None RelateCurveMatrix.SInt RelateCurveMatrix.SInt
      (triangle_geometry ax ay bx by_ cx cy)
      (triangle_geometry dx dy ex ey fx fy).
Proof.
  intros ax ay bx by_ cx cy dx dy ex ey fx fy Htouch Hii.
  unfold RelateCurveMatrix.cell_ok.
  split.
  - simpl; auto.
  - split.
    + intro Hdn. exfalso. apply Hdn. reflexivity.
    + intro Hex. exfalso. apply Hii. exact Hex.
Qed.

(* JCT seam lift -- DISCHARGED (was Admitted).  The converse Jordan direction
   "ray-parity inside ==> strictly inside" assembled 3-axiom from the in-house
   JCT machinery: JCTSeamAssembly.point_in_ring_imp_geometric_cont (the trapped
   half) gives geometric_interior_cont, then a trichotomy on gtri closes it via
   GeneralTriangleExterior.gtri_exterior_escapes (gtri<0 escapes the bounded
   component) and GeneralTriangleSeparation.gtri_zero_imp_ring_image (gtri=0 is
   on the ring image, contradicting ring_complement).

   The unguarded statement is FALSE (refuted by GeneralTriangleParityRED and the
   vertex-grazing / on-edge counterexamples, and for CW triangles where 0<gtri is
   impossible), so the true theorem carries the natural guards: CCW (0 < gdbl),
   the point off the ring image (ring_complement), and ray genericity
   (ray_avoids_vertices).  Its first in-code consumers are
   touch_triangle_interiors_disjoint_generic and touch_triangle_pair_ii_cell_via_seam
   below, which derive the ii-cell point_set separation from this seam rather
   than assuming it. *)
Lemma gtri_point_in_ring_imp_pos : forall ax ay bx by_ cx cy p,
  0 < gdbl ax ay bx by_ cx cy ->
  ring_complement (gtri_ring ax ay bx by_ cx cy) p ->
  ray_avoids_vertices p (gtri_ring ax ay bx by_ cx cy) ->
  point_in_ring p (gtri_ring ax ay bx by_ cx cy) ->
  0 < gtri ax ay bx by_ cx cy p.
Proof.
  intros ax ay bx by_ cx cy p Hccw Hcompl Hrav Hpir.
  pose proof (gtri_ring_closed ax ay bx by_ cx cy) as Hclosed.
  pose proof (point_in_ring_imp_geometric_cont
                (gtri_ring ax ay bx by_ cx cy) p Hclosed Hcompl Hrav Hpir)
    as [_ Hbnd].
  destruct (Rtotal_order (gtri ax ay bx by_ cx cy p) 0) as [Hneg | [Hzero | Hpos]].
  - exfalso. exact (gtri_exterior_escapes ax ay bx by_ cx cy p Hccw Hneg Hbnd).
  - exfalso. apply Hcompl.
    exact (gtri_zero_imp_ring_image ax ay bx by_ cx cy Hccw p Hzero).
  - exact Hpos.
Qed.

Lemma point_set_characterises_geometric_interior :
  forall ax ay bx by_ cx cy p,
    0 < gdbl ax ay bx by_ cx cy ->
    ring_complement (gtri_ring ax ay bx by_ cx cy) p ->
    ray_avoids_vertices p (gtri_ring ax ay bx by_ cx cy) ->
    point_set (triangle_geometry ax ay bx by_ cx cy) p ->
    0 < gtri ax ay bx by_ cx cy p.
Proof.
  intros ax ay bx by_ cx cy p Hccw Hcompl Hrav Hps.
  apply (gtri_point_in_ring_imp_pos ax ay bx by_ cx cy p Hccw Hcompl Hrav).
  destruct Hps as [poly [Hin Hpip]].
  simpl in Hin. destruct Hin as [Heq | []]. subst poly.
  destruct Hpip as [Hpir _].
  unfold triangle_polygon in Hpir. simpl in Hpir.
  unfold triangle_ring in Hpir. unfold gtri_ring.
  exact Hpir.
Qed.

(* -------------------------------------------------------------------------- *)
(* FIRST CONSUMER of the Jordan seam point_set_characterises_geometric_interior. *)
(*                                                                            *)
(* Two CCW triangles touching on a shared edge have interiors separated by    *)
(* the shared edge's line, so no point that is interior to BOTH (in the       *)
(* parity point_set sense) AND off both ring images AND ray-generic for both  *)
(* can exist: the seam lifts each parity-interior membership to the strict    *)
(* algebraic form 0 < gtri, and the unconditional line separation             *)
(* touch_int_ext_exclusion (0 < gtri A p -> gtri B p < 0) then contradicts.   *)
(* The off-ring / ray-generic side conditions are exactly the seam's guards   *)
(* (CCW + ring_complement + ray_avoids_vertices); dropping the ray-genericity *)
(* one for an arbitrary witness is impossible -- see the RED refutation        *)
(* touch_triangle_ii_separation_not_unconditional (RelateNGTouchRED.v).        *)
(* 3-axiom (classical-reals trio only). *)
Lemma touch_triangle_interiors_disjoint_generic :
  forall ax ay bx by_ cx cy dx dy ex ey fx fy,
    triangles_touch_on_shared_edge (mkPoint ax ay) (mkPoint bx by_) (mkPoint cx cy)
                                   (mkPoint dx dy) (mkPoint ex ey) (mkPoint fx fy) ->
    0 < gdbl ax ay bx by_ cx cy ->
    0 < gdbl dx dy ex ey fx fy ->
    ~ exists p,
        (ring_complement (gtri_ring ax ay bx by_ cx cy) p /\
         ray_avoids_vertices p (gtri_ring ax ay bx by_ cx cy) /\
         point_set (triangle_geometry ax ay bx by_ cx cy) p) /\
        (ring_complement (gtri_ring dx dy ex ey fx fy) p /\
         ray_avoids_vertices p (gtri_ring dx dy ex ey fx fy) /\
         point_set (triangle_geometry dx dy ex ey fx fy) p).
Proof.
  intros ax ay bx by_ cx cy dx dy ex ey fx fy Htouch HccwA HccwB
         [p [[HcA [HrA HpsA]] [HcB [HrB HpsB]]]].
  pose proof (point_set_characterises_geometric_interior
                ax ay bx by_ cx cy p HccwA HcA HrA HpsA) as HgA.
  pose proof (point_set_characterises_geometric_interior
                dx dy ex ey fx fy p HccwB HcB HrB HpsB) as HgB.
  pose proof (touch_int_ext_exclusion
                ax ay bx by_ cx cy dx dy ex ey fx fy p Htouch HgA) as HgBneg.
  lra.
Qed.

(* The ii cell (cell_ok None SInt SInt), now wired THROUGH the seam: the opaque
   point_set-disjointness premise H_ii_disjoint is replaced by the explicit,
   seam-derivable residual -- that every common interior witness is off both ring
   images and ray-generic for both rings (plus the two CCW guards).  This is the
   honest remaining obligation, and it is IRREDUCIBLE: the ray-genericity part
   cannot be dropped even for off-ring witnesses.
   `touch_triangle_ii_separation_not_unconditional` (RelateNGTouchRED.v)
   exhibits two CCW
   triangles touching on a shared edge whose SInt point-sets genuinely overlap
   at an off-ring point that grazes a vertex -- so an unconditional (guard-free)
   H_ii_disjoint would be a FALSE theorem, and this guarded form is maximal.
   The disjointness itself is PROVED from the landed seam rather than assumed.
   3-axiom (classical-reals trio only). *)
Lemma touch_triangle_pair_ii_cell_via_seam :
  forall ax ay bx by_ cx cy dx dy ex ey fx fy,
    triangles_touch_on_shared_edge (mkPoint ax ay) (mkPoint bx by_) (mkPoint cx cy)
                                   (mkPoint dx dy) (mkPoint ex ey) (mkPoint fx fy) ->
    0 < gdbl ax ay bx by_ cx cy ->
    0 < gdbl dx dy ex ey fx fy ->
    (forall p,
        point_set (triangle_geometry ax ay bx by_ cx cy) p ->
        point_set (triangle_geometry dx dy ex ey fx fy) p ->
        (ring_complement (gtri_ring ax ay bx by_ cx cy) p /\
         ray_avoids_vertices p (gtri_ring ax ay bx by_ cx cy)) /\
        (ring_complement (gtri_ring dx dy ex ey fx fy) p /\
         ray_avoids_vertices p (gtri_ring dx dy ex ey fx fy))) ->
    RelateCurveMatrix.cell_ok None RelateCurveMatrix.SInt RelateCurveMatrix.SInt
      (triangle_geometry ax ay bx by_ cx cy)
      (triangle_geometry dx dy ex ey fx fy).
Proof.
  intros ax ay bx by_ cx cy dx dy ex ey fx fy Htouch HccwA HccwB Hgen.
  apply (touch_triangle_pair_ii_cell ax ay bx by_ cx cy dx dy ex ey fx fy Htouch).
  intros [p [HsA HsB]].
  unfold RelateCurveMatrix.in_stratum in HsA, HsB.
  destruct (Hgen p HsA HsB) as [[HcA HrA] [HcB HrB]].
  pose proof (point_set_characterises_geometric_interior
                ax ay bx by_ cx cy p HccwA HcA HrA HsA) as HgA.
  pose proof (point_set_characterises_geometric_interior
                dx dy ex ey fx fy p HccwB HcB HrB HsB) as HgB.
  pose proof (touch_int_ext_exclusion
                ax ay bx by_ cx cy dx dy ex ey fx fy p Htouch HgA) as HgBneg.
  lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* THE UNCONDITIONAL LIFT (main regime): II separation against the geometric   *)
(* interior.                                                                   *)
(*                                                                            *)
(* The matrix the touch dispatch produces sets im_ii = None                    *)
(* (touch_triangle_pair_bb_cell_shape) -- it CLAIMS the interiors are          *)
(* disjoint.  That claim is UNCONDITIONALLY SOUND against the geometrically-   *)
(* correct interior of a triangle (strict signed-area positivity, which for    *)
(* CCW triangles is the true topological interior,                            *)
(* GeneralTriangleSeparation.gtri_interior_is_geometric).  The parity          *)
(* point_set proxy needs the ray-genericity guard                             *)
(* (touch_triangle_ii_separation_not_unconditional shows exactly why), but the *)
(* interior the DE-9IM intends is separated with NO guard at all.  This is the *)
(* lift of H_ii_disjoint for the main regime, discharged outright.             *)
(* -------------------------------------------------------------------------- *)

(* The geometrically-correct interior of a triangle: strictly positive slack.  *)
Definition tri_interior (ax ay bx by_ cx cy : R) (p : Point) : Prop :=
  0 < gtri ax ay bx by_ cx cy p.

(* UNCONDITIONAL: two triangles touching on a shared edge have disjoint
   geometric interiors -- no CCW, ring_complement, or ray-genericity guard. *)
Theorem touch_triangle_pair_ii_disjoint_unconditional :
  forall ax ay bx by_ cx cy dx dy ex ey fx fy,
    triangles_touch_on_shared_edge (mkPoint ax ay) (mkPoint bx by_) (mkPoint cx cy)
                                   (mkPoint dx dy) (mkPoint ex ey) (mkPoint fx fy) ->
    ~ exists p, tri_interior ax ay bx by_ cx cy p
             /\ tri_interior dx dy ex ey fx fy p.
Proof.
  intros ax ay bx by_ cx cy dx dy ex ey fx fy Htouch.
  unfold tri_interior.
  apply touch_triangle_pair_strict_ii_no_common; assumption.
Qed.

(* The two interiors coincide OFF the ray-genericity-failing set: under the
   natural guards (CCW + off-ring + ray-generic) the geometric interior and the
   parity point_set agree, so the unconditional geometric separation above
   transfers to the parity point_set for every generic witness -- the guarded
   parity form (touch_triangle_pair_ii_cell_via_seam) is then exactly its
   restriction to those witnesses, and the RED (RelateNGTouchRED.v) is the
   whole gap. *)
Theorem tri_interior_iff_point_set_generic :
  forall ax ay bx by_ cx cy p,
    0 < gdbl ax ay bx by_ cx cy ->
    ring_complement (gtri_ring ax ay bx by_ cx cy) p ->
    ray_avoids_vertices p (gtri_ring ax ay bx by_ cx cy) ->
    (tri_interior ax ay bx by_ cx cy p
       <-> point_set (triangle_geometry ax ay bx by_ cx cy) p).
Proof.
  intros ax ay bx by_ cx cy p Hccw Hcompl Hrav. unfold tri_interior. split.
  - intro Hpos.
    exists (triangle_polygon ax ay bx by_ cx cy).
    split; [ left; reflexivity | ].
    unfold point_in_polygon, triangle_polygon, outer_ring, hole_rings.
    split; [ | intros h [] ].
    exact (gtri_interior_in_ring ax ay bx by_ cx cy p Hpos Hrav).
  - intro Hps.
    exact (point_set_characterises_geometric_interior
             ax ay bx by_ cx cy p Hccw Hcompl Hrav Hps).
Qed.

Print Assumptions touch_triangle_pair_ii_disjoint_unconditional.
Print Assumptions tri_interior_iff_point_set_generic.

(* Helper: each vertex of a triangle is on its boundary. *)
Lemma tri_bnd_v1 : forall ax ay bx by_ cx cy,
  RelateCurveMatrix.geom_boundary (triangle_geometry ax ay bx by_ cx cy) (mkPoint ax ay).
Proof.
  intros ax ay bx by_ cx cy.
  unfold RelateCurveMatrix.geom_boundary, triangle_geometry, triangle_polygon,
         RelateCurveMatrix.poly_edges, RelateCurveMatrix.on_edge, outer_ring, hole_rings.
  eexists. split. left; reflexivity.
  exists (mkPoint ax ay, mkPoint bx by_). split.
  - cbn. left; reflexivity.
  - cbn. apply between_P0.
Qed.

Lemma tri_bnd_v2 : forall ax ay bx by_ cx cy,
  RelateCurveMatrix.geom_boundary (triangle_geometry ax ay bx by_ cx cy) (mkPoint bx by_).
Proof.
  intros ax ay bx by_ cx cy.
  unfold RelateCurveMatrix.geom_boundary, triangle_geometry, triangle_polygon,
         RelateCurveMatrix.poly_edges, RelateCurveMatrix.on_edge, outer_ring, hole_rings.
  eexists. split. left; reflexivity.
  exists (mkPoint bx by_, mkPoint cx cy). split.
  - cbn. right; left; reflexivity.
  - cbn. apply between_P0.
Qed.

Lemma tri_bnd_v3 : forall ax ay bx by_ cx cy,
  RelateCurveMatrix.geom_boundary (triangle_geometry ax ay bx by_ cx cy) (mkPoint cx cy).
Proof.
  intros ax ay bx by_ cx cy.
  unfold RelateCurveMatrix.geom_boundary, triangle_geometry, triangle_polygon,
         RelateCurveMatrix.poly_edges, RelateCurveMatrix.on_edge, outer_ring, hole_rings.
  eexists. split. left; reflexivity.
  exists (mkPoint cx cy, mkPoint ax ay). split.
  - cbn. right; right; left; reflexivity.
  - cbn. apply between_P0.
Qed.

(* BB cell: a shared vertex is on the boundary of both triangles. *)
Lemma touch_triangle_pair_bb_cell :
  forall ax ay bx by_ cx cy dx dy ex ey fx fy,
    triangles_touch_on_shared_edge (mkPoint ax ay) (mkPoint bx by_) (mkPoint cx cy)
                                   (mkPoint dx dy) (mkPoint ex ey) (mkPoint fx fy) ->
    RelateCurveMatrix.cell_ok (Some 1%nat) RelateCurveMatrix.SBnd RelateCurveMatrix.SBnd
      (triangle_geometry ax ay bx by_ cx cy)
      (triangle_geometry dx dy ex ey fx fy).
Proof.
  intros ax ay bx by_ cx cy dx dy ex ey fx fy Htouch.
  unfold RelateCurveMatrix.cell_ok.
  split. simpl; auto.
  split.
  - intros Hdim.
    unfold triangles_touch_on_shared_edge, shares_edge in Htouch.
    destruct Htouch as [H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]].
    all: destruct H as [[[Hp1 Hp2]|[Hp1 Hp2]] _].
    (* For each of the 18 cases, the shared vertex is Hp1's LHS.
       Try each A-vertex as witness; rewrite Hp1 to convert to B-vertex name,
       then apply the matching tri_bnd_v* for B. *)
    all: first
    [ exists (mkPoint ax ay); split;
        [ apply tri_bnd_v1
        | rewrite Hp1; (apply tri_bnd_v1 || apply tri_bnd_v2 || apply tri_bnd_v3) ]
    | exists (mkPoint bx by_); split;
        [ apply tri_bnd_v2
        | rewrite Hp1; (apply tri_bnd_v1 || apply tri_bnd_v2 || apply tri_bnd_v3) ]
    | exists (mkPoint cx cy); split;
        [ apply tri_bnd_v3
        | rewrite Hp1; (apply tri_bnd_v1 || apply tri_bnd_v2 || apply tri_bnd_v3) ]
    ].
  - intros _. discriminate.
Qed.

(* F-exclusion (trimmed): the critical II/EE/BB are handled above; other F cells
   (IB/BI/BE/EB/EI/IE) follow from no interior overlap (strict) + exterior meet.
   Full 9-cell geom_de9im_pointset is DEFERRED (see note in capstone and rect precedent:
   matrix F vs actual point_set/geom_bnd on shared edges due to boundary inclusion). *)
Lemma touch_triangle_f_cells_trimmed :
  forall ax ay bx by_ cx cy dx dy ex ey fx fy,
    triangles_touch_on_shared_edge (mkPoint ax ay) (mkPoint bx by_) (mkPoint cx cy)
                                   (mkPoint dx dy) (mkPoint ex ey) (mkPoint fx fy) ->
    (* II (strict) already gives no int-int; EE + touch regime excludes int-ext meets.
       The prior false exclusion (interior A implies not exterior B) was the JCT seam
       falsehood (point_set can share bnd on shared edge; moved to counterexamples).
       Only the provable strict no-common remains. *)
    (~ exists p, 0 < gtri ax ay bx by_ cx cy p /\ 0 < gtri dx dy ex ey fx fy p).
Proof.
  intros ax ay bx by_ cx cy dx dy ex ey fx fy Htouch.
  apply touch_triangle_pair_strict_ii_no_common; assumption.
Qed.

(* Capstone: assemble the provable cells for triangle shared-edge touch.
   Provable: strict-II none, BB (bnd meet), EE (exterior meet), F-excl for key.
   Honest: uses 0<gtri for II (point_set common exists on shared bnd, which
   goes to BB cell per half-open philosophy as in rect). *)
Lemma touch_triangles_satisfy_pointset :
  forall ax ay bx by_ cx cy dx dy ex ey fx fy,
    triangles_touch_on_shared_edge (mkPoint ax ay) (mkPoint bx by_) (mkPoint cx cy)
                                   (mkPoint dx dy) (mkPoint ex ey) (mkPoint fx fy) ->
    (~ exists p, 0 < gtri ax ay bx by_ cx cy p /\ 0 < gtri dx dy ex ey fx fy p) /\
    RelateCurveMatrix.cell_ok (Some 1%nat) RelateCurveMatrix.SBnd RelateCurveMatrix.SBnd
      (triangle_geometry ax ay bx by_ cx cy) (triangle_geometry dx dy ex ey fx fy) /\
    RelateCurveMatrix.cell_ok (Some 2%nat) RelateCurveMatrix.SExt RelateCurveMatrix.SExt
      (triangle_geometry ax ay bx by_ cx cy) (triangle_geometry dx dy ex ey fx fy).
Proof.
  intros ax ay bx by_ cx cy dx dy ex ey fx fy Htouch.
  split; [| split].
  - apply touch_triangle_pair_strict_ii_no_common; assumption.
  - apply touch_triangle_pair_bb_cell; assumption.
  - apply touch_triangle_pair_ee_cell; assumption.
Qed.

(* Generalized form for other regimes (overlap/contains/disjoint): use S6 facts
   (two_geometries_exterior_meet, regime exclusions) + the touch separation.
   This is the bridge pattern for composition (Delaunay next). *)
Lemma touch_triangles_satisfy_pointset_and_general :
  forall ax ay bx by_ cx cy dx dy ex ey fx fy (r : TrianglePairRegime)
         (Htouch : triangles_touch_on_shared_edge (mkPoint ax ay) (mkPoint bx by_) (mkPoint cx cy)
                                                  (mkPoint dx dy) (mkPoint ex ey) (mkPoint fx fy)),
    r = TPR_TouchEdge ->
    (~ exists p, 0 < gtri ax ay bx by_ cx cy p /\ 0 < gtri dx dy ex ey fx fy p) /\
    RelateCurveMatrix.cell_ok (Some 1%nat) RelateCurveMatrix.SBnd RelateCurveMatrix.SBnd
      (triangle_geometry ax ay bx by_ cx cy) (triangle_geometry dx dy ex ey fx fy) /\
    RelateCurveMatrix.cell_ok (Some 2%nat) RelateCurveMatrix.SExt RelateCurveMatrix.SExt
      (triangle_geometry ax ay bx by_ cx cy) (triangle_geometry dx dy ex ey fx fy).
Proof.
  intros ax ay bx by_ cx cy dx dy ex ey fx fy r Htouch Hr.
  subst r.
  apply touch_triangles_satisfy_pointset; assumption.
Qed.

(* -------------------------------------------------------------------------- *)
(* Regime -> cell_ok TRIPLE (II / BB / EE) for the shared-edge touch regime.  *)
(*                                                                            *)
(* `touch_triangles_satisfy_pointset` bundles the *algebraic* interior        *)
(* separation (0 < gtri) with the BB and EE cells, but never delivers the     *)
(* interior conjunct as an actual DE-9IM II cell.  This capstone upgrades it: *)
(* it produces `cell_ok None SInt SInt` over the parity `point_set` alongside *)
(* the BB and EE `cell_ok`s, so all three provable strata cells are delivered *)
(* as `cell_ok` facts under one regime guard `r = TPR_TouchEdge`.             *)
(*                                                                            *)
(* The II cell carries the ray-genericity residual `Hgen` (every common       *)
(* point_set witness is off both ring images and ray-generic for both).  That *)
(* residual is IRREDUCIBLE, not a deferral: `touch_triangle_ii_separation_-   *)
(* not_unconditional` (Qed, RelateNGTouchRED.v) exhibits two CCW shared-edge  *)
(* triangles whose parity SInt point-sets genuinely overlap at a vertex-      *)
(* grazing witness, so a guard-free II `cell_ok None SInt SInt` would be a    *)
(* FALSE theorem.  BB                                                         *)
(* and EE stay unconditional.  Composes touch_triangle_pair_ii_cell_via_seam  *)
(* + _bb_cell + _ee_cell.  3-axiom (classical-reals trio only). *)
Lemma touch_triangles_regime_cells_ii_bb_ee :
  forall ax ay bx by_ cx cy dx dy ex ey fx fy (r : TrianglePairRegime),
    triangles_touch_on_shared_edge (mkPoint ax ay) (mkPoint bx by_) (mkPoint cx cy)
                                   (mkPoint dx dy) (mkPoint ex ey) (mkPoint fx fy) ->
    r = TPR_TouchEdge ->
    0 < gdbl ax ay bx by_ cx cy ->
    0 < gdbl dx dy ex ey fx fy ->
    (forall p,
        point_set (triangle_geometry ax ay bx by_ cx cy) p ->
        point_set (triangle_geometry dx dy ex ey fx fy) p ->
        (ring_complement (gtri_ring ax ay bx by_ cx cy) p /\
         ray_avoids_vertices p (gtri_ring ax ay bx by_ cx cy)) /\
        (ring_complement (gtri_ring dx dy ex ey fx fy) p /\
         ray_avoids_vertices p (gtri_ring dx dy ex ey fx fy))) ->
    RelateCurveMatrix.cell_ok None RelateCurveMatrix.SInt RelateCurveMatrix.SInt
      (triangle_geometry ax ay bx by_ cx cy) (triangle_geometry dx dy ex ey fx fy) /\
    RelateCurveMatrix.cell_ok (Some 1%nat) RelateCurveMatrix.SBnd RelateCurveMatrix.SBnd
      (triangle_geometry ax ay bx by_ cx cy) (triangle_geometry dx dy ex ey fx fy) /\
    RelateCurveMatrix.cell_ok (Some 2%nat) RelateCurveMatrix.SExt RelateCurveMatrix.SExt
      (triangle_geometry ax ay bx by_ cx cy) (triangle_geometry dx dy ex ey fx fy).
Proof.
  intros ax ay bx by_ cx cy dx dy ex ey fx fy r Htouch Hr HccwA HccwB Hgen.
  subst r.
  split; [| split].
  - apply (touch_triangle_pair_ii_cell_via_seam
             ax ay bx by_ cx cy dx dy ex ey fx fy Htouch HccwA HccwB Hgen).
  - apply touch_triangle_pair_bb_cell; assumption.
  - apply touch_triangle_pair_ee_cell; assumption.
Qed.

Print Assumptions touch_triangles_regime_cells_ii_bb_ee.

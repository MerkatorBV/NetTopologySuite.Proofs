(* ============================================================================
   NetTopologySuite.Proofs.WktGeoJsonRoundtrip
   ----------------------------------------------------------------------------
   Structural roundtrips between WKT and GeoJSON geometry models.

   Scope (honest):

     - We do NOT claim string-level identity.  WKT writers vary whitespace,
       precision, and EMPTY spelling; GeoJSON writers vary key order and
       number formatting.  "Same result" here means the *parsed geometry
       trees* agree after a WKT → GeoJSON → WKT (or reverse) conversion.

     - Both formats are modelled as typed ASTs over the shared OGC 2-D
       simple-features hierarchy (Point / LineString / Polygon / Multi* /
       GeometryCollection / Empty-of-type).  Coordinates are XY only
       (no Z/M), matching the corpus `Point` carrier.

     - GeoJSON positions are ordered pairs `(x, y)` (RFC 7946 Position
       restricted to 2-D).  WKT vertices are `Distance.Point`.

   Delivers:

     - `OgcGeometry` — shared parse-tree / value model
     - `WktGeometry` — synonym (WKT reader output)
     - `GeoJsonGeometry` — GeoJSON geometry object (no Feature wrapper)
     - `wkt_to_geojson` / `geojson_to_wkt`
     - Roundtrip lemmas:
         `wkt_geojson_wkt_roundtrip`
         `geojson_wkt_geojson_roundtrip`
       plus the coordinate bijection and a few concrete witnesses
       (POINT, LINESTRING, POLYGON).

   No `Admitted`, no `Axiom`, no `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
   ========================================================================== *)

From Stdlib Require Import Reals List.
From NTS.Proofs Require Import Distance.

Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  Shared OGC 2-D geometry tree (WKT parse model).                        *)
(* -------------------------------------------------------------------------- *)

(** Empty geometries in WKT carry a type tag (`POINT EMPTY`, …). *)
Inductive GeomType : Type :=
| GTPoint
| GTLineString
| GTPolygon
| GTMultiPoint
| GTMultiLineString
| GTMultiPolygon
| GTGeometryCollection.

(** WKT / OGC simple-features value after parse (2-D). *)
Inductive OgcGeometry : Type :=
| OgcPoint (p : Point)
| OgcLineString (pts : list Point)
| OgcPolygon (shell : list Point) (holes : list (list Point))
| OgcMultiPoint (pts : list Point)
| OgcMultiLineString (lines : list (list Point))
| OgcMultiPolygon (polys : list (list Point * list (list Point)))
| OgcGeometryCollection (geoms : list OgcGeometry)
| OgcEmpty (t : GeomType).

(** WKT reader/writer work on this tree.  String lexing/printing is out of scope. *)
Definition WktGeometry : Type := OgcGeometry.

(* -------------------------------------------------------------------------- *)
(* §2  GeoJSON geometry objects (RFC 7946 geometry, 2-D positions).           *)
(* -------------------------------------------------------------------------- *)

(** GeoJSON Position restricted to XY: the array `[x, y]`. *)
Definition GjPosition : Type := (R * R)%type.

Inductive GeoJsonGeometry : Type :=
| GJPoint (c : GjPosition)
| GJLineString (cs : list GjPosition)
| GJPolygon (shell : list GjPosition) (holes : list (list GjPosition))
  (* Wire GeoJSON packs these as the ring array [shell] ++ holes.  We keep
     shell/holes separate so the WKT ↔ GeoJSON value models are bijective,
     including the empty-shell edge case that a bare `list rings` would
     collapse (`[]` vs `[[]]`). *)
| GJMultiPoint (cs : list GjPosition)
| GJMultiLineString (lines : list (list GjPosition))
| GJMultiPolygon (polys : list (list GjPosition * list (list GjPosition)))
| GJGeometryCollection (geoms : list GeoJsonGeometry)
| GJEmpty (t : GeomType).

(* -------------------------------------------------------------------------- *)
(* §3  Coordinate bijection Point ↔ GjPosition.                               *)
(* -------------------------------------------------------------------------- *)

Definition gjpos_of_point (p : Point) : GjPosition :=
  (px p, py p).

Definition point_of_gjpos (c : GjPosition) : Point :=
  mkPoint (fst c) (snd c).

Lemma point_of_gjpos_of_point :
  forall p : Point, point_of_gjpos (gjpos_of_point p) = p.
Proof.
  intros [x y]. reflexivity.
Qed.

Lemma gjpos_of_point_of_gjpos :
  forall c : GjPosition, gjpos_of_point (point_of_gjpos c) = c.
Proof.
  intros [x y]. reflexivity.
Qed.

(* Map helpers on lists / nested rings. *)

Definition map_pts_to_gj (pts : list Point) : list GjPosition :=
  map gjpos_of_point pts.

Definition map_gj_to_pts (cs : list GjPosition) : list Point :=
  map point_of_gjpos cs.

Definition map_rings_to_gj (rings : list (list Point)) : list (list GjPosition) :=
  map map_pts_to_gj rings.

Definition map_gj_to_rings (rings : list (list GjPosition)) : list (list Point) :=
  map map_gj_to_pts rings.

Lemma map_gj_to_pts_of_map_pts_to_gj :
  forall pts, map_gj_to_pts (map_pts_to_gj pts) = pts.
Proof.
  induction pts as [| p pts IH]; simpl.
  - reflexivity.
  - rewrite point_of_gjpos_of_point, IH. reflexivity.
Qed.

Lemma map_pts_to_gj_of_map_gj_to_pts :
  forall cs, map_pts_to_gj (map_gj_to_pts cs) = cs.
Proof.
  induction cs as [| c cs IH]; simpl.
  - reflexivity.
  - rewrite gjpos_of_point_of_gjpos, IH. reflexivity.
Qed.

Lemma map_gj_to_rings_of_map_rings_to_gj :
  forall rings, map_gj_to_rings (map_rings_to_gj rings) = rings.
Proof.
  induction rings as [| r rings IH]; simpl.
  - reflexivity.
  - rewrite map_gj_to_pts_of_map_pts_to_gj, IH. reflexivity.
Qed.

Lemma map_rings_to_gj_of_map_gj_to_rings :
  forall rings, map_rings_to_gj (map_gj_to_rings rings) = rings.
Proof.
  induction rings as [| r rings IH]; simpl.
  - reflexivity.
  - rewrite map_pts_to_gj_of_map_gj_to_pts, IH. reflexivity.
Qed.

(* MultiPolygon member: WKT (shell, holes) ↔ GeoJSON (shell, holes). *)

Definition gj_poly_of_wkt_poly (ph : list Point * list (list Point))
  : list GjPosition * list (list GjPosition) :=
  (map_pts_to_gj (fst ph), map_rings_to_gj (snd ph)).

Definition wkt_poly_of_gj_poly (ph : list GjPosition * list (list GjPosition))
  : list Point * list (list Point) :=
  (map_gj_to_pts (fst ph), map_gj_to_rings (snd ph)).

Lemma wkt_poly_of_gj_poly_of_wkt :
  forall ph, wkt_poly_of_gj_poly (gj_poly_of_wkt_poly ph) = ph.
Proof.
  intros [shell holes].
  unfold wkt_poly_of_gj_poly, gj_poly_of_wkt_poly. simpl.
  rewrite map_gj_to_pts_of_map_pts_to_gj.
  rewrite map_gj_to_rings_of_map_rings_to_gj.
  reflexivity.
Qed.

Lemma gj_poly_of_wkt_poly_of_gj :
  forall ph, gj_poly_of_wkt_poly (wkt_poly_of_gj_poly ph) = ph.
Proof.
  intros [shell holes].
  unfold gj_poly_of_wkt_poly, wkt_poly_of_gj_poly. simpl.
  rewrite map_pts_to_gj_of_map_gj_to_pts.
  rewrite map_rings_to_gj_of_map_gj_to_rings.
  reflexivity.
Qed.

(** Optional wire packing: GeoJSON Polygon encodes shell/holes as one ring array. *)
Definition geojson_polygon_rings (shell : list GjPosition)
    (holes : list (list GjPosition)) : list (list GjPosition) :=
  shell :: holes.

Lemma geojson_polygon_rings_cons :
  forall shell holes,
    geojson_polygon_rings shell holes = shell :: holes.
Proof. intros. reflexivity. Qed.

(* -------------------------------------------------------------------------- *)
(* §4  WKT ↔ GeoJSON conversions.                                             *)
(* -------------------------------------------------------------------------- *)

Fixpoint wkt_to_geojson (w : WktGeometry) : GeoJsonGeometry :=
  match w with
  | OgcPoint p =>
      GJPoint (gjpos_of_point p)
  | OgcLineString pts =>
      GJLineString (map_pts_to_gj pts)
  | OgcPolygon shell holes =>
      GJPolygon (map_pts_to_gj shell) (map_rings_to_gj holes)
  | OgcMultiPoint pts =>
      GJMultiPoint (map_pts_to_gj pts)
  | OgcMultiLineString lines =>
      GJMultiLineString (map map_pts_to_gj lines)
  | OgcMultiPolygon polys =>
      GJMultiPolygon (map gj_poly_of_wkt_poly polys)
  | OgcGeometryCollection geoms =>
      GJGeometryCollection (map wkt_to_geojson geoms)
  | OgcEmpty t =>
      GJEmpty t
  end.

Fixpoint geojson_to_wkt (g : GeoJsonGeometry) : WktGeometry :=
  match g with
  | GJPoint c =>
      OgcPoint (point_of_gjpos c)
  | GJLineString cs =>
      OgcLineString (map_gj_to_pts cs)
  | GJPolygon shell holes =>
      OgcPolygon (map_gj_to_pts shell) (map_gj_to_rings holes)
  | GJMultiPoint cs =>
      OgcMultiPoint (map_gj_to_pts cs)
  | GJMultiLineString lines =>
      OgcMultiLineString (map map_gj_to_pts lines)
  | GJMultiPolygon polys =>
      OgcMultiPolygon (map wkt_poly_of_gj_poly polys)
  | GJGeometryCollection geoms =>
      OgcGeometryCollection (map geojson_to_wkt geoms)
  | GJEmpty t =>
      OgcEmpty t
  end.

(* -------------------------------------------------------------------------- *)
(* §5  Headline roundtrips.                                                   *)
(* -------------------------------------------------------------------------- *)

Lemma map_lines_gj_to_pts_of_pts_to_gj :
  forall lines,
    map map_gj_to_pts (map map_pts_to_gj lines) = lines.
Proof.
  induction lines as [| ln lines IH]; simpl.
  - reflexivity.
  - rewrite map_gj_to_pts_of_map_pts_to_gj, IH. reflexivity.
Qed.

Lemma map_lines_pts_to_gj_of_gj_to_pts :
  forall lines,
    map map_pts_to_gj (map map_gj_to_pts lines) = lines.
Proof.
  induction lines as [| ln lines IH]; simpl.
  - reflexivity.
  - rewrite map_pts_to_gj_of_map_gj_to_pts, IH. reflexivity.
Qed.

Lemma map_polys_wkt_of_gj_of_wkt :
  forall polys,
    map wkt_poly_of_gj_poly (map gj_poly_of_wkt_poly polys) = polys.
Proof.
  induction polys as [| ph polys IH]; simpl.
  - reflexivity.
  - rewrite wkt_poly_of_gj_poly_of_wkt, IH. reflexivity.
Qed.

Lemma map_polys_gj_of_wkt_of_gj :
  forall polys,
    map gj_poly_of_wkt_poly (map wkt_poly_of_gj_poly polys) = polys.
Proof.
  induction polys as [| ph polys IH]; simpl.
  - reflexivity.
  - rewrite gj_poly_of_wkt_poly_of_gj, IH. reflexivity.
Qed.

Theorem wkt_geojson_wkt_roundtrip :
  forall w : WktGeometry,
    geojson_to_wkt (wkt_to_geojson w) = w.
Proof.
  fix IH 1.
  intros w.
  destruct w as [p | pts | shell holes | pts | lines | polys | geoms | t]; simpl.
  - rewrite point_of_gjpos_of_point. reflexivity.
  - rewrite map_gj_to_pts_of_map_pts_to_gj. reflexivity.
  - rewrite map_gj_to_pts_of_map_pts_to_gj,
            map_gj_to_rings_of_map_rings_to_gj. reflexivity.
  - rewrite map_gj_to_pts_of_map_pts_to_gj. reflexivity.
  - rewrite map_lines_gj_to_pts_of_pts_to_gj. reflexivity.
  - rewrite map_polys_wkt_of_gj_of_wkt. reflexivity.
  - f_equal.
    induction geoms as [| g gs IHgs]; simpl.
    + reflexivity.
    + rewrite (IH g), IHgs. reflexivity.
  - reflexivity.
Qed.

Theorem geojson_wkt_geojson_roundtrip :
  forall g : GeoJsonGeometry,
    wkt_to_geojson (geojson_to_wkt g) = g.
Proof.
  fix IH 1.
  intros g.
  destruct g as [c | cs | shell holes | cs | lines | polys | geoms | t]; simpl.
  - rewrite gjpos_of_point_of_gjpos. reflexivity.
  - rewrite map_pts_to_gj_of_map_gj_to_pts. reflexivity.
  - rewrite map_pts_to_gj_of_map_gj_to_pts,
            map_rings_to_gj_of_map_gj_to_rings. reflexivity.
  - rewrite map_pts_to_gj_of_map_gj_to_pts. reflexivity.
  - rewrite map_lines_pts_to_gj_of_gj_to_pts. reflexivity.
  - rewrite map_polys_gj_of_wkt_of_gj. reflexivity.
  - f_equal.
    induction geoms as [| g' gs IHgs]; simpl.
    + reflexivity.
    + rewrite (IH g'), IHgs. reflexivity.
  - reflexivity.
Qed.

(* Composed form matching the user wording: WKT → GeoJSON → WKT is identity. *)
Corollary wkt_to_geojson_to_wkt_id :
  forall w : WktGeometry,
    geojson_to_wkt (wkt_to_geojson w) = w.
Proof. exact wkt_geojson_wkt_roundtrip. Qed.

Corollary geojson_to_wkt_to_geojson_id :
  forall g : GeoJsonGeometry,
    wkt_to_geojson (geojson_to_wkt g) = g.
Proof. exact geojson_wkt_geojson_roundtrip. Qed.

(* -------------------------------------------------------------------------- *)
(* §6  Concrete witnesses (POINT / LINESTRING / POLYGON / EMPTY).             *)
(* -------------------------------------------------------------------------- *)

Definition sample_point_wkt : WktGeometry :=
  OgcPoint (mkPoint 1 2).

Definition sample_linestring_wkt : WktGeometry :=
  OgcLineString [mkPoint 0 0; mkPoint 1 1; mkPoint 2 0].

Definition sample_polygon_wkt : WktGeometry :=
  OgcPolygon
    [mkPoint 0 0; mkPoint 4 0; mkPoint 4 4; mkPoint 0 4; mkPoint 0 0]
    [[mkPoint 1 1; mkPoint 2 1; mkPoint 2 2; mkPoint 1 2; mkPoint 1 1]].

Definition sample_empty_point_wkt : WktGeometry :=
  OgcEmpty GTPoint.

Lemma sample_point_wkt_geojson_wkt :
  geojson_to_wkt (wkt_to_geojson sample_point_wkt) = sample_point_wkt.
Proof. apply wkt_geojson_wkt_roundtrip. Qed.

Lemma sample_linestring_wkt_geojson_wkt :
  geojson_to_wkt (wkt_to_geojson sample_linestring_wkt) = sample_linestring_wkt.
Proof. apply wkt_geojson_wkt_roundtrip. Qed.

Lemma sample_polygon_wkt_geojson_wkt :
  geojson_to_wkt (wkt_to_geojson sample_polygon_wkt) = sample_polygon_wkt.
Proof. apply wkt_geojson_wkt_roundtrip. Qed.

Lemma sample_empty_point_wkt_geojson_wkt :
  geojson_to_wkt (wkt_to_geojson sample_empty_point_wkt) = sample_empty_point_wkt.
Proof. apply wkt_geojson_wkt_roundtrip. Qed.

(* Explicit expanded form for POINT(1 2) → GeoJSON Point → WKT. *)
Example point_1_2_roundtrip_explicit :
  geojson_to_wkt (wkt_to_geojson (OgcPoint (mkPoint 1 2)))
    = OgcPoint (mkPoint 1 2).
Proof. reflexivity. Qed.

Example point_1_2_geojson_shape :
  wkt_to_geojson (OgcPoint (mkPoint 1 2)) = GJPoint (1, 2).
Proof. reflexivity. Qed.

(* -------------------------------------------------------------------------- *)
(* Axiom audit.                                                               *)
(* -------------------------------------------------------------------------- *)

Print Assumptions wkt_geojson_wkt_roundtrip.
Print Assumptions geojson_wkt_geojson_roundtrip.
Print Assumptions sample_polygon_wkt_geojson_wkt.

(* ============================================================================
   oracle/nts_ffi.ml
   ----------------------------------------------------------------------------
   Phase 5 (extraction toolchain + C# FFI): the in-process callable surface of
   the Coq-extracted kernel.

   `oracle/driver.ml` exposes the same extracted functions over a stdin/stdout
   line protocol (`oracle_bin`, the RocqRefRunner).  That is a SUBPROCESS
   boundary: one fork + two pipe round-trips per predicate call, which is fine
   for differential test corpora but not for production NTS, where orientation
   is called millions of times inside a noding loop.

   This module registers the same extracted entry points as OCaml callbacks so
   `oracle/nts_ffi_stubs.c` can expose them as plain C functions
   (`oracle/nts_ffi.h`), which .NET binds with `DllImport`.  No arithmetic is
   re-implemented here: every function below is a marshalling shim around the
   SAME `Extracted.*` symbol that `driver.ml` calls, so the FFI result is
   bit-identical to the published oracle_bin protocol by construction (and that
   identity is gated by `oracle/gen_ffi_parity_tests.py`).

   Calling convention (uniform, to keep the C side generic):

     - every entry takes ONE `float array` argument (flat doubles);
     - it returns `int` (status/enum code), `float`, or `float array`.

   Enum encodings are the ABI contract and are duplicated in `nts_ffi.h`:

     orient_sign_robust  POS=1  NEG=-1  ZERO=0  NAN=2  UNCERTAIN=3
     orient_sign (naive) POS=1  NEG=-1  ZERO=0  NAN=2
     intersect_sign      NONE=0 POINT=1 COLLINEAR=2 NAN=3 UNCERTAIN=4
     bool                FALSE=0 TRUE=1
     boolean_op          UNION=0 INTERSECTION=1 DIFFERENCE=2 SYMDIFF=3

   NOT part of the trusted proof base: like the rest of `oracle/`, this file is
   glue.  The proofs live in `theories-flocq/`; the extraction overrides that
   make the OCaml floats bit-equal to .NET `double` live in
   `theories-flocq/Validate_binary64_extract.v`.

   AI disclosure: authored with AI assistance (see CONTRIBUTING.md).
   ========================================================================== *)

open Extracted

(* ---------------------------------------------------------------------- *)
(* Marshalling helpers.                                                    *)
(* ---------------------------------------------------------------------- *)

let pt (a : float array) (i : int) : bPoint = { bx = a.(i); by_ = a.(i + 1) }

let code_of_orient_robust = function
  | OrientRPos       ->  1
  | OrientRNeg       -> -1
  | OrientRZero      ->  0
  | OrientRNan       ->  2
  | OrientRUncertain ->  3

let code_of_orient_naive = function
  | OrientPos  ->  1
  | OrientNeg  -> -1
  | OrientZero ->  0
  | OrientNan  ->  2

let code_of_intersect = function
  | IntersectNone      -> 0
  | IntersectPoint     -> 1
  | IntersectCollinear -> 2
  | IntersectNan       -> 3
  | IntersectUncertain -> 4

let code_of_bool b = if b then 1 else 0

let op_of_code = function
  | 0 -> Union
  | 1 -> Intersection
  | 2 -> Difference
  | 3 -> SymDiff
  | n -> invalid_arg (Printf.sprintf "nts_ffi: unknown boolean_op code %d" n)

(* Flat [x0;y0;x1;y1;...] -> bPoint list, and back. *)
let points_of_flat (a : float array) (off : int) (n : int) : bPoint list =
  let rec go i acc =
    if i < 0 then acc
    else go (i - 1) ({ bx = a.(off + (2 * i)); by_ = a.(off + (2 * i) + 1) } :: acc)
  in
  go (n - 1) []

let flat_of_points (ps : bPoint list) : float array =
  let n = List.length ps in
  let out = Array.make (2 * n) 0.0 in
  List.iteri
    (fun i p ->
      out.(2 * i) <- p.bx;
      out.((2 * i) + 1) <- p.by_)
    ps;
  out

(* ---------------------------------------------------------------------- *)
(* Phase 0 -- robust orientation (Orientation_b64.v).                      *)
(* ---------------------------------------------------------------------- *)

(* [| p0x; p0y; p1x; p1y; qx; qy |] *)
let orient_sign_filtered (a : float array) : int =
  code_of_orient_robust (b64_orient_sign_filtered (pt a 0) (pt a 2) (pt a 4))

let orient_sign_naive (a : float array) : int =
  code_of_orient_naive (b64_orient_sign_naive (pt a 0) (pt a 2) (pt a 4))

let orient2d (a : float array) : float = b64_orient2d (pt a 0) (pt a 2) (pt a 4)

(* ---------------------------------------------------------------------- *)
(* Phase 1 -- segment intersection (Intersect_b64.v, Intersect_b64_exact). *)
(* ---------------------------------------------------------------------- *)

(* [| p0x; p0y; p1x; p1y; q0x; q0y; q1x; q1y |] *)
let intersect_sign_filtered (a : float array) : int =
  code_of_intersect
    (b64_intersect_sign_filtered (pt a 0) (pt a 2) (pt a 4) (pt a 6))

(* -> [| present; x; y |], present = 1.0 for Some / 0.0 for None. *)
let intersect_point (a : float array) : float array =
  match b64_intersect_point (pt a 0) (pt a 2) (pt a 4) (pt a 6) with
  | None    -> [| 0.0; Float.nan; Float.nan |]
  | Some bp -> [| 1.0; bp.bx; bp.by_ |]

(* Total projections -- no option wrapper, no pre-filter (Scope C.2-tight). *)
let intersect_point_xy (a : float array) : float array =
  [| b64_intersect_point_x (pt a 0) (pt a 2) (pt a 4) (pt a 6);
     b64_intersect_point_y (pt a 0) (pt a 2) (pt a 4) (pt a 6) |]

(* ---------------------------------------------------------------------- *)
(* Phase 2 -- snap rounding / hot pixels (HotPixel_b64.v et al.).          *)
(* ---------------------------------------------------------------------- *)

(* [| p0x; p0y; p1x; p1y; cx; cy |] -- c is the hot-pixel centre. *)
let passes_through_hot_pixel (a : float array) : int =
  code_of_bool (b64_passes_through_hot_pixel_compute (pt a 0) (pt a 2) (pt a 4))

let passes_through_hot_pixel_halfopen (a : float array) : int =
  code_of_bool
    (b64_passes_through_hot_pixel_halfopen_compute (pt a 0) (pt a 2) (pt a 4))

(* [| x |] -- round-half-to-even to the unit grid. *)
let snap_coord (a : float array) : float = b64_snap_coord a.(0)

(* [| x; scale |] -- C1 power-of-two grid (SnapRoundingScale_b64.v).  Argument
   order follows the Coq definition `b64_snap_coord_scaled (x s : binary64)`. *)
let snap_coord_scaled (a : float array) : float = b64_snap_coord_scaled a.(0) a.(1)

(* ---------------------------------------------------------------------- *)
(* Phase 3 -- overlay labelling (OverlayGraph.v).                          *)
(* ---------------------------------------------------------------------- *)

(* [| op; in_left; in_right |] as doubles. *)
let edge_in_result (a : float array) : int =
  let label = { in_left = a.(1) <> 0.0; in_right = a.(2) <> 0.0 } in
  code_of_bool (edge_in_result (op_of_code (int_of_float a.(0))) label)

(* ---------------------------------------------------------------------- *)
(* Phase 4 -- circular arcs (InCircle_b64, ArcCircle_b64, ArcPixel_b64,    *)
(* ArcLineIntersect_b64_exact).                                            *)
(* ---------------------------------------------------------------------- *)

(* [| ax; ay; bx; by; cx; cy; px; py |] *)
let in_circle (a : float array) : float =
  b64_inCircle (pt a 0) (pt a 2) (pt a 4) (pt a 6)

(* [| sx; sy; mx; my; ex; ey; px; py; qx; qy |] -- arc (S,M,E), chord (P,Q). *)
let chord_crosses_arc_circle (a : float array) : int =
  code_of_bool
    (b64_chord_crosses_arc_circle (pt a 0) (pt a 2) (pt a 4) (pt a 6) (pt a 8))

let arc_line_intersect_xy (a : float array) : float array =
  [| b64_arc_line_intersect_point_x (pt a 0) (pt a 2) (pt a 4) (pt a 6) (pt a 8);
     b64_arc_line_intersect_point_y (pt a 0) (pt a 2) (pt a 4) (pt a 6) (pt a 8) |]

(* [| sx; sy; mx; my; ex; ey; cx; cy; scale |] *)
let arc_passes_through_hot_pixel (a : float array) : int =
  code_of_bool
    (b64_arc_passes_through_hot_pixel (pt a 0) (pt a 2) (pt a 4) (pt a 6) a.(8))

(* ---------------------------------------------------------------------- *)
(* Stage D building blocks (B64_Pff_bridge.v, B64_FastExpansionSum.v).     *)
(* ---------------------------------------------------------------------- *)

(* [| x; y |] -> [| sum; err |] *)
let two_sum (a : float array) : float array =
  let s, e = b64_TwoSum a.(0) a.(1) in
  [| s; e |]

(* [| q; x0; x1; ... |] -> [| qfinal; h0; h1; ... |] *)
let grow_expansion (a : float array) : float array =
  let xs = Array.to_list (Array.sub a 1 (Array.length a - 1)) in
  let hs, qfinal = b64_grow_expansion_aux a.(0) xs in
  Array.of_list (qfinal :: hs)

(* ---------------------------------------------------------------------- *)
(* Simplifier (Validate_binary64.v) -- the Phase 0a consumer path.         *)
(* ---------------------------------------------------------------------- *)

(* [| eps; x0; y0; x1; y1; ... |] -> flat [| x0; y0; ... |] *)
let simplify_perp (a : float array) : float array =
  let n = (Array.length a - 1) / 2 in
  flat_of_points (greedy_simplify_perp_b64 a.(0) (points_of_flat a 1 n))

(* ---------------------------------------------------------------------- *)
(* Registration.  Names are the ABI: `nts_ffi_stubs.c` looks them up with  *)
(* `caml_named_value`, so renaming one is a breaking ABI change.           *)
(* ---------------------------------------------------------------------- *)

let () =
  Callback.register "nts_ffi_orient_sign_filtered" orient_sign_filtered;
  Callback.register "nts_ffi_orient_sign_naive" orient_sign_naive;
  Callback.register "nts_ffi_orient2d" orient2d;
  Callback.register "nts_ffi_intersect_sign_filtered" intersect_sign_filtered;
  Callback.register "nts_ffi_intersect_point" intersect_point;
  Callback.register "nts_ffi_intersect_point_xy" intersect_point_xy;
  Callback.register "nts_ffi_passes_through_hot_pixel" passes_through_hot_pixel;
  Callback.register "nts_ffi_passes_through_hot_pixel_halfopen"
    passes_through_hot_pixel_halfopen;
  Callback.register "nts_ffi_snap_coord" snap_coord;
  Callback.register "nts_ffi_snap_coord_scaled" snap_coord_scaled;
  Callback.register "nts_ffi_edge_in_result" edge_in_result;
  Callback.register "nts_ffi_in_circle" in_circle;
  Callback.register "nts_ffi_chord_crosses_arc_circle" chord_crosses_arc_circle;
  Callback.register "nts_ffi_arc_line_intersect_xy" arc_line_intersect_xy;
  Callback.register "nts_ffi_arc_passes_through_hot_pixel"
    arc_passes_through_hot_pixel;
  Callback.register "nts_ffi_two_sum" two_sum;
  Callback.register "nts_ffi_grow_expansion" grow_expansion;
  Callback.register "nts_ffi_simplify_perp" simplify_perp

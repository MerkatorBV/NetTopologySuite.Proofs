/* ============================================================================
   oracle/nts_ffi.h
   ----------------------------------------------------------------------------
   Phase 5: the C ABI of the Coq-extracted NTS kernel (`libntsrocq`).

   This header IS the ABI contract.  It is consumed by:
     - oracle/ffi_smoke.c        (in-tree C smoke test)
     - oracle/csharp/RocqNative.cs (reference .NET P/Invoke binding)
     - NetTopologySuite.Curve    (the production consumer)

   Every entry point forwards to the SAME extracted symbol that `oracle_bin`
   (the RocqRefRunner stdin/stdout oracle) calls, so results are bit-identical
   to the published oracle protocol.  `oracle/gen_ffi_parity_tests.py` gates
   that identity on every build.

   -- Lifecycle ---------------------------------------------------------------
   Call `nts_rocq_init()` exactly once before any other entry point; it boots
   the OCaml runtime bundled into the shared library.  It is idempotent and
   returns 0 on success.  There is no shutdown call: the runtime lives for the
   life of the process.

   -- Threading ---------------------------------------------------------------
   SINGLE-THREADED CONTRACT.  The bundled OCaml 4.14 runtime is not re-entrant,
   and these stubs do not register foreign threads with it.  All calls
   (including `nts_rocq_init`) must be made from one thread, or serialised by
   the caller under a lock owned for the whole call.  The reference C# binding
   does the latter.

   -- Error handling ----------------------------------------------------------
   The predicates are total: every input, including NaN and infinity, returns a
   defined code (`..._NAN` / `..._UNCERTAIN` where the proofs provide one).
   Only the two variable-length entry points can fail, and they signal it with
   a negative return (buffer too small); they never write past `out_cap`.

   -- Numerics ----------------------------------------------------------------
   Bit-exactness with .NET `double` holds on a 64-bit runtime using SSE2 (x86-64)
   or NEON (ARM64) with round-to-nearest-even -- see the x87 double-rounding
   caveat in theories-flocq/Validate_binary64_extract.v.

   NOT part of the trusted proof base: this is marshalling glue.  The proofs are
   in theories-flocq/; what each predicate is proven to satisfy (and where the
   soundness is conditional) is tabulated in docs/phase5-ffi-abi.md.

   AI disclosure: authored with AI assistance (see CONTRIBUTING.md).
   ========================================================================== */

#ifndef NTS_ROCQ_FFI_H
#define NTS_ROCQ_FFI_H

#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/* ---- ABI version ------------------------------------------------------- */
/* Bumped whenever an entry point changes signature, is removed, or an enum
   encoding changes.  Adding a new entry point does not bump it. */
#define NTS_ROCQ_ABI_VERSION 1

/* ---- Enum encodings (mirrored in nts_ffi.ml and RocqNative.cs) ---------- */

/* b64_orient_sign_filtered (5-valued, Phase 0) */
#define NTS_ORIENT_POS        1
#define NTS_ORIENT_NEG      (-1)
#define NTS_ORIENT_ZERO       0
#define NTS_ORIENT_NAN        2
#define NTS_ORIENT_UNCERTAIN  3   /* filtered predicate only */

/* b64_intersect_sign_filtered (5-valued, Phase 1) */
#define NTS_INTERSECT_NONE       0
#define NTS_INTERSECT_POINT      1
#define NTS_INTERSECT_COLLINEAR  2
#define NTS_INTERSECT_NAN        3
#define NTS_INTERSECT_UNCERTAIN  4

/* boolean_op (Phase 3, OverlayGraph.v constructor order) */
#define NTS_OP_UNION         0
#define NTS_OP_INTERSECTION  1
#define NTS_OP_DIFFERENCE    2
#define NTS_OP_SYMDIFF       3

/* ---- Lifecycle --------------------------------------------------------- */

/* Boots the embedded OCaml runtime.  Idempotent.  Returns 0 on success. */
int32_t nts_rocq_init(void);

/* Returns NTS_ROCQ_ABI_VERSION as compiled into the library, so a consumer can
   check the loaded .so/.dylib/.dll against the header it was built against. */
int32_t nts_rocq_abi_version(void);

/* ---- Phase 0: robust orientation --------------------------------------- */

/* b64_orient_sign_filtered p0 p1 q -- Shewchuk Stage A filter.
   Returns one of NTS_ORIENT_*.  UNCERTAIN means "the filter declines"; it is
   never a wrong sign (that is the Qed-closed part). */
int32_t nts_rocq_orient_sign_filtered(double p0x, double p0y,
                                      double p1x, double p1y,
                                      double qx,  double qy);

/* b64_orient_sign_naive -- unfiltered sign of the raw determinant.  Never
   returns UNCERTAIN, and is NOT robust; provided for differential testing. */
int32_t nts_rocq_orient_sign_naive(double p0x, double p0y,
                                   double p1x, double p1y,
                                   double qx,  double qy);

/* b64_orient2d -- the raw binary64 determinant value. */
double nts_rocq_orient2d(double p0x, double p0y,
                         double p1x, double p1y,
                         double qx,  double qy);

/* ---- Phase 1: segment intersection ------------------------------------- */

/* b64_intersect_sign_filtered p0 p1 q0 q1.  Returns one of NTS_INTERSECT_*. */
int32_t nts_rocq_intersect_sign_filtered(double p0x, double p0y,
                                         double p1x, double p1y,
                                         double q0x, double q0y,
                                         double q1x, double q1y);

/* b64_intersect_point -- option-wrapped intersection point.
   Returns 1 and writes *out_x / *out_y when the predicate says POINT;
   returns 0 and writes NaN otherwise. */
int32_t nts_rocq_intersect_point(double p0x, double p0y,
                                 double p1x, double p1y,
                                 double q0x, double q0y,
                                 double q1x, double q1y,
                                 double *out_x, double *out_y);

/* b64_intersect_point_x / _y -- the TOTAL projections, computed
   unconditionally (no option wrapper, no pre-filter).  Matches the C# port
   that branches on the predicate first and then computes coordinates. */
void nts_rocq_intersect_point_xy(double p0x, double p0y,
                                 double p1x, double p1y,
                                 double q0x, double q0y,
                                 double q1x, double q1y,
                                 double *out_x, double *out_y);

/* ---- Phase 2: snap rounding / hot pixels -------------------------------- */

/* b64_passes_through_hot_pixel_compute -- closed Liang-Barsky filter.
   (cx, cy) is the hot-pixel centre.  Returns 0/1. */
int32_t nts_rocq_passes_through_hot_pixel(double p0x, double p0y,
                                          double p1x, double p1y,
                                          double cx,  double cy);

/* Half-open variant (tight pixel ownership). Returns 0/1. */
int32_t nts_rocq_passes_through_hot_pixel_halfopen(double p0x, double p0y,
                                                   double p1x, double p1y,
                                                   double cx,  double cy);

/* b64_snap_coord -- round half to even onto the unit grid. */
double nts_rocq_snap_coord(double x);

/* b64_snap_coord_scaled x scale -- the C1 power-of-two grid variant.  Argument
   order follows the Coq definition (value first, grid scale second). */
double nts_rocq_snap_coord_scaled(double x, double scale);

/* ---- Phase 3: overlay labelling ----------------------------------------- */

/* edge_in_result op {in_left; in_right}.  `op` is one of NTS_OP_*; the two
   label flags are 0/1.  Returns 0/1.  Any other `op` returns -1. */
int32_t nts_rocq_edge_in_result(int32_t op, int32_t in_left, int32_t in_right);

/* ---- Phase 4: circular arcs --------------------------------------------- */

/* b64_inCircle a b c p -- the in-circle determinant VALUE (sign convention:
   positive iff (a,b,c) is CCW and p is strictly inside its circumcircle). */
double nts_rocq_in_circle(double ax, double ay, double bx, double by,
                          double cx, double cy, double px, double py);

/* b64_chord_crosses_arc_circle (S,M,E) (P,Q) -- inCircle sign-product test.
   SUFFICIENT ONLY: 1 => the chord crosses the arc's circumcircle; 0 is
   inconclusive (both endpoints may be on the same side of a secant). */
int32_t nts_rocq_chord_crosses_arc_circle(double sx, double sy,
                                          double mx, double my,
                                          double ex, double ey,
                                          double px, double py,
                                          double qx, double qy);

/* b64_arc_line_intersect_point_x / _y -- single-root Cramer projection.
   NOT an enumerator: emits inf/NaN on a two-crossing line (issue #224). */
void nts_rocq_arc_line_intersect_xy(double sx, double sy,
                                    double mx, double my,
                                    double ex, double ey,
                                    double px, double py,
                                    double qx, double qy,
                                    double *out_x, double *out_y);

/* b64_arc_passes_through_hot_pixel (S,M,E) centre scale.
   SUFFICIENT ONLY: 1 => the arc passes through the pixel; 0 is inconclusive. */
int32_t nts_rocq_arc_passes_through_hot_pixel(double sx, double sy,
                                              double mx, double my,
                                              double ex, double ey,
                                              double cx, double cy,
                                              double scale);

/* ---- Stage D expansion building blocks ---------------------------------- */

/* b64_TwoSum x y -> (sum, err), the error-free transformation. */
void nts_rocq_two_sum(double x, double y, double *out_sum, double *out_err);

/* b64_grow_expansion_aux q xs -> (hs, qfinal).
   `xs` has `n` entries; the settled components `hs` are written to `out_h`
   (which must hold at least `n` doubles) and `qfinal` to *out_qfinal.
   Returns the number of components written, or -1 if out_cap < n. */
int32_t nts_rocq_grow_expansion(double q, const double *xs, int32_t n,
                                double *out_h, int32_t out_cap,
                                double *out_qfinal);

/* ---- Simplifier (Phase 0a consumer path) -------------------------------- */

/* greedy_simplify_perp_b64 eps pts.
   `xy` holds `n_pts` (x,y) pairs; the kept points are written to `out_xy`,
   which must hold at least `out_cap` pairs (2 * out_cap doubles).
   Returns the number of points written, or -(needed) if out_cap is too small
   (in which case nothing is written). */
int32_t nts_rocq_simplify_perp(double eps, const double *xy, int32_t n_pts,
                               double *out_xy, int32_t out_cap);

#ifdef __cplusplus
} /* extern "C" */
#endif

#endif /* NTS_ROCQ_FFI_H */

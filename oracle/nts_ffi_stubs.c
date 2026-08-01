/* ============================================================================
   oracle/nts_ffi_stubs.c
   ----------------------------------------------------------------------------
   Phase 5: C entry points for the Coq-extracted kernel (see oracle/nts_ffi.h
   for the ABI contract and oracle/nts_ffi.ml for the OCaml side).

   Each stub packs its `double` arguments into a flat OCaml float array, invokes
   the registered callback, and unpacks the result.  No arithmetic happens here:
   every number crossing this boundary was produced by extracted Coq code.

   GC discipline: values held across a `caml_callback` are registered with the
   CAMLparam/CAMLlocal macros, since the callback can allocate and move them.

   AI disclosure: authored with AI assistance (see CONTRIBUTING.md).
   ========================================================================== */

#include <string.h>

#include <caml/mlvalues.h>
#include <caml/memory.h>
#include <caml/alloc.h>
#include <caml/callback.h>

#include "nts_ffi.h"

/* ---------------------------------------------------------------------- */
/* Runtime lifecycle.                                                      */
/* ---------------------------------------------------------------------- */

static int nts_rocq_started = 0;

int32_t nts_rocq_init(void)
{
  static char  arg0[] = "libntsrocq";
  static char *argv[] = { arg0, NULL };

  if (nts_rocq_started) {
    return 0;
  }
  caml_startup(argv);
  nts_rocq_started = 1;
  return 0;
}

int32_t nts_rocq_abi_version(void)
{
  return NTS_ROCQ_ABI_VERSION;
}

/* ---------------------------------------------------------------------- */
/* Generic callback plumbing.                                              */
/* ---------------------------------------------------------------------- */

/* Sentinels returned when a callback name is missing from the library --
   only reachable if nts_ffi.ml and this file drift apart. */
#define NTS_FFI_NO_CALLBACK_INT  (-9999)
#define NTS_FFI_NO_CALLBACK_DBL  ((double)0.0 / (double)0.0)

static value nts_args(const double *v, int n)
{
  CAMLparam0();
  CAMLlocal1(a);
  int i;

  a = caml_alloc(n * Double_wosize, Double_array_tag);
  for (i = 0; i < n; i++) {
    Store_double_field(a, i, v[i]);
  }
  CAMLreturn(a);
}

static int32_t nts_call_int(const char *name, const double *v, int n)
{
  CAMLparam0();
  CAMLlocal2(args, res);
  const value *closure;

  nts_rocq_init();
  closure = caml_named_value(name);
  if (closure == NULL) {
    CAMLreturnT(int32_t, NTS_FFI_NO_CALLBACK_INT);
  }
  args = nts_args(v, n);
  res  = caml_callback(*closure, args);
  CAMLreturnT(int32_t, (int32_t)Int_val(res));
}

static double nts_call_double(const char *name, const double *v, int n)
{
  CAMLparam0();
  CAMLlocal2(args, res);
  const value *closure;

  nts_rocq_init();
  closure = caml_named_value(name);
  if (closure == NULL) {
    CAMLreturnT(double, NTS_FFI_NO_CALLBACK_DBL);
  }
  args = nts_args(v, n);
  res  = caml_callback(*closure, args);
  CAMLreturnT(double, Double_val(res));
}

/* Calls a `float array -> float array` callback.  Copies at most `out_cap`
   doubles into `out` and returns the FULL result length (which may exceed
   out_cap, letting the caller detect truncation). */
static int32_t nts_call_array(const char *name, const double *v, int n,
                              double *out, int out_cap)
{
  CAMLparam0();
  CAMLlocal2(args, res);
  const value *closure;
  int len, i;

  nts_rocq_init();
  closure = caml_named_value(name);
  if (closure == NULL) {
    CAMLreturnT(int32_t, NTS_FFI_NO_CALLBACK_INT);
  }
  args = nts_args(v, n);
  res  = caml_callback(*closure, args);
  len  = (int)(Wosize_val(res) / Double_wosize);
  for (i = 0; i < len && i < out_cap; i++) {
    out[i] = Double_flat_field(res, i);
  }
  CAMLreturnT(int32_t, (int32_t)len);
}

/* ---------------------------------------------------------------------- */
/* Phase 0: robust orientation.                                            */
/* ---------------------------------------------------------------------- */

int32_t nts_rocq_orient_sign_filtered(double p0x, double p0y,
                                      double p1x, double p1y,
                                      double qx,  double qy)
{
  const double v[6] = { p0x, p0y, p1x, p1y, qx, qy };
  return nts_call_int("nts_ffi_orient_sign_filtered", v, 6);
}

int32_t nts_rocq_orient_sign_naive(double p0x, double p0y,
                                   double p1x, double p1y,
                                   double qx,  double qy)
{
  const double v[6] = { p0x, p0y, p1x, p1y, qx, qy };
  return nts_call_int("nts_ffi_orient_sign_naive", v, 6);
}

double nts_rocq_orient2d(double p0x, double p0y,
                         double p1x, double p1y,
                         double qx,  double qy)
{
  const double v[6] = { p0x, p0y, p1x, p1y, qx, qy };
  return nts_call_double("nts_ffi_orient2d", v, 6);
}

int32_t nts_rocq_orient_sign_exact(double p0x, double p0y,
                                   double p1x, double p1y,
                                   double qx,  double qy)
{
  const double v[6] = { p0x, p0y, p1x, p1y, qx, qy };
  return nts_call_int("nts_ffi_orient_sign_exact", v, 6);
}

/* ---------------------------------------------------------------------- */
/* Phase 1: segment intersection.                                          */
/* ---------------------------------------------------------------------- */

int32_t nts_rocq_intersect_sign_filtered(double p0x, double p0y,
                                         double p1x, double p1y,
                                         double q0x, double q0y,
                                         double q1x, double q1y)
{
  const double v[8] = { p0x, p0y, p1x, p1y, q0x, q0y, q1x, q1y };
  return nts_call_int("nts_ffi_intersect_sign_filtered", v, 8);
}

int32_t nts_rocq_intersect_point(double p0x, double p0y,
                                 double p1x, double p1y,
                                 double q0x, double q0y,
                                 double q1x, double q1y,
                                 double *out_x, double *out_y)
{
  const double v[8] = { p0x, p0y, p1x, p1y, q0x, q0y, q1x, q1y };
  double r[3];
  int32_t len = nts_call_array("nts_ffi_intersect_point", v, 8, r, 3);

  if (len != 3) {
    return -1;
  }
  if (out_x != NULL) { *out_x = r[1]; }
  if (out_y != NULL) { *out_y = r[2]; }
  return (r[0] != 0.0) ? 1 : 0;
}

void nts_rocq_intersect_point_xy(double p0x, double p0y,
                                 double p1x, double p1y,
                                 double q0x, double q0y,
                                 double q1x, double q1y,
                                 double *out_x, double *out_y)
{
  const double v[8] = { p0x, p0y, p1x, p1y, q0x, q0y, q1x, q1y };
  double r[2];

  if (nts_call_array("nts_ffi_intersect_point_xy", v, 8, r, 2) != 2) {
    return;
  }
  if (out_x != NULL) { *out_x = r[0]; }
  if (out_y != NULL) { *out_y = r[1]; }
}

/* ---------------------------------------------------------------------- */
/* Phase 2: snap rounding / hot pixels.                                    */
/* ---------------------------------------------------------------------- */

int32_t nts_rocq_passes_through_hot_pixel(double p0x, double p0y,
                                          double p1x, double p1y,
                                          double cx,  double cy)
{
  const double v[6] = { p0x, p0y, p1x, p1y, cx, cy };
  return nts_call_int("nts_ffi_passes_through_hot_pixel", v, 6);
}

int32_t nts_rocq_passes_through_hot_pixel_halfopen(double p0x, double p0y,
                                                   double p1x, double p1y,
                                                   double cx,  double cy)
{
  const double v[6] = { p0x, p0y, p1x, p1y, cx, cy };
  return nts_call_int("nts_ffi_passes_through_hot_pixel_halfopen", v, 6);
}

double nts_rocq_snap_coord(double x)
{
  const double v[1] = { x };
  return nts_call_double("nts_ffi_snap_coord", v, 1);
}

double nts_rocq_snap_coord_scaled(double x, double scale)
{
  const double v[2] = { x, scale };
  return nts_call_double("nts_ffi_snap_coord_scaled", v, 2);
}

/* ---------------------------------------------------------------------- */
/* Phase 3: overlay labelling.                                             */
/* ---------------------------------------------------------------------- */

int32_t nts_rocq_edge_in_result(int32_t op, int32_t in_left, int32_t in_right)
{
  double v[3];

  if (op < NTS_OP_UNION || op > NTS_OP_SYMDIFF) {
    return -1;
  }
  v[0] = (double)op;
  v[1] = in_left  ? 1.0 : 0.0;
  v[2] = in_right ? 1.0 : 0.0;
  return nts_call_int("nts_ffi_edge_in_result", v, 3);
}

/* ---------------------------------------------------------------------- */
/* Phase 4: circular arcs.                                                 */
/* ---------------------------------------------------------------------- */

double nts_rocq_in_circle(double ax, double ay, double bx, double by,
                          double cx, double cy, double px, double py)
{
  const double v[8] = { ax, ay, bx, by, cx, cy, px, py };
  return nts_call_double("nts_ffi_in_circle", v, 8);
}

int32_t nts_rocq_chord_crosses_arc_circle(double sx, double sy,
                                          double mx, double my,
                                          double ex, double ey,
                                          double px, double py,
                                          double qx, double qy)
{
  const double v[10] = { sx, sy, mx, my, ex, ey, px, py, qx, qy };
  return nts_call_int("nts_ffi_chord_crosses_arc_circle", v, 10);
}

void nts_rocq_arc_line_intersect_xy(double sx, double sy,
                                    double mx, double my,
                                    double ex, double ey,
                                    double px, double py,
                                    double qx, double qy,
                                    double *out_x, double *out_y)
{
  const double v[10] = { sx, sy, mx, my, ex, ey, px, py, qx, qy };
  double r[2];

  if (nts_call_array("nts_ffi_arc_line_intersect_xy", v, 10, r, 2) != 2) {
    return;
  }
  if (out_x != NULL) { *out_x = r[0]; }
  if (out_y != NULL) { *out_y = r[1]; }
}

int32_t nts_rocq_arc_passes_through_hot_pixel(double sx, double sy,
                                              double mx, double my,
                                              double ex, double ey,
                                              double cx, double cy,
                                              double scale)
{
  const double v[9] = { sx, sy, mx, my, ex, ey, cx, cy, scale };
  return nts_call_int("nts_ffi_arc_passes_through_hot_pixel", v, 9);
}

/* ---------------------------------------------------------------------- */
/* Stage D expansion building blocks.                                      */
/* ---------------------------------------------------------------------- */

void nts_rocq_two_sum(double x, double y, double *out_sum, double *out_err)
{
  const double v[2] = { x, y };
  double r[2];

  if (nts_call_array("nts_ffi_two_sum", v, 2, r, 2) != 2) {
    return;
  }
  if (out_sum != NULL) { *out_sum = r[0]; }
  if (out_err != NULL) { *out_err = r[1]; }
}

int32_t nts_rocq_grow_expansion(double q, const double *xs, int32_t n,
                                double *out_h, int32_t out_cap,
                                double *out_qfinal)
{
  CAMLparam0();
  CAMLlocal2(args, res);
  const value *closure;
  int32_t len, i;

  if (n < 0 || (xs == NULL && n > 0)) {
    CAMLreturnT(int32_t, -1);
  }

  nts_rocq_init();
  closure = caml_named_value("nts_ffi_grow_expansion");
  if (closure == NULL) {
    CAMLreturnT(int32_t, NTS_FFI_NO_CALLBACK_INT);
  }

  /* Pack [| q; xs... |] without a temporary heap buffer on the C side. */
  args = caml_alloc((n + 1) * Double_wosize, Double_array_tag);
  Store_double_field(args, 0, q);
  for (i = 0; i < n; i++) {
    Store_double_field(args, i + 1, xs[i]);
  }

  res = caml_callback(*closure, args);
  /* res = [| qfinal; h0; ... |] */
  len = (int32_t)(Wosize_val(res) / Double_wosize) - 1;
  if (len > out_cap) {
    CAMLreturnT(int32_t, -1);
  }
  if (out_qfinal != NULL) {
    *out_qfinal = Double_flat_field(res, 0);
  }
  for (i = 0; i < len; i++) {
    out_h[i] = Double_flat_field(res, i + 1);
  }
  CAMLreturnT(int32_t, len);
}

/* ---------------------------------------------------------------------- */
/* Simplifier.                                                             */
/* ---------------------------------------------------------------------- */

int32_t nts_rocq_simplify_perp(double eps, const double *xy, int32_t n_pts,
                               double *out_xy, int32_t out_cap)
{
  CAMLparam0();
  CAMLlocal2(args, res);
  const value *closure;
  int32_t len, out_pts, i;

  if (n_pts < 0 || (xy == NULL && n_pts > 0)) {
    CAMLreturnT(int32_t, -1);
  }

  nts_rocq_init();
  closure = caml_named_value("nts_ffi_simplify_perp");
  if (closure == NULL) {
    CAMLreturnT(int32_t, NTS_FFI_NO_CALLBACK_INT);
  }

  args = caml_alloc(((2 * n_pts) + 1) * Double_wosize, Double_array_tag);
  Store_double_field(args, 0, eps);
  for (i = 0; i < 2 * n_pts; i++) {
    Store_double_field(args, i + 1, xy[i]);
  }

  res     = caml_callback(*closure, args);
  len     = (int32_t)(Wosize_val(res) / Double_wosize);
  out_pts = len / 2;
  if (out_pts > out_cap) {
    CAMLreturnT(int32_t, -out_pts);
  }
  for (i = 0; i < len; i++) {
    out_xy[i] = Double_flat_field(res, i);
  }
  CAMLreturnT(int32_t, out_pts);
}

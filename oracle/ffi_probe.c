/* ============================================================================
   oracle/ffi_probe.c
   ----------------------------------------------------------------------------
   Phase 5: a thin C driver over `libntsrocq` (oracle/nts_ffi.h), used by
   `oracle/gen_ffi_parity_tests.py` to check that the in-process FFI returns
   BIT-IDENTICAL answers to the `oracle_bin` stdin/stdout protocol.

   It is deliberately dumb: no arithmetic, no parsing beyond `strtod`, and it
   prints doubles as raw IEEE 754 bit patterns (16 hex digits) so the
   comparison cannot be blurred by decimal or hex-float formatting differences
   between OCaml's `%h` and C's `%a`.

   Usage:  ffi_probe MODE < numbers
           (whitespace-separated doubles on stdin; one result line on stdout)

   Output grammar per mode is documented beside each handler; integers print as
   decimal, doubles as `#<16 hex digits>`.

   AI disclosure: authored with AI assistance (see CONTRIBUTING.md).
   ========================================================================== */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "nts_ffi.h"

#define MAX_VALS 4096

static double vals[MAX_VALS];
static int    n_vals = 0;

static void read_vals(void)
{
  char tok[128];

  while (n_vals < MAX_VALS && scanf("%127s", tok) == 1) {
    vals[n_vals++] = strtod(tok, NULL);
  }
}

static void need(int n, const char *mode)
{
  if (n_vals < n) {
    fprintf(stderr, "ffi_probe: %s needs %d doubles, got %d\n", mode, n, n_vals);
    exit(2);
  }
}

/* Print a double as its raw bit pattern -- exact, formatting-independent. */
static void put_d(double d)
{
  unsigned long long bits;

  memcpy(&bits, &d, sizeof(bits));
  printf(" #%016llx", bits);
}

int main(int argc, char **argv)
{
  const char *mode;

  if (argc < 2) {
    fprintf(stderr, "usage: ffi_probe MODE < numbers\n");
    return 2;
  }
  mode = argv[1];

  if (nts_rocq_init() != 0) {
    fprintf(stderr, "ffi_probe: nts_rocq_init failed\n");
    return 2;
  }
  if (nts_rocq_abi_version() != NTS_ROCQ_ABI_VERSION) {
    fprintf(stderr, "ffi_probe: ABI mismatch (lib %d, header %d)\n",
            (int)nts_rocq_abi_version(), NTS_ROCQ_ABI_VERSION);
    return 2;
  }

  read_vals();

  /* "<sign_code> #<orient2d bits>" */
  if (strcmp(mode, "ORIENT_FILTERED") == 0) {
    need(6, mode);
    printf("%d", (int)nts_rocq_orient_sign_filtered(vals[0], vals[1], vals[2],
                                                    vals[3], vals[4], vals[5]));
    put_d(nts_rocq_orient2d(vals[0], vals[1], vals[2], vals[3], vals[4], vals[5]));
    printf("\n");
    return 0;
  }

  /* "<naive_sign_code> #<orient2d bits>" */
  if (strcmp(mode, "ORIENT") == 0) {
    need(6, mode);
    printf("%d", (int)nts_rocq_orient_sign_naive(vals[0], vals[1], vals[2],
                                                 vals[3], vals[4], vals[5]));
    put_d(nts_rocq_orient2d(vals[0], vals[1], vals[2], vals[3], vals[4], vals[5]));
    printf("\n");
    return 0;
  }

  /* "<sign_code>" -- exact full-plane sign (escalation path); code 2 (NAN)
     on any non-finite input, matching oracle_bin's ORIENT_EXACT[_EXTRACTED]
     "NAN" answer. */
  if (strcmp(mode, "ORIENT_EXACT") == 0) {
    need(6, mode);
    printf("%d\n", (int)nts_rocq_orient_sign_exact(vals[0], vals[1], vals[2],
                                                   vals[3], vals[4], vals[5]));
    return 0;
  }

  /* "<intersect_code>" */
  if (strcmp(mode, "INTERSECT_FILTERED") == 0) {
    need(8, mode);
    printf("%d\n", (int)nts_rocq_intersect_sign_filtered(
                       vals[0], vals[1], vals[2], vals[3],
                       vals[4], vals[5], vals[6], vals[7]));
    return 0;
  }

  /* "<present> [#x #y]" -- coordinates only when present. */
  if (strcmp(mode, "INTERSECT_POINT_FILTERED") == 0) {
    double x = 0.0, y = 0.0;
    int32_t present;

    need(8, mode);
    present = nts_rocq_intersect_point(vals[0], vals[1], vals[2], vals[3],
                                       vals[4], vals[5], vals[6], vals[7], &x, &y);
    printf("%d", (int)present);
    if (present == 1) {
      put_d(x);
      put_d(y);
    }
    printf("\n");
    return 0;
  }

  /* "#x #y" */
  if (strcmp(mode, "INTERSECT_POINT_XY") == 0) {
    double x = 0.0, y = 0.0;

    need(8, mode);
    nts_rocq_intersect_point_xy(vals[0], vals[1], vals[2], vals[3],
                                vals[4], vals[5], vals[6], vals[7], &x, &y);
    printf("XY");
    put_d(x);
    put_d(y);
    printf("\n");
    return 0;
  }

  /* "<0|1>" */
  if (strcmp(mode, "PASSES_THROUGH_FILTER") == 0) {
    need(6, mode);
    printf("%d\n", (int)nts_rocq_passes_through_hot_pixel(
                       vals[0], vals[1], vals[2], vals[3], vals[4], vals[5]));
    return 0;
  }

  if (strcmp(mode, "PASSES_THROUGH_HALFOPEN") == 0) {
    need(6, mode);
    printf("%d\n", (int)nts_rocq_passes_through_hot_pixel_halfopen(
                       vals[0], vals[1], vals[2], vals[3], vals[4], vals[5]));
    return 0;
  }

  /* "#snapped_x #snapped_y" -- input: scale, x, y (SNAP_SCALED order). */
  if (strcmp(mode, "SNAP_SCALED") == 0) {
    need(3, mode);
    printf("SNAP");
    put_d(nts_rocq_snap_coord_scaled(vals[1], vals[0]));
    put_d(nts_rocq_snap_coord_scaled(vals[2], vals[0]));
    printf("\n");
    return 0;
  }

  /* "#snapped" -- unit-grid round-half-to-even. */
  if (strcmp(mode, "SNAP_COORD") == 0) {
    need(1, mode);
    printf("SNAP");
    put_d(nts_rocq_snap_coord(vals[0]));
    printf("\n");
    return 0;
  }

  /* "<0|1>" -- input: op code, in_left, in_right. */
  if (strcmp(mode, "EDGE_IN_RESULT") == 0) {
    need(3, mode);
    printf("%d\n", (int)nts_rocq_edge_in_result((int32_t)vals[0],
                                                (int32_t)vals[1],
                                                (int32_t)vals[2]));
    return 0;
  }

  /* "#determinant" */
  if (strcmp(mode, "INCIRCLE_SIGN") == 0) {
    need(8, mode);
    printf("IC");
    put_d(nts_rocq_in_circle(vals[0], vals[1], vals[2], vals[3],
                             vals[4], vals[5], vals[6], vals[7]));
    printf("\n");
    return 0;
  }

  /* "<0|1>" */
  if (strcmp(mode, "ARC_CHORD_CROSSES_CIRCLE") == 0) {
    need(10, mode);
    printf("%d\n", (int)nts_rocq_chord_crosses_arc_circle(
                       vals[0], vals[1], vals[2], vals[3], vals[4],
                       vals[5], vals[6], vals[7], vals[8], vals[9]));
    return 0;
  }

  /* "#x #y" */
  if (strcmp(mode, "ARC_LINE_XY") == 0) {
    double x = 0.0, y = 0.0;

    need(10, mode);
    nts_rocq_arc_line_intersect_xy(vals[0], vals[1], vals[2], vals[3], vals[4],
                                   vals[5], vals[6], vals[7], vals[8], vals[9],
                                   &x, &y);
    printf("XY");
    put_d(x);
    put_d(y);
    printf("\n");
    return 0;
  }

  /* "<0|1>" -- input: S, M, E, centre, scale. */
  if (strcmp(mode, "ARC_PASSES_THROUGH_PIXEL") == 0) {
    need(9, mode);
    printf("%d\n", (int)nts_rocq_arc_passes_through_hot_pixel(
                       vals[0], vals[1], vals[2], vals[3], vals[4],
                       vals[5], vals[6], vals[7], vals[8]));
    return 0;
  }

  /* "#sum #err" */
  if (strcmp(mode, "TWOSUM") == 0) {
    double s = 0.0, e = 0.0;

    need(2, mode);
    nts_rocq_two_sum(vals[0], vals[1], &s, &e);
    printf("TS");
    put_d(s);
    put_d(e);
    printf("\n");
    return 0;
  }

  /* "#qfinal #h0 #h1 ..." -- input: q, then the expansion components. */
  if (strcmp(mode, "GROW_EXPANSION") == 0) {
    double out_h[MAX_VALS];
    double qfinal = 0.0;
    int32_t k, i;

    need(1, mode);
    k = nts_rocq_grow_expansion(vals[0], vals + 1, n_vals - 1, out_h,
                                MAX_VALS, &qfinal);
    if (k < 0) {
      fprintf(stderr, "ffi_probe: grow_expansion failed (%d)\n", (int)k);
      return 2;
    }
    printf("GE");
    put_d(qfinal);
    for (i = 0; i < k; i++) {
      put_d(out_h[i]);
    }
    printf("\n");
    return 0;
  }

  /* "<n> #x0 #y0 #x1 #y1 ..." -- input: eps, then the (x,y) pairs. */
  if (strcmp(mode, "SIMPLIFY") == 0) {
    double out_xy[MAX_VALS];
    int32_t k, i;

    need(1, mode);
    k = nts_rocq_simplify_perp(vals[0], vals + 1, (n_vals - 1) / 2, out_xy,
                               MAX_VALS / 2);
    if (k < 0) {
      fprintf(stderr, "ffi_probe: simplify buffer too small (need %d)\n", (int)-k);
      return 2;
    }
    printf("%d", (int)k);
    for (i = 0; i < 2 * k; i++) {
      put_d(out_xy[i]);
    }
    printf("\n");
    return 0;
  }

  fprintf(stderr, "ffi_probe: unknown mode: %s\n", mode);
  return 2;
}

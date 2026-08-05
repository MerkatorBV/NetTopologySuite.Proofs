/* ============================================================================
   oracle/scout_incircle_stubs.c
   ----------------------------------------------------------------------------
   Minimal C ABI for the mesh in-circle scout: only
     nts_rocq_init / nts_rocq_abi_version / nts_rocq_in_circle
   matching the production signatures in nts_ffi.h for those three entries.

   AI disclosure: authored with AI assistance (see CONTRIBUTING.md).
   ========================================================================== */

#include <string.h>

#include <caml/mlvalues.h>
#include <caml/memory.h>
#include <caml/alloc.h>
#include <caml/callback.h>

#include "nts_ffi.h"

static int nts_rocq_started = 0;

int32_t nts_rocq_init(void)
{
  static char  arg0[] = "libscout_incircle";
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

double nts_rocq_in_circle(double ax, double ay, double bx, double by,
                          double cx, double cy, double px, double py)
{
  const double v[8] = { ax, ay, bx, by, cx, cy, px, py };
  return nts_call_double("nts_ffi_in_circle", v, 8);
}

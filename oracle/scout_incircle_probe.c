/* ============================================================================
   oracle/scout_incircle_probe.c
   ----------------------------------------------------------------------------
   Thin driver over the scout in-circle library (nts_rocq_in_circle).
   Same output style as ffi_probe for INCIRCLE_SIGN: "IC #<16 hex digits>".

   Usage:  scout_incircle_probe INCIRCLE_SIGN < 8 doubles

   AI disclosure: authored with AI assistance (see CONTRIBUTING.md).
   ========================================================================== */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "nts_ffi.h"

static double vals[16];
static int n_vals = 0;

static void read_vals(void)
{
  char tok[128];
  while (n_vals < 16 && scanf("%127s", tok) == 1) {
    vals[n_vals++] = strtod(tok, NULL);
  }
}

static void put_d(double d)
{
  unsigned long long bits;
  memcpy(&bits, &d, sizeof(bits));
  printf(" #%016llx", (unsigned long long)bits);
}

int main(int argc, char **argv)
{
  if (argc < 2) {
    fprintf(stderr, "usage: scout_incircle_probe INCIRCLE_SIGN < 8 doubles\n");
    return 2;
  }
  if (strcmp(argv[1], "INCIRCLE_SIGN") != 0) {
    fprintf(stderr, "scout_incircle_probe: only INCIRCLE_SIGN supported\n");
    return 2;
  }
  if (nts_rocq_init() != 0) {
    fprintf(stderr, "scout_incircle_probe: nts_rocq_init failed\n");
    return 2;
  }
  if (nts_rocq_abi_version() != NTS_ROCQ_ABI_VERSION) {
    fprintf(stderr, "scout_incircle_probe: ABI mismatch\n");
    return 2;
  }
  read_vals();
  if (n_vals < 8) {
    fprintf(stderr, "scout_incircle_probe: need 8 doubles, got %d\n", n_vals);
    return 2;
  }
  printf("IC");
  put_d(nts_rocq_in_circle(vals[0], vals[1], vals[2], vals[3],
                           vals[4], vals[5], vals[6], vals[7]));
  printf("\n");
  return 0;
}

(* ============================================================================
   oracle/scout_incircle_ffi.ml
   ----------------------------------------------------------------------------
   Minimal Phase-5-style FFI surface for the mesh in-circle scout lane.

   Registers only `b64_inCircle` (the same extracted symbol that
   `oracle_bin` INCIRCLE_SIGN and production `nts_rocq_in_circle` use).
   Full `nts_ffi.ml` currently needs a fresher extraction (e.g.
   `b64_orient2d_exact`); this scout library does not.

   Bit-identity with oracle_bin is the same construction as Phase 5:
   one extracted symbol, two call paths (subprocess protocol vs C ABI).

   AI disclosure: authored with AI assistance (see CONTRIBUTING.md).
   ========================================================================== *)

open Extracted

let pt (a : float array) (i : int) : bPoint = { bx = a.(i); by_ = a.(i + 1) }

(* [| ax; ay; bx; by; cx; cy; px; py |] *)
let in_circle (a : float array) : float =
  b64_inCircle (pt a 0) (pt a 2) (pt a 4) (pt a 6)

let () = Callback.register "nts_ffi_in_circle" in_circle

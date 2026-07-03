(* ==========================================================================
   CornerCorridorBridge.v

   [H-bridge attack, C-3e step 1] The algebraic bridge between the corner
   connector's SHORT-RANGE construction and the corridor's LONG-RANGE
   one: for a non-horizontal dart `d`, the corner samples at its two
   endpoints -- `corner_sample_out (ddir d)` at `dbase d`, `corner_sample_in
   (point_diff (dbase d) (dtip d))` at `dtip d` -- are, for EVERY choice
   of `(rho, delta)`, EXACTLY a point on d's own WEST or EAST corridor
   (`JCTCorridor.corridor` / `MirrorCorridor.corridor_east`), at the
   height the sample's own `(rho, delta)` produces.

   Why this holds and why it picks a definite side: `d`'s carrier line
   through `dbase d` has slope `vx (ddir d) / vy (ddir d)`, so the
   corner sample's `x`-coordinate at its own height differs from the
   carrier's value there by EXACTLY `delta * |ddir d|^2 / vy (ddir d)`
   -- a pure consequence of `{u, perpL u}` being an orthogonal basis
   (no case split needed for the identity itself, only `vy (ddir d) <>
   0`, i.e. `d` non-horizontal).  The SIGN of that quantity is pinned by
   `d`'s own ascending/descending status: `vy (ddir d) < 0` (descending)
   gives a POSITIVE westward offset (matches `corridor`); `vy (ddir d) >
   0` (ascending) gives EXACTLY the corresponding eastward offset
   (matches `corridor_east`) -- the same dichotomy already documented at
   `MirrorCorridor.v`'s header ("right-of-travel is west on a descent
   and east on an ascent"), now verified to be the SAME side at BOTH of
   `d`'s endpoints (it is the same line throughout).  This is what lets
   C-3e's straddle tie-in reuse the corner connector's OWN sample points
   as corridor endpoints, with no separate "meeting hop" needed at the
   algebraic level.

   Pure vector/field algebra; no `Admitted` / `Axiom` / `Parameter`;
   allowlist axioms only.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
   ========================================================================== *)

From Stdlib Require Import Reals Lra List.
From NTS.Proofs Require Import Distance Overlay Vec Azimuth Dart
                               DartAngularOrder SectorPath CornerSamples
                               CornerConnector JCTCorridor MirrorCorridor.

Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  At `dbase d`: `corner_sample_out (ddir d)` sits on d's corridor.        *)
(* -------------------------------------------------------------------------- *)

Lemma corner_sample_out_on_corridor_west :
  forall (d : Dart) (rho delta : R),
    vy (ddir d) < 0 ->
    point_at (dbase d) (corner_sample_out (ddir d) rho delta)
      = corridor d
          (delta * (vx (ddir d) * vx (ddir d) + vy (ddir d) * vy (ddir d))
             / (- vy (ddir d)))
          (py (dbase d) + (rho * vy (ddir d) - delta * vx (ddir d))).
Proof.
  intros [[xa ya] [xb yb]] rho delta Hneg.
  cbv [ddir dbase dtip point_diff point_at corner_sample_out
       vadd vscale vneg vperpL corridor edge_x_at fst snd vx vy px py]
    in *.
  assert (Hnh : yb - ya <> 0) by lra.
  f_equal; [ | ring ].
  field; lra.
Qed.

Lemma corner_sample_out_on_corridor_east :
  forall (d : Dart) (rho delta : R),
    vy (ddir d) > 0 ->
    point_at (dbase d) (corner_sample_out (ddir d) rho delta)
      = corridor_east d
          (delta * (vx (ddir d) * vx (ddir d) + vy (ddir d) * vy (ddir d))
             / vy (ddir d))
          (py (dbase d) + (rho * vy (ddir d) - delta * vx (ddir d))).
Proof.
  intros [[xa ya] [xb yb]] rho delta Hpos.
  cbv [ddir dbase dtip point_diff point_at corner_sample_out
       vadd vscale vneg vperpL corridor_east edge_x_at fst snd vx vy px py]
    in *.
  assert (Hnh : yb - ya <> 0) by lra.
  f_equal; [ | ring ].
  field; lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  At `dtip d`: `corner_sample_in (point_diff (dbase d) (dtip d))` sits    *)
(*     on the SAME corridor, on the SAME side (it is the same line).          *)
(* -------------------------------------------------------------------------- *)

Lemma corner_sample_in_on_corridor_west :
  forall (d : Dart) (rho delta : R),
    vy (ddir d) < 0 ->
    point_at (dtip d) (corner_sample_in (point_diff (dbase d) (dtip d)) rho delta)
      = corridor d
          (delta * (vx (ddir d) * vx (ddir d) + vy (ddir d) * vy (ddir d))
             / (- vy (ddir d)))
          (py (dtip d) + (- rho * vy (ddir d) - delta * vx (ddir d))).
Proof.
  intros [[xa ya] [xb yb]] rho delta Hneg.
  cbv [ddir dbase dtip point_diff point_at corner_sample_in
       vadd vscale vperpL corridor edge_x_at fst snd vx vy px py]
    in *.
  assert (Hnh : ya - yb <> 0) by lra.
  f_equal; [ | ring ].
  field; lra.
Qed.

Lemma corner_sample_in_on_corridor_east :
  forall (d : Dart) (rho delta : R),
    vy (ddir d) > 0 ->
    point_at (dtip d) (corner_sample_in (point_diff (dbase d) (dtip d)) rho delta)
      = corridor_east d
          (delta * (vx (ddir d) * vx (ddir d) + vy (ddir d) * vy (ddir d))
             / vy (ddir d))
          (py (dtip d) + (- rho * vy (ddir d) - delta * vx (ddir d))).
Proof.
  intros [[xa ya] [xb yb]] rho delta Hpos.
  cbv [ddir dbase dtip point_diff point_at corner_sample_in
       vadd vscale vperpL corridor_east edge_x_at fst snd vx vy px py]
    in *.
  assert (Hnh : ya - yb <> 0) by lra.
  f_equal; [ | ring ].
  field; lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Axiom audit.  Pure vector/field algebra; allowlist axioms only.             *)
(* -------------------------------------------------------------------------- *)

Print Assumptions corner_sample_out_on_corridor_west.
Print Assumptions corner_sample_out_on_corridor_east.
Print Assumptions corner_sample_in_on_corridor_west.
Print Assumptions corner_sample_in_on_corridor_east.

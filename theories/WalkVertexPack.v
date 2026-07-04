(* ==========================================================================
   WalkVertexPack.v

   [H-bridge attack, C-3f discharge rung D-4a(i)] PER-VERTEX PACKAGING,
   the OFF-RING case: at a walk vertex in the ring complement, the D-2
   corner threshold holds with NO incident-edge bookkeeping at all.

   The trick: `walk_corner_threshold` parameterizes the two pruned
   slots by points `a`, `b`; choosing `a := b := v` makes
     - the pruned-clearance hypothesis VACUOUSLY total: `v` is off
       EVERY ring edge because it is in the complement
       (`off_ring_vertex_clearance` -- an on-edge witness would be a
       `ring_image` witness);
     - both germ-exclusion hypotheses free: `point_diff v v = vzero`,
       and the zero vector is never strictly inside an open sector
       (`vzero_not_in_sector`, both certificate crosses vanish).
   So the only remaining input is the gap nondegeneracy
   `vcross u1 u2 <> 0`, which the walk supplies from `fan_ok`'s
   pairwise nonparallelism (`cross_nonzero`).

   The ON-RING case -- identifying the two incident chain edges at a
   cycle vertex and discharging the pruned clearance from the
   twin-aware guards -- is D-4a(ii), the next rung.

   No `Admitted` / `Axiom` / `Parameter`; allowlist axioms only.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
   ========================================================================== *)

From Stdlib Require Import Reals Lra List.
From NTS.Proofs Require Import Distance Overlay OverlayGraph Vec Azimuth
                               Direction Dart DartAngularOrder
                               PointInRingTangents JordanCurveSeam JCT
                               JCTHugStep RingClearance SectorPath
                               CornerSamples CornerConnector FanGapSector
                               FanCorner WalkCorners.

Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  The two vacuous inputs.                                                 *)
(* -------------------------------------------------------------------------- *)

(* A complement vertex is off EVERY ring edge -- the pruned-clearance
   hypothesis holds for any slot choice. *)
Lemma off_ring_vertex_clearance :
  forall (r : Ring) (v a b : Point),
    ring_complement r v ->
    forall f, In f (ring_edges r) -> f <> (a, v) -> f <> (v, b) ->
      ~ on_edge f v.
Proof.
  intros r v a b Hcomp f Hf _ _ [s [Hs [Hx Hy]]].
  apply Hcomp.
  exists f, s.
  split; [ exact Hf | ].
  split; [ exact Hs | ].
  split; [ exact Hx | exact Hy ].
Qed.

(* The zero vector is never strictly inside an open sector: both
   certificate crosses vanish. *)
Lemma vzero_not_in_sector :
  forall u1 u2 : Vec, ~ in_open_sector u1 u2 vzero.
Proof.
  intros u1 u2 Hin.
  unfold in_open_sector in Hin.
  rewrite vcross_zero_l, vcross_zero_r in Hin.
  destruct Hin as [[_ [H1 _]] | [_ [H1 | H1]]]; lra.
Qed.

Lemma point_diff_self : forall v : Point, point_diff v v = vzero.
Proof.
  intros [x y]. unfold point_diff, vzero. cbn. f_equal; ring.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  The off-ring corner threshold.                                          *)
(* -------------------------------------------------------------------------- *)

Theorem off_ring_corner_threshold :
  forall (r : Ring) (v : Point) (u1 u2 : Vec),
    no_horizontal_edges r ->
    ring_complement r v ->
    vcross u1 u2 <> 0 ->
    exists t rho_factor : R,
      0 < t /\ 0 < rho_factor /\
      forall delta, 0 < delta < t ->
        connected_in_complement_cont r
          (point_at v (corner_sample_in u1 (rho_factor * delta) delta))
          (point_at v (corner_sample_out u2 (rho_factor * delta) delta)).
Proof.
  intros r v u1 u2 Hnoh Hcomp Hcne.
  apply (walk_corner_threshold r v v v u1 u2 Hnoh).
  - exact (off_ring_vertex_clearance r v v v Hcomp).
  - rewrite point_diff_self. apply vzero_not_in_sector.
  - rewrite point_diff_self. apply vzero_not_in_sector.
  - exact Hcne.
Qed.

(* -------------------------------------------------------------------------- *)
(* Axiom audit.  Vacuous-slot packaging; allowlist axioms only.                *)
(* -------------------------------------------------------------------------- *)

Print Assumptions off_ring_vertex_clearance.
Print Assumptions off_ring_corner_threshold.

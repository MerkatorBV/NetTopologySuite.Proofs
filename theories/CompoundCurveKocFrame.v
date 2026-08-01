(* ============================================================================
   NetTopologySuite.Proofs.CompoundCurveKocFrame
   ----------------------------------------------------------------------------
   Placing the compound-curve design frame into the national grid
   (Koc 2015, §7-§8: equations (37)-(41)) -- part 2 of CompoundCurveKoc.v.

   THE REAL-WORLD PROBLEM, CONTINUED.  Part 1 mechanised the in-frame
   geometry: transitions, arcs, tangency.  But a design that lives only in
   the local frame stakes out nothing.  The last step of Koc's pipeline is
   to PIN the local coordinate system to the national grid ("system 2000"):

     1. inside the local frame, intersect the two symmetric main directions
        (slopes -m and +m, m = tan(alpha/2)) to get the vertex W and its
        distance OW from the frame origin (eqs (37)-(39));
     2. in the grid, walk that same distance OW from the surveyed vertex
        along the first main direction (X = A1 + B1*Y) to place the frame
        origin O -- the point every stakeout coordinate is generated from
        (eqs (40),(41)).

   A wrong vertex or a wrong walk direction shifts the ENTIRE designed
   alignment along the old track axis: the geometry is internally perfect
   and globally misplaced -- the kind of error only caught when the
   setting-out crew finds the new curve starting metres from where the
   survey said it should.

   WHAT IS MECHANISED (paper eq |-> lemma):

     (37),(38)  `koc_vertex_on_both_directions` -- the closed-form W lies on
                BOTH main directions;
                `koc_vertex_unique` -- and it is the ONLY such point
                (m <> 0), so the frame vertex is well-defined;
     (39)       `koc_vertex_dist_sq` -- OW^2 = (1+m^2) t^2 / (4 m^2) with
                t = yO3 - m*xO3, sqrt-free;
     (40),(41)  `koc_grid_origin_placement` -- walking distance d along the
                grid line X = A1 + B1*Y from the surveyed vertex stays ON
                the line and lands at squared distance exactly d^2, for
                BOTH branch choices (the paper's side-selector picks one);
     example    an exact 3-4-5 instance closing the loop with part 1:
                m = 3/4, O3 = (8,0) gives W = (4,-3), OW = 5; in the grid,
                walking d = 5 down the line X = (3/4) Y from (4,3) lands
                the origin at (0,0) exactly.

   Sqrt-free throughout (u > 0, u^2 = 1 + B1^2 carried as hypotheses), same
   as part 1.  No `Admitted`, no `Axiom`, no `Parameter`.

   Source: W. Koc, "Design of compound curves adapted to the satellite
   measurements", The Archives of Transport 34(2), 2015, 37-49
   (doi:10.5604/08669546.1169211).

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import Distance CompoundCurveKoc.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  The vertex of the symmetric main directions (Koc eqs (37),(38)).       *)
(*                                                                            *)
(* In the local frame the first main direction runs through the origin with   *)
(* slope -m and the second through O3 = (xO3, yO3) with slope +m, where       *)
(* m = tan(alpha/2) and alpha is the route's turning angle.  Koc's closed     *)
(* form for their intersection W:                                             *)
(*                                                                            *)
(*   xW = (yO3 - m xO3) / (-2m),      yW = (yO3 - m xO3) / 2.                 *)
(* -------------------------------------------------------------------------- *)

Definition koc_dir1 (m x : R) : R := - m * x.
Definition koc_dir2 (m xO3 yO3 x : R) : R := yO3 + m * (x - xO3).

Definition koc_vertex_x (m xO3 yO3 : R) : R := (yO3 - m * xO3) / (- 2 * m).
Definition koc_vertex_y (m xO3 yO3 : R) : R := (yO3 - m * xO3) / 2.

(* The closed-form W lies on BOTH main directions. *)
Theorem koc_vertex_on_both_directions :
  forall m xO3 yO3,
    m <> 0 ->
    koc_dir1 m (koc_vertex_x m xO3 yO3) = koc_vertex_y m xO3 yO3 /\
    koc_dir2 m xO3 yO3 (koc_vertex_x m xO3 yO3) = koc_vertex_y m xO3 yO3.
Proof.
  intros m xO3 yO3 Hm.
  unfold koc_dir1, koc_dir2, koc_vertex_x, koc_vertex_y.
  split; field; lra.
Qed.

(* ... and it is the ONLY point on both: the two directions are transversal
   whenever m <> 0, so the frame vertex is well-defined.  (The "scout" fact
   the paper never states: without it eqs (40),(41) would be anchored to an
   arbitrary member of a solution set.) *)
Theorem koc_vertex_unique :
  forall m xO3 yO3 x y,
    m <> 0 ->
    koc_dir1 m x = y ->
    koc_dir2 m xO3 yO3 x = y ->
    x = koc_vertex_x m xO3 yO3 /\ y = koc_vertex_y m xO3 yO3.
Proof.
  intros m xO3 yO3 x y Hm H1 H2.
  unfold koc_dir1 in H1. unfold koc_dir2 in H2.
  unfold koc_vertex_x, koc_vertex_y.
  assert (Hx : x = (yO3 - m * xO3) / (- 2 * m)).
  { apply (Rmult_eq_reg_l (- 2 * m)); [ | lra ].
    field_simplify; lra. }
  split.
  - exact Hx.
  - rewrite <- H1, Hx. field. lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  The vertex distance (Koc eq (39)), sqrt-free.                          *)
(*                                                                            *)
(* OW = sqrt(xW^2 + yW^2); in squared form OW^2 = (1+m^2) t^2 / (4 m^2)       *)
(* with t = yO3 - m xO3.  This is the length walked along the grid line in    *)
(* §3, so it must be exact: an error here translates the whole alignment.     *)
(* -------------------------------------------------------------------------- *)

Theorem koc_vertex_dist_sq :
  forall m xO3 yO3,
    m <> 0 ->
    dist_sq (mkPoint (koc_vertex_x m xO3 yO3) (koc_vertex_y m xO3 yO3))
            (mkPoint 0 0)
    = (1 + m * m) * ((yO3 - m * xO3) * (yO3 - m * xO3)) / (4 * (m * m)).
Proof.
  intros m xO3 yO3 Hm.
  unfold dist_sq, koc_vertex_x, koc_vertex_y; simpl.
  field. lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Placing the frame origin in the grid (Koc eqs (40),(41)).              *)
(*                                                                            *)
(* In system 2000 the first main direction is X = A1 + B1*Y and the surveyed  *)
(* vertex is (YW, XW) on it.  The frame origin O is the point at distance     *)
(* OW from W ALONG the line; the paper's (A2-A1)/(B1-B2) selector picks the   *)
(* branch (which side of W).  We prove both branches at once: for either      *)
(* sign, the landing point is still on the line and at squared distance       *)
(* exactly d^2.  Sqrt-free via u > 0, u^2 = 1 + B1^2.                         *)
(* -------------------------------------------------------------------------- *)

Theorem koc_grid_origin_placement :
  forall A1 B1 YW XW d u (sgn : R),
    0 < u -> u * u = 1 + B1 * B1 ->
    (sgn = 1 \/ sgn = -1) ->
    XW = A1 + B1 * YW ->
    let YO := YW + sgn * d / u in
    let XO := XW + sgn * B1 * d / u in
    (* the origin is still on the first main direction *)
    XO = A1 + B1 * YO /\
    (* at squared distance exactly d^2 from the vertex *)
    dist_sq (mkPoint YO XO) (mkPoint YW XW) = d * d.
Proof.
  intros A1 B1 YW XW d u sgn Hu Husq Hsgn HW YO XO.
  assert (Hne : u <> 0) by lra.
  split.
  - unfold XO, YO. rewrite HW. field. exact Hne.
  - unfold XO, YO, dist_sq; simpl.
    transitivity (sgn * sgn * (d * d) * (1 + B1 * B1) / (u * u)).
    + field. exact Hne.
    + rewrite <- Husq.
      destruct Hsgn as [-> | ->]; field; exact Hne.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Worked example: the 3-4-5 loop closes.                                 *)
(*                                                                            *)
(* Local frame: m = 3/4, O3 = (8,0).  Then t = -6, W = (4,-3), OW^2 = 25 --   *)
(* the third 3-4-5 triangle of this lane.  Grid: the first main direction is  *)
(* X = (3/4) Y, the surveyed vertex (4,3) lies on it, and walking d = 5       *)
(* with u = 5/4 on the sgn = -1 branch lands the frame origin at EXACTLY      *)
(* (0,0) -- the same rational loop part 1's example started from.            *)
(* -------------------------------------------------------------------------- *)

Example koc_example_345_vertex :
  koc_vertex_x (3/4) 8 0 = 4 /\
  koc_vertex_y (3/4) 8 0 = -3 /\
  dist_sq (mkPoint (koc_vertex_x (3/4) 8 0) (koc_vertex_y (3/4) 8 0))
          (mkPoint 0 0) = 5 * 5.
Proof.
  unfold koc_vertex_x, koc_vertex_y, dist_sq; simpl.
  repeat split; lra.
Qed.

Example koc_example_345_grid_origin :
  let YO := 4 + (-1) * 5 / (5/4) in
  let XO := 3 + (-1) * (3/4) * 5 / (5/4) in
  YO = 0 /\ XO = 0 /\ XO = 0 + (3/4) * YO /\
  dist_sq (mkPoint YO XO) (mkPoint 4 3) = 5 * 5.
Proof.
  cbv zeta. unfold dist_sq; simpl.
  repeat split; lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  Audit footprint.                                                       *)
(* -------------------------------------------------------------------------- *)

Print Assumptions koc_vertex_on_both_directions.
Print Assumptions koc_vertex_unique.
Print Assumptions koc_vertex_dist_sq.
Print Assumptions koc_grid_origin_placement.

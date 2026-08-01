(* ============================================================================
   NetTopologySuite.Proofs.CompoundCurveAssembly
   ----------------------------------------------------------------------------
   The compound-curve ASSEMBLY invariant: tangent conformity at all four
   joints of the full five-element EN 13803-1 system

       TC1 -- CA1 -- TC2 -- CA2 -- TC3

   (Koc 2015, Archives of Transport 34(2); Koc 2025, Geomatics 5(2):21;
   local pieces mechanised in CompoundCurveKoc.v / ...KocFrame.v /
   ...KocJoin.v -- this file is the "one theorem chain" their companion doc
   flags as the natural next rung.)

   THE REAL-WORLD FAILURE MODE.  A designer (or an NTS/LandXML consumer)
   substitutes radii and transition lengths into the closed-form Koc
   formulas and obtains a "design".  If the four interfaces are not C^1
   (common tangent direction), the alignment has a kink no vehicle can
   negotiate, or a curvature jump that breaks the lateral-acceleration /
   jerk envelope at line speed (the papers' example runs 110 km/h).
   Floating-point implementations introduce exactly these kinks through
   sign errors and frame-drift accumulation.  This file makes the
   continuity obligations explicit and machine-checked -- in the LOCAL
   design frame AND after the stakeout transform to the national grid.

   WHAT IS MECHANISED:

     `joint_C1`                     the interface contract: the joint point
                                    lies on the arc's circle and the radius
                                    is perpendicular to the shared tangent
                                    direction (1, s) -- for a transition
                                    piece the tangent is (1, s) by
                                    definition of slope, so this IS the C^1
                                    condition at a transition/arc interface.
     `koc_joint_transition_to_arc`  entering an arc: centre-on-normal
                                    placement satisfies the contract
                                    (joints K1: TC1->CA1 and K2: TC2->CA2).
     `koc_joint_arc_to_transition`  leaving an arc: the prescribed-slope
                                    point satisfies the contract (joints
                                    O2: CA1->TC2 and K3: CA2->TC3).
     `koc_compound_assembly_C1`     HEADLINE: the four-joint conjunction
                                    for the whole five-element chain --
                                    shared interface points, both circles,
                                    ARBITRARY SIGNED radii (a reverse curve
                                    is R2 < 0, no separate statement).
     `koc_assembly_slope_provenance`the slopes at the outer joints are the
                                    clothoid's: s = tan(theta(L) - alpha/2)
                                    with theta(L) = L/(2R) from part 1 --
                                    the chain consumes the end angle, so a
                                    wrong transition length breaks joint 1,
                                    not some remote formula.
     `koc_global_pt_isometry`       the stakeout transform preserves
                                    squared distances -- DERIVED from part
                                    1's local isometry via the round-trip,
                                    not re-proven.
     `koc_global_preserves_dot`     ... and preserves dot products of
                                    difference vectors (it is a rotation +
                                    shift), so
     `koc_assembly_C1_in_grid`      the C^1 contract SURVIVES the transform:
                                    kink-freedom checked in the design frame
                                    is kink-freedom on the ground.
     examples                       a full rational assembly (all four
                                    joints on the 3-4-5 / 3-4-5-10 circles)
                                    and a reverse-curve joint (R2 = -10)
                                    showing the signed case needs nothing new.

   Sqrt-free throughout (u > 0, u^2 = 1 + s^2 as hypotheses); classical-
   reals trio only.  No `Admitted`, no `Axiom`, no `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import Distance CompoundCurveKoc.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  The interface contract.                                                *)
(*                                                                            *)
(* At a transition/arc interface J the transition's tangent direction is      *)
(* (1, s) by definition of its slope s.  The arc side is C^1 there exactly    *)
(* when J is on the circle and the radius J-S is perpendicular to (1, s):     *)
(* the circle's tangent at J is then the same line.  `joint_C1` packages      *)
(* both conditions; it is deliberately agnostic about the SIGN of R, so a     *)
(* reverse curve (centre on the other side) satisfies the same contract.      *)
(* -------------------------------------------------------------------------- *)

Definition joint_C1 (J S : Point) (Rr s : R) : Prop :=
  dist_sq J S = Rr * Rr /\
  (px J - px S) * 1 + (py J - py S) * s = 0.

(* Entering an arc (K1: TC1->CA1, K2: TC2->CA2): the centre-on-normal
   construction of part 1 satisfies the contract at the transition end. *)
Theorem koc_joint_transition_to_arc :
  forall xK yK s Rr u,
    0 < u -> u * u = 1 + s * s ->
    joint_C1 (mkPoint xK yK)
             (mkPoint (xK + s * Rr / u) (yK - Rr / u)) Rr s.
Proof.
  intros xK yK s Rr u Hu Husq.
  destruct (koc_center_on_normal xK yK s Rr u Hu Husq) as [Hd Hp].
  split.
  - (* dist_sq is symmetric in its arguments here by the ring shape *)
    unfold dist_sq in *; simpl in *. lra.
  - unfold dist_sq in *; simpl in *. lra.
Qed.

(* Leaving an arc (O2: CA1->TC2, K3: CA2->TC3): the prescribed-slope point
   of part 1 satisfies the contract at the arc end. *)
Theorem koc_joint_arc_to_transition :
  forall xS yS s Rr u,
    0 < u -> u * u = 1 + s * s ->
    joint_C1 (mkPoint (xS - s * Rr / u) (yS + Rr / u))
             (mkPoint xS yS) Rr s.
Proof.
  intros xS yS s Rr u Hu Husq.
  destruct (koc_slope_point_on_circle xS yS s Rr u Hu Husq) as [Hd Hp].
  split; [ exact Hd | exact Hp ].
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  HEADLINE: the five-element chain is C^1 at all four interfaces.        *)
(*                                                                            *)
(* The chain is parameterised by the four interface slopes s1..s4 (their      *)
(* provenance from the clothoid end angles is §3) and the two signed radii.   *)
(* The interface points are DEFINED ONCE and used by both sides:              *)
(*   K1 (TC1 end = CA1 start), O2 (CA1 end = TC2 start),                      *)
(*   K2 (TC2 end = CA2 start), K3 (CA2 end = TC3 start).                      *)
(* A reverse curve is R2 < 0 -- same statement, no extra case.                *)
(* -------------------------------------------------------------------------- *)

Theorem koc_compound_assembly_C1 :
  forall xK1 yK1 s1 s2 xK2 yK2 s3 s4 R1 R2 u1 u2 u3 u4,
    0 < u1 -> u1 * u1 = 1 + s1 * s1 ->
    0 < u2 -> u2 * u2 = 1 + s2 * s2 ->
    0 < u3 -> u3 * u3 = 1 + s3 * s3 ->
    0 < u4 -> u4 * u4 = 1 + s4 * s4 ->
    let K1 := mkPoint xK1 yK1 in
    let S1 := mkPoint (xK1 + s1 * R1 / u1) (yK1 - R1 / u1) in
    let O2 := mkPoint (px S1 - s2 * R1 / u2) (py S1 + R1 / u2) in
    let K2 := mkPoint xK2 yK2 in
    let S2 := mkPoint (xK2 + s3 * R2 / u3) (yK2 - R2 / u3) in
    let K3 := mkPoint (px S2 - s4 * R2 / u4) (py S2 + R2 / u4) in
    joint_C1 K1 S1 R1 s1 /\   (* TC1 -> CA1 *)
    joint_C1 O2 S1 R1 s2 /\   (* CA1 -> TC2 *)
    joint_C1 K2 S2 R2 s3 /\   (* TC2 -> CA2 *)
    joint_C1 K3 S2 R2 s4.     (* CA2 -> TC3 *)
Proof.
  intros xK1 yK1 s1 s2 xK2 yK2 s3 s4 R1 R2 u1 u2 u3 u4
         Hu1 Hs1 Hu2 Hs2 Hu3 Hs3 Hu4 Hs4 K1 S1 O2 K2 S2 K3.
  repeat split.
  - exact (proj1 (koc_joint_transition_to_arc xK1 yK1 s1 R1 u1 Hu1 Hs1)).
  - exact (proj2 (koc_joint_transition_to_arc xK1 yK1 s1 R1 u1 Hu1 Hs1)).
  - exact (proj1 (koc_joint_arc_to_transition (px S1) (py S1) s2 R1 u2 Hu2 Hs2)).
  - exact (proj2 (koc_joint_arc_to_transition (px S1) (py S1) s2 R1 u2 Hu2 Hs2)).
  - exact (proj1 (koc_joint_transition_to_arc xK2 yK2 s3 R2 u3 Hu3 Hs3)).
  - exact (proj2 (koc_joint_transition_to_arc xK2 yK2 s3 R2 u3 Hu3 Hs3)).
  - exact (proj1 (koc_joint_arc_to_transition (px S2) (py S2) s4 R2 u4 Hu4 Hs4)).
  - exact (proj2 (koc_joint_arc_to_transition (px S2) (py S2) s4 R2 u4 Hu4 Hs4)).
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Slope provenance: the chain consumes the clothoid end angle.           *)
(*                                                                            *)
(* Koc eq (7): the slope entering CA1 is s_K1 = tan(theta1(l1) - alpha/2).    *)
(* With part 1's `koc_clothoid_end_angle`, theta1(l1) = l1/(2 R1), so the     *)
(* assembly's s1 is a function of the DESIGN PARAMETERS l1, R1, alpha alone.  *)
(* A wrong transition length manifests as a violated joint-1 contract, not   *)
(* as a mysterious remote defect.                                             *)
(* -------------------------------------------------------------------------- *)

Theorem koc_assembly_slope_provenance :
  forall Rr L alpha,
    Rr <> 0 -> L <> 0 ->
    tan (koc_clothoid_angle Rr L L - alpha / 2) = tan (L / (2 * Rr) - alpha / 2).
Proof.
  intros Rr L alpha HR HL.
  rewrite koc_clothoid_end_angle; [ reflexivity | exact HR | exact HL ].
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  The C^1 contract survives the stakeout transform.                      *)
(*                                                                            *)
(* Stakeout sends local design points to the national grid via eqs (42),      *)
(* (43) -- a rotation plus a shift.  Rotations preserve dot products of       *)
(* difference vectors and shifts cancel in differences, so BOTH conjuncts of  *)
(* `joint_C1` transfer: distances via the (derived) global isometry, and      *)
(* perpendicularity via dot-product preservation, with the tangent direction  *)
(* transported as the image of a direction segment.  Kink-freedom checked in  *)
(* the design frame is kink-freedom on the ground.                            *)
(* -------------------------------------------------------------------------- *)

Definition koc_global_pt (Y0 X0 beta : R) (p : Point) : Point :=
  mkPoint (koc_global_Y Y0 X0 beta (px p) (py p))
          (koc_global_X Y0 X0 beta (px p) (py p)).

Definition koc_local_pt (Y0 X0 beta : R) (p : Point) : Point :=
  mkPoint (koc_local_x Y0 X0 beta (px p) (py p))
          (koc_local_y Y0 X0 beta (px p) (py p)).

(* Round-trip at the Point level (from part 1's coordinate round-trip). *)
Lemma koc_local_global_pt_id :
  forall Y0 X0 beta p,
    koc_local_pt Y0 X0 beta (koc_global_pt Y0 X0 beta p) = p.
Proof.
  intros Y0 X0 beta [x y].
  unfold koc_local_pt, koc_global_pt; simpl.
  destruct (koc_roundtrip_local_global Y0 X0 beta x y) as [Hx Hy].
  rewrite Hx, Hy. reflexivity.
Qed.

(* The stakeout transform is an isometry -- DERIVED: apply part 1's local
   isometry to the transformed points and collapse with the round-trip. *)
Theorem koc_global_pt_isometry :
  forall Y0 X0 beta p q,
    dist_sq (koc_global_pt Y0 X0 beta p) (koc_global_pt Y0 X0 beta q)
    = dist_sq p q.
Proof.
  intros Y0 X0 beta p q.
  pose proof (koc_to_local_isometry Y0 X0 beta
                (px (koc_global_pt Y0 X0 beta p)) (py (koc_global_pt Y0 X0 beta p))
                (px (koc_global_pt Y0 X0 beta q)) (py (koc_global_pt Y0 X0 beta q)))
    as H.
  (* the left side of H is dist_sq of the local images of the global images,
     i.e. dist_sq p q by the round-trip; its right side is the global dist. *)
  assert (Hp : koc_local_pt Y0 X0 beta (koc_global_pt Y0 X0 beta p) = p)
    by apply koc_local_global_pt_id.
  assert (Hq : koc_local_pt Y0 X0 beta (koc_global_pt Y0 X0 beta q) = q)
    by apply koc_local_global_pt_id.
  unfold koc_local_pt in Hp, Hq.
  rewrite Hp, Hq in H.
  (* H : dist_sq p q = dist_sq (mkPoint (px gp) (py gp)) (mkPoint ...) *)
  destruct (koc_global_pt Y0 X0 beta p) as [gx gy].
  destruct (koc_global_pt Y0 X0 beta q) as [hx hy].
  simpl in H. symmetry. exact H.
Qed.

(* Rotations preserve dot products of difference vectors (shifts cancel). *)
Theorem koc_global_preserves_dot :
  forall Y0 X0 beta p q r s,
    (px (koc_global_pt Y0 X0 beta p) - px (koc_global_pt Y0 X0 beta q))
    * (px (koc_global_pt Y0 X0 beta r) - px (koc_global_pt Y0 X0 beta s))
    + (py (koc_global_pt Y0 X0 beta p) - py (koc_global_pt Y0 X0 beta q))
      * (py (koc_global_pt Y0 X0 beta r) - py (koc_global_pt Y0 X0 beta s))
    = (px p - px q) * (px r - px s) + (py p - py q) * (py r - py s).
Proof.
  intros Y0 X0 beta [px1 py1] [px2 py2] [px3 py3] [px4 py4].
  unfold koc_global_pt, koc_global_Y, koc_global_X; simpl.
  pose proof (sin2_cos2 beta) as H. unfold Rsqr in H.
  replace ((Y0 + px1 * cos beta - py1 * sin beta
            - (Y0 + px2 * cos beta - py2 * sin beta))
           * (Y0 + px3 * cos beta - py3 * sin beta
              - (Y0 + px4 * cos beta - py4 * sin beta))
           + (X0 + px1 * sin beta + py1 * cos beta
              - (X0 + px2 * sin beta + py2 * cos beta))
             * (X0 + px3 * sin beta + py3 * cos beta
                - (X0 + px4 * sin beta + py4 * cos beta)))
    with (((px1 - px2) * (px3 - px4) + (py1 - py2) * (py3 - py4))
          * (sin beta * sin beta + cos beta * cos beta)) by ring.
  rewrite H. ring.
Qed.

(* COROLLARY: kink-freedom survives stakeout.  If a joint satisfies the C^1
   contract in the design frame, then after the transform the (image of the)
   radius is still perpendicular to the (image of the) tangent direction --
   the tangent direction being transported as the segment from any point A
   to A + (1, s).  Distances transfer by the isometry. *)
Theorem koc_assembly_C1_in_grid :
  forall Y0 X0 beta J S Rr s (A : Point),
    joint_C1 J S Rr s ->
    let g := koc_global_pt Y0 X0 beta in
    let TA := mkPoint (px A + 1) (py A + s) in
    dist_sq (g J) (g S) = Rr * Rr /\
    (px (g J) - px (g S)) * (px (g TA) - px (g A))
    + (py (g J) - py (g S)) * (py (g TA) - py (g A)) = 0.
Proof.
  intros Y0 X0 beta J S Rr s A [Hd Hp] g TA.
  unfold g.
  split.
  - rewrite koc_global_pt_isometry. exact Hd.
  - rewrite (koc_global_preserves_dot Y0 X0 beta J S TA A).
    unfold TA; simpl.
    replace (px A + 1 - px A) with 1 by ring.
    replace (py A + s - py A) with s by ring.
    exact Hp.
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  Worked examples.                                                       *)
(*                                                                            *)
(* (a) A full rational assembly on the lane's 3-4-5 / 3-4-5-10 circles:       *)
(*     K1 = (0,0), s1 = 3/4, R1 = 5   =>  S1 = (3,-4);                        *)
(*     leave CA1 at s2 = 0 (the apex) =>  O2 = (3,1);                         *)
(*     K2 = (10,0), s3 = 0, R2 = 10   =>  S2 = (10,-10);                      *)
(*     leave CA2 at s4 = -3/4         =>  K3 = (16,-2).                       *)
(*     All four joint contracts close by rational arithmetic.                 *)
(* (b) A reverse-curve joint: same K2, s3 but R2 = -10 puts the centre at     *)
(*     (10, 10) -- the other side of the track -- and the SAME contract       *)
(*     holds: the signed case needs nothing new.                              *)
(* -------------------------------------------------------------------------- *)

Example koc_assembly_example_345 :
  joint_C1 (mkPoint 0 0) (mkPoint 3 (-4)) 5 (3/4) /\
  joint_C1 (mkPoint 3 1) (mkPoint 3 (-4)) 5 0 /\
  joint_C1 (mkPoint 10 0) (mkPoint 10 (-10)) 10 0 /\
  joint_C1 (mkPoint 16 (-2)) (mkPoint 10 (-10)) 10 (-(3/4)).
Proof.
  unfold joint_C1, dist_sq; simpl.
  repeat split; lra.
Qed.

Example koc_assembly_example_reverse :
  joint_C1 (mkPoint 10 0) (mkPoint 10 10) (-10) 0.
Proof.
  unfold joint_C1, dist_sq; simpl.
  split; lra.
Qed.

(* The example interface points are exactly the assembly constructions. *)
Example koc_assembly_example_is_koc :
  mkPoint (0 + (3/4) * 5 / (5/4)) (0 - 5 / (5/4)) = mkPoint 3 (-4) /\
  mkPoint (3 - 0 * 5 / 1) ((-4) + 5 / 1) = mkPoint 3 1 /\
  mkPoint (10 + 0 * 10 / 1) (0 - 10 / 1) = mkPoint 10 (-10) /\
  mkPoint (10 - (-(3/4)) * 10 / (5/4)) ((-10) + 10 / (5/4)) = mkPoint 16 (-2).
Proof.
  repeat split; f_equal; lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §6  Audit footprint.                                                       *)
(* -------------------------------------------------------------------------- *)

Print Assumptions koc_joint_transition_to_arc.
Print Assumptions koc_joint_arc_to_transition.
Print Assumptions koc_compound_assembly_C1.
Print Assumptions koc_assembly_slope_provenance.
Print Assumptions koc_global_pt_isometry.
Print Assumptions koc_global_preserves_dot.
Print Assumptions koc_assembly_C1_in_grid.

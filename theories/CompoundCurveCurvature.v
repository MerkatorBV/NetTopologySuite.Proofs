(* ============================================================================
   NetTopologySuite.Proofs.CompoundCurveCurvature
   ----------------------------------------------------------------------------
   The compound-curve CURVATURE invariant: C^0 curvature continuity at all
   four joints of the full five-element EN 13803-1 system

       TC1 -- CA1 -- TC2 -- CA2 -- TC3

   and the intermediate transition TC2's linear curvature ramp 1/R1 -> 1/R2
   (Koc 2015, Archives of Transport 34(2), Sec. 2; EN 13803-1).  Companion
   to CompoundCurveAssembly.v, which mechanised the dual C^1 (tangent)
   contract; this file closes the passenger-comfort side of the same
   joints -- continuous lateral acceleration, bounded transverse jerk.

   THE REAL-WORLD FAILURE MODE.  Part 4 (CompoundCurveAssembly.v) guarantees
   the alignment is kink-free (shared tangent).  That is necessary but not
   sufficient for runnability at line speed: a jump in CURVATURE at a joint
   is a jump in lateral acceleration.  At the papers' example speed of
   110 km/h that is a passenger-comfort failure and, for a large enough
   jump, a derailment risk under EN 13803-1's cant/jerk envelopes.  The
   classic source is a mis-coded intermediate transition TC2 that starts
   at 0 (as if it were TC1) instead of at 1/R1, or ends at 0 instead of
   1/R2 -- floating-point sign/order errors produce exactly those jumps.
   This file makes the C^0 curvature obligations explicit and machine-
   checked, including the non-trivial TC2 ramp that is NOT a start-from-
   straight clothoid.

   WHAT IS MECHANISED:

     `joint_C0_curvature`             the interface contract: the two sides
                                      of a joint carry the same curvature
                                      value (no jump in lateral accel).
     `koc_arc_curvature`              constant arc curvature 1/R (signed).
     `koc_joint_tc1_to_ca_C0`         TC1 end = CA1: reuses part 1's
                                      `koc_clothoid_end_curvature` (k(L)=1/R).
     `koc_tc2_curvature` /
     `koc_tc2_angle`                  intermediate transition: linear ramp
                                      k(l) = 1/R1 + l*(1/R2 - 1/R1)/L, with
                                      integrated angle theta(l).
     `koc_tc2_start` / `koc_tc2_end`  boundary values: k(0)=1/R1, k(L)=1/R2.
     `koc_tc2_angle_deriv`            theta' = k for the intermediate ramp
                                      (the dual of part 1's clothoid deriv).
     `koc_tc2_linear_ramp`            the ramp is the affine interpolation of
                                      the two arc curvatures (algebraic form).
     `koc_joint_ca_to_tc2_C0` /
     `koc_joint_tc2_to_ca_C0`         CA1->TC2 and TC2->CA2 satisfy C^0.
     `koc_exit_clothoid_curvature`    TC3-style exit ramp 1/R -> 0
                                      (mirror of TC1: k(l)=(L-l)/(R L)).
     `koc_exit_clothoid_start` /
     `koc_exit_clothoid_end`          k(0)=1/R, k(L)=0.
     `koc_exit_is_reversed_entry`     exit ramp = entry clothoid read
                                      backwards: k_exit(l) = k_entry(L-l).
     `koc_exit_clothoid_angle_deriv`  theta' = k for the exit ramp.
     `koc_joint_ca_to_tc3_C0`         CA2->TC3 satisfies C^0.
     `koc_compound_assembly_C0`       HEADLINE: the four-joint C^0 conjunction
                                      for the whole five-element chain, with
                                      SIGNED radii (reverse curve = R2 < 0,
                                      no separate case).
     `koc_assembly_C0_to_straight`    TC3 ends at curvature 0 -- the join
                                      back onto the second main direction.
     examples                         rational witness R1=5, R2=10, L=4 and
                                      reverse-curve R2=-10, all by field.

   Sqrt-free throughout; classical-reals trio only.  No `Admitted`, no
   `Axiom`, no `Parameter`.  Reuses part 1's clothoid surface
   (`koc_clothoid_curvature`, `koc_clothoid_end_curvature`) rather than
   re-proving the outer entry ramp.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Grok Build (xAI)
   ========================================================================== *)

From Stdlib Require Import Reals Lra Ranalysis1.
From NTS.Proofs Require Import Distance CompoundCurveKoc.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  The interface contract.                                                *)
(*                                                                            *)
(* At a joint the left piece ends with some curvature k_left and the right    *)
(* piece starts with k_right.  C^0 curvature continuity is exactly            *)
(* k_left = k_right -- no jump in lateral acceleration.  Packaged as a named  *)
(* Prop so the assembly can conjoin four of them the same way part 4 packs    *)
(* `joint_C1`.  Sign-agnostic: a reverse curve carries negative curvature     *)
(* and the equality still means "no jump".                                    *)
(* -------------------------------------------------------------------------- *)

Definition joint_C0_curvature (k_left k_right : R) : Prop :=
  k_left = k_right.

(* Constant curvature of a circular arc of (signed) radius R. *)
Definition koc_arc_curvature (Rr : R) : R := / Rr.

(* -------------------------------------------------------------------------- *)
(* §2  Outer entry ramp TC1 -> CA1 (reuses part 1).                            *)
(*                                                                            *)
(* TC1 is the start-from-straight clothoid of part 1: k(l) = l/(R L) runs      *)
(* from 0 to 1/R.  The C^0 join into CA1 is exactly part 1's end-curvature    *)
(* lemma; we restate it as a joint contract so the assembly is uniform.       *)
(* -------------------------------------------------------------------------- *)

Theorem koc_joint_tc1_to_ca_C0 :
  forall Rr L,
    Rr <> 0 -> L <> 0 ->
    joint_C0_curvature (koc_clothoid_curvature Rr L L) (koc_arc_curvature Rr).
Proof.
  intros Rr L HR HL.
  unfold joint_C0_curvature, koc_arc_curvature.
  exact (koc_clothoid_end_curvature Rr L HR HL).
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Intermediate transition TC2: linear ramp 1/R1 -> 1/R2.                 *)
(*                                                                            *)
(* THIS is the piece that is not a start-from-straight clothoid.  Between     *)
(* the two arcs the curvature must run continuously from the first arc's      *)
(* 1/R1 to the second's 1/R2.  EN 13803-1 / Koc Sec. 2 take the ramp linear    *)
(* in arc length:                                                             *)
(*                                                                            *)
(*   k(l) = 1/R1 + l * (1/R2 - 1/R1) / L                                      *)
(*        = ((L - l)/L) * (1/R1) + (l/L) * (1/R2)                             *)
(*                                                                            *)
(* so k(0) = 1/R1 and k(L) = 1/R2.  The integrated tangent angle is            *)
(*                                                                            *)
(*   theta(l) = (1/R1)*l + (1/R2 - 1/R1)/(2 L) * l^2                           *)
(*                                                                            *)
(* and we prove theta' = k exactly as part 1 did for the outer clothoid.      *)
(* A reverse curve is R2 < 0: same formulas, signed curvature, no extra case. *)
(* -------------------------------------------------------------------------- *)

Definition koc_tc2_curvature (R1 R2 L l : R) : R :=
  / R1 + l * (/ R2 - / R1) / L.

(* Angle written as a*l + c*(l*l) so the derivative proof is a direct sum of
   two `derivable_pt_lim_scal` applications (mirrors part 1's shape). *)
Definition koc_tc2_angle (R1 R2 L l : R) : R :=
  / R1 * l + (/ R2 - / R1) / (2 * L) * (l * l).

(* Boundary: TC2 starts at the first arc's curvature. *)
Lemma koc_tc2_start :
  forall R1 R2 L,
    R1 <> 0 -> R2 <> 0 -> L <> 0 ->
    koc_tc2_curvature R1 R2 L 0 = / R1.
Proof.
  intros R1 R2 L HR1 HR2 HL.
  unfold koc_tc2_curvature. field; lra.
Qed.

(* Boundary: TC2 ends at the second arc's curvature. *)
Lemma koc_tc2_end :
  forall R1 R2 L,
    R1 <> 0 -> R2 <> 0 -> L <> 0 ->
    koc_tc2_curvature R1 R2 L L = / R2.
Proof.
  intros R1 R2 L HR1 HR2 HL.
  unfold koc_tc2_curvature. field; lra.
Qed.

(* Affine-interpolation form of the same ramp (the form a designer reads
   off the two design radii). *)
Theorem koc_tc2_linear_ramp :
  forall R1 R2 L l,
    R1 <> 0 -> R2 <> 0 -> L <> 0 ->
    koc_tc2_curvature R1 R2 L l
    = (L - l) / L * (/ R1) + l / L * (/ R2).
Proof.
  intros R1 R2 L l HR1 HR2 HL.
  unfold koc_tc2_curvature. field; lra.
Qed.

(* theta really is the antiderivative of k for the intermediate ramp. *)
Theorem koc_tc2_angle_deriv :
  forall R1 R2 L l,
    R1 <> 0 -> R2 <> 0 -> L <> 0 ->
    derivable_pt_lim (koc_tc2_angle R1 R2 L) l
                     (koc_tc2_curvature R1 R2 L l).
Proof.
  intros R1 R2 L l HR1 HR2 HL.
  unfold koc_tc2_angle, koc_tc2_curvature.
  (* Target derivative rewritten as a*1 + c*(l+l). *)
  set (a := / R1).
  set (c := (/ R2 - / R1) / (2 * L)).
  assert (Htgt : / R1 + l * (/ R2 - / R1) / L = a * 1 + c * (l + l)).
  { unfold a, c. field; lra. }
  rewrite Htgt.
  assert (Hid : derivable_pt_lim id l 1) by apply derivable_pt_lim_id.
  assert (Hlin : derivable_pt_lim (fun x => a * x) l (a * 1)).
  { apply derivable_pt_lim_scal. exact Hid. }
  assert (Hsq : derivable_pt_lim (fun x => x * x) l (l + l)).
  { pose proof (derivable_pt_lim_mult id id l 1 1 Hid Hid) as H.
    unfold id in H.
    replace (l + l) with (1 * l + l * 1) by ring. exact H. }
  assert (Hquad : derivable_pt_lim (fun x => c * (x * x)) l (c * (l + l))).
  { apply derivable_pt_lim_scal. exact Hsq. }
  pose proof (derivable_pt_lim_plus (fun x => a * x) (fun x => c * (x * x))
                l (a * 1) (c * (l + l)) Hlin Hquad) as Hsum.
  (* a, c are transparent lets: fun x => a*x + c*(x*x) converts to the
     unfolded koc_tc2_angle body, and the rewritten target matches. *)
  exact Hsum.
Qed.

(* CA1 -> TC2: the arc's constant curvature meets TC2's start. *)
Theorem koc_joint_ca_to_tc2_C0 :
  forall R1 R2 L,
    R1 <> 0 -> R2 <> 0 -> L <> 0 ->
    joint_C0_curvature (koc_arc_curvature R1) (koc_tc2_curvature R1 R2 L 0).
Proof.
  intros R1 R2 L HR1 HR2 HL.
  unfold joint_C0_curvature, koc_arc_curvature.
  symmetry. exact (koc_tc2_start R1 R2 L HR1 HR2 HL).
Qed.

(* TC2 -> CA2: TC2's end meets the second arc's constant curvature. *)
Theorem koc_joint_tc2_to_ca_C0 :
  forall R1 R2 L,
    R1 <> 0 -> R2 <> 0 -> L <> 0 ->
    joint_C0_curvature (koc_tc2_curvature R1 R2 L L) (koc_arc_curvature R2).
Proof.
  intros R1 R2 L HR1 HR2 HL.
  unfold joint_C0_curvature, koc_arc_curvature.
  exact (koc_tc2_end R1 R2 L HR1 HR2 HL).
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Outer exit ramp CA2 -> TC3 (mirror of TC1).                             *)
(*                                                                            *)
(* TC3 runs curvature from 1/R2 back down to 0 so the chain can land on the    *)
(* second main direction (a straight).  Linear in arc length:                 *)
(*                                                                            *)
(*   k(l) = (L - l) / (R L)                                                   *)
(*                                                                            *)
(* so k(0) = 1/R and k(L) = 0.  Angle theta(l) = (1/R)*l - 1/(2 R L)*l^2.     *)
(* -------------------------------------------------------------------------- *)

Definition koc_exit_clothoid_curvature (Rr L l : R) : R :=
  (L - l) / (Rr * L).

Definition koc_exit_clothoid_angle (Rr L l : R) : R :=
  / Rr * l - / (2 * Rr * L) * (l * l).

Lemma koc_exit_clothoid_start :
  forall Rr L,
    Rr <> 0 -> L <> 0 ->
    koc_exit_clothoid_curvature Rr L 0 = / Rr.
Proof.
  intros Rr L HR HL.
  unfold koc_exit_clothoid_curvature. field; lra.
Qed.

Lemma koc_exit_clothoid_end :
  forall Rr L,
    Rr <> 0 -> L <> 0 ->
    koc_exit_clothoid_curvature Rr L L = 0.
Proof.
  intros Rr L HR HL.
  unfold koc_exit_clothoid_curvature. field; lra.
Qed.

(* Exit ramp is the entry clothoid read backwards: k_exit(l) = k_entry(L-l). *)
Theorem koc_exit_is_reversed_entry :
  forall Rr L l,
    Rr <> 0 -> L <> 0 ->
    koc_exit_clothoid_curvature Rr L l = koc_clothoid_curvature Rr L (L - l).
Proof.
  intros Rr L l HR HL.
  unfold koc_exit_clothoid_curvature, koc_clothoid_curvature. field; lra.
Qed.

Theorem koc_exit_clothoid_angle_deriv :
  forall Rr L l,
    Rr <> 0 -> L <> 0 ->
    derivable_pt_lim (koc_exit_clothoid_angle Rr L) l
                     (koc_exit_clothoid_curvature Rr L l).
Proof.
  intros Rr L l HR HL.
  unfold koc_exit_clothoid_angle, koc_exit_clothoid_curvature.
  set (a := / Rr).
  set (c := / (2 * Rr * L)).
  assert (Htgt : (L - l) / (Rr * L) = a * 1 - c * (l + l)).
  { unfold a, c. field; lra. }
  rewrite Htgt.
  assert (Hid : derivable_pt_lim id l 1) by apply derivable_pt_lim_id.
  assert (Hlin : derivable_pt_lim (fun x => a * x) l (a * 1)).
  { apply derivable_pt_lim_scal. exact Hid. }
  assert (Hsq : derivable_pt_lim (fun x => x * x) l (l + l)).
  { pose proof (derivable_pt_lim_mult id id l 1 1 Hid Hid) as H.
    unfold id in H.
    replace (l + l) with (1 * l + l * 1) by ring. exact H. }
  assert (Hquad : derivable_pt_lim (fun x => c * (x * x)) l (c * (l + l))).
  { apply derivable_pt_lim_scal. exact Hsq. }
  pose proof (derivable_pt_lim_minus (fun x => a * x) (fun x => c * (x * x))
                l (a * 1) (c * (l + l)) Hlin Hquad) as Hsum.
  exact Hsum.
Qed.

(* CA2 -> TC3: the second arc meets the exit ramp's start. *)
Theorem koc_joint_ca_to_tc3_C0 :
  forall Rr L,
    Rr <> 0 -> L <> 0 ->
    joint_C0_curvature (koc_arc_curvature Rr) (koc_exit_clothoid_curvature Rr L 0).
Proof.
  intros Rr L HR HL.
  unfold joint_C0_curvature, koc_arc_curvature.
  symmetry. exact (koc_exit_clothoid_start Rr L HR HL).
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  HEADLINE: the five-element chain is C^0 in curvature at all four       *)
(*     interfaces.                                                            *)
(*                                                                            *)
(* Parameterised by the two signed radii and the three transition lengths.    *)
(* A reverse curve is R2 < 0 -- same statement, no extra case.                *)
(* -------------------------------------------------------------------------- *)

Theorem koc_compound_assembly_C0 :
  forall R1 R2 L1 L2 L3,
    R1 <> 0 -> R2 <> 0 -> L1 <> 0 -> L2 <> 0 -> L3 <> 0 ->
    joint_C0_curvature (koc_clothoid_curvature R1 L1 L1)
                       (koc_arc_curvature R1) /\          (* TC1 -> CA1 *)
    joint_C0_curvature (koc_arc_curvature R1)
                       (koc_tc2_curvature R1 R2 L2 0) /\  (* CA1 -> TC2 *)
    joint_C0_curvature (koc_tc2_curvature R1 R2 L2 L2)
                       (koc_arc_curvature R2) /\          (* TC2 -> CA2 *)
    joint_C0_curvature (koc_arc_curvature R2)
                       (koc_exit_clothoid_curvature R2 L3 0). (* CA2 -> TC3 *)
Proof.
  intros R1 R2 L1 L2 L3 HR1 HR2 HL1 HL2 HL3.
  repeat split.
  - exact (koc_joint_tc1_to_ca_C0 R1 L1 HR1 HL1).
  - exact (koc_joint_ca_to_tc2_C0 R1 R2 L2 HR1 HR2 HL2).
  - exact (koc_joint_tc2_to_ca_C0 R1 R2 L2 HR1 HR2 HL2).
  - exact (koc_joint_ca_to_tc3_C0 R2 L3 HR2 HL3).
Qed.

(* Bonus: TC3 lands on the straight (curvature 0) -- the join back onto the
   second main direction that the frame vertex of part 2 anchors. *)
Theorem koc_assembly_C0_to_straight :
  forall Rr L,
    Rr <> 0 -> L <> 0 ->
    joint_C0_curvature (koc_exit_clothoid_curvature Rr L L) 0.
Proof.
  intros Rr L HR HL.
  unfold joint_C0_curvature.
  exact (koc_exit_clothoid_end Rr L HR HL).
Qed.

(* -------------------------------------------------------------------------- *)
(* §6  Worked examples.                                                       *)
(*                                                                            *)
(* (a) Sharp-then-gentle: R1 = 5, R2 = 10, L = 4.                             *)
(*     TC1 end = 1/5; TC2 runs 1/5 -> 1/10; TC3 starts at 1/10, ends at 0.    *)
(* (b) Reverse curve: R2 = -10 puts the second arc's curvature at -1/10 --    *)
(*     TC2 ends there, CA2 carries it, same contracts, nothing new.           *)
(* -------------------------------------------------------------------------- *)

Example koc_curvature_example_345 :
  joint_C0_curvature (koc_clothoid_curvature 5 4 4) (koc_arc_curvature 5) /\
  joint_C0_curvature (koc_arc_curvature 5) (koc_tc2_curvature 5 10 4 0) /\
  joint_C0_curvature (koc_tc2_curvature 5 10 4 4) (koc_arc_curvature 10) /\
  joint_C0_curvature (koc_arc_curvature 10) (koc_exit_clothoid_curvature 10 4 0) /\
  joint_C0_curvature (koc_exit_clothoid_curvature 10 4 4) 0 /\
  (* midpoint of TC2 is the arithmetic mean of the two arc curvatures *)
  koc_tc2_curvature 5 10 4 2 = (/ 5 + / 10) / 2.
Proof.
  unfold joint_C0_curvature, koc_arc_curvature,
         koc_clothoid_curvature, koc_tc2_curvature,
         koc_exit_clothoid_curvature.
  repeat split; field.
Qed.

Example koc_curvature_example_reverse :
  joint_C0_curvature (koc_arc_curvature 5) (koc_tc2_curvature 5 (-10) 4 0) /\
  joint_C0_curvature (koc_tc2_curvature 5 (-10) 4 4) (koc_arc_curvature (-10)) /\
  koc_tc2_curvature 5 (-10) 4 4 = - / 10.
Proof.
  unfold joint_C0_curvature, koc_arc_curvature, koc_tc2_curvature.
  repeat split; field.
Qed.

(* The example numbers are exactly the boundary constructions. *)
Example koc_curvature_example_is_koc :
  koc_clothoid_curvature 5 4 4 = / 5 /\
  koc_tc2_curvature 5 10 4 0 = / 5 /\
  koc_tc2_curvature 5 10 4 4 = / 10 /\
  koc_exit_clothoid_curvature 10 4 0 = / 10 /\
  koc_exit_clothoid_curvature 10 4 4 = 0.
Proof.
  unfold koc_clothoid_curvature, koc_tc2_curvature, koc_exit_clothoid_curvature.
  repeat split; field.
Qed.

(* -------------------------------------------------------------------------- *)
(* §7  Audit footprint.                                                       *)
(* -------------------------------------------------------------------------- *)

Print Assumptions koc_joint_tc1_to_ca_C0.
Print Assumptions koc_tc2_linear_ramp.
Print Assumptions koc_tc2_angle_deriv.
Print Assumptions koc_exit_is_reversed_entry.
Print Assumptions koc_exit_clothoid_angle_deriv.
Print Assumptions koc_compound_assembly_C0.
Print Assumptions koc_assembly_C0_to_straight.

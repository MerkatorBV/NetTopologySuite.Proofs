(* ============================================================================
   nts-eval micro unit — claimId 65-a (RED)
   ----------------------------------------------------------------------------
   Flat endcap geometry is the DIAMETER SEGMENT through the offset terminal
   point, perpendicular to the terminal unit tangent: endpoints p ± r·J(t)
   (J = π/2 rotation), and the cap is exactly the segment joining them —
   equivalently, the perpendicular chord of the radius-r circle at p.

   RED SURFACE.  The headline biconditional is STATED below
   (`flat_endcap_is_diameter_segment_claim`) and deliberately NOT proved in
   this unit — no `Admitted` (forbidden), no `Axiom`; the claim is a named
   `Definition ... : Prop`, so the Eval → Qed matcher finds no Qed lemma of
   this statement here or in production and reports 65-a red.  Green must
   land `Lemma flat_endcap_is_diameter_segment : flat_endcap_is_diameter_
   segment_claim.` (or the unfolded statement verbatim) under classical
   reals in the production Buffer/Offset lane (`BufferEndcap.v`
   neighbourhood), same WITNESS tag.

   What IS Qed here: the rational witness pins that fix the intended
   semantics so a wrong Green cannot close the claim vacuously —
   axis-aligned unit segment ending at p = (1,0), tangent t = (1,0), r = 1:
   the cap endpoints are exactly (1,-1) and (1,1); both lie on the
   perpendicular through p at squared distance exactly r²; interior sample
   (1, 1/2) satisfies both sides; and two MISMATCH probes — (1, 3/2) is on
   the perpendicular but outside the disk, (3/2, 0) is off the
   perpendicular — refute the two tempting wrong geometries (infinite
   perpendicular line; cap along the tangent).

   WITNESS claimId: 65-a
   Lemma (Green target): flat_endcap_is_diameter_segment
   ========================================================================== *)

(* WITNESS {"claimId":"65-a","topic":"buffer","lemma":"flat_endcap_is_diameter_segment","title":"Flat endcap = perpendicular diameter segment at the offset terminal"} *)

From Stdlib Require Import Reals Lra.
Local Open Scope R_scope.

Record Point : Type := mkPoint { px : R; py : R }.

Definition dist_sq (p q : Point) : R :=
  (px p - px q) * (px p - px q) + (py p - py q) * (py p - py q).

(* Q on the closed segment P0–P1 (parametric, as in the corpus Segment.v). *)
Definition between (P0 P1 Q : Point) : Prop :=
  exists s : R, 0 <= s /\ s <= 1 /\
    px Q = (1 - s) * px P0 + s * px P1 /\
    py Q = (1 - s) * py P0 + s * py P1.

(* J = π/2 rotation of the unit tangent: J(tx,ty) = (-ty, tx). *)
Definition cap_plus (p t : Point) (r : R) : Point :=
  mkPoint (px p - r * py t) (py p + r * px t).
Definition cap_minus (p t : Point) (r : R) : Point :=
  mkPoint (px p + r * py t) (py p - r * px t).

(* -------------------------------------------------------------------------- *)
(* The 65-a claim (RED: stated, not closed).                                  *)
(* Flat endcap = { q : q ⊥-aligned with t through p, within radius r }        *)
(*             = the segment cap_minus(p,t,r) — cap_plus(p,t,r).              *)
(* -------------------------------------------------------------------------- *)

Definition flat_endcap_is_diameter_segment_claim : Prop :=
  forall (p t : Point) (r : R),
    0 < r ->
    px t * px t + py t * py t = 1 ->
    forall q : Point,
      between (cap_minus p t r) (cap_plus p t r) q <->
      ((px q - px p) * px t + (py q - py p) * py t = 0 /\
       dist_sq q p <= r * r).

(* RED: no proof of the claim in this unit.  Green target statement:
     Lemma flat_endcap_is_diameter_segment :
       flat_endcap_is_diameter_segment_claim.
   in the production Buffer/Offset lane, same WITNESS tag. *)

(* -------------------------------------------------------------------------- *)
(* Rational witness pins (Qed at Red).                                        *)
(* Axis-aligned unit segment (0,0)→(1,0): terminal p=(1,0), tangent t=(1,0),  *)
(* r = 1.  Diameter segment must be (1,-1)—(1,1).                             *)
(* -------------------------------------------------------------------------- *)

Definition w_p : Point := mkPoint 1 0.
Definition w_t : Point := mkPoint 1 0.
Definition w_r : R := 1.

Lemma w_tangent_unit : px w_t * px w_t + py w_t * py w_t = 1.
Proof. unfold w_t; simpl. lra. Qed.

(* The cap endpoints are exactly (1,1) and (1,-1). *)
Lemma w_cap_plus_eq  : cap_plus  w_p w_t w_r = mkPoint 1 1.
Proof. unfold cap_plus, w_p, w_t, w_r; simpl. f_equal; lra. Qed.

Lemma w_cap_minus_eq : cap_minus w_p w_t w_r = mkPoint 1 (-1).
Proof. unfold cap_minus, w_p, w_t, w_r; simpl. f_equal; lra. Qed.

(* Both endpoints: on the perpendicular through p, at squared distance r². *)
Lemma w_endpoints_pin :
  ((px (cap_plus w_p w_t w_r) - px w_p) * px w_t
   + (py (cap_plus w_p w_t w_r) - py w_p) * py w_t = 0 /\
   dist_sq (cap_plus w_p w_t w_r) w_p = w_r * w_r) /\
  ((px (cap_minus w_p w_t w_r) - px w_p) * px w_t
   + (py (cap_minus w_p w_t w_r) - py w_p) * py w_t = 0 /\
   dist_sq (cap_minus w_p w_t w_r) w_p = w_r * w_r).
Proof.
  unfold cap_plus, cap_minus, dist_sq, w_p, w_t, w_r; simpl.
  repeat split; lra.
Qed.

(* Interior sample (1, 1/2): on the segment AND satisfies the right side. *)
Lemma w_interior_between :
  between (cap_minus w_p w_t w_r) (cap_plus w_p w_t w_r) (mkPoint 1 (1/2)).
Proof.
  unfold between, cap_minus, cap_plus, w_p, w_t, w_r; simpl.
  exists (3/4). repeat split; lra.
Qed.

Lemma w_interior_rhs :
  (px (mkPoint 1 (1/2)) - px w_p) * px w_t
  + (py (mkPoint 1 (1/2)) - py w_p) * py w_t = 0 /\
  dist_sq (mkPoint 1 (1/2)) w_p <= w_r * w_r.
Proof. unfold dist_sq, w_p, w_t, w_r; simpl. split; lra. Qed.

(* MISMATCH PROBE 1: (1, 3/2) is on the perpendicular but OUTSIDE the disk —
   refutes "cap = the whole perpendicular line". *)
Lemma w_probe_outside_disk :
  (px (mkPoint 1 (3/2)) - px w_p) * px w_t
  + (py (mkPoint 1 (3/2)) - py w_p) * py w_t = 0 /\
  ~ dist_sq (mkPoint 1 (3/2)) w_p <= w_r * w_r.
Proof. unfold dist_sq, w_p, w_t, w_r; simpl. split; lra. Qed.

(* MISMATCH PROBE 2: (3/2, 0) is inside the disk but OFF the perpendicular —
   refutes "cap lies along the tangent direction". *)
Lemma w_probe_off_perpendicular :
  dist_sq (mkPoint (3/2) 0) w_p <= w_r * w_r /\
  ~ (px (mkPoint (3/2) 0) - px w_p) * px w_t
    + (py (mkPoint (3/2) 0) - py w_p) * py w_t = 0.
Proof. unfold dist_sq, w_p, w_t, w_r; simpl. split; lra. Qed.

(* ============================================================================
   NetTopologySuite.Proofs.Flocq.Intersect_b64_exact_refs
   ----------------------------------------------------------------------------
   PURE-R REFERENCE LAYER: the R-side Cramer's-rule reference expressions
   `intersect_param_s`, `intersect_x_R`, `intersect_y_R`, and their
   dovetail with the clean-lane closed form
   `Intersect.strict_intersection_point` (two pure `ring` identities).

   This module imports NO Flocq: its Print Assumptions footprint is the
   standard Reals trio only (no `Classical_Prop.classic`), so it is
   deliberately NOT on docs/audit-exceptions.txt -- the first
   Intersect-lineage module to leave the Category C1 block, mirroring
   PassesThrough_b64_grid_gap_kernel.v (meso-audit B4).  The binary64
   layers (Intersect_b64_exact_core.v and up) state the forward-error
   story against these references.

   Split out of the former 2888-line Intersect_b64_exact.v monolith
   (Phase 1, line-line intersection point; topic: binary64);
   Intersect_b64_exact.v remains as the Require Export umbrella, so
   reverse dependencies import unchanged.  Slice text, declarations,
   and Print Assumptions footers carried over verbatim.  No Admitted,
   no Axiom, no Parameter.
   ============================================================================ *)

From Stdlib Require Import Reals.

From NTS.Proofs Require Import Distance Orientation Intersect.

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* R-side Cramer's-rule reference expressions.                                *)
(*                                                                            *)
(* Convention: the segment we parameterise is P0->P1, with `s` the parameter *)
(* along it; the segment we test against is Q0->Q1.  Matches the b64 code:  *)
(*    s := orient(Q0,Q1,P0) / (orient(Q0,Q1,P0) - orient(Q0,Q1,P1))         *)
(* -------------------------------------------------------------------------- *)

Definition intersect_param_s (P0 P1 Q0 Q1 : Point) : R :=
  cross Q0 Q1 P0 / (cross Q0 Q1 P0 - cross Q0 Q1 P1).

Definition intersect_x_R (P0 P1 Q0 Q1 : Point) : R :=
  px P0 + intersect_param_s P0 P1 Q0 Q1 * (px P1 - px P0).

Definition intersect_y_R (P0 P1 Q0 Q1 : Point) : R :=
  py P0 + intersect_param_s P0 P1 Q0 Q1 * (py P1 - py P0).

(* -------------------------------------------------------------------------- *)
(* Dovetail with the clean-lane closed form (theories/Intersect.v).           *)
(*                                                                            *)
(* `Intersect.strict_intersection_point A B C D` (the convex combination of   *)
(* C and D at t = cross A B C / (cross A B C - cross A B D)) is the named      *)
(* closed form of *the* proper-crossing intersection point, proved to equal   *)
(* every shared point by `Intersect.strict_intersection_eq_formula`.          *)
(*                                                                            *)
(* `intersect_x_R` / `intersect_y_R` are the exact R-side targets that        *)
(* `b64_intersect_point_{x,y}_forward_error` bound the rounded binary64        *)
(* projections against (and which the oracle's INTERSECT_POINT_XY mode         *)
(* computes).  Our convention runs along P0->P1 using cross(Q0,Q1,.), so with  *)
(* A:=Q0, B:=Q1, C:=P0, D:=P1 the reference IS that closed form -- and it      *)
(* holds UNCONDITIONALLY (no proper-crossing hypothesis), since both sides are *)
(* the same Cramer expression: a pure `ring` identity in the parameter.       *)
(* Hence the forward-error story is stated against the canonical closed-form   *)
(* intersection point, not an ad-hoc Cramer expression.                       *)
(* -------------------------------------------------------------------------- *)

Lemma intersect_x_R_eq_strict_point :
  forall P0 P1 Q0 Q1 : Point,
    intersect_x_R P0 P1 Q0 Q1
      = px (Intersect.strict_intersection_point Q0 Q1 P0 P1).
Proof.
  intros P0 P1 Q0 Q1.
  unfold intersect_x_R, intersect_param_s,
         Intersect.strict_intersection_point, px.
  simpl. ring.
Qed.

Lemma intersect_y_R_eq_strict_point :
  forall P0 P1 Q0 Q1 : Point,
    intersect_y_R P0 P1 Q0 Q1
      = py (Intersect.strict_intersection_point Q0 Q1 P0 P1).
Proof.
  intros P0 P1 Q0 Q1.
  unfold intersect_y_R, intersect_param_s,
         Intersect.strict_intersection_point, py.
  simpl. ring.
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions intersect_x_R_eq_strict_point.
Print Assumptions intersect_y_R_eq_strict_point.

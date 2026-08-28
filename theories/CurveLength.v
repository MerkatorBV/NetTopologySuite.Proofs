(* ============================================================================
   NetTopologySuite.Proofs.CurveLength
   ----------------------------------------------------------------------------
   The corpus-canonical metric-length SPEC (#508 M-LEN-ZOO, ADR-0004;
   CONTEXT.md "Metric length"): the length of a parameterized curve over
   [a, b] is the supremum of the lengths of its inscribed polylines — the
   classical rectifiable length, integration-free.

   The spec is a PREDICATE, not a function:

     is_curve_length g a b L  :=  is_lub (inscribed_len g a b) L

   so no completeness axiom is spent constructing L; each per-type length
   obligation (#508 order: ellipse -> cubic Bezier -> clothoid -> NURBS,
   arc first as the served member) states that its formula SATISFIES the
   spec, at whatever tier it can reach.

   Proven here (the base facts every obligation leans on):
     - curve_length_ge_chord : chord <= L      (the lower sandwich half)
     - curve_length_nonneg   : 0 <= L
     - curve_length_unique   : the spec pins L
     - curve_length_additive : L(a,c) = L(a,b) + L(b,c)

   curve_length_additive is the aggregation theorem behind LENGTH_UNIFIED's
   "CC: sum of member lengths" semantics — before this file that was a
   differential observation only (#508 differential datapoint, 2026-08-22).
   The arc obligation itself (r*theta satisfies is_curve_length for the
   circular-arc parameterization) is the NEXT rung, not this file.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra List.
From NTS.Proofs Require Import Distance.
Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* A parameterized curve.  No continuity is assumed by the spec itself:       *)
(* inscribed polylines and their supremum make sense for any map R -> Point,  *)
(* and each per-type obligation supplies its own parameterization.            *)
(* -------------------------------------------------------------------------- *)

Definition Curve : Type := R -> Point.

(* Length of the polyline that starts at (g t) and visits (g u) for each u
   along ts, in order. *)
Fixpoint polyline_len (g : Curve) (t : R) (ts : list R) : R :=
  match ts with
  | [] => 0
  | u :: tl => dist (g t) (g u) + polyline_len g u tl
  end.

(* ts is a weakly increasing chain of parameters from lo to hi.  Weak
   inequalities: a repeated parameter contributes dist x x = 0, so nothing
   is lost and refinements stay painless. *)
Fixpoint chain (lo : R) (ts : list R) (hi : R) : Prop :=
  match ts with
  | [] => lo <= hi
  | u :: tl => lo <= u /\ chain u tl hi
  end.

(* l is the length of an inscribed polyline of g over [a, b]: interior
   sample parameters ts, endpoints always included. *)
Definition inscribed_len (g : Curve) (a b l : R) : Prop :=
  exists ts, chain a ts b /\ l = polyline_len g a (ts ++ [b]).

(* THE SPEC (#508): L is the metric length of g over [a, b]. *)
Definition is_curve_length (g : Curve) (a b L : R) : Prop :=
  is_lub (inscribed_len g a b) L.

Definition rectifiable (g : Curve) (a b : R) : Prop :=
  exists L, is_curve_length g a b L.

(* -------------------------------------------------------------------------- *)
(* Base facts.                                                                *)
(* -------------------------------------------------------------------------- *)

(* The single chord is an inscribed polyline (the empty refinement). *)
Lemma inscribed_chord : forall (g : Curve) a b,
  a <= b -> inscribed_len g a b (dist (g a) (g b)).
Proof.
Qed.

(* Lower sandwich half: no curve is shorter than its chord. *)
Theorem curve_length_ge_chord : forall (g : Curve) a b L,
  a <= b -> is_curve_length g a b L -> dist (g a) (g b) <= L.
Proof.
Qed.

Theorem curve_length_nonneg : forall (g : Curve) a b L,
  a <= b -> is_curve_length g a b L -> 0 <= L.
Proof.
Qed.

(* The spec pins its value: lub uniqueness. *)
Theorem curve_length_unique : forall (g : Curve) a b L1 L2,
  is_curve_length g a b L1 -> is_curve_length g a b L2 -> L1 = L2.
Proof.
Qed.

(* -------------------------------------------------------------------------- *)
(* Aggregation: length is additive at any waypoint.                           *)
(* -------------------------------------------------------------------------- *)

Theorem curve_length_additive : forall (g : Curve) a b c L1 L2,
  a <= b -> b <= c ->
  is_curve_length g a b L1 -> is_curve_length g b c L2 ->
  is_curve_length g a c (L1 + L2).
Proof.
Qed.

Print Assumptions curve_length_additive.

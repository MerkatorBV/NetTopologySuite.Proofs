(* ============================================================================
   NetTopologySuite.Proofs.InArc
   ----------------------------------------------------------------------------
   Issue #64 subtask 64-c — RED surface only: the in-arc predicate for a
   point on the minor arc between two distinct endpoints on a circle.

   WHAT THIS FILE IS.  The smallest failing claim for "point on minor arc
   between endpoints satisfies InArc", with a rational unit-circle witness.
   Green / Refactor are out of scope: no production body that closes the
   goal, no `Admitted` as a fake green.  Open goals end with `Abort` (same
   discipline as HobbyTheorem_b64 / B64_FastExpansionSum — an Aborted claim
   is not `apply`-able and cannot silently poison consumers).

   WHAT IS MISSING ON MAIN (why the focused check fails without Green).
   There is no geometric `InArc` that ties central-angle order to minor-arc
   membership.  Existing pieces are related but not this surface:
     - `inCircle_R` (ArcOrient) — in-circle, not in-arc;
     - `on_arc` / `arc_span_contains` (CurveRingSimple / ArcIntersect) —
       three-control-point span membership, not the two-endpoint + centre
       minor-arc form stated here;
     - `arc_minor` (ArcOrient) — labels a control arc as subtended ≤ π, not
       point membership on the minor arc between endpoints.
   Permutation-cycle helpers named `InArc` in PermCycle*.v are unrelated.

   INTENDED PREDICATE (spec shape for Green).  `InArc O A B P` means:
     - A, B, P all lie on the circle centred at O of radius |O A| > 0;
     - A and B are distinct;
     - the principal central angle γ = ∠AOB satisfies |γ| < π (strict minor);
     - the principal central angle θ = ∠AOP is on the same side of ray OA
       as γ and |θ| ≤ |γ| (P on the closed minor arc from A to B).
   The Red definition below packages that shape via `angle_between` but does
   NOT discharge the rational witness; Green Qeds the claims once the
   central-angle order is fully wired and the witness arithmetic closed.

   RATIONAL WITNESS (unit circle, centre origin).
     A = (1, 0)           principal angle 0
     P = (3/5, 4/5)       3-4-5 point, angle atan2(4/5,3/5) ∈ (0, π/2)
     B = (0, 1)           principal angle π/2
     Q = (-1, 0)          principal angle π  (major-arc counter-position)
   Endpoints A,B are distinct, minor arc A→B has central angle π/2 < π, and
   P is strictly between them on that minor arc.  Q lies on the complementary
   major arc and must NOT satisfy InArc.

   Refs: issue #64, docs/issue-64-arc-primitives-triage.md (ask #3 / in-arc).
   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Grok (grok-4.5)
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import Distance Atan2 AngleBetween.

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  InArc — minor-arc membership via central-angle order.                  *)
(*                                                                            *)
(* Spec shape only.  Green is authorised to refine the angular clauses if a   *)
(* half-open / endpoint convention needs to match JTS `isOnArc` exactly; the  *)
(* Red claim is the interior minor-arc witness below.                         *)
(* -------------------------------------------------------------------------- *)

(** Signed central angle at [O] from ray [O]->[X] to ray [O]->[Y]. *)
Definition central_angle (O X Y : Point) : R :=
  angle_between (px X - px O) (py X - py O)
                (px Y - px O) (py Y - py O).

(** [InArc O A B P]: [P] lies on the closed minor arc of the circle
    centred at [O] from endpoint [A] to endpoint [B].

    Clauses:
      - positive common radius [r = dist O A];
      - [B] and [P] on that circle;
      - endpoints distinct;
      - principal sweep [γ = central_angle O A B] is a strict minor ([|γ| < π]);
      - [θ = central_angle O A P] has the same sign as [γ] (or is zero) and
        [|θ| ≤ |γ|] (angularly between [A] and [B], including endpoints).

    RED: stated for typechecking and the failing claim; the rational witness
    is not discharged here.  Green ties this fully to central-angle order and
    Qeds [in_arc_point_on_minor_arc]. *)
Definition InArc (O A B P : Point) : Prop :=
  let r := dist O A in
  0 < r /\
  dist O B = r /\
  dist O P = r /\
  A <> B /\
  let gamma := central_angle O A B in
  let theta := central_angle O A P in
  Rabs gamma < PI /\
  0 <= theta * gamma /\
  Rabs theta <= Rabs gamma.

(* -------------------------------------------------------------------------- *)
(* §2  Rational unit-circle witness (3-4-5 interior point).                   *)
(* -------------------------------------------------------------------------- *)

Definition in_arc_O : Point := mkPoint 0 0.
Definition in_arc_A : Point := mkPoint 1 0.
Definition in_arc_B : Point := mkPoint 0 1.
(** Interior test point on the minor arc A→B (rational coords, on unit circle). *)
Definition in_arc_P : Point := mkPoint (3/5) (4/5).
(** Counter-position: on the complementary major arc from A to B. *)
Definition in_arc_Q_major : Point := mkPoint (-1) 0.

(* Geometric scaffolding for the witness — Qed.  Does not mention InArc, so
   it cannot accidentally close the Red claims below. *)

Lemma in_arc_A_on_unit :
  dist_sq in_arc_O in_arc_A = 1.
Proof. unfold in_arc_O, in_arc_A, dist_sq; cbn [px py]; lra. Qed.

Lemma in_arc_B_on_unit :
  dist_sq in_arc_O in_arc_B = 1.
Proof. unfold in_arc_O, in_arc_B, dist_sq; cbn [px py]; lra. Qed.

Lemma in_arc_P_on_unit :
  dist_sq in_arc_O in_arc_P = 1.
Proof. unfold in_arc_O, in_arc_P, dist_sq; cbn [px py]; field. Qed.

Lemma in_arc_Q_major_on_unit :
  dist_sq in_arc_O in_arc_Q_major = 1.
Proof. unfold in_arc_O, in_arc_Q_major, dist_sq; cbn [px py]; lra. Qed.

Lemma in_arc_endpoints_distinct : in_arc_A <> in_arc_B.
Proof.
  unfold in_arc_A, in_arc_B. intros Heq.
  assert (Hpx : px (mkPoint 1 0) = px (mkPoint 0 1)) by (rewrite Heq; reflexivity).
  cbn in Hpx. lra.
Qed.

Lemma in_arc_P_not_endpoint :
  in_arc_P <> in_arc_A /\ in_arc_P <> in_arc_B.
Proof.
  unfold in_arc_P, in_arc_A, in_arc_B. split; intros Heq.
  - assert (Hpy : py (mkPoint (3/5) (4/5)) = py (mkPoint 1 0))
      by (rewrite Heq; reflexivity).
    cbn in Hpy. lra.
  - assert (Hpx : px (mkPoint (3/5) (4/5)) = px (mkPoint 0 1))
      by (rewrite Heq; reflexivity).
    cbn in Hpx. lra.
Qed.

Lemma in_arc_Q_major_not_endpoint :
  in_arc_Q_major <> in_arc_A /\ in_arc_Q_major <> in_arc_B.
Proof.
  unfold in_arc_Q_major, in_arc_A, in_arc_B. split; intros Heq.
  - assert (Hpx : px (mkPoint (-1) 0) = px (mkPoint 1 0))
      by (rewrite Heq; reflexivity).
    cbn in Hpx. lra.
  - assert (Hpx : px (mkPoint (-1) 0) = px (mkPoint 0 1))
      by (rewrite Heq; reflexivity).
    cbn in Hpx. lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Focused Red claims — open, not Admitted.                               *)
(*                                                                            *)
(* These are the surface Eval / nts-eval will re-check after Green is          *)
(* authorised.  Until then they remain Abort: neither closed nor disproven.   *)
(* -------------------------------------------------------------------------- *)

(** RED (64-c): a point lying on the minor arc between two distinct endpoints
    on the unit circle satisfies [InArc].  Witness: [in_arc_P] between
    [in_arc_A] and [in_arc_B] about [in_arc_O]. *)
Theorem in_arc_point_on_minor_arc :
  InArc in_arc_O in_arc_A in_arc_B in_arc_P.
Proof.
  (* RED #64-c: Green closes once InArc's central-angle order is discharged
     on the rational unit-circle witness (0 < θ_P < θ_B = π/2 < π).
     Do not Admitted — that would be a fake green. *)
Abort.

(** RED counter-position (64-c): a point on the complementary major arc does
    not satisfy [InArc] for the same endpoints.  Witness: [in_arc_Q_major]. *)
Theorem in_arc_point_on_major_arc_rejected :
  ~ InArc in_arc_O in_arc_A in_arc_B in_arc_Q_major.
Proof.
  (* RED #64-c: Green closes the rejection (|θ_Q| = π > π/2 = |γ|).
     Do not Admitted. *)
Abort.

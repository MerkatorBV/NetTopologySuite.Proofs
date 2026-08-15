(* ============================================================================
   nts-eval micro unit — claimId 9005-a — RED (unproved teaching claim)
   ----------------------------------------------------------------------------
   Pole of inaccessibility, planar teaching instance: the PIA of a
   three-point shoreline over its triangle is the equidistant point,
   touching EXACTLY THREE closest shoreline points.

   Board card #9005: Garcia-Castellanos, D. & Lombardo, U. (2007), "Poles
   of inaccessibility: A calculation algorithm for the remotest places on
   earth", doi:10.1080/14702540801897809.

   HONEST SCOPE (the card's gap, kept open on purpose).  The paper's PIA
   is SPHERICAL (great-circle distances); this corpus is planar
   throughout, and plane MIC/LEC ≠ spherical PIA.  The paper therefore
   gets NO production cite in theories/ (library-footnotes: a module cite
   would be false ancestry).  What CAN be taught planarly — and what this
   micro unit claims — is the paper's DEFINITIONAL signature: the PIA is
   the centre of the largest circle empty of the shoreline, and in the
   generic case it is pinned by exactly three closest shoreline points.

   Teaching instance, fully rational in the squared metric: shoreline
   obstacles A = (0,0), B = (4,0), C = (0,4); land domain = the closed
   triangle ABC; PIA = the hypotenuse midpoint (2,2), empty radius √8,
   equidistant from ALL THREE obstacles (dist_sq = 8 to each).
   Maximality is the nearest-vertex case split: on x ≤ 2 ∧ y ≤ 2 the
   clearance² at A is ≤ 8; on x > 2 (so y < 2) the clearance² at B is
   ≤ 8; on y > 2 the clearance² at C is ≤ 8.

   RED GATE (micro).  The headline body is deliberately unproved: `rocq c`
   on this file fails at `Qed` with "Attempt to save an incomplete proof"
   — an unproved obligation, not a syntax error; everything above it
   elaborates cleanly, so the failing surface is exactly one goal.  No
   `Admitted`, no `admit` tactic, no `Axiom`, no `Parameter`.

   Self-contained for the nts-eval harness: no NTS.Proofs Requires.
   Production twins named after theories/LargestEmptyCircle.v
   (empty_disk / largest_empty_disk); this unit is the mutation SEED for
   the engine's vacuity suite.

   WITNESS claimId: 9005-a
   Lemma: pia_triangle_three_touch
   ========================================================================== *)

(* WITNESS {"claimId":"9005-a","topic":"teaching","lemma":"pia_triangle_three_touch","title":"Planar PIA teaching instance: LEC centre of a 3-point shoreline touches exactly three closest points"} *)

From Stdlib Require Import Reals Lra.
Local Open Scope R_scope.

(* ---- Minimal geometry carrier (Distance twins) ---------------------------- *)

Record Point : Type := mkPoint { px : R; py : R }.

Definition dist_sq (P Q : Point) : R :=
  (px P - px Q) * (px P - px Q) + (py P - py Q) * (py P - py Q).

Definition dist (P Q : Point) : R := sqrt (dist_sq P Q).

Lemma sqr_nonneg : forall x : R, 0 <= x * x.
Proof. intros x. nra. Qed.

Lemma dist_sq_nonneg : forall P Q, 0 <= dist_sq P Q.
Proof.
  intros P Q. unfold dist_sq.
  pose proof (sqr_nonneg (px P - px Q)).
  pose proof (sqr_nonneg (py P - py Q)).
  lra.
Qed.

Lemma dist_nonneg : forall P Q, 0 <= dist P Q.
Proof. intros P Q. apply sqrt_pos. Qed.

Lemma dist_mul_self : forall P Q, dist P Q * dist P Q = dist_sq P Q.
Proof. intros P Q. unfold dist. apply sqrt_sqrt. apply dist_sq_nonneg. Qed.

(* ---- Production twins (theories/LargestEmptyCircle.v) --------------------- *)

Definition Region : Type := Point -> Prop.

(** The disk (O, r) is empty of the obstacle set. *)
Definition empty_disk (obs : Region) (O : Point) (r : R) : Prop :=
  0 <= r /\ forall P : Point, obs P -> r <= dist O P.

(** Largest empty disk with centre constrained to a domain. *)
Definition largest_empty_disk (obs dom : Region) (O : Point) (r : R) : Prop :=
  dom O /\ empty_disk obs O r /\
  forall (O' : Point) (r' : R),
    dom O' -> empty_disk obs O' r' -> r' <= r.

(* ---- The teaching configuration -------------------------------------------- *)

Definition shore_A : Point := mkPoint 0 0.
Definition shore_B : Point := mkPoint 4 0.
Definition shore_C : Point := mkPoint 0 4.

(** The three-point shoreline. *)
Definition shoreline : Region :=
  fun P : Point => P = shore_A \/ P = shore_B \/ P = shore_C.

(** The land: the closed triangle ABC. *)
Definition land : Region :=
  fun P : Point => 0 <= px P /\ 0 <= py P /\ px P + py P <= 4.

(** The pole of inaccessibility: the hypotenuse midpoint. *)
Definition pia : Point := mkPoint 2 2.

(** Its clearance: √8 (squared clearance 8, rational). *)
Definition pia_radius : R := sqrt 8.

(* ---- Headline (9005-a) — RED, unproved ------------------------------------- *)

(** The PIA of the three-point shoreline over the closed triangle is the
    hypotenuse midpoint with clearance √8 — the planar teaching instance
    of Garcia-Castellanos & Lombardo's definition.

    RED: the body is intentionally left open.  Proving it is the micro
    Green and is out of scope in this commit. *)
Theorem pia_triangle_three_touch :
  largest_empty_disk shoreline land pia pia_radius.
Proof.
  (* RED — unproved obligation.  Do not close this with the `admit` tactic
     or with `Admitted`: the corpus invariant forbids both, and the Red
     gate wants `rocq c` to fail here with "Attempt to save an incomplete
     proof". *)
Qed.

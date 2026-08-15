(* ============================================================================
   nts-eval micro unit — claimId 9005-a — GREEN (Qed-closed teaching claim;
   Red surface planted and witnessed in the previous commit)
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

   GREEN (micro).  The headline is Qed: domain membership is arithmetic;
   emptiness is the three squared-distance-8 equalities; maximality is
   the nearest-vertex case split (the x > 2 ∧ y > 2 quadrant is outside
   the land).  Anti-vacuity content for the mutation suite: the three
   equidistance pins (dist_sq = 8 to EACH shoreline point — the paper's
   exactly-three-closest-points signature), the centroid probe (the
   centroid cannot support the PIA radius: its clearance² to A is 32/9),
   and the hypotenuse-drift pin ((3,1) has clearance² 2 at B).  Qed-closed
   throughout; no Axiom, no Parameter.

   Self-contained for the nts-eval harness: no NTS.Proofs Requires.
   Production twins named after theories/LargestEmptyCircle.v
   (empty_disk / largest_empty_disk); this unit is the mutation SEED for
   the engine's 5-op vacuity suite.

   WITNESS claimId: 9005-a
   Lemma: pia_triangle_three_touch
   ========================================================================== *)

(* WITNESS {"claimId":"9005-a","topic":"teaching","lemma":"pia_triangle_three_touch","title":"Planar PIA teaching instance: LEC centre of a 3-point shoreline touches exactly three closest points"} *)
(* ADR-0001: self-contained smoke *)

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

(* ---- Squared-bound bridge (LargestEmptyCircle twin) ------------------------ *)

Lemma empty_disk_sq_bound :
  forall (obs : Region) (O : Point) (r : R) (P : Point),
    empty_disk obs O r -> obs P -> r * r <= dist_sq O P.
Proof.
  intros obs O r P [Hr He] HP.
  specialize (He P HP).
  rewrite <- (dist_mul_self O P).
  apply Rmult_le_compat; assumption.
Qed.

(* ---- Headline (9005-a) — GREEN ---------------------------------------------- *)

(** The PIA of the three-point shoreline over the closed triangle is the
    hypotenuse midpoint with clearance √8 — the planar teaching instance
    of Garcia-Castellanos & Lombardo's definition. *)
Theorem pia_triangle_three_touch :
  largest_empty_disk shoreline land pia pia_radius.
Proof.
  unfold largest_empty_disk, pia_radius.
  split; [| split].
  - (* Domain: the PIA lies on the land (hypotenuse midpoint). *)
    unfold land, pia. simpl. repeat split; lra.
  - (* Emptiness: each shoreline point is at distance exactly √8. *)
    split; [apply sqrt_pos |].
    intros P HP.
    destruct HP as [-> | [-> | ->]]; unfold dist.
    + replace (dist_sq pia shore_A) with 8
        by (unfold dist_sq, pia, shore_A; simpl; lra).
      lra.
    + replace (dist_sq pia shore_B) with 8
        by (unfold dist_sq, pia, shore_B; simpl; lra).
      lra.
    + replace (dist_sq pia shore_C) with 8
        by (unfold dist_sq, pia, shore_C; simpl; lra).
      lra.
  - (* Maximality: nearest-vertex case split. *)
    intros O' r' Hdom Hemp.
    pose proof (empty_disk_sq_bound shoreline O' r' shore_A
                  Hemp (or_introl eq_refl)) as HA.
    pose proof (empty_disk_sq_bound shoreline O' r' shore_B
                  Hemp (or_intror (or_introl eq_refl))) as HB.
    pose proof (empty_disk_sq_bound shoreline O' r' shore_C
                  Hemp (or_intror (or_intror eq_refl))) as HC.
    destruct Hemp as [Hr' _].
    destruct Hdom as [Hx0 [Hy0 Hxy]].
    unfold dist_sq, shore_A, shore_B, shore_C in HA, HB, HC.
    simpl in HA, HB, HC.
    assert (H8 : sqrt 8 * sqrt 8 = 8) by (apply sqrt_sqrt; lra).
    pose proof (sqrt_pos 8) as Hs8.
    destruct (Rle_dec (px O') 2) as [Hx | Hx];
      destruct (Rle_dec (py O') 2) as [Hy | Hy].
    + (* x <= 2, y <= 2: shore_A is within √8. *)
      assert (Hxx : px O' * px O' <= 4) by nra.
      assert (Hyy : py O' * py O' <= 4) by nra.
      nra.
    + (* x <= 2, y > 2: shore_C is within √8. *)
      apply Rnot_le_lt in Hy.
      assert (Hxx : px O' * px O' <= 4) by nra.
      assert (Hyy : (py O' - 4) * (py O' - 4) <= 4) by nra.
      nra.
    + (* x > 2, y <= 2: shore_B is within √8. *)
      apply Rnot_le_lt in Hx.
      assert (Hxx : (px O' - 4) * (px O' - 4) <= 4) by nra.
      assert (Hyy : py O' * py O' <= 4) by nra.
      nra.
    + (* x > 2 and y > 2 is off the land: x + y > 4. *)
      apply Rnot_le_lt in Hx. apply Rnot_le_lt in Hy.
      exfalso. lra.
Qed.

(** Projections for consumers of the teaching claim. *)
Corollary pia_empty : empty_disk shoreline pia pia_radius.
Proof. exact (proj1 (proj2 pia_triangle_three_touch)). Qed.

Corollary pia_radius_maximal :
  forall (O' : Point) (r' : R),
    land O' -> empty_disk shoreline O' r' -> r' <= pia_radius.
Proof. exact (proj2 (proj2 pia_triangle_three_touch)). Qed.

(* ---- Rational pins: the exactly-three-closest-points signature ------------- *)

(** The PIA is equidistant from ALL THREE shoreline points — squared
    distance exactly 8 to each (Garcia-Castellanos & Lombardo's generic
    PIA signature, planar instance). *)
Lemma pia_touch_A : dist_sq pia shore_A = 8.
Proof. unfold dist_sq, pia, shore_A. simpl. lra. Qed.

Lemma pia_touch_B : dist_sq pia shore_B = 8.
Proof. unfold dist_sq, pia, shore_B. simpl. lra. Qed.

Lemma pia_touch_C : dist_sq pia shore_C = 8.
Proof. unfold dist_sq, pia, shore_C. simpl. lra. Qed.

Lemma pia_touches_all_three :
  dist_sq pia shore_A = dist_sq pia shore_B /\
  dist_sq pia shore_B = dist_sq pia shore_C.
Proof. rewrite pia_touch_A, pia_touch_B, pia_touch_C. split; reflexivity. Qed.

(* ---- Mismatch probes -------------------------------------------------------- *)

(** Centroid misreading kill: the triangle's centroid (4/3, 4/3) cannot
    support the PIA radius — its squared clearance to shore_A is only
    32/9 < 8.  (The PIA is a max-min point, not a mass centre.) *)
Lemma centroid_cannot_reach_pia_radius :
  ~ empty_disk shoreline (mkPoint (4/3) (4/3)) pia_radius.
Proof.
  intros Hemp.
  pose proof (empty_disk_sq_bound shoreline (mkPoint (4/3) (4/3))
                pia_radius shore_A Hemp (or_introl eq_refl)) as Hsq.
  unfold pia_radius in Hsq.
  rewrite (sqrt_sqrt 8) in Hsq by lra.
  unfold dist_sq, shore_A in Hsq. simpl in Hsq. lra.
Qed.

(** Hypotenuse-drift pin: sliding along the hypotenuse to (3,1) drops the
    clearance — squared distance to shore_B is 2 < 8. *)
Lemma hypotenuse_drift_clearance_drops :
  dist_sq (mkPoint 3 1) shore_B = 2.
Proof. unfold dist_sq, shore_B. simpl. lra. Qed.

Print Assumptions pia_triangle_three_touch.
Print Assumptions centroid_cannot_reach_pia_radius.

(* ============================================================================
   NetTopologySuite.Proofs.PenetrationGauge
   ----------------------------------------------------------------------------
   Wen & Zhang, "A Minimax Model for Generalized Penetration Distance
   Between Convex Sets by Directed Hausdorff Distance", IEEE Robotics and
   Automation Letters 7(3):6123-6130, 2022 (doi:10.1109/LRA.2022.3166111).
   Part 1: THE GAUGE IS ESSENTIALLY A NORM (paper Lemma 2), instantiated
   at the paper's own test gauges.

   The real-world problem: penetration distance (PD) -- how deep two
   overlapping bodies interpenetrate, i.e. the smallest translation that
   separates them -- drives collision response in robot motion planning,
   grasp-posture scoring, and VLSI compaction.  Wen-Zhang generalize PD
   from the Euclidean ball to an arbitrary GAUGE SET F (Manhattan,
   Chebyshev, hexagon "balls"): the generalized PD is the largest
   dilation lambda of F that still fits inside the Minkowski difference
   C = A (-) B (paper eq (9)).  Everything rests on the gauge function
   g_F(x) = inf { lam >= 0 | x in lam*F } behaving like a norm
   (paper Lemma 2: nonnegative, definite, absolutely homogeneous,
   sublinear, with lam*F = { g_F <= lam }).

   This file proves exactly that package for the paper's flagship
   non-l^p gauge -- the HEXAGON ball of eq (18a),
       F = { (x,y) | |x| + |y| <= 2, |y| <= 1 },
   whose gauge has the closed form
       gauge_hex (x,y) = max( (|x|+|y|)/2 , |y| ),
   together with the l^inf / l^1 gauges it interpolates:

     Lemma 2 (i,ii)  -> gauge_hex_nonneg, gauge_hex_zero_iff
     Lemma 2 (iii)   -> gauge_hex_abs_homogeneous
     Lemma 2 (iv)    -> gauge_hex_subadditive
     Lemma 2 (v)     -> gauge_hex_sublevel  (lam*F = sublevel set, all lam)
     eq (18a)        -> gauge_hex_unit_ball (the unit sublevel IS F)
     norm-equivalence sandwich -> gauge_sandwich
       (l^1)/2 <= hex <= l^inf <= l^1 : the "essentially a norm" claim
       made quantitative -- any gauge PD is within a factor 2 of the
       Chebyshev PD on this family.

   Rational pins fix the hexagon SHAPE (all six boundary features are
   rational): the east vertex (2,0), the corner (1,1) and the north edge
   point (0,1) all sit at gauge exactly 1, the interior probe (1,1/2)
   sits at 3/4 < 1, and two strict-inequality probes kill the "it is
   just l^inf" (would give 2 at the east vertex) and "just l^1" (would
   give 2 at the corner) misreadings.

   Everything is rational Rmax/Rabs case algebra: no sqrt, no limits --
   the paper's inf over dilations is replaced by the closed-form gauge
   and the sublevel characterisation, which is what a collision backend
   evaluates anyway.

   Relation to epic #423: paper eq (7) is the continuous directed
   Hausdorff h(A,B) = sup_{x in A} d_B(x); its discrete counterpart on
   point lists is micro-claim 423-a (eval/Claim423a.v, RED).  This lane
   is production enrichment and does not touch that claim surface.

   No `Admitted`, no `Axiom`, no `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  The three gauges of the paper's 2D experiments (Table I):              *)
(*     Chebyshev (l^inf ball), Manhattan (l^1 ball), and the hexagon (18a).   *)
(* -------------------------------------------------------------------------- *)

Definition gauge_inf (x y : R) : R := Rmax (Rabs x) (Rabs y).
Definition gauge_one (x y : R) : R := Rabs x + Rabs y.
Definition gauge_hex (x y : R) : R := Rmax ((Rabs x + Rabs y) / 2) (Rabs y).

(* -------------------------------------------------------------------------- *)
(* §0  Case-analysis workhorse: open Rmax/Rmin/Rabs into their Rle_dec /      *)
(*     Rcase_abs branches and finish linear branches with lra.                *)
(* -------------------------------------------------------------------------- *)

Ltac gauge_crunch :=
  unfold gauge_hex, gauge_inf, gauge_one, Rmax, Rmin, Rabs in *;
  repeat match goal with
         | |- context [Rle_dec ?a ?b] => destruct (Rle_dec a b)
         | H : context [Rle_dec ?a ?b] |- _ => destruct (Rle_dec a b)
         | |- context [Rcase_abs ?a] => destruct (Rcase_abs a)
         | H : context [Rcase_abs ?a] |- _ => destruct (Rcase_abs a)
         end;
  try lra.

(* Scaling out of a max by a nonnegative factor (used for homogeneity). *)
Lemma Rmax_scale : forall a u v, 0 <= a -> Rmax (a * u) (a * v) = a * Rmax u v.
Proof.
  intros a u v Ha. unfold Rmax.
  destruct (Rle_dec (a * u) (a * v)); destruct (Rle_dec u v); nra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  Paper Lemma 2 for the hexagon gauge.                                   *)
(* -------------------------------------------------------------------------- *)

(* Lemma 2 (ii), first half: nonnegativity. *)
Lemma gauge_hex_nonneg : forall x y, 0 <= gauge_hex x y.
Proof. intros x y. gauge_crunch. Qed.

(* Lemma 2 (ii), second half: definiteness -- gauge zero exactly at the
   origin.  (A zero-depth "penetration" means the bodies merely touch.) *)
Lemma gauge_hex_zero_iff : forall x y, gauge_hex x y = 0 <-> x = 0 /\ y = 0.
Proof.
  intros x y. split.
  - intros H. split; gauge_crunch.
  - intros [-> ->]. gauge_crunch.
Qed.

(* Lemma 2 (iii): absolute homogeneity g(a*x) = |a| * g(x). *)
Lemma gauge_hex_abs_homogeneous : forall a x y,
    gauge_hex (a * x) (a * y) = Rabs a * gauge_hex x y.
Proof.
  intros a x y. unfold gauge_hex.
  rewrite !Rabs_mult.
  replace ((Rabs a * Rabs x + Rabs a * Rabs y) / 2)
    with (Rabs a * ((Rabs x + Rabs y) / 2)) by field.
  rewrite Rmax_scale by apply Rabs_pos.
  reflexivity.
Qed.

(* Lemma 2 (iv): sublinearity (the triangle inequality). *)
Lemma gauge_hex_subadditive : forall x y x' y',
    gauge_hex (x + x') (y + y') <= gauge_hex x y + gauge_hex x' y'.
Proof.
  intros x y x' y'. unfold gauge_hex.
  pose proof (Rabs_triang x x') as Hx.
  pose proof (Rabs_triang y y') as Hy.
  pose proof (Rmax_l ((Rabs x + Rabs y) / 2) (Rabs y)) as A1.
  pose proof (Rmax_r ((Rabs x + Rabs y) / 2) (Rabs y)) as A2.
  pose proof (Rmax_l ((Rabs x' + Rabs y') / 2) (Rabs y')) as B1.
  pose proof (Rmax_r ((Rabs x' + Rabs y') / 2) (Rabs y')) as B2.
  apply Rmax_lub; lra.
Qed.

(* Lemma 2 (v): the dilation lam*F is exactly the gauge sublevel set --
   the identity that turns "largest inscribed dilation" (eq (9)) into a
   one-dimensional root-finding problem (eq (10)).  Holds for ALL lam:
   below 0 both sides are empty (gauge_hex_nonneg). *)
Lemma gauge_hex_sublevel : forall lam x y,
    gauge_hex x y <= lam <-> Rabs x + Rabs y <= 2 * lam /\ Rabs y <= lam.
Proof.
  intros lam x y. unfold gauge_hex. split.
  - intros H.
    pose proof (Rmax_l ((Rabs x + Rabs y) / 2) (Rabs y)).
    pose proof (Rmax_r ((Rabs x + Rabs y) / 2) (Rabs y)).
    lra.
  - intros [H1 H2]. apply Rmax_lub; lra.
Qed.

(* eq (18a): the unit sublevel is the paper's hexagon F itself. *)
Lemma gauge_hex_unit_ball : forall x y,
    gauge_hex x y <= 1 <-> Rabs x + Rabs y <= 2 /\ Rabs y <= 1.
Proof.
  intros x y.
  pose proof (gauge_hex_sublevel 1 x y) as H.
  replace (2 * 1) with 2 in H by lra.
  exact H.
Qed.

(* Norm-equivalence sandwich: (l^1)/2 <= hex <= l^inf <= l^1.  This is
   Lemma 2's "essentially a norm" made quantitative for the test family:
   swapping the gauge changes any generalized PD by at most a factor 2. *)
Lemma gauge_sandwich : forall x y,
    gauge_one x y / 2 <= gauge_hex x y /\
    gauge_hex x y <= gauge_inf x y /\
    gauge_inf x y <= gauge_one x y.
Proof.
  intros x y. unfold gauge_hex, gauge_inf, gauge_one.
  pose proof (Rabs_pos x). pose proof (Rabs_pos y).
  repeat split.
  - apply Rmax_l.
  - apply Rmax_lub.
    + pose proof (Rmax_l (Rabs x) (Rabs y)).
      pose proof (Rmax_r (Rabs x) (Rabs y)).
      lra.
    + apply Rmax_r.
  - apply Rmax_lub; lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Rational shape pins.  The hexagon of eq (18a) has vertices             *)
(*     (+-2, 0), (+-1, +-1); all pins are exact rational evaluations.         *)
(* -------------------------------------------------------------------------- *)

(* East vertex (2,0): gauge exactly 1 (on the unit hexagon boundary). *)
Lemma gauge_hex_vertex_east : gauge_hex 2 0 = 1.
Proof. gauge_crunch. Qed.

(* North-east corner (1,1): both defining constraints active at once. *)
Lemma gauge_hex_vertex_corner : gauge_hex 1 1 = 1.
Proof. gauge_crunch. Qed.

(* North edge point (0,1): the |y| <= 1 face is the active constraint. *)
Lemma gauge_hex_edge_north : gauge_hex 0 1 = 1.
Proof. gauge_crunch. Qed.

(* Interior probe (1, 1/2): strictly inside the unit hexagon (3/4 < 1). *)
Lemma gauge_hex_interior_probe : gauge_hex 1 (1 / 2) = 3 / 4.
Proof. gauge_crunch. Qed.

(* MISMATCH PROBE 1: at the east vertex the Chebyshev gauge says 2, the
   hexagon gauge says 1 -- kills the "hexagon = l^inf" misreading. *)
Lemma gauge_hex_below_linf_at_east : gauge_hex 2 0 < gauge_inf 2 0.
Proof. gauge_crunch. Qed.

(* MISMATCH PROBE 2: at the corner the Manhattan gauge says 2, the hexagon
   gauge says 1 -- kills the "hexagon = l^1" misreading. *)
Lemma gauge_hex_below_l1_at_corner : gauge_hex 1 1 < gauge_one 1 1.
Proof. gauge_crunch. Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions gauge_hex_sublevel.
Print Assumptions gauge_hex_subadditive.
Print Assumptions gauge_sandwich.

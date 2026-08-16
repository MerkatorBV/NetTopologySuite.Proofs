(* ============================================================================
   NetTopologySuite.Proofs.LECCandidateVertex
   ----------------------------------------------------------------------------
   CANDIDATE COMPLETENESS, witness-scoped (the ledger's summit rung, in the
   corpus's witness-first style): for the LEC of three point obstacles over
   their convex hull, the finite candidate enumeration
       { weighted-Voronoi vertices }  ∪  { bisector × boundary crossings }
       ∪  { domain vertices }
   contains EVERY maximiser — and the enumeration's best value IS the LEC.

   The witness instance: sites A(0,0), B(4,0), C(2,3) — an acute isoceles
   triangle with RATIONAL circumcentre K = (2, 5/6) and circumradius
   R = 13/6 — domain the closed triangle itself.  Headline
   (`lec_three_points`): the largest empty disk is centred at K with
   radius 13/6, and the maximiser is UNIQUE
   (`lec_three_points_maximiser_unique`), hence lies in the candidate
   list (`maximiser_is_candidate`) — candidate completeness for this
   instance, Qed.

   The proof engine is per-Voronoi-cell Handelman certificates, found by
   hand so every step is a deterministic `replace … by ring` plus sign
   bookkeeping (no solver search).  E.g. on A's cell (x ≤ 2, 4x+6y ≤ 13):

     169/36 − x² − y²  =  13/9·(2−x) + 5/36·(13−4x−6y)
                         + 1/3·(2−x)(3x−2y) + 1/6·(13−4x−6y)·y

   — every summand nonnegative on the cell, so d_A² ≤ R²; and equality
   forces the two tight factors to vanish, pinning P = K.  The bound and
   the uniqueness fall out of the SAME identity.  Cells B and C mirror.

   The obstacle is priced through the typed table: the region is
   `typed_list_region [TPoint A; TPoint B; TPoint C]` and emptiness is one
   comparison against the min-fold (`empty_disk_flatten_iff`) — the summit
   consumes the flatten row it stands on.

   Failed path F7 (ledger): "H-INTERIOR — the maximiser lies strictly
   inside the domain, so boundary candidates can be skipped."  REFUTED
   (`interior_maximiser_hypothesis_refuted`) by the OTHER corpus witness:
   both maximisers of the two-disc cell (`lec_two_discs_maximisers`) sit
   ON the rectangle's boundary (y = ±3).  Together the two instances show
   both candidate classes are load-bearing: this module's maximiser is an
   interior tie-vertex, the two-disc maximisers are bisector × boundary
   crossings — an enumeration may drop neither.

   The GENERAL candidate-completeness theorem (arbitrary sites/domains)
   remains the lane's open summit; this rung fixes its statement shape and
   retires the witness obligation.

   Pure math on R.  Classical-reals trio only (see Print Assumptions).

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   ========================================================================== *)

From Stdlib Require Import Reals Lra List.
Import ListNotations.
From NTS.Proofs Require Import Distance MaximumInscribedCircle
  LargestEmptyCircle LECObstacleDistance LECFlattenRow.

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  The witness instance.                                                   *)
(* -------------------------------------------------------------------------- *)

Definition sA : Point := mkPoint 0 0.
Definition sB : Point := mkPoint 4 0.
Definition sC : Point := mkPoint 2 3.

(** The interior weighted-Voronoi (here: plain Voronoi) vertex — the
    circumcentre, equidistant from all three sites at R = 13/6. *)
Definition kvertex : Point := mkPoint 2 (5/6).

(** The domain: the sites' closed convex hull, as three half-planes. *)
Definition in_tri : Region :=
  fun P => 0 <= py P /\ 0 <= 3 * px P - 2 * py P /\ 3 * px P + 2 * py P <= 12.

Definition tri_sites : list typed_obstacle := [TPoint sB; TPoint sC].
Definition tri_region : Region := typed_list_region (TPoint sA :: tri_sites).

(* -------------------------------------------------------------------------- *)
(* §2  Per-cell Handelman certificates (bound AND uniqueness from one          *)
(*     identity each).                                                         *)
(* -------------------------------------------------------------------------- *)

Lemma cell_A_cert : forall x y : R,
  0 <= y -> 0 <= 3*x - 2*y ->
  x <= 2 -> 4*x + 6*y <= 13 ->
  x*x + y*y <= 169/36 /\
  (169/36 <= x*x + y*y -> x = 2 /\ y = 5/6).
Proof.
  intros x y Hy He1 Hb1 Hb2.
  assert (Hid : 169 - 36*(x*x + y*y)
                = 52*(2-x) + 5*(13-4*x-6*y)
                  + 12*((2-x)*(3*x-2*y)) + 6*((13-4*x-6*y)*y)) by ring.
  assert (T3 : 0 <= (2-x)*(3*x-2*y)) by (apply Rmult_le_pos; lra).
  assert (T4 : 0 <= (13-4*x-6*y)*y) by (apply Rmult_le_pos; lra).
  split; [lra |].
  intro Hge.
  assert (Hz1 : 2 - x = 0) by lra.
  assert (Hz2 : 13 - 4*x - 6*y = 0) by lra.
  lra.
Qed.

Lemma cell_B_cert : forall x y : R,
  0 <= y -> 3*x + 2*y <= 12 ->
  2 <= x -> 3 <= 4*x - 6*y ->
  (x-4)*(x-4) + y*y <= 169/36 /\
  (169/36 <= (x-4)*(x-4) + y*y -> x = 2 /\ y = 5/6).
Proof.
  intros x y Hy He2 Hb1 Hb2.
  assert (Hid : 169 - 36*((x-4)*(x-4) + y*y)
                = 52*(x-2) + 5*(4*x-6*y-3)
                  + 12*((x-2)*(12-3*x-2*y)) + 6*((4*x-6*y-3)*y)) by ring.
  assert (T3 : 0 <= (x-2)*(12-3*x-2*y)) by (apply Rmult_le_pos; lra).
  assert (T4 : 0 <= (4*x-6*y-3)*y) by (apply Rmult_le_pos; lra).
  split; [lra |].
  intro Hge.
  assert (Hz1 : x - 2 = 0) by lra.
  assert (Hz2 : 4*x - 6*y - 3 = 0) by lra.
  lra.
Qed.

Lemma cell_C_cert : forall x y : R,
  0 <= 3*x - 2*y -> 3*x + 2*y <= 12 ->
  13 <= 4*x + 6*y -> 4*x - 6*y <= 3 ->
  (x-2)*(x-2) + (y-3)*(y-3) <= 169/36 /\
  (169/36 <= (x-2)*(x-2) + (y-3)*(y-3) -> x = 2 /\ y = 5/6).
Proof.
  intros x y He1 He2 Hb1 Hb2.
  assert (Hid : 338 - 72*((x-2)*(x-2) + (y-3)*(y-3))
                = 13*(4*x+6*y-13) + 13*(3-4*x+6*y)
                  + 3*((4*x+6*y-13)*(12-3*x-2*y))
                  + 3*((3-4*x+6*y)*(3*x-2*y))) by ring.
  assert (T3 : 0 <= (4*x+6*y-13)*(12-3*x-2*y)) by (apply Rmult_le_pos; lra).
  assert (T4 : 0 <= (3-4*x+6*y)*(3*x-2*y)) by (apply Rmult_le_pos; lra).
  split; [lra |].
  intro Hge.
  assert (Hz1 : 4*x + 6*y - 13 = 0) by lra.
  assert (Hz2 : 3 - 4*x + 6*y = 0) by lra.
  lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Cell trichotomy: the bound and the unique maximiser, at dist_sq level.  *)
(* -------------------------------------------------------------------------- *)

Lemma dist_sq_sA : forall x y, dist_sq (mkPoint x y) sA = x*x + y*y.
Proof. intros. unfold dist_sq, sA. cbn. ring. Qed.

Lemma dist_sq_sB : forall x y, dist_sq (mkPoint x y) sB = (x-4)*(x-4) + y*y.
Proof. intros. unfold dist_sq, sB. cbn. ring. Qed.

Lemma dist_sq_sC : forall x y,
  dist_sq (mkPoint x y) sC = (x-2)*(x-2) + (y-3)*(y-3).
Proof. intros. unfold dist_sq, sC. cbn. ring. Qed.

(** Somewhere in the triangle, one site is within the circumradius. *)
Lemma tri_cell_bound : forall P : Point, in_tri P ->
  dist_sq P sA <= 169/36 \/ dist_sq P sB <= 169/36 \/ dist_sq P sC <= 169/36.
Proof.
  intros [x y] [Hy [He1 He2]]. cbn [px py] in *.
  rewrite dist_sq_sA, dist_sq_sB, dist_sq_sC.
  destruct (Rle_dec x 2) as [Hx | Hx].
  - destruct (Rle_dec (4*x + 6*y) 13) as [Hb | Hb].
    + left. apply (proj1 (cell_A_cert x y Hy He1 Hx Hb)).
    + right; right. apply cell_C_cert; lra.
  - destruct (Rle_dec (4*x - 6*y) 3) as [Hb | Hb].
    + right; right. apply cell_C_cert; lra.
    + right; left. apply cell_B_cert; lra.
Qed.

(** A point of the triangle at least R from EVERY site is the vertex. *)
Lemma tri_max_unique : forall P : Point, in_tri P ->
  169/36 <= dist_sq P sA -> 169/36 <= dist_sq P sB -> 169/36 <= dist_sq P sC ->
  P = kvertex.
Proof.
  intros [x y] [Hy [He1 He2]] HA HB HC. cbn [px py] in *.
  rewrite dist_sq_sA in HA. rewrite dist_sq_sB in HB.
  rewrite dist_sq_sC in HC.
  assert (Hxy : x = 2 /\ y = 5/6).
  { destruct (Rle_dec x 2) as [Hx | Hx].
    - destruct (Rle_dec (4*x + 6*y) 13) as [Hb | Hb].
      + apply (proj2 (cell_A_cert x y Hy He1 Hx Hb)). exact HA.
      + apply (proj2 (cell_C_cert x y He1 He2 ltac:(lra) ltac:(lra))).
        exact HC.
    - destruct (Rle_dec (4*x - 6*y) 3) as [Hb | Hb].
      + apply (proj2 (cell_C_cert x y He1 He2 ltac:(lra) ltac:(lra))).
        exact HC.
      + apply (proj2 (cell_B_cert x y Hy He2 ltac:(lra) ltac:(lra))).
        exact HB. }
  destruct Hxy as [-> ->]. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  The metric level: distances at the vertex, and the fold bound.          *)
(* -------------------------------------------------------------------------- *)

Lemma dist_kvertex_sA : dist kvertex sA = 13/6.
Proof.
  apply dist_eq_of_dist_sq; [lra |].
  unfold dist_sq, kvertex, sA. cbn. lra.
Qed.

Lemma dist_kvertex_sB : dist kvertex sB = 13/6.
Proof.
  apply dist_eq_of_dist_sq; [lra |].
  unfold dist_sq, kvertex, sB. cbn. lra.
Qed.

Lemma dist_kvertex_sC : dist kvertex sC = 13/6.
Proof.
  apply dist_eq_of_dist_sq; [lra |].
  unfold dist_sq, kvertex, sC. cbn. lra.
Qed.

Lemma kvertex_in_tri : in_tri kvertex.
Proof. unfold in_tri, kvertex. cbn. lra. Qed.

(** The typed min-fold of the instance, spelled out. *)
Lemma tri_fold_eval : forall P : Point,
  typed_list_dist (TPoint sA) tri_sites P
  = Rmin (dist P sB) (Rmin (dist P sC) (dist P sA)).
Proof. reflexivity. Qed.

Lemma tri_min_bound : forall P : Point, in_tri P ->
  typed_list_dist (TPoint sA) tri_sites P <= 13/6.
Proof.
  intros P HP. rewrite tri_fold_eval.
  assert (H136 : (0:R) <= 13/6) by lra.
  destruct (tri_cell_bound P HP) as [HA | [HB | HC]].
  - eapply Rle_trans; [apply Rmin_r |].
    eapply Rle_trans; [apply Rmin_r |].
    apply (proj2 (dist_le_iff_dist_sq_le P sA (13/6) H136)).
    replace (13/6 * (13/6)) with (169/36) by lra. exact HA.
  - eapply Rle_trans; [apply Rmin_l |].
    apply (proj2 (dist_le_iff_dist_sq_le P sB (13/6) H136)).
    replace (13/6 * (13/6)) with (169/36) by lra. exact HB.
  - eapply Rle_trans; [apply Rmin_r |].
    eapply Rle_trans; [apply Rmin_l |].
    apply (proj2 (dist_le_iff_dist_sq_le P sC (13/6) H136)).
    replace (13/6 * (13/6)) with (169/36) by lra. exact HC.
Qed.

(** Emptiness of the instance region is one comparison against the fold —
    the flatten row doing the pricing. *)
Lemma tri_region_iff : forall (P : Point) (rho : R),
  empty_disk tri_region P rho
  <-> (0 <= rho /\ rho <= typed_list_dist (TPoint sA) tri_sites P).
Proof.
  intros P rho.
  apply (empty_disk_flatten_iff (TPoint sA) tri_sites P rho I).
  repeat constructor.
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  The LEC headline and the unique maximiser.                              *)
(* -------------------------------------------------------------------------- *)

Theorem lec_three_points :
  largest_empty_disk tri_region in_tri kvertex (13/6).
Proof.
  split; [exact kvertex_in_tri | split].
  - apply (proj2 (tri_region_iff kvertex (13/6))). split; [lra |].
    rewrite tri_fold_eval.
    rewrite dist_kvertex_sA, dist_kvertex_sB, dist_kvertex_sC.
    rewrite (Rmin_left (13/6) (13/6)) by lra.
    rewrite (Rmin_left (13/6) (13/6)) by lra. lra.
  - intros O' r' Hdom Hemp.
    apply (proj1 (tri_region_iff O' r')) in Hemp.
    destruct Hemp as [_ Hle].
    pose proof (tri_min_bound O' Hdom). lra.
Qed.

Theorem lec_three_points_maximiser_unique : forall P : Point,
  in_tri P -> empty_disk tri_region P (13/6) -> P = kvertex.
Proof.
  intros P HP Hemp.
  apply (proj1 (tri_region_iff P (13/6))) in Hemp.
  destruct Hemp as [_ Hle]. rewrite tri_fold_eval in Hle.
  assert (H136 : (0:R) <= 13/6) by lra.
  assert (HB : 13/6 <= dist P sB)
    by (eapply Rle_trans; [exact Hle | apply Rmin_l]).
  assert (HC : 13/6 <= dist P sC).
  { eapply Rle_trans; [exact Hle |].
    eapply Rle_trans; [apply Rmin_r | apply Rmin_l]. }
  assert (HA : 13/6 <= dist P sA).
  { eapply Rle_trans; [exact Hle |].
    eapply Rle_trans; [apply Rmin_r | apply Rmin_r]. }
  apply tri_max_unique; try exact HP.
  - pose proof (dist_mul_self P sA) as Hm.
    pose proof (Rmult_le_compat (13/6) (dist P sA) (13/6) (dist P sA)
                  H136 H136 HA HA) as Hc.
    lra.
  - pose proof (dist_mul_self P sB) as Hm.
    pose proof (Rmult_le_compat (13/6) (dist P sB) (13/6) (dist P sB)
                  H136 H136 HB HB) as Hc.
    lra.
  - pose proof (dist_mul_self P sC) as Hm.
    pose proof (Rmult_le_compat (13/6) (dist P sC) (13/6) (dist P sC)
                  H136 H136 HC HC) as Hc.
    lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §6  The candidate enumeration and completeness, witness-scoped.             *)
(* -------------------------------------------------------------------------- *)

(** The finite enumeration an O(n log n) LEC walks: the interior Voronoi
    vertex, the bisector × boundary crossings, the domain vertices. *)
Definition tri_candidates : list Point :=
  [ kvertex;                    (* Voronoi vertex, equidistant tie of 3   *)
    mkPoint 2 0;                (* bisector(A,B) × base edge              *)
    mkPoint 1 (3/2);            (* bisector(A,C) × edge AC                *)
    mkPoint 3 (3/2);            (* bisector(B,C) × edge BC                *)
    sA; sB; sC ].               (* domain vertices                        *)

Lemma candidates_in_tri : Forall in_tri tri_candidates.
Proof.
  unfold tri_candidates.
  repeat apply Forall_cons; try apply Forall_nil;
    unfold in_tri, kvertex, sA, sB, sC; cbn; lra.
Qed.

(** Every candidate's clearance is at most the vertex's. *)
Lemma candidates_bounded :
  Forall (fun Q => typed_list_dist (TPoint sA) tri_sites Q <= 13/6)
         tri_candidates.
Proof.
  pose proof candidates_in_tri as H.
  induction H as [| Q l HQ Hl IH]; constructor;
    [apply tri_min_bound; exact HQ | exact IH].
Qed.

(** CANDIDATE COMPLETENESS, witness-scoped: every maximiser of the
    instance lies in the finite enumeration. *)
Theorem maximiser_is_candidate : forall P : Point,
  in_tri P -> empty_disk tri_region P (13/6) -> In P tri_candidates.
Proof.
  intros P HP Hemp.
  rewrite (lec_three_points_maximiser_unique P HP Hemp).
  left. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* §7  Ledger F7 — interior candidates suffice (REFUTED).                      *)
(*                                                                            *)
(* H-INTERIOR: the maximiser lies strictly inside the domain, so the          *)
(* enumeration may skip boundary candidates.  The two-disc corpus witness     *)
(* kills it: BOTH its maximisers sit on the rectangle's boundary.             *)
(* -------------------------------------------------------------------------- *)

Definition strictly_interior_rect (P : Point) : Prop :=
  -4 < px P < 4 /\ -3 < py P < 3.

Theorem interior_maximiser_hypothesis_refuted :
  ~ (exists P : Point,
       rect_dom P /\ empty_disk two_discs P 2 /\ strictly_interior_rect P).
Proof.
  intros [P [Hdom [Hemp Hint]]].
  destruct (lec_two_discs_maximisers P Hdom Hemp) as [-> | ->];
    unfold strictly_interior_rect in Hint; cbn in Hint; lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §8  Audit footprint (classical-reals trio only).                            *)
(* -------------------------------------------------------------------------- *)

Print Assumptions tri_cell_bound.
Print Assumptions tri_max_unique.
Print Assumptions lec_three_points.
Print Assumptions lec_three_points_maximiser_unique.
Print Assumptions maximiser_is_candidate.
Print Assumptions interior_maximiser_hypothesis_refuted.

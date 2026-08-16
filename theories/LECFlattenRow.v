(* ============================================================================
   NetTopologySuite.Proofs.LECFlattenRow
   ----------------------------------------------------------------------------
   The n-ary FLATTEN row of the typed LEC obstacle-distance table (the
   ledger's open rung "CompoundCurve / n-ary flatten" — closed).

   The engine's `ObstacleDistance` prices a collection obstacle by folding
   min over its members (`getNumMembers`/`getMemberN`).  #467 proved the
   BINARY case (`empty_disk_union_iff`); this module gives the fold its
   corpus twin, in three layers:

     1. `empty_disk_list_iff` — the generic n-ary union: a candidate disk
        is empty of a finite union iff it is empty of every member
        (induction over `runion_list`, no metric content).
     2. `exact_clearance` algebra — "v is THE clearance of region Rg from
        O" (lower bound on every member point + attained).  One generic
        row lemma (`empty_disk_iff_exact`) turns any exact clearance into
        the emptiness threshold; `exact_clearance_union` shows exactness
        is closed under union with value Rmin; `exact_clearance_fold`
        folds it over a NONEMPTY member list.
     3. The typed table (`typed_obstacle`: point / filled disc /
        full-circle ring / circular arc / line segment) — each row's
        closed form is an exact clearance (`typed_row_exact`, reusing
        LECObstacleDistance's disc/ring rows, LECArcRow's arc row, and
        LECSegmentRow's clamped-projection facet row), so the min-fold of
        typed rows is EXACTLY the collection's emptiness threshold
        (`empty_disk_flatten_iff`).  This is the engine's whole
        `ObstacleDistance` per-component table plus flatten, as one Qed
        statement over a nonempty typed member list.

   Failed path F5 (ledger): "seed the empty fold with unit 0" — the
   tempting `fold Rmin 0 []`-style base case.  REFUTED: against an empty
   obstacle list EVERY radius is empty, so the iff with threshold 0 fails
   at rho = 1 (`empty_fold_zero_unit_hypothesis_refuted`) — and no finite
   unit can repair it (`empty_fold_no_finite_unit`: rho = max(0,v) + 1
   breaks any candidate v).  Rmin has no unit in R; the mathematically
   forced behaviour for an empty member list is a verdict, not a value —
   exactly the oracle's k = 0 → DEGENERATE gate (OBSTACLE_DISTANCE).

   Pure math on R.  Classical-reals trio only (see Print Assumptions).

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   ========================================================================== *)

From Stdlib Require Import Reals Lra List.
Import ListNotations.
From NTS.Proofs Require Import Distance CurveGeometry MaximumInscribedCircle
  LargestEmptyCircle LECObstacleDistance CurveRingSimple ArcPointDistance
  LECArcRow LECSegmentRow.

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  The n-ary union of obstacle regions.                                    *)
(* -------------------------------------------------------------------------- *)

Definition rnone : Region := fun _ => False.

Fixpoint runion_list (rs : list Region) : Region :=
  match rs with
  | [] => rnone
  | Rg :: tl => runion Rg (runion_list tl)
  end.

Lemma empty_disk_rnone : forall (O : Point) (rho : R),
  empty_disk rnone O rho <-> 0 <= rho.
Proof.
  intros O rho. unfold empty_disk, rnone. split.
  - intros [Hr _]. exact Hr.
  - intros Hr. split; [exact Hr | intros P []].
Qed.

(** The generic n-ary flatten: emptiness against a finite union is
    emptiness against every member.  Folds #467's binary
    `empty_disk_union_iff` down the list. *)
Lemma empty_disk_list_iff : forall (rs : list Region) (O : Point) (rho : R),
  empty_disk (runion_list rs) O rho
  <-> (0 <= rho /\ Forall (fun Rg => empty_disk Rg O rho) rs).
Proof.
  intros rs O rho. induction rs as [| Rg tl IH]; cbn [runion_list].
  - rewrite empty_disk_rnone. split.
    + intro Hr. split; [exact Hr | constructor].
    + intros [Hr _]. exact Hr.
  - rewrite empty_disk_union_iff, IH. split.
    + intros [HA [Hr Htl]]. split; [exact Hr | constructor; assumption].
    + intros [Hr Hall]. inversion Hall; subst. split; [assumption | split; assumption].
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  Exact-clearance algebra: the shape every typed row shares.              *)
(* -------------------------------------------------------------------------- *)

(** [v] is THE clearance of region [Rg] seen from [O]: a lower bound on the
    distance to every member point, and attained by one.  Each row of the
    typed table proves exactly this pair; everything downstream is generic. *)
Definition exact_clearance (Rg : Region) (O : Point) (v : R) : Prop :=
  (forall Q, Rg Q -> v <= dist O Q) /\ (exists Q, Rg Q /\ dist O Q = v).

Lemma exact_clearance_nonneg :
  forall Rg O v, exact_clearance Rg O v -> 0 <= v.
Proof.
  intros Rg O v [_ [Q [_ HQ]]]. rewrite <- HQ. apply dist_nonneg.
Qed.

(** The generic row lemma: an exact clearance is the emptiness threshold.
    (This is the shape `empty_disk_disc_iff` / `empty_disk_ring_iff` /
    `empty_disk_arc_iff` each proved by hand — now once, for any row.) *)
Lemma empty_disk_iff_exact :
  forall (Rg : Region) (O : Point) (v : R),
    exact_clearance Rg O v ->
    forall rho, empty_disk Rg O rho <-> (0 <= rho /\ rho <= v).
Proof.
  intros Rg O v [Hlow [Q [HQ Hatt]]] rho. unfold empty_disk. split.
  - intros [Hr He]. split; [exact Hr |]. rewrite <- Hatt. apply He. exact HQ.
  - intros [Hr Hle]. split; [exact Hr |]. intros P HP.
    eapply Rle_trans; [exact Hle | apply Hlow; exact HP].
Qed.

(** Exactness transports across pointwise-equivalent regions (used to
    shuffle unions below). *)
Lemma exact_clearance_ext :
  forall (A B : Region) (O : Point) (v : R),
    (forall Q, A Q <-> B Q) ->
    exact_clearance A O v -> exact_clearance B O v.
Proof.
  intros A B O v Hiff [Hlow [Q [HQ Hatt]]]. split.
  - intros Q' HQ'. apply Hlow, Hiff, HQ'.
  - exists Q. split; [apply Hiff, HQ | exact Hatt].
Qed.

(** Union of exact rows is exact with value Rmin — the binary flatten. *)
Lemma exact_clearance_union :
  forall (A B : Region) (O : Point) (u v : R),
    exact_clearance A O u -> exact_clearance B O v ->
    exact_clearance (runion A B) O (Rmin u v).
Proof.
  intros A B O u v [HlA [QA [HQA HaA]]] [HlB [QB [HQB HaB]]]. split.
  - intros Q [HQ | HQ].
    + eapply Rle_trans; [apply Rmin_l | apply HlA; exact HQ].
    + eapply Rle_trans; [apply Rmin_r | apply HlB; exact HQ].
  - destruct (Rle_dec u v) as [Hle | Hgt].
    + exists QA. split; [left; exact HQA |].
      rewrite HaA. symmetry. apply Rmin_left. exact Hle.
    + exists QB. split; [right; exact HQB |].
      rewrite HaB. symmetry. apply Rmin_right. lra.
Qed.

(** The n-ary flatten, metric level: fold Rmin over a NONEMPTY member list
    (head row seeds the fold — Rmin has no unit in R, see §4). *)
Lemma exact_clearance_fold :
  forall (O : Point) (rs : list Region) (vs : list R) (Rg : Region) (v : R),
    exact_clearance Rg O v ->
    Forall2 (fun Rg' v' => exact_clearance Rg' O v') rs vs ->
    exact_clearance (runion Rg (runion_list rs)) O (fold_right Rmin v vs).
Proof.
  intros O rs vs Rg v Hhd Hall. revert Rg v Hhd.
  induction Hall as [| Rg' v' rs' vs' Hhd' Htl IH]; intros Rg v Hhd;
    cbn [runion_list fold_right].
  - eapply exact_clearance_ext; [| exact Hhd].
    intros Q. unfold runion, rnone. tauto.
  - eapply exact_clearance_ext.
    2: { apply (exact_clearance_union _ _ _ _ _ Hhd' (IH Rg v Hhd)). }
    intros Q. unfold runion. tauto.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  The typed table: the engine's `ObstacleDistance` rows, flattened.       *)
(* -------------------------------------------------------------------------- *)

(** One typed member of a collection obstacle — the engine's per-component
    table: Point/MultiPoint, filled disc (CurvePolygon), full-circle ring
    (closed CircularString), circular arc (CircularString window), line
    segment (LineString facet). *)
Inductive typed_obstacle : Type :=
  | TPoint (q : Point)
  | TDisc  (c : Point) (r : R)
  | TRing  (c : Point) (r : R)
  | TArc   (a : CircularArc)
  | TSeg   (a b : Point).

Definition typed_region (t : typed_obstacle) : Region :=
  match t with
  | TPoint q  => fun P => P = q
  | TDisc c r => disc_obstacle c r
  | TRing c r => ring_obstacle c r
  | TArc a    => on_arc a
  | TSeg a b  => on_seg a b
  end.

(** The closed-form row values — euclid, max(0, d − r), abs(d − r),
    LECArcRow's total point-to-arc form, and LECSegmentRow's total
    clamped-projection facet form. *)
Definition typed_dist (t : typed_obstacle) (O : Point) : R :=
  match t with
  | TPoint q  => dist O q
  | TDisc c r => disc_dist c r O
  | TRing c r => ring_dist c r O
  | TArc a    => arc_dist a O
  | TSeg a b  => seg_dist a b O
  end.

(** The segment row is TOTAL (A = B collapses to the point row), so like
    the point row it needs no validity side condition. *)
Definition typed_valid (t : typed_obstacle) : Prop :=
  match t with
  | TPoint _  => True
  | TDisc _ r => 0 <= r
  | TRing _ r => 0 <= r
  | TArc a    => valid_arc a
  | TSeg _ _  => True
  end.

(** Every typed row is an exact clearance. *)
Lemma typed_row_exact :
  forall (t : typed_obstacle) (O : Point),
    typed_valid t -> exact_clearance (typed_region t) O (typed_dist t O).
Proof.
  intros t O Hv.
  destruct t as [q | c r | c r | a | a b];
    cbn [typed_region typed_dist typed_valid] in *.
  - split.
    + intros Q ->. lra.
    + exists q. split; reflexivity.
  - split.
    + intros Q HQ. exact (disc_dist_lower c r O Q Hv HQ).
    + destruct (disc_dist_attained c r O Hv) as [Q [HQ Ha]].
      exists Q. split; assumption.
  - split.
    + intros Q HQ. exact (ring_dist_lower c r O Q Hv HQ).
    + destruct (ring_dist_attained c r O Hv) as [Q [HQ Ha]].
      exists Q. split; assumption.
  - destruct (arc_dist_exact a O Hv) as [Hlow Hatt]. split.
    + intros Q HQ. exact (Hlow Q HQ).
    + destruct Hatt as [X [HX Ha]]. exists X. split; assumption.
  - split.
    + intros Q HQ. exact (seg_dist_lower a b O Q HQ).
    + destruct (seg_dist_attained a b O) as [Q [HQ Ha]].
      exists Q. split; assumption.
Qed.

(** The collection obstacle and its min-fold — the corpus twin of the
    engine's `getNumMembers`/`getMemberN` loop (head member seeds the fold,
    mirroring the oracle's k >= 1 gate). *)
Definition typed_list_region (ts : list typed_obstacle) : Region :=
  runion_list (map typed_region ts).

Definition typed_list_dist
    (t : typed_obstacle) (ts : list typed_obstacle) (O : Point) : R :=
  fold_right Rmin (typed_dist t O) (map (fun t' => typed_dist t' O) ts).

Theorem obstacle_list_flatten_exact :
  forall (t : typed_obstacle) (ts : list typed_obstacle) (O : Point),
    typed_valid t -> Forall typed_valid ts ->
    exact_clearance (typed_list_region (t :: ts)) O (typed_list_dist t ts O).
Proof.
  intros t ts O Hv Hall.
  unfold typed_list_region, typed_list_dist. cbn [map runion_list].
  apply exact_clearance_fold.
  - apply typed_row_exact. exact Hv.
  - induction Hall as [| t' tl Hv' Htl IH]; cbn [map].
    + constructor.
    + constructor; [apply typed_row_exact; exact Hv' | exact IH].
Qed.

(** HEADLINE — the flatten row: a candidate disk is empty of a nonempty
    typed collection iff its radius is at most the min-fold of the typed
    per-member closed forms.  The engine's whole `ObstacleDistance` table,
    one comparison. *)
Theorem empty_disk_flatten_iff :
  forall (t : typed_obstacle) (ts : list typed_obstacle) (O : Point) (rho : R),
    typed_valid t -> Forall typed_valid ts ->
    (empty_disk (typed_list_region (t :: ts)) O rho
     <-> 0 <= rho /\ rho <= typed_list_dist t ts O).
Proof.
  intros t ts O rho Hv Hall.
  exact (empty_disk_iff_exact _ _ _
           (obstacle_list_flatten_exact t ts O Hv Hall) rho).
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Ledger F5 — "seed the empty fold with unit 0" (REFUTED).                *)
(*                                                                            *)
(* Against an empty member list EVERY radius is empty, so no finite value    *)
(* can play the threshold: Rmin has no unit in R.  The forced behaviour for  *)
(* k = 0 is a verdict, not a value — the oracle's DEGENERATE gate.           *)
(* -------------------------------------------------------------------------- *)

Theorem empty_fold_zero_unit_hypothesis_refuted :
  ~ (forall (O : Point) (rho : R),
       empty_disk (runion_list []) O rho <-> (0 <= rho /\ rho <= 0)).
Proof.
  intro H.
  assert (He : empty_disk (runion_list []) (mkPoint 0 0) 1).
  { cbn [runion_list]. apply (proj2 (empty_disk_rnone (mkPoint 0 0) 1)). lra. }
  destruct (proj1 (H (mkPoint 0 0) 1) He) as [_ Habs]. lra.
Qed.

Theorem empty_fold_no_finite_unit :
  forall (O : Point),
    ~ (exists v : R,
         forall rho, empty_disk (runion_list []) O rho <-> (0 <= rho /\ rho <= v)).
Proof.
  intros O [v Hv].
  set (rho := Rmax 0 v + 1).
  assert (Hr : 0 <= rho) by (unfold rho; pose proof (Rmax_l 0 v); lra).
  assert (He : empty_disk (runion_list []) O rho).
  { cbn [runion_list]. apply (proj2 (empty_disk_rnone O rho)). exact Hr. }
  destruct (proj1 (Hv rho) He) as [_ Hle].
  unfold rho in Hle. pose proof (Rmax_r 0 v). lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  Audit footprint (classical-reals trio only).                            *)
(* -------------------------------------------------------------------------- *)

Print Assumptions empty_disk_list_iff.
Print Assumptions empty_disk_iff_exact.
Print Assumptions exact_clearance_fold.
Print Assumptions typed_row_exact.
Print Assumptions obstacle_list_flatten_exact.
Print Assumptions empty_disk_flatten_iff.
Print Assumptions empty_fold_zero_unit_hypothesis_refuted.
Print Assumptions empty_fold_no_finite_unit.

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

   Proven here (the base facts every obligation leans on), all Qed:
     - curve_length_ge_chord  : chord <= L     (the lower sandwich half)
     - curve_length_nonneg    : 0 <= L
     - curve_length_unique    : the spec pins L
     - curve_length_additive  : L(a,c) = L(a,b) + L(b,c)
     - is_curve_length_ext    : pointwise-equal curves carry the same lengths
     - is_curve_length_shift  : translated parameterizations too (t ↦ g (c+t))
       — both reparameterization invariances funext-free
     - curve_length_upper_of_chord_modulus (+ polyline_le_of_chord_modulus,
       chain_le) : a chord modulus F on [a,b] telescopes, so L <= F b − F a
       — the one upper-half telescoping every Lipschitz/primitive lane uses

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
(* Polyline and chain plumbing.                                               *)
(* -------------------------------------------------------------------------- *)

(* Splitting a polyline at a listed waypoint: an exact decomposition. *)
Lemma polyline_len_app_mid : forall (g : Curve) xs t u ys,
  polyline_len g t (xs ++ u :: ys)
  = polyline_len g t (xs ++ [u]) + polyline_len g u ys.
Proof.
  intros g xs; induction xs as [|v xs IH]; intros t u ys; simpl.
  - lra.
  - rewrite IH. lra.
Qed.

(* Rerouting the final vertex from v to w costs at most dist (g v) (g w):
   the triangle inequality lifted along the polyline. *)
Lemma polyline_len_last_triangle : forall (g : Curve) xs t v w,
  polyline_len g t (xs ++ [w])
  <= polyline_len g t (xs ++ [v]) + dist (g v) (g w).
Proof.
  intros g xs; induction xs as [|u xs IH]; intros t v w; simpl.
  - pose proof (dist_triangle (g t) (g v) (g w)). lra.
  - specialize (IH u v w). lra.
Qed.

(* Chains concatenate through a shared waypoint. *)
Lemma chain_app : forall xs lo mid ys hi,
  chain lo xs mid -> chain mid ys hi -> chain lo (xs ++ mid :: ys) hi.
Proof.
  induction xs as [|u xs IH]; simpl; intros lo mid ys hi H1 H2.
  - split; assumption.
  - destruct H1 as [Hlu H1]. split; [exact Hlu | apply IH; assumption].
Qed.

(* A chain's endpoints are ordered. *)
Lemma chain_le : forall xs lo hi, chain lo xs hi -> lo <= hi.
Proof.
  induction xs as [|u xs IH]; simpl; intros lo hi Hch.
  - exact Hch.
  - destruct Hch as [Hlu Hch]. specialize (IH u hi Hch). lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* The generic upper-half telescoping: a chord MODULUS F — every chord        *)
(* within [a, b] bounded by its F-increment — telescopes over any inscribed   *)
(* polyline, so every metric-length value is at most F b − F a.  Instances:  *)
(* F = K·x for the Lipschitz lanes (circle, ellipse, Bézier control net),    *)
(* F = the elliptic-E primitive for the conditional ellipse tier.            *)
(* -------------------------------------------------------------------------- *)

Lemma polyline_le_of_chord_modulus :
  forall (g : Curve) (F : R -> R) (a b : R) ts t,
  (forall s u, a <= s -> s <= u -> u <= b -> dist (g s) (g u) <= F u - F s) ->
  a <= t -> chain t ts b ->
  polyline_len g t (ts ++ [b]) <= F b - F t.
Proof.
  intros g F a b ts; induction ts as [|u tl IH]; simpl;
    intros t Hmod Hat Hch.
  - pose proof (Hmod t b Hat Hch (Rle_refl b)). lra.
  - destruct Hch as [Htu Hch].
    pose proof (chain_le tl u b Hch) as Hub.
    pose proof (Hmod t u Hat Htu Hub) as Hc.
    assert (Hau : a <= u) by lra.
    specialize (IH u Hmod Hau Hch). lra.
Qed.

Theorem curve_length_upper_of_chord_modulus :
  forall (g : Curve) (F : R -> R) a b L,
  (forall s t, a <= s -> s <= t -> t <= b -> dist (g s) (g t) <= F t - F s) ->
  is_curve_length g a b L ->
  L <= F b - F a.
Proof.
  intros g F a b L Hmod [_ Hlst].
  apply Hlst. intros l (ts & Hch & Hl). subst l.
  apply (polyline_le_of_chord_modulus g F a b ts a Hmod (Rle_refl a) Hch).
Qed.

(* A chain over [lo, hi] splits at any waypoint m of [lo, hi]. *)
Lemma chain_split : forall xs lo m hi,
  lo <= m -> m <= hi -> chain lo xs hi ->
  exists ys zs, xs = ys ++ zs /\ chain lo ys m /\ chain m zs hi.
Proof.
  induction xs as [|u xs IH]; simpl; intros lo m hi Hlom Hmhi Hch.
  - exists [], []. simpl. repeat split; auto.
  - destruct Hch as [Hlu Hch].
    destruct (Rle_dec u m) as [Hum | Hum].
    + destruct (IH u m hi Hum Hmhi Hch) as (ys & zs & Heq & Hy & Hz).
      exists (u :: ys), zs. subst xs. simpl. repeat split; assumption.
    + exists [], (u :: xs). simpl.
      repeat split; try assumption; try reflexivity; lra.
Qed.

(* The two halves of a split partition over-estimate the whole: only the
   seam edge changes, and it changes by a triangle inequality. *)
Lemma polyline_split_le : forall (g : Curve) ys zs a m c,
  polyline_len g a (ys ++ zs ++ [c])
  <= polyline_len g a (ys ++ [m]) + polyline_len g m (zs ++ [c]).
Proof.
  intros g ys zs a m c.
  destruct zs as [|w zs]; simpl.
  - pose proof (polyline_len_last_triangle g ys a m c). lra.
  - rewrite polyline_len_app_mid.
    pose proof (polyline_len_last_triangle g ys a m w). lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Base facts.                                                                *)
(* -------------------------------------------------------------------------- *)

(* The single chord is an inscribed polyline (the empty refinement). *)
Lemma inscribed_chord : forall (g : Curve) a b,
  a <= b -> inscribed_len g a b (dist (g a) (g b)).
Proof.
  intros g a b Hab. exists []. split.
  - exact Hab.
  - simpl. lra.
Qed.

(* Lower sandwich half: no curve is shorter than its chord. *)
Theorem curve_length_ge_chord : forall (g : Curve) a b L,
  a <= b -> is_curve_length g a b L -> dist (g a) (g b) <= L.
Proof.
  intros g a b L Hab [Hub _].
  exact (Hub _ (inscribed_chord g a b Hab)).
Qed.

Theorem curve_length_nonneg : forall (g : Curve) a b L,
  a <= b -> is_curve_length g a b L -> 0 <= L.
Proof.
  intros g a b L Hab HL.
  apply Rle_trans with (dist (g a) (g b)).
  - apply dist_nonneg.
  - exact (curve_length_ge_chord g a b L Hab HL).
Qed.

(* The spec pins its value: lub uniqueness. *)
Theorem curve_length_unique : forall (g : Curve) a b L1 L2,
  is_curve_length g a b L1 -> is_curve_length g a b L2 -> L1 = L2.
Proof.
  intros g a b L1 L2 [Hub1 Hlst1] [Hub2 Hlst2].
  apply Rle_antisym; [apply Hlst1, Hub2 | apply Hlst2, Hub1].
Qed.

(* -------------------------------------------------------------------------- *)
(* Aggregation: length is additive at any waypoint.                           *)
(* -------------------------------------------------------------------------- *)

Theorem curve_length_additive : forall (g : Curve) a b c L1 L2,
  a <= b -> b <= c ->
  is_curve_length g a b L1 -> is_curve_length g b c L2 ->
  is_curve_length g a c (L1 + L2).
Proof.
  intros g a b c L1 L2 Hab Hbc [Hub1 Hlst1] [Hub2 Hlst2].
  split.
  - (* L1 + L2 bounds every inscribed polyline of [a, c]: split its chain
       at b, pay one triangle inequality at the seam. *)
    intros l (ts & Hch & Hl). subst l.
    destruct (chain_split ts a b c Hab Hbc Hch) as (ys & zs & Heq & Hy & Hz).
    subst ts. rewrite <- app_assoc.
    eapply Rle_trans; [apply polyline_split_le with (m := b) |].
    apply Rplus_le_compat.
    + apply Hub1. exists ys. split; [exact Hy | reflexivity].
    + apply Hub2. exists zs. split; [exact Hz | reflexivity].
  - (* Least: any bound M of [a, c] bounds every concatenated pair, and the
       two lub minimalities peel off L1 then L2 — no epsilon needed. *)
    intros M HM.
    assert (Hstep : forall l2, inscribed_len g b c l2 -> L1 <= M - l2).
    { intros l2 (ts2 & Hc2 & Hl2). subst l2.
      apply Hlst1. intros l1 (ts1 & Hc1 & Hl1). subst l1.
      assert (Hin : inscribed_len g a c
        (polyline_len g a (ts1 ++ [b]) + polyline_len g b (ts2 ++ [c]))).
      { exists (ts1 ++ b :: ts2). split.
        - apply chain_app; assumption.
        - rewrite <- app_assoc. simpl. symmetry.
          apply polyline_len_app_mid. }
      specialize (HM _ Hin). lra. }
    assert (HL2 : L2 <= M - L1).
    { apply Hlst2. intros l2 Hl2m. specialize (Hstep _ Hl2m). lra. }
    lra.
Qed.

Print Assumptions curve_length_additive.

(* -------------------------------------------------------------------------- *)
(* Reparameterization invariances (#508 ellipse rung 2 consumers): the spec   *)
(* only sees curves through dist, so pointwise-equal curves and translated    *)
(* parameterizations carry the same lengths.  Both proven without funext.     *)
(* -------------------------------------------------------------------------- *)

Lemma polyline_len_ext : forall (g1 g2 : Curve),
  (forall t, g1 t = g2 t) ->
  forall ts t, polyline_len g1 t ts = polyline_len g2 t ts.
Proof.
  intros g1 g2 Hg ts; induction ts as [|u tl IH]; intro t; simpl.
  - reflexivity.
  - rewrite !Hg, IH. reflexivity.
Qed.

Lemma is_curve_length_ext : forall (g1 g2 : Curve) a b L,
  (forall t, g1 t = g2 t) ->
  is_curve_length g1 a b L -> is_curve_length g2 a b L.
Proof.
  intros g1 g2 a b L Hg [Hub Hlst].
  assert (H21 : forall l, inscribed_len g2 a b l -> inscribed_len g1 a b l).
  { intros l (ts & Hch & Hl). exists ts. split; [exact Hch |].
    rewrite (polyline_len_ext g1 g2 Hg). exact Hl. }
  assert (H12 : forall l, inscribed_len g1 a b l -> inscribed_len g2 a b l).
  { intros l (ts & Hch & Hl). exists ts. split; [exact Hch |].
    rewrite <- (polyline_len_ext g1 g2 Hg). exact Hl. }
  split.
  - intros l Hl. exact (Hub _ (H21 _ Hl)).
  - intros M HM. apply Hlst. intros l Hl. exact (HM _ (H12 _ Hl)).
Qed.

Lemma chain_shift : forall c ts lo hi,
  chain lo ts hi -> chain (c + lo) (map (Rplus c) ts) (c + hi).
Proof.
  intros c ts; induction ts as [|u tl IH]; simpl; intros lo hi Hch.
  - lra.
  - destruct Hch as [Hlu Hch]. split; [lra | exact (IH u hi Hch)].
Qed.

Lemma map_shift_cancel : forall c ts,
  map (Rplus c) (map (Rplus (- c)) ts) = ts.
Proof.
  intros c ts; induction ts as [|u tl IH]; simpl.
  - reflexivity.
  - rewrite IH. f_equal. ring.
Qed.

Lemma polyline_len_shift : forall (g : Curve) c ts t,
  polyline_len (fun u => g (c + u)) t ts
  = polyline_len g (c + t) (map (Rplus c) ts).
Proof.
  intros g c ts; induction ts as [|u tl IH]; intro t; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma is_curve_length_shift : forall (g : Curve) c a b L,
  is_curve_length g (c + a) (c + b) L ->
  is_curve_length (fun t => g (c + t)) a b L.
Proof.
  intros g c a b L [Hub Hlst].
  split.
  - intros l (ts & Hch & Hl). subst l.
    apply Hub. exists (map (Rplus c) ts). split.
    + exact (chain_shift c ts a b Hch).
    + rewrite polyline_len_shift, map_app. reflexivity.
  - intros M HM. apply Hlst. intros l (ts & Hch & Hl). subst l.
    apply HM.
    exists (map (Rplus (- c)) ts). split.
    + pose proof (chain_shift (- c) ts (c + a) (c + b) Hch) as H.
      replace (- c + (c + a)) with a in H by ring.
      replace (- c + (c + b)) with b in H by ring.
      exact H.
    + rewrite polyline_len_shift, map_app, map_shift_cancel. reflexivity.
Qed.

Print Assumptions is_curve_length_shift.

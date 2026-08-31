(* ============================================================================
   NetTopologySuite.Proofs.NurbsKnotSpans
   ----------------------------------------------------------------------------
   Issue #565 / claimId 508-g: knot-vector carrier + induction over spans,
   and the two-golden-quarter half-circle instance.

   NurbsGeneralLength.nurbs_knot_span_additive is already the two-window
   special case (curve_length_additive on one curve).  This file does NOT
   remint that identifier.  It adds:

     1. knot_vector  = a weakly increasing chain of knots
     2. span_lengths = one is_curve_length per consecutive knot window
     3. nurbs_spans_additive : induction on the interior-knot list
        (curve_length_additive at each cons; no new analysis)

   Instance: two quadratic golden spans glued at (0,1) — first quadrant
   from 508-a, second quadrant the rotate-90 image — on knots [0; 1; 2].
   Total length is π, which is π/2 + π/2, not a new π theorem.

   Not Cox-de Boor multi-span evaluation.  Oracle N stays single-span.
   Not a CurveSegment / Exact* zoo type.  Does not steal 508-e / 508-h.
   Does not retire epic 508 (that is #566).

   WITNESS topic: metric · claimId: 508-g · witness: 508-g-nurbs-spans
   macro: metric
   lane: proofs
   issue: #565 / #508

   No `Admitted`, no `Axiom`, no `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.6
   ========================================================================== *)

From Stdlib Require Import Reals Lra List.
From NTS.Proofs Require Import
  Distance CurveLength NurbsQuadraticLength NurbsConicExact.
Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* Knot-vector carrier and span-length induction.                             *)
(* -------------------------------------------------------------------------- *)

(* A knot vector is a weakly increasing chain.  Empty interior knots is
   a single span [k0, kend].  Repeated knots contribute dist x x = 0. *)
Definition knot_vector (k0 : R) (ks : list R) (kend : R) : Prop :=
  chain k0 ks kend.

(* One metric length per consecutive knot window.  Length-list shape
   must match: n interior knots need n+1 lengths. *)
Fixpoint span_lengths (g : Curve) (k0 : R) (ks : list R) (kend : R)
                      (Ls : list R) : Prop :=
  match ks, Ls with
  | [], [L] => is_curve_length g k0 kend L
  | k :: ks', L :: Ls' =>
      is_curve_length g k0 k L /\ span_lengths g k ks' kend Ls'
  | _, _ => False
  end.

Definition list_sum (xs : list R) : R := fold_right Rplus 0 xs.

(* WITNESS {"claimId":"508-g","witness":"508-g-nurbs-spans","topic":"metric","lemma":"nurbs_spans_additive","title":"Metric length on a knot vector is the sum of the per-span lengths","file":"theories/NurbsKnotSpans.v","board":"#565"} *)

Theorem nurbs_spans_additive :
  forall (g : Curve) k0 ks kend Ls,
    knot_vector k0 ks kend ->
    span_lengths g k0 ks kend Ls ->
    is_curve_length g k0 kend (list_sum Ls).
Proof.
  intros g k0 ks kend Ls.
  revert k0 Ls.
  induction ks as [|k ks' IH]; intros k0 Ls Hkv Hsp.
  - destruct Ls as [|L Ls']; [simpl in Hsp; contradiction Hsp |].
    destruct Ls' as [|L2 rest]; [| simpl in Hsp; contradiction Hsp].
    unfold list_sum. simpl.
    replace (L + 0) with L by ring.
    exact Hsp.
  - destruct Ls as [|L Ls']; [simpl in Hsp; contradiction Hsp |].
    destruct Hkv as [Hk0k Htail].
    destruct Hsp as [Hspan0 Hrest].
    unfold list_sum. simpl.
    apply curve_length_additive with (b := k).
    + exact Hk0k.
    + exact (chain_le ks' k kend Htail).
    + exact Hspan0.
    + exact (IH k Ls' Htail Hrest).
Qed.

Print Assumptions nurbs_spans_additive.

(* The two-window special case is already
   NurbsGeneralLength.nurbs_knot_span_additive
   (= CurveLength.curve_length_additive).  This file does not remint it. *)

(* -------------------------------------------------------------------------- *)
(* Rotate-90 isometry (second-quadrant golden span).                          *)
(* -------------------------------------------------------------------------- *)

Definition rot90 (p : Point) : Point := mkPoint (- py p) (px p).

Lemma rot90_dist_sq : forall p q, dist_sq (rot90 p) (rot90 q) = dist_sq p q.
Proof.
  intros p q. unfold dist_sq, rot90. simpl. ring.
Qed.

Lemma rot90_dist : forall p q, dist (rot90 p) (rot90 q) = dist p q.
Proof.
  intros p q. unfold dist. f_equal. apply rot90_dist_sq.
Qed.

Lemma polyline_len_isometry :
  forall (f : Point -> Point) (g : Curve) ts t,
    (forall p q, dist (f p) (f q) = dist p q) ->
    polyline_len (fun u => f (g u)) t ts = polyline_len g t ts.
Proof.
  intros f g ts; induction ts as [|u tl IH]; intros t Hf; simpl.
  - reflexivity.
  - rewrite Hf, (IH u Hf). reflexivity.
Qed.

Lemma is_curve_length_isometry :
  forall (f : Point -> Point) (g : Curve) a b L,
    (forall p q, dist (f p) (f q) = dist p q) ->
    is_curve_length g a b L ->
    is_curve_length (fun t => f (g t)) a b L.
Proof.
  intros f g a b L Hf [Hub Hlst].
  split.
  - intros l (ts & Hch & Hl). subst l.
    apply Hub. exists ts. split; [exact Hch |].
    rewrite <- (polyline_len_isometry f g (ts ++ [b]) a Hf).
    reflexivity.
  - intros M HM. apply Hlst. intros l (ts & Hch & Hl). subst l.
    apply HM. exists ts. split; [exact Hch |].
    rewrite (polyline_len_isometry f g (ts ++ [b]) a Hf).
    reflexivity.
Qed.

Lemma rot90_nurbs2_pt : forall p0 p1 p2 w0 w1 w2 t,
  nurbs2_pt (rot90 p0) (rot90 p1) (rot90 p2) w0 w1 w2 t
  = rot90 (nurbs2_pt p0 p1 p2 w0 w1 w2 t).
Proof.
  intros p0 p1 p2 w0 w1 w2 t.
  unfold nurbs2_pt, rot90, nurbs2_den. simpl.
  apply point_ext; simpl.
  - rewrite <- Ropp_div. f_equal. ring.
  - reflexivity.
Qed.

Definition golden_q2_p0 : Point := rot90 golden_p0.
Definition golden_q2_p1 : Point := rot90 golden_p1.
Definition golden_q2_p2 : Point := rot90 golden_p2.

Definition golden_q2_param : Curve :=
  nurbs2_param golden_q2_p0 golden_q2_p1 golden_q2_p2
               golden_w0 golden_w1 golden_w2.

Lemma golden_q2_rot : forall t,
  golden_q2_param t = rot90 (golden_param t).
Proof.
  intro t.
  unfold golden_q2_param, golden_param, nurbs2_param.
  unfold golden_q2_p0, golden_q2_p1, golden_q2_p2.
  apply rot90_nurbs2_pt.
Qed.

Theorem golden_q2_length :
  is_curve_length golden_q2_param 0 1 (PI / 2).
Proof.
  apply (is_curve_length_ext (fun t => rot90 (golden_param t))
                             golden_q2_param).
  - intro t. symmetry. apply golden_q2_rot.
  - apply (is_curve_length_isometry rot90 golden_param).
    + apply rot90_dist.
    + exact nurbs2_golden_quarter_length.
Qed.

(* -------------------------------------------------------------------------- *)
(* Piecewise two-span half-circle on knots [0; 1; 2].                         *)
(* -------------------------------------------------------------------------- *)

Definition golden_half (t : R) : Point :=
  match Rle_dec t 1 with
  | left _ => golden_param t
  | right _ => golden_q2_param (t - 1)
  end.

Lemma golden_param_at_1 : golden_param 1 = mkPoint 0 1.
Proof.
  unfold golden_param, nurbs2_param, nurbs2_pt, nurbs2_den.
  unfold golden_p0, golden_p1, golden_p2, golden_w0, golden_w1, golden_w2.
  unfold bern2_0, bern2_1, bern2_2. simpl.
  apply point_ext; simpl; field.
Qed.

Lemma golden_q2_param_at_0 : golden_q2_param 0 = mkPoint 0 1.
Proof.
  unfold golden_q2_param, nurbs2_param, nurbs2_pt, nurbs2_den.
  unfold golden_q2_p0, golden_q2_p1, golden_q2_p2, rot90.
  unfold golden_p0, golden_p1, golden_p2, golden_w0, golden_w1, golden_w2.
  unfold bern2_0, bern2_1, bern2_2. simpl.
  apply point_ext; simpl; field.
Qed.

Lemma golden_half_glue : golden_param 1 = golden_q2_param 0.
Proof.
  rewrite golden_param_at_1, golden_q2_param_at_0. reflexivity.
Qed.

Lemma golden_half_on_span0 : forall t, t <= 1 -> golden_half t = golden_param t.
Proof.
  intros t Ht. unfold golden_half.
  destruct (Rle_dec t 1) as [Hle | Hgt]; [reflexivity | lra].
Qed.

Lemma golden_half_on_span1 :
  forall t, 1 <= t -> golden_half t = golden_q2_param (t - 1).
Proof.
  intros t Ht. unfold golden_half.
  destruct (Rle_dec t 1) as [Hle | Hgt].
  - assert (Heq : t = 1) by lra. rewrite Heq.
    replace (1 - 1) with 0 by ring.
    exact golden_half_glue.
  - reflexivity.
Qed.

Lemma golden_half_span0 : is_curve_length golden_half 0 1 (PI / 2).
Proof.
  apply (is_curve_length_ext_on golden_param golden_half).
  - intros t _ Ht1. symmetry. apply golden_half_on_span0. exact Ht1.
  - exact nurbs2_golden_quarter_length.
Qed.

Lemma golden_half_span1 : is_curve_length golden_half 1 2 (PI / 2).
Proof.
  apply (is_curve_length_ext_on
           (fun t => golden_q2_param (t - 1)) golden_half).
  - intros t Ht1 _. symmetry. apply golden_half_on_span1. exact Ht1.
  - apply (is_curve_length_ext
             (fun t => golden_q2_param (-1 + t))
             (fun t => golden_q2_param (t - 1))).
    + intro t. f_equal. ring.
    + pose proof (is_curve_length_shift golden_q2_param (-1) 1 2 (PI / 2))
        as Hshift.
      replace (-1 + 1) with 0 in Hshift by ring.
      replace (-1 + 2) with 1 in Hshift by ring.
      apply Hshift. exact golden_q2_length.
Qed.

(* WITNESS {"claimId":"508-g","witness":"508-g-nurbs-spans","topic":"metric","lemma":"golden_half_circle_length","title":"Two golden quarter NURBS spans glue to a half-circle of length π","file":"theories/NurbsKnotSpans.v","board":"#565"} *)

Theorem golden_half_circle_length :
  is_curve_length golden_half 0 2 PI.
Proof.
  pose (Ls := [PI / 2; PI / 2]).
  assert (H : is_curve_length golden_half 0 2 (list_sum Ls)).
  { apply (nurbs_spans_additive golden_half 0 [1] 2 Ls).
    - unfold knot_vector. simpl. split; lra.
    - unfold Ls. simpl. split.
      + exact golden_half_span0.
      + exact golden_half_span1. }
  unfold Ls, list_sum in H. simpl in H.
  replace (PI / 2 + (PI / 2 + 0)) with PI in H by field.
  exact H.
Qed.

Print Assumptions golden_half_circle_length.

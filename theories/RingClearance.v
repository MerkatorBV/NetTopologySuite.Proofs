(* ==========================================================================
   RingClearance.v

   [H-bridge attack, rung C-3a] The clearance ball: an off-ring point of a
   horizontal-edge-free ring has a whole (sup-metric) ball inside the ring
   complement.

   Every corner connector of the planned face-walk transport (rung C-3, see
   plan.md) must route a short polyline near a vertex while staying in
   `ring_complement` -- and unlike the fixed-height corridors of rungs
   C-1/C-2, corners are genuinely two-dimensional, so a positive clearance
   radius around an off-ring point is unavoidable.  For a HORIZONTAL-FREE
   ring this needs no distance/sqrt analysis at all:

     a point off a non-horizontal closed segment either has its height
     STRICTLY outside the segment's closed y-span (heights survive small
     perturbations), or it has an ABSCISSA GAP to the segment's carrier
     line at its own height (the carrier is an affine graph x = al*y + be;
     the gap shrinks by at most (1 + |al|) * eps under an eps-perturbation).

   `off_edge_ball` proves the per-edge ball from that dichotomy;
   `off_edges_ball_list` takes the finite minimum (same induction shape as
   `StraddlePair.ho_cross_agree_ball`); the headline `ring_complement_ball`
   assembles them over `ring_edges`.

   Pure-R + list combinatorics; no `Admitted` / `Axiom` / `Parameter`;
   allowlist axioms only.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
   ========================================================================== *)

From Stdlib Require Import Reals Lra List Arith Lia.
From NTS.Proofs Require Import Distance Overlay PointInRingTangents JCTHugStep.

Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  Membership in one closed segment, and its two elementary facts.         *)
(* -------------------------------------------------------------------------- *)

Definition on_edge (f : Edge) (q : Point) : Prop :=
  exists s : R, 0 <= s <= 1 /\
    px q = (1 - s) * px (fst f) + s * px (snd f) /\
    py q = (1 - s) * py (fst f) + s * py (snd f).

(* A segment point's height lies in the closed y-span of the endpoints. *)
Lemma on_edge_height_in_span :
  forall (f : Edge) (q : Point),
    on_edge f q ->
    Rmin (py (fst f)) (py (snd f)) <= py q <= Rmax (py (fst f)) (py (snd f)).
Proof.
  intros f q [s [Hs [_ Hy]]].
  pose proof (Rmin_l (py (fst f)) (py (snd f))).
  pose proof (Rmin_r (py (fst f)) (py (snd f))).
  pose proof (Rmax_l (py (fst f)) (py (snd f))).
  pose proof (Rmax_r (py (fst f)) (py (snd f))).
  rewrite Hy. split; nra.
Qed.

(* A segment point of a non-horizontal edge satisfies the carrier-line
   equation x = al * y + be. *)
Lemma on_edge_carrier :
  forall (f : Edge) (q : Point),
    py (fst f) <> py (snd f) ->
    on_edge f q ->
    px q = (px (snd f) - px (fst f)) / (py (snd f) - py (fst f)) * py q
           + (px (fst f)
              - (px (snd f) - px (fst f)) / (py (snd f) - py (fst f))
                * py (fst f)).
Proof.
  intros f q Hnh [s [Hs [Hx Hy]]].
  rewrite Hx, Hy. field. intro Hc. apply Hnh. lra.
Qed.

(* Conversely: carrier equation + height in the closed span = on the edge. *)
Lemma carrier_in_span_on_edge :
  forall (f : Edge) (q : Point),
    py (fst f) <> py (snd f) ->
    Rmin (py (fst f)) (py (snd f)) <= py q <= Rmax (py (fst f)) (py (snd f)) ->
    px q = (px (snd f) - px (fst f)) / (py (snd f) - py (fst f)) * py q
           + (px (fst f)
              - (px (snd f) - px (fst f)) / (py (snd f) - py (fst f))
                * py (fst f)) ->
    on_edge f q.
Proof.
  intros f q Hnh Hspan Hcar.
  set (s := (py q - py (fst f)) / (py (snd f) - py (fst f))).
  assert (Hsd : s * (py (snd f) - py (fst f)) = py q - py (fst f))
    by (unfold s; field; intro Hc; apply Hnh; lra).
  exists s.
  assert (Hs01 : 0 <= s <= 1).
  { destruct (Rtotal_order (py (fst f)) (py (snd f))) as [Hlt | [Heq | Hgt]];
      [ | exfalso; exact (Hnh Heq) | ].
    - rewrite Rmin_left, Rmax_right in Hspan by lra. nra.
    - rewrite Rmin_right, Rmax_left in Hspan by lra. nra. }
  split; [ exact Hs01 | ].
  split.
  - rewrite Hcar. unfold s. field. intro Hc. apply Hnh. lra.
  - nra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  Per-edge clearance ball (the height/abscissa dichotomy).                *)
(* -------------------------------------------------------------------------- *)

Lemma off_edge_ball :
  forall (f : Edge) (q : Point),
    py (fst f) <> py (snd f) ->
    ~ on_edge f q ->
    exists eps, 0 < eps /\
      forall q' : Point,
        Rabs (px q' - px q) < eps -> Rabs (py q' - py q) < eps ->
        ~ on_edge f q'.
Proof.
  intros f q Hnh Hoff.
  set (lo := Rmin (py (fst f)) (py (snd f))).
  set (hi := Rmax (py (fst f)) (py (snd f))).
  set (al := (px (snd f) - px (fst f)) / (py (snd f) - py (fst f))).
  set (be := px (fst f) - al * py (fst f)).
  destruct (Rlt_dec (py q) lo) as [Hbelow | Hnb].
  - (* strictly below the span *)
    exists (lo - py q). split; [ lra | ].
    intros q' _ Hdy Hon.
    pose proof (on_edge_height_in_span f q' Hon) as Hspan.
    fold lo in Hspan.
    apply Rabs_def2 in Hdy. lra.
  - destruct (Rlt_dec hi (py q)) as [Habove | Hna].
    + (* strictly above the span *)
      exists (py q - hi). split; [ lra | ].
      intros q' _ Hdy Hon.
      pose proof (on_edge_height_in_span f q' Hon) as Hspan.
      fold hi in Hspan.
      apply Rabs_def2 in Hdy. lra.
    + (* height in the closed span: the abscissa gap is nonzero *)
      assert (Hspanq : lo <= py q <= hi) by lra.
      set (G := px q - (al * py q + be)).
      assert (HG : G <> 0).
      { intro HG0. apply Hoff.
        unfold lo, hi in Hspanq.
        apply (carrier_in_span_on_edge f q Hnh Hspanq).
        unfold G, be, al in HG0. lra. }
      assert (Hden : 0 < 1 + Rabs al) by (pose proof (Rabs_pos al); lra).
      assert (HGpos : 0 < Rabs G) by (apply Rabs_pos_lt; exact HG).
      exists (Rabs G / (2 * (1 + Rabs al))).
      split.
      { apply Rdiv_lt_0_compat; lra. }
      intros q' Hdx Hdy Hon.
      (* q' on f satisfies the carrier equation *)
      pose proof (on_edge_carrier f q' Hnh Hon) as Hcar'.
      fold al in Hcar'. fold be in Hcar'.
      assert (Hcar0 : px q' - (al * py q' + be) = 0) by lra.
      (* but the perturbed gap is still nonzero *)
      set (dx := px q' - px q). set (dy := py q' - py q).
      assert (Hval : px q' - (al * py q' + be) = G + (dx - al * dy))
        by (unfold G, dx, dy; ring).
      assert (Heq0 : G + (dx - al * dy) = 0) by lra.
      assert (Hper : Rabs (dx - al * dy) < Rabs G / 2).
      { eapply Rle_lt_trans; [ apply Rabs_triang | ].
        rewrite Rabs_Ropp, Rabs_mult.
        assert (Hb1 : Rabs dx < Rabs G / (2 * (1 + Rabs al))) by exact Hdx.
        assert (Hb2 : Rabs al * Rabs dy
                        <= Rabs al * (Rabs G / (2 * (1 + Rabs al)))).
        { apply Rmult_le_compat_l; [ apply Rabs_pos | ].
          left. exact Hdy. }
        assert (Hsum : Rabs G / (2 * (1 + Rabs al))
                         + Rabs al * (Rabs G / (2 * (1 + Rabs al)))
                       = Rabs G / 2)
          by (field; lra).
        lra. }
      apply Rabs_def2 in Hper. destruct Hper as [Hp1 Hp2].
      destruct (Rcase_abs G) as [Hneg | Hpos].
      * rewrite (Rabs_left G Hneg) in Hp1, Hp2. lra.
      * rewrite (Rabs_right G Hpos) in Hp1, Hp2, HGpos. lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Finite assembly over an edge list, and the ring headline.               *)
(* -------------------------------------------------------------------------- *)

Lemma off_edges_ball_list :
  forall (es : list Edge) (q : Point),
    (forall f, In f es ->
       exists eps, 0 < eps /\
         forall q' : Point,
           Rabs (px q' - px q) < eps -> Rabs (py q' - py q) < eps ->
           ~ on_edge f q') ->
    exists eps, 0 < eps /\
      forall q' : Point,
        Rabs (px q' - px q) < eps -> Rabs (py q' - py q) < eps ->
        forall f, In f es -> ~ on_edge f q'.
Proof.
  intros es q Hst. induction es as [| e es IH].
  - exists 1. split; [ lra | ]. intros q' _ _ f [].
  - destruct (Hst e (or_introl eq_refl)) as [e1 [He1 Hb1]].
    destruct (IH (fun f Hf => Hst f (or_intror Hf))) as [e2 [He2 Hb2]].
    exists (Rmin e1 e2). split; [ apply Rmin_glb_lt; lra | ].
    intros q' Hdx Hdy f [Hf | Hf].
    + subst f. apply Hb1.
      * eapply Rlt_le_trans; [ exact Hdx | apply Rmin_l ].
      * eapply Rlt_le_trans; [ exact Hdy | apply Rmin_l ].
    + apply (Hb2 q'); [ | | exact Hf ].
      * eapply Rlt_le_trans; [ exact Hdx | apply Rmin_r ].
      * eapply Rlt_le_trans; [ exact Hdy | apply Rmin_r ].
Qed.

(* Headline: an off-ring point of a horizontal-free ring has a whole
   clearance ball inside the complement. *)
Theorem ring_complement_ball :
  forall (r : Ring) (q : Point),
    no_horizontal_edges r ->
    ring_complement r q ->
    exists eps, 0 < eps /\
      forall q' : Point,
        Rabs (px q' - px q) < eps -> Rabs (py q' - py q) < eps ->
        ring_complement r q'.
Proof.
  intros r q Hnoh Hcomp.
  assert (Hst : forall f, In f (ring_edges r) ->
    exists eps, 0 < eps /\
      forall q' : Point,
        Rabs (px q' - px q) < eps -> Rabs (py q' - py q) < eps ->
        ~ on_edge f q').
  { intros f Hf.
    apply off_edge_ball.
    - exact (Hnoh f Hf).
    - intros [s [Hs [Hx Hy]]]. apply Hcomp.
      exists f, s.
      split; [ exact Hf | split; [ exact Hs | split; [ exact Hx | exact Hy ] ] ]. }
  destruct (off_edges_ball_list (ring_edges r) q Hst) as [eps [Heps Hball]].
  exists eps. split; [ exact Heps | ].
  intros q' Hdx Hdy [f [s [Hf [Hs [Hx Hy]]]]].
  apply (Hball q' Hdx Hdy f Hf).
  exists s.
  split; [ exact Hs | split; [ exact Hx | exact Hy ] ].
Qed.

(* -------------------------------------------------------------------------- *)
(* Axiom audit.  Pure-R + combinatorial wiring; allowlist axioms only.         *)
(* -------------------------------------------------------------------------- *)

Print Assumptions off_edge_ball.
Print Assumptions ring_complement_ball.

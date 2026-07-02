(* ==========================================================================
   FanGapSector.v

   [H-bridge attack, C-3d step 1] The fan-gap sector bridge: no fan dart's
   direction lies strictly inside the CCW gap from a dart to its `next`.

   This is the azimuth <-> sector bridge flagged since the C-3 design: the
   corner connectors (`CornerConnector.v`) certify their polylines with
   `SectorPath.in_open_sector`, while the face walk's turn is governed by
   `DartNext.next` in the `dir_lt` azimuth order.  Here the two worlds
   meet:

     - `dir_between u g w`: strict cyclic betweenness in the CCW-from-east
       order `dir_lt` (the three rotations of `u < g < w`);
     - `next_gap_empty` (pure order): for a fan dart `a`, no OTHER fan
       dart sits `dir_between` `a` and `next F a` -- direct from
       `next_min_successor` / `next_wrap_least`;
     - `in_open_sector_dir_between` (the geometric bridge): a strict
       sector certificate implies cyclic betweenness -- an 8-way
       half-plane case analysis in the style of `dir_lt_trans`, with
       `vcross_chain_cert` + sign algebra refuting the five impossible
       mixed configurations;
     - `fan_next_gap_empty_sector` (headline): composing the two, the
       open sector from `ddir a` to `ddir (next F a)` contains no other
       fan direction.  Downstream (C-3d step 2) this lets the corner
       polyline avoid EVERY edge germ at the vertex, not just the two
       walls.

   Pure Vec/order algebra; no `Admitted` / `Axiom` / `Parameter`;
   allowlist axioms only.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
   ========================================================================== *)

From Stdlib Require Import Reals Lra List Arith Lia.
From NTS.Proofs Require Import Distance Overlay OverlayGraph Vec Direction
                               Dart DartAngularOrder DartNext DartNextSpec
                               MinDegreeCore SectorPath.

Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  Cyclic betweenness in the azimuth order, and small order plumbing.      *)
(* -------------------------------------------------------------------------- *)

(* `g` lies strictly between `u` and `w` on the CCW circle: one of the three
   rotations of `u < g < w` in the linear order `dir_lt`. *)
Definition dir_between (u g w : Vec) : Prop :=
  (dir_lt u g /\ dir_lt g w)
  \/ (dir_lt w u /\ dir_lt u g)
  \/ (dir_lt g w /\ dir_lt w u).

Lemma cross_nonzero : forall p q, ~ parallel p q -> vcross p q <> 0.
Proof.
  intros p q Hnp H0. apply Hnp.
  apply (proj2 (parallel_iff_vcross_zero p q)). exact H0.
Qed.

Lemma nonparallel_nonzero_l : forall p q, ~ parallel p q -> p <> vzero.
Proof.
  intros p q Hnp Heq. apply (cross_nonzero p q Hnp).
  subst p. unfold vcross, vzero. cbn. ring.
Qed.

Lemma nonparallel_nonzero_r : forall p q, ~ parallel p q -> q <> vzero.
Proof.
  intros p q Hnp Heq. apply (cross_nonzero p q Hnp).
  subst q. unfold vcross, vzero. cbn. ring.
Qed.

(* The three `dir_lt` constructors used by the bridge. *)
Lemma dir_lt_same_fh :
  forall p q, first_half p -> first_half q -> vcross p q > 0 -> dir_lt p q.
Proof.
  intros p q Hp Hq Hc. right. split; [ left; split; assumption | exact Hc ].
Qed.

Lemma dir_lt_same_nfh :
  forall p q, ~ first_half p -> ~ first_half q -> vcross p q > 0 -> dir_lt p q.
Proof.
  intros p q Hp Hq Hc. right. split; [ right; split; assumption | exact Hc ].
Qed.

Lemma dir_lt_split :
  forall p q, first_half p -> ~ first_half q -> dir_lt p q.
Proof. intros p q Hp Hq. left. split; assumption. Qed.

(* Reversed-pair variants: the available sign is about the SWAPPED pair. *)
Lemma dir_lt_same_fh_rev :
  forall p q, first_half p -> first_half q -> vcross q p < 0 -> dir_lt p q.
Proof.
  intros p q Hp Hq Hc. apply dir_lt_same_fh; try assumption.
  pose proof (vcross_antisym q p). lra.
Qed.

Lemma dir_lt_same_nfh_rev :
  forall p q, ~ first_half p -> ~ first_half q -> vcross q p < 0 -> dir_lt p q.
Proof.
  intros p q Hp Hq Hc. apply dir_lt_same_nfh; try assumption.
  pose proof (vcross_antisym q p). lra.
Qed.

(* Strict half-plane dichotomies (feeding the refutations). *)
Lemma fh_cases :
  forall p, first_half p -> vy p > 0 \/ (vy p = 0 /\ vx p > 0).
Proof. intros p H. exact H. Qed.

Lemma nfh_cases :
  forall p, p <> vzero -> ~ first_half p ->
    vy p < 0 \/ (vy p = 0 /\ vx p < 0).
Proof.
  intros p Hnz Hnf.
  destruct (not_first_half_signs p Hnz Hnf) as [Hy Hax].
  destruct (Rtotal_order (vy p) 0) as [H | [H | H]].
  - left. exact H.
  - right. split; [ exact H | exact (Hax H) ].
  - lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  The order half: the `next` gap holds no other fan dart.                 *)
(* -------------------------------------------------------------------------- *)

Lemma next_gap_empty :
  forall F a g,
    fan_ok F -> In a F -> In g F ->
    g <> a -> g <> next F a ->
    ~ dir_between (ddir a) (ddir g) (ddir (next F a)).
Proof.
  intros F a g HF Ha Hg Hga Hgb Hbet.
  set (b := next F a) in *.
  destruct (existsb (fun e => dart_ltb a e) F) eqn:Hex.
  - (* a has a strict successor: b is the least one *)
    apply existsb_exists in Hex. destruct Hex as [e [HeF Hlt]].
    apply dart_ltb_spec in Hlt.
    destruct (next_min_successor F a HF (ex_intro _ e (conj HeF Hlt)))
      as [HbF [Hab Hmin]].
    destruct Hbet as [[Hag Hgb'] | [[Hba Hag] | [Hgb' Hba]]].
    + (* a < g < b contradicts minimality *)
      destruct (Hmin g Hg Hag) as [Hbg | Hbg].
      * apply Hgb. symmetry. exact Hbg.
      * exact (dart_lt_asym g b Hgb' Hbg).
    + exact (dart_lt_asym a b Hab Hba).
    + exact (dart_lt_asym a b Hab Hba).
  - (* a is the fan maximum: b is the global least *)
    assert (Hmax : forall e, In e F -> ~ dart_lt a e).
    { intros e HeF Hcontra.
      assert (Htrue : existsb (fun e0 => dart_ltb a e0) F = true).
      { apply existsb_exists. exists e.
        split; [ exact HeF | apply dart_ltb_spec; exact Hcontra ]. }
      rewrite Htrue in Hex. discriminate. }
    pose proof (next_wrap_least F a HF Ha Hmax) as Hleast.
    destruct Hbet as [[Hag _] | [[_ Hag] | [Hgb' _]]].
    + exact (Hmax g Hg Hag).
    + exact (Hmax g Hg Hag).
    + destruct (Hleast g Hg) as [Hbg | Hbg].
      * apply Hgb. symmetry. exact Hbg.
      * exact (dart_lt_asym g b Hgb' Hbg).
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  The geometric half: a strict sector certificate implies betweenness.    *)
(* -------------------------------------------------------------------------- *)

(* An 8-way half-plane case analysis (the `dir_lt_trans` pattern,
   DartAngularOrder.v).  The two all-same-half configurations close
   constructively; six mixed sub-cases close by the free half-split
   ordering; the five impossible sign patterns are refuted by
   `vcross_chain_cert` + strict half-plane sign algebra. *)
Lemma in_open_sector_dir_between :
  forall u g w : Vec,
    ~ parallel u w -> ~ parallel u g -> ~ parallel g w ->
    in_open_sector u w g ->
    dir_between u g w.
Proof.
  intros u g w Hnp_uw Hnp_ug Hnp_gw Hsect.
  assert (Hu0 : u <> vzero) by (exact (nonparallel_nonzero_l u w Hnp_uw)).
  assert (Hw0 : w <> vzero) by (exact (nonparallel_nonzero_r u w Hnp_uw)).
  assert (Hg0 : g <> vzero) by (exact (nonparallel_nonzero_r u g Hnp_ug)).
  assert (Huw : vcross u w <> 0) by (exact (cross_nonzero u w Hnp_uw)).
  assert (Hug : vcross u g <> 0) by (exact (cross_nonzero u g Hnp_ug)).
  assert (Hgw : vcross g w <> 0) by (exact (cross_nonzero g w Hnp_gw)).
  pose proof (vcross_chain_cert u g w) as Hcert.
  destruct Hsect as [[Hcuw [Hcug Hcgw]] | [Hcuw Hor]].
  - (* CONVEX certificate: both wall crosses strictly positive *)
    destruct (first_half_dec u) as [Fu | Fu];
    destruct (first_half_dec g) as [Fg | Fg];
    destruct (first_half_dec w) as [Fw | Fw].
    + (* TTT *) left.
      split; [ apply dir_lt_same_fh; assumption
             | apply dir_lt_same_fh; assumption ].
    + (* TTF *) left.
      split; [ apply dir_lt_same_fh; assumption
             | apply dir_lt_split; assumption ].
    + (* TFT : impossible under convex *)
      exfalso.
      destruct (fh_cases u Fu) as [Hyu | [Hyu Hxu]];
      destruct (nfh_cases g Hg0 Fg) as [Hyg | [Hyg Hxg]];
      destruct (fh_cases w Fw) as [Hyw | [Hyw Hxw]];
      try nra;
      unfold vcross in *; nra.
    + (* TFF *) left.
      split; [ apply dir_lt_split; assumption
             | apply dir_lt_same_nfh; assumption ].
    + (* FTT *) right. right.
      split; [ apply dir_lt_same_fh; assumption
             | apply dir_lt_split; assumption ].
    + (* FTF : impossible under convex *)
      exfalso.
      destruct (nfh_cases u Hu0 Fu) as [Hyu | [Hyu Hxu]];
      destruct (fh_cases g Fg) as [Hyg | [Hyg Hxg]];
      destruct (nfh_cases w Hw0 Fw) as [Hyw | [Hyw Hxw]];
      try nra;
      unfold vcross in *; nra.
    + (* FFT *) right. left.
      split; [ apply dir_lt_split; assumption
             | apply dir_lt_same_nfh; assumption ].
    + (* FFF *) left.
      split; [ apply dir_lt_same_nfh; assumption
             | apply dir_lt_same_nfh; assumption ].
  - (* REFLEX certificate: negative gap cross, one positive side cross *)
    destruct (first_half_dec u) as [Fu | Fu];
    destruct (first_half_dec g) as [Fg | Fg];
    destruct (first_half_dec w) as [Fw | Fw].
    + (* TTT *)
      destruct Hor as [Hcug | Hcgw].
      * destruct (Rdichotomy _ _ Hgw) as [Hneg | Hpos].
        -- (* w < g here, and w < u from the reflex gap: disjunct 2 *)
           right. left.
           split; [ apply dir_lt_same_fh_rev; assumption
                  | apply dir_lt_same_fh; assumption ].
        -- left.
           split; [ apply dir_lt_same_fh; assumption
                  | apply dir_lt_same_fh; assumption ].
      * destruct (Rdichotomy _ _ Hug) as [Hneg | Hpos].
        -- (* g < u here: disjunct 3 *)
           right. right.
           split; [ apply dir_lt_same_fh; assumption
                  | apply dir_lt_same_fh_rev; assumption ].
        -- left.
           split; [ apply dir_lt_same_fh; assumption
                  | apply dir_lt_same_fh; assumption ].
    + (* TTF *)
      destruct Hor as [Hcug | Hcgw].
      * left.
        split; [ apply dir_lt_same_fh; assumption
               | apply dir_lt_split; assumption ].
      * (* only g-w positive: impossible in TTF under reflex *)
        destruct (Rdichotomy _ _ Hug) as [Hneg | Hpos].
        -- exfalso.
           destruct (fh_cases u Fu) as [Hyu | [Hyu Hxu]];
           destruct (fh_cases g Fg) as [Hyg | [Hyg Hxg]];
           destruct (nfh_cases w Hw0 Fw) as [Hyw | [Hyw Hxw]];
           try nra;
           unfold vcross in *; nra.
        -- (* the u-g cross is positive after all: disjunct 1 *)
           left.
           split; [ apply dir_lt_same_fh; assumption
                  | apply dir_lt_split; assumption ].
    + (* TFT : disjunct 2 directly (w < u from the reflex gap) *)
      right. left.
      split; [ apply dir_lt_same_fh_rev; assumption
             | apply dir_lt_split; assumption ].
    + (* TFF *)
      destruct Hor as [Hcug | Hcgw].
      * (* u-g positive: does g < w hold?  decide *)
        destruct (Rdichotomy _ _ Hgw) as [Hneg | Hpos].
        -- (* impossible: refute *)
           exfalso.
           destruct (fh_cases u Fu) as [Hyu | [Hyu Hxu]];
           destruct (nfh_cases g Hg0 Fg) as [Hyg | [Hyg Hxg]];
           destruct (nfh_cases w Hw0 Fw) as [Hyw | [Hyw Hxw]];
           try nra;
           unfold vcross in *; nra.
        -- left.
           split; [ apply dir_lt_split; assumption
                  | apply dir_lt_same_nfh; assumption ].
      * left.
        split; [ apply dir_lt_split; assumption
               | apply dir_lt_same_nfh; assumption ].
    + (* FTT *)
      destruct Hor as [Hcug | Hcgw].
      * (* only u-g positive: decide g-w *)
        destruct (Rdichotomy _ _ Hgw) as [Hneg | Hpos].
        -- exfalso.
           destruct (nfh_cases u Hu0 Fu) as [Hyu | [Hyu Hxu]];
           destruct (fh_cases g Fg) as [Hyg | [Hyg Hxg]];
           destruct (fh_cases w Fw) as [Hyw | [Hyw Hxw]];
           try nra;
           unfold vcross in *; nra.
        -- right. right.
           split; [ apply dir_lt_same_fh; assumption
                  | apply dir_lt_split; assumption ].
      * right. right.
        split; [ apply dir_lt_same_fh; assumption
               | apply dir_lt_split; assumption ].
    + (* FTF : disjunct 3 directly (w < u from the reflex gap) *)
      right. right.
      split; [ apply dir_lt_split; assumption
             | apply dir_lt_same_nfh_rev; assumption ].
    + (* FFT *)
      destruct Hor as [Hcug | Hcgw].
      * right. left.
        split; [ apply dir_lt_split; assumption
               | apply dir_lt_same_nfh; assumption ].
      * (* only g-w positive: impossible in FFT under reflex *)
        destruct (Rdichotomy _ _ Hug) as [Hneg | Hpos].
        -- exfalso.
           destruct (nfh_cases u Hu0 Fu) as [Hyu | [Hyu Hxu]];
           destruct (nfh_cases g Hg0 Fg) as [Hyg | [Hyg Hxg]];
           destruct (fh_cases w Fw) as [Hyw | [Hyw Hxw]];
           try nra;
           unfold vcross in *; nra.
        -- (* the u-g cross is positive after all: disjunct 2 *)
           right. left.
           split; [ apply dir_lt_split; assumption
                  | apply dir_lt_same_nfh; assumption ].
    + (* FFF *)
      destruct Hor as [Hcug | Hcgw].
      * destruct (Rdichotomy _ _ Hgw) as [Hneg | Hpos].
        -- right. left.
           split; [ apply dir_lt_same_nfh_rev; assumption
                  | apply dir_lt_same_nfh; assumption ].
        -- left.
           split; [ apply dir_lt_same_nfh; assumption
                  | apply dir_lt_same_nfh; assumption ].
      * destruct (Rdichotomy _ _ Hug) as [Hneg | Hpos].
        -- right. right.
           split; [ apply dir_lt_same_nfh; assumption
                  | apply dir_lt_same_nfh_rev; assumption ].
        -- left.
           split; [ apply dir_lt_same_nfh; assumption
                  | apply dir_lt_same_nfh; assumption ].
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Headline: the open next-gap sector holds no other fan direction.        *)
(* -------------------------------------------------------------------------- *)

Theorem fan_next_gap_empty_sector :
  forall F a g,
    fan_ok F -> In a F -> In g F ->
    g <> a -> g <> next F a ->
    ~ in_open_sector (ddir a) (ddir (next F a)) (ddir g).
Proof.
  intros F a g HF Ha Hg Hga Hgb Hsect.
  set (b := next F a) in *.
  assert (HbF : In b F) by (apply next_in; exact Ha).
  assert (Hba : b <> a).
  { apply (next_neq_self_of_other F a g HF Ha Hg Hga). }
  destruct HF as [Hproper Hpair].
  assert (Hnp_ab : ~ parallel (ddir a) (ddir b))
    by (apply Hpair; try assumption; intro Hc; exact (Hba (eq_sym Hc))).
  assert (Hnp_ag : ~ parallel (ddir a) (ddir g))
    by (apply Hpair; try assumption; intro Hc; exact (Hga (eq_sym Hc))).
  assert (Hnp_gb : ~ parallel (ddir g) (ddir b))
    by (apply Hpair; try assumption).
  apply (next_gap_empty F a g (conj Hproper Hpair) Ha Hg Hga Hgb).
  exact (in_open_sector_dir_between (ddir a) (ddir g) (ddir b)
           Hnp_ab Hnp_ag Hnp_gb Hsect).
Qed.

(* -------------------------------------------------------------------------- *)
(* Axiom audit.  Pure Vec/order algebra; allowlist axioms only.                *)
(* -------------------------------------------------------------------------- *)

Print Assumptions next_gap_empty.
Print Assumptions in_open_sector_dir_between.
Print Assumptions fan_next_gap_empty_sector.

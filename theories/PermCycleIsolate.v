(* ==========================================================================
   PermCycleIsolate.v

   [EF-4 induction] Euler ladder: cycle-count ISOLATE -- removing a
   SELF-CONTAINED 2-cycle `{d, td}` (`f d = td`, `f td = d`, nothing else in
   `S` maps to either) drops the orbit count by exactly one.

   This is the companion `PermCycleShrink.v` explicitly excluded: `Hper_ge3`
   there rules out the case where `{d, td}` is d's WHOLE orbit (period
   exactly 2) -- the isolated K2 component (`EulerWitness.w1_euler`'s single
   edge: V=2,E=1,F=1,C=1).  Unlike SPLIT/MERGE/SHRINK, no cross-wiring
   redirect is needed at all: since `f d = td` and `f td = d` already account
   for the ONLY two preimages `d` and `td` have (by injectivity), nothing
   else in `S` can map into `{d, td}`, so `f` restricted to
   `S' := S \ {d, td}` is automatically closed -- `f' := f` unchanged.

   Pure combinatorial wiring; no `Admitted` / `Axiom` / `Parameter`; allowlist
   axioms only.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
   ========================================================================== *)

From Stdlib Require Import List Arith Lia Bool.
From NTS.Proofs Require Import OrbitCycle ClassCount PermCycleCount.

Import ListNotations.

(* `cycle_count` depends on `f` only through its values ON the carrier: two
   maps that agree pointwise on a shared closed carrier give the same count.
   Needed at the Dart layer because `f' = f` there is only an EQUALITY of
   values on the surviving darts, not a literal identity of the two `fstep`
   functions (`fstep (darts_of (E_minus E d))` vs `fstep (darts_of E)`). *)
Lemma cycle_count_ext_f : forall {A : Type} (eqdec : forall a b : A, {a = b} + {a <> b})
  (f1 f2 : A -> A) (S : list A),
  (forall x, In x S -> In (f1 x) S) ->
  (forall x, In x S -> f1 x = f2 x) ->
  cycle_count eqdec f1 S = cycle_count eqdec f2 S.
Proof.
  intros A eqdec f1 f2 S Hclos1 Hagree.
  assert (Hind : forall n x, In x S ->
            In (OrbitCycle.iter f1 n x) S /\
            OrbitCycle.iter f1 n x = OrbitCycle.iter f2 n x).
  { induction n as [| n IH]; intros x Hx; cbn [OrbitCycle.iter].
    - split; [ exact Hx | reflexivity ].
    - destruct (IH x Hx) as [HinS Heq].
      split.
      + apply Hclos1; exact HinS.
      + rewrite <- Heq. apply Hagree. exact HinS. }
  unfold cycle_count, orbit_reps.
  f_equal. apply class_reps_ext_on.
  intros x y Hx _. unfold same_orbit_b.
  apply existsb_ext_in. intros n _.
  destruct (Hind n x Hx) as [_ Heqn]. rewrite Heqn. reflexivity.
Qed.

Section CycleIsolate.
  Context {A : Type}.
  Variable eqdec : forall a b : A, {a = b} + {a <> b}.
  Variable f : A -> A.
  Variable S : list A.
  Hypothesis Hclos : forall x, In x S -> In (f x) S.
  Hypothesis Hinj : forall a b, In a S -> In b S -> f a = f b -> a = b.

  Variable d td : A.
  Hypothesis HdS : In d S.
  Hypothesis HtdS : In td S.
  Hypothesis Hdtd : d <> td.
  Hypothesis Hf_d_td : f d = td.
  Hypothesis Hf_td_d : f td = d.

  Variable S' : list A.
  Hypothesis Hcarrier : forall x, In x S' <-> (In x S /\ x <> d /\ x <> td).

  Local Notation it := (OrbitCycle.iter f).

  (* `f` restricted to `S'` is closed -- no redirect needed, derived purely
     from injectivity: if `f x = d` then `f x = f td`, forcing `x = td`; if
     `f x = td` then `f x = f d`, forcing `x = d`. *)
  Lemma f_closed_S' : forall x, In x S' -> In (f x) S'.
  Proof.
    intros x Hx. destruct (proj1 (Hcarrier x) Hx) as [HxS [Hxd Hxtd]].
    apply (proj2 (Hcarrier (f x))). repeat split.
    - apply Hclos; exact HxS.
    - intro Heq. apply Hxtd. apply (Hinj x td HxS HtdS). rewrite Heq. symmetry. exact Hf_td_d.
    - intro Heq. apply Hxd. apply (Hinj x d HxS HdS). rewrite Heq. symmetry. exact Hf_d_td.
  Qed.

  Lemma f_inj_S' : forall a b, In a S' -> In b S' -> f a = f b -> a = b.
  Proof.
    intros a b Ha Hb Heq. apply Hinj.
    - exact (proj1 (proj1 (Hcarrier a) Ha)).
    - exact (proj1 (proj1 (Hcarrier b) Hb)).
    - exact Heq.
  Qed.

  (* `d`'s orbit in `(f, S)` never leaves `{d, td}`. *)
  Lemma it_d_cycle2 : forall n, it n d = d \/ it n d = td.
  Proof.
    induction n as [| n IH].
    - left. reflexivity.
    - cbn [OrbitCycle.iter]. destruct IH as [-> | ->].
      + right. exact Hf_d_td.
      + left. exact Hf_td_d.
  Qed.

  Definition inO (x : A) : bool := same_orbit_b eqdec f S d x.

  Lemma inO_charac : forall x, In x S -> (inO x = true <-> (x = d \/ x = td)).
  Proof.
    intros x Hx. unfold inO. split.
    - intro Hb. apply same_orbit_b_sound in Hb. destruct Hb as [n Hn].
      destruct (it_d_cycle2 n) as [Heq | Heq]; rewrite Heq in Hn;
        [ left | right ]; symmetry; exact Hn.
    - intros [-> | ->].
      + apply same_orbit_b_refl.
      + apply (same_orbit_b_complete eqdec f S Hclos Hinj d HdS td). exists 1%nat.
        cbn [OrbitCycle.iter]. exact Hf_d_td.
  Qed.

  Lemma inO_block_eq_1 : count_classes (same_orbit_b eqdec f S) (filter inO S) = 1%nat.
  Proof.
    apply (count_classes_eq_1 (same_orbit_b eqdec f S) (same_orbit_b_refl eqdec f S)).
    - intro Hnil.
      assert (Hin : In d (filter inO S))
        by (apply filter_In; split; [ exact HdS | unfold inO; apply same_orbit_b_refl ]).
      rewrite Hnil in Hin. destruct Hin.
    - intros x y Hx Hy. apply filter_In in Hx. apply filter_In in Hy.
      destruct Hx as [HxS Hxo]. destruct Hy as [HyS Hyo].
      apply (inO_charac x HxS) in Hxo. apply (inO_charac y HyS) in Hyo.
      destruct Hxo as [-> | ->]; destruct Hyo as [-> | ->].
      + apply same_orbit_b_refl.
      + apply (same_orbit_b_complete eqdec f S Hclos Hinj d HdS td). exists 1%nat.
        cbn [OrbitCycle.iter]. exact Hf_d_td.
      + apply (same_orbit_b_complete eqdec f S Hclos Hinj td HtdS d). exists 1%nat.
        cbn [OrbitCycle.iter]. exact Hf_td_d.
      + apply same_orbit_b_refl.
  Qed.

  Lemma filter_negb_inO_eq_S' : forall x, In x S -> (negb (inO x) = true <-> In x S').
  Proof.
    intros x Hx. rewrite (Hcarrier x).
    destruct (same_orbit_b eqdec f S d x) eqn:Hxo; unfold inO; rewrite Hxo; cbn [negb].
    - split; [ discriminate | ].
      intros [_ [Hxd Hxtd]].
      apply (inO_charac x Hx) in Hxo. unfold inO in Hxo.
      destruct Hxo as [-> | ->]; exfalso; [ exact (Hxd eq_refl) | exact (Hxtd eq_refl) ].
    - split.
      + intros _. split; [ exact Hx | split ].
        * intro Heqd. subst x. rewrite same_orbit_b_refl in Hxo. discriminate.
        * intro Heqtd. subst x.
          assert (Hbad : same_orbit_b eqdec f S d td = true)
            by (apply (same_orbit_b_complete eqdec f S Hclos Hinj d HdS td);
                exists 1%nat; cbn [OrbitCycle.iter]; exact Hf_d_td).
          rewrite Hbad in Hxo. discriminate.
      + intros _. reflexivity.
  Qed.

  (* `same_orbit_b` on `S'` agrees with `same_orbit_b` on `S` -- orbits of
     `S'`-elements never leave `S'` (via `f_closed_S'`), so the same
     iteration witnesses the relation regardless of which carrier list
     decides it. *)
  Lemma same_orbit_b_S_S'_agree : forall x y, In x S' -> In y S' ->
    same_orbit_b eqdec f S' x y = same_orbit_b eqdec f S x y.
  Proof.
    intros x y Hx Hy.
    assert (HxS : In x S) by exact (proj1 (proj1 (Hcarrier x) Hx)).
    assert (HyS : In y S) by exact (proj1 (proj1 (Hcarrier y) Hy)).
    destruct (same_orbit_b eqdec f S' x y) eqn:E1; destruct (same_orbit_b eqdec f S x y) eqn:E2;
      try reflexivity; exfalso.
    - apply same_orbit_b_sound in E1.
      assert (same_orbit_b eqdec f S x y = true)
        by (apply (same_orbit_b_complete eqdec f S Hclos Hinj x HxS y); exact E1).
      congruence.
    - apply same_orbit_b_sound in E2. destruct E2 as [n Hn].
      assert (Hgen : forall m, In (it m x) S').
      { induction m as [| m IH]; cbn [OrbitCycle.iter].
        - exact Hx.
        - apply f_closed_S'. exact IH. }
      assert (Hiter_S' : In (it n x) S') by exact (Hgen n).
      rewrite Hn in Hiter_S'.
      assert (same_orbit_b eqdec f S' x y = true)
        by (apply (same_orbit_b_complete eqdec f S' f_closed_S' f_inj_S' x Hx y); exists n; exact Hn).
      congruence.
  Qed.

  Lemma cycle_count_as_count_classes : forall (g : A -> A) (T : list A),
    cycle_count eqdec g T = count_classes (same_orbit_b eqdec g T) T.
  Proof. intros g T. unfold cycle_count, orbit_reps, count_classes. reflexivity. Qed.

  Lemma inO_complement_eq :
    count_classes (same_orbit_b eqdec f S') S'
    = count_classes (same_orbit_b eqdec f S) (filter (fun x => negb (inO x)) S).
  Proof.
    assert (HmemS' : forall z, In z S' -> In z S)
      by (intros z Hz; exact (proj1 (proj1 (Hcarrier z) Hz))).
    assert (HmemF : forall z, In z (filter (fun x => negb (inO x)) S) -> In z S)
      by (intros z Hz; apply filter_In in Hz; tauto).
    assert (Hiff : forall z, In z S' <-> In z (filter (fun x => negb (inO x)) S)).
    { intro z. split.
      - intro Hz. apply filter_In. split; [ exact (HmemS' z Hz) | ].
        apply (proj2 (filter_negb_inO_eq_S' z (HmemS' z Hz))). exact Hz.
      - intro Hz. apply filter_In in Hz. destruct Hz as [HzS Hzn].
        apply (proj1 (filter_negb_inO_eq_S' z HzS)). exact Hzn. }
    assert (Hswitch : count_classes (same_orbit_b eqdec f S') S'
                    = count_classes (same_orbit_b eqdec f S) S').
    { unfold count_classes. f_equal. apply class_reps_ext_on. intros x y Hx Hy.
      apply (same_orbit_b_S_S'_agree x y Hx Hy). }
    rewrite Hswitch.
    apply Nat.le_antisymm.
    - apply (class_reps_length_mono (same_orbit_b eqdec f S) (same_orbit_b_refl eqdec f S)
               S' (filter (fun x => negb (inO x)) S)).
      + intros x y Hx Hy. apply (same_orbit_b_sym_on eqdec f S Hclos Hinj x y (HmemF x Hx) (HmemF y Hy)).
      + intros x y z Hx Hy Hz.
        apply (same_orbit_b_trans_on eqdec f S Hclos Hinj x y z (HmemF x Hx) (HmemF y Hy) (HmemF z Hz)).
      + intros z Hz. exact (proj1 (Hiff z) Hz).
    - apply (class_reps_length_mono (same_orbit_b eqdec f S) (same_orbit_b_refl eqdec f S)
               (filter (fun x => negb (inO x)) S) S').
      + intros x y Hx Hy. apply (same_orbit_b_sym_on eqdec f S Hclos Hinj x y (HmemS' x Hx) (HmemS' y Hy)).
      + intros x y z Hx Hy Hz.
        apply (same_orbit_b_trans_on eqdec f S Hclos Hinj x y z (HmemS' x Hx) (HmemS' y Hy) (HmemS' z Hz)).
      + intros z Hz. exact (proj2 (Hiff z) Hz).
  Qed.

  (* THE ISOLATE: removing the self-contained 2-cycle drops the orbit count
     by exactly one. *)
  Theorem cycle_count_isolate : cycle_count eqdec f S' = (cycle_count eqdec f S - 1)%nat.
  Proof.
    assert (Htr : forall x y z, In x S -> In y S -> In z S ->
              same_orbit_b eqdec f S x y = true -> same_orbit_b eqdec f S y z = true ->
              same_orbit_b eqdec f S x z = true)
      by (intros x y z Hx Hy Hz; apply (same_orbit_b_trans_on eqdec f S Hclos Hinj x y z Hx Hy Hz)).
    assert (Hcc : forall x y, In x S -> In y S -> same_orbit_b eqdec f S x y = true -> inO x = inO y).
    { intros x y Hx Hy Hxy. unfold inO.
      destruct (same_orbit_b eqdec f S d x) eqn:Ex;
        destruct (same_orbit_b eqdec f S d y) eqn:Ey; try reflexivity; exfalso.
      - assert (same_orbit_b eqdec f S d y = true)
          by (apply (same_orbit_b_trans_on eqdec f S Hclos Hinj d x y HdS Hx Hy Ex Hxy)); congruence.
      - assert (same_orbit_b eqdec f S y x = true)
          by (apply (same_orbit_b_sym_on eqdec f S Hclos Hinj x y Hx Hy Hxy)).
        assert (same_orbit_b eqdec f S d x = true)
          by (apply (same_orbit_b_trans_on eqdec f S Hclos Hinj d y x HdS Hy Hx Ey H)); congruence. }
    rewrite (cycle_count_as_count_classes f S'), (cycle_count_as_count_classes f S).
    rewrite (count_classes_filter_split (same_orbit_b eqdec f S)
               (same_orbit_b_refl eqdec f S) inO S Hcc Htr).
    rewrite inO_block_eq_1, inO_complement_eq. lia.
  Qed.

End CycleIsolate.

(* -------------------------------------------------------------------------- *)
(* Axiom audit.  Thin instances of ClassCount; allowlist axioms only.          *)
(* -------------------------------------------------------------------------- *)

Print Assumptions cycle_count_isolate.

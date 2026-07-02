(* ==========================================================================
   EulerCoreInduction.v

   [EF-4 induction] Euler ladder: the degree->=2-core induction principle.

   Ties [EF-4]'s leaf-peeling transfers (`EulerFormula.
   euler_characteristic_leaf_edge_transfer` / `_tip`, `euler_characteristic_
   isolated_edge_transfer`) into a genuine induction: repeatedly peel a
   degree-1 vertex's edge until the graph is empty or every remaining vertex
   has degree >= 2.  This gives a strong, fully unconditional PARTIAL Euler
   result -- `euler_characteristic E <-> euler_characteristic E'` for some
   min-degree->=2 (or empty) `E'` reachable from `E` by peeling -- even
   though `euler_characteristic E'` itself, for the min-degree->=2 core,
   still needs the (currently Euler-gated) bridge/cycle dichotomy to go
   further (the same_face <-> cut-edge combinatorial-Jordan step, still
   open per the investigation in PR #319).

   Two standing invariants thread through every recursive step, both
   trivially preserved by `E_minus`:
     - `NoDup E`             (already needed by every [EF-4] transfer)
     - `no_twin_dup E`       (E stores each undirected edge ONCE -- neither
                              orientation is duplicated; needed here to get
                              `NoDup (darts_of E)`, hence `NoDup` on each
                              vertex's outgoing fan, which is what lets a
                              `vdeg >= 2` far endpoint be turned into BOTH
                              the `fstep _ <> _` non-reciprocal-leaf
                              condition and the vertex-survival condition
                              [EF-4]'s transfers need.)

   `MinDegreeCore.exists_leaf_or_min_degree2` finds a degree-1 vertex (or
   certifies none exists); `MinDegreeCore.next_neq_self_of_other` (the
   missing "no fixed point on a non-singleton fan" fact) is exactly what
   turns a `vdeg >= 2` far endpoint into the non-reciprocal-leaf condition,
   avoiding the global `no_spurs` the induction cannot assume (peeling one
   leaf can create new spurs elsewhere).

   Pure combinatorial wiring; no `Admitted` / `Axiom` / `Parameter`; allowlist
   axioms only.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
   ========================================================================== *)

From Stdlib Require Import List Arith Lia Wf_nat.
From NTS.Proofs Require Import Distance Overlay Dart DartNextSpec DartAngularOrder
                               DartFace EdgeConnectivity EdgeFaceBridge
                               ArrangementEMinus ReachableDec EulerArrangement
                               ClassCount MinDegreeCore EulerFormula.

Import ListNotations.

(* -------------------------------------------------------------------------- *)
(* §1  Standing invariant: E stores each undirected edge exactly once.        *)
(* -------------------------------------------------------------------------- *)

Definition no_twin_dup (E : list Edge) : Prop := forall e, In e E -> ~ In (twin e) E.

Lemma no_twin_dup_E_minus : forall E d, no_twin_dup E -> no_twin_dup (E_minus E d).
Proof.
  intros E d H e He Hc.
  apply (H e).
  - exact (proj1 (proj1 (in_E_minus E d e) He)).
  - exact (proj1 (proj1 (in_E_minus E d (twin e)) Hc)).
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  `darts_of E` is duplicate-free, given the two standing invariants.     *)
(* -------------------------------------------------------------------------- *)

Lemma NoDup_app_disjoint : forall {A : Type} (l1 l2 : list A),
  NoDup l1 -> NoDup l2 -> (forall x, In x l1 -> In x l2 -> False) -> NoDup (l1 ++ l2).
Proof.
  induction l1 as [| a l1 IH]; intros l2 H1 H2 Hdisj.
  - exact H2.
  - inversion H1 as [| ? ? Hnin Hnd Heq]; subst.
    cbn [app]. constructor.
    + intro Hin. apply in_app_or in Hin. destruct Hin as [Hin | Hin].
      * exact (Hnin Hin).
      * exact (Hdisj a (or_introl eq_refl) Hin).
    + apply IH; [ exact Hnd | exact H2 | intros x Hx; exact (Hdisj x (or_intror Hx)) ].
Qed.

Lemma darts_of_NoDup : forall E, NoDup E -> no_twin_dup E -> NoDup (darts_of E).
Proof.
  intros E Hnd Hntd. unfold darts_of.
  apply NoDup_app_disjoint.
  - exact Hnd.
  - apply (nodup_map_inj twin E Hnd). intros x y _ _ Hxy. exact (twin_inj x y Hxy).
  - intros x Hx Hy. apply in_map_iff in Hy. destruct Hy as [e' [Heq He']].
    apply (Hntd e' He'). rewrite Heq. exact Hx.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Vertex-vanishing, generalised from `EulerFormula.v`'s two internal      *)
(* derivations (base-is-leaf's `Ha`, tip-is-leaf's `Hb`) into standalone       *)
(* reusable lemmas.                                                          *)
(* -------------------------------------------------------------------------- *)

Lemma vertex_vanishes_via_leaf : forall E d,
  In d E -> ~ In (twin d) E -> outgoing (dbase d) (darts_of E) = [d] ->
  ~ In (dbase d) (verts (E_minus E d)).
Proof.
  intros E d HdE Hntwin Hleaf Hcontra.
  apply in_verts in Hcontra. destruct Hcontra as [e [He Hend]].
  destruct (proj1 (in_E_minus E d e) He) as [HeE Hene].
  destruct Hend as [Hf | Hs].
  - assert (HeD : In e (darts_of E)) by (apply in_darts_of_orig; exact HeE).
    assert (HeOut : In e (outgoing (dbase d) (darts_of E)))
      by (apply in_outgoing; split; [ exact HeD | exact Hf ]).
    rewrite Hleaf in HeOut. destruct HeOut as [Heq | []]. exact (Hene (eq_sym Heq)).
  - assert (HteD : In (twin e) (darts_of E)) by (apply in_darts_of_twin; exact HeE).
    assert (HteOut : In (twin e) (outgoing (dbase d) (darts_of E))).
    { apply in_outgoing. split; [ exact HteD | rewrite dbase_twin; exact Hs ]. }
    rewrite Hleaf in HteOut. destruct HteOut as [Heq | []].
    apply Hntwin. assert (Hte : twin d = e) by (rewrite Heq, twin_involutive; reflexivity).
    rewrite Hte. exact HeE.
Qed.

Lemma vertex_vanishes_via_leaf_tip : forall E d,
  In d E -> ~ In (twin d) E -> outgoing (dtip d) (darts_of E) = [twin d] ->
  ~ In (dtip d) (verts (E_minus E d)).
Proof.
  intros E d HdE Hntwin Hleaf Hcontra.
  apply in_verts in Hcontra. destruct Hcontra as [e [He Hend]].
  destruct (proj1 (in_E_minus E d e) He) as [HeE Hene].
  destruct Hend as [Hf | Hs].
  - assert (HeD : In e (darts_of E)) by (apply in_darts_of_orig; exact HeE).
    assert (HeOut : In e (outgoing (dtip d) (darts_of E)))
      by (apply in_outgoing; split; [ exact HeD | exact Hf ]).
    rewrite Hleaf in HeOut. destruct HeOut as [Heq | []].
    apply Hntwin. rewrite Heq. exact HeE.
  - assert (HteD : In (twin e) (darts_of E)) by (apply in_darts_of_twin; exact HeE).
    assert (HteOut : In (twin e) (outgoing (dtip d) (darts_of E))).
    { apply in_outgoing. split; [ exact HteD | rewrite dbase_twin; exact Hs ]. }
    rewrite Hleaf in HteOut. destruct HteOut as [Heq | []].
    apply twin_inj in Heq. exact (Hene (eq_sym Heq)).
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Turning a `vdeg >= 2` far endpoint into the non-reciprocal-leaf and    *)
(* survival conditions [EF-4]'s transfers need, via `next_neq_self_of_other`. *)
(* -------------------------------------------------------------------------- *)

Lemma list_other_elem_dart : forall (l : list Dart) (x : Dart),
  NoDup l -> In x l -> (2 <= length l)%nat -> exists y, In y l /\ y <> x.
Proof.
  intros l x Hnd Hx Hlen.
  destruct l as [| a l']; [ destruct Hx | ].
  destruct l' as [| b l'']; [ cbn in Hlen; lia | ].
  destruct (dart_eq_dec a x) as [-> | Hne].
  - exists b. split; [ right; left; reflexivity | ].
    inversion Hnd as [| ? ? Hnin _]; subst. intro Hc. apply Hnin. left. exact Hc.
  - exists a. split; [ left; reflexivity | exact Hne ].
Qed.

Lemma fstep_ne_twin_of_vdeg_ge2 : forall E e,
  (forall v : Point, fan_ok (outgoing v (darts_of E))) -> NoDup (darts_of E) ->
  In e (darts_of E) -> (2 <= vdeg (dtip e) (darts_of E))%nat ->
  fstep (darts_of E) e <> twin e.
Proof.
  intros E e Hfan Hnd HeD Hdeg.
  assert (Htw : In (twin e) (outgoing (dtip e) (darts_of E)))
    by (apply in_outgoing; split;
        [ apply darts_of_closed_under_twin; exact HeD | apply dbase_twin ]).
  assert (HndF : NoDup (outgoing (dtip e) (darts_of E))) by (apply NoDup_filter; exact Hnd).
  destruct (list_other_elem_dart (outgoing (dtip e) (darts_of E)) (twin e) HndF Htw Hdeg)
    as [y [Hy Hyne]].
  unfold fstep. exact (next_neq_self_of_other _ (twin e) y (Hfan (dtip e)) Htw Hy Hyne).
Qed.

Lemma fstep_twin_ne_of_vdeg_ge2 : forall E e,
  (forall v : Point, fan_ok (outgoing v (darts_of E))) -> NoDup (darts_of E) ->
  In e (darts_of E) -> (2 <= vdeg (dbase e) (darts_of E))%nat ->
  fstep (darts_of E) (twin e) <> e.
Proof.
  intros E e Hfan Hnd HeD Hdeg.
  assert (He_in : In e (outgoing (dbase e) (darts_of E)))
    by (apply in_outgoing; split; [ exact HeD | reflexivity ]).
  assert (HndF : NoDup (outgoing (dbase e) (darts_of E))) by (apply NoDup_filter; exact Hnd).
  destruct (list_other_elem_dart (outgoing (dbase e) (darts_of E)) e HndF He_in Hdeg)
    as [y [Hy Hyne]].
  unfold fstep. rewrite dtip_twin, twin_involutive.
  exact (next_neq_self_of_other _ e y (Hfan (dbase e)) He_in Hy Hyne).
Qed.

Lemma vertex_survives_via_far : forall E e,
  In e E -> ~ In (twin e) E -> fst e <> snd e -> NoDup (darts_of E) ->
  (2 <= vdeg (dtip e) (darts_of E))%nat ->
  In (dtip e) (verts (E_minus E e)).
Proof.
  intros E e HeE Hntwin Hproper Hnd Hdeg.
  assert (Htw : In (twin e) (outgoing (dtip e) (darts_of E)))
    by (apply in_outgoing; split;
        [ apply darts_of_closed_under_twin, in_darts_of_orig; exact HeE | apply dbase_twin ]).
  assert (HndF : NoDup (outgoing (dtip e) (darts_of E))) by (apply NoDup_filter; exact Hnd).
  destruct (list_other_elem_dart (outgoing (dtip e) (darts_of E)) (twin e) HndF Htw Hdeg)
    as [y [Hy Hyne]].
  destruct (proj1 (in_outgoing (dtip e) (darts_of E) y) Hy) as [HyD Hyw].
  destruct (dart_carrier_edge E y HyD) as [e' [He'E Hcase]].
  assert (He'ne : e' <> e).
  { intro Hc. subst e'. destruct Hcase as [Heq | Heq].
    - subst y. exact (Hproper Hyw).
    - assert (Hye : y = twin e) by (rewrite Heq, twin_involutive; reflexivity).
      exact (Hyne Hye). }
  apply in_verts. exists e'. split; [ apply in_E_minus; split; assumption | ].
  destruct Hcase as [Heq | Heq].
  - left. change (dbase e' = dtip e). rewrite Heq. exact Hyw.
  - right. change (dtip e' = dtip e). rewrite Heq, dtip_twin. exact Hyw.
Qed.

Lemma vertex_survives_via_far_tip : forall E e,
  In e E -> ~ In (twin e) E -> fst e <> snd e -> NoDup (darts_of E) ->
  (2 <= vdeg (dbase e) (darts_of E))%nat ->
  In (dbase e) (verts (E_minus E e)).
Proof.
  intros E e HeE Hntwin Hproper Hnd Hdeg.
  assert (He_in : In e (outgoing (dbase e) (darts_of E)))
    by (apply in_outgoing; split; [ apply in_darts_of_orig; exact HeE | reflexivity ]).
  assert (HndF : NoDup (outgoing (dbase e) (darts_of E))) by (apply NoDup_filter; exact Hnd).
  destruct (list_other_elem_dart (outgoing (dbase e) (darts_of E)) e HndF He_in Hdeg)
    as [y [Hy Hyne]].
  destruct (proj1 (in_outgoing (dbase e) (darts_of E) y) Hy) as [HyD Hyw].
  destruct (dart_carrier_edge E y HyD) as [e' [He'E Hcase]].
  assert (He'ne : e' <> e).
  { intro Hc. subst e'. destruct Hcase as [Heq | Heq].
    - exact (Hyne (eq_sym Heq)).
    - assert (Hye : y = twin e) by (rewrite Heq, twin_involutive; reflexivity).
      apply Hproper. rewrite Hye, dbase_twin in Hyw. symmetry. exact Hyw. }
  apply in_verts. exists e'. split; [ apply in_E_minus; split; assumption | ].
  destruct Hcase as [Heq | Heq].
  - left. change (dbase e' = dbase e). rewrite Heq. exact Hyw.
  - right. change (dtip e' = dbase e). rewrite Heq, dtip_twin. exact Hyw.
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  The single peeling step: find a leaf, dispatch to the correct one of   *)
(* the four [EF-4] transfers, and shrink strictly.                          *)
(* -------------------------------------------------------------------------- *)

Lemma euler_core_step : forall E,
  NoDup E -> no_twin_dup E -> (forall v : Point, fan_ok (outgoing v (darts_of E))) ->
  ~ min_degree_2 E ->
  exists d, In d E /\
    NoDup (E_minus E d) /\ no_twin_dup (E_minus E d) /\
    (forall v : Point, fan_ok (outgoing v (darts_of (E_minus E d)))) /\
    (length (E_minus E d) < length E)%nat /\
    (euler_characteristic E <-> euler_characteristic (E_minus E d)).
Proof.
  intros E Hnodup Hntd Hfan Hnmin.
  destruct (exists_leaf_or_min_degree2 E) as [[v [HvV Hv1]] | Hmin];
    [ | exfalso; exact (Hnmin Hmin) ].
  destruct (length_eq_1_singleton (outgoing v (darts_of E)) Hv1) as [d0 Hd0eq].
  assert (Hd0In : In d0 (outgoing v (darts_of E))) by (rewrite Hd0eq; left; reflexivity).
  destruct (proj1 (in_outgoing v (darts_of E) d0) Hd0In) as [Hd0D Hd0v].
  destruct (dart_carrier_edge E d0 Hd0D) as [e [HeE Hcase]].
  assert (Hntwin_e : ~ In (twin e) E) by exact (Hntd e HeE).
  assert (HeD : In e (darts_of E)) by (apply in_darts_of_orig; exact HeE).
  assert (HeND : NoDup (darts_of E)) by (apply darts_of_NoDup; assumption).
  assert (HbND : NoDup (E_minus E e)) by (unfold E_minus; apply NoDup_filter; exact Hnodup).
  assert (HbNTD : no_twin_dup (E_minus E e)) by (apply no_twin_dup_E_minus; exact Hntd).
  assert (HbFan : forall w0 : Point, fan_ok (outgoing w0 (darts_of (E_minus E e))))
    by (intro w0; apply fan_ok_E_minus; exact Hfan).
  assert (HbLen : (length (E_minus E e) < length E)%nat).
  { assert (Hcount : count_occ edge_eq_dec E e = 1%nat)
      by (apply count_occ_1_of_NoDup; assumption).
    pose proof (num_edges_E_minus E e Hcount) as HEd.
    change (num_edges (E_minus E e) < num_edges E)%nat.
    lia. }
  destruct Hcase as [Heq | Heq].
  - (* leaf at fst e (= dbase e) *)
    assert (Hleaf : outgoing (dbase e) (darts_of E) = [e])
      by (rewrite Heq, Hd0v; exact Hd0eq).
    assert (Hproper : fst e <> snd e).
    { intro Hc. apply Hntwin_e.
      assert (Hte : twin e = e) by (destruct e as [a b]; cbn in Hc; subst b; reflexivity).
      rewrite Hte. exact HeE. }
    destruct (Nat.eq_dec (vdeg (dtip e) (darts_of E)) 1) as [Hfar1 | Hfar2].
    + (* isolated K2 *)
      destruct (length_eq_1_singleton (outgoing (dtip e) (darts_of E)) Hfar1) as [d1 Hd1eq].
      assert (Htwe_in : In (twin e) (outgoing (dtip e) (darts_of E))).
      { apply in_outgoing. split.
        - apply darts_of_closed_under_twin, in_darts_of_orig; exact HeE.
        - apply dbase_twin. }
      assert (Hd1_eq : d1 = twin e)
        by (rewrite Hd1eq in Htwe_in; destruct Htwe_in as [Heqx | []]; exact Heqx).
      assert (Hleaf_b : outgoing (dtip e) (darts_of E) = [twin e])
        by (rewrite <- Hd1_eq; exact Hd1eq).
      exists e. split; [ exact HeE | split; [ exact HbND | split; [ exact HbNTD |
        split; [ exact HbFan | split; [ exact HbLen | ] ] ] ] ].
      apply (euler_characteristic_isolated_edge_transfer E e Hnodup Hfan HeE Hntwin_e Hproper
               Hleaf Hleaf_b
               (vertex_vanishes_via_leaf E e HeE Hntwin_e Hleaf)
               (vertex_vanishes_via_leaf_tip E e HeE Hntwin_e Hleaf_b)).
    + (* regular leaf: far endpoint (dtip e) has degree >= 2 *)
      assert (Hfarpos : (1 <= vdeg (dtip e) (darts_of E))%nat)
        by (apply vdeg_pos_of_in_verts; apply in_verts; exists e;
              split; [ exact HeE | right; reflexivity ]).
      assert (Hfarge2 : (2 <= vdeg (dtip e) (darts_of E))%nat) by lia.
      exists e. split; [ exact HeE | split; [ exact HbND | split; [ exact HbNTD |
        split; [ exact HbFan | split; [ exact HbLen | ] ] ] ] ].
      apply (euler_characteristic_leaf_edge_transfer E e Hnodup Hfan HeE Hntwin_e Hproper
               Hleaf (fstep_ne_twin_of_vdeg_ge2 E e Hfan HeND HeD Hfarge2)
               (vertex_survives_via_far E e HeE Hntwin_e Hproper HeND Hfarge2)).
  - (* leaf at snd e (= dtip e, via twin d0 = e) *)
    assert (Hd0_eq_twin_e : d0 = twin e) by (rewrite Heq, twin_involutive; reflexivity).
    assert (Hv_eq : v = dtip e).
    { rewrite <- Hd0v, Hd0_eq_twin_e. apply dbase_twin. }
    assert (Hleaf : outgoing (dtip e) (darts_of E) = [twin e]).
    { rewrite <- Hv_eq, <- Hd0_eq_twin_e. exact Hd0eq. }
    assert (Hproper : fst e <> snd e).
    { intro Hc. apply Hntwin_e.
      assert (Hte : twin e = e) by (destruct e as [a b]; cbn in Hc; subst b; reflexivity).
      rewrite Hte. exact HeE. }
    destruct (Nat.eq_dec (vdeg (dbase e) (darts_of E)) 1) as [Hfar1 | Hfar2].
    + (* isolated K2 *)
      destruct (length_eq_1_singleton (outgoing (dbase e) (darts_of E)) Hfar1) as [d1 Hd1eq].
      assert (He_in : In e (outgoing (dbase e) (darts_of E)))
        by (apply in_outgoing; split; [ apply in_darts_of_orig; exact HeE | reflexivity ]).
      assert (Hd1_eq : d1 = e)
        by (rewrite Hd1eq in He_in; destruct He_in as [Heqx | []]; exact Heqx).
      assert (Hleaf_a : outgoing (dbase e) (darts_of E) = [e])
        by (rewrite Hd1eq, Hd1_eq; reflexivity).
      exists e. split; [ exact HeE | split; [ exact HbND | split; [ exact HbNTD |
        split; [ exact HbFan | split; [ exact HbLen | ] ] ] ] ].
      apply (euler_characteristic_isolated_edge_transfer E e Hnodup Hfan HeE Hntwin_e Hproper
               Hleaf_a Hleaf
               (vertex_vanishes_via_leaf E e HeE Hntwin_e Hleaf_a)
               (vertex_vanishes_via_leaf_tip E e HeE Hntwin_e Hleaf)).
    + (* regular leaf: far endpoint (dbase e) has degree >= 2 *)
      assert (Hfarpos : (1 <= vdeg (dbase e) (darts_of E))%nat)
        by (apply vdeg_pos_of_in_verts; apply in_verts; exists e;
              split; [ exact HeE | left; reflexivity ]).
      assert (Hfarge2 : (2 <= vdeg (dbase e) (darts_of E))%nat) by lia.
      exists e. split; [ exact HeE | split; [ exact HbND | split; [ exact HbNTD |
        split; [ exact HbFan | split; [ exact HbLen | ] ] ] ] ].
      apply (euler_characteristic_leaf_edge_transfer_tip E e Hnodup Hfan HeE Hntwin_e Hproper
               Hleaf (fstep_twin_ne_of_vdeg_ge2 E e Hfan HeND HeD Hfarge2)
               (vertex_survives_via_far_tip E e HeE Hntwin_e Hproper HeND Hfarge2)).
Qed.

(* -------------------------------------------------------------------------- *)
(* §6  The induction, and the headline reduction theorem.                    *)
(* -------------------------------------------------------------------------- *)

Theorem euler_core_reduction : forall E,
  NoDup E -> no_twin_dup E -> (forall v : Point, fan_ok (outgoing v (darts_of E))) ->
  exists E', NoDup E' /\ no_twin_dup E' /\
    (forall v : Point, fan_ok (outgoing v (darts_of E'))) /\
    min_degree_2 E' /\
    (euler_characteristic E <-> euler_characteristic E').
Proof.
  assert (Hind : forall n E, length E = n ->
            NoDup E -> no_twin_dup E -> (forall v : Point, fan_ok (outgoing v (darts_of E))) ->
            exists E', NoDup E' /\ no_twin_dup E' /\
              (forall v : Point, fan_ok (outgoing v (darts_of E'))) /\
              min_degree_2 E' /\
              (euler_characteristic E <-> euler_characteristic E')).
  { induction n as [n IH] using lt_wf_ind.
    intros E Hn Hnodup Hntd Hfan.
    destruct (exists_leaf_or_min_degree2 E) as [[v [HvV Hv1]] | Hmin].
    - assert (Hnmin : ~ min_degree_2 E) by (intro Hmin'; specialize (Hmin' v HvV); lia).
      destruct (euler_core_step E Hnodup Hntd Hfan Hnmin)
        as [d [HdE [Hnd' [Hntd' [Hfan' [Hlt Heuler]]]]]].
      destruct (IH (length (E_minus E d)) ltac:(rewrite <- Hn; exact Hlt)
                  (E_minus E d) eq_refl Hnd' Hntd' Hfan')
        as [E' [Hnd'' [Hntd'' [Hfan'' [Hmin'' Heuler'']]]]].
      exists E'. split; [ exact Hnd'' | split; [ exact Hntd'' | split; [ exact Hfan'' |
        split; [ exact Hmin'' | ] ] ] ].
      rewrite Heuler. exact Heuler''.
    - exists E. split; [ exact Hnodup | split; [ exact Hntd | split; [ exact Hfan |
        split; [ exact Hmin | split; intro H; exact H ] ] ] ]. }
  intros E Hnodup Hntd Hfan.
  exact (Hind (length E) E eq_refl Hnodup Hntd Hfan).
Qed.

(* -------------------------------------------------------------------------- *)
(* Axiom audit.  Combinatorial wiring; allowlist axioms only.                  *)
(* -------------------------------------------------------------------------- *)

Print Assumptions euler_core_reduction.

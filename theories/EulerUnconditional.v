(* ==========================================================================
   EulerUnconditional.v

   [H-bridge / Euler campaign, rung E-3b] THE PLANAR EULER IDENTITY IS
   UNCONDITIONAL: for any duplicate-free, twin-duplicate-free
   arrangement with well-formed vertex fans, under the four E-level
   geometric/noding guards,

       V + F = E + 2C            (`euler_characteristic E`)

   holds outright -- the identity `extract_rings_valid` and the whole
   overlay stack carried as a NAMED HYPOTHESIS is now a THEOREM.

   THE INDUCTION (breaking EulerFormula.v's circularity for good):
     1. `euler_core_reduction_incl`: peel leaf / isolated-K2 edges to a
        min-degree->=2 core, REMEMBERING that the core is an iterated
        `E_minus` (so `incl E' E`, and the length never grows) -- the
        same well-founded recursion as the banked
        `euler_core_reduction`, replayed over the exported
        `euler_core_step` with the two extra invariants threaded;
     2. the geometric guards restrict along `incl` (they are pointwise
        properties of the dart set -- §1);
     3. on the core: if empty, `euler_characteristic_nil`; otherwise
        delete its head edge by E-3a's SAME-FACE DISPATCH step
        (`euler_characteristic_core_edge_transfer`, whose bridge branch
        consumes the Euler-FREE `H_bridge_premise_holds`) and recurse
        on the strictly smaller remainder.

   Nothing here is hypothetical: every branch of every rung from the
   dart-order kernel through the JCT parity machinery to the walk
   residual is Qed, and the axiom footprint is the corpus allowlist
   trio.

   No `Admitted` / `Axiom` / `Parameter`; allowlist axioms only.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
   ========================================================================== *)

From Stdlib Require Import Reals List Arith Lia Bool Wf_nat.
From NTS.Proofs Require Import Distance Overlay OverlayGraph EdgeConnectivity
                               Dart DartNext DartNextSpec DartFace
                               NoShortFaces FaceChain ExtractFaces
                               FaceOrbitSep EdgeFaceBridge MinDegreeCore
                               EulerArrangement MapCounts ReachableDec
                               EulerBridge ClassCount ArrangementEMinus
                               EulerCoreInduction NumFacesSplice
                               NumFacesMerge EulerFormula FaceTwinAware
                               HBridgeCoreSlice WalkPremiseBridge
                               WalkResidualDischarge EulerSameFaceStep.

Import ListNotations.

(* -------------------------------------------------------------------------- *)
(* §1  The geometric guards restrict along dart-set inclusion.                 *)
(* -------------------------------------------------------------------------- *)

Lemma darts_of_incl :
  forall E' E : list Edge, incl E' E -> incl (darts_of E') (darts_of E).
Proof.
  intros E' E Hincl x Hx.
  unfold darts_of in Hx. apply in_app_or in Hx. destruct Hx as [Hx | Hx].
  - apply in_darts_of_orig. apply Hincl. exact Hx.
  - apply in_map_iff in Hx. destruct Hx as [e [Heq He]]. subst x.
    apply in_darts_of_twin. apply Hincl. exact He.
Qed.

Lemma pairwise_no_proper_cross_twin_aware_incl :
  forall D' D : list Dart,
    incl D' D ->
    pairwise_no_proper_cross_twin_aware D ->
    pairwise_no_proper_cross_twin_aware D'.
Proof.
  intros D' D Hincl H d1 d2 H1 H2 Hne Hnt.
  exact (H d1 d2 (Hincl _ H1) (Hincl _ H2) Hne Hnt).
Qed.

Lemma no_horizontal_darts_incl :
  forall D' D : list Dart,
    incl D' D -> no_horizontal_darts D -> no_horizontal_darts D'.
Proof.
  intros D' D Hincl H x Hx. exact (H x (Hincl _ Hx)).
Qed.

Lemma no_foreign_vertex_twin_aware_incl :
  forall D' D : list Dart,
    incl D' D ->
    no_foreign_vertex_twin_aware D ->
    no_foreign_vertex_twin_aware D'.
Proof.
  intros D' D Hincl H e f He Hf Hne Hnt.
  exact (H e f (Hincl _ He) (Hincl _ Hf) Hne Hnt).
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  The core reduction, remembering the core is a sub-arrangement.          *)
(* -------------------------------------------------------------------------- *)

Theorem euler_core_reduction_incl : forall E,
  NoDup E -> no_twin_dup E ->
  (forall v : Point, fan_ok (outgoing v (darts_of E))) ->
  exists E', NoDup E' /\ no_twin_dup E' /\
    (forall v : Point, fan_ok (outgoing v (darts_of E'))) /\
    min_degree_2 E' /\
    incl E' E /\
    (length E' <= length E)%nat /\
    (euler_characteristic E <-> euler_characteristic E').
Proof.
  assert (Hind : forall n E, length E = n ->
            NoDup E -> no_twin_dup E ->
            (forall v : Point, fan_ok (outgoing v (darts_of E))) ->
            exists E', NoDup E' /\ no_twin_dup E' /\
              (forall v : Point, fan_ok (outgoing v (darts_of E'))) /\
              min_degree_2 E' /\
              incl E' E /\
              (length E' <= length E)%nat /\
              (euler_characteristic E <-> euler_characteristic E')).
  { induction n as [n IH] using lt_wf_ind.
    intros E Hn Hnodup Hntd Hfan.
    destruct (exists_leaf_or_min_degree2 E) as [[v [HvV Hv1]] | Hmin].
    - assert (Hnmin : ~ min_degree_2 E)
        by (intro Hmin'; specialize (Hmin' v HvV); lia).
      destruct (euler_core_step E Hnodup Hntd Hfan Hnmin)
        as [d [HdE [Hnd' [Hntd' [Hfan' [Hlt Heuler]]]]]].
      destruct (IH (length (E_minus E d)) ltac:(rewrite <- Hn; exact Hlt)
                  (E_minus E d) eq_refl Hnd' Hntd' Hfan')
        as [E' [Hnd'' [Hntd'' [Hfan'' [Hmin'' [Hincl'' [Hlen'' Heuler'']]]]]]].
      exists E'.
      split; [ exact Hnd'' | split; [ exact Hntd'' | split; [ exact Hfan'' |
        split; [ exact Hmin'' | split; [ | split ] ] ] ] ].
      + intros x Hx. exact (E_minus_incl E d x (Hincl'' x Hx)).
      + lia.
      + rewrite Heuler. exact Heuler''.
    - exists E.
      split; [ exact Hnodup | split; [ exact Hntd | split; [ exact Hfan |
        split; [ exact Hmin | split; [ apply incl_refl | split;
        [ lia | split; intro H; exact H ] ] ] ] ] ]. }
  intros E Hnodup Hntd Hfan.
  exact (Hind (length E) E eq_refl Hnodup Hntd Hfan).
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Headline: the planar Euler identity, unconditional.                     *)
(* -------------------------------------------------------------------------- *)

Theorem euler_characteristic_holds :
  forall E : list Edge,
    NoDup E -> no_twin_dup E ->
    (forall v : Point, fan_ok (outgoing v (darts_of E))) ->
    pairwise_no_proper_cross_twin_aware (darts_of E) ->
    no_horizontal_darts (darts_of E) ->
    no_foreign_vertex_twin_aware (darts_of E) ->
    euler_characteristic E.
Proof.
  assert (Hind : forall n E, length E = n ->
            NoDup E -> no_twin_dup E ->
            (forall v : Point, fan_ok (outgoing v (darts_of E))) ->
            pairwise_no_proper_cross_twin_aware (darts_of E) ->
            no_horizontal_darts (darts_of E) ->
            no_foreign_vertex_twin_aware (darts_of E) ->
            euler_characteristic E).
  { induction n as [n IH] using lt_wf_ind.
    intros E Hn Hnd Hntd Hfan Hpw Hnh Hnfv.
    destruct (euler_core_reduction_incl E Hnd Hntd Hfan)
      as [E' [Hnd' [Hntd' [Hfan' [Hmin' [Hincl [Hlen Hiff]]]]]]].
    apply (proj2 Hiff).
    assert (Hdincl : incl (darts_of E') (darts_of E))
      by (apply darts_of_incl; exact Hincl).
    assert (Hpw' : pairwise_no_proper_cross_twin_aware (darts_of E'))
      by (exact (pairwise_no_proper_cross_twin_aware_incl _ _ Hdincl Hpw)).
    assert (Hnh' : no_horizontal_darts (darts_of E'))
      by (exact (no_horizontal_darts_incl _ _ Hdincl Hnh)).
    assert (Hnfv' : no_foreign_vertex_twin_aware (darts_of E'))
      by (exact (no_foreign_vertex_twin_aware_incl _ _ Hdincl Hnfv)).
    destruct E' as [| d0 E''].
    - exact euler_characteristic_nil.
    - (* delete the head edge of the core by the same-face dispatch *)
      pose proof (euler_characteristic_core_edge_transfer (d0 :: E'') d0
                    Hnd' Hntd' Hfan' Hmin' Hpw' Hnh' Hnfv'
                    (or_introl eq_refl)) as Hstep.
      apply (proj2 Hstep).
      set (Ed := E_minus (d0 :: E'') d0).
      assert (Hcnt : count_occ edge_eq_dec (d0 :: E'') d0 = 1%nat)
        by (apply count_occ_1_of_NoDup; [ exact Hnd' | left; reflexivity ]).
      pose proof (num_edges_E_minus (d0 :: E'') d0 Hcnt) as Hlen'.
      assert (Hlt : (length Ed < length (d0 :: E''))%nat).
      { change ((num_edges Ed < num_edges (d0 :: E''))%nat). unfold Ed. lia. }
      assert (HdinclEd : incl (darts_of Ed) (darts_of E)).
      { intros x Hx. apply Hdincl.
        apply (darts_of_incl Ed (d0 :: E'')); [ | exact Hx ].
        intros y Hy. exact (E_minus_incl (d0 :: E'') d0 y Hy). }
      apply (IH (length Ed)).
      + lia.
      + reflexivity.
      + unfold Ed, E_minus. apply NoDup_filter. exact Hnd'.
      + apply no_twin_dup_E_minus. exact Hntd'.
      + intro v. apply fan_ok_E_minus. exact Hfan'.
      + exact (pairwise_no_proper_cross_twin_aware_incl _ _ HdinclEd Hpw).
      + exact (no_horizontal_darts_incl _ _ HdinclEd Hnh).
      + exact (no_foreign_vertex_twin_aware_incl _ _ HdinclEd Hnfv). }
  intros E Hnd Hntd Hfan Hpw Hnh Hnfv.
  exact (Hind (length E) E eq_refl Hnd Hntd Hfan Hpw Hnh Hnfv).
Qed.

(* -------------------------------------------------------------------------- *)
(* Axiom audit.  The unconditional Euler identity; allowlist axioms only.      *)
(* -------------------------------------------------------------------------- *)

Print Assumptions euler_core_reduction_incl.
Print Assumptions euler_characteristic_holds.

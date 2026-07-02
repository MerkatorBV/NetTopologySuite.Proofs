(* ==========================================================================
   NumFacesIsolate.v

   [EF-4 induction] Euler ladder: cycle-count ISOLATE, the INSTANTIATION.

   Fourth (and simplest) member of the `num_faces_E_minus_*` family, alongside
   `NumFacesSplice.v` (SPLIT, +1), `NumFacesMerge.v` (MERGE, -1), and
   `NumFacesShrink.v` (SHRINK, 0): deleting an ISOLATED K2 edge -- BOTH
   endpoints degree-1 -- drops the face count by exactly one.

   `PermCycleIsolate.cycle_count_isolate` is the generic fact: removing a
   self-contained 2-cycle `{d, td}` (`f d = td`, `f td = d`) drops the orbit
   count by exactly one, with NO cross-wiring redirect (`f' = f`
   unchanged), since nothing else in the carrier maps into `{d, td}`.

   Here we instantiate it at the face-step permutation for an edge `d` whose
   BOTH endpoints are degree-1: `EulerWitness.fstep_of_singleton_fan` gives
   both spurs directly (`fstep (darts_of E) d = twin d` from the tip's
   singleton fan, `fstep (darts_of E) (twin d) = d` from the base's). The
   `Hf'spec` step needs NO case split at all (unlike `NumFacesSplice.v`'s
   redirect formula): `ArrangementEMinus.fstep_E_minus_eq_away` applies
   UNIFORMLY to every surviving dart, because a surviving dart can never tip
   into `dbase d` or `dtip d` -- both vertices' WHOLE fan was exactly `{d}`/
   `{twin d}` respectively, so the only darts that could tip there are `twin
   d`/`d` themselves, both removed.

   Pure combinatorial wiring; no `Admitted` / `Axiom` / `Parameter`; allowlist
   axioms only.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
   ========================================================================== *)

From Stdlib Require Import List Arith Lia.
From NTS.Proofs Require Import Distance Overlay Dart DartNextSpec DartAngularOrder
                               DartNextSpec DartFace FaceOrbitSep NoShortFaces
                               ExtractFaces EdgeConnectivity EdgeFaceBridge
                               ArrangementEMinus FaceStepRemove MapCounts
                               EulerWitness
                               OrbitCycle PermCycleCount PermCycleIsolate.

Import ListNotations.

(* A surviving dart can never tip into either endpoint of the removed
   isolated edge -- both vertices' whole fan collapses to the removed pair. *)
Lemma isolate_survivor_tip_ne : forall E d x,
  In d E -> ~ In (twin d) E ->
  outgoing (dbase d) (darts_of E) = [d] ->
  outgoing (dtip d) (darts_of E) = [twin d] ->
  In x (darts_of (E_minus E d)) ->
  dtip x <> dbase d /\ dtip x <> dtip d.
Proof.
  intros E d x HdE Hntwin Hleaf_a Hleaf_b Hx.
  assert (HxE : In x (darts_of E)) by (apply (incl_darts_of_E_minus E d); exact Hx).
  assert (HtwxE : In (twin x) (darts_of E)) by (apply darts_of_closed_under_twin; exact HxE).
  destruct (proj1 (in_darts_of_E_minus_iff E d x Hntwin) Hx) as [_ [Hxne_d Hxne_td]].
  split.
  - intro Heq.
    assert (HtwOut : In (twin x) (outgoing (dbase d) (darts_of E)))
      by (apply in_outgoing; split; [ exact HtwxE | rewrite dbase_twin; exact Heq ]).
    rewrite Hleaf_a in HtwOut. destruct HtwOut as [Htw | []].
    assert (Ht : twin d = x) by (rewrite Htw; apply twin_involutive).
    exact (Hxne_td (eq_sym Ht)).
  - intro Heq.
    assert (HtwOut : In (twin x) (outgoing (dtip d) (darts_of E)))
      by (apply in_outgoing; split; [ exact HtwxE | rewrite dbase_twin; exact Heq ]).
    rewrite Hleaf_b in HtwOut. destruct HtwOut as [Htw | []].
    apply twin_inj in Htw. exact (Hxne_d (eq_sym Htw)).
Qed.

(* Deleting an isolated K2 edge (both endpoints degree-1) drops the face
   count by exactly one. *)
Lemma num_faces_E_minus_isolate : forall (E : list Edge) (d : Dart),
  (forall v : Point, fan_ok (outgoing v (darts_of E))) ->
  In d E -> ~ In (twin d) E ->
  dbase d <> dtip d ->
  outgoing (dbase d) (darts_of E) = [d] ->
  outgoing (dtip d) (darts_of E) = [twin d] ->
  num_faces (E_minus E d) = (num_faces E - 1)%nat.
Proof.
  intros E d Hfan HdE Hntwin Hproper Hleaf_a Hleaf_b.
  assert (Hao : arrangement_ok (darts_of E))
    by (split; [ exact (darts_of_closed_under_twin E) | exact Hfan ]).
  assert (HdS : In d (darts_of E))
    by (unfold darts_of; apply in_or_app; left; exact HdE).
  assert (Htwin_in : In (twin d) (darts_of E))
    by (apply darts_of_closed_under_twin; exact HdS).
  assert (Hdtd : twin d <> d) by (apply twin_neq_self; exact Hproper).
  (* Both spurs, directly from the two singleton fans. *)
  assert (Hf_d_td : fstep (darts_of E) d = twin d)
    by (apply (fstep_of_singleton_fan E d); exact Hleaf_b).
  assert (Hf_td_d : fstep (darts_of E) (twin d) = d).
  { pose proof (fstep_of_singleton_fan E (twin d)) as Hgen.
    rewrite dtip_twin, twin_involutive in Hgen.
    apply Hgen. exact Hleaf_a. }
  (* SpliceSpec hypotheses for the (f,S) side. *)
  assert (Hclos : forall x, In x (darts_of E) -> In (fstep (darts_of E) x) (darts_of E))
    by (intros x Hx; exact (fstep_in (darts_of E) x (darts_of_closed_under_twin E) Hx)).
  assert (Hinj : forall a b, In a (darts_of E) -> In b (darts_of E) ->
                   fstep (darts_of E) a = fstep (darts_of E) b -> a = b)
    by (exact (fstep_inj (darts_of E) Hao)).
  (* SpliceSpec hypotheses for the (f',S') side. *)
  assert (Hao' : arrangement_ok (darts_of (E_minus E d)))
    by (apply arrangement_ok_E_minus; exact Hfan).
  assert (Hcarrier : forall x, In x (darts_of (E_minus E d)) <->
                       (In x (darts_of E) /\ x <> d /\ x <> twin d))
    by (intro x; exact (in_darts_of_E_minus_iff E d x Hntwin)).
  assert (Hclos' : forall x, In x (darts_of (E_minus E d)) ->
                     In (fstep (darts_of (E_minus E d)) x) (darts_of (E_minus E d)))
    by (intros x Hx; exact (fstep_in (darts_of (E_minus E d)) x (proj1 Hao') Hx)).
  assert (Hinj' : forall a b, In a (darts_of (E_minus E d)) -> In b (darts_of (E_minus E d)) ->
                    fstep (darts_of (E_minus E d)) a = fstep (darts_of (E_minus E d)) b -> a = b)
    by (exact (fstep_inj (darts_of (E_minus E d)) Hao')).
  assert (Hf'spec : forall x, In x (darts_of (E_minus E d)) ->
            fstep (darts_of (E_minus E d)) x = fstep (darts_of E) x).
  { intros x Hx.
    destruct (isolate_survivor_tip_ne E d x HdE Hntwin Hleaf_a Hleaf_b Hx) as [Hne_a Hne_b].
    exact (fstep_E_minus_eq_away E d x Hne_a Hne_b). }
  (* Apply the generic capstone, bridging `f' = f` (equal VALUES on the
     surviving darts, not a literal identity of the two `fstep` functions). *)
  unfold num_faces.
  rewrite (cycle_count_ext_f dart_eq_dec (fstep (darts_of (E_minus E d))) (fstep (darts_of E))
             (darts_of (E_minus E d)) Hclos' Hf'spec).
  exact (cycle_count_isolate dart_eq_dec (fstep (darts_of E)) (darts_of E)
           Hclos Hinj d (twin d) HdS Htwin_in Hf_d_td Hf_td_d
           (darts_of (E_minus E d)) Hcarrier).
Qed.

(* -------------------------------------------------------------------------- *)
(* Axiom audit.  Combinatorial wiring; allowlist axioms only.                  *)
(* -------------------------------------------------------------------------- *)

Print Assumptions num_faces_E_minus_isolate.

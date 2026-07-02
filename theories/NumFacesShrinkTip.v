(* ==========================================================================
   NumFacesShrinkTip.v

   [EF-4 induction] Euler ladder: cycle-count SHRINK, the TIP-IS-LEAF mirror.

   `NumFacesShrink.num_faces_E_minus_shrink` requires the leaf vertex to be
   `dbase d` -- the BASE of the E-stored dart `d`.  `E_minus E e` only ever
   removes the LITERAL stored value `e`, so `E_minus E d <> E_minus E (twin d)`
   in general (the latter is just `E` again, since `~ In (twin d) E`): there
   is no way to reuse `num_faces_E_minus_shrink` when the leaf happens to sit
   at `dtip d` instead by simply swapping arguments.  This file supplies the
   missing mirror, needed so the degree->=2-core induction can peel a leaf
   REGARDLESS of which orientation `E` happened to store its edge in.

   The generic engine (`PermCycleShrink.cycle_count_shrink`) is orientation-
   agnostic -- only the roles of "generic d" / "generic td" swap: here
   `f d = twin d` directly (`EulerWitness.fstep_of_singleton_fan` applies to
   `d` itself, no rewriting needed, unlike the base-is-leaf case), so
   generic-d := `d`, generic-td := `twin d` (the reverse assignment from
   `NumFacesShrink.v`).  The period bound and the `Hf'spec` redirect are
   otherwise identical modulo the `dbase`/`dtip` swap.

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
                               OrbitCycle PermCycleCount PermCycleShrink.

Import ListNotations.

(* Deleting a leaf edge whose leaf sits at `dtip d` (the mirror of
   `NumFacesShrink.num_faces_E_minus_shrink`, whose leaf sits at `dbase d`)
   leaves the face count UNCHANGED. *)
Lemma num_faces_E_minus_shrink_tip : forall (E : list Edge) (d : Dart),
  (forall v : Point, fan_ok (outgoing v (darts_of E))) ->
  In d E -> ~ In (twin d) E ->
  dbase d <> dtip d ->
  outgoing (dtip d) (darts_of E) = [twin d] ->
  fstep (darts_of E) (twin d) <> d ->
  num_faces (E_minus E d) = num_faces E.
Proof.
  intros E d Hfan HdE Hntwin Hproper Hleaf Hnotrecip.
  assert (Hao : arrangement_ok (darts_of E))
    by (split; [ exact (darts_of_closed_under_twin E) | exact Hfan ]).
  assert (HdS : In d (darts_of E))
    by (unfold darts_of; apply in_or_app; left; exact HdE).
  assert (Htwin_in : In (twin d) (darts_of E))
    by (apply darts_of_closed_under_twin; exact HdS).
  assert (Hdtd : d <> twin d) by (intro Heq; apply (twin_neq_self d Hproper); symmetry; exact Heq).
  (* The spur: the leaf's own fan forces fstep d = twin d, directly. *)
  assert (Hspur : fstep (darts_of E) d = twin d)
    by (apply (fstep_of_singleton_fan E d); exact Hleaf).
  (* Period of the (shared) face orbit, taken at `d`. *)
  destruct (face_period_spec (darts_of E) Hao d HdS) as [Hper_pos Hper_ret].
  assert (Hper_min : forall j, (1 <= j < face_period (darts_of E) d)%nat ->
                       OrbitCycle.iter (fstep (darts_of E)) j d <> d)
    by (intros j Hj; exact (face_period_no_early_return (darts_of E) d j Hao HdS Hj)).
  assert (Hper_ne1 : face_period (darts_of E) d <> 1%nat).
  { intro Heq. rewrite Heq in Hper_ret. cbn [OrbitCycle.iter] in Hper_ret.
    apply Hdtd. transitivity (fstep (darts_of E) d); [ symmetry; exact Hper_ret | exact Hspur ]. }
  assert (Hper_ne2 : face_period (darts_of E) d <> 2%nat).
  { intro Heq. rewrite Heq in Hper_ret. cbn [OrbitCycle.iter] in Hper_ret.
    rewrite Hspur in Hper_ret. apply Hnotrecip. exact Hper_ret. }
  assert (Hper_ge3 : (3 <= face_period (darts_of E) d)%nat) by lia.
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
                       (In x (darts_of E) /\ x <> d /\ x <> twin d)).
  { intro x. exact (in_darts_of_E_minus_iff E d x Hntwin). }
  assert (Hclos' : forall x, In x (darts_of (E_minus E d)) ->
                     In (fstep (darts_of (E_minus E d)) x) (darts_of (E_minus E d)))
    by (intros x Hx; exact (fstep_in (darts_of (E_minus E d)) x (proj1 Hao') Hx)).
  assert (Hinj' : forall a b, In a (darts_of (E_minus E d)) -> In b (darts_of (E_minus E d)) ->
                    fstep (darts_of (E_minus E d)) a = fstep (darts_of (E_minus E d)) b -> a = b)
    by (exact (fstep_inj (darts_of (E_minus E d)) Hao')).
  assert (Hf'spec : forall x, In x (darts_of (E_minus E d)) ->
            fstep (darts_of (E_minus E d)) x =
              (if dart_eq_dec (fstep (darts_of E) x) d then fstep (darts_of E) (twin d)
               else if dart_eq_dec (fstep (darts_of E) x) (twin d) then fstep (darts_of E) d
               else fstep (darts_of E) x)).
  { intros x Hx. exact (fstep_E_minus_splice E d x Hfan HdE Hntwin Hproper Hx). }
  (* Apply the generic capstone: generic-d := d, generic-td := twin d
     (the REVERSE assignment from NumFacesShrink.v). *)
  unfold num_faces.
  exact (cycle_count_shrink dart_eq_dec (fstep (darts_of E)) (darts_of E)
           Hclos Hinj d (twin d) HdS Hspur
           (face_period (darts_of E) d) Hper_ret Hper_ge3 Hper_min
           (fstep (darts_of (E_minus E d))) (darts_of (E_minus E d))
           Hcarrier Hclos' Hinj' Hf'spec).
Qed.

(* -------------------------------------------------------------------------- *)
(* Axiom audit.  Combinatorial wiring; allowlist axioms only.                  *)
(* -------------------------------------------------------------------------- *)

Print Assumptions num_faces_E_minus_shrink_tip.

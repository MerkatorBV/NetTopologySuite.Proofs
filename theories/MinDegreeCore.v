(* ==========================================================================
   MinDegreeCore.v

   [EF-4 induction] Euler ladder: degree infrastructure for the degree->=2-core
   induction principle.

   `EulerFormula.euler_characteristic_leaf_edge_transfer` ([EF-4], PRs
   #316-#318) proves that peeling a degree-1 vertex's unique edge preserves
   `euler_characteristic`, UNCONDITIONALLY.  To actually RUN an induction that
   repeatedly peels leaves down to a min-degree->=2 core, we first need to be
   able to FIND a leaf (or certify there is none).  `VertexDegree.v` proves
   the min-degree-2 CONSEQUENCE of `no_spurs` but never names a numeric
   degree; `Dart.v:159`'s `vdeg` is exactly that numeric degree but has never
   been used.  This file supplies:

     - `next_neq_self_of_other` : the missing "no fixed point on a
       non-singleton fan" fact (`fan_ok F` + some OTHER element of `F` =>
       `next F d <> d`).  Needed because the induction cannot assume global
       `no_spurs` (peeling one leaf can create new spurs elsewhere), so the
       degree-based case-split cannot route through `NoShortFaces.no_spurs`
       the way `VertexDegree.v` does; it must derive the fact straight from
       `fan_ok`'s total order (`next_min_successor` / `next_wrap_least`),
       which no_spurs itself is built from.
     - `length_eq_1_singleton` : a generic length-1-list extraction helper.
     - `min_degree_2` : the named predicate `VertexDegree.v` never defined.
     - `exists_leaf_or_min_degree2` : the case-split the induction dispatches
       on -- either some vertex has degree exactly 1 (with its unique dart
       extracted), or the whole graph is already min-degree->=2.

   Pure dart + list combinatorics; no `Admitted` / `Axiom` / `Parameter`;
   allowlist axioms only.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
   ========================================================================== *)

From Stdlib Require Import List Arith Lia.
From NTS.Proofs Require Import Distance Overlay Dart DartAngularOrder DartNext
                               DartNextSpec DartFace EdgeConnectivity ReachableDec.

Import ListNotations.

(* -------------------------------------------------------------------------- *)
(* §1  `next` has no fixed point once another fan element exists.              *)
(* -------------------------------------------------------------------------- *)

Lemma next_neq_self_of_other : forall F d y,
  fan_ok F -> In d F -> In y F -> y <> d -> next F d <> d.
Proof.
  intros F d y HF Hd Hy Hyd Heq.
  destruct (existsb (fun e => dart_ltb d e) F) eqn:Hex.
  - apply existsb_exists in Hex. destruct Hex as [e [HeF Hlt]].
    apply dart_ltb_spec in Hlt.
    destruct (next_min_successor F d HF (ex_intro _ e (conj HeF Hlt))) as [_ [Hlt2 _]].
    rewrite Heq in Hlt2. exact (dart_lt_irrefl d Hlt2).
  - assert (Hmax : forall e, In e F -> ~ dart_lt d e).
    { intros e HeF Hcontra.
      assert (Htrue : existsb (fun e => dart_ltb d e) F = true).
      { apply existsb_exists. exists e. split; [ exact HeF | apply dart_ltb_spec; exact Hcontra ]. }
      rewrite Htrue in Hex. discriminate. }
    destruct (next_wrap_least F d HF Hd Hmax y Hy) as [Heqy | Hlty].
    + rewrite Heq in Heqy. exact (Hyd (eq_sym Heqy)).
    + rewrite Heq in Hlty. exact (Hmax y Hy Hlty).
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  A length-1 list is a singleton.                                         *)
(* -------------------------------------------------------------------------- *)

Lemma length_eq_1_singleton : forall {A : Type} (l : list A),
  length l = 1%nat -> exists x, l = [x].
Proof.
  intros A l Hl. destruct l as [| x [| y l']]; cbn [length] in Hl; try lia.
  exists x. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Every vertex of `E` has positive degree.                                *)
(* -------------------------------------------------------------------------- *)

Lemma In_length_pos : forall {A : Type} (x : A) (l : list A), In x l -> (1 <= length l)%nat.
Proof. intros A x l Hx. destruct l as [| y l']; [ destruct Hx | cbn [length]; lia ]. Qed.

Lemma vdeg_pos_of_in_verts : forall E v,
  In v (verts E) -> (1 <= vdeg v (darts_of E))%nat.
Proof.
  intros E v Hv. apply in_verts in Hv. destruct Hv as [e [He Hor]].
  unfold vdeg.
  destruct Hor as [Hf | Hs].
  - apply (In_length_pos e). apply in_outgoing.
    split; [ apply in_darts_of_orig; exact He | unfold dbase; exact Hf ].
  - apply (In_length_pos (twin e)). apply in_outgoing.
    split; [ apply in_darts_of_twin; exact He | rewrite dbase_twin; unfold dtip; exact Hs ].
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  The min-degree-2 predicate and the leaf-or-min-degree-2 case split.     *)
(* -------------------------------------------------------------------------- *)

Definition min_degree_2 (E : list Edge) : Prop :=
  forall v, In v (verts E) -> (2 <= vdeg v (darts_of E))%nat.

Lemma exists_leaf_or_min_degree2_on : forall E vs,
  (forall v, In v vs -> In v (verts E)) ->
  (exists v, In v vs /\ vdeg v (darts_of E) = 1%nat) \/
  (forall v, In v vs -> (2 <= vdeg v (darts_of E))%nat).
Proof.
  intros E vs. induction vs as [| v vs IH]; intro Hsub.
  - right. intros v [].
  - destruct (IH (fun v' Hv' => Hsub v' (or_intror Hv'))) as [[v' [Hv'in Hv'eq]] | Hmin].
    + left. exists v'. split; [ right; exact Hv'in | exact Hv'eq ].
    + assert (Hvpos : (1 <= vdeg v (darts_of E))%nat)
        by (apply vdeg_pos_of_in_verts, Hsub; left; reflexivity).
      destruct (Nat.eq_dec (vdeg v (darts_of E)) 1) as [Heq1 | Hneq1].
      * left. exists v. split; [ left; reflexivity | exact Heq1 ].
      * right. intros v0 [-> | Hv0]; [ lia | apply Hmin; exact Hv0 ].
Qed.

Theorem exists_leaf_or_min_degree2 : forall E,
  (exists v, In v (verts E) /\ vdeg v (darts_of E) = 1%nat) \/ min_degree_2 E.
Proof.
  intro E. apply exists_leaf_or_min_degree2_on. auto.
Qed.

(* -------------------------------------------------------------------------- *)
(* Axiom audit.  Pure dart + list combinatorics; allowlist axioms only.        *)
(* -------------------------------------------------------------------------- *)

Print Assumptions next_neq_self_of_other.
Print Assumptions vdeg_pos_of_in_verts.
Print Assumptions exists_leaf_or_min_degree2.

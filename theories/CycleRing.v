(* ==========================================================================
   CycleRing.v

   [H-bridge attack, rung B] The vertex-simple cycle through a non-cut edge
   yields a VALID SIMPLE RING -- the exact shape the winding-number/JCT
   strand consumes.

   Rung A (`DartPath.v`) produced, for a non-cut edge `d`, a vertex-simple
   dart path `c` from `dtip d` back to `dbase d` in `E_minus E d` with
   `2 <= length c`.  Here the closed cycle `d :: c` is fed to the ring
   pipeline (`Dart = Edge = Point*Point`, so the dart list IS its own
   segment chain):

     - `dpath_chain_ok` / `cycle_closed_chain`: the cycle is a
       `closed_chain`, so `RingExtract.face_walk_core` delivers
       `ring_closed`, `ring_has_minimum_points`, and edge fidelity
       (`ring_edges = d :: c`);
     - `dpath_nth_pair` (positional skeleton): the i-th dart of a path is
       exactly the i-th consecutive pair of the visited-vertex trace, so
       `NoDup` of the trace turns positional distinctness into dart-level
       facts;
     - `dpath_no_twin_pair` / `dpath_chord_ne` / `cycle_window_twin_free`:
       a vertex-simple cycle contains NO twin pair -- the `d1 <> twin d2`
       proviso of the twin-aware noding predicate is vacuously satisfied,
       so `FaceTwinAware.ring_simple_of_subset_twin_aware` applies.  This
       is precisely where the recorded PR #319 obstruction (a
       `same_face d (twin d)` FACE walk contains `d` AND `twin d`, hence
       is never `ring_simple`) evaporates for the CYCLE object;
     - `cycle_ring_core_nodup`: the ring's core vertices are distinct
       (`JCTRingCycle.ring_core_nodup`), by rotating the path trace;
     - `non_cut_edge_cycle_ring` (headline): under twin-aware noding, a
       non-cut proper edge `d` (stored orientation unique) lies on a cycle
       whose ring is closed, min-points, core-NoDup, and SIMPLE, with
       `ring_edges` exactly `d :: c`.

   Next rungs: feed the ring to the parity/JCT strand
   (`GeneralTautBridge.parity_seam_offring_of_simple` needs exactly
   `ring_simple` + `ring_core_nodup` + general-position seasoning) and
   build the face-orbit parity bridge.

   Pure Point/list combinatorics; no `Admitted` / `Axiom` / `Parameter`;
   allowlist axioms only.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
   ========================================================================== *)

From Stdlib Require Import List Arith Lia Permutation.
From NTS.Proofs Require Import Distance Overlay OverlayGraph Dart EdgeConnectivity
                               DartPath BufferAssembly RingExtract RingSimple
                               FaceTwinAware ArrangementEMinus JCTRingCycle.

Import ListNotations.

(* -------------------------------------------------------------------------- *)
(* §1  A dart path is a chain; closing it with `d` gives a closed chain.       *)
(* -------------------------------------------------------------------------- *)

Lemma dpath_chain_ok :
  forall D u v c, dpath D u v c -> chain_ok c.
Proof.
  intros D u v c H. induction H as [u0 | x w c Hx Hp IH].
  - exact I.
  - destruct c as [| y c'].
    + exact I.
    + cbn [chain_ok]. split; [ | exact IH ].
      inversion Hp; subst.
      first [ assumption | symmetry; assumption ].
Qed.

Lemma cycle_closed_chain :
  forall D d c,
    dpath D (dtip d) (dbase d) c -> c <> [] -> closed_chain (d :: c).
Proof.
  intros D d c Hp Hne. split.
  - destruct c as [| y c']; [ contradiction | ].
    cbn [chain_ok]. split.
    + inversion Hp; subst.
      first [ assumption | symmetry; assumption ].
    + exact (dpath_chain_ok D (dtip d) (dbase d) (y :: c') Hp).
  - intros d0 _.
    destruct (exists_last Hne) as [c' [x Hcx]]. subst c.
    (* normalise the goal (hd reduces; re-associate the snoc) in one change,
       then use the POLYMORPHIC stdlib `last_last` -- the monomorphic
       BufferAssembly last-lemmas fail rewrite's syntactic matching against
       the goal's `@cons Dart` type argument *)
    change (snd (last ((d :: c') ++ [x]) d0) = fst d).
    rewrite last_last.
    symmetry.
    exact (dpath_last_tip D c' x (dtip d) (dbase d) Hp).
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  Positional skeleton: the i-th dart is the i-th trace pair.              *)
(* -------------------------------------------------------------------------- *)

Lemma dpath_nth_pair :
  forall D u v c,
    dpath D u v c ->
    forall i (d0 : Dart) (p0 : Point), (i < length c)%nat ->
      nth i c d0 =
      (nth i (u :: map dtip c) p0, nth (S i) (u :: map dtip c) p0).
Proof.
  intros D u v c H.
  induction H as [u0 | x w c Hx Hp IH]; intros i d0 p0 Hi.
  - cbn [length] in Hi. lia.
  - destruct i as [| i'].
    + cbn [nth map]. unfold dbase, dtip.
      rewrite <- surjective_pairing. reflexivity.
    + cbn [nth map]. apply IH. cbn [length] in Hi. lia.
Qed.

Lemma dpath_trace_last_nth :
  forall D u v c (p0 : Point),
    dpath D u v c -> nth (length c) (u :: map dtip c) p0 = v.
Proof.
  intros D u v c p0 H.
  induction H as [u0 | x w c Hx Hp IH]; cbn [length map nth].
  - reflexivity.
  - exact IH.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Vertex-simplicity kills every twin pair on the cycle.                   *)
(* -------------------------------------------------------------------------- *)

(* Within a vertex-simple path, no dart is the twin of any path dart
   (including itself -- so all path darts are proper). *)
Lemma dpath_no_twin_pair :
  forall D u v c,
    dpath D u v c -> NoDup (u :: map dtip c) ->
    forall x y, In x c -> In y c -> x <> twin y.
Proof.
  intros D u v c Hp Hnd x y Hx Hy Heq.
  destruct (In_nth c x (u, u) Hx) as [i [Hi Hxi]].
  destruct (In_nth c y (u, u) Hy) as [j [Hj Hyj]].
  pose proof (dpath_nth_pair D u v c Hp i (u, u) u Hi) as Hpi.
  pose proof (dpath_nth_pair D u v c Hp j (u, u) u Hj) as Hpj.
  rewrite Hxi in Hpi. rewrite Hyj in Hpj.
  rewrite Hpi, Hpj in Heq.
  unfold twin in Heq. cbn [fst snd] in Heq.
  injection Heq as He1 He2.
  pose proof (proj1 (NoDup_nth (u :: map dtip c) u) Hnd) as Hinj.
  assert (Hlt : length (u :: map dtip c) = S (length c))
    by (cbn [length]; rewrite length_map; reflexivity).
  assert (Hij1 : i = S j)
    by (apply Hinj; [ rewrite Hlt; lia | rewrite Hlt; lia | exact He1 ]).
  assert (Hij2 : S i = j)
    by (apply Hinj; [ rewrite Hlt; lia | rewrite Hlt; lia | exact He2 ]).
  lia.
Qed.

(* No path dart short-circuits the endpoints: a dart equal to `(u, v)`
   would sit at trace positions (0, length c), forcing a length-1 path. *)
Lemma dpath_chord_ne :
  forall D u v c,
    dpath D u v c -> NoDup (u :: map dtip c) -> (2 <= length c)%nat ->
    forall y, In y c -> y <> (u, v).
Proof.
  intros D u v c Hp Hnd Hlen y Hy Heq.
  destruct (In_nth c y (u, u) Hy) as [j [Hj Hyj]].
  pose proof (dpath_nth_pair D u v c Hp j (u, u) u Hj) as Hpj.
  rewrite Hyj in Hpj. rewrite Hpj in Heq.
  injection Heq as He1 He2.
  pose proof (proj1 (NoDup_nth (u :: map dtip c) u) Hnd) as Hinj.
  assert (Hlt : length (u :: map dtip c) = S (length c))
    by (cbn [length]; rewrite length_map; reflexivity).
  assert (Hj0 : j = 0%nat).
  { apply Hinj; [ rewrite Hlt; lia | rewrite Hlt; lia | ].
    cbn [nth]. exact He1. }
  assert (HSj : S j = length c).
  { apply Hinj; [ rewrite Hlt; lia | rewrite Hlt; lia | ].
    rewrite (dpath_trace_last_nth D u v c u Hp). exact He2. }
  lia.
Qed.

(* The cycle window `d :: c` is twin-free: the proviso of the twin-aware
   noding predicate is vacuous on a vertex-simple cycle. *)
Lemma cycle_window_twin_free :
  forall (D : list Dart) (d : Dart) (c : list Dart),
    dpath D (dtip d) (dbase d) c ->
    NoDup (dtip d :: map dtip c) ->
    (2 <= length c)%nat ->
    dbase d <> dtip d ->
    forall x, In x (d :: c) -> ~ In (twin x) (d :: c).
Proof.
  intros D d c Hp Hnd Hlen Hproper x Hx Htx.
  destruct Hx as [Hx | Hx]; destruct Htx as [Htx | Htx].
  - (* x = d and twin d = d: impossible for a proper edge *)
    subst x. exact (twin_neq_self d Hproper (eq_sym Htx)).
  - (* x = d and twin d on the path: the (dtip d, dbase d) chord *)
    subst x.
    apply (dpath_chord_ne D (dtip d) (dbase d) c Hp Hnd Hlen (twin d) Htx).
    reflexivity.
  - (* x on the path and twin x = d: x IS the chord again *)
    assert (Hxd : x = twin d)
      by (rewrite Htx, twin_involutive; reflexivity).
    apply (dpath_chord_ne D (dtip d) (dbase d) c Hp Hnd Hlen x Hx).
    rewrite Hxd. reflexivity.
  - (* both on the path: §3's no-twin-pair fact *)
    exact (dpath_no_twin_pair D (dtip d) (dbase d) c Hp Hnd
             (twin x) x Htx Hx eq_refl).
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Core vertex distinctness: rotate the path trace.                        *)
(* -------------------------------------------------------------------------- *)

(* The base trace is the tip trace shifted by one. *)
Lemma dpath_base_trace :
  forall D u v c, dpath D u v c -> map dbase c ++ [v] = u :: map dtip c.
Proof.
  intros D u v c H.
  induction H as [u0 | x w c Hx Hp IH]; cbn [map app].
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma cycle_ring_core_nodup :
  forall D d c,
    dpath D (dtip d) (dbase d) c ->
    NoDup (dtip d :: map dtip c) ->
    ring_core_nodup (ring_of_chain (d :: c)).
Proof.
  intros D d c Hp Hnd.
  exists (fst d), (map fst c). split.
  - cbn [ring_of_chain map app]. reflexivity.
  - assert (Hmb : map (fun z : Dart => fst z) c = map dbase c)
      by (apply map_ext; intro; reflexivity).
    change (NoDup (dbase d :: map (fun z : Dart => fst z) c)).
    rewrite Hmb.
    pose proof (dpath_base_trace D (dtip d) (dbase d) c Hp) as Htr.
    eapply Permutation_NoDup.
    + apply Permutation_sym.
      apply (Permutation_cons_append (map dbase c) (dbase d)).
    + rewrite Htr. exact Hnd.
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  Headline: the non-cut-edge cycle ring is a valid simple ring.           *)
(* -------------------------------------------------------------------------- *)

Theorem non_cut_edge_cycle_ring :
  forall (E : list Edge) (d : Dart),
    pairwise_no_proper_cross_twin_aware (darts_of E) ->
    In d E -> ~ In (twin d) E -> dbase d <> dtip d ->
    reachable (E_minus E d) (dtip d) (dbase d) ->
    exists c : list Dart,
      dpath (darts_of (E_minus E d)) (dtip d) (dbase d) c /\
      (2 <= length c)%nat /\
      NoDup (dtip d :: map dtip c) /\
      closed_chain (d :: c) /\
      ring_closed (ring_of_chain (d :: c)) /\
      ring_has_minimum_points (ring_of_chain (d :: c)) /\
      ring_core_nodup (ring_of_chain (d :: c)) /\
      ring_simple (ring_of_chain (d :: c)) /\
      ring_edges (ring_of_chain (d :: c)) = d :: c.
Proof.
  intros E d Hpw HdE Hntwin Hproper Hreach.
  destruct (non_cut_edge_simple_cycle E d HdE Hntwin Hproper Hreach)
    as [c [Hp [Hnd Hlen]]].
  assert (Hne : c <> [])
    by (destruct c; [ cbn [length] in Hlen; lia | discriminate ]).
  assert (Hcc : closed_chain (d :: c))
    by (exact (cycle_closed_chain (darts_of (E_minus E d)) d c Hp Hne)).
  assert (Hlen3 : (3 <= length (d :: c))%nat) by (cbn [length]; lia).
  destruct (face_walk_core (d :: c) Hcc Hlen3) as [Hclosed [Hmin Hedges]].
  assert (Htf : forall x, In x (d :: c) -> ~ In (twin x) (d :: c))
    by (exact (cycle_window_twin_free (darts_of (E_minus E d)) d c
                 Hp Hnd Hlen Hproper)).
  assert (HWD : forall x, In x (d :: c) -> In x (darts_of E)).
  { intros x [Hxd | Hxc].
    - rewrite <- Hxd. apply in_darts_of_orig. exact HdE.
    - apply (incl_darts_of_E_minus E d).
      exact (dpath_darts_in _ _ _ _ Hp x Hxc). }
  assert (Hsimple : ring_simple (ring_of_chain (d :: c))).
  { apply (ring_simple_of_subset_twin_aware (darts_of E) (d :: c));
      [ exact Hpw | exact HWD | exact Htf | ].
    rewrite Hedges. intros e He. exact He. }
  exists c.
  split; [ exact Hp | split; [ exact Hlen | split; [ exact Hnd |
    split; [ exact Hcc | split; [ exact Hclosed | split; [ exact Hmin |
    split; [ | split; [ exact Hsimple | exact Hedges ] ] ] ] ] ] ] ].
  exact (cycle_ring_core_nodup (darts_of (E_minus E d)) d c Hp Hnd).
Qed.

(* -------------------------------------------------------------------------- *)
(* Axiom audit.  Combinatorial wiring; allowlist axioms only.                  *)
(* -------------------------------------------------------------------------- *)

Print Assumptions cycle_window_twin_free.
Print Assumptions non_cut_edge_cycle_ring.

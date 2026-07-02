(* ==========================================================================
   DartPath.v

   [H-bridge attack, rung A] Dart paths: reachability as an explicit dart
   list, vertex-simple path extraction, and the simple cycle through a
   non-cut edge.

   The corpus's `reachable` (EdgeConnectivity.v) is a bare inductive walk;
   nothing ties it to an explicit list of darts, and nothing extracts a
   VERTEX-SIMPLE (NoDup visited-vertex trace) path from a walk.  This file
   supplies that layer:

     - `dpath D u v c`      : `c` is a chained list of darts of `D` from
                              `u` to `v` (each dart based where the
                              previous one tipped);
     - `reachable_dpath`    : `reachable E u v <->
                              exists c, dpath (darts_of E) u v c`;
     - `dpath_simple`       : every dart path contains a vertex-simple one
                              with the same endpoints -- loops are cut at
                              repeated vertices (strong induction on the
                              path length);
     - `non_cut_edge_simple_cycle` (headline): if deleting edge `d` leaves
       its endpoints connected, there is a vertex-simple dart path from
       `dtip d` back to `dbase d` in `E_minus E d` with AT LEAST TWO darts
       -- i.e. `d` lies on a vertex-simple cycle of length >= 3.

   WHY THIS RUNG: the `same_face <-> cut-edge` investigation (plan.md,
   2026-07-02) showed the per-face ring of a `same_face d (twin d)` face
   walk is provably NOT `ring_simple` -- it contains both `d` and
   `twin d`, and a segment properly crosses its own reversal -- so the
   winding-number/JCT strand cannot consume it.  A VERTEX-SIMPLE cycle
   through `d` has no twin pair (its visited vertices are distinct, so no
   undirected edge repeats in either orientation): its ring is exactly the
   shape `ring_simple` / `ring_core_nodup` demand.  This rung banks the
   combinatorial half of that pivot; making the cycle ring `ring_simple`
   under noding, and the face-orbit parity bridge, are subsequent rungs.

   Pure Point/list combinatorics; no `Admitted` / `Axiom` / `Parameter`;
   allowlist axioms only.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
   ========================================================================== *)

From Stdlib Require Import List Arith Lia Wf_nat ListDec.
From NTS.Proofs Require Import Distance Overlay OverlayGraph Dart EdgeConnectivity.

Import ListNotations.

(* -------------------------------------------------------------------------- *)
(* §1  Dart paths: chained dart lists with explicit endpoints.                 *)
(* -------------------------------------------------------------------------- *)

(* `dpath D u v c`: the darts of `c` all lie in `D`, the first is based at
   `u`, each subsequent dart is based at the previous dart's tip, and the
   last dart tips at `v` (an empty path forces `u = v`). *)
Inductive dpath (D : list Dart) : Point -> Point -> list Dart -> Prop :=
| dpath_nil : forall u, dpath D u u []
| dpath_cons : forall x w c,
    In x D -> dpath D (dtip x) w c -> dpath D (dbase x) w (x :: c).

Lemma dpath_nil_eq : forall D u v, dpath D u v [] -> u = v.
Proof. intros D u v H. inversion H. reflexivity. Qed.

Lemma dpath_darts_in :
  forall D u v c, dpath D u v c -> forall x, In x c -> In x D.
Proof.
  intros D u v c H. induction H as [u0 | x w c Hx Hp IH]; intros y Hy.
  - destruct Hy.
  - destruct Hy as [Heq | Hy]; [ rewrite <- Heq; exact Hx | exact (IH y Hy) ].
Qed.

(* Concatenation: paths compose end to end. *)
Lemma dpath_app :
  forall D u m v c1 c2,
    dpath D u m c1 -> dpath D m v c2 -> dpath D u v (c1 ++ c2).
Proof.
  intros D u m v c1 c2 H1 H2. revert v c2 H2.
  induction H1 as [u0 | x w c Hx Hp IH]; intros v c2 H2.
  - exact H2.
  - cbn [app]. apply dpath_cons; [ exact Hx | exact (IH v c2 H2) ].
Qed.

(* Splitting: a path over an appended list factorises through a midpoint. *)
Lemma dpath_app_inv :
  forall D c1 c2 u v,
    dpath D u v (c1 ++ c2) -> exists m, dpath D u m c1 /\ dpath D m v c2.
Proof.
  intros D c1. induction c1 as [| x c1 IH]; intros c2 u v H.
  - exists u. split; [ apply dpath_nil | exact H ].
  - cbn [app] in H.
    inversion H as [| x' w c' Hx Hp He1 He2 He3]; subst.
    destruct (IH c2 (dtip x) v Hp) as [m [Hm1 Hm2]].
    exists m. split; [ apply dpath_cons; assumption | exact Hm2 ].
Qed.

(* A path ending with dart `x` ends at `dtip x`. *)
Lemma dpath_last_tip :
  forall D c x u v, dpath D u v (c ++ [x]) -> v = dtip x.
Proof.
  intros D c x u v H.
  destruct (dpath_app_inv D c [x] u v H) as [m [_ Hm]].
  inversion Hm as [| x' w c' Hx Hp He1 He2 He3]; subst.
  inversion Hp; subst. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  Dart paths realise `reachable`.                                         *)
(* -------------------------------------------------------------------------- *)

(* One adjacency step is exactly one dart of `darts_of E`. *)
Lemma adj_dart_iff :
  forall (E : list Edge) (u v : Point),
    adj E u v <-> exists x, In x (darts_of E) /\ dbase x = u /\ dtip x = v.
Proof.
  intros E u v. split.
  - intros [e [He Hor]]. destruct Hor as [[Hf Hs] | [Hf Hs]].
    + exists e. split; [ apply in_darts_of_orig; exact He | ].
      split; [ exact Hf | exact Hs ].
    + exists (twin e). split; [ apply in_darts_of_twin; exact He | ].
      split; [ rewrite dbase_twin; exact Hs | rewrite dtip_twin; exact Hf ].
  - intros [x [Hx [Hb Ht]]]. unfold darts_of in Hx. apply in_app_or in Hx.
    destruct Hx as [Hx | Hx].
    + exists x. split; [ exact Hx | left; split; [ exact Hb | exact Ht ] ].
    + apply in_map_iff in Hx. destruct Hx as [e [Heq He]].
      exists e. split; [ exact He | right ]. split.
      * rewrite <- Ht, <- Heq, dtip_twin. reflexivity.
      * rewrite <- Hb, <- Heq, dbase_twin. reflexivity.
Qed.

(* Reachability is exactly the existence of a dart path. *)
Theorem reachable_dpath :
  forall (E : list Edge) (u v : Point),
    reachable E u v <-> exists c, dpath (darts_of E) u v c.
Proof.
  intros E u v. split.
  - intro H. induction H as [u0 | u0 v0 w Hadj Hrec IH].
    + exists []. apply dpath_nil.
    + destruct IH as [c Hc].
      apply adj_dart_iff in Hadj. destruct Hadj as [x [Hx [Hb Ht]]].
      exists (x :: c). rewrite <- Hb. apply dpath_cons; [ exact Hx | ].
      rewrite Ht. exact Hc.
  - intros [c Hc]. induction Hc as [u0 | x w c Hx Hp IH].
    + apply reach_refl.
    + apply reach_step with (dtip x).
      * apply adj_dart_iff. exists x.
        split; [ exact Hx | split; reflexivity ].
      * exact IH.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Vertex-simple extraction: cut every loop at its repeated vertex.        *)
(* -------------------------------------------------------------------------- *)

(* A duplicated element splits a list into two occurrences (needs decidable
   equality to FIND the duplicate). *)
Lemma not_NoDup_split :
  forall {A : Type} (eqdec : forall a b : A, {a = b} + {a <> b})
         (l : list A),
    ~ NoDup l -> exists l1 a l2 l3, l = l1 ++ a :: l2 ++ a :: l3.
Proof.
  intros A eqdec l. induction l as [| a l IH]; intro Hnd.
  - exfalso. apply Hnd. constructor.
  - destruct (in_dec eqdec a l) as [Hin | Hnin].
    + apply in_split in Hin. destruct Hin as [l2 [l3 Heq]].
      exists [], a, l2, l3. cbn [app]. rewrite Heq. reflexivity.
    + destruct (NoDup_dec eqdec l) as [Hnd' | Hnd'].
      * exfalso. apply Hnd. constructor; assumption.
      * destruct (IH Hnd') as [l1 [b [l2 [l3 Heq]]]].
        exists (a :: l1), b, l2, l3. cbn [app]. rewrite Heq. reflexivity.
Qed.

(* Every dart path contains a VERTEX-SIMPLE dart path with the same
   endpoints: the visited-vertex trace `u :: map dtip c'` has no
   duplicates.  Loops are cut at their repeated vertex; strong induction
   on the path length. *)
Theorem dpath_simple :
  forall D u v c,
    dpath D u v c ->
    exists c', dpath D u v c' /\ NoDup (u :: map dtip c').
Proof.
  intros D u v.
  assert (Hgen : forall n c, length c = n -> dpath D u v c ->
            exists c', dpath D u v c' /\ NoDup (u :: map dtip c')).
  { induction n as [n IH] using lt_wf_ind; intros c Hn H.
    destruct (in_dec point_eq_dec u (map dtip c)) as [Hin | Hnin].
    - (* the source is revisited: keep only the tail after the revisit *)
      apply in_map_iff in Hin. destruct Hin as [x [Htip Hx]].
      apply in_split in Hx. destruct Hx as [c1 [c2 Hc]]. subst c.
      assert (Happ : c1 ++ x :: c2 = (c1 ++ [x]) ++ c2)
        by (rewrite <- app_assoc; reflexivity).
      rewrite Happ in H.
      destruct (dpath_app_inv D (c1 ++ [x]) c2 u v H) as [m [H1 H2]].
      assert (Hm : m = dtip x) by (exact (dpath_last_tip D c1 x u m H1)).
      rewrite Hm, Htip in H2.
      assert (Hlen : (length c2 < n)%nat).
      { rewrite <- Hn.
        repeat first [ rewrite length_app | progress cbn [length] ]. lia. }
      exact (IH _ Hlen _ eq_refl H2).
    - destruct (NoDup_dec point_eq_dec (map dtip c)) as [Hnd | Hnd].
      + (* already simple *)
        exists c. split; [ exact H | constructor; assumption ].
      + (* an interior vertex repeats: cut the loop between the two visits *)
        destruct (not_NoDup_split point_eq_dec (map dtip c) Hnd)
          as [t1 [w [t2 [t3 Ht]]]].
        destruct (map_eq_app dtip c t1 (w :: t2 ++ w :: t3) Ht)
          as [ca [cb [Hc [Hca Hcb]]]].
        destruct (map_eq_cons dtip cb Hcb)
          as [x [cb' [Hcb1 [Hxw Hcb']]]].
        destruct (map_eq_app dtip cb' t2 (w :: t3) Hcb')
          as [cc [cd [Hcb'2 [Hcc Hcd]]]].
        destruct (map_eq_cons dtip cd Hcd)
          as [y [ce [Hcd1 [Hyw Hce]]]].
        subst cd cb' cb c.
        assert (Happ : ca ++ x :: cc ++ y :: ce
                       = (ca ++ [x]) ++ (cc ++ [y]) ++ ce)
          by (rewrite <- !app_assoc; reflexivity).
        rewrite Happ in H.
        destruct (dpath_app_inv D (ca ++ [x]) ((cc ++ [y]) ++ ce) u v H)
          as [m1 [H1 H2]].
        destruct (dpath_app_inv D (cc ++ [y]) ce m1 v H2) as [m2 [H3 H4]].
        assert (Hm1 : m1 = dtip x) by (exact (dpath_last_tip D ca x u m1 H1)).
        assert (Hm2 : m2 = dtip y) by (exact (dpath_last_tip D cc y m1 m2 H3)).
        assert (Hm12 : m2 = m1) by congruence.
        rewrite Hm12 in H4.
        pose proof (dpath_app D u m1 v (ca ++ [x]) ce H1 H4) as Hnew.
        assert (Hlen : (length ((ca ++ [x]) ++ ce) < n)%nat).
        { rewrite <- Hn.
          repeat first [ rewrite length_app | progress cbn [length] ]. lia. }
        exact (IH _ Hlen _ eq_refl Hnew). }
  intros c H. exact (Hgen (length c) c eq_refl H).
Qed.

(* Packaged with §2: reachability yields a vertex-simple dart path. *)
Corollary reachable_simple_dpath :
  forall (E : list Edge) (u v : Point),
    reachable E u v ->
    exists c, dpath (darts_of E) u v c /\ NoDup (u :: map dtip c).
Proof.
  intros E u v H.
  destruct (proj1 (reachable_dpath E u v) H) as [c Hc].
  exact (dpath_simple (darts_of E) u v c Hc).
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Headline: a non-cut edge lies on a vertex-simple cycle of length >= 3.  *)
(* -------------------------------------------------------------------------- *)

(* If deleting `d` leaves its endpoints connected, there is a vertex-simple
   dart path from `dtip d` back to `dbase d` avoiding `d` -- and it has at
   least TWO darts: a one-dart path would BE the dart `(dtip d, dbase d)`
   = `twin d`, which `E_minus E d` cannot contain (its original orientation
   is exactly the deleted `d`; its stored orientation is excluded by
   `~ In (twin d) E`).  Together with `d` itself this is a vertex-simple
   cycle of length >= 3 through `d`. *)
Theorem non_cut_edge_simple_cycle :
  forall (E : list Edge) (d : Dart),
    In d E -> ~ In (twin d) E -> dbase d <> dtip d ->
    reachable (E_minus E d) (dtip d) (dbase d) ->
    exists c,
      dpath (darts_of (E_minus E d)) (dtip d) (dbase d) c /\
      NoDup (dtip d :: map dtip c) /\
      (2 <= length c)%nat.
Proof.
  intros E d HdE Hntwin Hproper Hreach.
  destruct (reachable_simple_dpath (E_minus E d) (dtip d) (dbase d) Hreach)
    as [c [Hp Hnd]].
  exists c. split; [ exact Hp | split; [ exact Hnd | ] ].
  destruct c as [| x c'].
  - (* empty path: endpoints would coincide *)
    exfalso. apply Hproper. symmetry. exact (dpath_nil_eq _ _ _ Hp).
  - destruct c' as [| y c''].
    + (* a single dart from dtip d to dbase d IS twin d -- impossible *)
      exfalso.
      assert (Hin : In x (darts_of (E_minus E d)))
        by (exact (dpath_darts_in _ _ _ _ Hp x (or_introl eq_refl))).
      inversion Hp as [| x0 w0 c0 Hx0 Hrest He1 He2 He3]; subst.
      inversion Hrest as [u1 Hu1 Hv1 Hc1 |]; subst.
      (* now: dbase x = dtip d (He2) and dtip x = dbase d (from Hrest) *)
      assert (Hxd : x = twin d).
      { destruct x as [a b]; destruct d as [p q].
        unfold dbase, dtip, twin in *; cbn in *. congruence. }
      unfold darts_of in Hin. apply in_app_or in Hin.
      destruct Hin as [Hin | Hin].
      * apply in_E_minus in Hin. destruct Hin as [HxE _].
        apply Hntwin. rewrite <- Hxd. exact HxE.
      * apply in_map_iff in Hin. destruct Hin as [e [Heq He]].
        apply in_E_minus in He. destruct He as [_ Hne].
        apply Hne. apply twin_inj. rewrite Heq. exact Hxd.
    + cbn [length]. lia.
Qed.

(* -------------------------------------------------------------------------- *)
(* Axiom audit.  Combinatorial wiring; allowlist axioms only.                  *)
(* -------------------------------------------------------------------------- *)

Print Assumptions reachable_dpath.
Print Assumptions dpath_simple.
Print Assumptions non_cut_edge_simple_cycle.

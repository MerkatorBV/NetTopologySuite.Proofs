(* ============================================================================
   NetTopologySuite.Proofs.BufferAssembly
   ----------------------------------------------------------------------------
   Buffer/noder pipeline, Stage 2 seam: EDGE-LIST ASSEMBLY.
   (Seam map: docs/buffer-noder-pipeline.md §2.2 / §6 slice "edge-list assembly".)

   Turns the per-edge offset walls (theories/BufferOffset.v) and the
   per-vertex joins into the raw buffer-curve segment list that the
   pipeline nodes.  Uses the BEVEL join (theories/BufferBevel.v): between
   the offset wall of edge e1 and the wall of the next edge e2 (sharing the
   corner vertex), insert the straight segment connecting the end of wall
   e1 to the start of wall e2.

   The deliverable is the STRUCTURAL soundness of the assembly, the
   property ring extraction needs: the assembled boundary is a *closed
   chain* -- consecutive segments share an endpoint (`snd s_i = fst s_{i+1}`)
   and the last segment's end returns to the first segment's start.  This
   holds BY CONSTRUCTION (the joins are defined to bridge wall-end to
   next-wall-start), so the proofs are pure list induction.

   Also: each wall is parallel to its source edge (`wall_parallel`, citing
   `BufferOffset.offset_seg_parallel`).

   §6 (follow-up landed, issue #65 RGR pivot to a low-risk/low-cost slice):
   the MITER join is now wired into the same assembly, exactly the
   generalisation this file's own §1 comment anticipated -- a join
   sub-chain is any list from `snd (owall e1)` to `fst (owall e2)`, and a
   miter join is just TWO such segments meeting at `BufferMiter.miter_apex`
   instead of bevel's one.  `assemble_open_miter` / `assemble_closed_miter`
   are the miter analogues of `assemble_open` / `assemble_closed`, and
   `assemble_open_miter_chain` / `assemble_closed_miter_closed` are the
   exact miter analogues of `assemble_open_chain` / `assemble_closed_closed`
   -- same structural argument, generalised via two small reusable list
   lemmas (`chain_ok_cons_nonempty`, `chain_ok_app`) instead of duplicating
   the bevel proof by hand. Pure structural assembly: no new geometric
   content beyond the already-Qed `miter_apex`, no self-intersection claim
   (the noding frontier for non-convex/self-crossing offsets is untouched).
   Round-join assembly is NOT done here: unlike bevel/miter (one/two
   straight segments), a round join is a curved arc, which does not fit
   this file's `list (Point * Point)` straight-segment model without a
   chord approximation (still open, per docs/buffer-noder-pipeline.md §3).

   All pure-R, three-axiom (no atan / Flocq / classic).  No `Admitted` /
   `Axiom` / `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude (Opus-4.8)
   ========================================================================== *)

From Stdlib Require Import Reals Lra List.
From NTS.Proofs Require Import Real Vec Distance Direction BufferOffset BufferMiter.
Import ListNotations.
Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  Walls, joins, and the open assembly.                                   *)
(* -------------------------------------------------------------------------- *)

(* The offset wall of an input edge e = (A, B), parallel to it at distance d. *)
Definition owall (e : Point * Point) (d : R) : Point * Point :=
  offset_seg (fst e) (snd e) d.

(* The bevel join between consecutive edges e1, e2 (sharing a corner):
   bridge the end of wall e1 to the start of wall e2. *)
Definition obevel (e1 e2 : Point * Point) (d : R) : Point * Point :=
  (snd (owall e1 d), fst (owall e2 d)).

(* Assemble an open chain of edges into walls interleaved with bevel joins:
   [owall e0; obevel e0 e1; owall e1; obevel e1 e2; ...; owall e_{n-1}]. *)
Fixpoint assemble_open (es : list (Point * Point)) (d : R) : list (Point * Point) :=
  match es with
  | [] => []
  | e :: rest =>
      match rest with
      | [] => owall e d :: nil
      | e2 :: _ => owall e d :: obevel e e2 d :: assemble_open rest d
      end
  end.

(* -------------------------------------------------------------------------- *)
(* §2  The chain predicate.                                                   *)
(* -------------------------------------------------------------------------- *)

(* Consecutive segments share an endpoint: snd s_i = fst s_{i+1}. *)
Fixpoint chain_ok (segs : list (Point * Point)) : Prop :=
  match segs with
  | [] => True
  | s1 :: rest =>
      match rest with
      | [] => True
      | s2 :: _ => snd s1 = fst s2 /\ chain_ok rest
      end
  end.

(* -------------------------------------------------------------------------- *)
(* §3  The open assembly is a chain (by construction).                        *)
(* -------------------------------------------------------------------------- *)

(* The assembly of a non-empty edge list starts with the first edge's wall. *)
Lemma assemble_open_head : forall e es d,
  exists r, assemble_open (e :: es) d = owall e d :: r.
Proof. intros e es d. destruct es as [|e2 es']; eexists; reflexivity. Qed.

Theorem assemble_open_chain : forall es d, chain_ok (assemble_open es d).
Proof.
  intros es d. induction es as [| e es' IH].
  - exact I.
  - destruct es' as [| e2 es''].
    + exact I.
    + change (assemble_open (e :: e2 :: es'') d)
        with (owall e d :: obevel e e2 d :: assemble_open (e2 :: es'') d).
      destruct (assemble_open_head e2 es'' d) as [r Hr].
      rewrite Hr. rewrite Hr in IH.
      cbn [chain_ok].
      split; [ reflexivity | split; [ reflexivity | exact IH ] ].
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Each wall is parallel to its source edge.                              *)
(* -------------------------------------------------------------------------- *)

Theorem wall_parallel : forall e d,
  parallel (seg_vec (fst (owall e d)) (snd (owall e d)))
           (seg_vec (fst e) (snd e)).
Proof.
  intros e d. unfold owall. apply offset_seg_parallel.
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  Closing the chain into a loop.                                         *)
(* -------------------------------------------------------------------------- *)

(* `last` does not depend on the default once the list is non-empty. *)
Lemma last_indep : forall (l : list (Point * Point)) a b,
  l <> [] -> last l a = last l b.
Proof.
  induction l as [| x l' IH]; intros a b Hne.
  - exfalso; apply Hne; reflexivity.
  - destruct l' as [| y l''].
    + reflexivity.
    + cbn [last]. apply IH. discriminate.
Qed.

(* Appending one segment whose start equals the chain's end preserves the
   chain property. *)
Lemma chain_ok_snoc : forall (c : Point * Point) segs,
  chain_ok segs ->
  (forall d0, segs <> [] -> snd (last segs d0) = fst c) ->
  chain_ok (segs ++ [c]).
Proof.
  intros c segs. induction segs as [| s1 segs' IH]; intros Hchain Hjunc.
  - exact I.
  - destruct segs' as [| s2 rest].
    + cbn [app chain_ok]. split; [ apply (Hjunc s1); discriminate | exact I ].
    + change ((s1 :: s2 :: rest) ++ [c]) with (s1 :: (s2 :: rest) ++ [c]).
      cbn [chain_ok] in Hchain. destruct Hchain as [H12 Hrest].
      change ((s2 :: rest) ++ [c]) with (s2 :: (rest ++ [c])).
      cbn [chain_ok]. split.
      * exact H12.
      * change (s2 :: rest ++ [c]) with ((s2 :: rest) ++ [c]).
        apply IH; [ exact Hrest | ].
        intros d0 _. specialize (Hjunc d0 ltac:(discriminate)).
        cbn [last] in Hjunc. exact Hjunc.
Qed.

(* Close any chain into a loop: append the segment from the chain's end back
   to its start. *)
Definition close_chain (segs : list (Point * Point)) : list (Point * Point) :=
  match segs with
  | [] => []
  | s0 :: _ => segs ++ [ (snd (last segs s0), fst s0) ]
  end.

(* The closed assembly: bevel-join open assembly, then close the loop. *)
Definition assemble_closed (es : list (Point * Point)) (d : R) : list (Point * Point) :=
  close_chain (assemble_open es d).

(* A closed chain: chained, and the last segment's end is the first's start. *)
Definition closed_chain (segs : list (Point * Point)) : Prop :=
  chain_ok segs /\
  (forall d0, segs <> [] -> snd (last segs d0) = fst (hd d0 segs)).

(* `last` of a cons with a non-empty tail drops the head. *)
Lemma last_cons_ne : forall (a : Point * Point) m d0,
  m <> [] -> last (a :: m) d0 = last m d0.
Proof. intros a m d0 Hne. destruct m as [| y m']; [ contradiction | reflexivity ]. Qed.

(* last of a snoc is the snoc'd element. *)
Lemma last_snoc : forall (l : list (Point * Point)) c d0,
  last (l ++ [c]) d0 = c.
Proof.
  induction l as [| x l' IH]; intros c d0.
  - reflexivity.
  - cbn [app].
    rewrite (last_cons_ne x (l' ++ [c]) d0) by (destruct l'; discriminate).
    apply IH.
Qed.

(* hd of a cons-snoc is the head. *)
Lemma hd_cons_snoc : forall (x : Point * Point) l c d0,
  hd d0 ((x :: l) ++ [c]) = x.
Proof. intros. reflexivity. Qed.

(* close_chain turns any chain into a closed chain. *)
Theorem close_chain_closed : forall segs,
  chain_ok segs -> closed_chain (close_chain segs).
Proof.
  intros segs Hchain. destruct segs as [| s0 segs'].
  - unfold close_chain, closed_chain.
    split; [ exact I | intros d0 Hne; exfalso; apply Hne; reflexivity ].
  - cbn [close_chain]. unfold closed_chain. split.
    + apply chain_ok_snoc; [ exact Hchain | ].
      intros d0 _. cbn [fst]. f_equal. apply last_indep. discriminate.
    + intros d0 _.
      rewrite last_snoc. rewrite hd_cons_snoc. cbn [fst snd]. reflexivity.
Qed.

(* The closed bevel assembly of any edge list is a closed chain. *)
Theorem assemble_closed_closed : forall es d,
  closed_chain (assemble_closed es d).
Proof.
  intros es d. unfold assemble_closed.
  apply close_chain_closed. apply assemble_open_chain.
Qed.

(* -------------------------------------------------------------------------- *)
(* §6  The MITER join, wired into the same assembly (the follow-up noted in  *)
(*     the file header: any join sub-chain runs from snd (owall e1) to       *)
(*     fst (owall e2), so the chain structure generalises.  Reuses the       *)
(*     already-Qed `BufferMiter.miter_apex` -- no new geometric content, pure *)
(*     structural assembly exactly like the bevel case above, generalised to *)
(*     a two-segment join (through the apex) instead of one.                 *)
(* -------------------------------------------------------------------------- *)

(* Two generic list facts `chain_ok`/bevel didn't need but the multi-segment
   join does: `hd`/`chain_ok` compose across `++` once the pieces line up at
   the seam. *)
Lemma hd_app_l : forall (l1 l2 : list (Point * Point)) e0,
  l1 <> [] -> hd e0 (l1 ++ l2) = hd e0 l1.
Proof. intros l1 l2 e0 Hne. destruct l1 as [| x l1']; [contradiction | reflexivity]. Qed.

Lemma chain_ok_cons_nonempty : forall (s1 : Point * Point) (L : list (Point * Point)) d0,
  L <> [] ->
  snd s1 = fst (hd d0 L) ->
  chain_ok L ->
  chain_ok (s1 :: L).
Proof.
  intros s1 L d0 Hne Hjunc HL.
  destruct L as [| s2 L']; [contradiction | ].
  cbn [chain_ok]. cbn [hd] in Hjunc.
  split; [ exact Hjunc | exact HL ].
Qed.

Lemma chain_ok_app : forall l1 l2 : list (Point * Point),
  chain_ok l1 -> chain_ok l2 ->
  (forall d0 e0, l1 <> [] -> l2 <> [] -> snd (last l1 d0) = fst (hd e0 l2)) ->
  chain_ok (l1 ++ l2).
Proof.
  induction l1 as [| s1 rest IH]; intros l2 H1 H2 Hjunc.
  - exact H2.
  - destruct rest as [| s2' rest'].
    + cbn [app].
      destruct l2 as [| s2 l2'].
      * exact I.
      * cbn [chain_ok]. split.
        -- specialize (Hjunc s1 s2 ltac:(discriminate) ltac:(discriminate)).
           cbn [last hd] in Hjunc. exact Hjunc.
        -- exact H2.
    + cbn [chain_ok] in H1. destruct H1 as [H12 Hrest].
      change ((s1 :: s2' :: rest') ++ l2) with (s1 :: (s2' :: rest') ++ l2).
      cbn [chain_ok]. split.
      * exact H12.
      * apply IH; [ exact Hrest | exact H2 | ].
        intros d0 e0 _ Hne2.
        specialize (Hjunc d0 e0 ltac:(discriminate) Hne2).
        rewrite (last_cons_ne s1 (s2' :: rest') d0 ltac:(discriminate)) in Hjunc.
        exact Hjunc.
Qed.

(* The miter join between consecutive edges e1, e2 (sharing corner `snd e1`):
   two segments, wall-end to apex and apex to next-wall-start, where the apex
   is `BufferMiter.miter_apex` at the corner using each edge's own direction
   vector. *)
Definition omiter (e1 e2 : Point * Point) (d : R) : list (Point * Point) :=
  let apex := miter_apex (snd e1) (seg_vec (fst e1) (snd e1))
                          (seg_vec (fst e2) (snd e2)) d in
  [ (snd (owall e1 d), apex); (apex, fst (owall e2 d)) ].

Lemma omiter_ne : forall e1 e2 d, omiter e1 e2 d <> [].
Proof. intros e1 e2 d. unfold omiter. discriminate. Qed.

Lemma omiter_chain_ok : forall e1 e2 d, chain_ok (omiter e1 e2 d).
Proof. intros e1 e2 d. unfold omiter. cbn [chain_ok]. split; [ reflexivity | exact I ]. Qed.

Lemma omiter_hd : forall e1 e2 d e0,
  snd (owall e1 d) = fst (hd e0 (omiter e1 e2 d)).
Proof. intros. unfold omiter. reflexivity. Qed.

Lemma omiter_last : forall e1 e2 d d0,
  snd (last (omiter e1 e2 d) d0) = fst (owall e2 d).
Proof. intros. unfold omiter. reflexivity. Qed.

(* Assemble an open chain of edges into walls interleaved with MITER joins:
   [owall e0; omiter e0 e1 (2 segs); owall e1; omiter e1 e2 (2 segs); ...]. *)
Fixpoint assemble_open_miter (es : list (Point * Point)) (d : R) : list (Point * Point) :=
  match es with
  | [] => []
  | e :: rest =>
      match rest with
      | [] => owall e d :: nil
      | e2 :: _ => owall e d :: omiter e e2 d ++ assemble_open_miter rest d
      end
  end.

Lemma assemble_open_miter_head : forall e es d,
  exists r, assemble_open_miter (e :: es) d = owall e d :: r.
Proof. intros e es d. destruct es as [|e2 es']; eexists; reflexivity. Qed.

Theorem assemble_open_miter_chain : forall es d, chain_ok (assemble_open_miter es d).
Proof.
  intros es d. induction es as [| e es' IH].
  - exact I.
  - destruct es' as [| e2 es''].
    + exact I.
    + change (assemble_open_miter (e :: e2 :: es'') d)
        with (owall e d :: (omiter e e2 d ++ assemble_open_miter (e2 :: es'') d)).
      apply chain_ok_cons_nonempty with (d0 := owall e d).
      * intro Heq. apply app_eq_nil in Heq. destruct Heq as [Heq1 _].
        exact (omiter_ne e e2 d Heq1).
      * rewrite (hd_app_l (omiter e e2 d) (assemble_open_miter (e2 :: es'') d)
                   (owall e d) (omiter_ne e e2 d)).
        apply omiter_hd.
      * apply chain_ok_app.
        -- apply omiter_chain_ok.
        -- exact IH.
        -- intros d0 e0 _ Hne2.
           rewrite omiter_last.
           destruct (assemble_open_miter_head e2 es'' d) as [r Hr].
           rewrite Hr. reflexivity.
Qed.

(* The closed MITER assembly: miter-join open assembly, then close the loop. *)
Definition assemble_closed_miter (es : list (Point * Point)) (d : R) : list (Point * Point) :=
  close_chain (assemble_open_miter es d).

(* The closed miter assembly of any edge list is a closed chain -- the exact
   miter analogue of `assemble_closed_closed`. *)
Theorem assemble_closed_miter_closed : forall es d,
  closed_chain (assemble_closed_miter es d).
Proof.
  intros es d. unfold assemble_closed_miter.
  apply close_chain_closed. apply assemble_open_miter_chain.
Qed.

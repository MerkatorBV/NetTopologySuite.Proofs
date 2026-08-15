(* ============================================================================
   NetTopologySuite.Proofs.HeytingOpens
   ----------------------------------------------------------------------------
   The frame of metric opens of the plane, as the algebra of truth values
   Omega = O(R^2) of the spatial topos Sh(R^2).

   This is the foundation of the discrete -> Sh(R^2) bridge lane (see
   docs/discrete-sh-r2-bridge.md and DiscreteShBridge.v).  A "truth value
   over the plane" is an open subset; this module equips the opens with
   their Heyting-algebra operations and proves, in the pointwise (spatial)
   semantics:

     - openness is closed under top, bottom, binary meet, binary join,
       ARBITRARY (index-typed) join, implication and negation
       (`open_top` .. `open_onot`);
     - `oimp` is the Heyting implication: modus ponens (`oimp_elim`) and
       the adjunction  W /\ U <= V  <->  W <= (U ==> V)  for open W
       (`heyting_adjunction`) -- so O(R^2) really is a Heyting algebra;
     - binary meet distributes over arbitrary joins (`oand_ojoin_distrib`):
       the frame law;
     - Omega is PROPERLY Heyting, not Boolean: for the punctured plane
       U = R^2 \ {0} (open: `punct_open`) the excluded middle
       U \/ ~U = top FAILS (`heyting_em_fails`) and ~~U = top while
       U <> top (`not_not_punct_top`, `double_negation_strict`);
     - the infinitary asymmetry that forces the Heyting (not complete
       Boolean) structure: arbitrary joins of opens are open
       (`open_ojoin`) but the pointwise meet of the open balls
       ball(0,r), r > 0, is the non-open singleton {0}
       (`infinite_meet_not_open`);
     - non-strict (closed) predicates are not truth values of the spatial
       topos: `closed_halfplane_not_open`.  This is the formal face of the
       JTS/NTS convention that OGC Interior-based (strict) predicates are
       the ones with stable local semantics.

   Everything is stated against the pointwise order `oincl` and pointwise
   equivalence `osame`; no propositional extensionality is used.

   No `Admitted`, no `Axiom`, no `Parameter`; classical content only via
   the corpus' three allowed real-number axioms.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import Real Distance Linearise.
Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* Truth values over the plane: predicates, order, equivalence.               *)
(* -------------------------------------------------------------------------- *)

Definition OSet : Type := Point -> Prop.

Definition oincl (U V : OSet) : Prop := forall p, U p -> V p.
Definition osame (U V : OSet) : Prop := forall p, U p <-> V p.

Lemma oincl_refl : forall U, oincl U U.
Proof. intros U p H. exact H. Qed.

Lemma oincl_trans : forall U V W, oincl U V -> oincl V W -> oincl U W.
Proof. intros U V W H1 H2 p Hp. exact (H2 p (H1 p Hp)). Qed.

Lemma osame_refl : forall U, osame U U.
Proof. intros U p. tauto. Qed.

Lemma osame_sym : forall U V, osame U V -> osame V U.
Proof. intros U V H p. specialize (H p). tauto. Qed.

Lemma osame_trans : forall U V W, osame U V -> osame V W -> osame U W.
Proof. intros U V W H1 H2 p. specialize (H1 p). specialize (H2 p). tauto. Qed.

Lemma osame_oincl : forall U V, osame U V -> oincl U V.
Proof. intros U V H p Hp. apply (H p). exact Hp. Qed.

Lemma oincl_antisym : forall U V, oincl U V -> oincl V U -> osame U V.
Proof. intros U V H1 H2 p. split; [apply H1 | apply H2]. Qed.

(* -------------------------------------------------------------------------- *)
(* Metric openness (Euclidean balls).                                         *)
(* -------------------------------------------------------------------------- *)

Definition ball (c : Point) (r : R) : OSet := fun p => dist c p < r.

Definition is_open (U : OSet) : Prop :=
  forall p, U p -> exists eps, 0 < eps /\ forall q, dist p q < eps -> U q.

(* Openness only depends on the pointwise extension. *)
Lemma is_open_ext : forall U V, osame U V -> is_open U -> is_open V.
Proof.
  intros U V Hs HU p Hp.
  destruct (HU p (proj2 (Hs p) Hp)) as [eps [Heps Hball]].
  exists eps. split; [exact Heps |].
  intros q Hq. apply (Hs q). apply Hball. exact Hq.
Qed.

(* -------------------------------------------------------------------------- *)
(* The Heyting operations on truth values.                                    *)
(*                                                                            *)
(* Meet, join and (arbitrary) indexed join are pointwise; implication is the  *)
(* INTERIOR of the pointwise implication -- the largest open with             *)
(* W /\ U <= V, as `heyting_adjunction` below proves.  Negation is            *)
(* implication into bottom, i.e. the interior of the complement.              *)
(* -------------------------------------------------------------------------- *)

Definition otop : OSet := fun _ => True.
Definition obot : OSet := fun _ => False.
Definition oand (U V : OSet) : OSet := fun p => U p /\ V p.
Definition oor  (U V : OSet) : OSet := fun p => U p \/ V p.
Definition ojoin {I : Type} (F : I -> OSet) : OSet := fun p => exists i, F i p.
Definition oimp (U V : OSet) : OSet :=
  fun p => exists eps, 0 < eps /\ forall q, dist p q < eps -> U q -> V q.
Definition onot (U : OSet) : OSet := oimp U obot.

(* -------------------------------------------------------------------------- *)
(* Openness is closed under the Heyting operations.                           *)
(* -------------------------------------------------------------------------- *)

Lemma open_top : is_open otop.
Proof.
  intros p _. exists 1. split; [lra |]. intros q _. exact I.
Qed.

Lemma open_bot : is_open obot.
Proof. intros p Hp. destruct Hp. Qed.

Lemma open_ball : forall c r, is_open (ball c r).
Proof.
  intros c r p Hp. unfold ball in *.
  exists (r - dist c p). split; [lra |].
  intros q Hq.
  pose proof (dist_triangle c p q) as T. lra.
Qed.

Lemma open_and : forall U V, is_open U -> is_open V -> is_open (oand U V).
Proof.
  intros U V HU HV p [Hu Hv].
  destruct (HU p Hu) as [e1 [He1 Hb1]].
  destruct (HV p Hv) as [e2 [He2 Hb2]].
  exists (Rmin e1 e2). split.
  - apply Rmin_glb_lt; assumption.
  - intros q Hq.
    pose proof (Rmin_l e1 e2). pose proof (Rmin_r e1 e2).
    split; [apply Hb1 | apply Hb2]; lra.
Qed.

Lemma open_or : forall U V, is_open U -> is_open V -> is_open (oor U V).
Proof.
  intros U V HU HV p [Hu | Hv].
  - destruct (HU p Hu) as [e [He Hb]].
    exists e. split; [exact He |]. intros q Hq. left. apply Hb. exact Hq.
  - destruct (HV p Hv) as [e [He Hb]].
    exists e. split; [exact He |]. intros q Hq. right. apply Hb. exact Hq.
Qed.

Lemma open_ojoin : forall (I : Type) (F : I -> OSet),
  (forall i, is_open (F i)) -> is_open (ojoin F).
Proof.
  intros I F HF p [i Hi].
  destruct (HF i p Hi) as [e [He Hb]].
  exists e. split; [exact He |]. intros q Hq. exists i. apply Hb. exact Hq.
Qed.

(* Implication is open by construction, with NO openness assumption on the    *)
(* arguments: it is an interior.                                              *)
Lemma open_oimp : forall U V, is_open (oimp U V).
Proof.
  intros U V p [eps [Heps H]].
  exists eps. split; [exact Heps |].
  intros q Hq.
  exists (eps - dist p q). split; [lra |].
  intros s Hs Hu.
  apply (H s); [| exact Hu].
  pose proof (dist_triangle p q s) as T. lra.
Qed.

Lemma open_onot : forall U, is_open (onot U).
Proof. intros U. apply open_oimp. Qed.

(* -------------------------------------------------------------------------- *)
(* Heyting laws.                                                              *)
(* -------------------------------------------------------------------------- *)

(* Modus ponens: evaluate the implication's ball at its own centre. *)
Lemma oimp_elim : forall U V p, (oimp U V) p -> U p -> V p.
Proof.
  intros U V p [eps [Heps H]] Hu.
  apply (H p); [| exact Hu].
  pose proof (dist_refl p). lra.
Qed.

Lemma onot_elim : forall U p, (onot U) p -> U p -> False.
Proof. intros U p Hn Hu. exact (oimp_elim U obot p Hn Hu). Qed.

(* Introduction: an open W with W /\ U <= V lands in the interior. *)
Lemma oimp_intro : forall W U V,
  is_open W -> oincl (oand W U) V -> oincl W (oimp U V).
Proof.
  intros W U V HW Hincl p Hp.
  destruct (HW p Hp) as [eps [Heps Hball]].
  exists eps. split; [exact Heps |].
  intros q Hq Hu. apply (Hincl q). split; [apply Hball; exact Hq | exact Hu].
Qed.

(* The Heyting adjunction: for open W,  W /\ U <= V  <->  W <= (U ==> V).     *)
(* Together with `open_oimp` this says `oimp U V` is the LARGEST open W with  *)
(* W /\ U <= V, i.e. the Heyting implication of the frame O(R^2).             *)
Theorem heyting_adjunction : forall W U V,
  is_open W -> (oincl (oand W U) V <-> oincl W (oimp U V)).
Proof.
  intros W U V HW. split.
  - apply oimp_intro. exact HW.
  - intros H p [Hw Hu]. exact (oimp_elim U V p (H p Hw) Hu).
Qed.

(* The frame law: binary meet distributes over arbitrary joins.  (At the      *)
(* level of pointwise predicates this is pure logic; the frame content is     *)
(* that both sides are opens, by `open_and` + `open_ojoin`.)                  *)
Theorem oand_ojoin_distrib : forall (I : Type) (U : OSet) (F : I -> OSet),
  osame (oand U (ojoin F)) (ojoin (fun i => oand U (F i))).
Proof.
  intros I U F p. split.
  - intros [Hu [i Hi]]. exists i. split; assumption.
  - intros [i [Hu Hi]]. split; [exact Hu | exists i; exact Hi].
Qed.

Lemma oand_oor_distrib : forall U V W,
  osame (oand U (oor V W)) (oor (oand U V) (oand U W)).
Proof. intros U V W p. unfold oand, oor. tauto. Qed.

(* Double negation introduction (needs openness of U: the ball witnessing     *)
(* openness at p refutes any neighbourhood avoiding U).                       *)
Lemma oincl_not_not : forall U, is_open U -> oincl U (onot (onot U)).
Proof.
  intros U HU p Hp.
  destruct (HU p Hp) as [eps [Heps Hball]].
  exists eps. split; [exact Heps |].
  intros q Hq Hn. exact (onot_elim U q Hn (Hball q Hq)).
Qed.

(* Negation swaps top and bottom (the Boolean base cases). *)
Lemma onot_bot_top : osame (onot obot) otop.
Proof.
  intros p. split; [intros _; exact I |].
  intros _. exists 1. split; [lra |]. intros q _ Hf. destruct Hf.
Qed.

Lemma onot_top_bot : osame (onot otop) obot.
Proof.
  intros p. split; [| intros Hf; destruct Hf].
  intros Hn. exact (onot_elim otop p Hn I).
Qed.

(* -------------------------------------------------------------------------- *)
(* The punctured plane: the standard witness that Omega is properly Heyting.  *)
(*                                                                            *)
(* `punct` holds where the point differs from the origin (stated on           *)
(* coordinates, matching Distance.v's characterisations).                     *)
(* -------------------------------------------------------------------------- *)

Definition origin : Point := mkPoint 0 0.

Definition punct : OSet := fun p => ~ (px p = 0 /\ py p = 0).

Lemma punct_open : is_open punct.
Proof.
  intros p Hp.
  assert (Hpos : 0 < dist p origin).
  { apply dist_pos_iff_distinct. simpl. exact Hp. }
  exists (dist p origin). split; [exact Hpos |].
  intros q Hq [Hqx Hqy].
  assert (Hq0 : dist q origin = 0).
  { apply dist_eq_zero_iff. simpl. split; assumption. }
  pose proof (dist_triangle p q origin) as T. lra.
Qed.

(* No point has a neighbourhood avoiding `punct`: every ball contains a point *)
(* off the origin (indeed two distinct points, of which at most one can be    *)
(* the origin).  Fully constructive: the two double negations are combined.   *)
Lemma onot_punct_empty : forall p, ~ (onot punct) p.
Proof.
  intros p [eps [Heps H]].
  (* First: the centre itself would have to be (0,0). *)
  apply (H p).
  { pose proof (dist_refl p). lra. }
  intros [Hx1 Hy1].
  (* Then: so would the centre shifted by eps/2 along x. *)
  apply (H (pt_translate p (eps / 2) 0)).
  { rewrite (dist_lt_iff_dist_sq_lt p (pt_translate p (eps / 2) 0) eps)
      by lra.
    unfold dist_sq, pt_translate. simpl. nra. }
  intros [Hx2 _]. simpl in Hx2. lra.
Qed.

(* Excluded middle fails in Omega: U \/ ~U is not the whole plane for the     *)
(* punctured plane U.  (It misses exactly the origin.)                        *)
Theorem heyting_em_fails : ~ (forall p, (oor punct (onot punct)) p).
Proof.
  intros H.
  destruct (H origin) as [Hp | Hn].
  - apply Hp. simpl. split; reflexivity.
  - exact (onot_punct_empty origin Hn).
Qed.

Corollary heyting_em_fails_osame : ~ osame (oor punct (onot punct)) otop.
Proof.
  intros Hs. apply heyting_em_fails. intros p. apply (Hs p). exact I.
Qed.

(* Double negation is strictly above: ~~U = top but U <> top. *)
Theorem not_not_punct_top : forall p, (onot (onot punct)) p.
Proof.
  intros p. exists 1. split; [lra |].
  intros q _ Hn. exact (onot_punct_empty q Hn).
Qed.

Theorem double_negation_strict : ~ osame (onot (onot punct)) punct.
Proof.
  intros Hs.
  apply (proj1 (Hs origin) (not_not_punct_top origin)).
  simpl. split; reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Non-strict (closed) predicates are not truth values: the closed left       *)
(* half-plane x <= 0 is not open.  (The strict half-plane is; see             *)
(* DiscreteShBridge.v.)                                                       *)
(* -------------------------------------------------------------------------- *)

Theorem closed_halfplane_not_open : ~ is_open (fun p => px p <= 0).
Proof.
  intros H.
  destruct (H origin) as [eps [Heps Hball]]; [simpl; lra |].
  assert (Hin : dist origin (mkPoint (eps / 2) 0) < eps).
  { rewrite (dist_lt_iff_dist_sq_lt origin (mkPoint (eps / 2) 0) eps) by lra.
    unfold dist_sq. simpl. nra. }
  pose proof (Hball (mkPoint (eps / 2) 0) Hin) as Hle.
  simpl in Hle. lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* The infinitary asymmetry: arbitrary joins of opens are open (open_ojoin),  *)
(* but arbitrary meets are not.  The pointwise meet of the open balls         *)
(* ball(origin, r) over all r > 0 is the singleton {origin}, which is not     *)
(* open.  Meets in Omega must therefore be interior-ified; only FINITE meets  *)
(* are computed pointwise.  This is exactly why Omega is a frame / Heyting    *)
(* algebra rather than a complete Boolean algebra.                            *)
(* -------------------------------------------------------------------------- *)

Definition ball_meet : OSet := fun p => forall r, 0 < r -> ball origin r p.

(* Each member of the guarded family is open... *)
Lemma ball_meet_member_open : forall r, is_open (fun p => 0 < r -> ball origin r p).
Proof.
  intros r p Hp.
  destruct (Rlt_dec 0 r) as [Hr | Hr].
  - pose proof (Hp Hr) as Hin. unfold ball in Hin.
    exists (r - dist origin p). split; [lra |].
    intros q Hq _. unfold ball.
    pose proof (dist_triangle origin p q) as T. lra.
  - exists 1. split; [lra |]. intros q _ Hr'. contradiction (Hr Hr').
Qed.

(* ... and the meet is the singleton at the origin ... *)
Lemma ball_meet_char : forall p, ball_meet p <-> (px p = 0 /\ py p = 0).
Proof.
  intros p. split.
  - intros H.
    assert (Hz : dist origin p = 0).
    { pose proof (dist_nonneg origin p) as Hnn.
      assert (Hnlt : ~ 0 < dist origin p).
      { intros Hlt. exact (Rlt_irrefl _ (H (dist origin p) Hlt)). }
      pose proof (Rnot_lt_le _ _ Hnlt). lra. }
    apply dist_eq_zero_iff in Hz. simpl in Hz.
    destruct Hz as [Hx Hy]. split; symmetry; assumption.
  - intros [Hx Hy] r Hr. unfold ball.
    assert (Hz : dist origin p = 0).
    { apply dist_eq_zero_iff. simpl. split; symmetry; assumption. }
    lra.
Qed.

(* ... which is not open ... *)
Lemma singleton_origin_not_open : ~ is_open (fun p => px p = 0 /\ py p = 0).
Proof.
  intros H.
  destruct (H origin) as [eps [Heps Hball]]; [simpl; split; reflexivity |].
  assert (Hin : dist origin (mkPoint (eps / 2) 0) < eps).
  { rewrite (dist_lt_iff_dist_sq_lt origin (mkPoint (eps / 2) 0) eps) by lra.
    unfold dist_sq. simpl. nra. }
  destruct (Hball (mkPoint (eps / 2) 0) Hin) as [Hx _].
  simpl in Hx. lra.
Qed.

(* ... so the infinite pointwise meet of opens fails to be open. *)
Theorem infinite_meet_not_open : ~ is_open ball_meet.
Proof.
  intros H.
  apply singleton_origin_not_open.
  apply (is_open_ext ball_meet); [| exact H].
  intros p. apply ball_meet_char.
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions heyting_adjunction.
Print Assumptions oand_ojoin_distrib.
Print Assumptions open_oimp.
Print Assumptions heyting_em_fails.
Print Assumptions double_negation_strict.
Print Assumptions closed_halfplane_not_open.
Print Assumptions infinite_meet_not_open.

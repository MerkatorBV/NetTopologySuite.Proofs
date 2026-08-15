(* ============================================================================
   NetTopologySuite.Proofs.OverlayNGCurve
   ----------------------------------------------------------------------------
   OverlayNGCurve Phase 0 — GREEN (Qed-closed headline; Red surface
   planted and witnessed in the previous commit).

   Name gate NTSC0001: the lane name is OverlayNGCurve — never
   "OverlayNGCurved".

   The four ops, point-set semantics (ops mnemonics):

     CAP  ∩  intersection    Common Area of Partners     = `oand`
     CUP  ∪  union           Cover Under Partners        = `oor`
     SUB  ∖  difference      Subtract B's shadow         = `odiff`  (new here)
     XOR  Δ  symDifference   keep only what isn't shared = `osym`   (new here)

   What this file is (Phase 0).  The OverlayNGCurve exactness matrix
   classifies op × case cells as EXACT (result returned without
   densification) or APPROX (linearize + OverlayNG, densified).  The
   provable kernel of that classification: a cell is exact precisely when
   the point-set result COLLAPSES to a closed form over the inputs —
   one of A, B, A ∪ B, or ∅.  That is:

     G1  CAP self          A ∩ A = A            (I meet myself → me)
     G2  CUP self          A ∪ A = A            (double pour → same cup)
     G3  SUB self          A ∖ A = ∅            (erase myself → empty)
     G4  XOR self          A Δ A = ∅            (mirror cancel → empty)
     G5  empty partner     A ∩ ∅ = ∅ · A ∪ ∅ = A · A ∖ ∅ = A ·
                           ∅ ∖ A = ∅ · A Δ ∅ = A
     disjoint row          A ∩ B = ∅ · A ∖ B = A · B ∖ A = B ·
                           A Δ B = A ∪ B
     covers row (B ⊆ A)    A ∩ B = B · A ∪ B = A
     coveredBy row (A ⊆ B) A ∩ B = A · A ∪ B = B · A ∖ B = ∅

   GREEN (this rung).  The headline
   `overlayng_curve_phase0_exact_cells` packages all eight blocks, each
   proved as a named lemma (`g1_cap_self` .. `g4_xor_self`,
   `g5_empty_partner`, `disjoint_row_exact`, `covers_row_exact`,
   `coveredby_row_exact`) — every proof is intuitionistic propositional
   logic over the pointwise semantics, so the headline's assumption
   footprint is EMPTY (see the Print Assumptions footer): the Phase-0
   algebra needs no real-number axioms at all.

   This kernel is the soundness of F1 ("fast before fat"): the G1–G5
   algebra and the containment/disjoint collapses may short-circuit
   BEFORE CurveOps.linearise, because in those cells the exact result is
   representable by the inputs as given — no arc is ever densified to
   compute it.  The remaining matrix cells (crossing row; covers-SUB,
   covers-XOR, coveredBy-XOR) produce genuinely new boundaries and stay
   on the linearize path; this rung witnesses that their collapse
   identities really FAIL, on rational squares:

     - crossing pair [0,2]² × [1,3]²: CAP is not ∅, CUP is not A,
       SUB is not A, XOR is not CUP (`probe_crossing_*`);
     - covers pair [0,3]² ⊇ [1,2]²: SUB is neither ∅ nor the outer
       square (`probe_covers_sub_*`) — the rim is a genuinely new
       region, which is exactly why covers-SUB reads "approx" in the
       matrix while covers-CAP and covers-CUP read "exact".

   So the exact/approx frontier drawn by the headline is tight, not
   vacuous.  The exact rows are also instantiated on the pinned pairs
   (`cap_disjoint_squares_empty`, `xor_disjoint_squares_is_cup`,
   `cap_covers_squares_is_inner`, `cup_covers_squares_is_outer`).

   CLAIMS vs PROVES.  The OverlayNGCurve brief also carries: V1–V3
   validity gates (multi-wound shells, hole nesting, type routing),
   R1/R2 representation policy (CurvePolygon retention, approx
   flagging), instance-level G1 ("same instance / equalsExact"), and
   measured densification counts (approx 801/1575/2349/3146/3150 at tip
   f90dfb42).  None of that is provable point-set content: validity and
   retention need a curve REPRESENTATION layer this corpus does not
   define, equalsExact is finer than pointwise equality, and vertex
   counts are engine measurements.  This file PROVES the point-set
   algebra only, stated against `osame`/`oincl` from HeytingOpens.v —
   the same carrier as the bridge lane, so the overlay algebra sits on
   the frame of truth values Omega = O(R^2) rather than on a private
   set theory.

   No `Admitted`, no `Axiom`, no `Parameter`.  The headline and the row
   lemmas are axiom-free (Print Assumptions: closed under the global
   context); only the rational square pins/probes touch R, with a
   classical-reals footprint inside the corpus' three-axiom allowlist
   (their footers show two of the three).

   Registered in `_CoqProject` AND `_CoqProject.full` (host lane: it
   imports Distance and HeytingOpens only).

   Refs: OverlayNGCurve ops mnemonics brief (Phase 0 suite G1–G5, V1–V3,
   R1–R2, F1; exactness matrix at tip f90dfb42); docs page
   docs/overlayng-curve-phase0.md; siblings HeytingOpens.v (carrier),
   OverlayGraph.v / OverlayContactSound.v (the noding-side overlay
   lane, downstream of this algebra).
   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import Distance HeytingOpens.
Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  The two ops HeytingOpens does not already provide.                     *)
(*     CAP = oand and CUP = oor are inherited; SUB and XOR are new.           *)
(* -------------------------------------------------------------------------- *)

(** SUB ∖ — subtract B's shadow: erase the second from the first. *)
Definition odiff (U V : OSet) : OSet := fun p => U p /\ ~ V p.

(** XOR Δ — exclusive or: keep only what isn't shared. *)
Definition osym (U V : OSet) : OSet := oor (odiff U V) (odiff V U).

(** Disjointness of the partners (empty common area). *)
Definition odisjoint (U V : OSet) : Prop := forall p, ~ (U p /\ V p).

(* -------------------------------------------------------------------------- *)
(* §2  The eight blocks of the Phase-0 suite, one lemma each.                 *)
(* -------------------------------------------------------------------------- *)

(** G1 · CAP self — I meet myself → me. *)
Lemma g1_cap_self : forall A : OSet, osame (oand A A) A.
Proof. intros A p. unfold oand. tauto. Qed.

(** G2 · CUP self — double pour → same cup. *)
Lemma g2_cup_self : forall A : OSet, osame (oor A A) A.
Proof. intros A p. unfold oor. tauto. Qed.

(** G3 · SUB self — erase myself → empty. *)
Lemma g3_sub_self : forall A : OSet, osame (odiff A A) obot.
Proof. intros A p. unfold odiff, obot. tauto. Qed.

(** G4 · XOR self — mirror cancel → empty. *)
Lemma g4_xor_self : forall A : OSet, osame (osym A A) obot.
Proof. intros A p. unfold osym, odiff, oor, obot. tauto. Qed.

(** G5 · empty partner — nothing in the room. *)
Lemma g5_empty_partner : forall A : OSet,
  osame (oand A obot) obot /\
  osame (oor A obot) A /\
  osame (odiff A obot) A /\
  osame (odiff obot A) obot /\
  osame (osym A obot) A.
Proof.
  intros A; repeat split;
    unfold osym, odiff, oand, oor, obot in *; tauto.
Qed.

(** Disjoint row of the exactness matrix: with no common area, every op
    collapses — and XOR coincides with CUP. *)
Lemma disjoint_row_exact : forall A B : OSet,
  odisjoint A B ->
  osame (oand A B) obot /\
  osame (odiff A B) A /\
  osame (odiff B A) B /\
  osame (osym A B) (oor A B).
Proof.
  intros A B Hd. unfold odisjoint in Hd.
  repeat split; specialize (Hd p);
    unfold osym, odiff, oand, oor, obot in *; tauto.
Qed.

(** Covers row (A covers B): CAP returns the inner input, CUP the outer. *)
Lemma covers_row_exact : forall A B : OSet,
  oincl B A ->
  osame (oand A B) B /\
  osame (oor A B) A.
Proof.
  intros A B Hc. unfold oincl in Hc.
  repeat split; specialize (Hc p);
    unfold oand, oor in *; tauto.
Qed.

(** CoveredBy row (A covered by B): CAP/CUP collapse to the inputs and
    SUB is empty. *)
Lemma coveredby_row_exact : forall A B : OSet,
  oincl A B ->
  osame (oand A B) A /\
  osame (oor A B) B /\
  osame (odiff A B) obot.
Proof.
  intros A B Hc. unfold oincl in Hc.
  repeat split; specialize (Hc p);
    unfold odiff, oand, oor, obot in *; tauto.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Headline — GREEN.                                                      *)
(* -------------------------------------------------------------------------- *)

(** The Phase-0 exact cells: every cell of the OverlayNGCurve exactness
    matrix marked exact collapses, in point-set semantics, to A, B,
    A ∪ B or ∅ — the soundness kernel of the F1 short-circuit. *)
Theorem overlayng_curve_phase0_exact_cells :
  forall A B : OSet,
    (* G1 · CAP self *) osame (oand A A) A /\
    (* G2 · CUP self *) osame (oor A A) A /\
    (* G3 · SUB self *) osame (odiff A A) obot /\
    (* G4 · XOR self *) osame (osym A A) obot /\
    (* G5 · empty partner *)
    (osame (oand A obot) obot /\
     osame (oor A obot) A /\
     osame (odiff A obot) A /\
     osame (odiff obot A) obot /\
     osame (osym A obot) A) /\
    (* disjoint row *)
    (odisjoint A B ->
       osame (oand A B) obot /\
       osame (odiff A B) A /\
       osame (odiff B A) B /\
       osame (osym A B) (oor A B)) /\
    (* covers row: A covers B *)
    (oincl B A ->
       osame (oand A B) B /\
       osame (oor A B) A) /\
    (* coveredBy row: A covered by B *)
    (oincl A B ->
       osame (oand A B) A /\
       osame (oor A B) B /\
       osame (odiff A B) obot).
Proof.
  intros A B.
  exact (conj (g1_cap_self A)
        (conj (g2_cup_self A)
        (conj (g3_sub_self A)
        (conj (g4_xor_self A)
        (conj (g5_empty_partner A)
        (conj (disjoint_row_exact A B)
        (conj (covers_row_exact A B)
              (coveredby_row_exact A B)))))))).
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Rational square witnesses: the matrix rows are inhabited.              *)
(* -------------------------------------------------------------------------- *)

(** Disjoint pair: [0,1]² and [2,3]². *)
Definition sq_lo : OSet := fun p => 0 <= px p <= 1 /\ 0 <= py p <= 1.
Definition sq_hi : OSet := fun p => 2 <= px p <= 3 /\ 2 <= py p <= 3.

(** Covers pair: [0,3]² covers [1,2]². *)
Definition sq_big : OSet := fun p => 0 <= px p <= 3 /\ 0 <= py p <= 3.
Definition sq_in  : OSet := fun p => 1 <= px p <= 2 /\ 1 <= py p <= 2.

(** Crossing pair: [0,2]² and [1,3]² (overlap [1,2]², neither contains
    the other). *)
Definition sq_a : OSet := fun p => 0 <= px p <= 2 /\ 0 <= py p <= 2.
Definition sq_b : OSet := fun p => 1 <= px p <= 3 /\ 1 <= py p <= 3.

(** Probe points: the shared midpoint, a B-only point, an A-rim point. *)
Definition w_mid : Point := mkPoint (3/2) (3/2).
Definition w_out : Point := mkPoint (5/2) (5/2).
Definition w_rim : Point := mkPoint (1/4) (1/4).

Lemma pin_disjoint_squares : odisjoint sq_lo sq_hi.
Proof.
  intros p [HA HB].
  unfold sq_lo in HA. unfold sq_hi in HB.
  destruct HA as [[_ Hx1] _]. destruct HB as [[Hx2 _] _].
  lra.
Qed.

Lemma pin_covers_squares : oincl sq_in sq_big.
Proof.
  intros p Hp. unfold sq_in in Hp. unfold sq_big.
  destruct Hp as [[Hx1 Hx2] [Hy1 Hy2]].
  repeat split; lra.
Qed.

Lemma w_mid_in_a : sq_a w_mid.
Proof. unfold sq_a, w_mid. simpl. repeat split; lra. Qed.

Lemma w_mid_in_b : sq_b w_mid.
Proof. unfold sq_b, w_mid. simpl. repeat split; lra. Qed.

Lemma w_mid_in_big : sq_big w_mid.
Proof. unfold sq_big, w_mid. simpl. repeat split; lra. Qed.

Lemma w_mid_in_inner : sq_in w_mid.
Proof. unfold sq_in, w_mid. simpl. repeat split; lra. Qed.

Lemma w_out_in_b : sq_b w_out.
Proof. unfold sq_b, w_out. simpl. repeat split; lra. Qed.

Lemma w_out_not_in_a : ~ sq_a w_out.
Proof. unfold sq_a, w_out. simpl. intros [[_ Hx] _]. lra. Qed.

Lemma w_rim_in_big : sq_big w_rim.
Proof. unfold sq_big, w_rim. simpl. repeat split; lra. Qed.

Lemma w_rim_not_in_inner : ~ sq_in w_rim.
Proof. unfold sq_in, w_rim. simpl. intros [[Hx _] _]. lra. Qed.

(* -------------------------------------------------------------------------- *)
(* §5  Exact rows instantiated on the pins (teaching corollaries).            *)
(* -------------------------------------------------------------------------- *)

Corollary cap_disjoint_squares_empty : osame (oand sq_lo sq_hi) obot.
Proof.
  exact (proj1 (disjoint_row_exact sq_lo sq_hi pin_disjoint_squares)).
Qed.

Corollary xor_disjoint_squares_is_cup :
  osame (osym sq_lo sq_hi) (oor sq_lo sq_hi).
Proof.
  exact (proj2 (proj2 (proj2
    (disjoint_row_exact sq_lo sq_hi pin_disjoint_squares)))).
Qed.

Corollary cap_covers_squares_is_inner : osame (oand sq_big sq_in) sq_in.
Proof.
  exact (proj1 (covers_row_exact sq_big sq_in pin_covers_squares)).
Qed.

Corollary cup_covers_squares_is_outer : osame (oor sq_big sq_in) sq_big.
Proof.
  exact (proj2 (covers_row_exact sq_big sq_in pin_covers_squares)).
Qed.

(* -------------------------------------------------------------------------- *)
(* §6  Mismatch probes: the approx cells genuinely fail to collapse.          *)
(*     Crossing row — no op collapses; covers-SUB — the rim is new.           *)
(* -------------------------------------------------------------------------- *)

(** Crossing CAP is not exact-∅: the overlap midpoint is common area. *)
Lemma probe_crossing_cap_not_empty : ~ osame (oand sq_a sq_b) obot.
Proof.
  intros H.
  apply (proj1 (H w_mid)).
  split; [exact w_mid_in_a | exact w_mid_in_b].
Qed.

(** Crossing CUP is not A: the cup holds B-only points too. *)
Lemma probe_crossing_cup_not_left : ~ osame (oor sq_a sq_b) sq_a.
Proof.
  intros H.
  apply w_out_not_in_a.
  apply (proj1 (H w_out)).
  right. exact w_out_in_b.
Qed.

(** Crossing SUB is not A: B's shadow erases the overlap from A. *)
Lemma probe_crossing_sub_not_left : ~ osame (odiff sq_a sq_b) sq_a.
Proof.
  intros H.
  destruct (proj2 (H w_mid) w_mid_in_a) as [_ Hnb].
  exact (Hnb w_mid_in_b).
Qed.

(** Crossing XOR is not CUP: the shared overlap is in the cup but
    cancelled by the mirror. *)
Lemma probe_crossing_xor_not_cup :
  ~ osame (osym sq_a sq_b) (oor sq_a sq_b).
Proof.
  intros H.
  assert (Hor : oor sq_a sq_b w_mid) by (left; exact w_mid_in_a).
  destruct (proj2 (H w_mid) Hor) as [[_ Hnb] | [_ Hna]].
  - exact (Hnb w_mid_in_b).
  - exact (Hna w_mid_in_a).
Qed.

(** Covers-SUB is not exact-∅: the rim point survives the subtraction. *)
Lemma probe_covers_sub_not_empty : ~ osame (odiff sq_big sq_in) obot.
Proof.
  intros H.
  apply (proj1 (H w_rim)).
  split; [exact w_rim_in_big | exact w_rim_not_in_inner].
Qed.

(** Covers-SUB is not the outer square either: the inner overlap is
    erased — the result is a genuinely NEW region (the rim), which is
    why the covers-SUB cell reads approx in the exactness matrix. *)
Lemma probe_covers_sub_not_outer : ~ osame (odiff sq_big sq_in) sq_big.
Proof.
  intros H.
  destruct (proj2 (H w_mid) w_mid_in_big) as [_ Hn].
  exact (Hn w_mid_in_inner).
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.  The headline is axiom-free (pure intuitionistic          *)
(* propositional logic over the pointwise semantics); the pins and probes     *)
(* carry a classical-reals footprint inside the three-axiom allowlist.        *)
(* -------------------------------------------------------------------------- *)

Print Assumptions overlayng_curve_phase0_exact_cells.
Print Assumptions g4_xor_self.
Print Assumptions disjoint_row_exact.
Print Assumptions pin_disjoint_squares.
Print Assumptions probe_crossing_xor_not_cup.
Print Assumptions probe_covers_sub_not_outer.

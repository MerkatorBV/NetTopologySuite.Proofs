(* ============================================================================
   NetTopologySuite.Proofs.OverlayNGCurve
   ----------------------------------------------------------------------------
   OverlayNGCurve Phase 0 — RED (planted surface; exactly ONE unproved
   headline below, failing at Qed).

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

   This kernel is the soundness of F1 ("fast before fat"): the G1–G5
   algebra and the containment/disjoint collapses may short-circuit
   BEFORE CurveOps.linearise, because in those cells the exact result is
   representable by the inputs as given — no arc is ever densified to
   compute it.  The remaining matrix cells (crossing row; covers-SUB,
   covers-XOR, coveredBy-XOR) produce genuinely new boundaries and stay
   on the linearize path; the Green rung witnesses that their collapse
   identities really FAIL (mismatch probes on crossing/covers squares),
   so the exact/approx frontier drawn here is tight, not vacuous.

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

   No `Admitted`, no `Axiom`, no `Parameter`.

   Refs: OverlayNGCurve ops mnemonics brief (Phase 0 suite G1–G5, V1–V3,
   R1–R2, F1; exactness matrix at tip f90dfb42); siblings
   HeytingOpens.v (carrier), OverlayGraph.v / OverlayContactSound.v
   (the noding-side overlay lane, downstream of this algebra).
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
(* §2  Headline — RED.  The Phase-0 exact cells: every cell of the           *)
(*     exactness matrix marked exact collapses, in point-set semantics,      *)
(*     to A, B, A ∪ B or ∅.                                                  *)
(* -------------------------------------------------------------------------- *)

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
  (* RED: stated, not yet proved — this Qed is the witnessed Red gate. *)
Qed.

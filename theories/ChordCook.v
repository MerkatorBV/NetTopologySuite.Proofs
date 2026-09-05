(* ============================================================================
   NetTopologySuite.Proofs.ChordCook
   ----------------------------------------------------------------------------
   First inhabitant of ADR-0007: the intersection oracle I for two chords on
   the sheet R^2.  Host lane, exact reals, no Flocq, no lattice, no arcs.

   ADR-0007 was a requirement with no `.v` behind it.  This is the first
   proof term that inhabits it.

   SCOPE, exactly.  Sheet = R^2, so there is no sheet parameter and no
   Decline: for two chords on R^2 the oracle is TOTAL.  Decline belongs to an
   egg class with no algorithm on the sheet, which is a later rung.  An
   earlier draft of this file used Decline for a vanishing determinant; that
   was wrong.  A vanishing determinant is Overlap or disjointness -- an
   outcome, not a refusal.

   WHAT IS PROVED HERE (Qed): the HIT lemma.

     If orient(A,B,C)*orient(A,B,D) < 0 and orient(C,D,A)*orient(C,D,B) < 0
     then there are t, s in the OPEN interval (0,1) with
     gamma_AB(t) = gamma_CD(s), and they are unique.

   The two strict products are the standard proper-crossing test.  They give
   the denominator for free: orient(C,D,A) - orient(C,D,B) = det, and
   opposite signs make a difference nonzero, so no separate non-degeneracy
   hypothesis is needed and no case analysis on det is performed.

   WHAT IS NOT PROVED, in the order ADR-0007's route puts them:

     - MISS.  Four nonzero orientations whose products are not both negative
       imply the pieces are disjoint.  Not attempted.
     - SPLIT-NODED.  After splitting every properly crossing pair at its
       parameter and identifying the new endpoints, any two pieces that meet
       do so at a shared endpoint.  THAT sentence is `fully_intersected`, and
       under ADR-0007 it must be the CONCLUSION of the cook rather than a
       hypothesis.  Every corpus theorem that currently takes
       `fully_intersected` as input is waiting on it.  Not attempted.
     - OVERLAP.  Collinear pieces meeting in a segment of positive length are
       a separate case and not a point constructor.  Not attempted.
     - Bounded-bit-length and floating realisations (LN; Priest 1991 §7,
       doi:10.1109/ARITH.1991.145549).  Not attempted.
     - IDENTITY.  Whether two hits at the same point of the sheet are one hen
       or two.  Open in ADR-0007 and open here.

   So this file does not yet let anything delete `fully_intersected` from a
   hypothesis list.  It supplies the first of the three lemmas that would.

   AXIOM FOOTPRINT, measured 2026-09-05 on Rocq 9.2.0.  Two axioms:

       ClassicalDedekindReals.sig_forall_dec
       FunctionalExtensionality.functional_extensionality_dep

   No `Classical_Prop.classic`, and not even `sig_not_dec` -- below the
   corpus's three-axiom floor.  That is structural, not luck: existence of
   the crossing point is the vanishing of two linear forms, and the file
   never reaches the Flocq format layer where `classic` enters elsewhere.
   Emitted by the `Print Assumptions` block at the end, so the audit reads it
   from the build log rather than from this comment.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import Distance.

Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* Chords on R^2.  A chord is a pair of points; its law is affine in t.        *)
(* No Geometry type, no subclass: the objects are points and pairs of points.  *)
(* -------------------------------------------------------------------------- *)

Definition chord_eval (A B : Point) (t : R) : Point :=
  mkPoint ((1 - t) * px A + t * px B)
          ((1 - t) * py A + t * py B).

(* The degree-2 orientation determinant.  Its SIGN is a predicate; the value
   is what the constructor below divides with. *)
Definition orient (P Q R0 : Point) : R :=
  (px Q - px P) * (py R0 - py P) - (py Q - py P) * (px R0 - px P).

(* The direction determinant of the two chords. *)
Definition chord_det (A B C D : Point) : R :=
  (px B - px A) * (py D - py C) - (py B - py A) * (px D - px C).

(* -------------------------------------------------------------------------- *)
(* The two identities that make the hit lemma need no extra hypothesis:       *)
(* both parameter denominators ARE the direction determinant, up to sign.     *)
(* -------------------------------------------------------------------------- *)

Lemma orient_diff_CD :
  forall A B C D : Point,
    orient C D A - orient C D B = chord_det A B C D.
Proof. intros; unfold orient, chord_det; ring. Qed.

Lemma orient_diff_AB :
  forall A B C D : Point,
    orient A B C - orient A B D = - chord_det A B C D.
Proof. intros; unfold orient, chord_det; ring. Qed.

(* The crossing parameters. *)
Definition chord_t (A B C D : Point) : R :=
  orient C D A / chord_det A B C D.

Definition chord_s (A B C D : Point) : R :=
  - orient A B C / chord_det A B C D.

(* -------------------------------------------------------------------------- *)
(* Opposite strict signs force the determinant nonzero, and pin the           *)
(* parameter strictly inside (0,1).                                           *)
(* -------------------------------------------------------------------------- *)

Lemma det_nonzero_of_opposite :
  forall A B C D : Point,
    orient C D A * orient C D B < 0 -> chord_det A B C D <> 0.
Proof.
  intros A B C D Hprod.
  rewrite <- orient_diff_CD.
  intro Hz.
  assert (Heq : orient C D A = orient C D B) by lra.
  rewrite Heq in Hprod.
  nra.
Qed.

Lemma ratio_in_open_unit :
  forall a d : R,
    a * (a - d) < 0 -> 0 < a / d < 1.
Proof.
  intros a d Hprod.
  assert (Hd : d <> 0) by (intro Hz; subst; nra).
  assert (Hd2 : 0 < d * d)
    by (pose proof (Rlt_0_sqr d Hd) as Hs; unfold Rsqr in Hs; exact Hs).
  assert (Har : a = (a / d) * d) by (field; exact Hd).
  (* Make the quotient an opaque variable so nothing below contains a
     division: what remains is polynomial in r and d, which nra can do. *)
  set (r := a / d) in *.
  clearbody r.
  rewrite Har in Hprod.
  (* Hprod : r*d*(r*d - d) < 0, i.e. d^2 * (r^2 - r) < 0.  With d^2 > 0 this
     is r*(r-1) < 0, which pins r strictly inside (0,1). *)
  assert (Hrr : r * (r - 1) < 0) by nra.
  split; nra.
Qed.

(* -------------------------------------------------------------------------- *)
(* THE HIT LEMMA.                                                             *)
(* -------------------------------------------------------------------------- *)

Theorem chord_hit :
  forall A B C D : Point,
    orient A B C * orient A B D < 0 ->
    orient C D A * orient C D B < 0 ->
    let t := chord_t A B C D in
    let s := chord_s A B C D in
    0 < t < 1 /\ 0 < s < 1 /\ chord_eval A B t = chord_eval C D s.
Proof.
  intros A B C D HAB HCD.
  assert (Hd : chord_det A B C D <> 0) by (apply det_nonzero_of_opposite; exact HCD).
  simpl.
  repeat split.
  (* t in (0,1) *)
  - unfold chord_t.
    apply (ratio_in_open_unit (orient C D A) (chord_det A B C D)).
    rewrite <- orient_diff_CD.
    replace (orient C D A - (orient C D A - orient C D B))
      with (orient C D B) by ring.
    exact HCD.
  - unfold chord_t.
    apply (ratio_in_open_unit (orient C D A) (chord_det A B C D)).
    rewrite <- orient_diff_CD.
    replace (orient C D A - (orient C D A - orient C D B))
      with (orient C D B) by ring.
    exact HCD.
  (* s in (0,1) *)
  - unfold chord_s.
    apply (ratio_in_open_unit (- orient A B C) (chord_det A B C D)).
    rewrite <- (Ropp_involutive (chord_det A B C D)).
    rewrite <- orient_diff_AB.
    replace (- orient A B C - - (orient A B C - orient A B D))
      with (- orient A B D) by ring.
    nra.
  - unfold chord_s.
    apply (ratio_in_open_unit (- orient A B C) (chord_det A B C D)).
    rewrite <- (Ropp_involutive (chord_det A B C D)).
    rewrite <- orient_diff_AB.
    replace (- orient A B C - - (orient A B C - orient A B D))
      with (- orient A B D) by ring.
    nra.
  (* the two evaluations agree *)
  - unfold chord_eval, chord_t, chord_s, orient, chord_det in *.
    apply f_equal2; field; assumption.
Qed.

(* Uniqueness: the parameters are determined, so the crossing point is. *)
Theorem chord_hit_unique :
  forall A B C D : Point,
    chord_det A B C D <> 0 ->
    forall t1 s1 t2 s2 : R,
      chord_eval A B t1 = chord_eval C D s1 ->
      chord_eval A B t2 = chord_eval C D s2 ->
      t1 = t2 /\ s1 = s2.
Proof.
  intros A B C D Hd t1 s1 t2 s2 H1 H2.
  unfold chord_eval in H1, H2.
  injection H1 as H1x H1y.
  injection H2 as H2x H2y.
  (* Subtracting the two crossings: (t1-t2)*u = (s1-s2)*v componentwise. *)
  assert (Hx : (t1 - t2) * (px B - px A) = (s1 - s2) * (px D - px C)) by lra.
  assert (Hy : (t1 - t2) * (py B - py A) = (s1 - s2) * (py D - py C)) by lra.
  (* Pair each against the other direction: the v-terms cancel, leaving
     (t1-t2)*det = 0, and symmetrically (s1-s2)*det = 0. *)
  assert (Hdt : (t1 - t2) * chord_det A B C D = 0).
  { unfold chord_det.
    replace ((t1 - t2) * ((px B - px A) * (py D - py C)
                          - (py B - py A) * (px D - px C)))
      with (((t1 - t2) * (px B - px A)) * (py D - py C)
            - ((t1 - t2) * (py B - py A)) * (px D - px C)) by ring.
    rewrite Hx, Hy. ring. }
  assert (Hds : (s1 - s2) * chord_det A B C D = 0).
  { unfold chord_det.
    replace ((s1 - s2) * ((px B - px A) * (py D - py C)
                          - (py B - py A) * (px D - px C)))
      with ((px B - px A) * ((s1 - s2) * (py D - py C))
            - (py B - py A) * ((s1 - s2) * (px D - px C))) by ring.
    rewrite <- Hx, <- Hy. ring. }
  split.
  - destruct (Rmult_integral _ _ Hdt) as [H | H]; [ lra | contradiction ].
  - destruct (Rmult_integral _ _ Hds) as [H | H]; [ lra | contradiction ].
Qed.

(* -------------------------------------------------------------------------- *)
(* Assumption audit.                                                          *)
(* -------------------------------------------------------------------------- *)

Print Assumptions orient_diff_CD.
Print Assumptions det_nonzero_of_opposite.
Print Assumptions ratio_in_open_unit.
Print Assumptions chord_hit.
Print Assumptions chord_hit_unique.

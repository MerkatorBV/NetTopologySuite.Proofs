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

   That is a SUBSET of the corpus's three-axiom allowlist, not something
   below it: `sig_forall_dec` is Dedekind choice and is still an axiom.  The
   precise claim is narrower and is the one that matters here -- no excluded
   middle is used for the EXISTENCE of the crossing, which is the vanishing
   of two linear forms.  The file also never reaches the Flocq format layer,
   which is where `Classical_Prop.classic` enters elsewhere in the corpus.
   Emitted by the `Print Assumptions` block at the end, so the audit reads it
   from the build log rather than from this comment.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra Lists.List.
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

(* --------------------------------------------------------------------------
   THE MISS LEMMA.

   If the four orientations are nonzero and the two products are not both
   negative, the pieces are disjoint.

   The whole argument is one algebraic fact: `orient A B _` is AFFINE in its
   third argument, so a point of [CD] carries the convex combination
   (1-s)*orient(A,B,C) + s*orient(A,B,D).  Two orientations of the same
   strict sign therefore never produce zero on [0,1], and a point of [AB] has
   orientation zero against AB.  No case analysis on the geometry.
   -------------------------------------------------------------------------- *)

Lemma orient_affine_third :
  forall P Q C D (s : R),
    orient P Q (chord_eval C D s)
    = (1 - s) * orient P Q C + s * orient P Q D.
Proof. intros; unfold orient, chord_eval; simpl; ring. Qed.

Lemma orient_on_own_chord :
  forall A B (t : R), orient A B (chord_eval A B t) = 0.
Proof. intros; unfold orient, chord_eval; simpl; ring. Qed.

(* Same strict sign on both endpoints: nothing on [CD] reaches line AB. *)
Lemma same_side_orient_nonzero :
  forall A B C D (s : R),
    0 <= s <= 1 ->
    0 < orient A B C * orient A B D ->
    orient A B (chord_eval C D s) <> 0.
Proof.
  intros A B C D s Hs Hpos.
  rewrite orient_affine_third.
  (* both factors positive, or both negative *)
  destruct (total_order_T (orient A B C) 0) as [[Hc | Hc] | Hc].
  - assert (Hd : orient A B D < 0) by nra. nra.
  - rewrite Hc in Hpos. nra.
  - assert (Hd : 0 < orient A B D) by nra. nra.
Qed.

Theorem chord_miss :
  forall A B C D : Point,
    orient A B C <> 0 -> orient A B D <> 0 ->
    orient C D A <> 0 -> orient C D B <> 0 ->
    ~ (orient A B C * orient A B D < 0 /\ orient C D A * orient C D B < 0) ->
    forall t s : R,
      0 <= t <= 1 -> 0 <= s <= 1 ->
      chord_eval A B t <> chord_eval C D s.
Proof.
  intros A B C D HC HD HA HB Hnot t s Ht Hs Hmeet.
  (* Products of nonzeros are nonzero, so each is strictly signed. *)
  assert (Hp : orient A B C * orient A B D <> 0)
    by (intro Hz; destruct (Rmult_integral _ _ Hz); contradiction).
  assert (Hq : orient C D A * orient C D B <> 0)
    by (intro Hz; destruct (Rmult_integral _ _ Hz); contradiction).
  (* Not both negative, so at least one pair lies strictly on one side. *)
  assert (Hside : 0 < orient A B C * orient A B D
                  \/ 0 < orient C D A * orient C D B).
  { destruct (total_order_T (orient A B C * orient A B D) 0) as [[H1|H1]|H1].
    - right. destruct (total_order_T (orient C D A * orient C D B) 0)
        as [[H2|H2]|H2]; [ exfalso; apply Hnot; split; assumption
                         | contradiction | exact H2 ].
    - contradiction.
    - left; exact H1. }
  destruct Hside as [Hside | Hside].
  - (* C and D strictly on one side of AB: [CD] never meets line AB. *)
    apply (same_side_orient_nonzero A B C D s Hs Hside).
    rewrite <- Hmeet. apply orient_on_own_chord.
  - (* A and B strictly on one side of CD: [AB] never meets line CD. *)
    apply (same_side_orient_nonzero C D A B t Ht Hside).
    rewrite Hmeet. apply orient_on_own_chord.
Qed.

(* --------------------------------------------------------------------------
   CASE 3 -- det = 0.  Splits in two, and only one half is a miss.

   `chord_det = 0` says the directions are parallel.  Two sub-cases:

     (3a) PARALLEL, DISTINCT LINES: some endpoint of CD is off line AB.
          Then nothing on [CD] ever reaches line AB, so the pieces are
          disjoint.  Qed below.
     (3b) COLLINEAR: all four points on one line.  This is where OVERLAP
          lives, and where the QEX below comes from.  Not a miss and not a
          point constructor: the intersection can be a subsegment.

   For (3a) the affine identity does all the work again.  det = 0 gives
   orient A B D = orient A B C by `orient_diff_AB`, so the convex
   combination along [CD] is CONSTANT and equal to that common value.  One
   endpoint off the line therefore keeps the whole piece off it.
   -------------------------------------------------------------------------- *)

Lemma orient_const_along_parallel :
  forall A B C D (s : R),
    chord_det A B C D = 0 ->
    orient A B (chord_eval C D s) = orient A B C.
Proof.
  intros A B C D s Hdet.
  rewrite orient_affine_third.
  assert (Heq : orient A B D = orient A B C).
  { pose proof (orient_diff_AB A B C D) as H. rewrite Hdet in H. lra. }
  rewrite Heq. ring.
Qed.

Theorem chord_parallel_distinct_miss :
  forall A B C D : Point,
    chord_det A B C D = 0 ->
    orient A B C <> 0 ->
    forall t s : R, chord_eval A B t <> chord_eval C D s.
Proof.
  intros A B C D Hdet Hoff t s Hmeet.
  apply Hoff.
  rewrite <- (orient_const_along_parallel A B C D s Hdet).
  rewrite <- Hmeet.
  apply orient_on_own_chord.
Qed.

(* (3b) COLLINEAR is not proved here.  Under `det = 0` AND
   `orient A B C = 0` every point involved lies on one line, and the meeting
   condition reduces to a one-dimensional parameter equation: writing
   C = chord_eval A B c and D = chord_eval A B d (which exist because
   A <> B), the pieces meet at (t,s) exactly when t = (1-s)*c + s*d.  The
   intersection is then a subsegment whenever [0,1] and the interval spanned
   by c and d share positive length -- which is the OVERLAP outcome, not a
   point, and so not something a point constructor may return.

   `chord_split_noded_hypothesis_free_false` below is an instance of exactly
   this sub-case: it is the specification of the missing lemma, not a
   substitute for it. *)

(* --------------------------------------------------------------------------
   SPLIT-NODED, and why the obvious statement of it is false.

   The intended third lemma is: once no pair of G1 satisfies both strict
   product inequalities, any meeting of two pieces is at an endpoint --
   i.e. `fully_intersected` as a CONCLUSION.

   Stated with only that hypothesis it is REFUTABLE, and the refutation is
   exactly the case the route says to classify separately: collinear overlap.
   Take four points on the x-axis,

       A = (0,0)   B = (2,0)   C = (1,0)   D = (3,0)

   Every orientation among them is 0, so every product is 0 and the
   "no crossing pair remains" hypothesis holds VACUOUSLY.  Yet [AB] and [CD]
   share the subsegment from (1,0) to (2,0): t = 3/4 and s = 1/4 both land on
   (3/2, 0), and neither parameter is an endpoint.

   So the hypothesis-free form cannot be Qed.  QEX, with the witness below.
   The repair is not to strengthen the no-crossing hypothesis but to exclude
   the parallel case, `chord_det <> 0`, which is what "classify overlap
   separately" means in the type.  That corrected statement is the next rung
   and is NOT proved here.
   -------------------------------------------------------------------------- *)

Definition cex_A : Point := mkPoint 0 0.
Definition cex_B : Point := mkPoint 2 0.
Definition cex_C : Point := mkPoint 1 0.
Definition cex_D : Point := mkPoint 3 0.

Definition cex_G1 : list (Point * Point) :=
  cons (cex_A, cex_B) (cons (cex_C, cex_D) nil).

Theorem chord_split_noded_hypothesis_free_false :
  exists (G1 : list (Point * Point)) (AB CD : Point * Point) (t s : R),
    (forall X Y : Point * Point,
        In X G1 -> In Y G1 ->
        orient (fst X) (snd X) (fst Y) * orient (fst X) (snd X) (snd Y) < 0 ->
        orient (fst Y) (snd Y) (fst X) * orient (fst Y) (snd Y) (snd X) < 0 ->
        False)
    /\ In AB G1 /\ In CD G1
    /\ 0 <= t <= 1 /\ 0 <= s <= 1
    /\ chord_eval (fst AB) (snd AB) t = chord_eval (fst CD) (snd CD) s
    /\ t <> 0 /\ t <> 1 /\ s <> 0 /\ s <> 1.
Proof.
  exists cex_G1, (cex_A, cex_B), (cex_C, cex_D), (3/4), (1/4).
  repeat split.
  - (* every orientation among four collinear points vanishes *)
    intros X Y HX HY H1 H2.
    unfold cex_G1 in HX, HY; simpl in HX, HY.
    destruct HX as [HX | [HX | HX]]; try contradiction; subst X;
    destruct HY as [HY | [HY | HY]]; try contradiction; subst Y;
    unfold orient, cex_A, cex_B, cex_C, cex_D in H1; simpl in H1; lra.
  - unfold cex_G1; simpl; left; reflexivity.
  - unfold cex_G1; simpl; right; left; reflexivity.
  - lra.
  - lra.
  - lra.
  - lra.
  - unfold chord_eval, cex_A, cex_B, cex_C, cex_D; simpl.
    apply f_equal2; lra.
  - lra.
  - lra.
  - lra.
  - lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Assumption audit.                                                          *)
(* -------------------------------------------------------------------------- *)

Print Assumptions orient_diff_CD.
Print Assumptions det_nonzero_of_opposite.
Print Assumptions ratio_in_open_unit.
Print Assumptions chord_hit.
Print Assumptions chord_hit_unique.
Print Assumptions orient_affine_third.
Print Assumptions same_side_orient_nonzero.
Print Assumptions chord_miss.
Print Assumptions chord_parallel_distinct_miss.
Print Assumptions chord_split_noded_hypothesis_free_false.

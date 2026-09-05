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

   WHAT IS PROVED HERE (Qed).  The pair oracle is complete: for two chords
   on the sheet, every configuration is decided.

     chord_hit / chord_hit_unique
       Proper crossing.  If orient(A,B,C)*orient(A,B,D) < 0 and
       orient(C,D,A)*orient(C,D,B) < 0 then there are UNIQUE t, s in the
       OPEN interval (0,1) with gamma_AB(t) = gamma_CD(s).  The two strict
       products give the denominator for free -- orient(C,D,A) -
       orient(C,D,B) = det, and opposite signs make a difference nonzero --
       so no non-degeneracy hypothesis is assumed and no case analysis on
       det is performed.

     chord_miss
       Same side.  If C and D are strictly on one side of AB, no pair of
       parameters in [0,1] meets.  Empty, not Decline.

     chord_parallel_distinct_miss
       det = 0 with orient(A,B,C) <> 0: parallel and distinct, disjoint.

     chord_collinear_overlap / chord_collinear_from_points
       det = 0 with both orientations 0: the meet is an interval in the
       parameter, classified by `classify_collinear` as CollMiss, CollTouch
       or CollOverlap.  An overlap is a shared SUBSEGMENT, not a point, and
       therefore not something the point constructor may return.

     chord_split_noded
       The pairwise conclusion.  On a family G1 in which no two members
       cross properly, any meeting of two members happens at an endpoint of
       one of them, or else the two are collinear -- in which case the meet
       is the subsegment `chord_collinear_overlap` produces.  This is
       stated with NO det <> 0 guard: the degenerate cases are inside the
       disjunction rather than excluded by hypothesis.

     chord_split_noded_hypothesis_free_false
       The QEX.  Dropping the no-crossing hypothesis makes the statement
       FALSE, witnessed by A=(0,0), B=(2,0), C=(1,0), D=(3,0), where
       t = 3/4 and s = 1/4 both evaluate to (3/2,0) with no endpoint and no
       proper crossing.  Collinear overlap is the obstruction, and it is why
       the collinear disjunct above is not decoration.

   WHAT IS NOT PROVED, and what that costs.

     - THE LOOP (the cook).  There is no function here sending an arbitrary
       family G0 to a G1 satisfying `chord_split_noded`'s hypothesis, and no
       termination argument for one.  Until that exists, this file proves a
       property OF a noded family; it does not node anything.  That is the
       whole distance between `fully_intersected` as a hypothesis and
       `fully_intersected` as a conclusion, and it is not crossed here.
     - THE GRID.  Rounding to Lambda = h*Z^2 and showing two rounded edges
       meet iff they share an endpoint.  Obligation (3).  Not attempted, and
       when it is, it must not assume the conclusion of the loop.
     - IDENTITY.  Whether two hits at the same point of the sheet are one
       hen or two.  Open in ADR-0007 and open here.
     - Bounded-bit-length and floating realisations (Priest 1991 section 7,
       doi:10.1109/ARITH.1991.145549).  Everything here is exact reals.

   ACCOUNTING.  CAP, CUP, SUB and XOR (SQL/MM 5.1.31--36) are four filters
   over ONE noded graph.  With no graph, all four stand at zero.  Nothing in
   this file is a fraction of an overlay operation; these are lemmas that an
   overlay is permitted to call once something builds the graph.  No
   hypothesis has been deleted from any corpus theorem: see
   docs/lemmas-under-constructor.txt, still seven entries.

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

(* --------------------------------------------------------------------------
   (3b) COLLINEAR -- the reduction to one dimension.

   Under `orient A B C = 0` and A <> B, C lies on the line through A and B,
   so it HAS a parameter: C = chord_eval A B c.  Same for D.  Once both are
   parameters, the meeting condition stops being geometry:

       chord_eval A B t = chord_eval C D s   <->   t = (1-s)*c + s*d

   and the intersection of the two pieces is the intersection of [0,1] with
   the interval spanned by c and d.  Empty, one point, or a subsegment --
   the three outcomes, now an interval question on R with no DOI attached.

   These two lemmas are what make `chord_collinear` a one-dimensional
   classification rather than a plane-geometry case analysis.  The
   classification itself is the next term.
   -------------------------------------------------------------------------- *)

(* The parameter comes from whichever component of B - A is nonzero.  The
   division is introduced once, as an equation, so nothing below has to
   divide. *)
Lemma collinear_param_x :
  forall A B C : Point,
    px B - px A <> 0 ->
    orient A B C = 0 ->
    C = chord_eval A B ((px C - px A) / (px B - px A)).
Proof.
  intros A B C Hx Hor.
  unfold orient in Hor. unfold chord_eval.
  destruct C as [cx cy]; simpl in *.
  remember ((cx - px A) / (px B - px A)) as k eqn:Hk.
  assert (Hkx : k * (px B - px A) = cx - px A)
    by (rewrite Hk; field; exact Hx).
  assert (Hky : k * (py B - py A) = cy - py A).
  { apply (Rmult_eq_reg_l (px B - px A)); [ nra | exact Hx ]. }
  apply f_equal2; nra.
Qed.

Lemma collinear_param_y :
  forall A B C : Point,
    py B - py A <> 0 ->
    orient A B C = 0 ->
    C = chord_eval A B ((py C - py A) / (py B - py A)).
Proof.
  intros A B C Hy Hor.
  unfold orient in Hor. unfold chord_eval.
  destruct C as [cx cy]; simpl in *.
  remember ((cy - py A) / (py B - py A)) as k eqn:Hk.
  assert (Hky : k * (py B - py A) = cy - py A)
    by (rewrite Hk; field; exact Hy).
  assert (Hkx : k * (px B - px A) = cx - px A).
  { apply (Rmult_eq_reg_l (py B - py A)); [ nra | exact Hy ]. }
  apply f_equal2; nra.
Qed.

Lemma collinear_param_exists :
  forall A B C : Point,
    (px A <> px B \/ py A <> py B) ->
    orient A B C = 0 ->
    exists c : R, C = chord_eval A B c.
Proof.
  intros A B C Hne Hor.
  destruct (total_order_T (px B - px A) 0) as [[Hx | Hx] | Hx].
  - eexists. apply collinear_param_x; [ lra | exact Hor ].
  - assert (Hy : py B - py A <> 0)
      by (destruct Hne as [H | H]; [ exfalso; apply H; lra | lra ]).
    eexists. apply collinear_param_y; [ exact Hy | exact Hor ].
  - eexists. apply collinear_param_x; [ lra | exact Hor ].
Qed.

Lemma collinear_meet_iff :
  forall A B (c d t s : R),
    (px A <> px B \/ py A <> py B) ->
    (chord_eval A B t = chord_eval (chord_eval A B c) (chord_eval A B d) s
     <-> t = (1 - s) * c + s * d).
Proof.
  intros A B c d t s Hne.
  unfold chord_eval; simpl.
  split.
  - intro H. injection H as Hx Hy.
    destruct Hne as [Hn | Hn]; nra.
  - intro H. subst t. apply f_equal2; ring.
Qed.

(* --------------------------------------------------------------------------
   (3b) COLLINEAR -- the three outcomes.

   With both pieces reduced to parameters on AB, the intersection is
   [0,1] cap [min c d, max c d].  Write

       lo = Rmax 0 (Rmin c d)      hi = Rmin 1 (Rmax c d)

   Then lo > hi is MISS, lo = hi is a single shared point, and lo < hi is a
   shared SUBSEGMENT.  The last is the case overlay actually meets in
   cadastral data, and it is the one a point constructor must refuse: the
   answer is an interval, so `chord_hit` has nothing to return.

   `chord_collinear_overlap` is that constructor.  It does not produce one
   vertex; it produces the whole shared parameter interval, which is what
   CAP of two overlapping chords has to be.
   -------------------------------------------------------------------------- *)

Inductive CollinearMeet : Type :=
  | CollMiss
  | CollTouch   (t : R)
  | CollOverlap (lo hi : R).

Definition classify_collinear (c d : R) : CollinearMeet :=
  let lo := Rmax 0 (Rmin c d) in
  let hi := Rmin 1 (Rmax c d) in
  match total_order_T lo hi with
  | inleft (left _)  => CollOverlap lo hi
  | inleft (right _) => CollTouch lo
  | inright _        => CollMiss
  end.

(* The shared subsegment is genuinely shared: EVERY parameter in [lo,hi]
   is a meeting point of the two pieces.  Not a vertex -- an interval. *)
Theorem chord_collinear_overlap :
  forall A B (c d : R),
    (px A <> px B \/ py A <> py B) ->
    forall lo hi,
      classify_collinear c d = CollOverlap lo hi ->
      lo < hi /\
      (forall t : R, lo <= t <= hi ->
        0 <= t <= 1 /\
        (exists s : R, 0 <= s <= 1 /\
          chord_eval A B t
          = chord_eval (chord_eval A B c) (chord_eval A B d) s)).
Proof.
  intros A B c d Hne lo hi Hcl.
  unfold classify_collinear in Hcl.
  destruct (total_order_T (Rmax 0 (Rmin c d)) (Rmin 1 (Rmax c d)))
    as [[Hlt | Heq] | Hgt]; try discriminate.
  injection Hcl as Hlo Hhi. subst lo hi.
  split; [ exact Hlt | ].
  intros t Ht.
  (* Bounds on Rmin/Rmax, supplied explicitly: lra cannot reason about them. *)
  assert (Hmax0 : 0 <= Rmax 0 (Rmin c d)) by apply Rmax_l.
  assert (Hmin1 : Rmin 1 (Rmax c d) <= 1) by apply Rmin_l.
  assert (Hminle : Rmin c d <= Rmax 0 (Rmin c d)) by apply Rmax_r.
  assert (Hmaxge : Rmin 1 (Rmax c d) <= Rmax c d) by apply Rmin_r.
  assert (H01 : 0 <= t <= 1) by lra.
  assert (Hin : Rmin c d <= t <= Rmax c d) by lra.
  split; [ exact H01 | ].
  (* A degenerate interval cannot satisfy lo < hi. *)
  assert (Hcd : c <> d).
  { intro Hz. subst d.
    replace (Rmin c c) with c in *
      by (unfold Rmin; destruct (Rle_dec c c); reflexivity).
    replace (Rmax c c) with c in *
      by (unfold Rmax; destruct (Rle_dec c c); reflexivity).
    lra. }
  assert (Hdc : d - c <> 0) by lra.
  exists ((t - c) / (d - c)).
  assert (Hs : t - c = ((t - c) / (d - c)) * (d - c)) by (field; exact Hdc).
  set (r := (t - c) / (d - c)) in *.
  clearbody r.
  split.
  - destruct (Rle_dec c d) as [Hle | Hle].
    + replace (Rmin c d) with c in Hin
        by (unfold Rmin; destruct (Rle_dec c d); [ reflexivity | lra ]).
      replace (Rmax c d) with d in Hin
        by (unfold Rmax; destruct (Rle_dec c d); [ reflexivity | lra ]).
      nra.
    + replace (Rmin c d) with d in Hin
        by (unfold Rmin; destruct (Rle_dec c d); [ lra | reflexivity ]).
      replace (Rmax c d) with c in Hin
        by (unfold Rmax; destruct (Rle_dec c d); [ lra | reflexivity ]).
      nra.
  - apply (collinear_meet_iff A B c d t r Hne). nra.
Qed.

(* --------------------------------------------------------------------------
   FROM FOUR POINTS TO THE CLASSIFICATION.

   `chord_collinear_overlap` speaks about parameters c, d that are already on
   the line of AB.  OverlayNG's COLLINEAR branch starts from four
   `Coordinate`s.  This is the step between: given the degeneracies, project
   C and D onto AB's parameter line and hand the classification the numbers
   it needs.
   -------------------------------------------------------------------------- *)

Theorem chord_collinear_from_points :
  forall A B C D : Point,
    (px A <> px B \/ py A <> py B) ->
    orient A B C = 0 ->
    orient A B D = 0 ->
    exists c d : R,
      C = chord_eval A B c /\
      D = chord_eval A B d /\
      forall lo hi,
        classify_collinear c d = CollOverlap lo hi ->
        lo < hi /\
        (forall t : R, lo <= t <= hi ->
           0 <= t <= 1 /\
           (exists s : R, 0 <= s <= 1 /\
              chord_eval A B t = chord_eval C D s)).
Proof.
  intros A B C D Hne HC HD.
  destruct (collinear_param_exists A B C Hne HC) as [c Hc].
  destruct (collinear_param_exists A B D Hne HD) as [d Hd].
  exists c, d.
  split; [ exact Hc | ].
  split; [ exact Hd | ].
  intros lo hi Hcl.
  rewrite Hc, Hd.
  apply (chord_collinear_overlap A B c d Hne lo hi Hcl).
Qed.

(* --------------------------------------------------------------------------
   THE CONVERSE OF THE PARAMETER BOUND.

   `ratio_in_open_unit` sends opposite strict signs to a parameter inside
   (0,1).  Split-noded needs the other direction: a meeting strictly inside
   BOTH pieces forces both product inequalities, so a list with no crossing
   pair can only meet at endpoints.
   -------------------------------------------------------------------------- *)

Lemma open_unit_ratio_back :
  forall a d : R,
    d <> 0 -> 0 < a / d < 1 -> a * (a - d) < 0.
Proof.
  intros a d Hd [Hlo Hhi].
  assert (Hd2 : 0 < d * d)
    by (pose proof (Rlt_0_sqr d Hd) as Hs; unfold Rsqr in Hs; exact Hs).
  assert (Har : a = (a / d) * d) by (field; exact Hd).
  set (r := a / d) in *.
  clearbody r.
  (* Substitute explicitly and expose the product shape: nra neither uses the
     defining equation nor finds the factorisation on its own. *)
  assert (Hrr : r * (r - 1) < 0) by nra.
  rewrite Har.
  replace (r * d * (r * d - d)) with ((d * d) * (r * (r - 1))) by ring.
  nra.
Qed.

Theorem chord_interior_meet_crosses :
  forall A B C D : Point,
    chord_det A B C D <> 0 ->
    forall t s : R,
      0 < t < 1 -> 0 < s < 1 ->
      chord_eval A B t = chord_eval C D s ->
      orient A B C * orient A B D < 0 /\
      orient C D A * orient C D B < 0.
Proof.
  intros A B C D Hdet t s Ht Hs Hmeet.
  (* The meeting is the unique one, so t and s are the Cramer quotients. *)
  assert (Hsame : chord_eval A B (chord_t A B C D)
                  = chord_eval C D (chord_s A B C D)).
  { unfold chord_eval, chord_t, chord_s, orient, chord_det in *.
    apply f_equal2; field; assumption. }
  destruct (chord_hit_unique A B C D Hdet t s (chord_t A B C D)
              (chord_s A B C D) Hmeet Hsame) as [Ht' Hs'].
  subst t s.
  split.
  - (* s in (0,1) gives the AB-side product *)
    (* chord_s IS (- orient A B C) / det, so the converse bound applies with
       a := - orient A B C directly.  Its conclusion
       (-c) * ((-c) - det) < 0 is c * (c + det) < 0, and orient_diff_AB gives
       orient A B D = c + det. *)
    assert (Hb : (- orient A B C) * ((- orient A B C) - chord_det A B C D) < 0).
    { apply open_unit_ratio_back; [ exact Hdet | ].
      unfold chord_s in Hs. exact Hs. }
    pose proof (orient_diff_AB A B C D) as Hdiff. nra.
  - (* t in (0,1) gives the CD-side product *)
    assert (Ha : orient C D A * (orient C D A - chord_det A B C D) < 0)
      by (apply open_unit_ratio_back; [ exact Hdet | exact Ht ]).
    pose proof (orient_diff_CD A B C D) as Hdiff. nra.
Qed.

(* --------------------------------------------------------------------------
   SPLIT-NODED, non-degenerate branch.  `fully_intersected` as a CONCLUSION.

   For a list whose pairs no longer properly cross, any meeting of two
   non-parallel pieces is at an endpoint.  That sentence is what every
   overlay headline currently takes as a hypothesis.

   The parallel and collinear pairs still need the same treatment; this is
   the branch `chord_interior_meet_crosses` unlocks, and it is stated over a
   LIST rather than a pair.
   -------------------------------------------------------------------------- *)

Theorem chord_split_noded_nondegenerate :
  forall G1 : list (Point * Point),
    (forall AB CD : Point * Point,
        In AB G1 -> In CD G1 ->
        ~ (orient (fst AB) (snd AB) (fst CD)
             * orient (fst AB) (snd AB) (snd CD) < 0
           /\ orient (fst CD) (snd CD) (fst AB)
                * orient (fst CD) (snd CD) (snd AB) < 0)) ->
    forall (AB CD : Point * Point) (t s : R),
      In AB G1 -> In CD G1 ->
      chord_det (fst AB) (snd AB) (fst CD) (snd CD) <> 0 ->
      0 <= t <= 1 -> 0 <= s <= 1 ->
      chord_eval (fst AB) (snd AB) t = chord_eval (fst CD) (snd CD) s ->
      t = 0 \/ t = 1 \/ s = 0 \/ s = 1.
Proof.
  intros G1 Hno AB CD t s HAB HCD Hdet Ht Hs Hmeet.
  destruct (total_order_T t 0) as [[H0 | H0] | H0]; [ lra | left; exact H0 | ].
  destruct (total_order_T t 1) as [[H1 | H1] | H1];
    [ | right; left; exact H1 | lra ].
  destruct (total_order_T s 0) as [[H2 | H2] | H2];
    [ lra | right; right; left; exact H2 | ].
  destruct (total_order_T s 1) as [[H3 | H3] | H3];
    [ | right; right; right; exact H3 | lra ].
  (* Strictly interior on both pieces: the crossing test must have fired. *)
  exfalso.
  destruct (chord_interior_meet_crosses (fst AB) (snd AB) (fst CD) (snd CD)
              Hdet t s (conj H0 H1) (conj H2 H3) Hmeet) as [P1 P2].
  exact (Hno AB CD HAB HCD (conj P1 P2)).
Qed.

(* --------------------------------------------------------------------------
   SPLIT-NODED without the det <> 0 guard.

   The guarded version above excludes exactly the branch OverlayNG fails on.
   Dropping the guard means the conclusion has to change: for a collinear
   pair the meeting genuinely IS interior, so "endpoint or nothing" is false
   -- that is `chord_split_noded_hypothesis_free_false` below.

   The honest trichotomy names the escape instead of forbidding it.  Once no
   pair properly crosses, a meeting is either at an endpoint, or the pair is
   collinear -- in which case the intersection is the shared subsegment
   `chord_collinear_overlap` produces, not a vertex.  No pair is left
   unaccounted for and no degenerate case is guarded away.
   -------------------------------------------------------------------------- *)

(* Vanishing is decidable from the Reals ORDER axioms; `total_order_T` is
   informative, so no excluded middle enters through the case split. *)
Definition Rzero_dec (x : R) : {x = 0} + {x <> 0}.
Proof.
  destruct (total_order_T x 0) as [[H | H] | H].
  - right; lra.
  - left; exact H.
  - right; lra.
Defined.

Theorem chord_split_noded :
  forall G1 : list (Point * Point),
    (forall AB CD : Point * Point,
        In AB G1 -> In CD G1 ->
        ~ (orient (fst AB) (snd AB) (fst CD)
             * orient (fst AB) (snd AB) (snd CD) < 0
           /\ orient (fst CD) (snd CD) (fst AB)
                * orient (fst CD) (snd CD) (snd AB) < 0)) ->
    forall (AB CD : Point * Point) (t s : R),
      In AB G1 -> In CD G1 ->
      0 <= t <= 1 -> 0 <= s <= 1 ->
      chord_eval (fst AB) (snd AB) t = chord_eval (fst CD) (snd CD) s ->
      t = 0 \/ t = 1 \/ s = 0 \/ s = 1
      \/ (orient (fst AB) (snd AB) (fst CD) = 0
          /\ orient (fst AB) (snd AB) (snd CD) = 0).
Proof.
  intros G1 Hno AB CD t s HAB HCD Ht Hs Hmeet.
  destruct (Rzero_dec (chord_det (fst AB) (snd AB) (fst CD) (snd CD)))
    as [Hdet | Hdet].
  - (* det = 0: parallel.  Either some endpoint is off the line, and then
       nothing meets at all, or the pair is collinear. *)
    destruct (Rzero_dec (orient (fst AB) (snd AB) (fst CD))) as [Hc | Hc].
    + (* collinear: orient A B D = orient A B C = 0 by orient_diff_AB *)
      right; right; right; right.
      split; [ exact Hc | ].
      pose proof (orient_diff_AB (fst AB) (snd AB) (fst CD) (snd CD)) as Hdiff.
      rewrite Hdet in Hdiff. lra.
    + (* parallel, distinct lines: the meeting is impossible *)
      exfalso.
      exact (chord_parallel_distinct_miss (fst AB) (snd AB) (fst CD) (snd CD)
               Hdet Hc t s Hmeet).
  - (* det <> 0: a strictly interior meeting would force both products. *)
    destruct (total_order_T t 0) as [[H0 | H0] | H0]; [ lra | left; exact H0 | ].
    destruct (total_order_T t 1) as [[H1 | H1] | H1];
      [ | right; left; exact H1 | lra ].
    destruct (total_order_T s 0) as [[H2 | H2] | H2];
      [ lra | right; right; left; exact H2 | ].
    destruct (total_order_T s 1) as [[H3 | H3] | H3];
      [ | right; right; right; left; exact H3 | lra ].
    exfalso.
    destruct (chord_interior_meet_crosses (fst AB) (snd AB) (fst CD) (snd CD)
                Hdet t s (conj H0 H1) (conj H2 H3) Hmeet) as [P1 P2].
    exact (Hno AB CD HAB HCD (conj P1 P2)).
Qed.

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
Print Assumptions collinear_param_x.
Print Assumptions collinear_param_exists.
Print Assumptions collinear_meet_iff.
Print Assumptions chord_collinear_overlap.
Print Assumptions chord_collinear_from_points.
Print Assumptions chord_interior_meet_crosses.
Print Assumptions chord_split_noded.
Print Assumptions chord_split_noded_hypothesis_free_false.

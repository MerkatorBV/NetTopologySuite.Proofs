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

     cook / cook_noded / cook_split_noded / cook_covers / cook_within
       THE CONSTRUCTOR.  `cook : list (Point*Point) -> list (Point*Point)`
       cuts every segment at every parameter at which it properly crosses
       another member of the input family.  `cook_noded` proves no two
       pieces of the result cross properly, and `cook_split_noded` therefore
       states the split-noded conclusion for `cook G` with NO hypothesis on
       G at all.  `cook_covers` and `cook_within` prove the image is the
       input as a point set, so `fun _ => nil` does not satisfy this.

       Termination is structural: `cook` is a flat_map over a fold, not a
       well-founded recursion.  That is legitimate because for CHORDS one
       pass is already a fixed point -- `subchord_cross_parent` shows a
       proper crossing of two pieces is a proper crossing of their parents,
       so cutting at the parents' parameters leaves nothing to cut.  That
       argument is specific to straight pieces and does not carry to arcs.

     cook2 / cook2_noded / cook2_split_noded_strict / cook2_nodup /
     cook2_covers / cook2_within
       OVERLAP AS ONE PIECE.  `crosses` is the two strict orientation
       products, so collinear overlap is invisible to `cook`: two
       overlapping input chords leave two overlapping output chords, and
       obligation (2) -- "two segments meet IFF they share an endpoint" --
       keeps only its "if" half.  `cook2` cuts additionally at the projected
       endpoints of every collinear member (`coll_params`), and dedups with
       `nodup`.  `cook2_split_noded_strict` is then the "only if" half:

         In P (cook2 G) -> In Q (cook2 G) -> gamma_P(t) = gamma_Q(s) ->
         t = 0 \/ t = 1 \/ s = 0 \/ s = 1 \/ P = Q \/ P = (snd Q, fst Q)

       No collinear disjunct.  Two pieces that meet away from their
       endpoints ARE the same piece, or that piece reversed -- and `nodup`
       makes the list carry it once.

       The engine is `cut_param_transport`: every cut parameter of a
       collinear neighbour transports to a cut parameter of this chord.  A
       crossing of the neighbour with a third member E is a crossing of THIS
       chord with E whenever the crossing point falls strictly inside it
       (`interior_root_gives_cross`), and an endpoint of a member collinear
       with the neighbour is an endpoint of a member collinear with this
       chord.  So the two subdivisions agree on the overlap, and the
       intervals must coincide.

   WHAT IS NOT PROVED, and what that costs.

     - NON-DEGENERATE INPUT IS A HYPOTHESIS.  `cook2_split_noded_strict`
       assumes every member of G has two distinct endpoints (`nondeg`).  A
       degenerate point-chord is not handled: its `proj_param` has no
       meaning and the transport argument has no direction to project onto.
       `cook2` still RUNS on such input and `cook2_noded` still holds; only
       the strict conclusion is withheld.  Rejecting or promoting
       degenerate members is a decision this file does not make.
     - `cook` ITSELF STILL HAS THE OVERLAP GAP.  `cook_split_noded` keeps
       its collinear disjunct and that is correct for `cook`, which does not
       cut at overlaps.  The strict statement belongs to `cook2` only.
     - ORIENTATION IS NOT NORMALISED.  A piece and its reverse are two
       entries; `nodup` does not merge them, and the strict theorem names
       the twin explicitly.  Under ADR-0007 that is right -- a chicken and
       its twin are two directed uses of one egg -- but this file has no
       egg, so it is a list quirk here rather than a structure.
     - THE GRID.  Rounding to Lambda = h*Z^2 and showing two rounded edges
       meet iff they share an endpoint.  Obligation (3).  Not attempted, and
       when it is, it must not assume `cook2_split_noded_strict`.
     - IDENTITY.  Whether two hits at the same point of the sheet are one
       hen or two.  In exact reals `cook` sidesteps this: the two pieces
       adjacent at a cut carry the SAME Point value, by construction, and
       `chord_eq_dec` decides it.  The question is a floating-point
       question and is untouched here.  Open in ADR-0007.
     - ANYTHING BUT CHORDS.  Arcs, clothoids and the rest have no `I` here,
       so the cook has nothing to cut them at.  Under ADR-0007 that is
       Decline, not a proof.
     - Bounded-bit-length and floating realisations (Priest 1991 section 7,
       doi:10.1109/ARITH.1991.145549).  Everything here is exact reals, and
       `chord_t` is a real quotient, not a rounded float.  A binary64 cook
       is a different theorem and is not implied by this one.
     - THE GRAPH.  `cook2 G` is a LIST of chords that pairwise meet only at
       endpoints.  It is not a DCEL: no vertex identification, no rotation
       system, no darts, no faces, no labelling against a second operand.
       Nothing here decides which operand a piece came from, which is what
       CAP, CUP, SUB and XOR differ by.

   ACCOUNTING.  CAP, CUP, SUB and XOR (SQL/MM 5.1.31--36) are four filters
   over one noded graph.  Obligation (2) is now closed for chords in exact
   reals with non-degenerate members: `cook2 G` is noded in both halves of
   "meet iff shared endpoint".  The graph is still not built and no
   labelling exists, so all four operations still stand at zero, and nothing
   in this file is a fraction of any of them.  No hypothesis has been
   deleted from any corpus theorem either: the seven entries in
   docs/lemmas-under-constructor.txt are stated in binary64 over the corpus
   graph type, not over a list of chords in R, so `cook2` does not discharge
   them.  It shows the shape such a discharge would have.

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
   THE COOK.  Everything above is a statement ABOUT a family with no proper
   crossing.  Nothing above produces one.  This section does.

   For chords the cook is not a fixpoint iteration: a proper crossing of two
   PIECES is a proper crossing of their PARENTS (subchord_cross_parent), so
   cutting every segment at every parameter at which it properly crosses
   another member of the ORIGINAL family is already a fixed point.  One pass.
   That is the whole termination argument, and it is why `cook` below is a
   plain flat_map and not a well-founded recursion.

   Three obligations are discharged together:
     cook_noded    -- no two pieces cross properly;
     cook_covers   -- every point of every input segment lies on some piece;
     cook_within   -- every point of every piece lies on some input segment.
   Without the last two, `fun _ => nil` would satisfy the first.
   -------------------------------------------------------------------------- *)

Definition subchord (A B : Point) (a b : R) : Point * Point :=
  (chord_eval A B a, chord_eval A B b).

Definition crosses (P Q : Point * Point) : Prop :=
  orient (fst P) (snd P) (fst Q) * orient (fst P) (snd P) (snd Q) < 0
  /\ orient (fst Q) (snd Q) (fst P) * orient (fst Q) (snd Q) (snd P) < 0.

(* Restricting to [a,b] is an affine reparametrisation, and orientation
   against a sub-chord is the parent orientation scaled by (b - a). *)

Lemma subchord_reparam :
  forall (A B : Point) (a b u : R),
    chord_eval (chord_eval A B a) (chord_eval A B b) u
    = chord_eval A B (a + u * (b - a)).
Proof. intros; unfold chord_eval; simpl; apply f_equal2; ring. Qed.

Lemma subchord_orient :
  forall (A B X : Point) (a b : R),
    orient (chord_eval A B a) (chord_eval A B b) X
    = (b - a) * orient A B X.
Proof. intros; unfold orient, chord_eval; simpl; ring. Qed.

Lemma scale_prod_neg :
  forall k x y : R, (k * x) * (k * y) < 0 -> x * y < 0.
Proof.
  intros k x y H.
  replace ((k * x) * (k * y)) with ((k * k) * (x * y)) in H by ring.
  destruct (Rle_or_lt 0 (x * y)) as [Hxy | Hxy]; [ | exact Hxy ].
  assert (Hk : 0 <= k * k) by nra.
  assert (Hp : 0 <= (k * k) * (x * y)) by nra.
  lra.
Qed.

(* An affine function of x cannot have strictly opposite signs at two points
   of [0,1] unless its values at 0 and 1 already have strictly opposite
   signs. *)
Lemma affine_same_sign_prod :
  forall u v c d : R,
    0 <= c <= 1 -> 0 <= d <= 1 -> 0 <= u * v ->
    0 <= ((1 - c) * u + c * v) * ((1 - d) * u + d * v).
Proof.
  intros u v c d [Hc0 Hc1] [Hd0 Hd1] Huv.
  assert (Hu2 : 0 <= u * u) by nra.
  assert (Hv2 : 0 <= v * v) by nra.
  assert (Hcd : 0 <= (1 - c) * (1 - d)) by nra.
  assert (Hmix : 0 <= (1 - c) * d + c * (1 - d)) by nra.
  assert (Hcd2 : 0 <= c * d) by nra.
  assert (T1 : 0 <= ((1 - c) * (1 - d)) * (u * u)) by nra.
  assert (T2 : 0 <= ((1 - c) * d + c * (1 - d)) * (u * v)) by nra.
  assert (T3 : 0 <= (c * d) * (v * v)) by nra.
  replace (((1 - c) * u + c * v) * ((1 - d) * u + d * v))
    with (((1 - c) * (1 - d)) * (u * u)
          + ((1 - c) * d + c * (1 - d)) * (u * v)
          + (c * d) * (v * v)) by ring.
  lra.
Qed.

Lemma affine_pair_sign :
  forall u v c d : R,
    0 <= c <= 1 -> 0 <= d <= 1 ->
    ((1 - c) * u + c * v) * ((1 - d) * u + d * v) < 0 ->
    u * v < 0.
Proof.
  intros u v c d Hc Hd H.
  destruct (Rle_or_lt 0 (u * v)) as [Huv | Huv]; [ | exact Huv ].
  pose proof (affine_same_sign_prod u v c d Hc Hd Huv). lra.
Qed.

(* THE KEY STRUCTURAL FACT.  A proper crossing of two pieces is a proper
   crossing of their parents.  No non-degeneracy hypothesis. *)
Lemma subchord_cross_parent :
  forall (A B C D : Point) (a b c d : R),
    0 <= a <= 1 -> 0 <= b <= 1 -> 0 <= c <= 1 -> 0 <= d <= 1 ->
    crosses (subchord A B a b) (subchord C D c d) ->
    orient A B C * orient A B D < 0 /\ orient C D A * orient C D B < 0.
Proof.
  intros A B C D a b c d Ha Hb Hc Hd [H1 H2].
  unfold subchord in H1, H2; simpl in H1, H2.
  rewrite !subchord_orient in H1.
  rewrite !subchord_orient in H2.
  rewrite !orient_affine_third in H1.
  rewrite !orient_affine_third in H2.
  split.
  - apply (affine_pair_sign _ _ c d Hc Hd).
    apply (scale_prod_neg (b - a)); exact H1.
  - apply (affine_pair_sign _ _ a b Ha Hb).
    apply (scale_prod_neg (d - c)); exact H2.
Qed.

(* --------------------------------------------------------------------------
   Cutting [0,1] at a finite set of parameters.  Every interval produced
   strictly excludes every parameter cut at.  insert_cut splits EVERY
   interval that strictly contains the parameter, so the invariant needs no
   disjointness lemma.
   -------------------------------------------------------------------------- *)

Fixpoint insert_cut (r : R) (iv : list (R * R)) : list (R * R) :=
  match iv with
  | nil => nil
  | p :: rest =>
      if Rlt_dec (fst p) r
      then if Rlt_dec r (snd p)
           then (fst p, r) :: (r, snd p) :: insert_cut r rest
           else p :: insert_cut r rest
      else p :: insert_cut r rest
  end.

Fixpoint cut_all (ts : list R) : list (R * R) :=
  match ts with
  | nil => (0, 1) :: nil
  | r :: rest => insert_cut r (cut_all rest)
  end.

Lemma insert_cut_excludes :
  forall (r : R) (iv : list (R * R)) (ab : R * R),
    In ab (insert_cut r iv) -> ~ (fst ab < r < snd ab).
Proof.
  intros r iv. induction iv as [| p rest IH]; simpl; intros ab Hin.
  - contradiction.
  - destruct (Rlt_dec (fst p) r) as [H1 | H1].
    + destruct (Rlt_dec r (snd p)) as [H2 | H2].
      * destruct Hin as [E | [E | Hin]].
        -- subst ab; simpl; lra.
        -- subst ab; simpl; lra.
        -- apply IH; exact Hin.
      * apply Rnot_lt_le in H2.
        destruct Hin as [E | Hin];
          [ subst ab; simpl; lra | apply IH; exact Hin ].
    + apply Rnot_lt_le in H1.
      destruct Hin as [E | Hin];
        [ subst ab; simpl; lra | apply IH; exact Hin ].
Qed.

Lemma insert_cut_preserves :
  forall (t r : R) (iv : list (R * R)),
    (forall ab, In ab iv -> ~ (fst ab < t < snd ab)) ->
    forall ab, In ab (insert_cut r iv) -> ~ (fst ab < t < snd ab).
Proof.
  intros t r iv. induction iv as [| p rest IH]; simpl; intros Hold ab Hin.
  - contradiction.
  - assert (Hp : ~ (fst p < t < snd p)) by (apply Hold; left; reflexivity).
    assert (Hrest : forall q, In q rest -> ~ (fst q < t < snd q))
      by (intros q Hq; apply Hold; right; exact Hq).
    destruct (Rlt_dec (fst p) r) as [H1 | H1].
    + destruct (Rlt_dec r (snd p)) as [H2 | H2].
      * destruct Hin as [E | [E | Hin]].
        -- subst ab; simpl; simpl in Hp; lra.
        -- subst ab; simpl; simpl in Hp; lra.
        -- apply (IH Hrest); exact Hin.
      * destruct Hin as [E | Hin];
          [ subst ab; exact Hp | apply (IH Hrest); exact Hin ].
    + destruct Hin as [E | Hin];
        [ subst ab; exact Hp | apply (IH Hrest); exact Hin ].
Qed.

Lemma insert_cut_bounds :
  forall (r : R) (iv : list (R * R)),
    (forall ab, In ab iv -> 0 <= fst ab /\ fst ab < snd ab /\ snd ab <= 1) ->
    forall ab, In ab (insert_cut r iv) ->
      0 <= fst ab /\ fst ab < snd ab /\ snd ab <= 1.
Proof.
  intros r iv. induction iv as [| p rest IH]; simpl; intros Hold ab Hin.
  - contradiction.
  - assert (Hp : 0 <= fst p /\ fst p < snd p /\ snd p <= 1)
      by (apply Hold; left; reflexivity).
    assert (Hrest : forall q, In q rest ->
                      0 <= fst q /\ fst q < snd q /\ snd q <= 1)
      by (intros q Hq; apply Hold; right; exact Hq).
    destruct (Rlt_dec (fst p) r) as [H1 | H1].
    + destruct (Rlt_dec r (snd p)) as [H2 | H2].
      * destruct Hin as [E | [E | Hin]].
        -- subst ab; simpl; destruct Hp as [Q1 [Q2 Q3]]; repeat split; lra.
        -- subst ab; simpl; destruct Hp as [Q1 [Q2 Q3]]; repeat split; lra.
        -- apply (IH Hrest); exact Hin.
      * destruct Hin as [E | Hin];
          [ subst ab; exact Hp | apply (IH Hrest); exact Hin ].
    + destruct Hin as [E | Hin];
        [ subst ab; exact Hp | apply (IH Hrest); exact Hin ].
Qed.

Lemma insert_cut_covers :
  forall (r : R) (iv : list (R * R)) (t : R),
    (exists ab, In ab iv /\ fst ab <= t <= snd ab) ->
    exists ab, In ab (insert_cut r iv) /\ fst ab <= t <= snd ab.
Proof.
  intros r iv t. induction iv as [| p rest IH]; simpl.
  - intros [ab [Hno _]]; contradiction.
  - intros [ab [[E | Hin] Hbd]].
    + subst p.
      destruct (Rlt_dec (fst ab) r) as [H1 | H1].
      * destruct (Rlt_dec r (snd ab)) as [H2 | H2].
        -- destruct (Rle_dec t r) as [H3 | H3].
           ++ exists (fst ab, r); simpl; split;
                [ left; reflexivity | simpl in Hbd; lra ].
           ++ exists (r, snd ab); simpl; split;
                [ right; left; reflexivity | simpl in Hbd; lra ].
        -- exists ab; split; [ left; reflexivity | exact Hbd ].
      * exists ab; split; [ left; reflexivity | exact Hbd ].
    + assert (Hex : exists q, In q rest /\ fst q <= t <= snd q)
        by (exists ab; split; assumption).
      destruct (IH Hex) as [q [Hinq Hbdq]].
      destruct (Rlt_dec (fst p) r) as [H1 | H1].
      * destruct (Rlt_dec r (snd p)) as [H2 | H2].
        -- exists q; split; [ right; right; exact Hinq | exact Hbdq ].
        -- exists q; split; [ right; exact Hinq | exact Hbdq ].
      * exists q; split; [ right; exact Hinq | exact Hbdq ].
Qed.

Lemma cut_all_excludes :
  forall (ts : list R) (t : R) (ab : R * R),
    In t ts -> In ab (cut_all ts) -> ~ (fst ab < t < snd ab).
Proof.
  intros ts. induction ts as [| r ts IH]; simpl; intros t ab Hint Hin.
  - contradiction.
  - destruct Hint as [E | Hint].
    + subst r. apply (insert_cut_excludes t (cut_all ts)); exact Hin.
    + apply (insert_cut_preserves t r (cut_all ts)); [ | exact Hin ].
      intros q Hq. apply (IH t q); assumption.
Qed.

Lemma cut_all_bounds :
  forall (ts : list R) (ab : R * R),
    In ab (cut_all ts) -> 0 <= fst ab /\ fst ab < snd ab /\ snd ab <= 1.
Proof.
  intros ts. induction ts as [| r ts IH]; simpl; intros ab Hin.
  - destruct Hin as [E | Hno];
      [ subst ab; simpl; repeat split; lra | contradiction ].
  - apply (insert_cut_bounds r (cut_all ts)); [ exact IH | exact Hin ].
Qed.

Lemma cut_all_covers :
  forall (ts : list R) (t : R),
    0 <= t <= 1 ->
    exists ab, In ab (cut_all ts) /\ fst ab <= t <= snd ab.
Proof.
  intros ts. induction ts as [| r ts IH]; simpl; intros t Ht.
  - exists (0, 1); simpl; split; [ left; reflexivity | lra ].
  - apply insert_cut_covers. apply IH. exact Ht.
Qed.

(* --------------------------------------------------------------------------
   The cook itself: cut every segment at every parameter at which it properly
   crosses another member of the input family.
   -------------------------------------------------------------------------- *)

Definition crosses_b (P Q : Point * Point) : bool :=
  if Rlt_dec (orient (fst P) (snd P) (fst Q)
              * orient (fst P) (snd P) (snd Q)) 0
  then if Rlt_dec (orient (fst Q) (snd Q) (fst P)
                   * orient (fst Q) (snd Q) (snd P)) 0
       then true else false
  else false.

Lemma crosses_b_intro :
  forall P Q : Point * Point, crosses P Q -> crosses_b P Q = true.
Proof.
  intros P Q [H1 H2]. unfold crosses_b.
  destruct (Rlt_dec (orient (fst P) (snd P) (fst Q)
                     * orient (fst P) (snd P) (snd Q)) 0) as [Hy | Hn];
    [ | lra ].
  destruct (Rlt_dec (orient (fst Q) (snd Q) (fst P)
                     * orient (fst Q) (snd Q) (snd P)) 0) as [Hy2 | Hn2];
    [ reflexivity | lra ].
Qed.

(* --------------------------------------------------------------------------
   The cook, parameterised by its cut set.  `cook` below is this at the
   crossing-only cut set; `cook2` is the same machine at the cut set that
   also carries collinear endpoints.
   -------------------------------------------------------------------------- *)

Definition pieces (f : Point * Point -> list R) (G : list (Point * Point))
  : list (Point * Point) :=
  flat_map (fun AB =>
              map (fun ab => subchord (fst AB) (snd AB) (fst ab) (snd ab))
                  (cut_all (f AB))) G.

Lemma pieces_shape :
  forall (f : Point * Point -> list R) (G : list (Point * Point))
         (P : Point * Point),
    In P (pieces f G) ->
    exists (AB : Point * Point) (ab : R * R),
      In AB G /\ In ab (cut_all (f AB))
      /\ P = subchord (fst AB) (snd AB) (fst ab) (snd ab).
Proof.
  intros f G P Hin.
  apply (proj1 (in_flat_map _ G P)) in Hin.
  destruct Hin as [AB [HAB Hin]].
  apply (proj1 (in_map_iff _ _ _)) in Hin.
  destruct Hin as [ab [Heq Hab]].
  exists AB, ab.
  repeat split; [ exact HAB | exact Hab | symmetry; exact Heq ].
Qed.

Lemma pieces_member :
  forall (f : Point * Point -> list R) (G : list (Point * Point))
         (AB : Point * Point) (ab : R * R),
    In AB G -> In ab (cut_all (f AB)) ->
    In (subchord (fst AB) (snd AB) (fst ab) (snd ab)) (pieces f G).
Proof.
  intros f G AB ab HAB Hab.
  apply (proj2 (in_flat_map _ G _)).
  exists AB. split; [ exact HAB | ].
  apply (proj2 (in_map_iff _ _ _)).
  exists ab. split; [ reflexivity | exact Hab ].
Qed.

(* THE INVARIANT, for any cut set that contains the crossing parameters. *)
Theorem pieces_noded :
  forall (f : Point * Point -> list R) (G : list (Point * Point)),
    (forall AB CD : Point * Point,
        In AB G -> In CD G -> crosses AB CD ->
        In (chord_t (fst AB) (snd AB) (fst CD) (snd CD)) (f AB)) ->
    forall P Q : Point * Point,
      In P (pieces f G) -> In Q (pieces f G) -> ~ crosses P Q.
Proof.
  intros f G Hf P Q HP HQ Hcross.
  destruct (pieces_shape f G P HP) as [AB [ab [HABG [Hab HPeq]]]].
  destruct (pieces_shape f G Q HQ) as [CD [cd [HCDG [Hcd HQeq]]]].
  destruct (cut_all_bounds _ _ Hab) as [Ha0 [Hab1 Hb1]].
  destruct (cut_all_bounds _ _ Hcd) as [Hc0 [Hcd1 Hd1]].
  subst P Q.
  set (A := fst AB) in *. set (B := snd AB) in *.
  set (C := fst CD) in *. set (D := snd CD) in *.
  set (a := fst ab) in *. set (b := snd ab) in *.
  set (c := fst cd) in *. set (d := snd cd) in *.
  assert (Hpar : orient A B C * orient A B D < 0
                 /\ orient C D A * orient C D B < 0).
  { apply (subchord_cross_parent A B C D a b c d);
      solve [ lra | exact Hcross ]. }
  destruct Hpar as [Hpar1 Hpar2].
  assert (Hdet : chord_det A B C D <> 0)
    by (apply det_nonzero_of_opposite; exact Hpar2).
  destruct Hcross as [HC1 HC2].
  unfold subchord in HC1, HC2; simpl in HC1, HC2.
  pose proof (chord_hit (chord_eval A B a) (chord_eval A B b)
                        (chord_eval C D c) (chord_eval C D d) HC1 HC2) as HH.
  cbv zeta in HH.
  destruct HH as [Hu01 [Hv01 Hmeet]].
  set (u := chord_t (chord_eval A B a) (chord_eval A B b)
                    (chord_eval C D c) (chord_eval C D d)) in *.
  set (v := chord_s (chord_eval A B a) (chord_eval A B b)
                    (chord_eval C D c) (chord_eval C D d)) in *.
  clearbody u v.
  rewrite !subchord_reparam in Hmeet.
  pose proof (chord_hit A B C D Hpar1 Hpar2) as HH2.
  cbv zeta in HH2.
  destruct HH2 as [Hw1 [Hw2 Hmeet2]].
  destruct (chord_hit_unique A B C D Hdet
              (a + u * (b - a)) (c + v * (d - c))
              (chord_t A B C D) (chord_s A B C D) Hmeet Hmeet2) as [Ht Hs].
  assert (Hinside : a < chord_t A B C D < b) by nra.
  assert (Hcp : In (chord_t A B C D) (f AB))
    by (apply Hf; [ exact HABG | exact HCDG | unfold crosses; split; assumption ]).
  apply (cut_all_excludes (f AB) (chord_t A B C D) ab Hcp Hab).
  exact Hinside.
Qed.

Lemma ratio_in_closed_unit :
  forall x y : R, 0 < y -> 0 <= x <= y -> 0 <= x / y <= 1.
Proof.
  intros x y Hy Hx.
  assert (Hx2 : x = (x / y) * y) by (field; lra).
  set (r := x / y) in *. clearbody r.
  split; nra.
Qed.

Theorem pieces_covers :
  forall (f : Point * Point -> list R) (G : list (Point * Point))
         (AB : Point * Point) (t : R),
    In AB G -> 0 <= t <= 1 ->
    exists (P : Point * Point) (u : R),
      In P (pieces f G) /\ 0 <= u <= 1
      /\ chord_eval (fst P) (snd P) u = chord_eval (fst AB) (snd AB) t.
Proof.
  intros f G AB t HAB Ht.
  destruct (cut_all_covers (f AB) t Ht) as [ab [Hab Hbd]].
  destruct (cut_all_bounds _ _ Hab) as [Ha0 [Hab1 Hb1]].
  assert (Hne : snd ab - fst ab <> 0) by lra.
  exists (subchord (fst AB) (snd AB) (fst ab) (snd ab)).
  exists ((t - fst ab) / (snd ab - fst ab)).
  split; [ apply pieces_member; assumption | split ].
  - apply ratio_in_closed_unit; lra.
  - unfold subchord; simpl.
    rewrite subchord_reparam.
    replace (fst ab + (t - fst ab) / (snd ab - fst ab) * (snd ab - fst ab))
      with t by (field; exact Hne).
    reflexivity.
Qed.

Theorem pieces_within :
  forall (f : Point * Point -> list R) (G : list (Point * Point))
         (P : Point * Point) (u : R),
    In P (pieces f G) -> 0 <= u <= 1 ->
    exists (AB : Point * Point) (t : R),
      In AB G /\ 0 <= t <= 1
      /\ chord_eval (fst AB) (snd AB) t = chord_eval (fst P) (snd P) u.
Proof.
  intros f G P u HP Hu.
  destruct (pieces_shape f G P HP) as [AB [ab [HABG [Hab HPeq]]]].
  destruct (cut_all_bounds _ _ Hab) as [Ha0 [Hab1 Hb1]].
  exists AB, (fst ab + u * (snd ab - fst ab)).
  split; [ exact HABG | split ].
  - split; nra.
  - subst P. unfold subchord; simpl.
    rewrite subchord_reparam. reflexivity.
Qed.

(* --------------------------------------------------------------------------
   COOK 1: cut at proper crossings only.
   -------------------------------------------------------------------------- *)

Definition cross_params (AB : Point * Point) (G : list (Point * Point))
  : list R :=
  map (fun CD => chord_t (fst AB) (snd AB) (fst CD) (snd CD))
      (filter (crosses_b AB) G).

Definition split_one (G : list (Point * Point)) (AB : Point * Point)
  : list (Point * Point) :=
  map (fun ab => subchord (fst AB) (snd AB) (fst ab) (snd ab))
      (cut_all (cross_params AB G)).

Definition cook (G : list (Point * Point)) : list (Point * Point) :=
  pieces (fun AB => cross_params AB G) G.

Lemma cook_alt : forall G, cook G = flat_map (split_one G) G.
Proof. reflexivity. Qed.

Lemma cross_params_spec :
  forall (G : list (Point * Point)) (AB CD : Point * Point),
    In CD G -> crosses AB CD ->
    In (chord_t (fst AB) (snd AB) (fst CD) (snd CD)) (cross_params AB G).
Proof.
  intros G AB CD HCD Hx.
  unfold cross_params.
  apply (proj2 (in_map_iff _ _ _)).
  exists CD. split; [ reflexivity | ].
  apply (proj2 (filter_In _ _ _)).
  split; [ exact HCD | apply crosses_b_intro; exact Hx ].
Qed.

Theorem cook_noded :
  forall (G : list (Point * Point)) (P Q : Point * Point),
    In P (cook G) -> In Q (cook G) -> ~ crosses P Q.
Proof.
  intros G. apply pieces_noded.
  intros AB CD HAB HCD Hx. apply cross_params_spec; assumption.
Qed.

Corollary cook_split_noded :
  forall (G : list (Point * Point)) (P Q : Point * Point) (t s : R),
    In P (cook G) -> In Q (cook G) ->
    0 <= t <= 1 -> 0 <= s <= 1 ->
    chord_eval (fst P) (snd P) t = chord_eval (fst Q) (snd Q) s ->
    t = 0 \/ t = 1 \/ s = 0 \/ s = 1
    \/ (orient (fst P) (snd P) (fst Q) = 0
        /\ orient (fst P) (snd P) (snd Q) = 0).
Proof.
  intros G P Q t s HP HQ Ht Hs Hmeet.
  apply (chord_split_noded (cook G)); try assumption.
  intros X Y HX HY. exact (cook_noded G X Y HX HY).
Qed.

Theorem cook_covers :
  forall (G : list (Point * Point)) (AB : Point * Point) (t : R),
    In AB G -> 0 <= t <= 1 ->
    exists (P : Point * Point) (u : R),
      In P (cook G) /\ 0 <= u <= 1
      /\ chord_eval (fst P) (snd P) u = chord_eval (fst AB) (snd AB) t.
Proof. intros G. apply pieces_covers. Qed.

Theorem cook_within :
  forall (G : list (Point * Point)) (P : Point * Point) (u : R),
    In P (cook G) -> 0 <= u <= 1 ->
    exists (AB : Point * Point) (t : R),
      In AB G /\ 0 <= t <= 1
      /\ chord_eval (fst AB) (snd AB) t = chord_eval (fst P) (snd P) u.
Proof. intros G. apply pieces_within. Qed.

(* --------------------------------------------------------------------------
   COOK 2: also cut at the projected endpoints of collinear members.

   `crosses` is the two strict orientation products, so collinear overlap is
   invisible to `cook`.  Two overlapping input chords leave two overlapping
   output chords, and obligation (2) -- "two segments meet IFF they share an
   endpoint" -- keeps only its "if" half.  The repair is to project the
   endpoints of every collinear member onto the chord and cut there as well.
   `cook2_split_noded_strict` is then the "only if" half: distinct pieces
   that are not each other's twin meet only at an endpoint.
   -------------------------------------------------------------------------- *)

Definition nondeg (P : Point * Point) : Prop :=
  px (fst P) <> px (snd P) \/ py (fst P) <> py (snd P).

Definition proj_param (A B X : Point) : R :=
  if Rzero_dec (px B - px A)
  then (py X - py A) / (py B - py A)
  else (px X - px A) / (px B - px A).

Lemma proj_param_correct :
  forall A B X : Point,
    nondeg (A, B) -> orient A B X = 0 ->
    X = chord_eval A B (proj_param A B X).
Proof.
  intros A B X Hnd Hor. unfold proj_param, nondeg in *; simpl in Hnd.
  destruct (Rzero_dec (px B - px A)) as [Hx | Hx].
  - apply collinear_param_y; [ | exact Hor ].
    destruct Hnd as [H | H]; [ exfalso; apply H; lra | intro Hc; apply H; lra ].
  - apply collinear_param_x; [ exact Hx | exact Hor ].
Qed.

Lemma chord_eval_inj :
  forall (A B : Point) (x y : R),
    nondeg (A, B) -> chord_eval A B x = chord_eval A B y -> x = y.
Proof.
  intros A B x y Hnd Heq.
  pose proof (f_equal px Heq) as Hx; simpl in Hx.
  pose proof (f_equal py Heq) as Hy; simpl in Hy.
  unfold nondeg in Hnd; simpl in Hnd.
  destruct Hnd as [H | H].
  - assert (Hd : px B - px A <> 0) by (intro Hc; apply H; lra).
    assert (Hz : (x - y) * (px B - px A) = 0).
    { replace ((x - y) * (px B - px A))
        with (((1 - x) * px A + x * px B) - ((1 - y) * px A + y * px B))
        by ring.
      rewrite Hx. ring. }
    apply Rmult_integral in Hz.
    destruct Hz as [Hz | Hz]; [ lra | contradiction ].
  - assert (Hd : py B - py A <> 0) by (intro Hc; apply H; lra).
    assert (Hz : (x - y) * (py B - py A) = 0).
    { replace ((x - y) * (py B - py A))
        with (((1 - x) * py A + x * py B) - ((1 - y) * py A + y * py B))
        by ring.
      rewrite Hy. ring. }
    apply Rmult_integral in Hz.
    destruct Hz as [Hz | Hz]; [ lra | contradiction ].
Qed.

Lemma proj_param_eval :
  forall (A B : Point) (x : R),
    nondeg (A, B) -> proj_param A B (chord_eval A B x) = x.
Proof.
  intros A B x Hnd.
  symmetry.
  apply (chord_eval_inj A B); [ exact Hnd | ].
  apply proj_param_correct; [ exact Hnd | apply orient_on_own_chord ].
Qed.

Lemma chord_eval_zero : forall A B : Point, chord_eval A B 0 = A.
Proof. intros A B; unfold chord_eval; destruct A; simpl; apply f_equal2; ring. Qed.

Lemma chord_eval_one : forall A B : Point, chord_eval A B 1 = B.
Proof. intros A B; unfold chord_eval; destruct B; simpl; apply f_equal2; ring. Qed.

(* Transport between two chords on one line. *)

Lemma coll_orient_transport :
  forall (A B C D X : Point) (sg tu : R),
    C = chord_eval A B sg -> D = chord_eval A B tu ->
    orient C D X = (tu - sg) * orient A B X.
Proof. intros A B C D X sg tu HC HD. subst C D. apply subchord_orient. Qed.

Lemma coll_eval_transport :
  forall (A B C D : Point) (sg tu x : R),
    C = chord_eval A B sg -> D = chord_eval A B tu ->
    chord_eval C D x = chord_eval A B (sg + x * (tu - sg)).
Proof. intros A B C D sg tu x HC HD. subst C D. apply subchord_reparam. Qed.

(* Two affine forms vanishing at two distinct parameters vanish outright. *)
Lemma two_affine_zero :
  forall u v c d : R,
    c <> d ->
    (1 - c) * u + c * v = 0 -> (1 - d) * u + d * v = 0 -> u = 0 /\ v = 0.
Proof.
  intros u v c d Hcd H1 H2.
  assert (Hz : (d - c) * (u - v) = 0).
  { replace ((d - c) * (u - v))
      with (((1 - c) * u + c * v) - ((1 - d) * u + d * v)) by ring.
    rewrite H1, H2. ring. }
  apply Rmult_integral in Hz.
  destruct Hz as [Hz | Hz]; [ exfalso; apply Hcd; lra | ].
  assert (Huv : u = v) by lra.
  subst v.
  assert (Hu : u = 0) by (ring_simplify in H1; lra).
  split; [ exact Hu | exact Hu ].
Qed.

(* An affine form with a root strictly inside has strictly opposite ends. *)
Lemma affine_root_opposite :
  forall u v g : R,
    0 < g < 1 -> (1 - g) * u + g * v = 0 -> ~ (u = 0 /\ v = 0) -> u * v < 0.
Proof.
  intros u v g Hg Heq Hnz.
  destruct (Rzero_dec u) as [Hu | Hu].
  - exfalso. apply Hnz. split; [ exact Hu | subst u; nra ].
  - assert (Hu2 : 0 < u * u)
      by (pose proof (Rlt_0_sqr u Hu) as Hs; unfold Rsqr in Hs; lra).
    assert (Hkey : g * (u * v) + (1 - g) * (u * u) = 0).
    { replace (g * (u * v) + (1 - g) * (u * u))
        with (u * ((1 - g) * u + g * v)) by ring.
      rewrite Heq. ring. }
    nra.
Qed.

Lemma both_zero_contra :
  forall A B E1 E2 : Point,
    orient A B E1 * orient A B E2 < 0 ->
    ~ (orient E1 E2 A = 0 /\ orient E1 E2 B = 0).
Proof.
  intros A B E1 E2 Hlt [H1 H2].
  assert (Hdet : chord_det A B E1 E2 = 0)
    by (rewrite <- orient_diff_CD; lra).
  pose proof (orient_diff_AB A B E1 E2) as Hd2.
  rewrite Hdet in Hd2.
  assert (Heq : orient A B E1 = orient A B E2) by lra.
  rewrite Heq in Hlt. nra.
Qed.

(* A point strictly inside AB lying on line E forces AB to cross E properly. *)
Lemma interior_root_gives_cross :
  forall (A B E1 E2 : Point) (g : R),
    0 < g < 1 ->
    orient A B E1 * orient A B E2 < 0 ->
    orient E1 E2 (chord_eval A B g) = 0 ->
    orient E1 E2 A * orient E1 E2 B < 0.
Proof.
  intros A B E1 E2 g Hg Hcross Hroot.
  rewrite orient_affine_third in Hroot.
  apply (affine_root_opposite _ _ g Hg Hroot).
  apply (both_zero_contra A B E1 E2 Hcross).
Qed.

Lemma not_between :
  forall x lo hi : R, ~ (lo < x < hi) -> x <= lo \/ hi <= x.
Proof.
  intros x lo hi H.
  destruct (Rle_or_lt x lo) as [Hl | Hl]; [ left; exact Hl | right ].
  destruct (Rle_or_lt hi x) as [Hr | Hr]; [ exact Hr | ].
  exfalso. apply H. split; assumption.
Qed.

(* --------------------------------------------------------------------------
   The enlarged cut set.
   -------------------------------------------------------------------------- *)

Definition collinear_b (P Q : Point * Point) : bool :=
  if Rzero_dec (orient (fst P) (snd P) (fst Q))
  then if Rzero_dec (orient (fst P) (snd P) (snd Q)) then true else false
  else false.

Lemma collinear_b_intro :
  forall P Q : Point * Point,
    orient (fst P) (snd P) (fst Q) = 0 ->
    orient (fst P) (snd P) (snd Q) = 0 ->
    collinear_b P Q = true.
Proof.
  intros P Q H1 H2. unfold collinear_b.
  destruct (Rzero_dec (orient (fst P) (snd P) (fst Q))) as [Hy | Hn];
    [ | contradiction ].
  destruct (Rzero_dec (orient (fst P) (snd P) (snd Q))) as [Hy2 | Hn2];
    [ reflexivity | contradiction ].
Qed.

Lemma collinear_b_elim :
  forall P Q : Point * Point,
    collinear_b P Q = true ->
    orient (fst P) (snd P) (fst Q) = 0 /\ orient (fst P) (snd P) (snd Q) = 0.
Proof.
  intros P Q H. unfold collinear_b in H.
  destruct (Rzero_dec (orient (fst P) (snd P) (fst Q))) as [Hy | Hn];
    [ | discriminate ].
  destruct (Rzero_dec (orient (fst P) (snd P) (snd Q))) as [Hy2 | Hn2];
    [ split; assumption | discriminate ].
Qed.

Definition coll_params (AB : Point * Point) (G : list (Point * Point))
  : list R :=
  flat_map (fun CD =>
              if collinear_b AB CD
              then proj_param (fst AB) (snd AB) (fst CD)
                   :: proj_param (fst AB) (snd AB) (snd CD) :: nil
              else nil) G.

Definition cut_params2 (AB : Point * Point) (G : list (Point * Point))
  : list R :=
  cross_params AB G ++ coll_params AB G.

Definition split_one2 (G : list (Point * Point)) (AB : Point * Point)
  : list (Point * Point) :=
  map (fun ab => subchord (fst AB) (snd AB) (fst ab) (snd ab))
      (cut_all (cut_params2 AB G)).

Definition point_eq_dec (p q : Point) : {p = q} + {p <> q}.
Proof.
  destruct (Rzero_dec (px p - px q)) as [Hx | Hx].
  - destruct (Rzero_dec (py p - py q)) as [Hy | Hy].
    + left. destruct p as [px1 py1]; destruct q as [px2 py2]; simpl in *.
      apply f_equal2; lra.
    + right. intro E. apply Hy. rewrite E. lra.
  - right. intro E. apply Hx. rewrite E. lra.
Defined.

Definition chord_eq_dec (x y : Point * Point) : {x = y} + {x <> y}.
Proof.
  destruct x as [x1 x2]; destruct y as [y1 y2].
  destruct (point_eq_dec x1 y1) as [E1 | N1];
    [ | right; intro E; inversion E; contradiction ].
  destruct (point_eq_dec x2 y2) as [E2 | N2];
    [ | right; intro E; inversion E; contradiction ].
  left; subst; reflexivity.
Defined.

(* The cooked family, deduplicated: one entry per distinct piece. *)
Definition cook2 (G : list (Point * Point)) : list (Point * Point) :=
  nodup chord_eq_dec (pieces (fun AB => cut_params2 AB G) G).

Lemma cook2_In :
  forall (G : list (Point * Point)) (P : Point * Point),
    In P (cook2 G) <-> In P (pieces (fun AB => cut_params2 AB G) G).
Proof. intros G P. apply nodup_In. Qed.

Theorem cook2_nodup : forall G : list (Point * Point), NoDup (cook2 G).
Proof. intros G. apply NoDup_nodup. Qed.

Lemma coll_params_spec :
  forall (G : list (Point * Point)) (AB CD : Point * Point),
    In CD G -> collinear_b AB CD = true ->
    In (proj_param (fst AB) (snd AB) (fst CD)) (coll_params AB G)
    /\ In (proj_param (fst AB) (snd AB) (snd CD)) (coll_params AB G).
Proof.
  intros G AB CD HCD Hcol.
  split.
  - apply (proj2 (in_flat_map _ G _)). exists CD. split; [ exact HCD | ].
    rewrite Hcol. simpl. left; reflexivity.
  - apply (proj2 (in_flat_map _ G _)). exists CD. split; [ exact HCD | ].
    rewrite Hcol. simpl. right; left; reflexivity.
Qed.

Lemma coll_params_elim :
  forall (G : list (Point * Point)) (AB : Point * Point) (e : R),
    In e (coll_params AB G) ->
    exists CD : Point * Point,
      In CD G /\ collinear_b AB CD = true
      /\ (e = proj_param (fst AB) (snd AB) (fst CD)
          \/ e = proj_param (fst AB) (snd AB) (snd CD)).
Proof.
  intros G AB e Hin.
  apply (proj1 (in_flat_map _ G e)) in Hin.
  destruct Hin as [CD [HCD Hin]].
  exists CD.
  destruct (collinear_b AB CD) eqn:Hcol; simpl in Hin; [ | contradiction ].
  split; [ exact HCD | split; [ reflexivity | ] ].
  destruct Hin as [E | [E | []]];
    [ left; symmetry; exact E | right; symmetry; exact E ].
Qed.

Lemma cross_params_elim :
  forall (G : list (Point * Point)) (AB : Point * Point) (e : R),
    In e (cross_params AB G) ->
    exists CD : Point * Point,
      In CD G /\ crosses AB CD
      /\ e = chord_t (fst AB) (snd AB) (fst CD) (snd CD).
Proof.
  intros G AB e Hin.
  unfold cross_params in Hin.
  apply (proj1 (in_map_iff _ _ _)) in Hin.
  destruct Hin as [CD [Heq Hin]].
  apply (proj1 (filter_In _ _ _)) in Hin.
  destruct Hin as [HCD Hb].
  exists CD.
  split; [ exact HCD | split; [ | symmetry; exact Heq ] ].
  unfold crosses.
  unfold crosses_b in Hb.
  destruct (Rlt_dec (orient (fst AB) (snd AB) (fst CD)
                     * orient (fst AB) (snd AB) (snd CD)) 0) as [Hy | Hn];
    [ | discriminate ].
  destruct (Rlt_dec (orient (fst CD) (snd CD) (fst AB)
                     * orient (fst CD) (snd CD) (snd AB)) 0) as [Hy2 | Hn2];
    [ split; assumption | discriminate ].
Qed.

(* Endpoints of a cut interval are 0, 1, or one of the cut parameters. *)

Lemma insert_cut_endpoints :
  forall (Pr : R -> Prop) (r : R) (iv : list (R * R)),
    Pr r ->
    (forall p, In p iv -> (fst p = 0 \/ Pr (fst p)) /\ (snd p = 1 \/ Pr (snd p))) ->
    forall ab, In ab (insert_cut r iv) ->
      (fst ab = 0 \/ Pr (fst ab)) /\ (snd ab = 1 \/ Pr (snd ab)).
Proof.
  intros Pr r iv Hr. induction iv as [| p rest IH]; simpl; intros Hold ab Hin.
  - contradiction.
  - assert (Hp : (fst p = 0 \/ Pr (fst p)) /\ (snd p = 1 \/ Pr (snd p)))
      by (apply Hold; left; reflexivity).
    assert (Hrest : forall q, In q rest ->
                      (fst q = 0 \/ Pr (fst q)) /\ (snd q = 1 \/ Pr (snd q)))
      by (intros q Hq; apply Hold; right; exact Hq).
    destruct (Rlt_dec (fst p) r) as [H1 | H1].
    + destruct (Rlt_dec r (snd p)) as [H2 | H2].
      * destruct Hin as [E | [E | Hin]].
        -- subst ab; simpl; split; [ apply Hp | right; exact Hr ].
        -- subst ab; simpl; split; [ right; exact Hr | apply Hp ].
        -- apply (IH Hrest); exact Hin.
      * destruct Hin as [E | Hin];
          [ subst ab; exact Hp | apply (IH Hrest); exact Hin ].
    + destruct Hin as [E | Hin];
        [ subst ab; exact Hp | apply (IH Hrest); exact Hin ].
Qed.

Lemma cut_all_endpoint_in :
  forall (ts : list R) (ab : R * R),
    In ab (cut_all ts) ->
    (fst ab = 0 \/ In (fst ab) ts) /\ (snd ab = 1 \/ In (snd ab) ts).
Proof.
  induction ts as [| r ts IH]; simpl; intros ab Hin.
  - destruct Hin as [E | Hno]; [ | contradiction ].
    subst ab; simpl; split; left; reflexivity.
  - apply (insert_cut_endpoints (fun x => r = x \/ In x ts) r (cut_all ts));
      [ left; reflexivity | | exact Hin ].
    intros p Hp. destruct (IH p Hp) as [Hf Hs].
    split.
    + destruct Hf as [E | E]; [ left; exact E | right; right; exact E ].
    + destruct Hs as [E | E]; [ left; exact E | right; right; exact E ].
Qed.

(* --------------------------------------------------------------------------
   Transporting a cut parameter of one chord onto a collinear one.
   -------------------------------------------------------------------------- *)

Lemma cut_param_transport :
  forall (G : list (Point * Point)) (A B C D : Point) (e : R),
    (forall X, In X G -> nondeg X) ->
    In (A, B) G -> In (C, D) G ->
    orient A B C = 0 -> orient A B D = 0 ->
    In e (cut_params2 (C, D) G) ->
    0 < proj_param A B (chord_eval C D e) < 1 ->
    In (proj_param A B (chord_eval C D e)) (cut_params2 (A, B) G).
Proof.
  intros G A B C D e Hnd HAB HCD HC0 HD0 He Hg01.
  assert (HndAB : nondeg (A, B)) by (apply Hnd; exact HAB).
  assert (HndCD : nondeg (C, D)) by (apply Hnd; exact HCD).
  set (sg := proj_param A B C).
  set (tu := proj_param A B D).
  assert (HCeq : C = chord_eval A B sg)
    by (apply proj_param_correct; assumption).
  assert (HDeq : D = chord_eval A B tu)
    by (apply proj_param_correct; assumption).
  assert (Hk : tu - sg <> 0).
  { intro Hz.
    assert (HCD2 : C = D) by (rewrite HCeq, HDeq; f_equal; lra).
    unfold nondeg in HndCD; simpl in HndCD.
    destruct HndCD as [H | H]; apply H; rewrite HCD2; reflexivity. }
  (* the point being transported *)
  set (X := chord_eval C D e).
  assert (HXline : orient A B X = 0).
  { assert (H0 : orient C D X = 0) by (unfold X; apply orient_on_own_chord).
    rewrite (coll_orient_transport A B C D X sg tu HCeq HDeq) in H0.
    apply Rmult_integral in H0.
    destruct H0 as [H0 | H0]; [ contradiction | exact H0 ]. }
  assert (HXeq : X = chord_eval A B (proj_param A B X))
    by (apply proj_param_correct; assumption).
  apply in_app_or in He.
  destruct He as [Hcross | Hcoll].
  - (* e was a proper crossing of CD with some member E *)
    destruct (cross_params_elim G (C, D) e Hcross) as [E [HEG [HxCD Heeq]]].
    destruct E as [E1 E2]; simpl in HxCD, Heeq.
    destruct HxCD as [Hx1 Hx2].
    assert (HndE : nondeg (E1, E2)) by (apply Hnd; exact HEG).
    (* AB crosses E properly as well *)
    assert (HABE : orient A B E1 * orient A B E2 < 0).
    { apply (scale_prod_neg (tu - sg)).
      rewrite <- (coll_orient_transport A B C D E1 sg tu HCeq HDeq).
      rewrite <- (coll_orient_transport A B C D E2 sg tu HCeq HDeq).
      exact Hx1. }
    (* X is the crossing point, so it lies on line E *)
    pose proof (chord_hit C D E1 E2 Hx1 Hx2) as HH.
    cbv zeta in HH.
    destruct HH as [_ [_ Hmeet]].
    assert (HXE : X = chord_eval E1 E2 (chord_s C D E1 E2)).
    { unfold X. rewrite Heeq. exact Hmeet. }
    assert (Hroot : orient E1 E2 (chord_eval A B (proj_param A B X)) = 0).
    { rewrite <- HXeq. rewrite HXE. apply orient_on_own_chord. }
    assert (HEAB : orient E1 E2 A * orient E1 E2 B < 0)
      by (apply (interior_root_gives_cross A B E1 E2 (proj_param A B X));
          assumption).
    assert (Hdet : chord_det A B E1 E2 <> 0)
      by (apply det_nonzero_of_opposite; exact HEAB).
    pose proof (chord_hit A B E1 E2 HABE HEAB) as HH2.
    cbv zeta in HH2.
    destruct HH2 as [_ [_ Hmeet2]].
    assert (Hparam : proj_param A B X = chord_t A B E1 E2).
    { destruct (chord_hit_unique A B E1 E2 Hdet
                  (proj_param A B X) (chord_s C D E1 E2)
                  (chord_t A B E1 E2) (chord_s A B E1 E2)) as [Hq _];
        [ rewrite <- HXeq; exact HXE | exact Hmeet2 | exact Hq ]. }
    unfold cut_params2. apply in_or_app. left.
    rewrite Hparam.
    apply (cross_params_spec G (A, B) (E1, E2));
      [ exact HEG | simpl; split; assumption ].
  - (* e was a projected endpoint of a member collinear with CD *)
    destruct (coll_params_elim G (C, D) e Hcoll) as [F [HFG [Hcol Hpick]]].
    destruct (collinear_b_elim _ _ Hcol) as [HF1 HF2]; simpl in HF1, HF2.
    assert (HndF : nondeg F) by (apply Hnd; exact HFG).
    (* F is collinear with AB as well *)
    assert (HFA1 : orient A B (fst F) = 0).
    { rewrite (coll_orient_transport A B C D (fst F) sg tu HCeq HDeq) in HF1.
      apply Rmult_integral in HF1.
      destruct HF1 as [H | H]; [ contradiction | exact H ]. }
    assert (HFA2 : orient A B (snd F) = 0).
    { rewrite (coll_orient_transport A B C D (snd F) sg tu HCeq HDeq) in HF2.
      apply Rmult_integral in HF2.
      destruct HF2 as [H | H]; [ contradiction | exact H ]. }
    assert (HcolAB : collinear_b (A, B) F = true)
      by (apply collinear_b_intro; simpl; assumption).
    destruct (coll_params_spec G (A, B) F HFG HcolAB) as [Hm1 Hm2].
    simpl in Hm1, Hm2.
    unfold cut_params2. apply in_or_app. right.
    (* X is that endpoint of F *)
    destruct Hpick as [E | E].
    + assert (HXF : X = fst F).
      { unfold X. rewrite E. symmetry.
        apply proj_param_correct; [ exact HndCD | exact HF1 ]. }
      rewrite HXF. exact Hm1.
    + assert (HXF : X = snd F).
      { unfold X. rewrite E. symmetry.
        apply proj_param_correct; [ exact HndCD | exact HF2 ]. }
      rewrite HXF. exact Hm2.
Qed.

(* No endpoint of a collinear neighbour's piece lies strictly inside a piece. *)
Lemma coll_endpoint_excluded :
  forall (G : list (Point * Point)) (A B C D : Point) (ab cd : R * R) (e : R),
    (forall X, In X G -> nondeg X) ->
    In (A, B) G -> In (C, D) G ->
    orient A B C = 0 -> orient A B D = 0 ->
    In ab (cut_all (cut_params2 (A, B) G)) ->
    In cd (cut_all (cut_params2 (C, D) G)) ->
    (e = fst cd \/ e = snd cd) ->
    ~ (fst ab < proj_param A B (chord_eval C D e) < snd ab).
Proof.
  intros G A B C D ab cd e Hnd HAB HCD HC0 HD0 Hab Hcd He Hinside.
  destruct (cut_all_bounds _ _ Hab) as [Ha0 [Hab1 Hb1]].
  assert (Hg01 : 0 < proj_param A B (chord_eval C D e) < 1) by lra.
  assert (Hmem : In (proj_param A B (chord_eval C D e)) (cut_params2 (A, B) G)).
  { destruct (cut_all_endpoint_in _ _ Hcd) as [Hcz Hdo].
    destruct He as [E | E]; subst e.
    - destruct Hcz as [E0 | Hin].
      + rewrite E0, chord_eval_zero.
        unfold cut_params2. apply in_or_app. right.
        assert (Hcol : collinear_b (A, B) (C, D) = true)
          by (apply collinear_b_intro; simpl; assumption).
        destruct (coll_params_spec G (A, B) (C, D) HCD Hcol) as [Hm1 _].
        simpl in Hm1. exact Hm1.
      + apply cut_param_transport; assumption.
    - destruct Hdo as [E1 | Hin].
      + rewrite E1, chord_eval_one.
        unfold cut_params2. apply in_or_app. right.
        assert (Hcol : collinear_b (A, B) (C, D) = true)
          by (apply collinear_b_intro; simpl; assumption).
        destruct (coll_params_spec G (A, B) (C, D) HCD Hcol) as [_ Hm2].
        simpl in Hm2. exact Hm2.
      + apply cut_param_transport; assumption. }
  apply (cut_all_excludes (cut_params2 (A, B) G) _ ab Hmem Hab).
  exact Hinside.
Qed.

(* --------------------------------------------------------------------------
   COOK 2's guarantees.
   -------------------------------------------------------------------------- *)

Theorem cook2_noded :
  forall (G : list (Point * Point)) (P Q : Point * Point),
    In P (cook2 G) -> In Q (cook2 G) -> ~ crosses P Q.
Proof.
  intros G P Q HP HQ.
  apply (proj1 (cook2_In G P)) in HP.
  apply (proj1 (cook2_In G Q)) in HQ.
  revert P Q HP HQ.
  apply pieces_noded.
  intros AB CD HAB HCD Hx.
  unfold cut_params2. apply in_or_app. left.
  apply cross_params_spec; assumption.
Qed.

Theorem cook2_covers :
  forall (G : list (Point * Point)) (AB : Point * Point) (t : R),
    In AB G -> 0 <= t <= 1 ->
    exists (P : Point * Point) (u : R),
      In P (cook2 G) /\ 0 <= u <= 1
      /\ chord_eval (fst P) (snd P) u = chord_eval (fst AB) (snd AB) t.
Proof.
  intros G AB t HAB Ht.
  destruct (pieces_covers (fun X => cut_params2 X G) G AB t HAB Ht)
    as [P [u [HP [Hu Heq]]]].
  exists P, u.
  split; [ apply (proj2 (cook2_In G P)); exact HP | split; assumption ].
Qed.

Theorem cook2_within :
  forall (G : list (Point * Point)) (P : Point * Point) (u : R),
    In P (cook2 G) -> 0 <= u <= 1 ->
    exists (AB : Point * Point) (t : R),
      In AB G /\ 0 <= t <= 1
      /\ chord_eval (fst AB) (snd AB) t = chord_eval (fst P) (snd P) u.
Proof.
  intros G P u HP Hu.
  apply (proj1 (cook2_In G P)) in HP.
  apply (pieces_within (fun X => cut_params2 X G) G P u HP Hu).
Qed.

Corollary cook2_split_noded :
  forall (G : list (Point * Point)) (P Q : Point * Point) (t s : R),
    In P (cook2 G) -> In Q (cook2 G) ->
    0 <= t <= 1 -> 0 <= s <= 1 ->
    chord_eval (fst P) (snd P) t = chord_eval (fst Q) (snd Q) s ->
    t = 0 \/ t = 1 \/ s = 0 \/ s = 1
    \/ (orient (fst P) (snd P) (fst Q) = 0
        /\ orient (fst P) (snd P) (snd Q) = 0).
Proof.
  intros G P Q t s HP HQ Ht Hs Hmeet.
  apply (chord_split_noded (cook2 G)); try assumption.
  intros X Y HX HY. exact (cook2_noded G X Y HX HY).
Qed.

(* THE "ONLY IF" HALF.  Two pieces of `cook2 G` that meet away from their
   endpoints are the same piece, or the same piece reversed.  The collinear
   escape hatch of `cook_split_noded` is gone. *)
Theorem cook2_split_noded_strict :
  forall (G : list (Point * Point)) (P Q : Point * Point) (t s : R),
    (forall X, In X G -> nondeg X) ->
    In P (cook2 G) -> In Q (cook2 G) ->
    0 <= t <= 1 -> 0 <= s <= 1 ->
    chord_eval (fst P) (snd P) t = chord_eval (fst Q) (snd Q) s ->
    t = 0 \/ t = 1 \/ s = 0 \/ s = 1 \/ P = Q \/ P = (snd Q, fst Q).
Proof.
  intros G P Q t s Hnd HP HQ Ht Hs Hmeet.
  destruct (total_order_T t 0) as [[Hta | Hta] | Hta];
    [ exfalso; lra | left; exact Hta | ].
  destruct (total_order_T t 1) as [[Htb | Htb] | Htb];
    [ | right; left; exact Htb | exfalso; lra ].
  destruct (total_order_T s 0) as [[Hsa | Hsa] | Hsa];
    [ exfalso; lra | right; right; left; exact Hsa | ].
  destruct (total_order_T s 1) as [[Hsb | Hsb] | Hsb];
    [ | right; right; right; left; exact Hsb | exfalso; lra ].
  right; right; right; right.
  (* the collinear case is the only one left *)
  pose proof (cook2_split_noded G P Q t s HP HQ Ht Hs Hmeet) as Hcase.
  assert (Hcol : orient (fst P) (snd P) (fst Q) = 0
                 /\ orient (fst P) (snd P) (snd Q) = 0)
    by (destruct Hcase as [E | [E | [E | [E | E]]]];
        solve [ exfalso; lra | exact E ]).
  clear Hcase.
  apply (proj1 (cook2_In G P)) in HP.
  apply (proj1 (cook2_In G Q)) in HQ.
  destruct (pieces_shape _ G P HP) as [AB [ab [HABG [Hab HPeq]]]].
  destruct (pieces_shape _ G Q HQ) as [CD [cd [HCDG [Hcd HQeq]]]].
  destruct (cut_all_bounds _ _ Hab) as [Ha0 [Hab1 Hb1]].
  destruct (cut_all_bounds _ _ Hcd) as [Hc0 [Hcd1 Hd1]].
  destruct AB as [A B]; destruct CD as [C D].
  destruct ab as [a b]; destruct cd as [c d].
  simpl in Hab, Hcd, Ha0, Hab1, Hb1, Hc0, Hcd1, Hd1.
  subst P Q.
  unfold subchord in Hcol, Hmeet; simpl in Hcol, Hmeet.
  destruct Hcol as [Hcol1 Hcol2].
  assert (HndAB : nondeg (A, B)) by (apply Hnd; exact HABG).
  assert (HndCD : nondeg (C, D)) by (apply Hnd; exact HCDG).
  (* strip the piece scaling from the orientations *)
  rewrite subchord_orient in Hcol1, Hcol2.
  assert (Hba : b - a <> 0) by lra.
  assert (Hq1 : orient A B (chord_eval C D c) = 0)
    by (apply Rmult_integral in Hcol1;
        destruct Hcol1 as [H | H]; [ contradiction | exact H ]).
  assert (Hq2 : orient A B (chord_eval C D d) = 0)
    by (apply Rmult_integral in Hcol2;
        destruct Hcol2 as [H | H]; [ contradiction | exact H ]).
  rewrite orient_affine_third in Hq1, Hq2.
  assert (Hcdne : c <> d) by lra.
  destruct (two_affine_zero _ _ c d Hcdne Hq1 Hq2) as [HC0 HD0].
  (* transport CD onto AB's parameter *)
  set (sg := proj_param A B C).
  set (tu := proj_param A B D).
  assert (HCeq : C = chord_eval A B sg)
    by (apply proj_param_correct; assumption).
  assert (HDeq : D = chord_eval A B tu)
    by (apply proj_param_correct; assumption).
  assert (Hk : tu - sg <> 0).
  { intro Hz.
    assert (HCD2 : C = D) by (rewrite HCeq, HDeq; f_equal; lra).
    unfold nondeg in HndCD; simpl in HndCD.
    destruct HndCD as [H | H]; apply H; rewrite HCD2; reflexivity. }
  assert (HevC : forall x, chord_eval C D x = chord_eval A B (sg + x * (tu - sg)))
    by (intro x; apply (coll_eval_transport A B C D sg tu x HCeq HDeq)).
  (* AB is collinear with CD too *)
  assert (HA0 : orient C D A = 0).
  { rewrite (coll_orient_transport A B C D A sg tu HCeq HDeq).
    unfold orient; ring. }
  assert (HB0 : orient C D B = 0).
  { rewrite (coll_orient_transport A B C D B sg tu HCeq HDeq).
    unfold orient; ring. }
  (* the four exclusions *)
  assert (Hex1 : ~ (a < sg + c * (tu - sg) < b)).
  { intro Hbad. apply (coll_endpoint_excluded G A B C D (a, b) (c, d) c
                         Hnd HABG HCDG HC0 HD0 Hab Hcd
                         (or_introl eq_refl)).
    simpl. rewrite HevC. rewrite proj_param_eval by exact HndAB. exact Hbad. }
  assert (Hex2 : ~ (a < sg + d * (tu - sg) < b)).
  { intro Hbad. apply (coll_endpoint_excluded G A B C D (a, b) (c, d) d
                         Hnd HABG HCDG HC0 HD0 Hab Hcd
                         (or_intror eq_refl)).
    simpl. rewrite HevC. rewrite proj_param_eval by exact HndAB. exact Hbad. }
  (* AB's endpoints, seen from CD *)
  set (u := proj_param C D (chord_eval A B a)).
  set (w := proj_param C D (chord_eval A B b)).
  assert (Hau : a = sg + u * (tu - sg)).
  { apply (chord_eval_inj A B); [ exact HndAB | ].
    rewrite <- HevC.
    apply proj_param_correct; [ exact HndCD | ].
    rewrite (coll_orient_transport A B C D (chord_eval A B a) sg tu HCeq HDeq).
    rewrite orient_on_own_chord. ring. }
  assert (Hbw : b = sg + w * (tu - sg)).
  { apply (chord_eval_inj A B); [ exact HndAB | ].
    rewrite <- HevC.
    apply proj_param_correct; [ exact HndCD | ].
    rewrite (coll_orient_transport A B C D (chord_eval A B b) sg tu HCeq HDeq).
    rewrite orient_on_own_chord. ring. }
  assert (Hex3 : ~ (c < u < d)).
  { intro Hbad. apply (coll_endpoint_excluded G C D A B (c, d) (a, b) a
                         Hnd HCDG HABG HA0 HB0 Hcd Hab
                         (or_introl eq_refl)).
    simpl. exact Hbad. }
  assert (Hex4 : ~ (c < w < d)).
  { intro Hbad. apply (coll_endpoint_excluded G C D A B (c, d) (a, b) b
                         Hnd HCDG HABG HA0 HB0 Hcd Hab
                         (or_intror eq_refl)).
    simpl. exact Hbad. }
  (* the meeting parameter, in AB's coordinate *)
  rewrite !subchord_reparam in Hmeet.
  rewrite HevC in Hmeet.
  assert (Hth : a + t * (b - a)
                = sg + (c + s * (d - c)) * (tu - sg))
    by (apply (chord_eval_inj A B); [ exact HndAB | exact Hmeet ]).
  apply not_between in Hex1. apply not_between in Hex2.
  apply not_between in Hex3. apply not_between in Hex4.
  assert (Hth1 : a < a + t * (b - a) < b) by nra.
  assert (Hmid : c < c + s * (d - c) < d) by nra.
  set (k := tu - sg) in *.
  clearbody k.
  set (th := a + t * (b - a)) in *.
  clearbody th.
  set (m := c + s * (d - c)) in *.
  clearbody m.
  assert (Hgoal : (a = sg + c * k /\ b = sg + d * k)
                  \/ (a = sg + d * k /\ b = sg + c * k)).
  { destruct (Rdichotomy _ _ Hk) as [Hneg | Hpos].
    - (* k < 0 : the transport reverses order *)
      right.
      assert (Hbg : b <= sg + c * k) by (destruct Hex1 as [H | H]; nra).
      assert (Hda : sg + d * k <= a) by (destruct Hex2 as [H | H]; nra).
      assert (Hcw : c <= w) by nra.
      assert (Hud : u <= d) by nra.
      assert (Hwu : w < u) by nra.
      assert (Hdu : d <= u) by (destruct Hex3 as [H | H]; lra).
      assert (Hwc : w <= c) by (destruct Hex4 as [H | H]; lra).
      assert (Hu2 : u = d) by lra.
      assert (Hw2 : w = c) by lra.
      rewrite Hu2 in Hau. rewrite Hw2 in Hbw.
      split; [ exact Hau | exact Hbw ].
    - (* k > 0 : order preserved *)
      left.
      assert (Hga : sg + c * k <= a) by (destruct Hex1 as [H | H]; nra).
      assert (Hbd : b <= sg + d * k) by (destruct Hex2 as [H | H]; nra).
      assert (Hcu : c <= u) by nra.
      assert (Hwd : w <= d) by nra.
      assert (Huw : u < w) by nra.
      assert (Huc : u <= c) by (destruct Hex3 as [H | H]; lra).
      assert (Hdw : d <= w) by (destruct Hex4 as [H | H]; lra).
      assert (Hu2 : u = c) by lra.
      assert (Hw2 : w = d) by lra.
      rewrite Hu2 in Hau. rewrite Hw2 in Hbw.
      split; [ exact Hau | exact Hbw ]. }
  unfold subchord; simpl.
  rewrite !HevC.
  destruct Hgoal as [[E1 E2] | [E1 E2]].
  - left. rewrite E1, E2. reflexivity.
  - right. simpl. rewrite E1, E2. reflexivity.
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
   The repair is NOT to add `chord_det <> 0`: that would exclude the case by
   hypothesis instead of classifying it.  The repair shipped above is the
   collinear disjunct in `chord_split_noded`, which names the overlap as an
   outcome, and `cook_split_noded`, which supplies the no-crossing premise
   from a constructor rather than assuming it.
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
Print Assumptions cook_noded.
Print Assumptions cook2_noded.
Print Assumptions cook2_nodup.
Print Assumptions cook2_split_noded.
Print Assumptions cook2_split_noded_strict.
Print Assumptions cook2_covers.
Print Assumptions cook2_within.
Print Assumptions cook_split_noded.
Print Assumptions cook_covers.
Print Assumptions cook_within.
Print Assumptions chord_split_noded_hypothesis_free_false.

(* ============================================================================
   NetTopologySuite.Proofs.LECCandidateComplete
   ----------------------------------------------------------------------------
   GENERAL CANDIDATE COMPLETENESS -- the theorem a trusted O(n log n) LEC
   needs, for ARBITRARY finite point-site sets (the summit rung's general
   half; the witness half landed in LECCandidateVertex.v with the statement
   shape and proof technique this file generalises).

   An O(n log n) largest-empty-circle implementation (JTS/NTS
   LargestEmptyCircle over point sites) evaluates the clearance only at a
   finite candidate set: Voronoi vertices (>= 3 equidistant nearest sites),
   bisector/boundary crossings (>= 2 equidistant nearest sites on the
   domain boundary), and domain vertices.  Candidate completeness is the
   statement that this enumeration cannot miss the optimum.  Contrapositive
   form, which is what this file proves CONSTRUCTIVELY: every non-candidate
   point is strictly improvable, so no maximiser is a non-candidate.

     - `improvement_kernel`: the single engine.  Given a direction d with
       <d, p - s> >= 0 at every nearest site (and any behaviour at far
       sites), the shifted point p + t*d strictly beats clearance r for
       every small t > 0.  The inner product may be ZERO: the quadratic
       term t^2*|d|^2 of

           dist_sq (p + t*d) s  =  r^2 + 2*t*<d, p - s> + t^2*|d|^2

       already forces strict improvement.  This one hypothesis shape
       covers all the classical cases at once -- unique nearest site
       (d = p - s0), two nearest sites in general position
       (d = (p - s1) + (p - s2), both inner products strictly positive via
       the nonzero-square trick, no Cauchy-Schwarz needed), two ANTIPODAL
       nearest sites (d = the perpendicular, both inner products exactly
       zero), and the edge-constrained case (d = +/- the edge direction).

     - `within_two_improvable` / `within_one_improvable_on_segment`: the
       positive, fully constructive improvement theorems.  At most two
       (resp. one, along an edge) nearest sites  =>  an explicitly
       constructed strictly better centre exists arbitrarily close.

     - `lec_candidate_completeness_interior`: a maximiser with an interior
       ball cannot have its nearest sites covered by two points -- i.e.
       an interior maximiser is a Voronoi vertex (>= 3 nearest sites).
     - `lec_candidate_completeness_boundary_edge`: a maximiser in the open
       part of a domain edge cannot have a unique nearest site -- i.e. an
       edge maximiser is a bisector crossing (>= 2 nearest sites).
       Domain vertices are the only remaining boundary points: together
       the three candidate classes are exhaustive for maximisers.

   F8 (ledger failed path): "the >= 3-nearest conclusion holds for
   maximisers over ANY convex domain, no interiority premise" -- REFUTED.
   Two sites at (0,0) and (2,0) with the domain their connecting segment:
   the midpoint (1,0) IS the largest-empty-disk centre (radius 1) yet has
   exactly TWO nearest sites (`f8_interiority_load_bearing`).  The domain
   has empty interior, so the interior theorem's ball premise fails at
   every point, and the edge theorem permits two nearest sites -- the
   instance also witnesses that `nearest_within_one` genuinely fails at
   the midpoint (`f8_midpoint_not_within_one`), so the theorem family is
   consistent on it.  Degenerate (lower-dimensional) domains route to the
   edge kernel, never to the interior one.

   Everything is Qed-closed and classic-free (standard Reals trio only):
   the improvement theorems CONSTRUCT their witnesses, and the maximiser
   corollaries are stated in negation form, so no classical existence
   extraction is ever needed.

   Corpus invariant preserved: no Admitted / Axiom / Parameter.
   topic: metric

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude (Fable)
   ============================================================================ *)

From Stdlib Require Import Reals.
From Stdlib Require Import Lra.
From Stdlib Require Import List.
Import ListNotations.

From NTS.Proofs Require Import Distance.
From NTS.Proofs Require Import MaximumInscribedCircle.
From NTS.Proofs Require Import LargestEmptyCircle.
From NTS.Proofs Require Import LECObstacleDistance.
From NTS.Proofs Require Import LECFlattenRow.

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §0  Point sites as a Region; squared-distance shift algebra.               *)
(* -------------------------------------------------------------------------- *)

(** A finite set of point sites, as the lane's obstacle [Region]. *)
Definition sites_region (sites : list Point) : Region :=
  fun P => In P sites.

(** Dovetail with the typed table: the same region, spelled through
    [LECFlattenRow]'s constructors. *)
Lemma sites_region_typed_iff :
  forall (sites : list Point) (P : Point),
    typed_list_region (map TPoint sites) P <-> sites_region sites P.
Proof.
  intros sites P. unfold sites_region.
  induction sites as [| a tl IH].
  - unfold typed_list_region. simpl. unfold rnone. tauto.
  - unfold typed_list_region in *. simpl. unfold runion.
    simpl in IH. split.
    + intros [HP | HP]; [left; symmetry; exact HP | right; apply IH, HP].
    + intros [HP | HP]; [left; symmetry; exact HP | right; apply IH, HP].
Qed.

(** The shifted centre: [p] moved by [t] along direction [(dx, dy)]. *)
Definition shift (p : Point) (dx dy t : R) : Point :=
  pt_translate p (t * dx) (t * dy).

(** The whole file runs on this one polynomial identity. *)
Lemma dist_sq_shift :
  forall (p s : Point) (dx dy t : R),
    dist_sq (shift p dx dy t) s
    = dist_sq p s
      + 2 * t * (dx * (px p - px s) + dy * (py p - py s))
      + t * t * (dx * dx + dy * dy).
Proof.
  intros p s dx dy t. unfold shift, pt_translate, dist_sq. simpl. ring.
Qed.

Lemma dist_sq_shift_centre :
  forall (p : Point) (dx dy t : R),
    dist_sq p (shift p dx dy t) = t * t * (dx * dx + dy * dy).
Proof.
  intros p dx dy t. unfold shift, pt_translate, dist_sq. simpl. ring.
Qed.

Lemma dist_mul_self : forall p q : Point, dist p q * dist p q = dist_sq p q.
Proof.
  intros p q. unfold dist. apply sqrt_sqrt, dist_sq_nonneg.
Qed.

(** The squared distance under a known distance. *)
Lemma dist_sq_of_dist :
  forall (p q : Point) (r : R), dist p q = r -> dist_sq p q = r * r.
Proof.
  intros p q r Hd. rewrite <- dist_mul_self, Hd. reflexivity.
Qed.

(** Strict order transfers from squares to distances. *)
Lemma lt_dist_of_lt_sq :
  forall (p q : Point) (r : R),
    0 <= r -> r * r < dist_sq p q -> r < dist p q.
Proof.
  intros p q r Hr Hlt.
  rewrite <- (sqrt_square r Hr). unfold dist.
  apply sqrt_lt_1_alt. split; [apply Rmult_le_pos; assumption | exact Hlt].
Qed.

(** How far the shift moves the centre. *)
Lemma dist_shift_centre :
  forall (p : Point) (dx dy t : R),
    0 <= t ->
    dist p (shift p dx dy t) = t * sqrt (dx * dx + dy * dy).
Proof.
  intros p dx dy t Ht. unfold dist.
  rewrite dist_sq_shift_centre.
  rewrite sqrt_mult_alt by (apply Rmult_le_pos; exact Ht).
  rewrite sqrt_square by exact Ht. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* §1  Finite-list glue: a uniform step bound, and strict clearance bounds.   *)
(* -------------------------------------------------------------------------- *)

(** Finitely many per-site step bounds admit one uniform bound. *)
Lemma uniform_tau :
  forall (P : Point -> R -> Prop) (l : list Point),
    (forall s, In s l -> exists tau, 0 < tau /\
       forall t, 0 < t -> t < tau -> P s t) ->
    exists tau, 0 < tau /\
      forall s t, In s l -> 0 < t -> t < tau -> P s t.
Proof.
  intros P l. induction l as [| a tl IH]; intros H.
  - exists 1. split; [lra |]. intros s t [] _ _.
  - destruct (H a (in_eq a tl)) as [ta [Hta Ha]].
    destruct IH as [tt [Htt Htl]].
    { intros s Hs. apply H, in_cons, Hs. }
    exists (Rmin ta tt). split; [apply Rmin_glb_lt; assumption |].
    intros s t Hs Ht Hlt. destruct (in_inv Hs) as [-> | Hin].
    + apply Ha; [exact Ht |]. apply Rlt_le_trans with (Rmin ta tt);
        [exact Hlt | apply Rmin_l].
    + apply Htl; [exact Hin | exact Ht |].
      apply Rlt_le_trans with (Rmin ta tt); [exact Hlt | apply Rmin_r].
Qed.

(** The nearest site of a nonempty list is attained. *)
Lemma min_dist_attained :
  forall (p : Point) (l : list Point),
    l <> [] ->
    exists s, In s l /\ forall s', In s' l -> dist p s <= dist p s'.
Proof.
  intros p l. induction l as [| a tl IH]; intros Hne; [congruence |].
  destruct tl as [| b tl'].
  - exists a. split; [apply in_eq |].
    intros s' Hs'. destruct (in_inv Hs') as [-> | []]. apply Rle_refl.
  - destruct IH as [m [Hm Hmin]]; [congruence |].
    destruct (Rle_dec (dist p a) (dist p m)) as [Hle | Hgt].
    + exists a. split; [apply in_eq |].
      intros s' Hs'. destruct (in_inv Hs') as [-> | Hin].
      * apply Rle_refl.
      * apply Rle_trans with (dist p m); [exact Hle | apply Hmin, Hin].
    + exists m. split; [apply in_cons, Hm |].
      intros s' Hs'. destruct (in_inv Hs') as [-> | Hin].
      * left. apply Rnot_le_lt, Hgt.
      * apply Hmin, Hin.
Qed.

(** Pointwise strict clearance over a nonempty list yields a strictly
    larger uniform clearance radius. *)
Lemma strict_clearance_radius :
  forall (p : Point) (l : list Point) (r : R),
    l <> [] ->
    (forall s, In s l -> r < dist p s) ->
    exists rho, r < rho /\ forall s, In s l -> rho <= dist p s.
Proof.
  intros p l r Hne Hall.
  destruct (min_dist_attained p l Hne) as [m [Hm Hmin]].
  exists (dist p m). split; [apply Hall, Hm |].
  intros s Hs. apply Hmin, Hs.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  The improvement kernel.                                                *)
(* -------------------------------------------------------------------------- *)

(** THE ENGINE.  If direction [(dx, dy)] is nonzero, points away-or-tangent
    from every nearest site (inner product >= 0 -- zero is allowed, the
    quadratic term takes over), and the remaining sites are strictly
    farther than [r], then every small positive step strictly clears [r]
    at EVERY site. *)
Theorem improvement_kernel :
  forall (sites : list Point) (p : Point) (r dx dy : R),
    0 < r ->
    0 < dx * dx + dy * dy ->
    (forall s, In s sites ->
       r < dist p s \/
       (dist p s = r /\ 0 <= dx * (px p - px s) + dy * (py p - py s))) ->
    exists tau, 0 < tau /\
      forall t, 0 < t -> t < tau ->
        forall s, In s sites -> r < dist (shift p dx dy t) s.
Proof.
  intros sites p r dx dy Hr HL Hdir.
  assert (HsL : 0 < sqrt (dx * dx + dy * dy)) by (apply sqrt_lt_R0; exact HL).
  destruct (uniform_tau (fun s t => r < dist (shift p dx dy t) s) sites)
    as [tau [Htau Hall]].
  { intros s Hs. destruct (Hdir s Hs) as [Hfar | [Hnear Hip]].
    - (* far site: the move is too short to eat the slack *)
      exists ((dist p s - r) / sqrt (dx * dx + dy * dy)). split.
      + apply Rdiv_lt_0_compat; lra.
      + intros t Ht Hlt.
        assert (Hmove : dist p (shift p dx dy t)
                        = t * sqrt (dx * dx + dy * dy))
          by (apply dist_shift_centre; lra).
        assert (Htri : dist p s <= dist p (shift p dx dy t)
                                     + dist (shift p dx dy t) s)
          by apply dist_triangle.
        assert (Hfield : (dist p s - r) / sqrt (dx * dx + dy * dy)
                         * sqrt (dx * dx + dy * dy) = dist p s - r)
          by (field; lra).
        assert (Hstep : t * sqrt (dx * dx + dy * dy) < dist p s - r).
        { rewrite <- Hfield.
          apply Rmult_lt_compat_r; [exact HsL | exact Hlt]. }
        lra.
    - (* nearest site: away-or-tangent, the quadratic term wins *)
      exists 1. split; [lra |].
      intros t Ht _.
      apply lt_dist_of_lt_sq; [lra |].
      rewrite dist_sq_shift.
      rewrite (dist_sq_of_dist p s r Hnear).
      assert (H2 : 0 <= 2 * t * (dx * (px p - px s) + dy * (py p - py s)))
        by (apply Rmult_le_pos; lra).
      assert (H3 : 0 < t * t * (dx * dx + dy * dy))
        by (apply Rmult_lt_0_compat; [apply Rmult_lt_0_compat; lra | lra]).
      lra. }
  exists tau. split; [exact Htau |].
  intros t Ht Hlt s Hs. apply Hall; assumption.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Non-candidate configurations, and their improving directions.          *)
(* -------------------------------------------------------------------------- *)

(** All nearest sites (at radius [r]) are covered by two named ones.  Note
    [s1 = s2] expresses "at most one nearest site". *)
Definition nearest_within_two
    (sites : list Point) (p : Point) (r : R) (s1 s2 : Point) : Prop :=
  In s1 sites /\ In s2 sites /\ dist p s1 = r /\ dist p s2 = r /\
  forall s, In s sites -> dist p s = r -> s = s1 \/ s = s2.

(** All nearest sites are covered by one named one. *)
Definition nearest_within_one
    (sites : list Point) (p : Point) (r : R) (s0 : Point) : Prop :=
  In s0 sites /\ dist p s0 = r /\
  forall s, In s sites -> dist p s = r -> s = s0.

(** A within-two configuration supplies a kernel-ready direction: the sum
    of the two away-vectors when it is nonzero (both inner products then
    strictly positive, by the nonzero-square trick -- no Cauchy-Schwarz
    needed), and the perpendicular of either when the away-vectors are
    antipodal (both inner products exactly zero; the kernel's >= 0
    tolerance is what makes this case free). *)
Lemma within_two_direction :
  forall (sites : list Point) (p : Point) (r : R) (s1 s2 : Point),
    0 < r ->
    (forall s, In s sites -> r <= dist p s) ->
    nearest_within_two sites p r s1 s2 ->
    exists dx dy,
      0 < dx * dx + dy * dy /\
      forall s, In s sites ->
        r < dist p s \/
        (dist p s = r /\ 0 <= dx * (px p - px s) + dy * (py p - py s)).
Proof.
  intros sites p r s1 s2 Hr Hcl (Hin1 & Hin2 & Hd1 & Hd2 & Hcover).
  set (u1x := px p - px s1). set (u1y := py p - py s1).
  set (u2x := px p - px s2). set (u2y := py p - py s2).
  assert (Hsq1 : u1x * u1x + u1y * u1y = r * r).
  { unfold u1x, u1y.
    replace ((px p - px s1) * (px p - px s1)
             + (py p - py s1) * (py p - py s1))
      with (dist_sq p s1) by (unfold dist_sq; ring).
    apply dist_sq_of_dist, Hd1. }
  assert (Hsq2 : u2x * u2x + u2y * u2y = r * r).
  { unfold u2x, u2y.
    replace ((px p - px s2) * (px p - px s2)
             + (py p - py s2) * (py p - py s2))
      with (dist_sq p s2) by (unfold dist_sq; ring).
    apply dist_sq_of_dist, Hd2. }
  (* the per-site disjunction only ever needs the two cover cases plus
     "strictly farther", which follows from clearance + not-equal *)
  assert (Hsite : forall dx dy,
             0 <= dx * u1x + dy * u1y ->
             0 <= dx * u2x + dy * u2y ->
             forall s, In s sites ->
               r < dist p s \/
               (dist p s = r /\
                0 <= dx * (px p - px s) + dy * (py p - py s))).
  { intros dx dy Hip1 Hip2 s Hs.
    destruct (total_order_T r (dist p s)) as [[Hlt | Heq] | Hgt].
    - left. exact Hlt.
    - right. split; [symmetry; exact Heq |].
      destruct (Hcover s Hs (eq_sym Heq)) as [-> | ->].
      + exact Hip1.
      + exact Hip2.
    - exfalso. specialize (Hcl s Hs). lra. }
  destruct (total_order_T 0 ((u1x + u2x) * (u1x + u2x)
                             + (u1y + u2y) * (u1y + u2y)))
    as [[Hpos | Hzero] | Hneg].
  - (* generic: d = u1 + u2, both inner products strictly positive *)
    assert (Hexp : (u1x + u2x) * (u1x + u2x) + (u1y + u2y) * (u1y + u2y)
                   = (u1x * u1x + u1y * u1y) + (u2x * u2x + u2y * u2y)
                     + 2 * (u1x * u2x + u1y * u2y)) by ring.
    rewrite Hsq1, Hsq2 in Hexp.
    assert (Hip12 : - (r * r) < u1x * u2x + u1y * u2y) by lra.
    exists (u1x + u2x), (u1y + u2y).
    split; [exact Hpos |].
    apply Hsite.
    + assert (He1 : (u1x + u2x) * u1x + (u1y + u2y) * u1y
                    = (u1x * u1x + u1y * u1y)
                      + (u1x * u2x + u1y * u2y)) by ring.
      rewrite He1, Hsq1. lra.
    + assert (He2 : (u1x + u2x) * u2x + (u1y + u2y) * u2y
                    = (u2x * u2x + u2y * u2y)
                      + (u1x * u2x + u1y * u2y)) by ring.
      rewrite He2, Hsq2. lra.
  - (* antipodal: u2 = -u1; d = perp u1, both inner products zero *)
    symmetry in Hzero.
    assert (Hax : u1x + u2x = 0).
    { destruct (Req_EM_T (u1x + u2x) 0) as [H0 | Hne0]; [exact H0 |].
      exfalso. pose proof (Rsqr_pos_lt _ Hne0) as Hp.
      pose proof (Rle_0_sqr (u1y + u2y)) as Hq.
      unfold Rsqr in Hp, Hq. lra. }
    assert (Hay : u1y + u2y = 0).
    { destruct (Req_EM_T (u1y + u2y) 0) as [H0 | Hne0]; [exact H0 |].
      exfalso. pose proof (Rsqr_pos_lt _ Hne0) as Hp.
      pose proof (Rle_0_sqr (u1x + u2x)) as Hq.
      unfold Rsqr in Hp, Hq. lra. }
    assert (Hu2x : u2x = - u1x) by lra.
    assert (Hu2y : u2y = - u1y) by lra.
    exists (- u1y), u1x.
    split.
    + assert (HdL : - u1y * - u1y + u1x * u1x = u1x * u1x + u1y * u1y)
        by ring.
      rewrite HdL, Hsq1.
      apply Rmult_lt_0_compat; lra.
    + apply Hsite.
      * assert (Hz : - u1y * u1x + u1x * u1y = 0) by ring. lra.
      * rewrite Hu2x, Hu2y.
        assert (Hz : - u1y * - u1x + u1x * - u1y = 0) by ring. lra.
  - (* a sum of squares is never negative *)
    exfalso.
    pose proof (Rle_0_sqr (u1x + u2x)) as Ha.
    pose proof (Rle_0_sqr (u1y + u2y)) as Hb.
    unfold Rsqr in Ha, Hb. lra.
Qed.

(** THE POSITIVE IMPROVEMENT THEOREM (interior form).  At most two nearest
    sites at positive clearance  =>  a strictly better centre is
    constructed at every sufficiently small step along an explicit
    direction.  This is candidate completeness in constructive dress:
    non-candidates never win. *)
Theorem within_two_improvable :
  forall (sites : list Point) (p : Point) (r : R) (s1 s2 : Point),
    0 < r ->
    (forall s, In s sites -> r <= dist p s) ->
    nearest_within_two sites p r s1 s2 ->
    exists dx dy tau,
      0 < dx * dx + dy * dy /\ 0 < tau /\
      forall t, 0 < t -> t < tau ->
        forall s, In s sites -> r < dist (shift p dx dy t) s.
Proof.
  intros sites p r s1 s2 Hr Hcl Hw2.
  destruct (within_two_direction sites p r s1 s2 Hr Hcl Hw2)
    as [dx [dy [HL Hdir]]].
  destruct (improvement_kernel sites p r dx dy Hr HL Hdir)
    as [tau [Htau Himp]].
  exists dx, dy, tau. auto.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  The edge-constrained kernel.                                           *)
(* -------------------------------------------------------------------------- *)

(** Strict interior of the segment [a, b], parametrically. *)
Definition on_open_segment (a b q : Point) : Prop :=
  exists theta, 0 < theta < 1 /\
    px q = px a + theta * (px b - px a) /\
    py q = py a + theta * (py b - py a).

(** A within-one configuration on an edge supplies a direction ALONG the
    edge: the sign is chosen so the inner product with the away-vector is
    >= 0; when the edge is perpendicular to the away-vector both signs
    give zero and the quadratic term improves regardless (the "site
    directly under the edge" case, no case split needed). *)
Lemma within_one_direction_along :
  forall (sites : list Point) (a b p : Point) (r : R) (s0 : Point),
    0 < r ->
    0 < (px b - px a) * (px b - px a) + (py b - py a) * (py b - py a) ->
    (forall s, In s sites -> r <= dist p s) ->
    nearest_within_one sites p r s0 ->
    exists dx dy,
      ((dx = px b - px a /\ dy = py b - py a) \/
       (dx = - (px b - px a) /\ dy = - (py b - py a))) /\
      0 < dx * dx + dy * dy /\
      forall s, In s sites ->
        r < dist p s \/
        (dist p s = r /\ 0 <= dx * (px p - px s) + dy * (py p - py s)).
Proof.
  intros sites a b p r s0 Hr He Hcl (Hin0 & Hd0 & Hcover).
  set (ex := px b - px a). set (ey := py b - py a).
  set (u0x := px p - px s0). set (u0y := py p - py s0).
  assert (Hsite : forall dx dy,
             0 <= dx * u0x + dy * u0y ->
             forall s, In s sites ->
               r < dist p s \/
               (dist p s = r /\
                0 <= dx * (px p - px s) + dy * (py p - py s))).
  { intros dx dy Hip s Hs.
    destruct (total_order_T r (dist p s)) as [[Hlt | Heq] | Hgt].
    - left. exact Hlt.
    - right. split; [symmetry; exact Heq |].
      rewrite (Hcover s Hs (eq_sym Heq)). exact Hip.
    - exfalso. specialize (Hcl s Hs). lra. }
  destruct (Rle_dec 0 (ex * u0x + ey * u0y)) as [Hge | Hlt].
  - exists ex, ey. split; [left; split; reflexivity |].
    split; [exact He |]. apply Hsite. exact Hge.
  - apply Rnot_le_lt in Hlt.
    exists (- ex), (- ey). split; [right; split; reflexivity |].
    split.
    + assert (Hsq : - ex * - ex + - ey * - ey = ex * ex + ey * ey) by ring.
      rewrite Hsq. exact He.
    + apply Hsite.
      assert (Hneg : - ex * u0x + - ey * u0y
                     = - (ex * u0x + ey * u0y)) by ring.
      lra.
Qed.

(** THE POSITIVE IMPROVEMENT THEOREM (edge form).  A unique nearest site
    at a point strictly inside a segment  =>  a strictly better centre
    exists ON the open segment. *)
Theorem within_one_improvable_on_segment :
  forall (sites : list Point) (a b p : Point) (r : R) (s0 : Point),
    0 < r ->
    0 < (px b - px a) * (px b - px a) + (py b - py a) * (py b - py a) ->
    on_open_segment a b p ->
    (forall s, In s sites -> r <= dist p s) ->
    nearest_within_one sites p r s0 ->
    exists q, on_open_segment a b q /\
      forall s, In s sites -> r < dist q s.
Proof.
  intros sites a b p r s0 Hr He Hseg Hcl Hw1.
  destruct Hseg as [theta [Hth [Hpx Hpy]]].
  destruct (within_one_direction_along sites a b p r s0 Hr He Hcl Hw1)
    as [dx [dy [Hsign [HL Hdir]]]].
  destruct (improvement_kernel sites p r dx dy Hr HL Hdir)
    as [tau [Htau Himp]].
  set (t := Rmin (tau / 2) (Rmin (theta / 2) ((1 - theta) / 2))).
  assert (Ht : 0 < t).
  { unfold t. apply Rmin_glb_lt; [lra |]. apply Rmin_glb_lt; lra. }
  assert (Httau : t < tau).
  { unfold t. apply Rle_lt_trans with (tau / 2); [apply Rmin_l | lra]. }
  assert (Hthl : t < theta).
  { unfold t.
    apply Rle_lt_trans with (Rmin (theta / 2) ((1 - theta) / 2));
      [apply Rmin_r |].
    apply Rle_lt_trans with (theta / 2); [apply Rmin_l | lra]. }
  assert (Hthr : t < 1 - theta).
  { unfold t.
    apply Rle_lt_trans with (Rmin (theta / 2) ((1 - theta) / 2));
      [apply Rmin_r |].
    apply Rle_lt_trans with ((1 - theta) / 2); [apply Rmin_r | lra]. }
  exists (shift p dx dy t). split.
  - destruct Hsign as [[-> ->] | [-> ->]].
    + exists (theta + t). split; [lra |].
      unfold shift, pt_translate. simpl. rewrite Hpx, Hpy.
      split; ring.
    + exists (theta - t). split; [lra |].
      unfold shift, pt_translate. simpl. rewrite Hpx, Hpy.
      split; ring.
  - intros s Hs. apply Himp; assumption.
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  Candidate completeness for maximisers (the trusted-LEC theorems).      *)
(* -------------------------------------------------------------------------- *)

(** An interior maximiser is a Voronoi vertex: its nearest sites can NEVER
    be covered by two points.  Stated in negation form so the proof stays
    classic-free; the positive reading is ">= 3 pairwise-distinct nearest
    sites", which is exactly the candidate class an O(n log n) LEC
    enumerates via the Voronoi diagram. *)
Theorem lec_candidate_completeness_interior :
  forall (sites : list Point) (dom : Region) (p : Point) (r eps : R),
    sites <> [] ->
    0 < r ->
    0 < eps ->
    (forall q, dist p q < eps -> dom q) ->
    largest_empty_disk (sites_region sites) dom p r ->
    ~ (exists s1 s2, nearest_within_two sites p r s1 s2).
Proof.
  intros sites dom p r eps Hne Hr Heps Hball
         (Hdom & (Hr0 & Hcl) & Hmax) [s1 [s2 Hw2]].
  destruct (within_two_improvable sites p r s1 s2 Hr Hcl Hw2)
    as [dx [dy [tau [HL [Htau Himp]]]]].
  assert (HsL : 0 < sqrt (dx * dx + dy * dy)) by (apply sqrt_lt_R0; exact HL).
  set (t := Rmin (tau / 2) (eps / (2 * sqrt (dx * dx + dy * dy)))).
  assert (Ht : 0 < t).
  { unfold t. apply Rmin_glb_lt; [lra |].
    apply Rdiv_lt_0_compat; lra. }
  assert (Httau : t < tau).
  { unfold t. apply Rle_lt_trans with (tau / 2); [apply Rmin_l | lra]. }
  set (q := shift p dx dy t).
  assert (Hmove : dist p q < eps).
  { unfold q. rewrite dist_shift_centre by lra.
    assert (Hhalf : eps / (2 * sqrt (dx * dx + dy * dy))
                    * sqrt (dx * dx + dy * dy) = eps / 2)
      by (field; lra).
    apply Rle_lt_trans with (eps / 2); [| lra].
    rewrite <- Hhalf.
    apply Rmult_le_compat_r; [lra |].
    unfold t. apply Rmin_r. }
  assert (Hstrict : forall s, In s sites -> r < dist q s).
  { intros s Hs. unfold q. apply Himp; assumption. }
  destruct (strict_clearance_radius q sites r Hne Hstrict)
    as [rho [Hrho Hrho_cl]].
  assert (Hemp : empty_disk (sites_region sites) q rho).
  { split; [lra |]. intros P HP. apply Hrho_cl, HP. }
  specialize (Hmax q rho (Hball q Hmove) Hemp). lra.
Qed.

(** A maximiser strictly inside a domain edge is a bisector crossing: it
    can never have a unique nearest site.  Domain vertices are the only
    remaining boundary candidates, completing the three-class candidate
    enumeration. *)
Theorem lec_candidate_completeness_boundary_edge :
  forall (sites : list Point) (dom : Region) (a b p : Point) (r : R),
    sites <> [] ->
    0 < r ->
    0 < (px b - px a) * (px b - px a) + (py b - py a) * (py b - py a) ->
    on_open_segment a b p ->
    (forall q, on_open_segment a b q -> dom q) ->
    largest_empty_disk (sites_region sites) dom p r ->
    ~ (exists s0, nearest_within_one sites p r s0).
Proof.
  intros sites dom a b p r Hne Hr He Hseg Hsub
         (Hdom & (Hr0 & Hcl) & Hmax) [s0 Hw1].
  destruct (within_one_improvable_on_segment
              sites a b p r s0 Hr He Hseg Hcl Hw1)
    as [q [Hqseg Hstrict]].
  destruct (strict_clearance_radius q sites r Hne Hstrict)
    as [rho [Hrho Hrho_cl]].
  assert (Hemp : empty_disk (sites_region sites) q rho).
  { split; [lra |]. intros P HP. apply Hrho_cl, HP. }
  specialize (Hmax q rho (Hsub q Hqseg) Hemp). lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §6  F8: the interiority premise is load-bearing.                           *)
(* -------------------------------------------------------------------------- *)

Definition f8_sL : Point := mkPoint 0 0.
Definition f8_sR : Point := mkPoint 2 0.
Definition f8_sites : list Point := [f8_sL; f8_sR].
Definition f8_p : Point := mkPoint 1 0.

(** The connecting segment, closed, as the domain. *)
Definition f8_dom : Region :=
  fun q => exists theta, 0 <= theta <= 1 /\
    px q = 2 * theta /\ py q = 0.

Lemma f8_dist_sL : dist f8_p f8_sL = 1.
Proof.
  unfold dist.
  replace (dist_sq f8_p f8_sL) with 1
    by (unfold dist_sq, f8_p, f8_sL; simpl; ring).
  apply sqrt_1.
Qed.

Lemma f8_dist_sR : dist f8_p f8_sR = 1.
Proof.
  unfold dist.
  replace (dist_sq f8_p f8_sR) with 1
    by (unfold dist_sq, f8_p, f8_sR; simpl; ring).
  apply sqrt_1.
Qed.

Lemma f8_led : largest_empty_disk (sites_region f8_sites) f8_dom f8_p 1.
Proof.
  split; [| split].
  - exists (1 / 2). unfold f8_p. simpl. lra.
  - split; [lra |].
    intros P HP. unfold sites_region in HP. simpl in HP.
    destruct HP as [HP | [HP | []]].
    + rewrite <- HP, f8_dist_sL. lra.
    + rewrite <- HP, f8_dist_sR. lra.
  - intros q rho [theta [Hth [Hqx Hqy]]] [Hrho Hemp].
    assert (HdL : dist q f8_sL = 2 * theta).
    { unfold dist.
      replace (dist_sq q f8_sL) with ((2 * theta) * (2 * theta))
        by (unfold dist_sq, f8_sL; simpl; rewrite Hqx, Hqy; ring).
      apply sqrt_square. lra. }
    assert (HdR : dist q f8_sR = 2 - 2 * theta).
    { unfold dist.
      replace (dist_sq q f8_sR) with ((2 - 2 * theta) * (2 - 2 * theta))
        by (unfold dist_sq, f8_sR; simpl; rewrite Hqx, Hqy; ring).
      apply sqrt_square. lra. }
    assert (HL : rho <= dist q f8_sL)
      by (apply Hemp; unfold sites_region; simpl; left; reflexivity).
    assert (HR : rho <= dist q f8_sR)
      by (apply Hemp; unfold sites_region; simpl; right; left; reflexivity).
    lra.
Qed.

Lemma f8_within_two :
  nearest_within_two f8_sites f8_p 1 f8_sL f8_sR.
Proof.
  split; [left; reflexivity |].
  split; [right; left; reflexivity |].
  split; [exact f8_dist_sL |].
  split; [exact f8_dist_sR |].
  intros s Hs _. simpl in Hs.
  destruct Hs as [Hs | [Hs | []]];
    [left; symmetry; exact Hs | right; symmetry; exact Hs].
Qed.

(** F8, REFUTED HYPOTHESIS: dropping the interior-ball premise from
    `lec_candidate_completeness_interior` makes it FALSE -- a maximiser
    over a degenerate (empty-interior) domain can have exactly two
    nearest sites.  The candidate classes below Voronoi vertices are
    genuinely load-bearing. *)
Theorem f8_interiority_load_bearing :
  exists (sites : list Point) (dom : Region) (p : Point) (r : R)
         (s1 s2 : Point),
    sites <> [] /\ 0 < r /\
    largest_empty_disk (sites_region sites) dom p r /\
    nearest_within_two sites p r s1 s2.
Proof.
  exists f8_sites, f8_dom, f8_p, 1, f8_sL, f8_sR.
  split; [discriminate |].
  split; [lra |].
  split; [exact f8_led | exact f8_within_two].
Qed.

(** Consistency witness: the F8 midpoint has TWO distinct nearest sites,
    so `nearest_within_one` fails there and the edge theorem's conclusion
    is compatible with the instance (the midpoint IS a bisector
    crossing). *)
Lemma f8_midpoint_not_within_one :
  forall s0, ~ nearest_within_one f8_sites f8_p 1 s0.
Proof.
  intros s0 (Hin0 & Hd0 & Hcover).
  assert (HL : f8_sL = s0)
    by (apply Hcover; [left; reflexivity | exact f8_dist_sL]).
  assert (HR : f8_sR = s0)
    by (apply Hcover; [right; left; reflexivity | exact f8_dist_sR]).
  assert (Habs : px f8_sL = px f8_sR) by (rewrite HL, HR; reflexivity).
  unfold f8_sL, f8_sR in Habs. simpl in Habs. lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions sites_region_typed_iff.
Print Assumptions dist_sq_shift.
Print Assumptions dist_sq_shift_centre.
Print Assumptions dist_mul_self.
Print Assumptions dist_sq_of_dist.
Print Assumptions lt_dist_of_lt_sq.
Print Assumptions dist_shift_centre.
Print Assumptions uniform_tau.
Print Assumptions min_dist_attained.
Print Assumptions strict_clearance_radius.
Print Assumptions improvement_kernel.
Print Assumptions within_two_direction.
Print Assumptions within_two_improvable.
Print Assumptions within_one_direction_along.
Print Assumptions within_one_improvable_on_segment.
Print Assumptions lec_candidate_completeness_interior.
Print Assumptions lec_candidate_completeness_boundary_edge.
Print Assumptions f8_led.
Print Assumptions f8_within_two.
Print Assumptions f8_interiority_load_bearing.
Print Assumptions f8_midpoint_not_within_one.

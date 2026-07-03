(* ==========================================================================
   CornerGapKit.v

   [H-bridge attack, C-3d step 2a] Two corner tools the general-fan corner
   connector needs, both cheap consequences of banked machinery:

     - FOREIGN-RAY EXCLUSION.  The strict sector certificate is invariant
       under positive scaling of the query (`in_open_sector_scale`), so a
       certified offset can never lie on a ray whose DIRECTION is not
       certified (`sector_off_foreign_ray`).  Fed with
       `FanGapSector.fan_next_gap_empty_sector` -- no fan direction is
       certified inside the next-gap -- this makes every corner polyline
       point avoid EVERY edge germ at the vertex, not just the two walls:
       the germ's v-based dart is a fan member, its segment near the
       vertex is a ray in a fan direction, and that direction fails the
       certificate.
     - THE OFF-RING CORNER.  When the shared vertex is NOT on the ring,
       no sector reasoning is needed at all: the sup-metric clearance
       ball (`RingClearance.ring_complement_ball`) is CONVEX, so any two
       samples inside it connect by a SINGLE chord
       (`ball_chord_connected`), packaged with the ball as
       `off_ring_corner_ball`.  This closes the transport corner case for
       every face-walk vertex away from the cycle.

   Pure algebra + assembly; no `Admitted` / `Axiom` / `Parameter`;
   allowlist axioms only.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
   ========================================================================== *)

From Stdlib Require Import Reals Lra List.
From NTS.Proofs Require Import Distance Overlay OverlayGraph Vec Direction
                               Dart PointInRingTangents JordanCurveSeam
                               JCTHugStep RingClearance SectorPath
                               CornerSamples CornerConnector.

Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  The sector certificate is scale-invariant in the query.                 *)
(* -------------------------------------------------------------------------- *)

Lemma in_open_sector_scale :
  forall u1 u2 m t,
    0 < t ->
    (in_open_sector u1 u2 (vscale t m) <-> in_open_sector u1 u2 m).
Proof.
  intros u1 u2 m t Ht.
  unfold in_open_sector.
  rewrite vcross_scale_r, vcross_scale_l.
  split; intros [[Hc [H1 H2]] | [Hc Hor]].
  - left. split; [ exact Hc | split; nra ].
  - right. split; [ exact Hc | destruct Hor as [H1 | H1]; [ left | right ]; nra ].
  - left. split; [ exact Hc | split; nra ].
  - right. split; [ exact Hc | destruct Hor as [H1 | H1]; [ left | right ]; nra ].
Qed.

(* A certified offset never lies on the closed ray of a NON-certified
   direction -- the germ-exclusion mechanism (feed the negative
   certificate from `FanGapSector.fan_next_gap_empty_sector`). *)
Lemma sector_off_foreign_ray :
  forall u1 u2 w m,
    in_open_sector u1 u2 w ->
    ~ in_open_sector u1 u2 m ->
    forall t, 0 <= t -> w <> vscale t m.
Proof.
  intros u1 u2 w m Hw Hm t Ht Heq. subst w.
  assert (Hcase : 0 < t \/ t = 0) by lra.
  destruct Hcase as [Hpos | Hzero].
  - exact (Hm (proj1 (in_open_sector_scale u1 u2 m t Hpos) Hw)).
  - subst t.
    unfold in_open_sector in Hw.
    rewrite vcross_scale_r, vcross_scale_l in Hw.
    destruct Hw as [[_ [H1 _]] | [_ [H1 | H1]]]; nra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  The off-ring corner: one chord inside the convex clearance ball.        *)
(* -------------------------------------------------------------------------- *)

(* Any two vertex-relative offsets inside a complement-valued sup-ball
   connect by a single straight hop (sup-balls are convex; the chord's
   coordinates are bounded by the endpoints'). *)
Lemma ball_chord_connected :
  forall (r : Ring) (v : Point) (eps : R) (A B : Vec),
    (forall q : Point,
       Rabs (px q - px v) < eps -> Rabs (py q - py v) < eps ->
       ring_complement r q) ->
    Rabs (vx A) < eps -> Rabs (vy A) < eps ->
    Rabs (vx B) < eps -> Rabs (vy B) < eps ->
    connected_in_complement_cont r (point_at v A) (point_at v B).
Proof.
  intros r v eps A B Hball HAx HAy HBx HBy.
  apply hop_connected. intros t Ht.
  apply Hball.
  - replace (px (point_at v (vaffine t A B)) - px v)
      with (vx (vaffine t A B))
      by (unfold point_at; cbn; ring).
    eapply Rle_lt_trans; [ apply vaffine_bound_x; exact Ht | ].
    apply Rmax_lub_lt; assumption.
  - replace (py (point_at v (vaffine t A B)) - py v)
      with (vy (vaffine t A B))
      by (unfold point_at; cbn; ring).
    eapply Rle_lt_trans; [ apply vaffine_bound_y; exact Ht | ].
    apply Rmax_lub_lt; assumption.
Qed.

(* The complete off-ring corner: a vertex in the ring complement carries a
   positive radius within which ALL corner samples are mutually connected
   in the complement -- no sector analysis needed away from the cycle. *)
Theorem off_ring_corner_ball :
  forall (r : Ring) (v : Point),
    no_horizontal_edges r ->
    ring_complement r v ->
    exists eps, 0 < eps /\
      forall A B : Vec,
        Rabs (vx A) < eps -> Rabs (vy A) < eps ->
        Rabs (vx B) < eps -> Rabs (vy B) < eps ->
        connected_in_complement_cont r (point_at v A) (point_at v B).
Proof.
  intros r v Hnoh Hcomp.
  destruct (ring_complement_ball r v Hnoh Hcomp) as [eps [Heps Hball]].
  exists eps. split; [ exact Heps | ].
  intros A B HAx HAy HBx HBy.
  apply (ball_chord_connected r v eps); assumption.
Qed.

(* -------------------------------------------------------------------------- *)
(* Axiom audit.  Pure algebra + assembly; allowlist axioms only.               *)
(* -------------------------------------------------------------------------- *)

Print Assumptions sector_off_foreign_ray.
Print Assumptions off_ring_corner_ball.

(* ============================================================================
   NetTopologySuite.Proofs.BufferEndcapSquare
   ----------------------------------------------------------------------------
   GREEN for micro-claim 65-c: the SQUARE endcap is exactly the U-shaped
   boundary of the square erected forward on the flat diameter —
   completing the ENDCAP TRIO's carrier characterisations
   (65-a flat = diameter segment, BufferEndcapDiameter.v;
    65-b round = forward semicircle, BufferEndcapSemicircle.v;
    65-c square = forward square U, this file).

   BufferEndcap.v ships the square cap's point-facts
   (`square_cap_extension`, `square_cap_corner_dist_sq`); this file
   closes the carrier biconditional: q lies on the three-segment walk
       cap_endpoint(-d) -> fwd-corner(-d) -> fwd-corner(d) -> cap_endpoint(d)
   IF AND ONLY IF q is the frame image of the unit square's boundary
   minus its open bottom side,
       q = E + d*(a*unit_perp ein + b*unit_dir ein),
       (a = -1 /\ 0 <= b <= 1) \/ (b = 1 /\ -1 <= a <= 1) \/
       (a =  1 /\ 0 <= b <= 1).
   The open bottom side is semantic: the diameter belongs to the FLAT
   cap (65-a), not to the square walk.

   One vocabulary note: the corpus's `sq_corner E ein d` pushes the
   boundary point by the SIGNED d along the edge, so for the minus side
   it would go backward.  The cap's corners both push FORWARD by +d:
   `sq_corner_fwd E ein side d` below (side = +-d); on the plus side it
   coincides definitionally with the corpus's `sq_corner`
   (`sq_corner_fwd_plus_is_sq_corner`, by conversion).

   Proof style: entirely LINEAR — no circle, no sqrt, no vmag; each of
   the three segments pins one frame coordinate and the between
   parameter sweeps the other, so all six directions close by lra over
   ring-normalised monomials in the unit_dir/unit_perp components.

   Mutation hardening at plant time (ADR-0004, the trio's discipline):
   `sq_corner_fwd_forward_signed` — BOTH corners' signed forward
   coordinate along unit_dir is exactly d, for ALL side values (kills
   d-sign flips on the forward push; companion of
   cap_endpoint_signed_side and round_apex_forward_signed).

   Mirrors eval/Claim65c.v (same WITNESS tag), which carries the
   self-contained unit-tangent version plus the rational pins
   (corners at dist_sq 2 echoing square_cap_corner_dist_sq; the face
   midpoint = the round apex, the trio's cross-cap seam; terminal off
   all sides; signed corner frame).

   WITNESS claimId: 65-c
   topic: buffer
   Lemma: square_endcap_is_diameter_square

   No `Admitted`, no `Axiom`, no `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import Vec Direction Distance Segment
                               BufferOffset BufferEndcap.
Open Scope R_scope.

(* WITNESS {"claimId":"65-c","topic":"buffer","lemma":"square_endcap_is_diameter_square","title":"Square endcap = U-boundary of the forward square on the flat diameter"} *)

(* -------------------------------------------------------------------------- *)
(* §1  The forward corners.                                                   *)
(* -------------------------------------------------------------------------- *)

(* The boundary point on side `side` (+-d), pushed FORWARD by d along the
   edge direction — the square cap's outer corners. *)
Definition sq_corner_fwd (E : Point) (ein : Vec) (side d : R) : Point :=
  pt_translate (cap_endpoint E ein side)
               (d * vx (unit_dir ein)) (d * vy (unit_dir ein)).

(* On the plus side this IS the corpus's sq_corner (by conversion). *)
Lemma sq_corner_fwd_plus_is_sq_corner : forall E ein d,
    sq_corner_fwd E ein d d = sq_corner E ein d.
Proof. reflexivity. Qed.

(* -------------------------------------------------------------------------- *)
(* §2  The 65-c headline in corpus vocabulary.                                *)
(* -------------------------------------------------------------------------- *)

Theorem square_endcap_is_diameter_square :
  forall (E : Point) (ein : Vec) (d : R) (q : Point),
    ein <> vzero ->
    0 < d ->
    ((between (cap_endpoint E ein (- d)) (sq_corner_fwd E ein (- d) d) q \/
      between (sq_corner_fwd E ein (- d) d) (sq_corner_fwd E ein d d) q \/
      between (sq_corner_fwd E ein d d) (cap_endpoint E ein d) q)
     <->
     (exists a b : R,
        ((a = -1 /\ 0 <= b <= 1) \/
         (b = 1 /\ -1 <= a <= 1) \/
         (a = 1 /\ 0 <= b <= 1)) /\
        px q = px E + d * (a * vx (unit_perp ein) + b * vx (unit_dir ein)) /\
        py q = py E + d * (a * vy (unit_perp ein) + b * vy (unit_dir ein)))).
Proof.
  intros E ein d q Hnz Hd.
  unfold between, sq_corner_fwd, cap_endpoint, pt_translate.
  cbn [px py].
  split.
  - (* walk => frame image: read (a,b) off the segment parameter *)
    intros [ [s [H0 [H1 [Hx Hy]]]]
           | [ [s [H0 [H1 [Hx Hy]]]] | [s [H0 [H1 [Hx Hy]]]] ] ].
    + exists (-1), s.
      split; [ left; repeat split; lra | split; lra ].
    + exists (2 * s - 1), 1.
      split; [ right; left; repeat split; lra | split; lra ].
    + exists 1, (1 - s).
      split; [ right; right; repeat split; lra | split; lra ].
  - (* frame image => walk: rebuild the segment parameter *)
    intros [a [b [ [ [Ha Hb] | [ [Hb Ha] | [Ha Hb] ] ] [Hx Hy] ] ] ].
    + subst a. left. exists b. repeat split; lra.
    + subst b. right. left. exists ((a + 1) / 2). repeat split; lra.
    + subst a. right. right. exists (1 - b). repeat split; lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Signed pin (ADR-0004 mutation hardening, planted with the Green).      *)
(* -------------------------------------------------------------------------- *)

(* BOTH corners' signed forward coordinate along unit_dir is exactly d —
   for ALL side values, so a sign flip on the forward push (unit_dir, d)
   falsifies it; companion of BufferEndcapDiameter.cap_endpoint_signed_side
   and BufferEndcapSemicircle.round_apex_forward_signed. *)
Theorem sq_corner_fwd_forward_signed :
  forall (E : Point) (ein : Vec) (side d : R),
    ein <> vzero ->
    (px (sq_corner_fwd E ein side d) - px E) * vx (unit_dir ein)
    + (py (sq_corner_fwd E ein side d) - py E) * vy (unit_dir ein) = d.
Proof.
  intros E ein side d Hnz.
  pose proof (vmag_sq_unit_dir ein Hnz) as Hu.
  unfold vmag_sq, vdot in Hu.
  pose proof (vdot_unit_perp_unit_dir ein) as Hperp.
  unfold vdot in Hperp.
  unfold sq_corner_fwd, cap_endpoint, pt_translate. cbn [px py].
  transitivity
    (side * (vx (unit_perp ein) * vx (unit_dir ein)
             + vy (unit_perp ein) * vy (unit_dir ein))
     + d * (vx (unit_dir ein) * vx (unit_dir ein)
            + vy (unit_dir ein) * vy (unit_dir ein))); [ ring | ].
  rewrite Hperp, Hu. ring.
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions square_endcap_is_diameter_square.
Print Assumptions sq_corner_fwd_forward_signed.

(* ============================================================================
   NetTopologySuite.Proofs.BufferEndcapSemicircle
   ----------------------------------------------------------------------------
   GREEN for micro-claim 65-b: the round endcap is EXACTLY the forward
   semicircle at the offset terminal.

   BufferEndcap.v ships the three point-facts of the round cap
   (`round_cap_endpoints_on_circle`, `round_cap_apex_on_circle`): the two
   flat-cap endpoints and the apex lie on the circle of radius |d|.  This
   file closes the 65-b biconditional characterising the WHOLE carrier:
   a point q is on the round cap at terminal E with edge direction ein
   (dist_sq q E = d² AND forward of the flat diameter, dot with
   `unit_dir ein` >= 0) IF AND ONLY IF q is the frame image of the unit
   half-circle,
       q = E + d * (a * unit_perp ein + b * unit_dir ein),
       a² + b² = 1,  0 <= b.
   The forward-dot clause kills the cap-as-full-circle reading; the
   dist_sq = d² clause kills the half-disk reading; together with the eval
   unit's mismatch probes (eval/Claim65b.v) this pins the round-endcap
   geometry the JTS round-cap constructor is about.

   Proof style: sqrt-free — no `vmag`/`sqrt` term appears in any proof
   here.  The unit facts enter only through `vmag_sq_unit_dir` /
   `vmag_sq_unit_perp` (unit-length squares) and the component identity
   `unit_perp = J(unit_dir)`; the geometric core is a raw-real frame
   lemma (`semicircle_frame_core`) closed by `ring`/`field`/`nra`, with
   the frame coordinates a := (q−E)·J(t)/d, b := (q−E)·t/d.

   Mutation hardening at plant time (ADR-0004, the 65-a lesson): the
   biconditional is invariant under d ↦ −d inside d² and under a ↦ −a
   (left/right mirror).  `round_apex_forward_signed` breaks the first —
   the apex's SIGNED forward coordinate is exactly d for ALL signed d;
   `cap_endpoint_forward_dot_zero` + `cap_endpoint_on_round_cap` pin the
   seam — the two flat-diameter endpoints sit on the round cap with
   forward coordinate exactly 0 (the two caps share exactly the diameter
   endpoints, so a rotated or shifted half-circle falsifies them).

   Mirrors eval/Claim65b.v (same WITNESS tag), which carries the
   self-contained unit-tangent version plus the rational witness pins.

   No `Admitted`, no `Axiom`, no `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import Vec Direction Distance BufferOffset BufferEndcap.
Open Scope R_scope.

(* WITNESS {"claimId":"65-b","topic":"buffer","lemma":"round_endcap_is_forward_semicircle","title":"Round endcap = forward semicircle at the offset terminal"} *)

(* -------------------------------------------------------------------------- *)
(* §1  The raw-real frame core: circle-and-forward = unit half-circle image.  *)
(*     (EX,EY) centre, (tx,ty) unit tangent, r radius, (QX,QY) test point.    *)
(* -------------------------------------------------------------------------- *)

Lemma semicircle_frame_core :
  forall (EX EY tx ty r QX QY : R),
    0 < r ->
    tx * tx + ty * ty = 1 ->
    (((QX - EX) * (QX - EX) + (QY - EY) * (QY - EY) = r * r /\
      0 <= (QX - EX) * tx + (QY - EY) * ty)
     <->
     (exists a b : R,
        a * a + b * b = 1 /\
        0 <= b /\
        QX = EX + r * (a * - ty + b * tx) /\
        QY = EY + r * (a * tx + b * ty))).
Proof.
  intros EX EY tx ty r QX QY Hr Hunit.
  assert (Hr0 : r <> 0) by lra.
  split.
  - (* on the circle, forward => frame image *)
    intros [Hdist Hfwd].
    (* Frame coordinates of Q - E, scaled by r: A along J(t), B along t. *)
    set (A := (QY - EY) * tx - (QX - EX) * ty).
    set (B := (QX - EX) * tx + (QY - EY) * ty) in Hfwd |- *.
    assert (Hkey : A * A + B * B = r * r).
    { unfold A, B.
      transitivity
        (((QX - EX) * (QX - EX) + (QY - EY) * (QY - EY)) *
         (tx * tx + ty * ty)); [ ring | ].
      rewrite Hunit, Hdist. ring. }
    exists (A / r), (B / r).
    repeat split.
    + (* a² + b² = 1, by the Lagrange-style identity Hkey *)
      apply (Rmult_eq_reg_r (r * r));
        [ transitivity (A * A + B * B);
          [ field; lra | rewrite Hkey; ring ]
        | intros He; nra ].
    + (* b >= 0 from the forward-side constraint *)
      unfold Rdiv. apply Rmult_le_pos; [ exact Hfwd | ].
      left. apply Rinv_0_lt_compat. lra.
    + (* x component: the frame reconstructs Q *)
      symmetry.
      transitivity (EX + (A * - ty + B * tx)); [ field; lra | ].
      unfold A, B.
      transitivity (EX + (QX - EX) * (tx * tx + ty * ty)); [ ring | ].
      rewrite Hunit. ring.
    + (* y component *)
      symmetry.
      transitivity (EY + (A * tx + B * ty)); [ field; lra | ].
      unfold A, B.
      transitivity (EY + (QY - EY) * (tx * tx + ty * ty)); [ ring | ].
      rewrite Hunit. ring.
  - (* frame image => on the circle, forward *)
    intros [a [b [Hab [Hb [Hqx Hqy]]]]].
    split.
    + rewrite Hqx, Hqy.
      transitivity ((a * a + b * b) * (tx * tx + ty * ty) * (r * r));
        [ ring | rewrite Hab, Hunit; ring ].
    + rewrite Hqx, Hqy.
      replace ((EX + r * (a * - ty + b * tx) - EX) * tx +
               (EY + r * (a * tx + b * ty) - EY) * ty)
        with (b * (tx * tx + ty * ty) * r) by ring.
      rewrite Hunit. nra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  The 65-b headline in corpus vocabulary.                                *)
(* -------------------------------------------------------------------------- *)

(* unit_perp is exactly the π/2 rotation of unit_dir: J(tx,ty) = (-ty,tx). *)
Lemma unit_perp_is_J_unit_dir :
  forall ein,
    vx (unit_perp ein) = - vy (unit_dir ein) /\
    vy (unit_perp ein) = vx (unit_dir ein).
Proof.
  intros ein.
  unfold unit_perp, unit_dir, vperp, vscale. simpl. split; ring.
Qed.

Theorem round_endcap_is_forward_semicircle :
  forall (E : Point) (ein : Vec) (d : R) (q : Point),
    ein <> vzero ->
    0 < d ->
    ((dist_sq q E = d * d /\
      0 <= (px q - px E) * vx (unit_dir ein) + (py q - py E) * vy (unit_dir ein))
     <->
     (exists a b : R,
        a * a + b * b = 1 /\
        0 <= b /\
        px q = px E + d * (a * vx (unit_perp ein) + b * vx (unit_dir ein)) /\
        py q = py E + d * (a * vy (unit_perp ein) + b * vy (unit_dir ein)))).
Proof.
  intros E ein d q Hnz Hd.
  assert (Hunit : vx (unit_dir ein) * vx (unit_dir ein)
                  + vy (unit_dir ein) * vy (unit_dir ein) = 1).
  { pose proof (vmag_sq_unit_dir ein Hnz) as Hu.
    unfold vmag_sq, vdot in Hu. exact Hu. }
  destruct (unit_perp_is_J_unit_dir ein) as [Hpx Hpy].
  rewrite Hpx, Hpy.
  unfold dist_sq.
  exact (semicircle_frame_core (px E) (py E)
           (vx (unit_dir ein)) (vy (unit_dir ein)) d (px q) (py q) Hd Hunit).
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Signed pins (ADR-0004 mutation hardening, planted with the Green).     *)
(* -------------------------------------------------------------------------- *)

(* The apex's SIGNED forward coordinate along unit_dir is exactly d — for
   ALL signed d, so a sign flip anywhere in the tangent chain (unit_dir, d)
   falsifies it; companion of BufferEndcapDiameter.cap_endpoint_signed_side. *)
Theorem round_apex_forward_signed :
  forall (E : Point) (ein : Vec) (d : R),
    ein <> vzero ->
    (px (round_apex E ein d) - px E) * vx (unit_dir ein)
    + (py (round_apex E ein d) - py E) * vy (unit_dir ein) = d.
Proof.
  intros E ein d Hnz.
  pose proof (vmag_sq_unit_dir ein Hnz) as Hu.
  unfold vmag_sq, vdot in Hu.
  unfold round_apex, pt_translate. cbn [px py].
  transitivity (d * (vx (unit_dir ein) * vx (unit_dir ein)
                     + vy (unit_dir ein) * vy (unit_dir ein))); [ ring | ].
  rewrite Hu. ring.
Qed.

(* The flat-diameter endpoints sit exactly ON the forward boundary of the
   round cap: forward coordinate 0 (no hypotheses — a ring identity). *)
Lemma cap_endpoint_forward_dot_zero :
  forall (E : Point) (ein : Vec) (d : R),
    (px (cap_endpoint E ein d) - px E) * vx (unit_dir ein)
    + (py (cap_endpoint E ein d) - py E) * vy (unit_dir ein) = 0.
Proof.
  intros E ein d.
  unfold cap_endpoint, pt_translate, unit_perp, unit_dir, vperp, vscale.
  simpl. ring.
Qed.

(* ... and at squared distance exactly d², hence on the round cap: the two
   caps share exactly the diameter endpoints (seam pin for the assembly). *)
Lemma cap_endpoint_on_round_cap :
  forall (E : Point) (ein : Vec) (d : R),
    ein <> vzero ->
    dist_sq (cap_endpoint E ein d) E = d * d /\
    0 <= (px (cap_endpoint E ein d) - px E) * vx (unit_dir ein)
         + (py (cap_endpoint E ein d) - py E) * vy (unit_dir ein).
Proof.
  intros E ein d Hnz.
  split.
  - unfold cap_endpoint, pt_translate, dist_sq. cbn [px py].
    transitivity (d * d * vmag_sq (unit_perp ein));
      [ unfold vmag_sq, vdot; ring | ].
    rewrite (vmag_sq_unit_perp ein Hnz). ring.
  - rewrite cap_endpoint_forward_dot_zero. lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions round_endcap_is_forward_semicircle.
Print Assumptions round_apex_forward_signed.
Print Assumptions cap_endpoint_on_round_cap.

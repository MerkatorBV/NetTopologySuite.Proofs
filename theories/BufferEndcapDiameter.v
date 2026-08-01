(* ============================================================================
   NetTopologySuite.Proofs.BufferEndcapDiameter
   ----------------------------------------------------------------------------
   GREEN for micro-claim 65-a: the flat endcap is EXACTLY the perpendicular
   diameter segment of the radius-d circle at the terminal point.

   BufferEndcap.v already ships the two half-facts (`flat_cap_length_sq`:
   the cap endpoints are 2d apart; `flat_cap_perp_edge`: the cap chord is
   perpendicular to the edge).  This file closes the 65-a biconditional:
   a point q is BETWEEN the two flat-cap endpoints
   `cap_endpoint E ein (-d)` / `cap_endpoint E ein d`
   IF AND ONLY IF q lies on the perpendicular to the edge direction through
   E (dot with `unit_dir ein` = 0) at squared distance at most d² -- i.e.
   the flat cap is the full perpendicular diameter chord, no more, no less.

   The "no more" half kills the cap-as-infinite-line reading; the "no less"
   half kills any short-chord reading; together with the eval unit's
   mismatch probes (eval/Claim65a.v) this pins the flat-endcap geometry the
   JTS#739 / #1028 artifact reports are about.

   Proof style: sqrt-free.  The normaliser m = vmag ein enters only through
   m > 0 and m * m = vmag_sq ein (the Koc-lane discipline), so every step
   closes with `ring`/`field`/`nra`.

   Mirrors eval/Claim65a.v (same WITNESS tag), which carries the
   self-contained micro-kernel version plus the rational witness pins.

   No `Admitted`, no `Axiom`, no `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import Real Vec Direction Distance Segment
                               BufferOffset BufferAssembly BufferEndcap.
Open Scope R_scope.

(* WITNESS {"claimId":"65-a","topic":"buffer","lemma":"flat_endcap_is_diameter_segment","title":"Flat endcap = perpendicular diameter segment at the offset terminal"} *)

Theorem flat_endcap_is_diameter_segment :
  forall (E : Point) (ein : Vec) (d : R) (q : Point),
    ein <> vzero ->
    0 < d ->
    (between (cap_endpoint E ein (- d)) (cap_endpoint E ein d) q <->
     ((px q - px E) * vx (unit_dir ein) + (py q - py E) * vy (unit_dir ein) = 0 /\
      dist_sq q E <= d * d)).
Proof.
  intros E ein d q Hnz Hd.
  (* Normaliser facts: m > 0 and m * m = ex^2 + ey^2, sqrt-free ever after. *)
  set (ex := vx ein). set (ey := vy ein). set (m := vmag ein).
  assert (Hpos : 0 < vmag_sq ein) by (apply vmag_sq_pos; exact Hnz).
  assert (Hm : 0 < m).
  { unfold m, vmag. apply sqrt_lt_R0. exact Hpos. }
  assert (Hmne : m <> 0) by lra.
  assert (Hmm : m * m = ex * ex + ey * ey).
  { unfold m, vmag. rewrite sqrt_sqrt by lra.
    unfold vmag_sq, vdot, ex, ey. ring. }
  (* Coordinates of the two cap endpoints and the unit direction. *)
  assert (Hcapm_x : px (cap_endpoint E ein (- d)) = px E + d * (ey * / m)).
  { unfold cap_endpoint, pt_translate, unit_perp, vperp, vscale, m, ey.
    simpl. ring. }
  assert (Hcapm_y : py (cap_endpoint E ein (- d)) = py E - d * (ex * / m)).
  { unfold cap_endpoint, pt_translate, unit_perp, vperp, vscale, m, ex.
    simpl. ring. }
  assert (Hcapp_x : px (cap_endpoint E ein d) = px E - d * (ey * / m)).
  { unfold cap_endpoint, pt_translate, unit_perp, vperp, vscale, m, ey.
    simpl. ring. }
  assert (Hcapp_y : py (cap_endpoint E ein d) = py E + d * (ex * / m)).
  { unfold cap_endpoint, pt_translate, unit_perp, vperp, vscale, m, ex.
    simpl. ring. }
  assert (Hdir_x : vx (unit_dir ein) = ex * / m).
  { unfold unit_dir, vscale, m, ex. simpl. ring. }
  assert (Hdir_y : vy (unit_dir ein) = ey * / m).
  { unfold unit_dir, vscale, m, ey. simpl. ring. }
  set (VX := px q - px E). set (VY := py q - py E).
  assert (Hinv : / m * m = 1) by (apply Rinv_l; exact Hmne).
  split.
  - (* between => on-perpendicular within radius *)
    intros [s [Hs0 [Hs1 [Hqx Hqy]]]].
    rewrite Hcapm_x, Hcapp_x in Hqx.
    rewrite Hcapm_y, Hcapp_y in Hqy.
    assert (HVX : VX = (1 - 2 * s) * (d * (ey * / m))).
    { unfold VX. rewrite Hqx. ring. }
    assert (HVY : VY = - (1 - 2 * s) * (d * (ex * / m))).
    { unfold VY. rewrite Hqy. ring. }
    split.
    + rewrite Hdir_x, Hdir_y.
      fold VX VY. rewrite HVX, HVY. ring.
    + assert (Hds : dist_sq q E =
                    ((1 - 2 * s) * (1 - 2 * s)) * (d * d)
                    * ((ex * ex + ey * ey) * (/ m * / m))).
      { unfold dist_sq. fold VX VY. rewrite HVX, HVY. ring. }
      rewrite Hds. rewrite <- Hmm.
      replace ((m * m) * (/ m * / m)) with ((/ m * m) * (/ m * m)) by ring.
      rewrite Hinv.
      assert (Hsq : (1 - 2 * s) * (1 - 2 * s) <= 1) by nra.
      nra.
  - (* on-perpendicular within radius => between *)
    intros [Hdot Hle].
    rewrite Hdir_x, Hdir_y in Hdot. fold VX VY in Hdot.
    (* Clear the /m from the perpendicularity constraint. *)
    assert (Hperp : VX * ex + VY * ey = 0).
    { assert (Hstep : VX * ex + VY * ey
                      = m * (VX * (ex * / m) + VY * (ey * / m)))
        by (field; exact Hmne).
      rewrite Hstep, Hdot. ring. }
    (* The signed coordinate of q - E along the unit normal. *)
    set (lam := (VY * ex - VX * ey) * / m).
    assert (HVXlam : VX = lam * (- ey * / m)).
    { unfold lam.
      apply (Rmult_eq_reg_l (m * m)); [ | nra ].
      transitivity (- ey * (VY * ex - VX * ey) * (/ m * m)).
      2: { field. exact Hmne. }
      rewrite Hinv, Hmm.
      replace (- ey * (VY * ex - VX * ey) * 1)
        with (VX * (ex * ex + ey * ey) - ex * (VX * ex + VY * ey)) by ring.
      rewrite Hperp. ring. }
    assert (HVYlam : VY = lam * (ex * / m)).
    { unfold lam.
      apply (Rmult_eq_reg_l (m * m)); [ | nra ].
      transitivity (ex * (VY * ex - VX * ey) * (/ m * m)).
      2: { field. exact Hmne. }
      rewrite Hinv, Hmm.
      replace (ex * (VY * ex - VX * ey) * 1)
        with (VY * (ex * ex + ey * ey) - ey * (VX * ex + VY * ey)) by ring.
      rewrite Hperp. ring. }
    (* dist_sq is exactly lam^2, so |lam| <= d. *)
    assert (Hlam_sq : lam * lam = dist_sq q E).
    { unfold dist_sq. fold VX VY. rewrite HVXlam, HVYlam.
      transitivity (lam * lam * ((ex * ex + ey * ey) * (/ m * / m)));
        [ | ring ].
      rewrite <- Hmm.
      replace ((m * m) * (/ m * / m)) with ((/ m * m) * (/ m * m)) by ring.
      rewrite Hinv. ring. }
    assert (Hlam_le : lam * lam <= d * d) by (rewrite Hlam_sq; exact Hle).
    assert (Hlam_bnd : - d <= lam <= d) by nra.
    (* Between-witness: s = (d + lam) / (2d). *)
    exists ((d + lam) / (2 * d)).
    assert (H2d : 0 < 2 * d) by lra.
    assert (Hs0 : 0 <= (d + lam) / (2 * d)).
    { unfold Rdiv. apply Rmult_le_pos; [ lra | ].
      left. apply Rinv_0_lt_compat. exact H2d. }
    assert (Hs1 : (d + lam) / (2 * d) <= 1).
    { apply (Rmult_le_reg_r (2 * d)); [ exact H2d | ].
      replace ((d + lam) / (2 * d) * (2 * d)) with (d + lam)
        by (field; lra).
      lra. }
    assert (H2s : 1 - 2 * ((d + lam) / (2 * d)) = - (lam * / d))
      by (field; lra).
    repeat split; [ exact Hs0 | exact Hs1 | | ].
    + (* x coordinate *)
      rewrite Hcapm_x, Hcapp_x.
      transitivity (px E + (1 - 2 * ((d + lam) / (2 * d))) * (d * (ey * / m)));
        [ | ring ].
      rewrite H2s.
      replace (px E + - (lam * / d) * (d * (ey * / m)))
        with (px E + lam * (- ey * / m) * (d * / d)) by ring.
      rewrite Rinv_r by lra.
      rewrite <- HVXlam. unfold VX. ring.
    + (* y coordinate *)
      rewrite Hcapm_y, Hcapp_y.
      transitivity (py E + (1 - 2 * ((d + lam) / (2 * d))) * (- (d * (ex * / m))));
        [ | ring ].
      rewrite H2s.
      replace (py E + - (lam * / d) * (- (d * (ex * / m))))
        with (py E + lam * (ex * / m) * (d * / d)) by ring.
      rewrite Rinv_r by lra.
      rewrite <- HVYlam. unfold VY. ring.
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions flat_endcap_is_diameter_segment.

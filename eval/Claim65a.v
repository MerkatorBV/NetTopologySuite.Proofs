(* ============================================================================
   nts-eval micro unit — claimId 65-a (GREEN)
   Red planted 2026-08-01 (9be9840) · Green closed 2026-08-01 (127a707)
   ----------------------------------------------------------------------------
   Flat endcap geometry is the DIAMETER SEGMENT through the offset terminal
   point, perpendicular to the terminal unit tangent: endpoints p ± r·J(t)
   (J = π/2 rotation), and the cap is exactly the segment joining them —
   equivalently, the perpendicular chord of the radius-r circle at p.

   GREEN.  The headline biconditional is stated
   (`flat_endcap_is_diameter_segment_claim`) and CLOSED in this unit
   (`flat_endcap_is_diameter_segment`, Qed) — the m = 1 self-contained
   version of the production proof.  Production home:
   `theories/BufferEndcapDiameter.v`, the same statement over the corpus's
   `cap_endpoint`/`unit_dir` vocabulary (sqrt-free normaliser m = vmag ein),
   same WITNESS tag.  Red history: the claim was planted 2026-08-01 with
   only the witness pins Qed; Green closed it the same day.

   What IS Qed here: the rational witness pins that fix the intended
   semantics so a wrong Green cannot close the claim vacuously —
   axis-aligned unit segment ending at p = (1,0), tangent t = (1,0), r = 1:
   the cap endpoints are exactly (1,-1) and (1,1); both lie on the
   perpendicular through p at squared distance exactly r²; interior sample
   (1, 1/2) satisfies both sides; and two MISMATCH probes — (1, 3/2) is on
   the perpendicular but outside the disk, (3/2, 0) is off the
   perpendicular — refute the two tempting wrong geometries (infinite
   perpendicular line; cap along the tangent).

   WITNESS claimId: 65-a
   Lemma (Green target): flat_endcap_is_diameter_segment
   ========================================================================== *)

(* WITNESS {"claimId":"65-a","topic":"buffer","lemma":"flat_endcap_is_diameter_segment","title":"Flat endcap = perpendicular diameter segment at the offset terminal"} *)

From Stdlib Require Import Reals Lra.
Local Open Scope R_scope.

Record Point : Type := mkPoint { px : R; py : R }.

Definition dist_sq (p q : Point) : R :=
  (px p - px q) * (px p - px q) + (py p - py q) * (py p - py q).

(* Q on the closed segment P0–P1 (parametric, as in the corpus Segment.v). *)
Definition between (P0 P1 Q : Point) : Prop :=
  exists s : R, 0 <= s /\ s <= 1 /\
    px Q = (1 - s) * px P0 + s * px P1 /\
    py Q = (1 - s) * py P0 + s * py P1.

(* J = π/2 rotation of the unit tangent: J(tx,ty) = (-ty, tx). *)
Definition cap_plus (p t : Point) (r : R) : Point :=
  mkPoint (px p - r * py t) (py p + r * px t).
Definition cap_minus (p t : Point) (r : R) : Point :=
  mkPoint (px p + r * py t) (py p - r * px t).

(* -------------------------------------------------------------------------- *)
(* The 65-a claim (closed below by flat_endcap_is_diameter_segment).          *)
(* Flat endcap = { q : q ⊥-aligned with t through p, within radius r }        *)
(*             = the segment cap_minus(p,t,r) — cap_plus(p,t,r).              *)
(* -------------------------------------------------------------------------- *)

Definition flat_endcap_is_diameter_segment_claim : Prop :=
  forall (p t : Point) (r : R),
    0 < r ->
    px t * px t + py t * py t = 1 ->
    forall q : Point,
      between (cap_minus p t r) (cap_plus p t r) q <->
      ((px q - px p) * px t + (py q - py p) * py t = 0 /\
       dist_sq q p <= r * r).

(* GREEN: the claim is closed below; production home
   theories/BufferEndcapDiameter.v carries the same statement over the
   corpus's cap_endpoint/unit_dir vocabulary (same WITNESS tag). *)

Lemma flat_endcap_is_diameter_segment :
  flat_endcap_is_diameter_segment_claim.
Proof.
  unfold flat_endcap_is_diameter_segment_claim.
  intros p t r Hr Hunit q.
  set (VX := px q - px p). set (VY := py q - py p).
  split.
  - (* between => perpendicular within radius *)
    intros [s [Hs0 [Hs1 [Hqx Hqy]]]].
    unfold cap_minus, cap_plus in Hqx, Hqy; simpl in Hqx, Hqy.
    assert (HVX : VX = (1 - 2 * s) * (r * py t))
      by (unfold VX; rewrite Hqx; ring).
    assert (HVY : VY = - (1 - 2 * s) * (r * px t))
      by (unfold VY; rewrite Hqy; ring).
    split.
    + fold VX VY. rewrite HVX, HVY. ring.
    + assert (Hds : dist_sq q p =
                    ((1 - 2 * s) * (1 - 2 * s)) * (r * r)
                    * (px t * px t + py t * py t)).
      { unfold dist_sq. fold VX VY. rewrite HVX, HVY. ring. }
      rewrite Hds, Hunit.
      assert (Hsq : (1 - 2 * s) * (1 - 2 * s) <= 1) by nra.
      nra.
  - (* perpendicular within radius => between *)
    intros [Hdot Hle].
    fold VX VY in Hdot.
    set (lam := VY * px t - VX * py t).
    assert (HVXlam : VX = lam * (- py t)).
    { unfold lam.
      replace ((VY * px t - VX * py t) * - py t)
        with (VX * (px t * px t + py t * py t)
              - px t * (VX * px t + VY * py t)) by ring.
      rewrite Hunit, Hdot. ring. }
    assert (HVYlam : VY = lam * px t).
    { unfold lam.
      replace ((VY * px t - VX * py t) * px t)
        with (VY * (px t * px t + py t * py t)
              - py t * (VX * px t + VY * py t)) by ring.
      rewrite Hunit, Hdot. ring. }
    assert (Hlam_sq : lam * lam = dist_sq q p).
    { unfold dist_sq. fold VX VY. rewrite HVXlam, HVYlam.
      transitivity (lam * lam * (px t * px t + py t * py t)); [ | ring ].
      rewrite Hunit. ring. }
    assert (Hlam_le : lam * lam <= r * r) by (rewrite Hlam_sq; exact Hle).
    assert (Hlam_bnd : - r <= lam <= r) by nra.
    exists ((r + lam) / (2 * r)).
    assert (H2r : 0 < 2 * r) by lra.
    assert (Hs0 : 0 <= (r + lam) / (2 * r)).
    { unfold Rdiv. apply Rmult_le_pos; [ lra | ].
      left. apply Rinv_0_lt_compat. exact H2r. }
    assert (Hs1 : (r + lam) / (2 * r) <= 1).
    { apply (Rmult_le_reg_r (2 * r)); [ exact H2r | ].
      replace ((r + lam) / (2 * r) * (2 * r)) with (r + lam) by (field; lra).
      lra. }
    assert (H2s : 1 - 2 * ((r + lam) / (2 * r)) = - (lam * / r))
      by (field; lra).
    unfold cap_minus, cap_plus; simpl.
    repeat split; [ exact Hs0 | exact Hs1 | | ].
    + transitivity (px p + (1 - 2 * ((r + lam) / (2 * r))) * (r * py t));
        [ | ring ].
      rewrite H2s.
      replace (px p + - (lam * / r) * (r * py t))
        with (px p + lam * - py t * (r * / r)) by ring.
      rewrite Rinv_r by lra.
      rewrite <- HVXlam. unfold VX. ring.
    + transitivity (py p + (1 - 2 * ((r + lam) / (2 * r))) * (- (r * px t)));
        [ | ring ].
      rewrite H2s.
      replace (py p + - (lam * / r) * (- (r * px t)))
        with (py p + lam * px t * (r * / r)) by ring.
      rewrite Rinv_r by lra.
      rewrite <- HVYlam. unfold VY. ring.
Qed.

(* -------------------------------------------------------------------------- *)
(* Signed-side pins (ADR-0004 mutation hardening).                            *)
(* The unsigned biconditional is genuinely invariant under the endpoint swap  *)
(* (between is endpoint-symmetric) and under r |-> -r inside r*r -- the two   *)
(* mutants that stayed Qed in the #426 review exploited exactly those         *)
(* symmetries.  These pins break them: the cap offsets have SIGNED            *)
(* cross-coordinate along J(t) exactly +r (cap_plus) and -r (cap_minus), so   *)
(* a J |-> -J flip, a plus/minus swap, or an r sign flip each falsifies one.  *)
(* -------------------------------------------------------------------------- *)

Lemma cap_plus_signed_side :
  forall p t r,
    px t * px t + py t * py t = 1 ->
    px t * (py (cap_plus p t r) - py p)
    - py t * (px (cap_plus p t r) - px p) = r.
Proof.
  intros p t r Hunit. unfold cap_plus; simpl.
  transitivity (r * (px t * px t + py t * py t)); [ ring | ].
  rewrite Hunit. ring.
Qed.

Lemma cap_minus_signed_side :
  forall p t r,
    px t * px t + py t * py t = 1 ->
    px t * (py (cap_minus p t r) - py p)
    - py t * (px (cap_minus p t r) - px p) = - r.
Proof.
  intros p t r Hunit. unfold cap_minus; simpl.
  transitivity (- r * (px t * px t + py t * py t)); [ ring | ].
  rewrite Hunit. ring.
Qed.

(* -------------------------------------------------------------------------- *)
(* Rational witness pins (Qed at Red).                                        *)
(* Axis-aligned unit segment (0,0)→(1,0): terminal p=(1,0), tangent t=(1,0),  *)
(* r = 1.  Diameter segment must be (1,-1)—(1,1).                             *)
(* -------------------------------------------------------------------------- *)

Definition w_p : Point := mkPoint 1 0.
Definition w_t : Point := mkPoint 1 0.
Definition w_r : R := 1.

Lemma w_tangent_unit : px w_t * px w_t + py w_t * py w_t = 1.
Proof. unfold w_t; simpl. lra. Qed.

(* Concrete signed pins at the rational witness: +1 / -1, not merely +/-r. *)
Lemma w_signed_sides :
  px w_t * (py (cap_plus w_p w_t w_r) - py w_p)
  - py w_t * (px (cap_plus w_p w_t w_r) - px w_p) = 1 /\
  px w_t * (py (cap_minus w_p w_t w_r) - py w_p)
  - py w_t * (px (cap_minus w_p w_t w_r) - px w_p) = -1.
Proof.
  unfold cap_plus, cap_minus, w_p, w_t, w_r; simpl. split; lra.
Qed.

(* The cap endpoints are exactly (1,1) and (1,-1). *)
Lemma w_cap_plus_eq  : cap_plus  w_p w_t w_r = mkPoint 1 1.
Proof. unfold cap_plus, w_p, w_t, w_r; simpl. f_equal; lra. Qed.

Lemma w_cap_minus_eq : cap_minus w_p w_t w_r = mkPoint 1 (-1).
Proof. unfold cap_minus, w_p, w_t, w_r; simpl. f_equal; lra. Qed.

(* Both endpoints: on the perpendicular through p, at squared distance r². *)
Lemma w_endpoints_pin :
  ((px (cap_plus w_p w_t w_r) - px w_p) * px w_t
   + (py (cap_plus w_p w_t w_r) - py w_p) * py w_t = 0 /\
   dist_sq (cap_plus w_p w_t w_r) w_p = w_r * w_r) /\
  ((px (cap_minus w_p w_t w_r) - px w_p) * px w_t
   + (py (cap_minus w_p w_t w_r) - py w_p) * py w_t = 0 /\
   dist_sq (cap_minus w_p w_t w_r) w_p = w_r * w_r).
Proof.
  unfold cap_plus, cap_minus, dist_sq, w_p, w_t, w_r; simpl.
  repeat split; lra.
Qed.

(* Interior sample (1, 1/2): on the segment AND satisfies the right side. *)
Lemma w_interior_between :
  between (cap_minus w_p w_t w_r) (cap_plus w_p w_t w_r) (mkPoint 1 (1/2)).
Proof.
  unfold between, cap_minus, cap_plus, w_p, w_t, w_r; simpl.
  exists (3/4). repeat split; lra.
Qed.

Lemma w_interior_rhs :
  (px (mkPoint 1 (1/2)) - px w_p) * px w_t
  + (py (mkPoint 1 (1/2)) - py w_p) * py w_t = 0 /\
  dist_sq (mkPoint 1 (1/2)) w_p <= w_r * w_r.
Proof. unfold dist_sq, w_p, w_t, w_r; simpl. split; lra. Qed.

(* MISMATCH PROBE 1: (1, 3/2) is on the perpendicular but OUTSIDE the disk —
   refutes "cap = the whole perpendicular line". *)
Lemma w_probe_outside_disk :
  (px (mkPoint 1 (3/2)) - px w_p) * px w_t
  + (py (mkPoint 1 (3/2)) - py w_p) * py w_t = 0 /\
  ~ dist_sq (mkPoint 1 (3/2)) w_p <= w_r * w_r.
Proof. unfold dist_sq, w_p, w_t, w_r; simpl. split; lra. Qed.

(* MISMATCH PROBE 2: (3/2, 0) is inside the disk but OFF the perpendicular —
   refutes "cap lies along the tangent direction". *)
Lemma w_probe_off_perpendicular :
  dist_sq (mkPoint (3/2) 0) w_p <= w_r * w_r /\
  ~ (px (mkPoint (3/2) 0) - px w_p) * px w_t
    + (py (mkPoint (3/2) 0) - py w_p) * py w_t = 0.
Proof. unfold dist_sq, w_p, w_t, w_r; simpl. split; lra. Qed.

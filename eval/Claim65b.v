(* ============================================================================
   nts-eval micro unit — claimId 65-b (GREEN)
   Red planted 2026-08-02 (e9eaaba) · Green closed 2026-08-02
   ----------------------------------------------------------------------------
   Round endcap geometry is the FORWARD SEMICIRCLE at the offset terminal:
   the set of points at distance exactly r from the terminal p on the
   forward side of the flat diameter (dot with the terminal unit tangent
   t >= 0), and that carrier is exactly the frame image of the unit
   half-circle -- q = p + r*(a*J(t) + b*t) with a^2 + b^2 = 1, b >= 0.

   GREEN.  The headline biconditional is stated
   (`round_endcap_is_forward_semicircle_claim`) and CLOSED in this unit
   (`round_endcap_is_forward_semicircle`, Qed) -- the unit-tangent
   self-contained version of the production proof.  Production home:
   `theories/BufferEndcapSemicircle.v`, the same statement over the
   corpus's `cap_endpoint` / `round_apex` / `unit_dir` / `unit_perp`
   vocabulary, same WITNESS tag.  Red history: the claim was planted
   2026-08-02 with only the witness pins Qed; Green closed it the same
   day.  The proof is the 65-a frame decomposition: forward direction
   sets b := (q-p)·t / r and a := (q-p)·J(t) / r, gets a^2 + b^2 = 1 from
   dist_sq = r^2, and b >= 0 from the forward-side constraint; the
   backward direction is ring algebra over the unit-tangent identity.

   What IS Qed here: rational witness pins fixing the intended semantics --
   terminal p = (1,0), tangent t = (1,0), r = 1:
     - both flat-cap endpoints (1,1)/(1,-1) are ON the cap (a = +/-1, b = 0):
       the round cap meets the flat diameter exactly at its endpoints;
     - the apex (2,0) is ON the cap (a = 0, b = 1) with SIGNED forward
       coordinate exactly +r (sign-sensitive per the 65-a mutation lesson);
     - the BACK point (0,0) is OFF (forward dot = -1 < 0): kills the
       full-circle reading;
     - the centre p is OFF (dist_sq = 0 <> 1): kills the disk reading.

   WITNESS claimId: 65-b
   Lemma (Green target): round_endcap_is_forward_semicircle
   ========================================================================== *)

(* WITNESS {"claimId":"65-b","topic":"buffer","lemma":"round_endcap_is_forward_semicircle","title":"Round endcap = forward semicircle at the offset terminal"} *)

From Stdlib Require Import Reals Lra.
Local Open Scope R_scope.

Record Point : Type := mkPoint { px : R; py : R }.

Definition dist_sq (p q : Point) : R :=
  (px p - px q) * (px p - px q) + (py p - py q) * (py p - py q).

(* The round-cap carrier: on the radius-r circle at p, forward of the flat
   diameter (non-negative dot with the terminal unit tangent t). *)
Definition on_round_cap (p t : Point) (r : R) (q : Point) : Prop :=
  dist_sq q p = r * r /\
  0 <= (px q - px p) * px t + (py q - py p) * py t.

(* -------------------------------------------------------------------------- *)
(* The 65-b claim (RED: stated, not closed).                                  *)
(* The carrier is exactly the frame image of the unit half-circle:            *)
(* q = p + r*(a*J(t) + b*t), a^2 + b^2 = 1, b >= 0  (J(tx,ty) = (-ty,tx)).    *)
(* -------------------------------------------------------------------------- *)

Definition round_endcap_is_forward_semicircle_claim : Prop :=
  forall (p t : Point) (r : R),
    0 < r ->
    px t * px t + py t * py t = 1 ->
    forall q : Point,
      on_round_cap p t r q <->
      (exists a b : R,
          a * a + b * b = 1 /\
          0 <= b /\
          px q = px p + r * (a * (- py t) + b * px t) /\
          py q = py p + r * (a * px t + b * py t)).

(* GREEN: the claim is closed here (self-contained) and mirrored in
   production over cap_endpoint/round_apex/unit_dir/unit_perp
   (theories/BufferEndcapSemicircle.v, same WITNESS tag). *)

Lemma round_endcap_is_forward_semicircle :
  round_endcap_is_forward_semicircle_claim.
Proof.
  unfold round_endcap_is_forward_semicircle_claim.
  intros p t r Hr Hunit q.
  assert (Hr0 : r <> 0) by lra.
  unfold on_round_cap, dist_sq.
  split.
  - (* on the cap => frame image of the unit half-circle *)
    intros [Hdist Hfwd].
    (* Frame coordinates of q - p, scaled by r: A along J(t), B along t. *)
    set (A := (py q - py p) * px t - (px q - px p) * py t).
    set (B := (px q - px p) * px t + (py q - py p) * py t) in Hfwd |- *.
    assert (Hkey : A * A + B * B = r * r).
    { unfold A, B.
      transitivity
        (((px q - px p) * (px q - px p) + (py q - py p) * (py q - py p)) *
         (px t * px t + py t * py t)); [ ring | ].
      rewrite Hunit, Hdist. ring. }
    exists (A / r), (B / r).
    repeat split.
    + (* a^2 + b^2 = 1, by the Lagrange-style identity Hkey *)
      apply (Rmult_eq_reg_r (r * r));
        [ transitivity (A * A + B * B);
          [ field; lra | rewrite Hkey; ring ]
        | intros He; nra ].
    + (* b >= 0 from the forward-side constraint *)
      unfold Rdiv. apply Rmult_le_pos; [ exact Hfwd | ].
      left. apply Rinv_0_lt_compat. lra.
    + (* x component: the frame reconstructs q *)
      symmetry.
      transitivity (px p + (A * - py t + B * px t)); [ field; lra | ].
      unfold A, B.
      transitivity (px p + (px q - px p) * (px t * px t + py t * py t));
        [ ring | ].
      rewrite Hunit. ring.
    + (* y component *)
      symmetry.
      transitivity (py p + (A * px t + B * py t)); [ field; lra | ].
      unfold A, B.
      transitivity (py p + (py q - py p) * (px t * px t + py t * py t));
        [ ring | ].
      rewrite Hunit. ring.
  - (* frame image => on the cap *)
    intros [a [b [Hab [Hb [Hqx Hqy]]]]].
    split.
    + rewrite Hqx, Hqy.
      transitivity ((a * a + b * b) * (px t * px t + py t * py t) * (r * r));
        [ ring | rewrite Hab, Hunit; ring ].
    + rewrite Hqx, Hqy.
      replace ((px p + r * (a * - py t + b * px t) - px p) * px t +
               (py p + r * (a * px t + b * py t) - py p) * py t)
        with (b * (px t * px t + py t * py t) * r) by ring.
      rewrite Hunit. nra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Rational witness pins (Qed at Red).                                        *)
(* Terminal p = (1,0), tangent t = (1,0), r = 1.                              *)
(* -------------------------------------------------------------------------- *)

Definition wb_p : Point := mkPoint 1 0.
Definition wb_t : Point := mkPoint 1 0.
Definition wb_r : R := 1.

Lemma wb_tangent_unit : px wb_t * px wb_t + py wb_t * py wb_t = 1.
Proof. unfold wb_t; simpl. lra. Qed.

(* Both flat-cap endpoints are ON the round cap (the two caps share exactly
   the diameter endpoints); their frame coordinates are (a,b) = (+/-1, 0). *)
Lemma wb_diameter_endpoints_on_cap :
  on_round_cap wb_p wb_t wb_r (mkPoint 1 1) /\
  on_round_cap wb_p wb_t wb_r (mkPoint 1 (-1)).
Proof.
  unfold on_round_cap, dist_sq, wb_p, wb_t, wb_r; simpl.
  repeat split; lra.
Qed.

(* The apex (terminal advanced by r along t) is ON the cap, with SIGNED
   forward coordinate exactly +r -- the sign-sensitive pin (65-a lesson). *)
Lemma wb_apex_on_cap_signed :
  on_round_cap wb_p wb_t wb_r (mkPoint 2 0) /\
  (px (mkPoint 2 0) - px wb_p) * px wb_t
  + (py (mkPoint 2 0) - py wb_p) * py wb_t = wb_r.
Proof.
  unfold on_round_cap, dist_sq, wb_p, wb_t, wb_r; simpl.
  repeat split; lra.
Qed.

(* MISMATCH PROBE 1: the back point (0,0) is at distance r but BEHIND the
   diameter (forward dot = -1 < 0) -- refutes "cap = the whole circle". *)
Lemma wb_back_point_off_cap :
  dist_sq (mkPoint 0 0) wb_p = wb_r * wb_r /\
  ~ on_round_cap wb_p wb_t wb_r (mkPoint 0 0).
Proof.
  unfold on_round_cap, dist_sq, wb_p, wb_t, wb_r; simpl.
  split; [ lra | intros [_ Hfwd]; lra ].
Qed.

(* MISMATCH PROBE 2: the centre p itself is forward but NOT at distance r --
   refutes "cap = the forward half-disk". *)
Lemma wb_centre_off_cap :
  0 <= (px wb_p - px wb_p) * px wb_t + (py wb_p - py wb_p) * py wb_t /\
  ~ on_round_cap wb_p wb_t wb_r wb_p.
Proof.
  unfold on_round_cap, dist_sq, wb_p, wb_t, wb_r; simpl.
  split; [ lra | intros [Hd _]; lra ].
Qed.

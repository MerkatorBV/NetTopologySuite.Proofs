(* ============================================================================
   nts-eval micro unit — claimId 65-c (RED)
   Red planted 2026-08-02 · Green pending
   ----------------------------------------------------------------------------
   SQUARE endcap geometry completes the ENDCAP TRIO (JTS
   BufferParameters.CAP_FLAT / CAP_ROUND / CAP_SQUARE; 65-a flat = the
   diameter segment, 65-b round = the forward semicircle, both merged):
   the square cap is the U-SHAPED BOUNDARY of the square erected forward
   on the flat diameter — three segments walked
       cap_minus -> corner_minus -> corner_plus -> cap_plus,
   i.e. exactly the frame image of the unit square's boundary minus its
   open bottom side:
       q = p + r*(a*J(t) + b*t)   with
       (a = -1 /\ 0 <= b <= 1)  \/  (b = 1 /\ -1 <= a <= 1)  \/
       (a =  1 /\ 0 <= b <= 1).
   All LINEAR — unlike 65-b there is no circle: the whole claim is
   segment-parametrisation algebra over the same J(t)-frame the trio
   shares.

   RED SURFACE.  The headline biconditional is STATED below
   (`square_endcap_is_diameter_square_claim`) and deliberately NOT
   proved in this unit — no `Admitted`, no `Axiom`; the claim is a named
   `Definition ... : Prop`, so the Eval -> Qed matcher reports 65-c red.
   Green target:
     Lemma square_endcap_is_diameter_square :
       square_endcap_is_diameter_square_claim.
   with the production home in the BufferEndcap.v neighbourhood
   (suggested file: theories/BufferEndcapSquare.v) over the corpus's
   `cap_endpoint` / `sq_corner` / `unit_dir` / `unit_perp` vocabulary,
   same WITNESS tag.  The proof machinery is the 65-a frame
   decomposition per side: each of the three segments pins one frame
   coordinate (a = -1, b = 1, a = 1) and lets the between-parameter s
   sweep the other — three linear equivalences, no sqrt, no nra beyond
   products with s.

   What IS Qed here: rational witness pins fixing the intended
   semantics — terminal p = (1,0), tangent t = (1,0), r = 1
   (J(t) = (0,1); cap endpoints (1,-1)/(1,1); corners (2,-1)/(2,1)):
     - both corners are ON the cap (side seam points, frame (+-1, 1))
       and sit at dist_sq 2 from p — echoing the corpus's
       square_cap_corner_dist_sq = 2*d^2;
     - the forward-face midpoint (2,0) is ON the cap (frame (0,1)) —
       the square cap's face passes through the ROUND cap's apex: the
       trio's cross-cap seam pin;
     - the terminal p itself is OFF all three sides: kills the
       filled-square reading AND witnesses that the bottom (diameter)
       side is open — the diameter belongs to the FLAT cap (65-a), not
       to the square cap's walk;
     - the corner's SIGNED frame coordinates are exactly (+1, +1)*r
       (sign-sensitive per the 65-a mutation lesson).

   WITNESS claimId: 65-c
   topic: buffer
   Lemma (Green target): square_endcap_is_diameter_square
   ========================================================================== *)

(* WITNESS {"claimId":"65-c","topic":"buffer","lemma":"square_endcap_is_diameter_square","title":"Square endcap = U-boundary of the forward square on the flat diameter"} *)

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

(* The trio's shared frame: J = pi/2 rotation of the unit tangent,
   J(tx,ty) = (-ty,tx).  Cap endpoints p +- r*J(t); corners pushed r
   further along t (the corpus's sq_corner construction). *)
Definition cap_plus (p t : Point) (r : R) : Point :=
  mkPoint (px p - r * py t) (py p + r * px t).
Definition cap_minus (p t : Point) (r : R) : Point :=
  mkPoint (px p + r * py t) (py p - r * px t).
Definition corner_plus (p t : Point) (r : R) : Point :=
  mkPoint (px p - r * py t + r * px t) (py p + r * px t + r * py t).
Definition corner_minus (p t : Point) (r : R) : Point :=
  mkPoint (px p + r * py t + r * px t) (py p - r * px t + r * py t).

(* The square-cap carrier: the U-shaped three-segment walk. *)
Definition on_square_cap (p t : Point) (r : R) (q : Point) : Prop :=
  between (cap_minus p t r) (corner_minus p t r) q \/
  between (corner_minus p t r) (corner_plus p t r) q \/
  between (corner_plus p t r) (cap_plus p t r) q.

(* -------------------------------------------------------------------------- *)
(* The 65-c claim (RED: stated, not closed).                                  *)
(* The carrier is exactly the frame image of the unit square's boundary       *)
(* minus its open bottom side.                                                *)
(* -------------------------------------------------------------------------- *)

Definition square_endcap_is_diameter_square_claim : Prop :=
  forall (p t : Point) (r : R),
    0 < r ->
    px t * px t + py t * py t = 1 ->
    forall q : Point,
      on_square_cap p t r q <->
      (exists a b : R,
          ((a = -1 /\ 0 <= b <= 1) \/
           (b = 1 /\ -1 <= a <= 1) \/
           (a = 1 /\ 0 <= b <= 1)) /\
          px q = px p + r * (a * (- py t) + b * px t) /\
          py q = py p + r * (a * px t + b * py t)).

(* RED: no proof of the claim in this unit or in production.  Green must Qed
   `square_endcap_is_diameter_square` with this statement (micro-kernel)
   and its production mirror over cap_endpoint/sq_corner/unit_dir/unit_perp. *)

(* -------------------------------------------------------------------------- *)
(* Rational witness pins (Qed at Red).                                        *)
(* Terminal p = (1,0), tangent t = (1,0), r = 1.                              *)
(* -------------------------------------------------------------------------- *)

Definition wc_p : Point := mkPoint 1 0.
Definition wc_t : Point := mkPoint 1 0.
Definition wc_r : R := 1.

Lemma wc_tangent_unit : px wc_t * px wc_t + py wc_t * py wc_t = 1.
Proof. unfold wc_t; simpl. lra. Qed.

(* Both corners are ON the cap (each is the seam of a side segment and
   the forward face), at dist_sq exactly 2 from the terminal — the
   corpus's square_cap_corner_dist_sq = 2*d^2 echoed rationally. *)
Lemma wc_corners_on_cap :
  on_square_cap wc_p wc_t wc_r (mkPoint 2 1) /\
  on_square_cap wc_p wc_t wc_r (mkPoint 2 (-1)) /\
  dist_sq (mkPoint 2 1) wc_p = 2 /\
  dist_sq (mkPoint 2 (-1)) wc_p = 2.
Proof.
  repeat split; try (unfold dist_sq, wc_p; simpl; lra).
  - (* (2,1) = corner_plus: end of the forward face *)
    right. left. exists 1.
    unfold corner_minus, corner_plus, wc_p, wc_t, wc_r; simpl.
    repeat split; lra.
  - (* (2,-1) = corner_minus: end of the minus side *)
    left. exists 1.
    unfold cap_minus, corner_minus, wc_p, wc_t, wc_r; simpl.
    repeat split; lra.
Qed.

(* The forward-face midpoint (2,0) is ON the cap — and it is exactly the
   ROUND cap's apex point (65-b's round_apex at the same fixture): the
   cross-cap seam of the trio. *)
Lemma wc_face_midpoint_on_cap :
  on_square_cap wc_p wc_t wc_r (mkPoint 2 0).
Proof.
  right. left. exists (1 / 2).
  unfold corner_minus, corner_plus, wc_p, wc_t, wc_r; simpl.
  repeat split; lra.
Qed.

(* MISMATCH PROBE: the terminal p is OFF all three sides — kills the
   filled-square reading, and witnesses that the bottom (diameter) side
   is OPEN: the diameter belongs to the flat cap (65-a), not to the
   square cap's walk. *)
Lemma wc_terminal_off_cap :
  ~ on_square_cap wc_p wc_t wc_r wc_p.
Proof.
  intros [H | [H | H]]; destruct H as [s [H0 [H1 [Hx Hy]]]];
    unfold cap_minus, cap_plus, corner_minus, corner_plus,
           wc_p, wc_t, wc_r in *; simpl in *; lra.
Qed.

(* SIGNED pin (the 65-a mutation lesson): corner_plus's frame coordinates
   are exactly (+1, +1) scaled by r — cross coordinate along J(t) AND
   forward coordinate along t both equal +r, for the concrete fixture. *)
Lemma wc_corner_signed_frame :
  (px (mkPoint 2 1) - px wc_p) * (- py wc_t) +
  (py (mkPoint 2 1) - py wc_p) * px wc_t = wc_r /\
  (px (mkPoint 2 1) - px wc_p) * px wc_t +
  (py (mkPoint 2 1) - py wc_p) * py wc_t = wc_r.
Proof.
  unfold wc_p, wc_t, wc_r; simpl. split; lra.
Qed.

(* ============================================================================
   NetTopologySuite.Proofs.ZetaHostHit
   ----------------------------------------------------------------------------
   #770 decision experiment, step 3: P, then the fixtures.

   P  (host_circ_chord_hit_ok).  A ζ that the C1 kernel accepts as a
   segment hit carries the host check: on_circ at t_of_zeta ζ and
   on_chord at tj_of ζ, at the chart point.  Stated over zeta_seg_hit
   (root, chart window, 0 ≤ tj ≤ 1) because classify_zeta (C1.9) is not
   proved.  Under carry-and-check that pair is what I_ok checks; this
   does not change host I_ok, which still declines the mixed pair.

   P uses only C1 (ChartLineQuadratic) and C2 (ZetaEggBridge) lemmas:
   no cos/sin/atan3/atan2/PI lemma and no case split on the sign of Δθ,
   on θ₀ versus π, or on a quadrant.  Its one range hypothesis is
   |Δθ| < 2π, which keeps both arc ends off the pole (F5 is outside it).

   zeta_mid_in_window is generic, not a fixture lemma: the egg's own mid
   (ζ = 0) is always inside the chart window.

   Oracle lane. Not an egg reparameterisation. Does not remint CircGamma,
   leftover Ⅹ, LoopDischarged, I_ok_mixed as host, or MkNurbs.
   No Admitted. No Axiom. No Parameter.
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import
  Distance SheetHenCircEgg SheetHenCookCore CircleChart ChartLineQuadratic
  ZetaEggBridge.
Local Open Scope R_scope.

Section EggChord.
Variables (c : CircularEgg) (s : ChordEgg).

Let O := circ_o c.
Let Q := egg_pole c.
Let S0 := ce_p0 s.
Let dx := px (ce_p1 s) - px (ce_p0 s).
Let dy := py (ce_p1 s) - py (ce_p0 s).

Definition egg_qf (z : R) : R :=
  zeta_qf (px O) (py O) (px Q) (py Q) (px S0) (py S0) dx dy z.
Definition egg_tj (z : R) : R :=
  tj_of (px O) (py O) (px Q) (py Q) (px S0) (py S0) dx dy z.
Definition egg_zA : R := zeta_of_pt O Q (circ_start c).
Definition egg_zB : R := zeta_of_pt O Q (circ_end c).

Definition zeta_seg_hit (z : R) : Prop :=
  egg_qf z = 0 /\ in_zeta_interval egg_zA egg_zB z /\ 0 <= egg_tj z <= 1.

Hypothesis Hr : circ_r c <> 0.
Hypothesis Hs : circ_sweep c <> 0.
Hypothesis Hsw : -(2 * PI) < circ_sweep c < 2 * PI.

Lemma egg_ends_t : t_of_zeta c egg_zA = 0 /\ t_of_zeta c egg_zB = 1.
Proof.
  unfold egg_zA, egg_zB, circ_start, circ_end, O, Q. split.
  - apply t_of_zeta_of_circ_eval; [exact Hr | exact Hs | lra].
  - apply t_of_zeta_of_circ_eval; [exact Hr | exact Hs | lra].
Qed.

Lemma zeta_in_window_iff : forall z,
  in_zeta_interval egg_zA egg_zB z <-> 0 <= t_of_zeta c z <= 1.
Proof.
  intro z. unfold in_zeta_interval.
  rewrite (t_of_zeta_window c z egg_zA egg_zB Hs).
  destruct egg_ends_t as [HA HB]. rewrite HA, HB.
  split; intro H; [split; nra | nra].
Qed.

Lemma zeta_mid_in_window : in_zeta_interval egg_zA egg_zB 0.
Proof.
  apply zeta_in_window_iff. rewrite t_of_zeta_mid. lra.
Qed.

Theorem host_circ_chord_hit_ok : forall z,
  (dx, dy) <> (0, 0) ->
  zeta_seg_hit z ->
  on_circ c (t_of_zeta c z) (zeta_pt O Q z) /\
  on_chord s (egg_tj z) (zeta_pt O Q z).
Proof.
  intros z Hd [Hf [Hw Htj]].
  split.
  - split; [apply zeta_in_window_iff; exact Hw |].
    symmetry. unfold O, Q. apply circ_eval_t_of_zeta. exact Hs.
  - split; [exact Htj |].
    destruct (on_line_param (px O) (py O) (px Q) (py Q) (px S0) (py S0)
                dx dy z Hd Hf) as [Ex Ey].
    unfold zeta_abs_x, zeta_abs_y in Ex, Ey.
    unfold zeta_pt, chord_eval. fold (egg_tj z) in Ex, Ey.
    f_equal.
    + rewrite Ex. unfold S0, dx. ring.
    + rewrite Ey. unfold S0, dy. ring.
Qed.

End EggChord.

Print Assumptions zeta_mid_in_window.
Print Assumptions host_circ_chord_hit_ok.

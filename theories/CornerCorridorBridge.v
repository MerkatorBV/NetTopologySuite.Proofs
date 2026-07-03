(* ==========================================================================
   CornerCorridorBridge.v

   [H-bridge attack, C-3e step 1] The algebraic bridge between the corner
   connector's SHORT-RANGE construction and the corridor's LONG-RANGE
   one: for a non-horizontal dart `d`, the corner samples at its two
   endpoints -- `corner_sample_out (ddir d)` at `dbase d`, `corner_sample_in
   (point_diff (dbase d) (dtip d))` at `dtip d` -- are, for EVERY choice
   of `(rho, delta)`, EXACTLY a point on d's own WEST or EAST corridor
   (`JCTCorridor.corridor` / `MirrorCorridor.corridor_east`), at the
   height the sample's own `(rho, delta)` produces.

   Why this holds and why it picks a definite side: `d`'s carrier line
   through `dbase d` has slope `vx (ddir d) / vy (ddir d)`, so the
   corner sample's `x`-coordinate at its own height differs from the
   carrier's value there by EXACTLY `delta * |ddir d|^2 / vy (ddir d)`
   -- a pure consequence of `{u, perpL u}` being an orthogonal basis
   (no case split needed for the identity itself, only `vy (ddir d) <>
   0`, i.e. `d` non-horizontal).  The SIGN of that quantity is pinned by
   `d`'s own ascending/descending status: `vy (ddir d) < 0` (descending)
   gives a POSITIVE westward offset (matches `corridor`); `vy (ddir d) >
   0` (ascending) gives EXACTLY the corresponding eastward offset
   (matches `corridor_east`) -- the same dichotomy already documented at
   `MirrorCorridor.v`'s header ("right-of-travel is west on a descent
   and east on an ascent"), now verified to be the SAME side at BOTH of
   `d`'s endpoints (it is the same line throughout).  This is what lets
   C-3e's straddle tie-in reuse the corner connector's OWN sample points
   as corridor endpoints, with no separate "meeting hop" needed at the
   algebraic level.

   Pure vector/field algebra; no `Admitted` / `Axiom` / `Parameter`;
   allowlist axioms only.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
   ========================================================================== *)

From Stdlib Require Import Reals Lra List.
From NTS.Proofs Require Import Distance Overlay OverlayGraph Vec Azimuth Direction
                               Dart DartAngularOrder PointInRingTangents
                               JordanCurveSeam JCT JCTHugStep JCTMinOpenStep
                               JCTTautClearance JCTNesting GeneralTautBridge
                               RingClearance SectorPath CornerSamples CornerConnector
                               JCTCorridor StraddleSides MirrorCorridor DartSideKit
                               HandoffWedge WalkCorridor FaceTwinAware HBridgeCoreSlice
                               RingExtract RectangleJCT.

Import ListNotations.
Local Open Scope R_scope.
(* §1  At `dbase d`: `corner_sample_out (ddir d)` sits on d's corridor.        *)
(* -------------------------------------------------------------------------- *)

Lemma corner_sample_out_on_corridor_west :
  forall (d : Dart) (rho delta : R),
    vy (ddir d) < 0 ->
    point_at (dbase d) (corner_sample_out (ddir d) rho delta)
      = corridor d
          (delta * (vx (ddir d) * vx (ddir d) + vy (ddir d) * vy (ddir d))
             / (- vy (ddir d)))
          (py (dbase d) + (rho * vy (ddir d) - delta * vx (ddir d))).
Proof.
  intros [[xa ya] [xb yb]] rho delta Hneg.
  cbv [ddir dbase dtip point_diff point_at corner_sample_out
       vadd vscale vneg vperpL corridor edge_x_at fst snd vx vy px py]
    in *.
  assert (Hnh : yb - ya <> 0) by lra.
  f_equal; [ | ring ].
  field; lra.
Qed.

Lemma corner_sample_out_on_corridor_east :
  forall (d : Dart) (rho delta : R),
    vy (ddir d) > 0 ->
    point_at (dbase d) (corner_sample_out (ddir d) rho delta)
      = corridor_east d
          (delta * (vx (ddir d) * vx (ddir d) + vy (ddir d) * vy (ddir d))
             / vy (ddir d))
          (py (dbase d) + (rho * vy (ddir d) - delta * vx (ddir d))).
Proof.
  intros [[xa ya] [xb yb]] rho delta Hpos.
  cbv [ddir dbase dtip point_diff point_at corner_sample_out
       vadd vscale vneg vperpL corridor_east edge_x_at fst snd vx vy px py]
    in *.
  assert (Hnh : yb - ya <> 0) by lra.
  f_equal; [ | ring ].
  field; lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  At `dtip d`: `corner_sample_in (point_diff (dbase d) (dtip d))` sits    *)
(*     on the SAME corridor, on the SAME side (it is the same line).          *)
(* -------------------------------------------------------------------------- *)

Lemma corner_sample_in_on_corridor_west :
  forall (d : Dart) (rho delta : R),
    vy (ddir d) < 0 ->
    point_at (dtip d) (corner_sample_in (point_diff (dbase d) (dtip d)) rho delta)
      = corridor d
          (delta * (vx (ddir d) * vx (ddir d) + vy (ddir d) * vy (ddir d))
             / (- vy (ddir d)))
          (py (dtip d) + (- rho * vy (ddir d) - delta * vx (ddir d))).
Proof.
  intros [[xa ya] [xb yb]] rho delta Hneg.
  cbv [ddir dbase dtip point_diff point_at corner_sample_in
       vadd vscale vperpL corridor edge_x_at fst snd vx vy px py]
    in *.
  assert (Hnh : ya - yb <> 0) by lra.
  f_equal; [ | ring ].
  field; lra.
Qed.

Lemma corner_sample_in_on_corridor_east :
  forall (d : Dart) (rho delta : R),
    vy (ddir d) > 0 ->
    point_at (dtip d) (corner_sample_in (point_diff (dbase d) (dtip d)) rho delta)
      = corridor_east d
          (delta * (vx (ddir d) * vx (ddir d) + vy (ddir d) * vy (ddir d))
             / vy (ddir d))
          (py (dtip d) + (- rho * vy (ddir d) - delta * vx (ddir d))).
Proof.
  intros [[xa ya] [xb yb]] rho delta Hpos.
  cbv [ddir dbase dtip point_diff point_at corner_sample_in
       vadd vscale vperpL corridor_east edge_x_at fst snd vx vy px py]
    in *.
  assert (Hnh : ya - yb <> 0) by lra.
  f_equal; [ | ring ].
  field; lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Axiom audit.  Pure vector/field algebra; allowlist axioms only.             *)
(* -------------------------------------------------------------------------- *)


(* -------------------------------------------------------------------------- *)
(* §C-3e-A  ef-vs-corridor assumption + corridor_absorbs_ef probe.            *)
(* -------------------------------------------------------------------------- *)

(* C-3e open design note (post-PR#339)
   Both tracks currently connect only d's own two corner samples via corridor.
   Target for face_transport_premise: (edge_x_at d my - ef, my) and +ef.
   Question: corridor.safe_offset guarantees δ < threshold, but ef comes from
   straddle_side_core with no explicit relation yet.
   Proposed closure: prove ∃ ε₀ > 0, ∀ ef < ε₀, corridor argument still holds
   (standard "sufficiently small" + triangle-inequality chaining). *)

(* Uniform corridor clearance from `walk_dart_corridor_clear` / east mirror. *)
Definition corridor_safe_threshold
  (delta0 : R) : R := delta0.

Definition corridor_safe_half (delta0 : R) : R := delta0 / 2.

Lemma corridor_half_pos :
  forall (delta0 : R), 0 < delta0 -> 0 < corridor_safe_half delta0.
Proof.
  intros delta0 Hd0.
  unfold corridor_safe_half, Rdiv.
  field_simplify; lra.
Qed.

Lemma corridor_half_lt_full :
  forall (delta0 : R), 0 < delta0 -> corridor_safe_half delta0 < delta0.
Proof.
  intros delta0 Hd0.
  unfold corridor_safe_half, Rdiv.
  field_simplify; lra.
Qed.

Definition corridor_safe_third (delta0 : R) : R := delta0 / 3.

Lemma corridor_third_pos :
  forall (delta0 : R), 0 < delta0 -> 0 < corridor_safe_third delta0.
Proof.
  intros delta0 Hd0.
  unfold corridor_safe_third, Rdiv.
  field_simplify; lra.
Qed.

Lemma ef_lt_threshold_third_implies_half :
  forall (delta0 ef : R),
    0 < delta0 ->
    0 < ef ->
    ef < corridor_safe_threshold delta0 / 3 ->
    ef < corridor_safe_half delta0.
Proof.
  intros delta0 ef Hd0 Hef Hthird.
  unfold corridor_safe_threshold, corridor_safe_half, corridor_safe_third in *.
  field_simplify in Hthird. lra.
Qed.

(* The straddle offset ef sits below the corridor half-threshold, hence below
   delta0 itself: the same uniform clearance window applies with delta := ef. *)
Lemma corridor_absorbs_ef :
  forall (delta0 ef : R),
    0 < delta0 ->
    0 < ef ->
    ef < corridor_safe_half delta0 ->
    0 < ef /\ ef < delta0.
Proof.
  intros delta0 ef Hd0 Hef Hhalf.
  unfold corridor_safe_half in Hhalf.
  split; [ exact Hef | ].
  apply (Rlt_trans _ _ _ Hhalf).
  exact (corridor_half_lt_full delta0 Hd0).
Qed.

(* Headline-shaped probe: any ef below half of a walk-dart delta0 inherits the
   corridor's ring-freedom at every height in the window. *)
Lemma corridor_ef_inherits_clearance :
  forall (x : Dart) (r : Ring) (delta0 ef y ylo yhi : R),
    0 < delta0 ->
    0 < ef ->
    ef < corridor_safe_half delta0 ->
    ylo <= yhi ->
    (forall delta, 0 < delta < delta0 ->
       forall y', ylo <= y' <= yhi ->
         ~ ring_image r (corridor x delta y')) ->
    ylo <= y <= yhi ->
    ~ ring_image r (corridor x ef y).
Proof.
  intros x r delta0 ef y ylo yhi Hd0 Hef Hhalf Hle Hclear Hy.
  unfold corridor_safe_half in Hhalf.
  destruct (corridor_absorbs_ef delta0 ef Hd0 Hef Hhalf) as [Hefpos Hef_bound].
  exact (Hclear ef (conj Hefpos Hef_bound) y Hy).
Qed.

Lemma corridor_ef_inherits_clearance_east :
  forall (x : Dart) (r : Ring) (delta0 ef y ylo yhi : R),
    0 < delta0 ->
    0 < ef ->
    ef < corridor_safe_half delta0 ->
    ylo <= yhi ->
    (forall delta, 0 < delta < delta0 ->
       forall y', ylo <= y' <= yhi ->
         ~ ring_image r (corridor_east x delta y')) ->
    ylo <= y <= yhi ->
    ~ ring_image r (corridor_east x ef y).
Proof.
  intros x r delta0 ef y ylo yhi Hd0 Hef Hhalf Hle Hclear Hy.
  unfold corridor_safe_half in Hhalf.
  destruct (corridor_absorbs_ef delta0 ef Hd0 Hef Hhalf) as [Hefpos Hef_bound].
  exact (Hclear ef (conj Hefpos Hef_bound) y Hy).
Qed.

(* ∃ ε₀ packaging for the proposed "sufficiently small ef" closure. *)
Lemma corridor_small_ef_exists :
  forall (delta0 : R), 0 < delta0 ->
    exists eps0, eps0 = corridor_safe_half delta0 /\
      0 < eps0 /\
      (forall ef, 0 < ef -> ef < eps0 ->
         ef < corridor_safe_half delta0 /\ ef < delta0).
Proof.
  intros delta0 Hd0.
  exists (corridor_safe_half delta0).
  split; [ reflexivity | ].
  split.
  - exact (corridor_half_pos delta0 Hd0).
  - intros ef Hef Hlt. split.
    + exact Hlt.
    + destruct (corridor_absorbs_ef delta0 ef Hd0 Hef Hlt); lra.
Qed.

(* Straddle west sample = west corridor point at the same offset. *)
Lemma straddle_west_eq_corridor :
  forall (d : Dart) (my ef : R),
    corridor d ef my = mkPoint (edge_x_at d my - ef) my.
Proof.
  intros d my ef. unfold corridor. reflexivity.
Qed.

Lemma straddle_east_eq_corridor_east :
  forall (d : Dart) (my ef : R),
    corridor_east d ef my = mkPoint (edge_x_at d my + ef) my.
Proof.
  intros d my ef. unfold corridor_east. reflexivity.
Qed.

Example corridor_absorbs_ef_numeric : 0 < 1 / 10 /\ 1 / 10 < 1.
Proof.
  assert (Hhalf : 1 / 10 < corridor_safe_half 1)
    by (unfold corridor_safe_half; field_simplify; lra).
  destruct (corridor_absorbs_ef 1 (1 / 10) (ltac:(lra)) (ltac:(lra)) Hhalf) as [Hef Hbound].
  exact (conj Hef Hbound).
Qed.

(* -------------------------------------------------------------------------- *)
(* §C-3e-B  Handoff connector (pruned ball + side kit + wedge).                *)
(* -------------------------------------------------------------------------- *)

Lemma vy_nonzero_of_lt : forall v : Vec, vy v < 0 -> v <> vzero.
Proof.
  intros v Hlt Hzero. inversion Hzero. subst. cbn in Hlt. lra.
Qed.

Lemma vy_nonzero_of_gt : forall v : Vec, vy v > 0 -> v <> vzero.
Proof.
  intros v Hgt Hzero. inversion Hzero. subst. cbn in Hgt. lra.
Qed.

Lemma dart_descend_tip_below_base : forall d : Dart,
  vy (ddir d) < 0 -> py (dtip d) < py (dbase d).
Proof.
  intros [base tip] H.
  unfold ddir, point_diff, dtip, dbase, vy, fst, snd in H.
  cbn in H. unfold dtip, dbase. cbn. lra.
Qed.

Lemma dart_ascend_base_below_tip : forall d : Dart,
  vy (ddir d) > 0 -> py (dbase d) < py (dtip d).
Proof.
  intros [base tip] H.
  unfold ddir, point_diff, dtip, dbase, vy, fst, snd in H.
  cbn in H. unfold dtip, dbase. cbn. lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §1  Re-export the complement mechanism under dart-handoff naming.          *)
(* -------------------------------------------------------------------------- *)

Lemma handoff_offset_in_complement :
  forall (r : Ring) (v a b : Point) (eps : R) (w : Vec),
    (forall q : Point,
       Rabs (px q - px v) < eps -> Rabs (py q - py v) < eps ->
       forall f, In f (ring_edges r) -> f <> (a, v) -> f <> (v, b) ->
         ~ on_edge f q) ->
    in_open_sector (point_diff a v) (point_diff b v) w ->
    Rabs (vx w) < eps -> Rabs (vy w) < eps ->
    ring_complement r (point_at v w).
Proof.
  intros r v a b eps w Hball Hsect Hbx Hby.
  exact (corner_offset_in_complement r v a b eps w Hball Hsect Hbx Hby).
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  Convex-gap handoff: one sector-certified chord.                          *)
(* -------------------------------------------------------------------------- *)

Theorem handoff_chord_connected_convex :
  forall (r : Ring) (v a b : Point) (u1 u2 w1 w2 : Vec) (eps : R),
    u1 = point_diff a v ->
    u2 = point_diff b v ->
    In (a, v) (ring_edges r) ->
    In (v, b) (ring_edges r) ->
    (forall q : Point,
       Rabs (px q - px v) < eps -> Rabs (py q - py v) < eps ->
       forall f, In f (ring_edges r) -> f <> (a, v) -> f <> (v, b) ->
         ~ on_edge f q) ->
    0 < vcross u1 u2 ->
    0 < vcross u1 w1 -> 0 < vcross w1 u2 ->
    0 < vcross u1 w2 -> 0 < vcross w2 u2 ->
    Rabs (vx w1) < eps -> Rabs (vy w1) < eps ->
    Rabs (vx w2) < eps -> Rabs (vy w2) < eps ->
    connected_in_complement_cont r (point_at v w1) (point_at v w2).
Proof.
  intros r v a b u1 u2 w1 w2 eps Hu1 Hu2 Hin Hout Hball Hc H11 H12 H21 H22
         H1x H1y H2x H2y.
  apply hop_connected. intros t Ht.
  apply (handoff_offset_in_complement r v a b eps); [ exact Hball | | | ].
  - pose proof (sector_path_convex u1 u2 w1 w2 Hc H11 H12 H21 H22 t Ht)
      as Hsect.
    rewrite Hu1, Hu2 in Hsect. exact Hsect.
  - eapply Rle_lt_trans; [ apply vaffine_bound_x; exact Ht | ].
    apply Rmax_lub_lt; assumption.
  - eapply Rle_lt_trans; [ apply vaffine_bound_y; exact Ht | ].
    apply Rmax_lub_lt; assumption.
Qed.

(* DESCENDING dart, west corridor, BASE vertex: corner sample to corridor end
   at height `y` inside the y-span. *)
Theorem handoff_base_to_corridor_west_convex :
  forall (r : Ring) (d : Dart) (a : Point) (eps rho delta y : R),
    In (a, dbase d) (ring_edges r) ->
    In d (ring_edges r) ->
    (forall q : Point,
       Rabs (px q - px (dbase d)) < eps ->
       Rabs (py q - py (dbase d)) < eps ->
       forall f, In f (ring_edges r) -> f <> (a, dbase d) -> f <> d ->
         ~ on_edge f q) ->
    vy (ddir d) < 0 ->
    0 < vcross (point_diff a (dbase d)) (ddir d) ->
    0 < rho -> 0 < delta ->
    delta * Rabs (vcross (vperpL (point_diff a (dbase d))) (ddir d))
      < rho * vcross (point_diff a (dbase d)) (ddir d) ->
    delta * Rabs (vcross (point_diff a (dbase d)) (vperpL (ddir d)))
      < rho * vcross (point_diff a (dbase d)) (ddir d) ->
    rho * Rabs (vx (ddir d)) + delta * Rabs (vy (ddir d)) < eps ->
    rho * Rabs (vy (ddir d)) + delta * Rabs (vx (ddir d)) < eps ->
    Rabs (vx (point_diff (corridor d delta y) (dbase d))) < eps ->
    Rabs (vy (point_diff (corridor d delta y) (dbase d))) < eps ->
    0 < vcross (point_diff a (dbase d))
               (point_diff (corridor d delta y) (dbase d)) ->
    connected_in_complement_cont r
      (point_at (dbase d) (corner_sample_out (ddir d) rho delta))
      (corridor d delta y).
Proof.
  intros r d a eps rho delta y Hin Hout Hball Hdesc Hc Hr Hd Hsmall1 Hsmall2
         Hb_out_x Hb_out_y Hcor_x Hcor_y Hcor_far.
  set (u1 := point_diff a (dbase d)).
  set (u2 := ddir d).
  set (w1 := corner_sample_out u2 rho delta).
  set (w2 := point_diff (corridor d delta y) (dbase d)).
  assert (Hu2eq : u2 = point_diff (dtip d) (dbase d)) by (unfold u2; reflexivity).
  assert (Hu2nz : u2 <> vzero) by (unfold u2; exact (vy_nonzero_of_lt _ Hdesc)).
  assert (Hwest : py (dtip d) < py (dbase d))
    by (apply dart_descend_tip_below_base; exact Hdesc).
  assert (H11 : 0 < vcross u1 w1).
  { apply corner_sample_out_cert_far; [ | exact Hr | lra | ].
    - unfold u1, u2. exact Hc.
    - unfold u1, u2. exact Hsmall2. }
  assert (H12 : 0 < vcross w1 u2)
    by (apply corner_sample_out_cert; [ exact Hu2nz | exact Hd ]).
  assert (H22 : 0 < vcross w2 u2)
    by (apply corridor_end_cert_base_west; [ exact Hwest | exact Hd ]).
  pose proof (corner_sample_out_bound u2 rho delta ltac:(lra) ltac:(lra))
    as [HoutBx HoutBy].
  assert (Hdart : d = (dbase d, dtip d)).
  { destruct d as [base tip]. unfold dbase, dtip. cbn. reflexivity. }
  assert (Hout' : In (dbase d, dtip d) (ring_edges r))
    by (rewrite <- Hdart; exact Hout).
  assert (Hball' :
    forall q : Point,
      Rabs (px q - px (dbase d)) < eps ->
      Rabs (py q - py (dbase d)) < eps ->
      forall f, In f (ring_edges r) -> f <> (a, dbase d) ->
        f <> (dbase d, dtip d) -> ~ on_edge f q).
  { intros q Hqx Hqy f Hf Hne1 Hne2.
    apply (Hball q Hqx Hqy f Hf Hne1). intro Heq. apply Hne2.
    rewrite <- Hdart. exact Heq. }
  assert (Hw2 : point_at (dbase d) w2 = corridor d delta y)
    by (unfold w2; rewrite point_at_diff; reflexivity).
  rewrite <- Hw2.
  apply (handoff_chord_connected_convex r (dbase d) a (dtip d) u1 u2 w1 w2 eps);
    [ reflexivity | exact Hu2eq | exact Hin | exact Hout' | exact Hball' | exact Hc
    | exact H11 | exact H12 | exact Hcor_far | exact H22
    | eapply Rle_lt_trans; [ exact HoutBx | exact Hb_out_x ]
    | eapply Rle_lt_trans; [ exact HoutBy | exact Hb_out_y ]
    | exact Hcor_x | exact Hcor_y ].
Qed.

(* ASCENDING dart, east corridor, TIP vertex: arriving sample to corridor end. *)
Theorem handoff_tip_to_corridor_east_convex :
  forall (r : Ring) (d : Dart) (b : Point) (eps rho delta y : R),
    In d (ring_edges r) ->
    In (dtip d, b) (ring_edges r) ->
    (forall q : Point,
       Rabs (px q - px (dtip d)) < eps ->
       Rabs (py q - py (dtip d)) < eps ->
       forall f, In f (ring_edges r) -> f <> d -> f <> (dtip d, b) ->
         ~ on_edge f q) ->
    vy (ddir d) > 0 ->
    0 < vcross (ddir (twin d)) (point_diff b (dtip d)) ->
    0 < rho -> 0 < delta ->
    delta * Rabs (vcross (vperpL (ddir (twin d))) (point_diff b (dtip d)))
      < rho * vcross (ddir (twin d)) (point_diff b (dtip d)) ->
    delta * Rabs (vcross (ddir (twin d)) (vperpL (point_diff b (dtip d))))
      < rho * vcross (ddir (twin d)) (point_diff b (dtip d)) ->
    rho * Rabs (vx (ddir (twin d))) + delta * Rabs (vy (ddir (twin d))) < eps ->
    rho * Rabs (vy (ddir (twin d))) + delta * Rabs (vx (ddir (twin d))) < eps ->
    Rabs (vx (point_diff (corridor_east d delta y) (dtip d))) < eps ->
    Rabs (vy (point_diff (corridor_east d delta y) (dtip d))) < eps ->
    0 < vcross (ddir (twin d))
               (point_diff (corridor_east d delta y) (dtip d)) ->
    0 < vcross (point_diff (corridor_east d delta y) (dtip d))
               (point_diff b (dtip d)) ->
    connected_in_complement_cont r
      (point_at (dtip d) (corner_sample_in (ddir (twin d)) rho delta))
      (corridor_east d delta y).
Proof.
  intros r d b eps rho delta y Hin Hout Hball Hasc Hc Hr Hd Hsmall1 Hsmall2
         Hb_in_x Hb_in_y Hcor_x Hcor_y Hcor_far Hcor_wall2.
  set (u1 := ddir (twin d)).
  set (u2 := point_diff b (dtip d)).
  set (w1 := corner_sample_in u1 rho delta).
  set (w2 := point_diff (corridor_east d delta y) (dtip d)).
  assert (Hu1eq : u1 = point_diff (dbase d) (dtip d)).
  { destruct d as [base tip].
    unfold u1, point_diff, ddir, twin, dtip, dbase, vneg, vx, vy. cbn.
    reflexivity. }
  assert (Hu1neg : vy u1 < 0).
  { destruct d as [base tip]. unfold u1, ddir, twin, vneg, vy in *. cbn in *. lra. }
  assert (Hu1nz : u1 <> vzero) by (exact (vy_nonzero_of_lt _ Hu1neg)).
  assert (Hasc' : py (dbase d) < py (dtip d))
    by (apply dart_ascend_base_below_tip; exact Hasc).
  assert (H11 : 0 < vcross u1 w1)
    by (apply corner_sample_in_cert; [ exact Hu1nz | exact Hd ]).
  assert (H12 : 0 < vcross w1 u2).
  { apply corner_sample_in_cert_far; [ | exact Hr | lra | ].
    - unfold u1, u2. exact Hc.
    - unfold u1, u2. exact Hsmall1. }
  assert (H21 : 0 < vcross u1 w2) by (unfold u1, w2; exact Hcor_far).
  assert (H22 : 0 < vcross w2 u2) by (unfold u2, w2; exact Hcor_wall2).
  pose proof (corner_sample_in_bound u1 rho delta ltac:(lra) ltac:(lra))
    as [HinBx HinBy].
  assert (Hdart : d = (dbase d, dtip d)).
  { destruct d as [base tip]. unfold dbase, dtip. cbn. reflexivity. }
  assert (Hin' : In (dbase d, dtip d) (ring_edges r))
    by (rewrite <- Hdart; exact Hin).
  assert (Hball' :
    forall q : Point,
      Rabs (px q - px (dtip d)) < eps ->
      Rabs (py q - py (dtip d)) < eps ->
      forall f, In f (ring_edges r) -> f <> (dbase d, dtip d) ->
        f <> (dtip d, b) -> ~ on_edge f q).
  { intros q Hqx Hqy f Hf Hne1 Hne2.
    apply (Hball q Hqx Hqy f Hf).
    - intro Hfd. apply Hne1. rewrite <- Hdart. exact Hfd.
    - exact Hne2. }
  assert (Hw2 : point_at (dtip d) w2 = corridor_east d delta y)
    by (unfold w2; rewrite point_at_diff; reflexivity).
  rewrite <- Hw2.
  apply (handoff_chord_connected_convex r (dtip d) (dbase d) b u1 u2 w1 w2 eps);
    [ exact Hu1eq | reflexivity | exact Hin' | exact Hout | exact Hball' | exact Hc
    | exact H11 | exact H12 | exact H21 | exact H22
    | eapply Rle_lt_trans; [ exact HinBx | exact Hb_in_x ]
    | eapply Rle_lt_trans; [ exact HinBy | exact Hb_in_y ]
    | exact Hcor_x | exact Hcor_y ].
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Algebraic bypass: corner sample = corridor point (zero-hop handoff).    *)
(* -------------------------------------------------------------------------- *)

Lemma handoff_base_bridge_west :
  forall (d : Dart) (rho delta : R),
    vy (ddir d) < 0 ->
    point_at (dbase d) (corner_sample_out (ddir d) rho delta)
      = corridor d
          (delta * (vx (ddir d) * vx (ddir d) + vy (ddir d) * vy (ddir d))
             / (- vy (ddir d)))
          (py (dbase d) + (rho * vy (ddir d) - delta * vx (ddir d))).
Proof.
  intros d rho delta Hdesc.
  exact (corner_sample_out_on_corridor_west d rho delta Hdesc).
Qed.

Lemma handoff_tip_bridge_west :
  forall (d : Dart) (rho delta : R),
    vy (ddir d) < 0 ->
    point_at (dtip d)
      (corner_sample_in (point_diff (dbase d) (dtip d)) rho delta)
      = corridor d
          (delta * (vx (ddir d) * vx (ddir d) + vy (ddir d) * vy (ddir d))
             / (- vy (ddir d)))
          (py (dtip d) + (- rho * vy (ddir d) - delta * vx (ddir d))).
Proof.
  intros d rho delta Hdesc.
  exact (corner_sample_in_on_corridor_west d rho delta Hdesc).
Qed.

Lemma handoff_base_bridge_east :
  forall (d : Dart) (rho delta : R),
    vy (ddir d) > 0 ->
    point_at (dbase d) (corner_sample_out (ddir d) rho delta)
      = corridor_east d
          (delta * (vx (ddir d) * vx (ddir d) + vy (ddir d) * vy (ddir d))
             / vy (ddir d))
          (py (dbase d) + (rho * vy (ddir d) - delta * vx (ddir d))).
Proof.
  intros d rho delta Hasc.
  exact (corner_sample_out_on_corridor_east d rho delta Hasc).
Qed.

Lemma handoff_tip_bridge_east :
  forall (d : Dart) (rho delta : R),
    vy (ddir d) > 0 ->
    point_at (dtip d)
      (corner_sample_in (point_diff (dbase d) (dtip d)) rho delta)
      = corridor_east d
          (delta * (vx (ddir d) * vx (ddir d) + vy (ddir d) * vy (ddir d))
             / vy (ddir d))
          (py (dtip d) + (- rho * vy (ddir d) - delta * vx (ddir d))).
Proof.
  intros d rho delta Hasc.
  exact (corner_sample_in_on_corridor_east d rho delta Hasc).
Qed.

Theorem handoff_base_bridge_connected_west :
  forall (r : Ring) (d : Dart) (rho delta : R),
    vy (ddir d) < 0 ->
    ring_complement r
      (corridor d
         (delta * (vx (ddir d) * vx (ddir d) + vy (ddir d) * vy (ddir d))
            / (- vy (ddir d)))
         (py (dbase d) + (rho * vy (ddir d) - delta * vx (ddir d)))) ->
    connected_in_complement_cont r
      (point_at (dbase d) (corner_sample_out (ddir d) rho delta))
      (corridor d
         (delta * (vx (ddir d) * vx (ddir d) + vy (ddir d) * vy (ddir d))
            / (- vy (ddir d)))
         (py (dbase d) + (rho * vy (ddir d) - delta * vx (ddir d)))).
Proof.
  intros r d rho delta Hdesc Hcomp.
  pose proof (handoff_base_bridge_west d rho delta Hdesc) as Heq.
  rewrite Heq.
  apply connected_in_complement_cont_refl. exact Hcomp.
Qed.

(* -------------------------------------------------------------------------- *)
(* §C-3e-C  Along-dart headline -> straddle (edge_x_at d my ± ef, my).        *)
(* -------------------------------------------------------------------------- *)

(* Bridge delta: the corridor offset produced by corner parameters. *)
Definition bridge_delta_west (d : Dart) (delta_c : R) : R :=
  delta_c * (vx (ddir d) * vx (ddir d) + vy (ddir d) * vy (ddir d))
    / (- vy (ddir d)).

Definition bridge_delta_east (d : Dart) (delta_c : R) : R :=
  delta_c * (vx (ddir d) * vx (ddir d) + vy (ddir d) * vy (ddir d))
    / vy (ddir d).

Definition bridge_height_base (d : Dart) (rho delta_c : R) : R :=
  py (dbase d) + (rho * vy (ddir d) - delta_c * vx (ddir d)).

Definition bridge_height_tip (d : Dart) (rho delta_c : R) : R :=
  py (dtip d) + (- rho * vy (ddir d) - delta_c * vx (ddir d)).

(* Corner delta that makes the bridge delta equal a target corridor offset `ef`. *)
Definition corner_delta_for_ef_west (d : Dart) (ef : R) : R :=
  ef * (- vy (ddir d))
    / (vx (ddir d) * vx (ddir d) + vy (ddir d) * vy (ddir d)).

Definition corner_delta_for_ef_east (d : Dart) (ef : R) : R :=
  ef * vy (ddir d)
    / (vx (ddir d) * vx (ddir d) + vy (ddir d) * vy (ddir d)).

Lemma ddir_sq_nez_of_vy_nez :
  forall (d : Dart), vy (ddir d) <> 0 ->
    vx (ddir d) * vx (ddir d) + vy (ddir d) * vy (ddir d) <> 0.
Proof.
  intros d Hvy H0.
  apply Rplus_sqr_eq_0 in H0. destruct H0 as [_ Hvy0]. exact (Hvy Hvy0).
Qed.

Lemma bridge_delta_west_for_ef :
  forall (d : Dart) (ef : R), vy (ddir d) < 0 ->
    bridge_delta_west d (corner_delta_for_ef_west d ef) = ef.
Proof.
  intros d ef Hdesc.
  unfold bridge_delta_west, corner_delta_for_ef_west.
  assert (Hvy : vy (ddir d) <> 0)
    by (intro Hz; rewrite Hz in Hdesc; cbn in Hdesc; lra).
  assert (Hden := ddir_sq_nez_of_vy_nez d Hvy).
  field.
  - split; [ exact Hden | exact Hvy ].
Qed.

Lemma bridge_delta_east_for_ef :
  forall (d : Dart) (ef : R), vy (ddir d) > 0 ->
    bridge_delta_east d (corner_delta_for_ef_east d ef) = ef.
Proof.
  intros d ef Hasc.
  unfold bridge_delta_east, corner_delta_for_ef_east.
  assert (Hvy : vy (ddir d) <> 0)
    by (intro Hz; rewrite Hz in Hasc; cbn in Hasc; lra).
  assert (Hden := ddir_sq_nez_of_vy_nez d Hvy).
  field.
  - split; [ exact Hden | exact Hvy ].
Qed.

(* -------------------------------------------------------------------------- *)
(* §1  DESCENDING / west: base sample -> straddle west at `my`.                *)
(* -------------------------------------------------------------------------- *)

Theorem along_dart_base_to_straddle_west :
  forall (r : Ring) (d : Dart) (rho ef my h_base : R),
    vy (ddir d) < 0 ->
    h_base = bridge_height_base d rho (corner_delta_for_ef_west d ef) ->
    h_base <= my ->
    (forall y, h_base <= y <= my ->
       ~ ring_image r (corridor d ef y)) ->
    connected_in_complement_cont r
      (point_at (dbase d)
         (corner_sample_out (ddir d) rho (corner_delta_for_ef_west d ef)))
      (mkPoint (edge_x_at d my - ef) my).
Proof.
  intros r d rho ef my h_base Hdesc Hhbase Hle Hclear.
  set (delta_c := corner_delta_for_ef_west d ef).
  assert (Hbase_eq :
    point_at (dbase d) (corner_sample_out (ddir d) rho delta_c)
      = corridor d ef h_base).
  { rewrite (handoff_base_bridge_west d rho delta_c Hdesc).
    change (delta_c * (vx (ddir d) * vx (ddir d) + vy (ddir d) * vy (ddir d))
              / (- vy (ddir d))) with (bridge_delta_west d delta_c).
    change (py (dbase d) + (rho * vy (ddir d) - delta_c * vx (ddir d)))
      with (bridge_height_base d rho delta_c).
    assert (Hbd : bridge_delta_west d delta_c = ef)
      by (unfold delta_c; exact (bridge_delta_west_for_ef d ef Hdesc)).
    assert (Hbh : bridge_height_base d rho delta_c = h_base)
      by (unfold delta_c; symmetry; exact Hhbase).
    rewrite Hbd, Hbh. reflexivity. }
  assert (Hride : connected_in_complement_cont r (corridor d ef h_base)
                    (corridor d ef my)).
  { assert (Hnh : py (dbase d) <> py (dtip d)).
    { intro Heq. pose proof (dart_descend_tip_below_base d Hdesc) as Hwest.
      rewrite Heq in Hwest. lra. }
    apply connected_in_complement_cont_sym.
    exact (corridor_connected r d h_base my ef Hnh Hle Hclear). }
  rewrite Hbase_eq, <- straddle_west_eq_corridor.
  exact Hride.
Qed.

(* DESCENDING / west: tip sample -> straddle west at `my`. *)
Theorem along_dart_tip_to_straddle_west :
  forall (r : Ring) (d : Dart) (rho ef my h_tip : R),
    vy (ddir d) < 0 ->
    my <= h_tip ->
    h_tip = bridge_height_tip d rho (corner_delta_for_ef_west d ef) ->
    (forall y, my <= y <= h_tip ->
       ~ ring_image r (corridor d ef y)) ->
    connected_in_complement_cont r
      (point_at (dtip d)
         (corner_sample_in (point_diff (dbase d) (dtip d)) rho
            (corner_delta_for_ef_west d ef)))
      (mkPoint (edge_x_at d my - ef) my).
Proof.
  intros r d rho ef my h_tip Hdesc Hle Hhtip Hclear.
  set (delta_c := corner_delta_for_ef_west d ef).
  assert (Htip_eq :
    point_at (dtip d)
      (corner_sample_in (point_diff (dbase d) (dtip d)) rho delta_c)
      = corridor d ef h_tip).
  { rewrite (handoff_tip_bridge_west d rho delta_c Hdesc).
    change (delta_c * (vx (ddir d) * vx (ddir d) + vy (ddir d) * vy (ddir d))
              / (- vy (ddir d))) with (bridge_delta_west d delta_c).
    change (py (dtip d) + (- rho * vy (ddir d) - delta_c * vx (ddir d)))
      with (bridge_height_tip d rho delta_c).
    assert (Hbd : bridge_delta_west d delta_c = ef)
      by (unfold delta_c; exact (bridge_delta_west_for_ef d ef Hdesc)).
    assert (Hth : bridge_height_tip d rho delta_c = h_tip)
      by (unfold delta_c; symmetry; exact Hhtip).
    rewrite Hbd, Hth. reflexivity. }
  assert (Hride : connected_in_complement_cont r (corridor d ef my)
                    (corridor d ef h_tip)).
  { assert (Hnh : py (dbase d) <> py (dtip d)).
    { intro Heq. pose proof (dart_descend_tip_below_base d Hdesc) as Hwest.
      rewrite Heq in Hwest. lra. }
    apply connected_in_complement_cont_sym.
    exact (corridor_connected r d my h_tip ef Hnh Hle Hclear). }
  apply connected_in_complement_cont_sym in Hride.
  rewrite <- Htip_eq in Hride.
  rewrite straddle_west_eq_corridor in Hride.
  exact Hride.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  ASCENDING / east mirror.                                                *)
(* -------------------------------------------------------------------------- *)

Theorem along_dart_base_to_straddle_east :
  forall (r : Ring) (d : Dart) (rho ef my h_base : R),
    vy (ddir d) > 0 ->
    h_base = bridge_height_base d rho (corner_delta_for_ef_east d ef) ->
    h_base <= my ->
    (forall y, h_base <= y <= my ->
       ~ ring_image r (corridor_east d ef y)) ->
    connected_in_complement_cont r
      (point_at (dbase d)
         (corner_sample_out (ddir d) rho (corner_delta_for_ef_east d ef)))
      (mkPoint (edge_x_at d my + ef) my).
Proof.
  intros r d rho ef my h_base Hasc Hhbase Hle Hclear.
  set (delta_c := corner_delta_for_ef_east d ef).
  assert (Hbase_eq :
    point_at (dbase d) (corner_sample_out (ddir d) rho delta_c)
      = corridor_east d ef h_base).
  { rewrite (handoff_base_bridge_east d rho delta_c Hasc).
    change (delta_c * (vx (ddir d) * vx (ddir d) + vy (ddir d) * vy (ddir d))
              / vy (ddir d)) with (bridge_delta_east d delta_c).
    change (py (dbase d) + (rho * vy (ddir d) - delta_c * vx (ddir d)))
      with (bridge_height_base d rho delta_c).
    assert (Hbd : bridge_delta_east d delta_c = ef)
      by (unfold delta_c; exact (bridge_delta_east_for_ef d ef Hasc)).
    assert (Hbh : bridge_height_base d rho delta_c = h_base)
      by (unfold delta_c; symmetry; exact Hhbase).
    rewrite Hbd, Hbh. reflexivity. }
  assert (Hride : connected_in_complement_cont r (corridor_east d ef h_base)
                    (corridor_east d ef my)).
  { assert (Hnh : py (dbase d) <> py (dtip d)).
    { intro Heq. pose proof (dart_ascend_base_below_tip d Hasc) as Hasc'.
      rewrite Heq in Hasc'. lra. }
    apply connected_in_complement_cont_sym.
    exact (corridor_connected_east r d h_base my ef Hnh Hle Hclear). }
  rewrite Hbase_eq, <- straddle_east_eq_corridor_east.
  exact Hride.
Qed.

Theorem along_dart_tip_to_straddle_east :
  forall (r : Ring) (d : Dart) (rho ef my h_tip : R),
    vy (ddir d) > 0 ->
    my <= h_tip ->
    h_tip = bridge_height_tip d rho (corner_delta_for_ef_east d ef) ->
    (forall y, my <= y <= h_tip ->
       ~ ring_image r (corridor_east d ef y)) ->
    connected_in_complement_cont r
      (point_at (dtip d)
         (corner_sample_in (point_diff (dbase d) (dtip d)) rho
            (corner_delta_for_ef_east d ef)))
      (mkPoint (edge_x_at d my + ef) my).
Proof.
  intros r d rho ef my h_tip Hasc Hle Hhtip Hclear.
  set (delta_c := corner_delta_for_ef_east d ef).
  assert (Htip_eq :
    point_at (dtip d)
      (corner_sample_in (point_diff (dbase d) (dtip d)) rho delta_c)
      = corridor_east d ef h_tip).
  { rewrite (handoff_tip_bridge_east d rho delta_c Hasc).
    change (delta_c * (vx (ddir d) * vx (ddir d) + vy (ddir d) * vy (ddir d))
              / vy (ddir d)) with (bridge_delta_east d delta_c).
    change (py (dtip d) + (- rho * vy (ddir d) - delta_c * vx (ddir d)))
      with (bridge_height_tip d rho delta_c).
    assert (Hbd : bridge_delta_east d delta_c = ef)
      by (unfold delta_c; exact (bridge_delta_east_for_ef d ef Hasc)).
    assert (Hth : bridge_height_tip d rho delta_c = h_tip)
      by (unfold delta_c; symmetry; exact Hhtip).
    rewrite Hbd, Hth. reflexivity. }
  assert (Hride : connected_in_complement_cont r (corridor_east d ef my)
                    (corridor_east d ef h_tip)).
  { assert (Hnh : py (dbase d) <> py (dtip d)).
    { intro Heq. pose proof (dart_ascend_base_below_tip d Hasc) as Hasc'.
      rewrite Heq in Hasc'. lra. }
    apply connected_in_complement_cont_sym.
    exact (corridor_connected_east r d my h_tip ef Hnh Hle Hclear). }
  apply connected_in_complement_cont_sym in Hride.
  rewrite <- Htip_eq in Hride.
  rewrite straddle_east_eq_corridor_east in Hride.
  exact Hride.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Packaged with walk-dart clearance + ef half-threshold.                  *)
(* -------------------------------------------------------------------------- *)

Theorem along_dart_base_to_straddle_west_clear :
  forall (D : list Dart) (r : Ring) (d : Dart) (rho ef my h_base ylo yhi : R),
    ring_taut r ->
    pairwise_no_proper_cross_twin_aware D ->
    no_foreign_vertex_twin_aware D ->
    In d D ->
    (forall f, In f (ring_edges r) -> In f D) ->
    ((py (fst d) < ylo /\ yhi < py (snd d)) \/
     (py (snd d) < ylo /\ yhi < py (fst d))) ->
    ylo <= yhi ->
    vy (ddir d) < 0 ->
    h_base = bridge_height_base d rho (corner_delta_for_ef_west d ef) ->
    ylo <= h_base <= my /\ my <= yhi ->
    0 < ef ->
    (exists delta0, 0 < delta0 /\
       ef < corridor_safe_half delta0 /\
       forall delta, 0 < delta < delta0 ->
         forall y, ylo <= y <= yhi ->
           ~ ring_image r (corridor d delta y)) ->
    connected_in_complement_cont r
      (point_at (dbase d)
         (corner_sample_out (ddir d) rho (corner_delta_for_ef_west d ef)))
      (mkPoint (edge_x_at d my - ef) my).
Proof.
  intros D r d rho ef my h_base ylo yhi Htaut Hcross Hforeign Hx HringD
         Hspan Hle Hdesc Hhbase [[Hhlo Hhhi] Hmhi] Hef
         [delta0 [Hd0 [Hhalf Hclear]]].
  apply (along_dart_base_to_straddle_west r d rho ef my h_base Hdesc Hhbase).
  - exact Hhhi.
  - intros y Hy.
    apply (corridor_ef_inherits_clearance d r delta0 ef y ylo yhi Hd0 Hef Hhalf Hle).
    + exact Hclear.
    + lra.
Qed.

Theorem along_dart_base_to_straddle_east_clear :
  forall (D : list Dart) (r : Ring) (d : Dart) (rho ef my h_base ylo yhi : R),
    ring_taut r ->
    pairwise_no_proper_cross_twin_aware D ->
    no_foreign_vertex_twin_aware D ->
    In d D ->
    (forall f, In f (ring_edges r) -> In f D) ->
    ((py (fst d) < ylo /\ yhi < py (snd d)) \/
     (py (snd d) < ylo /\ yhi < py (fst d))) ->
    ylo <= yhi ->
    vy (ddir d) > 0 ->
    h_base = bridge_height_base d rho (corner_delta_for_ef_east d ef) ->
    ylo <= h_base <= my /\ my <= yhi ->
    0 < ef ->
    (exists delta0, 0 < delta0 /\
       ef < corridor_safe_half delta0 /\
       forall delta, 0 < delta < delta0 ->
         forall y, ylo <= y <= yhi ->
           ~ ring_image r (corridor_east d delta y)) ->
    connected_in_complement_cont r
      (point_at (dbase d)
         (corner_sample_out (ddir d) rho (corner_delta_for_ef_east d ef)))
      (mkPoint (edge_x_at d my + ef) my).
Proof.
  intros D r d rho ef my h_base ylo yhi Htaut Hcross Hforeign Hx HringD
         Hspan Hle Hasc Hhbase [[Hhlo Hhhi] Hmhi] Hef
         [delta0 [Hd0 [Hhalf Hclear]]].
  apply (along_dart_base_to_straddle_east r d rho ef my h_base Hasc Hhbase).
  - exact Hhhi.
  - intros y Hy.
    apply (corridor_ef_inherits_clearance_east d r delta0 ef y ylo yhi Hd0 Hef Hhalf Hle).
    + exact Hclear.
    + lra.
Qed.

(* C-3e-4 corner endpoints for the along-dart headline (base = left, tip = right). *)
Definition corner_sample_left (d : Dart) (rho ef : R) : Point :=
  point_at (dbase d)
    (corner_sample_out (ddir d) rho (corner_delta_for_ef_west d ef)).

Definition corner_sample_right (d : Dart) (rho ef : R) : Point :=
  point_at (dtip d)
    (corner_sample_in (point_diff (dbase d) (dtip d)) rho
       (corner_delta_for_ef_west d ef)).

(* Exact straddle pair named as in `face_transport_premise` (HBridgeCoreSlice.v). *)
Lemma face_transport_straddle_pair_eq :
  forall (d : Dart) (my ef : R),
    let p1 := mkPoint (edge_x_at d my - ef) my in
    let p2 := mkPoint (edge_x_at d my + ef) my in
    p1 = corridor d ef my /\ p2 = corridor_east d ef my.
Proof.
  intros d my ef. split; [ exact (straddle_west_eq_corridor d my ef)
                           | exact (straddle_east_eq_corridor_east d my ef) ].
Qed.

(* FOREIGN-DART chord only: when `d` is off `ring_edges r`, the horizontal
   segment between p_west and p_east at `my` need not meet the ring (the
   carrier midpoint `(edge_x_at d my, my)` is avoided because `d` is not a
   ring edge).  Do NOT use on ring darts in `face_transport_premise`'s
   `ring_of_chain (d :: c)` — there the carrier lies on the cycle. *)
Lemma foreign_dart_straddle_pair_chord_at_my :
  forall (r : Ring) (d : Dart) (ef my : R),
    ~ In d (ring_edges r) ->
    (forall t, 0 <= t <= 1 ->
       ring_complement r
         (mkPoint (edge_x_at d my - ef + t * (2 * ef)) my)) ->
    connected_in_complement_cont r
      (mkPoint (edge_x_at d my - ef) my)
      (mkPoint (edge_x_at d my + ef) my).
Proof.
  intros r d ef my Hdedge Hchord.
  set (v := mkPoint (edge_x_at d my) my).
  set (A := mkVec (- ef) 0).
  set (B := mkVec ef 0).
  assert (Hwest : point_at v A = mkPoint (edge_x_at d my - ef) my).
  { unfold point_at, A, v. cbn. f_equal; ring. }
  assert (Heast : point_at v B = mkPoint (edge_x_at d my + ef) my).
  { unfold point_at, B, v. cbn. f_equal; ring. }
  assert (Hhop : forall t, 0 <= t <= 1 ->
    ring_complement r (point_at v (vaffine t A B))).
  { intros t Ht.
    assert (Hblend : point_at v (vaffine t A B) =
      mkPoint (edge_x_at d my - ef + t * (2 * ef)) my).
    { unfold point_at, vaffine, vadd, vscale, A, B, v. cbn. f_equal; ring. }
    rewrite Hblend. exact (Hchord t Ht). }
  pose proof (hop_connected r v A B Hhop) as Hconn.
  rewrite Hwest, Heast in Hconn.
  exact Hconn.
Qed.

Definition corner_sample_left_east (d : Dart) (rho ef : R) : Point :=
  point_at (dbase d)
    (corner_sample_out (ddir d) rho (corner_delta_for_ef_east d ef)).

Theorem along_dart_tip_to_straddle_west_clear :
  forall (D : list Dart) (r : Ring) (d : Dart) (rho ef my h_tip ylo yhi : R),
    ring_taut r ->
    pairwise_no_proper_cross_twin_aware D ->
    no_foreign_vertex_twin_aware D ->
    In d D ->
    (forall f, In f (ring_edges r) -> In f D) ->
    ((py (fst d) < ylo /\ yhi < py (snd d)) \/
     (py (snd d) < ylo /\ yhi < py (fst d))) ->
    ylo <= yhi ->
    vy (ddir d) < 0 ->
    h_tip = bridge_height_tip d rho (corner_delta_for_ef_west d ef) ->
    ylo <= my ->
    my <= h_tip <= yhi ->
    0 < ef ->
    (exists delta0, 0 < delta0 /\
       ef < corridor_safe_half delta0 /\
       forall delta, 0 < delta < delta0 ->
         forall y, ylo <= y <= yhi ->
           ~ ring_image r (corridor d delta y)) ->
    connected_in_complement_cont r (corner_sample_right d rho ef)
      (mkPoint (edge_x_at d my - ef) my).
Proof.
  intros D r d rho ef my h_tip ylo yhi Htaut Hcross Hforeign Hx HringD
         Hspan Hle Hdesc Hhtip Hylomy [Hmhi Hthhi] Hef
         [delta0 [Hd0 [Hhalf Hclear]]].
  apply (along_dart_tip_to_straddle_west r d rho ef my h_tip Hdesc).
  - exact Hmhi.
  - exact Hhtip.
  - intros y [Hylo Hyhi].
    apply (corridor_ef_inherits_clearance d r delta0 ef y ylo yhi Hd0 Hef Hhalf Hle).
    + exact Hclear.
    + split; lra.
Qed.

(* C-3e-4 west headline (descending): both corner samples reach the WEST
   `face_transport_premise` target `(edge_x_at d my - ef, my)` via the west
   corridor — no carrier-crossing chord. *)
Theorem corridor_safe_for_ef_west :
  forall (D : list Dart) (r : Ring) (d : Dart) (rho ef my h_base h_tip ylo yhi delta0 : R),
    ring_taut r ->
    pairwise_no_proper_cross_twin_aware D ->
    no_foreign_vertex_twin_aware D ->
    In d D ->
    (forall f, In f (ring_edges r) -> In f D) ->
    ((py (fst d) < ylo /\ yhi < py (snd d)) \/
     (py (snd d) < ylo /\ yhi < py (fst d))) ->
    ylo <= yhi ->
    vy (ddir d) < 0 ->
    h_base = bridge_height_base d rho (corner_delta_for_ef_west d ef) ->
    h_tip = bridge_height_tip d rho (corner_delta_for_ef_west d ef) ->
    ylo <= h_base <= my /\ my <= h_tip <= yhi ->
    0 < delta0 ->
    0 < ef ->
    ef < corridor_safe_threshold delta0 / 3 ->
    (forall delta, 0 < delta < delta0 ->
       forall y, ylo <= y <= yhi ->
         ~ ring_image r (corridor d delta y)) ->
    let p_west := mkPoint (edge_x_at d my - ef) my in
    connected_in_complement_cont r (corner_sample_left d rho ef) p_west /\
    connected_in_complement_cont r (corner_sample_right d rho ef) p_west.
Proof.
  intros D r d rho ef my h_base h_tip ylo yhi delta0 Htaut Hcross Hforeign Hx HringD
         Hspan Hle Hdesc Hhbase Hhtip [Hhlo [Hmhi Hthhi]] Hd0 Hef Hthird Hclear p_west.
  assert (Hhalf : ef < corridor_safe_half delta0)
    by (apply (ef_lt_threshold_third_implies_half delta0 ef Hd0 Hef); exact Hthird).
  assert (Hmyle : my <= yhi) by (apply (Rle_trans _ _ _ Hmhi Hthhi)).
  assert (Hylomy : ylo <= my).
  { destruct Hhlo as [Hblo Hbmy]. apply (Rle_trans _ _ _ Hblo Hbmy). }
  split.
  - apply (along_dart_base_to_straddle_west_clear D r d rho ef my h_base ylo yhi);
      [ exact Htaut | exact Hcross | exact Hforeign | exact Hx | exact HringD
      | exact Hspan | exact Hle | exact Hdesc | exact Hhbase
      | exact (conj Hhlo Hmyle) | exact Hef
      | exists delta0; split; [exact Hd0 | split; [exact Hhalf | exact Hclear]] ].
  - apply (along_dart_tip_to_straddle_west_clear D r d rho ef my h_tip ylo yhi);
      [ exact Htaut | exact Hcross | exact Hforeign | exact Hx | exact HringD
      | exact Hspan | exact Hle | exact Hdesc | exact Hhtip | exact Hylomy
      | repeat split; assumption | exact Hef
      | exists delta0; split; [exact Hd0 | split; [exact Hhalf | exact Hclear]] ].
Qed.

(* C-3e-4 east headline (ascending): base corner reaches the EAST
   `face_transport_premise` target `(edge_x_at d my + ef, my)`. *)
Theorem corridor_safe_for_ef_east :
  forall (D : list Dart) (r : Ring) (d : Dart) (rho ef my h_base ylo yhi delta0 : R),
    ring_taut r ->
    pairwise_no_proper_cross_twin_aware D ->
    no_foreign_vertex_twin_aware D ->
    In d D ->
    (forall f, In f (ring_edges r) -> In f D) ->
    ((py (fst d) < ylo /\ yhi < py (snd d)) \/
     (py (snd d) < ylo /\ yhi < py (fst d))) ->
    ylo <= yhi ->
    vy (ddir d) > 0 ->
    h_base = bridge_height_base d rho (corner_delta_for_ef_east d ef) ->
    ylo <= h_base <= my /\ my <= yhi ->
    0 < delta0 ->
    0 < ef ->
    ef < corridor_safe_threshold delta0 / 3 ->
    (forall delta, 0 < delta < delta0 ->
       forall y, ylo <= y <= yhi ->
         ~ ring_image r (corridor_east d delta y)) ->
    let p_east := mkPoint (edge_x_at d my + ef) my in
    connected_in_complement_cont r (corner_sample_left_east d rho ef) p_east.
Proof.
  intros D r d rho ef my h_base ylo yhi delta0 Htaut Hcross Hforeign Hx HringD
         Hspan Hle Hasc Hhbase [Hhlo Hmhi] Hd0 Hef Hthird Hclear_east p_east.
  assert (Hhalf : ef < corridor_safe_half delta0)
    by (apply (ef_lt_threshold_third_implies_half delta0 ef Hd0 Hef); exact Hthird).
  unfold corner_sample_left_east.
  apply (along_dart_base_to_straddle_east_clear D r d rho ef my h_base ylo yhi);
    [ exact Htaut | exact Hcross | exact Hforeign | exact Hx | exact HringD
    | exact Hspan | exact Hle | exact Hasc | exact Hhbase
    | exact (conj Hhlo Hmhi) | exact Hef
    | exists delta0; split; [exact Hd0 | split; [exact Hhalf | exact Hclear_east]] ].
Qed.

(* FOREIGN-DART packaging: when `d` is not on the ring, both exact straddle
   targets are reachable (east via the foreign chord after tip->west). *)
Theorem foreign_dart_corridor_safe_for_ef :
  forall (r : Ring) (d : Dart) (rho ef my : R),
    let p_west := mkPoint (edge_x_at d my - ef) my in
    let p_east := mkPoint (edge_x_at d my + ef) my in
    connected_in_complement_cont r (corner_sample_left d rho ef) p_west ->
    connected_in_complement_cont r (corner_sample_right d rho ef) p_west ->
    ~ In d (ring_edges r) ->
    (forall t, 0 <= t <= 1 ->
       ring_complement r (mkPoint (edge_x_at d my - ef + t * (2 * ef)) my)) ->
    connected_in_complement_cont r (corner_sample_left d rho ef) p_west /\
    connected_in_complement_cont r (corner_sample_right d rho ef) p_west /\
    connected_in_complement_cont r (corner_sample_right d rho ef) p_east.
Proof.
  intros r d rho ef my p_west p_east Hleft Hright Hdedge Hchord.
  split; [ exact Hleft | split; [ exact Hright | ] ].
  apply (connected_in_complement_cont_trans r
           (corner_sample_right d rho ef) p_west p_east).
  - exact Hright.
  - exact (foreign_dart_straddle_pair_chord_at_my r d ef my Hdedge Hchord).
Qed.

(* Foreign-dart branch of the C-3e-4 headline: both ±ef targets connected. *)
Theorem corridor_safe_for_ef_foreign :
  forall (D : list Dart) (r : Ring) (d : Dart) (rho ef my h_base h_tip ylo yhi delta0 : R),
    ring_taut r ->
    pairwise_no_proper_cross_twin_aware D ->
    no_foreign_vertex_twin_aware D ->
    In d D ->
    (forall f, In f (ring_edges r) -> In f D) ->
    ((py (fst d) < ylo /\ yhi < py (snd d)) \/
     (py (snd d) < ylo /\ yhi < py (fst d))) ->
    ylo <= yhi ->
    vy (ddir d) < 0 ->
    h_base = bridge_height_base d rho (corner_delta_for_ef_west d ef) ->
    h_tip = bridge_height_tip d rho (corner_delta_for_ef_west d ef) ->
    ylo <= h_base <= my /\ my <= h_tip <= yhi ->
    0 < delta0 ->
    0 < ef ->
    ef < corridor_safe_threshold delta0 / 3 ->
    (forall delta, 0 < delta < delta0 ->
       forall y, ylo <= y <= yhi ->
         ~ ring_image r (corridor d delta y)) ->
    ~ In d (ring_edges r) ->
    (forall t, 0 <= t <= 1 ->
       ring_complement r (mkPoint (edge_x_at d my - ef + t * (2 * ef)) my)) ->
    let p_west := mkPoint (edge_x_at d my - ef) my in
    let p_east := mkPoint (edge_x_at d my + ef) my in
    connected_in_complement_cont r (corner_sample_left d rho ef) p_west /\
    connected_in_complement_cont r (corner_sample_right d rho ef) p_west /\
    connected_in_complement_cont r (corner_sample_right d rho ef) p_east.
Proof.
  intros D r d rho ef my h_base h_tip ylo yhi delta0 Htaut Hcross Hforeign Hx HringD
         Hspan Hle Hdesc Hhbase Hhtip [Hhlo [Hmhi Hthhi]] Hd0 Hef Hthird Hclear Hdedge Hchord
         p_west p_east.
  destruct (corridor_safe_for_ef_west D r d rho ef my h_base h_tip ylo yhi delta0
              Htaut Hcross Hforeign Hx HringD Hspan Hle Hdesc Hhbase Hhtip
              (conj Hhlo (conj Hmhi Hthhi)) Hd0 Hef Hthird Hclear) as [Hleft Hright].
  apply (foreign_dart_corridor_safe_for_ef r d rho ef my Hleft Hright Hdedge Hchord).
Qed.

(* C-3e-4 headline: names the exact `face_transport_premise` pair and wires
   west (descending) / east (ascending) corridor rides.
   The first conj gives UNCONDITIONAL exact targets
   `(edge_x_at d my - ef, my)` / `(edge_x_at d my + ef, my)` via
   `face_transport_straddle_pair_eq`.  Connection facts are case-split
   (ring membership × vy sign); ring-dart east at `my` on descending darts
   is deferred to C-3f orbit (carrier blocks same-height chord). *)
Theorem corridor_safe_for_ef :
  forall (D : list Dart) (r : Ring) (d : Dart) (rho ef my h_base h_tip ylo yhi delta0 : R),
    ring_taut r ->
    pairwise_no_proper_cross_twin_aware D ->
    no_foreign_vertex_twin_aware D ->
    In d D ->
    (forall f, In f (ring_edges r) -> In f D) ->
    ((py (fst d) < ylo /\ yhi < py (snd d)) \/
     (py (snd d) < ylo /\ yhi < py (fst d))) ->
    ylo <= yhi ->
    ylo <= h_base <= my /\ my <= h_tip <= yhi ->
    0 < delta0 ->
    0 < ef ->
    ef < corridor_safe_threshold delta0 / 3 ->
    let p_west := mkPoint (edge_x_at d my - ef) my in
    let p_east := mkPoint (edge_x_at d my + ef) my in
    (p_west = corridor d ef my /\ p_east = corridor_east d ef my) /\
    ((In d (ring_edges r) /\ vy (ddir d) < 0 ->
      h_base = bridge_height_base d rho (corner_delta_for_ef_west d ef) ->
      h_tip = bridge_height_tip d rho (corner_delta_for_ef_west d ef) ->
      (forall delta, 0 < delta < delta0 ->
         forall y, ylo <= y <= yhi ->
           ~ ring_image r (corridor d delta y)) ->
      connected_in_complement_cont r (corner_sample_left d rho ef) p_west /\
      connected_in_complement_cont r (corner_sample_right d rho ef) p_west)) /\
    ((In d (ring_edges r) /\ vy (ddir d) > 0 ->
      h_base = bridge_height_base d rho (corner_delta_for_ef_east d ef) ->
      (forall delta, 0 < delta < delta0 ->
         forall y, ylo <= y <= yhi ->
           ~ ring_image r (corridor_east d delta y)) ->
      connected_in_complement_cont r (corner_sample_left_east d rho ef) p_east)) /\
    ((~ In d (ring_edges r) /\ vy (ddir d) < 0 ->
      h_base = bridge_height_base d rho (corner_delta_for_ef_west d ef) ->
      h_tip = bridge_height_tip d rho (corner_delta_for_ef_west d ef) ->
      (forall delta, 0 < delta < delta0 ->
         forall y, ylo <= y <= yhi ->
           ~ ring_image r (corridor d delta y)) ->
      (forall t, 0 <= t <= 1 ->
         ring_complement r (mkPoint (edge_x_at d my - ef + t * (2 * ef)) my)) ->
      connected_in_complement_cont r (corner_sample_left d rho ef) p_west /\
      connected_in_complement_cont r (corner_sample_right d rho ef) p_west /\
      connected_in_complement_cont r (corner_sample_right d rho ef) p_east)).
Proof.
  intros D r d rho ef my h_base h_tip ylo yhi delta0 Htaut Hcross Hforeign Hx HringD
         Hspan Hle [Hhlo [Hmhi Hthhi]] Hd0 Hef Hthird p_west p_east.
  destruct (face_transport_straddle_pair_eq d my ef) as [Heq_west Heq_east].
  assert (Hmyle : my <= yhi) by (apply (Rle_trans _ _ _ Hmhi Hthhi)).
  split.
  { split; [ exact Heq_west | exact Heq_east ]. }
  split.
  { intros [Hinring Hdesc] Hhbase' Hhtip' Hclear.
    apply (corridor_safe_for_ef_west D r d rho ef my h_base h_tip ylo yhi delta0);
      [ exact Htaut | exact Hcross | exact Hforeign | exact Hx | exact HringD
      | exact Hspan | exact Hle | exact Hdesc | exact Hhbase' | exact Hhtip'
      | exact (conj Hhlo (conj Hmhi Hthhi)) | exact Hd0 | exact Hef | exact Hthird
      | exact Hclear ]. }
  split.
  { intros [Hinring Hasc] Hhbase' Hclear_east.
    apply (corridor_safe_for_ef_east D r d rho ef my h_base ylo yhi delta0);
      [ exact Htaut | exact Hcross | exact Hforeign | exact Hx | exact HringD
      | exact Hspan | exact Hle | exact Hasc | exact Hhbase'
      | exact (conj Hhlo Hmyle) | exact Hd0 | exact Hef | exact Hthird
      | exact Hclear_east ]. }
  { intros [Hdedge Hdesc] Hhbase' Hhtip' Hclear Hchord.
    apply (corridor_safe_for_ef_foreign D r d rho ef my h_base h_tip ylo yhi delta0);
      [ exact Htaut | exact Hcross | exact Hforeign | exact Hx | exact HringD
      | exact Hspan | exact Hle | exact Hdesc | exact Hhbase' | exact Hhtip'
      | exact (conj Hhlo (conj Hmhi Hthhi)) | exact Hd0 | exact Hef | exact Hthird
      | exact Hclear | exact Hdedge | exact Hchord ]. }
Qed.

(* Downstream discharge for `face_transport_premise` (HBridgeCoreSlice.v §2):
   the premise's cycle ring has `d` ON the ring (`ring_edges r = d :: c`);
   descending ring dart — west exact target connected from both corners.
   East at `my` on ring darts deferred to C-3f orbit. *)
Lemma face_transport_premise_ring_dart_west_straddle_connected :
  forall (E : list Edge) (D : list Dart) (r : Ring) (d : Dart) (c : list Dart)
         (rho ef my h_base h_tip ylo yhi delta0 : R),
    face_transport_premise E ->
    r = ring_of_chain (d :: c) ->
    In d (ring_edges r) ->
    ring_taut r ->
    pairwise_no_proper_cross_twin_aware D ->
    no_foreign_vertex_twin_aware D ->
    In d D ->
    In d E ->
    (forall f, In f (ring_edges r) -> In f D) ->
    ((py (fst d) < ylo /\ yhi < py (snd d)) \/
     (py (snd d) < ylo /\ yhi < py (fst d))) ->
    ylo <= yhi ->
    vy (ddir d) < 0 ->
    h_base = bridge_height_base d rho (corner_delta_for_ef_west d ef) ->
    h_tip = bridge_height_tip d rho (corner_delta_for_ef_west d ef) ->
    ylo <= h_base <= my /\ my <= h_tip <= yhi ->
    0 < delta0 ->
    0 < ef ->
    ef < corridor_safe_threshold delta0 / 3 ->
    (forall delta, 0 < delta < delta0 ->
       forall y, ylo <= y <= yhi ->
         ~ ring_image r (corridor d delta y)) ->
    connected_in_complement_cont r (corner_sample_left d rho ef)
      (mkPoint (edge_x_at d my - ef) my) /\
    connected_in_complement_cont r (corner_sample_right d rho ef)
      (mkPoint (edge_x_at d my - ef) my).
Proof.
  intros E D r d c rho ef my h_base h_tip ylo yhi delta0
         Hprem Hr Hinring Htaut Hcross Hforeign Hx HdE HringD Hspan Hle Hdesc
         Hhbase Hhtip [Hhlo [Hmhi Hthhi]] Hd0 Hef Hthird Hclear.
  destruct (corridor_safe_for_ef D r d rho ef my h_base h_tip ylo yhi delta0
              Htaut Hcross Hforeign Hx HringD Hspan Hle
              (conj Hhlo (conj Hmhi Hthhi)) Hd0 Hef Hthird) as [_ [Hwest [_ _]]].
  apply (Hwest (conj Hinring Hdesc) Hhbase Hhtip Hclear).
Qed.

(* Ascending ring dart — east exact target connected from base east corner. *)
Lemma face_transport_premise_ring_dart_east_straddle_connected :
  forall (E : list Edge) (D : list Dart) (r : Ring) (d : Dart) (c : list Dart)
         (rho ef my h_base h_tip ylo yhi delta0 : R),
    face_transport_premise E ->
    r = ring_of_chain (d :: c) ->
    In d (ring_edges r) ->
    ring_taut r ->
    pairwise_no_proper_cross_twin_aware D ->
    no_foreign_vertex_twin_aware D ->
    In d D ->
    In d E ->
    (forall f, In f (ring_edges r) -> In f D) ->
    ((py (fst d) < ylo /\ yhi < py (snd d)) \/
     (py (snd d) < ylo /\ yhi < py (fst d))) ->
    ylo <= yhi ->
    vy (ddir d) > 0 ->
    h_base = bridge_height_base d rho (corner_delta_for_ef_east d ef) ->
    ylo <= h_base <= my /\ my <= h_tip <= yhi ->
    0 < delta0 ->
    0 < ef ->
    ef < corridor_safe_threshold delta0 / 3 ->
    (forall delta, 0 < delta < delta0 ->
       forall y, ylo <= y <= yhi ->
         ~ ring_image r (corridor_east d delta y)) ->
    connected_in_complement_cont r (corner_sample_left_east d rho ef)
      (mkPoint (edge_x_at d my + ef) my).
Proof.
  intros E D r d c rho ef my h_base h_tip ylo yhi delta0
         Hprem Hr Hinring Htaut Hcross Hforeign Hx HdE HringD Hspan Hle Hasc
         Hhbase [Hhlo [Hmhi Hthhi]] Hd0 Hef Hthird Hclear_east.
  destruct (corridor_safe_for_ef D r d rho ef my h_base h_tip ylo yhi delta0
              Htaut Hcross Hforeign Hx HringD Hspan Hle
              (conj Hhlo (conj Hmhi Hthhi)) Hd0 Hef Hthird) as [_ [_ [Heast _]]].
  apply (Heast (conj Hinring Hasc) Hhbase Hclear_east).
Qed.

(* Ring-dart packaging: exact ±ef target names + orientation-split connections.
   Descending: both corners -> west (`-ef`); ascending: base east corner -> `+ef`.
   Cross-orientation target on ring darts (descending `+ef`, ascending `-ef`)
   is deferred to C-3f orbit (carrier blocks same-height chord). *)
Lemma face_transport_premise_ring_dart_straddle_pair_connected :
  forall (E : list Edge) (D : list Dart) (r : Ring) (d : Dart) (c : list Dart)
         (rho ef my h_base h_tip ylo yhi delta0 : R),
    face_transport_premise E ->
    r = ring_of_chain (d :: c) ->
    In d (ring_edges r) ->
    ring_taut r ->
    pairwise_no_proper_cross_twin_aware D ->
    no_foreign_vertex_twin_aware D ->
    In d D ->
    In d E ->
    (forall f, In f (ring_edges r) -> In f D) ->
    ((py (fst d) < ylo /\ yhi < py (snd d)) \/
     (py (snd d) < ylo /\ yhi < py (fst d))) ->
    ylo <= yhi ->
    h_base = bridge_height_base d rho (corner_delta_for_ef_west d ef) ->
    h_tip = bridge_height_tip d rho (corner_delta_for_ef_west d ef) ->
    ylo <= h_base <= my /\ my <= h_tip <= yhi ->
    0 < delta0 ->
    0 < ef ->
    ef < corridor_safe_threshold delta0 / 3 ->
    (forall delta, 0 < delta < delta0 ->
       forall y, ylo <= y <= yhi ->
         ~ ring_image r (corridor d delta y)) ->
    let p_west := mkPoint (edge_x_at d my - ef) my in
    let p_east := mkPoint (edge_x_at d my + ef) my in
    (p_west = corridor d ef my /\ p_east = corridor_east d ef my) /\
    (vy (ddir d) < 0 ->
      connected_in_complement_cont r (corner_sample_left d rho ef) p_west /\
      connected_in_complement_cont r (corner_sample_right d rho ef) p_west) /\
    (vy (ddir d) > 0 ->
      h_base = bridge_height_base d rho (corner_delta_for_ef_east d ef) ->
      (forall delta, 0 < delta < delta0 ->
         forall y, ylo <= y <= yhi ->
           ~ ring_image r (corridor_east d delta y)) ->
      connected_in_complement_cont r (corner_sample_left_east d rho ef) p_east).
Proof.
  intros E D r d c rho ef my h_base h_tip ylo yhi delta0
         Hprem Hr Hinring Htaut Hcross Hforeign Hx HdE HringD Hspan Hle
         Hhbase_west Hhtip_west [Hhlo [Hmhi Hthhi]] Hd0 Hef Hthird Hclear_west
         p_west p_east.
  destruct (face_transport_straddle_pair_eq d my ef) as [Heq_west Heq_east].
  split.
  { split; [ exact Heq_west | exact Heq_east ]. }
  split.
  - intros Hdesc.
    apply (face_transport_premise_ring_dart_west_straddle_connected E D r d c
             rho ef my h_base h_tip ylo yhi delta0 Hprem Hr Hinring Htaut Hcross
             Hforeign Hx HdE HringD Hspan Hle Hdesc Hhbase_west Hhtip_west
             (conj Hhlo (conj Hmhi Hthhi)) Hd0 Hef Hthird Hclear_west).
  - intros Hasc Hhbase_east Hclear_east.
    apply (face_transport_premise_ring_dart_east_straddle_connected E D r d c
             rho ef my h_base h_tip ylo yhi delta0 Hprem Hr Hinring Htaut Hcross
             Hforeign Hx HdE HringD Hspan Hle Hasc Hhbase_east
             (conj Hhlo (conj Hmhi Hthhi)) Hd0 Hef Hthird Hclear_east).
Qed.

(* Premise-layer apply hooks (HBridgeCoreSlice cannot import this file). *)
Lemma face_transport_premise_ring_dart_west_straddle_in_complement :
  forall (E : list Edge) (D : list Dart) (r : Ring) (d : Dart) (c : list Dart)
         (rho ef my h_base h_tip ylo yhi delta0 : R),
    face_transport_premise E ->
    r = ring_of_chain (d :: c) ->
    In d (ring_edges r) ->
    ring_taut r ->
    pairwise_no_proper_cross_twin_aware D ->
    no_foreign_vertex_twin_aware D ->
    In d D ->
    In d E ->
    (forall f, In f (ring_edges r) -> In f D) ->
    ((py (fst d) < ylo /\ yhi < py (snd d)) \/
     (py (snd d) < ylo /\ yhi < py (fst d))) ->
    ylo <= yhi ->
    vy (ddir d) < 0 ->
    h_base = bridge_height_base d rho (corner_delta_for_ef_west d ef) ->
    h_tip = bridge_height_tip d rho (corner_delta_for_ef_west d ef) ->
    ylo <= h_base <= my /\ my <= h_tip <= yhi ->
    0 < delta0 ->
    0 < ef ->
    ef < corridor_safe_threshold delta0 / 3 ->
    (forall delta, 0 < delta < delta0 ->
       forall y, ylo <= y <= yhi ->
         ~ ring_image r (corridor d delta y)) ->
    ring_complement r (mkPoint (edge_x_at d my - ef) my).
Proof.
  intros E D r d c rho ef my h_base h_tip ylo yhi delta0
         Hprem Hr Hinring Htaut Hcross Hforeign Hx HdE HringD Hspan Hle Hdesc
         Hhbase Hhtip [Hhlo [Hmhi Hthhi]] Hd0 Hef Hthird Hclear.
  destruct (face_transport_premise_ring_dart_west_straddle_connected E D r d c
              rho ef my h_base h_tip ylo yhi delta0 Hprem Hr Hinring Htaut Hcross
              Hforeign Hx HdE HringD Hspan Hle Hdesc Hhbase Hhtip
              (conj Hhlo (conj Hmhi Hthhi)) Hd0 Hef Hthird Hclear) as [Hconn _].
  apply (face_transport_straddle_target_in_complement r _ _ Hconn).
Qed.

Lemma face_transport_premise_ring_dart_east_straddle_in_complement :
  forall (E : list Edge) (D : list Dart) (r : Ring) (d : Dart) (c : list Dart)
         (rho ef my h_base h_tip ylo yhi delta0 : R),
    face_transport_premise E ->
    r = ring_of_chain (d :: c) ->
    In d (ring_edges r) ->
    ring_taut r ->
    pairwise_no_proper_cross_twin_aware D ->
    no_foreign_vertex_twin_aware D ->
    In d D ->
    In d E ->
    (forall f, In f (ring_edges r) -> In f D) ->
    ((py (fst d) < ylo /\ yhi < py (snd d)) \/
     (py (snd d) < ylo /\ yhi < py (fst d))) ->
    ylo <= yhi ->
    vy (ddir d) > 0 ->
    h_base = bridge_height_base d rho (corner_delta_for_ef_east d ef) ->
    ylo <= h_base <= my /\ my <= h_tip <= yhi ->
    0 < delta0 ->
    0 < ef ->
    ef < corridor_safe_threshold delta0 / 3 ->
    (forall delta, 0 < delta < delta0 ->
       forall y, ylo <= y <= yhi ->
         ~ ring_image r (corridor_east d delta y)) ->
    ring_complement r (mkPoint (edge_x_at d my + ef) my).
Proof.
  intros E D r d c rho ef my h_base h_tip ylo yhi delta0
         Hprem Hr Hinring Htaut Hcross Hforeign Hx HdE HringD Hspan Hle Hasc
         Hhbase [Hhlo [Hmhi Hthhi]] Hd0 Hef Hthird Hclear_east.
  pose proof (face_transport_premise_ring_dart_east_straddle_connected E D r d c
               rho ef my h_base h_tip ylo yhi delta0 Hprem Hr Hinring Htaut Hcross
               Hforeign Hx HdE HringD Hspan Hle Hasc Hhbase
               (conj Hhlo (conj Hmhi Hthhi)) Hd0 Hef Hthird Hclear_east) as Hconn.
  apply (face_transport_straddle_target_in_complement r _ _ Hconn).
Qed.

Lemma face_transport_premise_ring_dart_straddle_pair_in_complement :
  forall (E : list Edge) (D : list Dart) (r : Ring) (d : Dart) (c : list Dart)
         (rho ef my h_base h_tip ylo yhi delta0 : R),
    face_transport_premise E ->
    r = ring_of_chain (d :: c) ->
    In d (ring_edges r) ->
    ring_taut r ->
    pairwise_no_proper_cross_twin_aware D ->
    no_foreign_vertex_twin_aware D ->
    In d D ->
    In d E ->
    (forall f, In f (ring_edges r) -> In f D) ->
    ((py (fst d) < ylo /\ yhi < py (snd d)) \/
     (py (snd d) < ylo /\ yhi < py (fst d))) ->
    ylo <= yhi ->
    h_base = bridge_height_base d rho (corner_delta_for_ef_west d ef) ->
    h_tip = bridge_height_tip d rho (corner_delta_for_ef_west d ef) ->
    ylo <= h_base <= my /\ my <= h_tip <= yhi ->
    0 < delta0 ->
    0 < ef ->
    ef < corridor_safe_threshold delta0 / 3 ->
    (forall delta, 0 < delta < delta0 ->
       forall y, ylo <= y <= yhi ->
         ~ ring_image r (corridor d delta y)) ->
    let p_west := mkPoint (edge_x_at d my - ef) my in
    let p_east := mkPoint (edge_x_at d my + ef) my in
    (p_west = corridor d ef my /\ p_east = corridor_east d ef my) /\
    (vy (ddir d) < 0 -> ring_complement r p_west) /\
    (vy (ddir d) > 0 ->
      h_base = bridge_height_base d rho (corner_delta_for_ef_east d ef) ->
      (forall delta, 0 < delta < delta0 ->
         forall y, ylo <= y <= yhi ->
           ~ ring_image r (corridor_east d delta y)) ->
      ring_complement r p_east).
Proof.
  intros E D r d c rho ef my h_base h_tip ylo yhi delta0
         Hprem Hr Hinring Htaut Hcross Hforeign Hx HdE HringD Hspan Hle
         Hhbase_west Hhtip_west [Hhlo [Hmhi Hthhi]] Hd0 Hef Hthird Hclear_west
         p_west p_east.
  destruct (face_transport_premise_ring_dart_straddle_pair_connected E D r d c
              rho ef my h_base h_tip ylo yhi delta0 Hprem Hr Hinring Htaut Hcross
              Hforeign Hx HdE HringD Hspan Hle Hhbase_west Hhtip_west
              (conj Hhlo (conj Hmhi Hthhi)) Hd0 Hef Hthird Hclear_west) as [Heq [Hwest Heast]].
  split.
  - exact Heq.
  - split.
    + intros Hdesc.
      apply (face_transport_premise_ring_dart_west_straddle_in_complement E D r d c
               rho ef my h_base h_tip ylo yhi delta0 Hprem Hr Hinring Htaut Hcross
               Hforeign Hx HdE HringD Hspan Hle Hdesc Hhbase_west Hhtip_west
               (conj Hhlo (conj Hmhi Hthhi)) Hd0 Hef Hthird Hclear_west).
    + intros Hasc Hhbase_east Hclear_east.
      apply (face_transport_premise_ring_dart_east_straddle_in_complement E D r d c
               rho ef my h_base h_tip ylo yhi delta0 Hprem Hr Hinring Htaut Hcross
               Hforeign Hx HdE HringD Hspan Hle Hasc Hhbase_east
               (conj Hhlo (conj Hmhi Hthhi)) Hd0 Hef Hthird Hclear_east).
Qed.

(* Foreign-dart discharge: BOTH exact ±ef targets connected and in complement. *)
Lemma face_transport_premise_foreign_straddle_pair_in_complement :
  forall (E : list Edge) (D : list Dart) (r : Ring) (d : Dart) (c : list Dart)
         (rho ef my h_base h_tip ylo yhi delta0 : R),
    face_transport_premise E ->
    r = ring_of_chain (d :: c) ->
    ~ In d (ring_edges r) ->
    ring_taut r ->
    pairwise_no_proper_cross_twin_aware D ->
    no_foreign_vertex_twin_aware D ->
    In d D ->
    In d E ->
    (forall f, In f (ring_edges r) -> In f D) ->
    ((py (fst d) < ylo /\ yhi < py (snd d)) \/
     (py (snd d) < ylo /\ yhi < py (fst d))) ->
    ylo <= yhi ->
    vy (ddir d) < 0 ->
    h_base = bridge_height_base d rho (corner_delta_for_ef_west d ef) ->
    h_tip = bridge_height_tip d rho (corner_delta_for_ef_west d ef) ->
    ylo <= h_base <= my /\ my <= h_tip <= yhi ->
    0 < delta0 ->
    0 < ef ->
    ef < corridor_safe_threshold delta0 / 3 ->
    (forall delta, 0 < delta < delta0 ->
       forall y, ylo <= y <= yhi ->
         ~ ring_image r (corridor d delta y)) ->
    (forall t, 0 <= t <= 1 ->
       ring_complement r (mkPoint (edge_x_at d my - ef + t * (2 * ef)) my)) ->
    let p_west := mkPoint (edge_x_at d my - ef) my in
    let p_east := mkPoint (edge_x_at d my + ef) my in
    (p_west = corridor d ef my /\ p_east = corridor_east d ef my) /\
    ring_complement r p_west /\ ring_complement r p_east.
Proof.
  intros E D r d c rho ef my h_base h_tip ylo yhi delta0
         Hprem Hr Hdedge Htaut Hcross Hforeign Hx HdE HringD Hspan Hle Hdesc
         Hhbase Hhtip [Hhlo [Hmhi Hthhi]] Hd0 Hef Hthird Hclear Hchord p_west p_east.
  destruct (face_transport_straddle_pair_eq d my ef) as [Heq_west Heq_east].
  destruct (corridor_safe_for_ef_foreign D r d rho ef my h_base h_tip ylo yhi delta0
              Htaut Hcross Hforeign Hx HringD Hspan Hle Hdesc Hhbase Hhtip
              (conj Hhlo (conj Hmhi Hthhi)) Hd0 Hef Hthird Hclear Hdedge Hchord) as [Hleft [Hright Heast]].
  split.
  - split; assumption.
  - apply (face_transport_straddle_complements_of_connected r _ _ _ _ Hleft Heast).
Qed.

(* Discharge hook for `face_transport_premise` (HBridgeCoreSlice.v §2): west
   straddle target connected from corner_sample_left on descending darts. *)
Lemma face_transport_west_straddle_headline_connected :
  forall (r : Ring) (d : Dart) (rho ef my : R),
    let p_west := mkPoint (edge_x_at d my - ef) my in
    connected_in_complement_cont r (corner_sample_left d rho ef) p_west ->
    p_west = corridor d ef my /\
    connected_in_complement_cont r (corner_sample_left d rho ef) p_west.
Proof.
  intros r d rho ef my p_west Hconn.
  destruct (face_transport_straddle_pair_eq d my ef) as [Heq _].
  split; [ exact Heq | exact Hconn ].
Qed.

Lemma face_transport_east_straddle_headline_connected :
  forall (r : Ring) (d : Dart) (rho ef my : R),
    let p_east := mkPoint (edge_x_at d my + ef) my in
    connected_in_complement_cont r (corner_sample_left_east d rho ef) p_east ->
    p_east = corridor_east d ef my /\
    connected_in_complement_cont r (corner_sample_left_east d rho ef) p_east.
Proof.
  intros r d rho ef my p_east Hconn.
  destruct (face_transport_straddle_pair_eq d my ef) as [_ Heq].
  split; [ exact Heq | exact Hconn ].
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Representative exercise on a concrete descending dart.                *)
(* -------------------------------------------------------------------------- *)

(* Base (0,2) -> tip (1,0): vy (ddir d) = -2 < 0. *)
Definition descending_sample_dart : Dart :=
  (mkPoint 0 2, mkPoint 1 0).

Lemma descending_sample_dart_vy :
  vy (ddir descending_sample_dart) < 0.
Proof.
  unfold descending_sample_dart, ddir, point_diff, dtip, dbase, vy, fst, snd.
  cbn. lra.
Qed.

Lemma bridge_delta_west_sample_closed :
  bridge_delta_west descending_sample_dart
    (corner_delta_for_ef_west descending_sample_dart (1 / 10))
  = 1 / 10.
Proof.
  apply bridge_delta_west_for_ef. exact descending_sample_dart_vy.
Qed.

Definition sample_ef : R := 1 / 10.
Definition sample_rho : R := 1 / 2.
Definition sample_my : R := 24 / 25.
Definition sample_h_base : R := 24 / 25.
Definition sample_h_tip : R := 24 / 25.
Definition sample_ring : Ring := rect_ring 10 10 12 12.
Definition sample_ylo : R := 1 / 100.
Definition sample_yhi : R := 99 / 50.
Definition sample_D : list Dart :=
  descending_sample_dart :: ring_edges sample_ring.

Lemma edge_x_at_sample_closed :
  edge_x_at descending_sample_dart sample_my = 13 / 25.
Proof.
  unfold descending_sample_dart, edge_x_at, sample_my. cbn.
  field_simplify. lra.
Qed.

Lemma straddle_west_target_sample_closed :
  corridor descending_sample_dart sample_ef sample_my =
    mkPoint (13 / 25 - sample_ef) sample_my.
Proof.
  rewrite straddle_west_eq_corridor, edge_x_at_sample_closed.
  reflexivity.
Qed.

Lemma handoff_base_sample_endpoint_closed :
  point_at (dbase descending_sample_dart)
    (corner_sample_out (ddir descending_sample_dart) (1 / 4)
       (corner_delta_for_ef_west descending_sample_dart (1 / 10)))
  = corridor descending_sample_dart (1 / 10)
      (bridge_height_base descending_sample_dart (1 / 4)
         (corner_delta_for_ef_west descending_sample_dart (1 / 10))).
Proof.
  set (d := descending_sample_dart).
  set (ef := 1 / 10).
  set (rho := 1 / 4).
  set (delta_c := corner_delta_for_ef_west d ef).
  set (h_base := bridge_height_base d rho delta_c).
  rewrite (handoff_base_bridge_west d rho delta_c descending_sample_dart_vy).
  change (delta_c * (vx (ddir d) * vx (ddir d) + vy (ddir d) * vy (ddir d))
            / (- vy (ddir d))) with (bridge_delta_west d delta_c).
  change (py (dbase d) + (rho * vy (ddir d) - delta_c * vx (ddir d)))
    with (bridge_height_base d rho delta_c).
  assert (Hbd : bridge_delta_west d delta_c = ef)
    by (unfold d, ef, delta_c; exact bridge_delta_west_sample_closed).
  assert (Hbh : bridge_height_base d rho delta_c = h_base) by reflexivity.
  rewrite Hbd, Hbh. reflexivity.
Qed.

Lemma rect_ring_no_foreign_vertex : forall x0 y0 x1 y1,
  x0 < x1 -> y0 < y1 ->
  ring_no_vertex_on_foreign_edge_interior (rect_ring x0 y0 x1 y1).
Proof.
  intros x0 y0 x1 y1 Hx01 Hy01 e f He Hf Hef.
  rewrite ring_edges_rect in He, Hf. cbn [In] in He, Hf.
  destruct He as [He | [He | [He | [He | []]]]];
  destruct Hf as [Hf | [Hf | [Hf | [Hf | []]]]];
    subst e f; cbn [fst snd px py];
    split; intros [t [[Ht0 Ht1] [Hx Hy]]];
    try (apply Hef; reflexivity);
    nra.
Qed.

Lemma sample_ring_taut : ring_taut sample_ring.
Proof.
  unfold sample_ring.
  apply ring_taut_of_simple_and_no_foreign_vertex.
  - apply rect_ring_simple; lra.
  - apply rect_ring_no_foreign_vertex; lra.
Qed.

Lemma sample_dart_px_le (t : R) :
  0 <= t <= 1 ->
  (1 - t) * px (dbase descending_sample_dart) + t * px (dtip descending_sample_dart) <= 1.
Proof.
  intros [Ht0 Ht1].
  unfold descending_sample_dart, dbase, dtip, px, fst, snd. nra.
Qed.

Lemma sample_dart_py_le (t : R) :
  0 <= t <= 1 ->
  (1 - t) * py (dbase descending_sample_dart) + t * py (dtip descending_sample_dart) <= 2.
Proof.
  intros [Ht0 Ht1].
  unfold descending_sample_dart, dbase, dtip, py, fst, snd. nra.
Qed.

Lemma sample_ring_edge_py_ge :
  forall (f : Edge) (s : R),
    In f (ring_edges sample_ring) ->
    0 <= s <= 1 ->
    10 <= (1 - s) * py (fst f) + s * py (snd f).
Proof.
  intros f s Hin Hs.
  unfold sample_ring in Hin.
  rewrite ring_edges_rect in Hin. cbn [In] in Hin.
  destruct Hin as [Hf | [Hf | [Hf | [Hf | []]]]]; subst f; cbn [fst snd py];
    destruct Hs as [Hs0 Hs1]; nra.
Qed.

Lemma sample_ring_edge_px_ge :
  forall (f : Edge) (t : R),
    In f (ring_edges sample_ring) ->
    0 <= t <= 1 ->
    10 <= (1 - t) * px (fst f) + t * px (snd f).
Proof.
  intros f t Hin Ht.
  unfold sample_ring in Hin.
  rewrite ring_edges_rect in Hin. cbn [In] in Hin.
  destruct Hin as [Hf | [Hf | [Hf | [Hf | []]]]]; subst f; cbn [fst snd px];
    destruct Ht as [Ht1 Ht2]; nra.
Qed.

Lemma sip_exchange_segments :
  forall (P0 P1 Q0 Q1 : Point),
    segments_intersect_properly P0 P1 Q0 Q1 ->
    segments_intersect_properly Q0 Q1 P0 P1.
Proof.
  intros P0 P1 Q0 Q1 (t & s & Ht & Hs & Hx & Hy).
  exists s, t. repeat split; try lra; assumption.
Qed.

Lemma sample_dart_no_proper_cross_ring_edge :
  forall (f : Edge),
    In f (ring_edges sample_ring) ->
    ~ segments_intersect_properly (dbase descending_sample_dart)
      (dtip descending_sample_dart) (fst f) (snd f).
Proof.
  intros f Hin (t & s & Ht & Hs & Hx & Hy).
  unfold sample_ring in Hin.
  rewrite ring_edges_rect in Hin. cbn [In] in Hin.
  destruct Hin as [Hf | [Hf | [Hf | [Hf | []]]]]; subst f;
    unfold descending_sample_dart, dbase, dtip, px, py, fst, snd in Hx, Hy;
    destruct Ht as [Ht0 Ht1]; destruct Hs as [Hs0 Hs1]; nra.
Qed.

Lemma sample_pairwise_twin_aware :
  pairwise_no_proper_cross_twin_aware sample_D.
Proof.
  unfold pairwise_no_proper_cross_twin_aware, sample_D.
  intros d1 d2 H1 H2 Hne Hnt Hcross.
  simpl in H1. destruct H1 as [Hd1 | H1]; [subst d1 | ].
  - simpl in H2. destruct H2 as [Hd2 | H2]; [subst d2; exfalso; apply Hne; reflexivity | ].
    apply (sample_dart_no_proper_cross_ring_edge d2 H2). exact Hcross.
  - simpl in H2. destruct H2 as [Hd2 | H2]; [subst d2 | ].
    + apply (sample_dart_no_proper_cross_ring_edge d1 H1).
      apply sip_exchange_segments. exact Hcross.
    + pose proof (rect_ring_simple 10 10 12 12 (ltac:(lra)) (ltac:(lra))) as Hsimp.
      unfold ring_simple in Hsimp.
      apply (Hsimp d1 d2 H1 H2 Hne). exact Hcross.
Qed.

Lemma sample_ring_vertices_not_on_dart :
  forall (f : Edge),
    In f (ring_edges sample_ring) ->
    (~ exists t : R, 0 < t < 1 /\
         px (fst f) = (1 - t) * px (dbase descending_sample_dart) + t * px (dtip descending_sample_dart) /\
         py (fst f) = (1 - t) * py (dbase descending_sample_dart) + t * py (dtip descending_sample_dart)) /\
    (~ exists t : R, 0 < t < 1 /\
         px (snd f) = (1 - t) * px (dbase descending_sample_dart) + t * px (dtip descending_sample_dart) /\
         py (snd f) = (1 - t) * py (dbase descending_sample_dart) + t * py (dtip descending_sample_dart)).
Proof.
  intros f Hin.
  unfold sample_ring in Hin.
  rewrite ring_edges_rect in Hin. cbn [In] in Hin.
  destruct Hin as [Hf | [Hf | [Hf | [Hf | []]]]]; subst f;
    split; intros [t [[Ht0 Ht1] [Hx Hy]]];
    unfold descending_sample_dart, dbase, dtip, px, py, fst, snd in Hx, Hy; nra.
Qed.

Lemma sample_dart_vertices_not_on_ring :
  forall (e : Edge),
    In e (ring_edges sample_ring) ->
    (~ exists t : R, 0 < t < 1 /\
         px (dbase descending_sample_dart) = (1 - t) * px (fst e) + t * px (snd e) /\
         py (dbase descending_sample_dart) = (1 - t) * py (fst e) + t * py (snd e)) /\
    (~ exists t : R, 0 < t < 1 /\
         px (dtip descending_sample_dart) = (1 - t) * px (fst e) + t * px (snd e) /\
         py (dtip descending_sample_dart) = (1 - t) * py (fst e) + t * py (snd e)).
Proof.
  intros e Hin.
  unfold sample_ring in Hin.
  rewrite ring_edges_rect in Hin. cbn [In] in Hin.
  destruct Hin as [He | [He | [He | [He | []]]]]; subst e;
    split; intros [t [[Ht0 Ht1] [Hx Hy]]];
    unfold descending_sample_dart, dbase, dtip, px, py, fst, snd in Hx, Hy; nra.
Qed.

Lemma sample_no_foreign_twin_aware :
  no_foreign_vertex_twin_aware sample_D.
Proof.
  unfold no_foreign_vertex_twin_aware, sample_D.
  intros e f He Hf Hne Hnt.
  simpl in He, Hf.
  destruct He as [Heq | He]; destruct Hf as [Heqf | Hf].
  - subst e f. exfalso. apply Hne. reflexivity.
  - subst e. apply sample_ring_vertices_not_on_dart. exact Hf.
  - subst f. apply sample_dart_vertices_not_on_ring. exact He.
  - destruct (rect_ring_no_foreign_vertex 10 10 12 12 (ltac:(lra)) (ltac:(lra))
                e f He Hf Hne) as [H1 H2].
    exact (conj H1 H2).
Qed.

Lemma sample_ring_edges_in_D :
  forall f, In f (ring_edges sample_ring) -> In f sample_D.
Proof.
  intros f Hin. simpl. right. exact Hin.
Qed.

Lemma sample_span :
  (py (snd descending_sample_dart) < sample_ylo /\ sample_yhi < py (fst descending_sample_dart)).
Proof.
  unfold sample_ylo, sample_yhi, descending_sample_dart, fst, snd, py. lra.
Qed.

Lemma edge_x_at_descending_sample (y : R) :
  edge_x_at descending_sample_dart y = (2 - y) / 2.
Proof.
  unfold descending_sample_dart, edge_x_at. cbn. field.
Qed.

Lemma corridor_px_sample_lt_delta :
  forall (delta y_sample : R),
    0 < delta < 1 ->
    sample_ylo <= y_sample <= sample_yhi ->
    px (corridor descending_sample_dart delta y_sample) < 1.
Proof.
  intros delta y_sample [Hdp Hdt] [Hylo Hyhi].
  unfold corridor. cbn [px].
  rewrite edge_x_at_descending_sample.
  unfold sample_ylo, sample_yhi in Hylo, Hyhi.
  assert (Hmax : (2 - y_sample) / 2 <= 199 / 200) by nra.
  nra.
Qed.

Lemma sample_clearance_delta :
  forall (delta y_sample : R),
    0 < delta < 1 ->
    sample_ylo <= y_sample <= sample_yhi ->
    ~ ring_image sample_ring
         (corridor descending_sample_dart delta y_sample).
Proof.
  intros delta y_sample Hdelta Hy Himg.
  destruct Himg as [f [s [Hin [[Hs1 Hs2] [Hx Hpy]]]]].
  pose proof (corridor_px_sample_lt_delta delta y_sample Hdelta Hy) as Hclt.
  pose proof (sample_ring_edge_px_ge f s Hin (conj Hs1 Hs2)) as Hcge.
  unfold corridor in Hclt, Hx. cbn [px] in Hclt, Hx.
  rewrite edge_x_at_descending_sample in Hclt, Hx.
  lra.
Qed.

Lemma sample_delta0_pack :
  exists delta0, 0 < delta0 /\
    sample_ef < corridor_safe_half delta0 /\
    forall delta, 0 < delta < delta0 ->
      forall y, sample_ylo <= y <= sample_yhi ->
        ~ ring_image sample_ring (corridor descending_sample_dart delta y).
Proof.
  exists 1. split; [lra | ].
  split.
  - unfold sample_ef, corridor_safe_half. field_simplify. lra.
  - intros delta Hdelta y Hy.
    exact (sample_clearance_delta delta y Hdelta Hy).
Qed.

Lemma sample_h_base_eq :
  sample_h_base =
  bridge_height_base descending_sample_dart sample_rho
    (corner_delta_for_ef_west descending_sample_dart sample_ef).
Proof.
  unfold sample_h_base, sample_rho, sample_ef, bridge_height_base,
         descending_sample_dart, corner_delta_for_ef_west.
  cbn. field_simplify. lra.
Qed.

Lemma sample_h_base_le_my : sample_h_base <= sample_my.
Proof. unfold sample_h_base, sample_my. lra. Qed.

Lemma sample_h_tip_eq :
  sample_h_tip =
  bridge_height_tip descending_sample_dart sample_rho
    (corner_delta_for_ef_west descending_sample_dart sample_ef).
Proof.
  unfold sample_h_tip, sample_rho, sample_ef, bridge_height_tip,
         descending_sample_dart, corner_delta_for_ef_west.
  cbn. field_simplify. lra.
Qed.

Lemma sample_my_le_h_tip : sample_my <= sample_h_tip.
Proof. unfold sample_my, sample_h_tip. lra. Qed.

Lemma sample_h_tip_le_yhi : sample_h_tip <= sample_yhi.
Proof. unfold sample_h_tip, sample_yhi. lra. Qed.

Lemma sample_ef_lt_threshold_third :
  sample_ef < corridor_safe_threshold 1 / 3.
Proof.
  unfold sample_ef, corridor_safe_threshold. field_simplify. lra.
Qed.

Lemma sample_straddle_chord_clear :
  forall t, 0 <= t <= 1 ->
    ring_complement sample_ring
      (mkPoint (edge_x_at descending_sample_dart sample_my - sample_ef
                  + t * (2 * sample_ef)) sample_my).
Proof.
  intros t [Ht0 Ht1] Himg.
  destruct Himg as [f [s [Hin [[Hs1 Hs2] [Hx Hpy]]]]].
  pose proof (sample_ring_edge_px_ge f s Hin (conj Hs1 Hs2)) as Hpx_ge.
  rewrite edge_x_at_descending_sample in Hx.
  unfold sample_my, sample_ef in Hx.
  assert (Hpx_lt : (2 - 24 / 25) / 2 - 1 / 10 + t * (2 / 10) < 10) by nra.
  cbn [px] in Hx, Hpx_ge.
  lra.
Qed.

Lemma corridor_px_sample_lt :
  forall y_sample, sample_h_base <= y_sample <= sample_my ->
    px (corridor descending_sample_dart sample_ef y_sample) < 1.
Proof.
  intros y_sample [Hylo Hyhi].
  unfold corridor. cbn [px].
  rewrite edge_x_at_descending_sample.
  unfold sample_ef, sample_h_base, sample_my in *.
  assert (Hle : (2 - y_sample) / 2 - 1 / 10 <= 21 / 50) by nra.
  lra.
Qed.

Lemma sample_clearance :
  forall y_sample, sample_h_base <= y_sample <= sample_my ->
    ~ ring_image sample_ring
         (corridor descending_sample_dart sample_ef y_sample).
Proof.
  intros y_sample Hy Himg.
  destruct Himg as [f [s [Hin [[Hs1 Hs2] [Hx Hpy]]]]].
  pose proof (corridor_px_sample_lt y_sample Hy) as Hclt.
  pose proof (sample_ring_edge_px_ge f s Hin (conj Hs1 Hs2)) as Hcge.
  unfold corridor in Hclt, Hx. cbn [px] in Hclt, Hx.
  rewrite edge_x_at_descending_sample in Hclt, Hx.
  unfold sample_ef in Hclt, Hx.
  lra.
Qed.

(* Headline west transport on the concrete sample: corner -> straddle west. *)
Lemma descending_sample_west_transport :
  connected_in_complement_cont sample_ring
    (point_at (dbase descending_sample_dart)
       (corner_sample_out (ddir descending_sample_dart) sample_rho
          (corner_delta_for_ef_west descending_sample_dart sample_ef)))
    (mkPoint (edge_x_at descending_sample_dart sample_my - sample_ef) sample_my).
Proof.
  apply (along_dart_base_to_straddle_west sample_ring descending_sample_dart
           sample_rho sample_ef sample_my sample_h_base).
  - exact descending_sample_dart_vy.
  - exact sample_h_base_eq.
  - exact sample_h_base_le_my.
  - exact sample_clearance.
Qed.

(* Packaged west transport via `along_dart_base_to_straddle_west_clear` and
   `corridor_ef_inherits_clearance` on the uniform delta0 window. *)
Lemma descending_sample_west_transport_clear :
  connected_in_complement_cont sample_ring
    (point_at (dbase descending_sample_dart)
       (corner_sample_out (ddir descending_sample_dart) sample_rho
          (corner_delta_for_ef_west descending_sample_dart sample_ef)))
    (mkPoint (edge_x_at descending_sample_dart sample_my - sample_ef) sample_my).
Proof.
  apply (along_dart_base_to_straddle_west_clear sample_D sample_ring
           descending_sample_dart sample_rho sample_ef sample_my sample_h_base
           sample_ylo sample_yhi).
  - exact sample_ring_taut.
  - exact sample_pairwise_twin_aware.
  - exact sample_no_foreign_twin_aware.
  - simpl. left. reflexivity.
  - exact sample_ring_edges_in_D.
  - right. exact sample_span.
  - unfold sample_ylo, sample_yhi. lra.
  - exact descending_sample_dart_vy.
  - exact sample_h_base_eq.
  - repeat split; unfold sample_ylo, sample_h_base, sample_my, sample_yhi; lra.
  - unfold sample_ef. lra.
  - destruct sample_delta0_pack as [delta0 [Hd0 [Hhalf Hclear]]].
    exists delta0. eauto.
Qed.

Lemma sample_dart_not_on_ring :
  ~ In descending_sample_dart (ring_edges sample_ring).
Proof.
  intro Hin.
  unfold sample_ring, descending_sample_dart in Hin.
  rewrite ring_edges_rect in Hin.
  cbn [In] in Hin.
  destruct Hin as [He | [He | [He | [He | []]]]].
  all: injection He; intros; lra.
Qed.

(* Foreign-dart application: both exact `face_transport_premise` straddle
   targets at `sample_my` (dart off-ring, so east chord is valid). *)
Lemma descending_sample_corridor_safe_for_ef :
  let p_west :=
    mkPoint (edge_x_at descending_sample_dart sample_my - sample_ef) sample_my in
  let p_east :=
    mkPoint (edge_x_at descending_sample_dart sample_my + sample_ef) sample_my in
  connected_in_complement_cont sample_ring
    (corner_sample_left descending_sample_dart sample_rho sample_ef) p_west /\
  connected_in_complement_cont sample_ring
    (corner_sample_right descending_sample_dart sample_rho sample_ef) p_west /\
  connected_in_complement_cont sample_ring
    (corner_sample_right descending_sample_dart sample_rho sample_ef) p_east.
Proof.
  assert (Hwest :
    connected_in_complement_cont sample_ring
      (corner_sample_left descending_sample_dart sample_rho sample_ef)
      (mkPoint (edge_x_at descending_sample_dart sample_my - sample_ef) sample_my) /\
    connected_in_complement_cont sample_ring
      (corner_sample_right descending_sample_dart sample_rho sample_ef)
      (mkPoint (edge_x_at descending_sample_dart sample_my - sample_ef) sample_my)).
  { apply (corridor_safe_for_ef_west sample_D sample_ring descending_sample_dart
              sample_rho sample_ef sample_my sample_h_base sample_h_tip
              sample_ylo sample_yhi 1).
    - exact sample_ring_taut.
    - exact sample_pairwise_twin_aware.
    - exact sample_no_foreign_twin_aware.
    - simpl. left. reflexivity.
    - exact sample_ring_edges_in_D.
    - right. exact sample_span.
    - unfold sample_ylo, sample_yhi. lra.
    - exact descending_sample_dart_vy.
    - exact sample_h_base_eq.
    - exact sample_h_tip_eq.
    - repeat split; unfold sample_ylo, sample_h_base, sample_my, sample_h_tip, sample_yhi; lra.
    - lra.
    - unfold sample_ef. lra.
    - exact sample_ef_lt_threshold_third.
    - intros delta Hdelta y Hy.
      exact (sample_clearance_delta delta y Hdelta Hy). }
  destruct Hwest as [Hleft Hright].
  apply (foreign_dart_corridor_safe_for_ef sample_ring descending_sample_dart
           sample_rho sample_ef sample_my Hleft Hright).
  - exact sample_dart_not_on_ring.
  - exact sample_straddle_chord_clear.
Qed.

(* -------------------------------------------------------------------------- *)
(* Axiom audit.  Pure vector/field algebra; allowlist axioms only.             *)
(* -------------------------------------------------------------------------- *)

Print Assumptions corner_sample_out_on_corridor_west.
Print Assumptions corner_sample_out_on_corridor_east.
Print Assumptions corner_sample_in_on_corridor_west.
Print Assumptions corner_sample_in_on_corridor_east.
Print Assumptions corridor_absorbs_ef.
Print Assumptions corridor_ef_inherits_clearance.
Print Assumptions straddle_west_eq_corridor.
Print Assumptions handoff_chord_connected_convex.
Print Assumptions handoff_base_to_corridor_west_convex.
Print Assumptions handoff_base_bridge_connected_west.
Print Assumptions along_dart_base_to_straddle_west.
Print Assumptions along_dart_base_to_straddle_west_clear.
Print Assumptions along_dart_base_to_straddle_east_clear.
Print Assumptions along_dart_tip_to_straddle_west_clear.
Print Assumptions corridor_safe_for_ef.
Print Assumptions corridor_safe_for_ef_west.
Print Assumptions corridor_safe_for_ef_east.
Print Assumptions foreign_dart_corridor_safe_for_ef.
Print Assumptions face_transport_premise_ring_dart_west_straddle_connected.
Print Assumptions face_transport_premise_ring_dart_east_straddle_connected.
Print Assumptions face_transport_premise_ring_dart_straddle_pair_connected.
Print Assumptions face_transport_premise_ring_dart_west_straddle_in_complement.
Print Assumptions face_transport_premise_ring_dart_east_straddle_in_complement.
Print Assumptions face_transport_premise_ring_dart_straddle_pair_in_complement.
Print Assumptions face_transport_premise_foreign_straddle_pair_in_complement.
Print Assumptions face_transport_west_straddle_headline_connected.
Print Assumptions face_transport_east_straddle_headline_connected.
Print Assumptions descending_sample_corridor_safe_for_ef.
Print Assumptions descending_sample_west_transport_clear.
Print Assumptions face_transport_straddle_pair_eq.
Print Assumptions along_dart_base_to_straddle_east.

(* ==========================================================================
   FanCorner.v

   [H-bridge attack, C-3d step 2b] The ON-RING GENERAL-FAN corner
   connector: at a cycle-ring vertex, the corner polyline between an
   arriving face-walk wall and its `next` successor stays in the ring
   complement even when the walls are NOT the incident ring edges.

   This closes rung C-3d.  The two-dart connector (`CornerConnector.v`)
   handled degree-2 vertices, where the sector walls ARE the two incident
   ring edges and the wall-ray exclusions dispose of them.  At a general
   vertex the face walk turns between arbitrary E-darts of the outgoing
   fan, and the incident ring edges sit SOMEWHERE in the fan.  The
   assembly:

     - every fan germ is UNCERTIFIED in the open next-gap sector
       (`fan_gap_uncertified`): the two walls fail the strict certificate
       outright (`in_open_sector_not_wall1`/`_2`, since
       `vcross u u = 0`), and every other fan direction is excluded by
       `FanGapSector.fan_next_gap_empty_sector`;
     - an incident ring edge whose germ direction is uncertified never
       meets a certified offset (`sector_point_off_edge_in`/`_out`): its
       on-edge witnesses are closed-ray points in the germ direction,
       killed by `CornerGapKit.sector_off_foreign_ray`;
     - non-incident ring edges are cleared by the pruned ball
       (`CornerConnector.vertex_pruned_clearance`) exactly as in the
       two-dart case (`fan_corner_offset_in_complement`);
     - the polyline itself is unchanged: the reflex three-hop /
       convex single-chord sector paths with the `CornerSamples`
       certificates and sup-norm bounds
       (`fan_corner_connected_reflex`/`_convex`), parameters produced
       once by `corner_params_exist` (`fan_corner_connected`);
     - `fan_corner_connected_at_vertex` composes everything at an
       actual fan: walls `ddir x`, `ddir (next F x)`, germ exclusion
       discharged from `fan_ok`, gap nondegeneracy from the fan's
       pairwise nonparallelism.

   Pure assembly of banked pieces; no `Admitted` / `Axiom` / `Parameter`;
   allowlist axioms only.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
   ========================================================================== *)

From Stdlib Require Import Reals Lra List.
From NTS.Proofs Require Import Distance Overlay OverlayGraph Vec Azimuth
                               Direction Dart DartAngularOrder DartNext
                               DartNextSpec MinDegreeCore EdgeConnectivity
                               PointInRingTangents JordanCurveSeam JCT
                               JCTHugStep RingClearance SectorPath
                               CornerSamples CornerConnector FanGapSector
                               CornerGapKit.

Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  The walls themselves are never strictly inside the sector.              *)
(* -------------------------------------------------------------------------- *)

Lemma in_open_sector_not_wall1 :
  forall u1 u2, ~ in_open_sector u1 u2 u1.
Proof.
  intros u1 u2 Hin.
  destruct Hin as [[Hc [H1 _]] | [Hc [H1 | H2]]].
  - rewrite vcross_self in H1. lra.
  - rewrite vcross_self in H1. lra.
  - lra.
Qed.

Lemma in_open_sector_not_wall2 :
  forall u1 u2, ~ in_open_sector u1 u2 u2.
Proof.
  intros u1 u2 Hin.
  destruct Hin as [[Hc [_ H2]] | [Hc [H1 | H2]]].
  - rewrite vcross_self in H2. lra.
  - lra.
  - rewrite vcross_self in H2. lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  NO fan germ is certified in the next-gap sector -- walls included.      *)
(* -------------------------------------------------------------------------- *)

Theorem fan_gap_uncertified :
  forall (F : list Dart) (x g : Dart),
    fan_ok F -> In x F -> In g F ->
    ~ in_open_sector (ddir x) (ddir (next F x)) (ddir g).
Proof.
  intros F x g HF Hx Hg.
  destruct (edge_eq_dec g x) as [-> | Hgx].
  - apply in_open_sector_not_wall1.
  - destruct (edge_eq_dec g (next F x)) as [-> | Hgn].
    + apply in_open_sector_not_wall2.
    + apply fan_next_gap_empty_sector; assumption.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Certified offsets are off any incident edge with uncertified germ.      *)
(* -------------------------------------------------------------------------- *)

(* An incident edge stored `(a, v)` has germ direction `point_diff a v`
   at `v`; its on-edge witnesses are closed-ray points in that direction,
   so an uncertified germ keeps every certified offset off the edge. *)
Lemma sector_point_off_edge_in :
  forall (u1 u2 : Vec) (a v : Point) (w : Vec),
    in_open_sector u1 u2 w ->
    ~ in_open_sector u1 u2 (point_diff a v) ->
    ~ on_edge (a, v) (point_at v w).
Proof.
  intros u1 u2 a v w Hsect Hm [s [Hs [Hx Hy]]].
  cbn [fst snd] in Hx, Hy.
  apply (sector_off_foreign_ray u1 u2 w (point_diff a v) Hsect Hm
           (1 - s) ltac:(lra)).
  unfold point_at in Hx, Hy. cbn in Hx, Hy.
  destruct w as [wx wy]. cbn in Hx, Hy.
  unfold vscale, point_diff. cbn. f_equal; nra.
Qed.

(* Mirror for an incident edge stored `(v, b)`: germ direction
   `point_diff b v`. *)
Lemma sector_point_off_edge_out :
  forall (u1 u2 : Vec) (v b : Point) (w : Vec),
    in_open_sector u1 u2 w ->
    ~ in_open_sector u1 u2 (point_diff b v) ->
    ~ on_edge (v, b) (point_at v w).
Proof.
  intros u1 u2 v b w Hsect Hm [s [Hs [Hx Hy]]].
  cbn [fst snd] in Hx, Hy.
  apply (sector_off_foreign_ray u1 u2 w (point_diff b v) Hsect Hm
           s ltac:(lra)).
  unfold point_at in Hx, Hy. cbn in Hx, Hy.
  destruct w as [wx wy]. cbn in Hx, Hy.
  unfold vscale, point_diff. cbn. f_equal; nra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Certificate + germ exclusion + ball bounds => ring complement.          *)
(* -------------------------------------------------------------------------- *)

(* The general-wall analogue of `corner_offset_in_complement`: the two
   incident ring edges fall to §3 (their germs are uncertified -- at the
   fan, by §2), everything else to the pruned clearance ball. *)
Lemma fan_corner_offset_in_complement :
  forall (r : Ring) (v a b : Point) (u1 u2 : Vec) (eps : R) (w : Vec),
    (forall q : Point,
       Rabs (px q - px v) < eps -> Rabs (py q - py v) < eps ->
       forall f, In f (ring_edges r) -> f <> (a, v) -> f <> (v, b) ->
         ~ on_edge f q) ->
    ~ in_open_sector u1 u2 (point_diff a v) ->
    ~ in_open_sector u1 u2 (point_diff b v) ->
    in_open_sector u1 u2 w ->
    Rabs (vx w) < eps -> Rabs (vy w) < eps ->
    ring_complement r (point_at v w).
Proof.
  intros r v a b u1 u2 eps w Hball Hma Hmb Hsect Hbx Hby
         [f [s [Hf [Hs [Hx Hy]]]]].
  assert (Hon : on_edge f (point_at v w))
    by (exists s; split; [ exact Hs | split; [ exact Hx | exact Hy ] ]).
  destruct (edge_eq_dec f (a, v)) as [-> | Hne1].
  - exact (sector_point_off_edge_in u1 u2 a v w Hsect Hma Hon).
  - destruct (edge_eq_dec f (v, b)) as [-> | Hne2].
    + exact (sector_point_off_edge_out u1 u2 v b w Hsect Hmb Hon).
    + assert (HBX : Rabs (px (point_at v w) - px v) < eps)
        by (replace (px (point_at v w) - px v) with (vx w)
              by (unfold point_at; cbn; ring); exact Hbx).
      assert (HBY : Rabs (py (point_at v w) - py v) < eps)
        by (replace (py (point_at v w) - py v) with (vy w)
              by (unfold point_at; cbn; ring); exact Hby).
      exact (Hball (point_at v w) HBX HBY f Hf Hne1 Hne2 Hon).
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  The general-wall corner connector, reflex case.                         *)
(* -------------------------------------------------------------------------- *)

Theorem fan_corner_connected_reflex :
  forall (r : Ring) (v a b : Point) (u1 u2 : Vec)
         (eps rho delta sigma : R),
    (forall q : Point,
       Rabs (px q - px v) < eps -> Rabs (py q - py v) < eps ->
       forall f, In f (ring_edges r) -> f <> (a, v) -> f <> (v, b) ->
         ~ on_edge f q) ->
    ~ in_open_sector u1 u2 (point_diff a v) ->
    ~ in_open_sector u1 u2 (point_diff b v) ->
    vcross u1 u2 < 0 ->
    0 < rho -> 0 < delta -> 0 < sigma ->
    rho * Rabs (vx u1) + delta * Rabs (vy u1) < eps ->
    rho * Rabs (vy u1) + delta * Rabs (vx u1) < eps ->
    rho * Rabs (vx u2) + delta * Rabs (vy u2) < eps ->
    rho * Rabs (vy u2) + delta * Rabs (vx u2) < eps ->
    sigma * Rabs (vx u1) < eps ->
    sigma * Rabs (vy u1) < eps ->
    connected_in_complement_cont r
      (point_at v (corner_sample_in u1 rho delta))
      (point_at v (corner_sample_out u2 rho delta)).
Proof.
  intros r v a b u1 u2 eps rho delta sigma Hball Hma Hmb Hc Hr Hd Hs
         Hb_in_x Hb_in_y Hb_out_x Hb_out_y Hb_s_x Hb_s_y.
  assert (Hu1 : u1 <> vzero)
    by (intro Hz; rewrite Hz, vcross_zero_l in Hc; lra).
  assert (Hu2 : u2 <> vzero)
    by (intro Hz; rewrite Hz, vcross_zero_r in Hc; lra).
  assert (Hcert1 : 0 < vcross u1 (corner_sample_in u1 rho delta))
    by (apply corner_sample_in_cert; assumption).
  assert (Hcert2 : 0 < vcross (corner_sample_out u2 rho delta) u2)
    by (apply corner_sample_out_cert; assumption).
  pose proof (corner_sample_in_bound u1 rho delta ltac:(lra) ltac:(lra))
    as [HinBx HinBy].
  pose proof (corner_sample_out_bound u2 rho delta ltac:(lra) ltac:(lra))
    as [HoutBx HoutBy].
  pose proof (hop_perpL_bound u1 sigma ltac:(lra)) as [HpBx HpBy].
  pose proof (hop_neg_bound u1 sigma ltac:(lra)) as [HnBx HnBy].
  eapply connected_in_complement_cont_trans.
  { (* hop 1: sample_in -> sigma * perpL u1 *)
    apply hop_connected. intros t Ht.
    apply (fan_corner_offset_in_complement r v a b u1 u2 eps);
      [ exact Hball | exact Hma | exact Hmb | | | ].
    - exact (sector_path_reflex_hop1_scaled u1 u2 _ sigma Hc Hu1 Hs Hcert1 t Ht).
    - eapply Rle_lt_trans; [ apply vaffine_bound_x; exact Ht | ].
      apply Rmax_lub_lt;
        [ eapply Rle_lt_trans; [ exact HinBx | exact Hb_in_x ]
        | eapply Rle_lt_trans; [ exact HpBx | exact Hb_s_y ] ].
    - eapply Rle_lt_trans; [ apply vaffine_bound_y; exact Ht | ].
      apply Rmax_lub_lt;
        [ eapply Rle_lt_trans; [ exact HinBy | exact Hb_in_y ]
        | eapply Rle_lt_trans; [ exact HpBy | exact Hb_s_x ] ]. }
  eapply connected_in_complement_cont_trans.
  { (* hop 2: sigma * perpL u1 -> sigma * (- u1) *)
    apply hop_connected. intros t Ht.
    apply (fan_corner_offset_in_complement r v a b u1 u2 eps);
      [ exact Hball | exact Hma | exact Hmb | | | ].
    - exact (sector_path_reflex_hop2_scaled u1 u2 sigma Hc Hu1 Hs t Ht).
    - eapply Rle_lt_trans; [ apply vaffine_bound_x; exact Ht | ].
      apply Rmax_lub_lt;
        [ eapply Rle_lt_trans; [ exact HpBx | exact Hb_s_y ]
        | eapply Rle_lt_trans; [ exact HnBx | exact Hb_s_x ] ].
    - eapply Rle_lt_trans; [ apply vaffine_bound_y; exact Ht | ].
      apply Rmax_lub_lt;
        [ eapply Rle_lt_trans; [ exact HpBy | exact Hb_s_x ]
        | eapply Rle_lt_trans; [ exact HnBy | exact Hb_s_y ] ]. }
  (* hop 3: sigma * (- u1) -> sample_out *)
  apply hop_connected. intros t Ht.
  apply (fan_corner_offset_in_complement r v a b u1 u2 eps);
    [ exact Hball | exact Hma | exact Hmb | | | ].
  - exact (sector_path_reflex_hop3_scaled u1 u2 _ sigma Hc Hs Hcert2 t Ht).
  - eapply Rle_lt_trans; [ apply vaffine_bound_x; exact Ht | ].
    apply Rmax_lub_lt;
      [ eapply Rle_lt_trans; [ exact HnBx | exact Hb_s_x ]
      | eapply Rle_lt_trans; [ exact HoutBx | exact Hb_out_x ] ].
  - eapply Rle_lt_trans; [ apply vaffine_bound_y; exact Ht | ].
    apply Rmax_lub_lt;
      [ eapply Rle_lt_trans; [ exact HnBy | exact Hb_s_y ]
      | eapply Rle_lt_trans; [ exact HoutBy | exact Hb_out_y ] ].
Qed.

(* -------------------------------------------------------------------------- *)
(* §6  The general-wall corner connector, convex case.                         *)
(* -------------------------------------------------------------------------- *)

Theorem fan_corner_connected_convex :
  forall (r : Ring) (v a b : Point) (u1 u2 : Vec) (eps rho delta : R),
    (forall q : Point,
       Rabs (px q - px v) < eps -> Rabs (py q - py v) < eps ->
       forall f, In f (ring_edges r) -> f <> (a, v) -> f <> (v, b) ->
         ~ on_edge f q) ->
    ~ in_open_sector u1 u2 (point_diff a v) ->
    ~ in_open_sector u1 u2 (point_diff b v) ->
    0 < vcross u1 u2 ->
    0 < rho -> 0 < delta ->
    delta * Rabs (vcross (vperpL u1) u2) < rho * vcross u1 u2 ->
    delta * Rabs (vcross u1 (vperpL u2)) < rho * vcross u1 u2 ->
    rho * Rabs (vx u1) + delta * Rabs (vy u1) < eps ->
    rho * Rabs (vy u1) + delta * Rabs (vx u1) < eps ->
    rho * Rabs (vx u2) + delta * Rabs (vy u2) < eps ->
    rho * Rabs (vy u2) + delta * Rabs (vx u2) < eps ->
    connected_in_complement_cont r
      (point_at v (corner_sample_in u1 rho delta))
      (point_at v (corner_sample_out u2 rho delta)).
Proof.
  intros r v a b u1 u2 eps rho delta Hball Hma Hmb Hc Hr Hd
         Hsmall_in Hsmall_out Hb_in_x Hb_in_y Hb_out_x Hb_out_y.
  assert (Hu1 : u1 <> vzero)
    by (intro Hz; rewrite Hz, vcross_zero_l in Hc; lra).
  assert (Hu2 : u2 <> vzero)
    by (intro Hz; rewrite Hz, vcross_zero_r in Hc; lra).
  assert (H11 : 0 < vcross u1 (corner_sample_in u1 rho delta))
    by (apply corner_sample_in_cert; assumption).
  assert (H12 : 0 < vcross (corner_sample_in u1 rho delta) u2)
    by (apply corner_sample_in_cert_far; try assumption; lra).
  assert (H21 : 0 < vcross u1 (corner_sample_out u2 rho delta))
    by (apply corner_sample_out_cert_far; try assumption; lra).
  assert (H22 : 0 < vcross (corner_sample_out u2 rho delta) u2)
    by (apply corner_sample_out_cert; assumption).
  pose proof (corner_sample_in_bound u1 rho delta ltac:(lra) ltac:(lra))
    as [HinBx HinBy].
  pose proof (corner_sample_out_bound u2 rho delta ltac:(lra) ltac:(lra))
    as [HoutBx HoutBy].
  apply hop_connected. intros t Ht.
  apply (fan_corner_offset_in_complement r v a b u1 u2 eps);
    [ exact Hball | exact Hma | exact Hmb | | | ].
  - exact (sector_path_convex u1 u2 _ _ Hc H11 H12 H21 H22 t Ht).
  - eapply Rle_lt_trans; [ apply vaffine_bound_x; exact Ht | ].
    apply Rmax_lub_lt;
      [ eapply Rle_lt_trans; [ exact HinBx | exact Hb_in_x ]
      | eapply Rle_lt_trans; [ exact HoutBx | exact Hb_out_x ] ].
  - eapply Rle_lt_trans; [ apply vaffine_bound_y; exact Ht | ].
    apply Rmax_lub_lt;
      [ eapply Rle_lt_trans; [ exact HinBy | exact Hb_in_y ]
      | eapply Rle_lt_trans; [ exact HoutBy | exact Hb_out_y ] ].
Qed.

(* -------------------------------------------------------------------------- *)
(* §7  Self-contained wrapper: parameters exist for any nondegenerate gap.     *)
(* -------------------------------------------------------------------------- *)

(* The reflex/convex split is internal: `corner_params_exist` sizes the
   parameters against the pruned clearance ball, and in the convex case
   delta additionally shrinks below the far-wall smallness threshold. *)
Theorem fan_corner_connected :
  forall (r : Ring) (v a b : Point) (u1 u2 : Vec),
    no_horizontal_edges r ->
    (forall f, In f (ring_edges r) -> f <> (a, v) -> f <> (v, b) ->
       ~ on_edge f v) ->
    ~ in_open_sector u1 u2 (point_diff a v) ->
    ~ in_open_sector u1 u2 (point_diff b v) ->
    vcross u1 u2 <> 0 ->
    exists rho delta : R, 0 < rho /\ 0 < delta /\
      connected_in_complement_cont r
        (point_at v (corner_sample_in u1 rho delta))
        (point_at v (corner_sample_out u2 rho delta)).
Proof.
  intros r v a b u1 u2 Hnoh Hoffv Hma Hmb Hcne.
  destruct (vertex_pruned_clearance r v (a, v) (v, b) Hnoh Hoffv)
    as [eps [Heps Hball]].
  destruct (corner_params_exist u1 u2 eps Heps)
    as [rho [delta0 [sigma [Hr [Hd0 [Hs [B1 [B2 [B3 [B4 [B5 B6]]]]]]]]]]].
  destruct (Rdichotomy _ _ Hcne) as [Hneg | Hgt].
  - (* reflex gap *)
    exists rho, delta0. split; [ exact Hr | split; [ exact Hd0 | ] ].
    exact (fan_corner_connected_reflex r v a b u1 u2 eps rho delta0 sigma
             Hball Hma Hmb Hneg Hr Hd0 Hs B1 B2 B3 B4 B5 B6).
  - (* convex gap: shrink delta below the far-wall threshold *)
    assert (Hpos : 0 < vcross u1 u2) by lra.
    set (C1 := Rabs (vcross (vperpL u1) u2)).
    set (C2 := Rabs (vcross u1 (vperpL u2))).
    assert (HC1 : 0 <= C1) by apply Rabs_pos.
    assert (HC2 : 0 <= C2) by apply Rabs_pos.
    set (delta := Rmin delta0 (rho * vcross u1 u2 / (C1 + C2 + 1))).
    assert (Hdle : delta <= delta0) by apply Rmin_l.
    assert (Hdsm : delta <= rho * vcross u1 u2 / (C1 + C2 + 1)) by apply Rmin_r.
    assert (Hdiv : 0 < rho * vcross u1 u2 / (C1 + C2 + 1))
      by (apply Rdiv_lt_0_compat; nra).
    assert (Hd : 0 < delta) by (unfold delta; apply Rmin_glb_lt; lra).
    assert (Hdiveq : rho * vcross u1 u2 / (C1 + C2 + 1) * (C1 + C2 + 1)
                     = rho * vcross u1 u2)
      by (field; lra).
    exists rho, delta. split; [ exact Hr | split; [ exact Hd | ] ].
    apply (fan_corner_connected_convex r v a b u1 u2 eps rho delta
             Hball Hma Hmb Hpos Hr Hd).
    + (* delta * C1 < rho * gap *)
      fold C1.
      assert (Hstep : delta * (C1 + C2 + 1) <= rho * vcross u1 u2) by nra.
      nra.
    + fold C2.
      assert (Hstep : delta * (C1 + C2 + 1) <= rho * vcross u1 u2) by nra.
      nra.
    + (* the four eps-bounds are monotone in delta *)
      pose proof (Rabs_pos (vy u1)). nra.
    + pose proof (Rabs_pos (vx u1)). nra.
    + pose proof (Rabs_pos (vy u2)). nra.
    + pose proof (Rabs_pos (vx u2)). nra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §8  Headline: the full-fan corner at a cycle vertex.                        *)
(* -------------------------------------------------------------------------- *)

(* At a fan vertex `v` whose incident ring edges are `(a, v)` and
   `(v, b)` (their germ-darts `(v, a)`, `(v, b)` are fan members), the
   corner polyline from any fan wall `x` to its face-walk successor
   `next F x` connects inside the ring complement.  Germ exclusion for
   the ring edges comes from §2; nondegeneracy of the gap from the fan's
   pairwise nonparallelism.  The two remaining vertex-side obligations
   (the walls differ; the vertex is off all non-incident ring edges) are
   the cycle-ring caller's, from min-degree-2 and the twin-aware
   no-T-junction guard respectively. *)
Theorem fan_corner_connected_at_vertex :
  forall (r : Ring) (F : list Dart) (x : Dart) (v a b : Point),
    fan_ok F -> In x F -> x <> next F x ->
    In ((v, a) : Dart) F -> In ((v, b) : Dart) F ->
    no_horizontal_edges r ->
    (forall f, In f (ring_edges r) -> f <> (a, v) -> f <> (v, b) ->
       ~ on_edge f v) ->
    exists rho delta : R, 0 < rho /\ 0 < delta /\
      connected_in_complement_cont r
        (point_at v (corner_sample_in (ddir x) rho delta))
        (point_at v (corner_sample_out (ddir (next F x)) rho delta)).
Proof.
  intros r F x v a b HF Hx Hxn Hva Hvb Hnoh Hoffv.
  apply (fan_corner_connected r v a b); try assumption.
  - change (point_diff a v) with (ddir ((v, a) : Dart)).
    apply (fan_gap_uncertified F x (v, a)); assumption.
  - change (point_diff b v) with (ddir ((v, b) : Dart)).
    apply (fan_gap_uncertified F x (v, b)); assumption.
  - apply cross_nonzero.
    destruct HF as [_ Hpair].
    apply Hpair; [ exact Hx | apply next_in; exact Hx | exact Hxn ].
Qed.

(* -------------------------------------------------------------------------- *)
(* Axiom audit.  Assembly wiring; allowlist axioms only.                       *)
(* -------------------------------------------------------------------------- *)

Print Assumptions fan_gap_uncertified.
Print Assumptions fan_corner_connected.
Print Assumptions fan_corner_connected_at_vertex.

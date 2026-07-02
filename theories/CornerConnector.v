(* ==========================================================================
   CornerConnector.v

   [H-bridge attack, rung C-3b, step 4] The two-dart corner connector,
   REFLEX case: at a degree-2 ring vertex, the right-of-arriving-dart
   sample connects to the right-of-departing-dart sample INSIDE the ring
   complement, along the scaled three-hop sector polyline.

   Assembly of the previously banked pieces:
     - the sector kernel (`SectorPath.v`): certified points avoid both
       incident wall RAYS, and the scaled hops (`CornerSamples.v`) keep
       every polyline point certified;
     - `sector_point_off_incident_in`/`_out` (here): an `on_edge` witness
       for an incident ring edge IS a wall-ray point, so certified points
       are off both incident edges -- pure coordinate/vector conversion;
     - `vertex_pruned_clearance` (here): `RingClearance.off_edges_ball_list`
       on the ring edges MINUS the two incident ones gives a ball around
       the vertex clear of every other edge (the vertex is off those by
       tautness/no-T-junction, supplied as a hypothesis the cycle-ring
       caller discharges);
     - `corner_offset_in_complement` (here): certificate + ball bounds =>
       `ring_complement`;
     - `hop_connected` (here): a straight segment whose points are all in
       the complement is a `connected_in_complement_cont` witness;
     - headline `two_dart_corner_connected_reflex`: chain the three hops
       with `connected_in_complement_cont_trans`.  Parameter sizing is
       CALLER-SIDE: six explicit linear bounds place all four polyline
       anchors inside the clearance ball (choosing rho, delta, sigma small
       enough is trivial arithmetic for the caller given `eps > 0`).

   The CONVEX-gap mirror (single chord, far-wall certificates under the
   explicit smallness inequalities) is the next step; then the general fan
   and the orbit-length transport.

   Pure-R + list/vector conversion; no `Admitted` / `Axiom` / `Parameter`;
   allowlist axioms only.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
   ========================================================================== *)

From Stdlib Require Import Reals Lra List.
From NTS.Proofs Require Import Distance Overlay OverlayGraph Vec Azimuth
                               EdgeConnectivity PointInRingTangents
                               JordanCurveSeam JCT JCTHugStep
                               RingClearance SectorPath CornerSamples.

Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  Points from vertex-relative offsets.                                    *)
(* -------------------------------------------------------------------------- *)

Definition point_at (v : Point) (w : Vec) : Point :=
  mkPoint (px v + vx w) (py v + vy w).

Lemma vcross_zero_l : forall u, vcross vzero u = 0.
Proof. intro u. unfold vcross, vzero. cbn. ring. Qed.

Lemma vcross_zero_r : forall u, vcross u vzero = 0.
Proof. intro u. unfold vcross, vzero. cbn. ring. Qed.

(* -------------------------------------------------------------------------- *)
(* §2  Certified offsets are off both INCIDENT edges.                          *)
(* -------------------------------------------------------------------------- *)

(* The arriving ring edge is stored `(a, v)`; an on-edge witness for the
   sample is exactly a wall-1-ray point, excluded by the certificate. *)
Lemma sector_point_off_incident_in :
  forall (a v b : Point) (w : Vec),
    in_open_sector (point_diff a v) (point_diff b v) w ->
    ~ on_edge (a, v) (point_at v w).
Proof.
  intros a v b w Hsect [s [Hs [Hx Hy]]].
  cbn [fst snd] in Hx, Hy.
  apply (in_open_sector_off_ray1 _ _ _ Hsect (1 - s) ltac:(lra)).
  unfold point_at in Hx, Hy. cbn in Hx, Hy.
  destruct w as [wx wy]. cbn in Hx, Hy.
  unfold vscale, point_diff. cbn. f_equal; nra.
Qed.

(* The departing ring edge is stored `(v, b)`; its on-edge witnesses are
   wall-2-ray points. *)
Lemma sector_point_off_incident_out :
  forall (a v b : Point) (w : Vec),
    in_open_sector (point_diff a v) (point_diff b v) w ->
    ~ on_edge (v, b) (point_at v w).
Proof.
  intros a v b w Hsect [s [Hs [Hx Hy]]].
  cbn [fst snd] in Hx, Hy.
  apply (in_open_sector_off_ray2 _ _ _ Hsect s ltac:(lra)).
  unfold point_at in Hx, Hy. cbn in Hx, Hy.
  destruct w as [wx wy]. cbn in Hx, Hy.
  unfold vscale, point_diff. cbn. f_equal; nra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Vertex-local clearance for the NON-incident edges.                      *)
(* -------------------------------------------------------------------------- *)

Lemma vertex_pruned_clearance :
  forall (r : Ring) (v : Point) (e_in e_out : Edge),
    no_horizontal_edges r ->
    (forall f, In f (ring_edges r) -> f <> e_in -> f <> e_out ->
       ~ on_edge f v) ->
    exists eps, 0 < eps /\
      forall q : Point,
        Rabs (px q - px v) < eps -> Rabs (py q - py v) < eps ->
        forall f, In f (ring_edges r) -> f <> e_in -> f <> e_out ->
          ~ on_edge f q.
Proof.
  intros r v e_in e_out Hnoh Hoff.
  set (keep := fun f : Edge =>
                 if edge_eq_dec f e_in then false
                 else if edge_eq_dec f e_out then false else true).
  assert (Hes : forall f, In f (filter keep (ring_edges r)) <->
                  (In f (ring_edges r) /\ f <> e_in /\ f <> e_out)).
  { intro f. rewrite filter_In. unfold keep. split.
    - intros [Hf Hb]. split; [ exact Hf | ].
      destruct (edge_eq_dec f e_in); [ discriminate | ].
      destruct (edge_eq_dec f e_out); [ discriminate | ].
      split; assumption.
    - intros [Hf [H1 H2]]. split; [ exact Hf | ].
      destruct (edge_eq_dec f e_in); [ contradiction | ].
      destruct (edge_eq_dec f e_out); [ contradiction | reflexivity ]. }
  destruct (off_edges_ball_list (filter keep (ring_edges r)) v) as
    [eps [Heps Hball]].
  { intros f Hf. apply Hes in Hf. destruct Hf as [Hf [H1 H2]].
    apply off_edge_ball; [ exact (Hnoh f Hf) | exact (Hoff f Hf H1 H2) ]. }
  exists eps. split; [ exact Heps | ].
  intros q Hqx Hqy f Hf H1 H2.
  apply (Hball q Hqx Hqy f). apply Hes. split; [ exact Hf | ].
  split; assumption.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Certificate + ball bounds => ring complement.                           *)
(* -------------------------------------------------------------------------- *)

Lemma corner_offset_in_complement :
  forall (r : Ring) (v a b : Point) (eps : R) (w : Vec),
    (forall q : Point,
       Rabs (px q - px v) < eps -> Rabs (py q - py v) < eps ->
       forall f, In f (ring_edges r) -> f <> (a, v) -> f <> (v, b) ->
         ~ on_edge f q) ->
    in_open_sector (point_diff a v) (point_diff b v) w ->
    Rabs (vx w) < eps -> Rabs (vy w) < eps ->
    ring_complement r (point_at v w).
Proof.
  intros r v a b eps w Hball Hsect Hbx Hby [f [s [Hf [Hs [Hx Hy]]]]].
  assert (Hon : on_edge f (point_at v w))
    by (exists s; split; [ exact Hs | split; [ exact Hx | exact Hy ] ]).
  destruct (edge_eq_dec f (a, v)) as [-> | Hne1].
  - exact (sector_point_off_incident_in a v b w Hsect Hon).
  - destruct (edge_eq_dec f (v, b)) as [-> | Hne2].
    + exact (sector_point_off_incident_out a v b w Hsect Hon).
    + assert (HBX : Rabs (px (point_at v w) - px v) < eps)
        by (replace (px (point_at v w) - px v) with (vx w)
              by (unfold point_at; cbn; ring); exact Hbx).
      assert (HBY : Rabs (py (point_at v w) - py v) < eps)
        by (replace (py (point_at v w) - py v) with (vy w)
              by (unfold point_at; cbn; ring); exact Hby).
      exact (Hball (point_at v w) HBX HBY f Hf Hne1 Hne2 Hon).
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  A complement-valued straight hop is a continuous connector.             *)
(* -------------------------------------------------------------------------- *)

Lemma hop_connected :
  forall (r : Ring) (v : Point) (A B : Vec),
    (forall t, 0 <= t <= 1 -> ring_complement r (point_at v (vaffine t A B))) ->
    connected_in_complement_cont r (point_at v A) (point_at v B).
Proof.
  intros r v A B Hfree.
  exists (fun t => mkPoint
            ((1 - t) * px (point_at v A) + t * px (point_at v B))
            ((1 - t) * py (point_at v A) + t * py (point_at v B))).
  split; [ apply straight_path_continuous | ].
  split; [ | split ].
  - unfold point_at. cbn. f_equal; ring.
  - unfold point_at. cbn. f_equal; ring.
  - intros t Ht. cbn beta.
    replace (mkPoint ((1 - t) * px (point_at v A) + t * px (point_at v B))
                     ((1 - t) * py (point_at v A) + t * py (point_at v B)))
      with (point_at v (vaffine t A B)).
    + exact (Hfree t Ht).
    + unfold point_at, vaffine, vadd, vscale. cbn. f_equal; ring.
Qed.

(* -------------------------------------------------------------------------- *)
(* §6  Headline: the two-dart corner connector, reflex case.                   *)
(* -------------------------------------------------------------------------- *)

Theorem two_dart_corner_connected_reflex :
  forall (r : Ring) (v a b : Point) (eps rho delta sigma : R),
    In (a, v) (ring_edges r) ->
    In (v, b) (ring_edges r) ->
    (forall q : Point,
       Rabs (px q - px v) < eps -> Rabs (py q - py v) < eps ->
       forall f, In f (ring_edges r) -> f <> (a, v) -> f <> (v, b) ->
         ~ on_edge f q) ->
    vcross (point_diff a v) (point_diff b v) < 0 ->
    0 < rho -> 0 < delta -> 0 < sigma ->
    rho * Rabs (vx (point_diff a v)) + delta * Rabs (vy (point_diff a v)) < eps ->
    rho * Rabs (vy (point_diff a v)) + delta * Rabs (vx (point_diff a v)) < eps ->
    rho * Rabs (vx (point_diff b v)) + delta * Rabs (vy (point_diff b v)) < eps ->
    rho * Rabs (vy (point_diff b v)) + delta * Rabs (vx (point_diff b v)) < eps ->
    sigma * Rabs (vx (point_diff a v)) < eps ->
    sigma * Rabs (vy (point_diff a v)) < eps ->
    connected_in_complement_cont r
      (point_at v (corner_sample_in (point_diff a v) rho delta))
      (point_at v (corner_sample_out (point_diff b v) rho delta)).
Proof.
  intros r v a b eps rho delta sigma Hin Hout Hball Hc Hr Hd Hs
         Hb_in_x Hb_in_y Hb_out_x Hb_out_y Hb_s_x Hb_s_y.
  set (u1 := point_diff a v) in *.
  set (u2 := point_diff b v) in *.
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
    apply (corner_offset_in_complement r v a b eps); [ exact Hball | | | ].
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
    apply (corner_offset_in_complement r v a b eps); [ exact Hball | | | ].
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
  apply (corner_offset_in_complement r v a b eps); [ exact Hball | | | ].
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
(* Axiom audit.  Assembly wiring; allowlist axioms only.                       *)
(* -------------------------------------------------------------------------- *)

Print Assumptions vertex_pruned_clearance.
Print Assumptions two_dart_corner_connected_reflex.

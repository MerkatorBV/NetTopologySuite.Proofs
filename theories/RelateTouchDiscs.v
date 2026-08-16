(* ============================================================================
   NetTopologySuite.Proofs.RelateTouchDiscs
   ----------------------------------------------------------------------------
   Issue #67 x OverlayNGCurve Phase 0: the DE-9IM matrix of the TOUCH pair,
   with per-cell point-set semantics.

   OverlayTouchRow.v (the Phase 0 completeness repair) pinned the externally
   tangent unit discs -- ext_A about (0,0), ext_B about (2,0), kiss (1,0) --
   as the pair the 5-relation matrix misses.  This module carries that same
   witness pair into the relate lane: its full DE-9IM matrix is

        II IB IE      F  F  2
        BI BB BE  =   F  0  1      ("FF2F01212")
        EI EB EE      2  1  2

   and, unlike the lane's constant witness matrices (RelateAreaArea.v ships
   hand-specified matrices with no geometry->matrix content), every cell
   here is backed by a point-set fact about the discs themselves:

     - the four F-cells are PROVEN EMPTY (`td_ii_empty`, `td_ib_empty`,
       `td_bi_empty` -- the triangle squeeze at the kiss -- and the pair's
       interiors-disjoint half of `disks_touch`);
     - BB = 0 is an EXACT SINGLETON: boundary x boundary is {kiss}
       (`td_bb_singleton`, a two-line reuse of `ext_cap_singleton` since
       boundary x boundary is inside the closed lens);
     - the three 2-cells each CONTAIN A METRIC BALL (`td_ie_ball`,
       `td_ei_ball`, `td_ee_ball` -- centres (0,0) / (2,0) / (5,0),
       squared radius (1/2)^2);
     - the two 1-cells are NONEMPTY and CONTAIN NO BALL
       (`td_be_nonempty` / `td_eb_nonempty` + `circle_subset_no_ball`, a
       radial-scale perturbation: any ball about a circle point leaves the
       circle).  Exact dimension-1 semantics (curve content) is deferred,
       matching the lane's own capstone
       (`geom_de9im_cell_dimensions_sound` handles II=2 and BB only).

   The matrix satisfies the OGC `touches` predicate (`pat_touches_1`:
   BI = F with BB nonempty) and `matrix_ok`; the pair itself satisfies the
   Phase 0 TOUCH relation (`ext_touch`, proved in OverlayTouchRow.v).
   Everything is stated in the squared metric (`dist_sq`), matching the
   Disk / DiscOverlay / OverlayTouchRow style -- no square roots anywhere.

   No `Admitted`, no `Axiom`, no `Parameter`; classical-reals trio only.
   topic: relate

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude (Fable)
   ============================================================================ *)

From Stdlib Require Import Reals Lra Lia.
From NTS.Proofs Require Import Distance Disk Overlay DiscOverlay
                               OverlayTouchRow DE9IM.

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  Disc cells in the squared metric.                                       *)
(* -------------------------------------------------------------------------- *)

(** The boundary circle and the (open) exterior; the interior is
    OverlayTouchRow's [in_disk_int]. *)
Definition on_disk_circle (D : Disk) (p : Point) : Prop :=
  dist_sq (dcentre D) p = dradius D * dradius D.

Definition in_disk_ext (D : Disk) (p : Point) : Prop :=
  dradius D * dradius D < dist_sq (dcentre D) p.

(** The nine DE-9IM cells of the TOUCH pair. *)
Definition td_ii (p : Point) : Prop := in_disk_int ext_A p /\ in_disk_int ext_B p.
Definition td_ib (p : Point) : Prop := in_disk_int ext_A p /\ on_disk_circle ext_B p.
Definition td_ie (p : Point) : Prop := in_disk_int ext_A p /\ in_disk_ext ext_B p.
Definition td_bi (p : Point) : Prop := on_disk_circle ext_A p /\ in_disk_int ext_B p.
Definition td_bb (p : Point) : Prop := on_disk_circle ext_A p /\ on_disk_circle ext_B p.
Definition td_be (p : Point) : Prop := on_disk_circle ext_A p /\ in_disk_ext ext_B p.
Definition td_ei (p : Point) : Prop := in_disk_ext ext_A p /\ in_disk_int ext_B p.
Definition td_eb (p : Point) : Prop := in_disk_ext ext_A p /\ on_disk_circle ext_B p.
Definition td_ee (p : Point) : Prop := in_disk_ext ext_A p /\ in_disk_ext ext_B p.

(* -------------------------------------------------------------------------- *)
(* §2  Cell semantics: empty / singleton / ball-backed / ball-free.            *)
(* -------------------------------------------------------------------------- *)

Definition region_empty (S : Point -> Prop) : Prop := forall p, ~ S p.

Definition region_singleton (S : Point -> Prop) (q : Point) : Prop :=
  S q /\ forall p, S p -> p = q.

(** Dimension-2 witness: the cell contains a metric ball (squared form). *)
Definition region_has_ball (S : Point -> Prop) : Prop :=
  exists q rho, 0 < rho /\ forall p, dist_sq q p < rho * rho -> S p.

(** Dimension-at-most-1 witness: no ball fits inside the cell. *)
Definition region_no_ball (S : Point -> Prop) : Prop :=
  forall q rho, 0 < rho -> exists p, dist_sq q p < rho * rho /\ ~ S p.

Definition region_nonempty (S : Point -> Prop) : Prop := exists p, S p.

(* -------------------------------------------------------------------------- *)
(* §3  The four F-cells are empty: the triangle squeeze at the kiss.           *)
(* -------------------------------------------------------------------------- *)

(** Interior x interior: OverlayTouchRow's interiors-disjoint half. *)
Lemma td_ii_empty : region_empty td_ii.
Proof.
  intros p H. exact (ext_cap_interiors_empty p H).
Qed.

(** Interior x boundary: strictly inside A yet exactly on B's circle --
    the centres are 2 apart, so the two distance constraints squeeze
    2*(x-1)^2 + 2*y^2 + 2 strictly below 2. *)
Lemma td_ib_empty : region_empty td_ib.
Proof.
  intros [x y] [H1 H2].
  unfold in_disk_int, on_disk_circle, ext_A, ext_B, dist_sq in *.
  cbn in H1, H2. nra.
Qed.

Lemma td_bi_empty : region_empty td_bi.
Proof.
  intros [x y] [H1 H2].
  unfold in_disk_int, on_disk_circle, ext_A, ext_B, dist_sq in *.
  cbn in H1, H2. nra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  BB is the kiss point, exactly.                                          *)
(* -------------------------------------------------------------------------- *)

(** Boundary x boundary sits inside the closed lens, and the closed lens
    IS the kiss (`ext_cap_singleton`); the kiss sits on both circles
    (`ext_kiss_on_both_circles`). *)
Lemma td_bb_singleton : region_singleton td_bb ext_kiss.
Proof.
  split.
  - destruct ext_kiss_on_both_circles as [HA HB].
    split; [exact HA | exact HB].
  - intros p [HA HB].
    apply ext_cap_singleton.
    unfold lens, in_disk.
    unfold on_disk_circle in HA, HB.
    split; [rewrite HA | rewrite HB]; lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  The three 2-cells contain balls.                                        *)
(* -------------------------------------------------------------------------- *)

(** Interior of A x exterior of B: the ball of radius 1/2 about A's centre. *)
Lemma td_ie_ball : region_has_ball td_ie.
Proof.
  exists (mkPoint 0 0), (1 / 2). split; [lra |].
  intros [x y] Hp.
  unfold dist_sq in Hp. cbn in Hp.
  unfold td_ie, in_disk_int, in_disk_ext, on_disk_circle, ext_A, ext_B,
         dist_sq. cbn.
  split; nra.
Qed.

(** Exterior of A x interior of B: mirrored about B's centre. *)
Lemma td_ei_ball : region_has_ball td_ei.
Proof.
  exists (mkPoint 2 0), (1 / 2). split; [lra |].
  intros [x y] Hp.
  unfold dist_sq in Hp. cbn in Hp.
  unfold td_ei, in_disk_int, in_disk_ext, on_disk_circle, ext_A, ext_B,
         dist_sq. cbn.
  split; nra.
Qed.

(** Exterior x exterior: a ball well east of both discs. *)
Lemma td_ee_ball : region_has_ball td_ee.
Proof.
  exists (mkPoint 5 0), (1 / 2). split; [lra |].
  intros [x y] Hp.
  unfold dist_sq in Hp. cbn in Hp.
  unfold td_ee, in_disk_ext, ext_A, ext_B, dist_sq. cbn.
  split; nra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §6  The two 1-cells: nonempty, and no ball fits.                            *)
(* -------------------------------------------------------------------------- *)

Lemma td_be_nonempty : region_nonempty td_be.
Proof.
  exists (mkPoint (-1) 0).
  unfold td_be, on_disk_circle, in_disk_ext, ext_A, ext_B, dist_sq. cbn.
  split; lra.
Qed.

Lemma td_eb_nonempty : region_nonempty td_eb.
Proof.
  exists (mkPoint 3 0).
  unfold td_eb, on_disk_circle, in_disk_ext, ext_A, ext_B, dist_sq. cbn.
  split; lra.
Qed.

(** Any subset of a circle contains no ball: off-circle points are dense
    (a radial scale about the centre moves any circle point off the circle
    by as little as one likes; off-circle query points defeat the ball at
    its own centre). *)
Lemma circle_subset_no_ball :
  forall (c : Point) (r : R) (S : Point -> Prop),
    0 < r ->
    (forall p, S p -> dist_sq c p = r * r) ->
    region_no_ball S.
Proof.
  intros c r S Hr Hsub q rho Hrho.
  destruct (Req_EM_T (dist_sq c q) (r * r)) as [Hon | Hoff].
  - (* q on the circle: nudge it radially outward by rho/(2r). *)
    set (t := rho / (2 * r)).
    assert (Ht : 0 < t) by (unfold t; apply Rdiv_lt_0_compat; lra).
    set (p := mkPoint (px c + (1 + t) * (px q - px c))
                      (py c + (1 + t) * (py q - py c))).
    assert (Hcp : dist_sq c p = (1 + t) * (1 + t) * dist_sq c q).
    { unfold p, dist_sq. cbn. ring. }
    assert (Hqp : dist_sq q p = t * t * dist_sq c q).
    { unfold p, dist_sq. cbn. ring. }
    exists p. split.
    + rewrite Hqp, Hon.
      unfold t.
      assert (Hexp : rho / (2 * r) * (rho / (2 * r)) * (r * r)
                     = rho * rho / 4) by (field; lra).
      rewrite Hexp. nra.
    + intros HS. specialize (Hsub p HS).
      rewrite Hcp, Hon in Hsub.
      assert (Hrr : 0 < r * r) by nra.
      assert (Htt : 0 < t * t) by nra.
      assert (He : (1 + t) * (1 + t) * (r * r)
                   = r * r + (2 * t) * (r * r) + (t * t) * (r * r)) by ring.
      assert (H1 : 0 < (2 * t) * (r * r))
        by (apply Rmult_lt_0_compat; lra).
      assert (H2 : 0 < (t * t) * (r * r))
        by (apply Rmult_lt_0_compat; lra).
      lra.
  - (* q off the circle: the ball's own centre defeats it. *)
    exists q. split.
    + assert (Hqq : dist_sq q q = 0) by (unfold dist_sq; ring).
      rewrite Hqq. nra.
    + intros HS. exact (Hoff (Hsub q HS)).
Qed.

Lemma td_be_no_ball : region_no_ball td_be.
Proof.
  apply (circle_subset_no_ball (mkPoint 0 0) 1); [lra |].
  intros p [HA _]. exact HA.
Qed.

Lemma td_eb_no_ball : region_no_ball td_eb.
Proof.
  apply (circle_subset_no_ball (mkPoint 2 0) 1); [lra |].
  intros p [_ HB]. exact HB.
Qed.

(* -------------------------------------------------------------------------- *)
(* §7  The matrix, its OGC predicate, and the soundness bundle.                *)
(* -------------------------------------------------------------------------- *)

(** "FF2F01212" -- the canonical area/area touches matrix, here EARNED
    cell by cell rather than hand-specified. *)
Definition touch_discs_matrix : IntersectionMatrix :=
  {| im_ii := None;          im_ib := None;          im_ie := Some 2%nat;
     im_bi := None;          im_bb := Some 0%nat;    im_be := Some 1%nat;
     im_ei := Some 2%nat;    im_eb := Some 1%nat;    im_ee := Some 2%nat |}.

Lemma touch_discs_matrix_ok : matrix_ok touch_discs_matrix.
Proof.
  unfold matrix_ok, touch_discs_matrix, dim_value_ok. cbn.
  repeat split; lia.
Qed.

(** The pair `touches` in the OGC sense: BI = F with BB nonempty
    (`pat_touches_1`). *)
Lemma touch_discs_matrix_touches : im_touches touch_discs_matrix.
Proof.
  unfold im_touches. right; left.
  unfold matrix_matches, pat_touches_1, touch_discs_matrix. cbn.
  repeat split.
Qed.

(** THE BUNDLE: every matrix entry is backed by its point-set fact.  The
    F-cells are empty; BB = 0 is the exact kiss singleton; the 2-cells
    contain balls; the 1-cells are nonempty and ball-free (dimension <= 1;
    exact curve dimension deferred, as in the lane's capstone). *)
Theorem touch_discs_de9im_sound :
  region_empty td_ii /\
  region_empty td_ib /\
  region_has_ball td_ie /\
  region_empty td_bi /\
  region_singleton td_bb ext_kiss /\
  (region_nonempty td_be /\ region_no_ball td_be) /\
  region_has_ball td_ei /\
  (region_nonempty td_eb /\ region_no_ball td_eb) /\
  region_has_ball td_ee.
Proof.
  split; [exact td_ii_empty |].
  split; [exact td_ib_empty |].
  split; [exact td_ie_ball |].
  split; [exact td_bi_empty |].
  split; [exact td_bb_singleton |].
  split; [split; [exact td_be_nonempty | exact td_be_no_ball] |].
  split; [exact td_ei_ball |].
  split; [split; [exact td_eb_nonempty | exact td_eb_no_ball] |].
  exact td_ee_ball.
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions td_ii_empty.
Print Assumptions td_ib_empty.
Print Assumptions td_bi_empty.
Print Assumptions td_bb_singleton.
Print Assumptions td_ie_ball.
Print Assumptions td_ei_ball.
Print Assumptions td_ee_ball.
Print Assumptions td_be_nonempty.
Print Assumptions td_eb_nonempty.
Print Assumptions circle_subset_no_ball.
Print Assumptions td_be_no_ball.
Print Assumptions td_eb_no_ball.
Print Assumptions touch_discs_matrix_ok.
Print Assumptions touch_discs_matrix_touches.
Print Assumptions touch_discs_de9im_sound.

(* ==========================================================================
   WalkStripLift.v

   [H-bridge attack, C-3f discharge rung D-3] The STRIP LIFT: the
   premise's straddle pair at an ARBITRARY offset `ef` connects to the
   walk's pair at any SMALLER offset `ef'` -- two horizontal segments
   inside the #343 strip clearance -- so the orbit chain only ever has
   to run in its own small-offset regime (the D-2 walk threshold).

   Why the segments are complement-valued: a segment point `q` sits at
   the premise's generic height `my` with `|px q - X| <= ef`
   (`X := edge_x_at d my`).  If `q` were on a ring edge `f`:
     - `f = d`: `on_edge_at_height_x` pins `px q = X`, but the segment
       stays at distance >= ef' > 0 from `X` -- contradiction;
     - `f <> d`: the strip-clearance hypothesis (exactly what
       `face_transport_premise` carries since #343, and what
       `straddle_side_core` provides) excludes it.
   The segments themselves are straight horizontal paths
   (`straight_path_continuous`, the corridor construction).

   `strip_lift_connected` composes west segment + inner connectivity +
   east segment, so with `WalkAssembly.walk_straddle_parity` the
   premise's biconditional follows from the walk's small-offset
   connectivity alone.

   No `Admitted` / `Axiom` / `Parameter`; allowlist axioms only.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
   ========================================================================== *)

From Stdlib Require Import Reals Lra List.
From NTS.Proofs Require Import JordanRingKit.
From NTS.Proofs Require Import OverlayGraph Vec Azimuth Dart JCTHugStep
                               RingClearance JCTCorridor EdgeConnectivity
                               StraddleSides.

Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  The two strip segments.                                                 *)
(* -------------------------------------------------------------------------- *)

Lemma strip_segment_west_connected :
  forall (r : Ring) (d : Dart) (my ef ef' : R),
    py (fst d) <> py (snd d) ->
    0 < ef' -> ef' <= ef ->
    (forall (q : Point) (f : Edge),
       In f (ring_edges r) -> f <> d ->
       py q = my ->
       Rabs (px q - edge_x_at d my) <= ef ->
       ~ on_edge f q) ->
    connected_in_complement_cont r
      (mkPoint (edge_x_at d my - ef) my)
      (mkPoint (edge_x_at d my - ef') my).
Proof.
  intros r d my ef ef' Hnh Hef' Hle Hstrip.
  set (X := edge_x_at d my).
  exists (fun t => mkPoint ((1 - t) * (X - ef) + t * (X - ef'))
                           ((1 - t) * my + t * my)).
  split; [ apply straight_path_continuous | ]. split; [ | split ].
  - cbn. f_equal; ring.
  - cbn. f_equal; ring.
  - intros t Ht Himg.
    destruct Himg as [f [s [Hf [Hs [Hx Hy]]]]].
    cbn [px py] in Hx, Hy.
    assert (Hqy : (1 - t) * my + t * my = my) by ring.
    destruct (edge_eq_dec f d) as [-> | Hne].
    + (* on d: the abscissa is pinned to X, but the segment stays away *)
      assert (Hpin : (1 - t) * (X - ef) + t * (X - ef')
                       = edge_x_at d ((1 - t) * my + t * my)).
      { exact (on_edge_at_height_x d
                 (mkPoint ((1 - t) * (X - ef) + t * (X - ef'))
                          ((1 - t) * my + t * my)) s Hnh Hx Hy). }
      rewrite Hqy in Hpin.
      fold X in Hpin. nra.
    + (* another ring edge: the strip clearance kills it *)
      apply (Hstrip (mkPoint ((1 - t) * (X - ef) + t * (X - ef'))
                            ((1 - t) * my + t * my)) f Hf Hne).
      * cbn [py]. exact Hqy.
      * cbn [px]. fold X.
        apply Rabs_le. nra.
      * exists s. split; [ exact Hs | ].
        split; [ exact Hx | exact Hy ].
Qed.

Lemma strip_segment_east_connected :
  forall (r : Ring) (d : Dart) (my ef ef' : R),
    py (fst d) <> py (snd d) ->
    0 < ef' -> ef' <= ef ->
    (forall (q : Point) (f : Edge),
       In f (ring_edges r) -> f <> d ->
       py q = my ->
       Rabs (px q - edge_x_at d my) <= ef ->
       ~ on_edge f q) ->
    connected_in_complement_cont r
      (mkPoint (edge_x_at d my + ef') my)
      (mkPoint (edge_x_at d my + ef) my).
Proof.
  intros r d my ef ef' Hnh Hef' Hle Hstrip.
  set (X := edge_x_at d my).
  exists (fun t => mkPoint ((1 - t) * (X + ef') + t * (X + ef))
                           ((1 - t) * my + t * my)).
  split; [ apply straight_path_continuous | ]. split; [ | split ].
  - cbn. f_equal; ring.
  - cbn. f_equal; ring.
  - intros t Ht Himg.
    destruct Himg as [f [s [Hf [Hs [Hx Hy]]]]].
    cbn [px py] in Hx, Hy.
    assert (Hqy : (1 - t) * my + t * my = my) by ring.
    destruct (edge_eq_dec f d) as [-> | Hne].
    + assert (Hpin : (1 - t) * (X + ef') + t * (X + ef)
                       = edge_x_at d ((1 - t) * my + t * my)).
      { exact (on_edge_at_height_x d
                 (mkPoint ((1 - t) * (X + ef') + t * (X + ef))
                          ((1 - t) * my + t * my)) s Hnh Hx Hy). }
      rewrite Hqy in Hpin.
      fold X in Hpin. nra.
    + apply (Hstrip (mkPoint ((1 - t) * (X + ef') + t * (X + ef))
                            ((1 - t) * my + t * my)) f Hf Hne).
      * cbn [py]. exact Hqy.
      * cbn [px]. fold X.
        apply Rabs_le. nra.
      * exists s. split; [ exact Hs | ].
        split; [ exact Hx | exact Hy ].
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  The lift: small-offset connectivity reaches the premise's pair.         *)
(* -------------------------------------------------------------------------- *)

Theorem strip_lift_connected :
  forall (r : Ring) (d : Dart) (my ef ef' : R),
    py (fst d) <> py (snd d) ->
    0 < ef' -> ef' <= ef ->
    (forall (q : Point) (f : Edge),
       In f (ring_edges r) -> f <> d ->
       py q = my ->
       Rabs (px q - edge_x_at d my) <= ef ->
       ~ on_edge f q) ->
    connected_in_complement_cont r
      (mkPoint (edge_x_at d my - ef') my)
      (mkPoint (edge_x_at d my + ef') my) ->
    connected_in_complement_cont r
      (mkPoint (edge_x_at d my - ef) my)
      (mkPoint (edge_x_at d my + ef) my).
Proof.
  intros r d my ef ef' Hnh Hef' Hle Hstrip Hinner.
  eapply connected_in_complement_cont_trans;
    [ exact (strip_segment_west_connected r d my ef ef' Hnh Hef' Hle Hstrip) | ].
  eapply connected_in_complement_cont_trans;
    [ exact Hinner | ].
  exact (strip_segment_east_connected r d my ef ef' Hnh Hef' Hle Hstrip).
Qed.

(* -------------------------------------------------------------------------- *)
(* Axiom audit.  Straight segments + the strip hypothesis; allowlist only.     *)
(* -------------------------------------------------------------------------- *)

Print Assumptions strip_segment_west_connected.
Print Assumptions strip_lift_connected.

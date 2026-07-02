(* ==========================================================================
   NextOrientationWitness.v

   [H-bridge attack, rung C-3b, step 1] The orientation of `next`,
   MACHINE-CHECKED on a concrete compass fan.

   Everything in the planned face-walk transport (plan.md, rung C-3)
   depends on one orientation convention: which rotational direction
   `DartNext.next` takes around a vertex, and hence on which SIDE of a
   dart `fstep = next o twin` keeps the face it traces.  The convention
   was pinned by hand from `DartAngularOrder.dir_lt`'s definition
   (azimuth order CCW from east: `first_half` upper half-plane first,
   `vcross` sign within a half) -- this file removes the hand-computation
   risk by checking it on the canonical compass fan at the origin:

       E = ((0,0),(1,0))   N = ((0,0),(0,1))
       W = ((0,0),(-1,0))  S = ((0,0),(0,-1))

     - the angular order is  E < N < W < S   (CCW from east);
     - `next fan E = N` (CCW step within the upper half);
     - `next fan S = E` (wrap from the fan maximum to the minimum).

   Consequently a face walk arriving at the origin along a NORTH-pointing
   dart x (so `twin x` = S in the fan) departs along `next fan S` = E --
   the walk turns north-then-east, i.e. `fstep` keeps the traced face on
   the RIGHT of each dart, and the local face sector at a corner is the
   CCW gap from `ddir (twin x)` to `ddir (fstep D x)`.  Downstream rungs
   (the corner connector, the side-sample transport) cite THIS file for
   the convention rather than re-deriving it.

   Pure-R decision unfolding; no `Admitted` / `Axiom` / `Parameter`;
   allowlist axioms only.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
   ========================================================================== *)

From Stdlib Require Import Reals Lra List.
From NTS.Proofs Require Import Distance Overlay OverlayGraph Vec Azimuth Dart
                               DartAngularOrder DartNext.

Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  The compass fan at the origin.                                          *)
(* -------------------------------------------------------------------------- *)

Definition cO : Point := mkPoint 0 0.
Definition dE : Dart := (cO, mkPoint 1 0).
Definition dN : Dart := (cO, mkPoint 0 1).
Definition dW : Dart := (cO, mkPoint (-1) 0).
Definition dS : Dart := (cO, mkPoint 0 (-1)).

Definition compass_fan : list Dart := [dE; dN; dW; dS].

(* Reduce the concrete compass-fan coordinates (cbn's unfolding heuristics
   decline to open the dart definitions inside hypotheses, so an explicit
   cbv allowlist is used). *)
Ltac compass_reduce_in H :=
  cbv [vcross ddir point_diff dtip dbase dE dN dW dS cO vx vy px py fst snd] in H.
Ltac compass_reduce :=
  cbv [vcross ddir point_diff dtip dbase dE dN dW dS cO vx vy px py fst snd].

(* -------------------------------------------------------------------------- *)
(* §2  Half-plane classification of the four directions.                       *)
(* -------------------------------------------------------------------------- *)

Lemma FH_E : first_half (ddir dE).
Proof. right. cbn. split; lra. Qed.

Lemma FH_N : first_half (ddir dN).
Proof. left. cbn. lra. Qed.

Lemma NFH_W : ~ first_half (ddir dW).
Proof. intros [H | [H1 H2]]; cbn in *; lra. Qed.

Lemma NFH_S : ~ first_half (ddir dS).
Proof. intros [H | [H1 H2]]; cbn in *; lra. Qed.

(* -------------------------------------------------------------------------- *)
(* §3  The eleven comparator values the two `next` computations consume.       *)
(* -------------------------------------------------------------------------- *)

Lemma ltb_E_E : dart_ltb dE dE = false.
Proof.
  unfold dart_ltb, dir_ltb.
  destruct (first_half_dec (ddir dE)) as [_ | H];
    [ | exact (False_ind _ (H FH_E)) ].
  destruct (Rlt_dec 0 (vcross (ddir dE) (ddir dE))) as [Hc | _];
    [ exfalso; compass_reduce_in Hc; nra | reflexivity ].
Qed.

Lemma ltb_E_N : dart_ltb dE dN = true.
Proof.
  unfold dart_ltb, dir_ltb.
  destruct (first_half_dec (ddir dE)) as [_ | H];
    [ | exact (False_ind _ (H FH_E)) ].
  destruct (first_half_dec (ddir dN)) as [_ | H];
    [ | exact (False_ind _ (H FH_N)) ].
  destruct (Rlt_dec 0 (vcross (ddir dE) (ddir dN))) as [_ | Hc];
    [ reflexivity | exfalso; apply Hc; compass_reduce; nra ].
Qed.

Lemma ltb_E_W : dart_ltb dE dW = true.
Proof.
  unfold dart_ltb, dir_ltb.
  destruct (first_half_dec (ddir dE)) as [_ | H];
    [ | exact (False_ind _ (H FH_E)) ].
  destruct (first_half_dec (ddir dW)) as [H | _];
    [ exact (False_ind _ (NFH_W H)) | reflexivity ].
Qed.

Lemma ltb_E_S : dart_ltb dE dS = true.
Proof.
  unfold dart_ltb, dir_ltb.
  destruct (first_half_dec (ddir dE)) as [_ | H];
    [ | exact (False_ind _ (H FH_E)) ].
  destruct (first_half_dec (ddir dS)) as [H | _];
    [ exact (False_ind _ (NFH_S H)) | reflexivity ].
Qed.

Lemma ltb_N_E : dart_ltb dN dE = false.
Proof.
  unfold dart_ltb, dir_ltb.
  destruct (first_half_dec (ddir dN)) as [_ | H];
    [ | exact (False_ind _ (H FH_N)) ].
  destruct (first_half_dec (ddir dE)) as [_ | H];
    [ | exact (False_ind _ (H FH_E)) ].
  destruct (Rlt_dec 0 (vcross (ddir dN) (ddir dE))) as [Hc | _];
    [ exfalso; compass_reduce_in Hc; nra | reflexivity ].
Qed.

Lemma ltb_W_E : dart_ltb dW dE = false.
Proof.
  unfold dart_ltb, dir_ltb.
  destruct (first_half_dec (ddir dW)) as [H | _];
    [ exact (False_ind _ (NFH_W H)) | ].
  destruct (first_half_dec (ddir dE)) as [_ | H];
    [ reflexivity | exact (False_ind _ (H FH_E)) ].
Qed.

Lemma ltb_W_N : dart_ltb dW dN = false.
Proof.
  unfold dart_ltb, dir_ltb.
  destruct (first_half_dec (ddir dW)) as [H | _];
    [ exact (False_ind _ (NFH_W H)) | ].
  destruct (first_half_dec (ddir dN)) as [_ | H];
    [ reflexivity | exact (False_ind _ (H FH_N)) ].
Qed.

Lemma ltb_S_E : dart_ltb dS dE = false.
Proof.
  unfold dart_ltb, dir_ltb.
  destruct (first_half_dec (ddir dS)) as [H | _];
    [ exact (False_ind _ (NFH_S H)) | ].
  destruct (first_half_dec (ddir dE)) as [_ | H];
    [ reflexivity | exact (False_ind _ (H FH_E)) ].
Qed.

Lemma ltb_S_N : dart_ltb dS dN = false.
Proof.
  unfold dart_ltb, dir_ltb.
  destruct (first_half_dec (ddir dS)) as [H | _];
    [ exact (False_ind _ (NFH_S H)) | ].
  destruct (first_half_dec (ddir dN)) as [_ | H];
    [ reflexivity | exact (False_ind _ (H FH_N)) ].
Qed.

Lemma ltb_S_W : dart_ltb dS dW = false.
Proof.
  unfold dart_ltb, dir_ltb.
  destruct (first_half_dec (ddir dS)) as [H | _];
    [ exact (False_ind _ (NFH_S H)) | ].
  destruct (first_half_dec (ddir dW)) as [H | _];
    [ exact (False_ind _ (NFH_W H)) | ].
  destruct (Rlt_dec 0 (vcross (ddir dS) (ddir dW))) as [Hc | _];
    [ exfalso; compass_reduce_in Hc; nra | reflexivity ].
Qed.

Lemma ltb_S_S : dart_ltb dS dS = false.
Proof.
  unfold dart_ltb, dir_ltb.
  destruct (first_half_dec (ddir dS)) as [H | _];
    [ exact (False_ind _ (NFH_S H)) | ].
  destruct (Rlt_dec 0 (vcross (ddir dS) (ddir dS))) as [Hc | _];
    [ exfalso; compass_reduce_in Hc; nra | reflexivity ].
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  The two witness computations.                                           *)
(* -------------------------------------------------------------------------- *)

(* CCW step within the upper half: east's successor is north. *)
Theorem next_compass_E : next compass_fan dE = dN.
Proof.
  unfold next.
  assert (Hfil : filter (fun e => dart_ltb dE e) compass_fan = [dN; dW; dS]).
  { unfold compass_fan. cbn [filter].
    rewrite ltb_E_E, ltb_E_N, ltb_E_W, ltb_E_S. reflexivity. }
  rewrite Hfil.
  cbn [list_min fold_left].
  unfold min_step.
  rewrite ltb_W_N. cbn beta iota.
  rewrite ltb_S_N. cbn beta iota.
  reflexivity.
Qed.

(* Wrap from the fan maximum: south's successor is east (the global min). *)
Theorem next_compass_S : next compass_fan dS = dE.
Proof.
  unfold next.
  assert (Hfil : filter (fun e => dart_ltb dS e) compass_fan = []).
  { unfold compass_fan. cbn [filter].
    rewrite ltb_S_E, ltb_S_N, ltb_S_W, ltb_S_S. reflexivity. }
  rewrite Hfil.
  cbn [list_min].
  unfold compass_fan.
  cbn [list_min fold_left].
  unfold min_step.
  rewrite ltb_N_E. cbn beta iota.
  rewrite ltb_W_E. cbn beta iota.
  rewrite ltb_S_E. cbn beta iota.
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  The reading: E < N < W < S, i.e. azimuth CCW from east.                  *)
(* -------------------------------------------------------------------------- *)

Lemma order_E_N : dart_lt dE dN.
Proof. apply dart_ltb_spec. exact ltb_E_N. Qed.

Lemma order_N_W : dart_lt dN dW.
Proof.
  left. split; [ exact FH_N | exact NFH_W ].
Qed.

Lemma order_W_S : dart_lt dW dS.
Proof.
  right. split.
  - right. split; [ exact NFH_W | exact NFH_S ].
  - compass_reduce. nra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Axiom audit.  Decision unfolding on rationals; allowlist axioms only.       *)
(* -------------------------------------------------------------------------- *)

Print Assumptions next_compass_E.
Print Assumptions next_compass_S.

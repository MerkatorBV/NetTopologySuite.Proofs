(* ============================================================================
   NetTopologySuite.Proofs.DiscreteShBridge
   ----------------------------------------------------------------------------
   The discrete -> Sh(R^2) bridge: Boolean truth values embed into the
   Heyting algebra Omega = O(R^2) of the spatial topos of sheaves on the
   plane; the embedding is logical (preserves and/or/not/implb on the
   nose), stalks of bridged values stay Boolean at every point, and the
   pointwise ("stalk") semantics is sound for the topos operations --
   exactly for the geometric fragment, laxly for implication/negation.

   Working level, stated honestly: we formalise the SUBTERMINAL fragment of
   Sh(R^2).  A truth value of Sh(R^2) is an open U of the plane
   (HeytingOpens.v); the "stalk of U at p" is its germ at p, which for
   open U collapses to plain membership (`open_germ_collapse`).  We do not
   build sheaf categories; every statement is at the level of the frame
   O(R^2), which IS the algebra of subobjects of 1 in Sh(R^2).

   Delivered, with the Kock / well-adapted-model reading of each item
   (Kock-Reyes: a model is well adapted when the embedding of the classical
   objects preserves the structure that matters -- finite limits, covers --
   and classical truth is recovered fibrewise):

     - `bridge b` (constant opens): the truth-value part of the constant-
       sheaf functor Delta : Set -> Sh(R^2).  It is injective
       (`bridge_injective`: Delta faithful on 2) and a Heyting/Boolean
       homomorphism on the nose (`bridge_andb/orb/negb/implb`: Delta
       logical on the Boolean algebra 2 -- finite meets, finite covers,
       negation, implication all preserved).
     - stalks stay Boolean: `bridge_stalks_boolean` (every stalk of a
       bridged value is decided: germ-true or germ-false, and decidably so,
       `bridge_stalk_dec`); `stalk_bridge_id` / `bridge_global_sections`
       (evaluation at any point retracts the bridge: Gamma o Delta = id, so
       the discrete logic is recovered fibrewise -- the well-adapted
       "spatial soundness" condition).
     - globally Omega is Heyting, not Boolean: `omega_not_boolean`
       repackages HeytingOpens' punctured-plane witness -- there is an open
       whose stalk at the origin is NOT decided (`punct_stalk_not_boolean`),
       so excluded middle fails globally while holding on the bridge image
       (`discrete_bridge_headline` packages the contrast).
     - the Boolean core of Omega is exactly the discrete image:
       `discrete_iff_complemented` + `stalks_boolean_iff_discrete`, via
       connectedness of the plane (PlaneConnected.v).  Corollary for
       fields: a pointwise-Boolean classification of the plane whose two
       classes are both perturbation-stable (open) is constant
       (`stable_bool_field_constant`) -- Gamma(Delta 2) = 2.
     - spatial soundness of the pointwise semantics: evaluation at p
       preserves top/bot/and/or and ARBITRARY joins exactly
       (`stalk_sound_*`), is sound-but-lax for implication and negation
       (`stalk_lax_imp/not`), and the laxity is strict
       (`stalk_imp_strict`); the subobject order is pointwise
       (`oincl_pointwise`: the topos has enough points).
     - the geometric well-adapted instantiation, NTS-side: strict (OGC
       Interior-style) predicates are truth values -- open half-planes
       (`strict_halfplane_open`) and open disks (`open_disk_open`, linked
       to Disk.v's closed `in_disk` by `open_disk_incl_in_disk`) -- while
       their non-strict closures are not (HeytingOpens.
       `closed_halfplane_not_open`).  This is the formal statement behind
       JTS/NTS's preference for strict predicates in robust branches: only
       open conditions have perturbation-stable (sheaf) semantics.

   No `Admitted`, no `Axiom`, no `Parameter`; three-axiom classical base.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import Real Distance Linearise Disk HeytingOpens PlaneConnected.
Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* The bridge: discrete (Boolean) truth values as constant opens.             *)
(* -------------------------------------------------------------------------- *)

Definition bridge (b : bool) : OSet := fun _ => b = true.

Lemma bridge_open : forall b, is_open (bridge b).
Proof.
  intros b p Hp. exists 1. split; [lra |]. intros q _. exact Hp.
Qed.

Lemma bridge_true_top : osame (bridge true) otop.
Proof.
  intros p. unfold bridge, otop. split; [intros _; exact I | intros _; reflexivity].
Qed.

Lemma bridge_false_bot : osame (bridge false) obot.
Proof.
  intros p. unfold bridge, obot. split; [discriminate | intros []].
Qed.

(* Faithfulness of the bridge on truth values. *)
Lemma bridge_injective : forall b c, osame (bridge b) (bridge c) -> b = c.
Proof.
  intros b c H.
  destruct b, c; try reflexivity.
  - symmetry. apply (H origin). reflexivity.
  - apply (H origin). reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* The bridge is a Boolean/Heyting homomorphism ON THE NOSE: discrete         *)
(* conjunction, disjunction, negation and implication go to the Heyting       *)
(* operations of Omega.                                                       *)
(* -------------------------------------------------------------------------- *)

Lemma bridge_andb : forall b c,
  osame (bridge (andb b c)) (oand (bridge b) (bridge c)).
Proof.
  intros b c p. unfold bridge, oand. destruct b, c; simpl; intuition congruence.
Qed.

Lemma bridge_orb : forall b c,
  osame (bridge (orb b c)) (oor (bridge b) (bridge c)).
Proof.
  intros b c p. unfold bridge, oor. destruct b, c; simpl; intuition congruence.
Qed.

Lemma bridge_negb : forall b,
  osame (bridge (negb b)) (onot (bridge b)).
Proof.
  intros b p. destruct b; simpl; split.
  - discriminate.
  - intros Hn. exfalso.
    apply (onot_elim (bridge true) p Hn). reflexivity.
  - intros _. exists 1. split; [lra |]. intros q _ Hf. discriminate Hf.
  - intros _. reflexivity.
Qed.

Lemma bridge_implb : forall b c,
  osame (bridge (implb b c)) (oimp (bridge b) (bridge c)).
Proof.
  intros b c p. destruct b; simpl.
  - (* implb true c = c *)
    destruct c; split.
    + intros _. exists 1. split; [lra |]. intros q _ _. reflexivity.
    + intros _. reflexivity.
    + discriminate.
    + intros Him. exfalso.
      pose proof (oimp_elim (bridge true) (bridge false) p Him eq_refl) as Hf.
      discriminate Hf.
  - (* implb false c = true *)
    split.
    + intros _. exists 1. split; [lra |]. intros q _ Hf. discriminate Hf.
    + intros _. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Stalks.  The stalk of a truth value at p is its germ; openness collapses   *)
(* the germ to plain membership, and the negation's germ says a whole         *)
(* neighbourhood misses U.  A stalk is BOOLEAN at p when it is decided one    *)
(* way or the other.                                                          *)
(* -------------------------------------------------------------------------- *)

Definition stalk_at (p : Point) (U : OSet) : Prop := U p.

Definition germ_true_at (p : Point) (U : OSet) : Prop :=
  exists eps, 0 < eps /\ forall q, dist p q < eps -> U q.

Definition germ_false_at (p : Point) (U : OSet) : Prop :=
  exists eps, 0 < eps /\ forall q, dist p q < eps -> ~ U q.

Lemma open_germ_collapse : forall U p,
  is_open U -> (stalk_at p U <-> germ_true_at p U).
Proof.
  intros U p HU. split.
  - intros Hp. exact (HU p Hp).
  - intros [eps [Heps H]]. apply (H p).
    pose proof (dist_refl p). lra.
Qed.

Lemma onot_germ_false : forall U p,
  stalk_at p (onot U) <-> germ_false_at p U.
Proof.
  intros U p. split; intros [eps [Heps H]]; exists eps; split; try exact Heps.
  - intros q Hq Hu. exact (H q Hq Hu).
  - intros q Hq Hu. exact (H q Hq Hu).
Qed.

Definition stalk_boolean (p : Point) (U : OSet) : Prop :=
  stalk_at p U \/ stalk_at p (onot U).

(* Transport along pointwise equivalence. *)
Lemma onot_ext : forall U V, osame U V -> oincl (onot U) (onot V).
Proof.
  intros U V Hs p [eps [Heps H]].
  exists eps. split; [exact Heps |].
  intros q Hq Hv. exact (H q Hq (proj2 (Hs q) Hv)).
Qed.

Lemma stalk_boolean_ext : forall U V p,
  osame U V -> stalk_boolean p U -> stalk_boolean p V.
Proof.
  intros U V p Hs [H | H].
  - left. exact (proj1 (Hs p) H).
  - right. exact (onot_ext U V Hs p H).
Qed.

(* ------------------------------------------------------------------------- *)
(* HEADLINE, first half: stalks of bridged (discrete) truth values stay       *)
(* Boolean -- at every point the germ is decided, and decidably so.           *)
(* ------------------------------------------------------------------------- *)

Theorem bridge_stalks_boolean : forall b p, stalk_boolean p (bridge b).
Proof.
  intros b p. destruct b.
  - left. reflexivity.
  - right. exists 1. split; [lra |]. intros q _ Hf. discriminate Hf.
Qed.

Lemma bridge_stalk_dec : forall b p,
  {stalk_at p (bridge b)} + {~ stalk_at p (bridge b)}.
Proof.
  intros b p. destruct b; [left; reflexivity | right; discriminate].
Qed.

(* Evaluation at any point retracts the bridge: Gamma o Delta = id on 2.      *)
Theorem stalk_bridge_id : forall b p, stalk_at p (bridge b) <-> b = true.
Proof. intros b p. unfold stalk_at, bridge. tauto. Qed.

Theorem bridge_global_sections : forall b,
  (forall p, (bridge b) p) <-> b = true.
Proof.
  intros b. split.
  - intros H. exact (H origin).
  - intros H p. exact H.
Qed.

(* ------------------------------------------------------------------------- *)
(* HEADLINE, second half: globally Omega is properly Heyting.  The punctured  *)
(* plane is an open whose stalk at the origin is NOT decided, so excluded     *)
(* middle fails in Omega while every bridged value satisfies it.              *)
(* ------------------------------------------------------------------------- *)

Theorem punct_stalk_not_boolean : ~ stalk_boolean origin punct.
Proof.
  intros [Hp | Hn].
  - apply Hp. simpl. split; reflexivity.
  - exact (onot_punct_empty origin Hn).
Qed.

Theorem omega_not_boolean :
  exists U, is_open U /\ ~ (forall p, stalk_boolean p U).
Proof.
  exists punct. split; [exact punct_open |].
  intros H. exact (punct_stalk_not_boolean (H origin)).
Qed.

(* The contrast, packaged: stalks of discrete values are Boolean everywhere;  *)
(* stalks of general opens are not.                                           *)
Theorem discrete_bridge_headline :
  (forall b p, stalk_boolean p (bridge b)) /\
  ~ (forall U, is_open U -> forall p, stalk_boolean p U).
Proof.
  split.
  - exact bridge_stalks_boolean.
  - intros H. exact (punct_stalk_not_boolean (H punct punct_open origin)).
Qed.

(* -------------------------------------------------------------------------- *)
(* The Boolean core of Omega is exactly the discrete image.  "Complemented"   *)
(* is the standard Heyting-algebra notion; connectedness of the plane         *)
(* (PlaneConnected.v) collapses the complemented elements to the two          *)
(* constants.                                                                 *)
(* -------------------------------------------------------------------------- *)

Definition complemented (U : OSet) : Prop :=
  is_open U /\
  exists V, is_open V /\ osame (oand U V) obot /\ osame (oor U V) otop.

Lemma bridge_complemented : forall b, complemented (bridge b).
Proof.
  intros b. split; [exact (bridge_open b) |].
  exists (bridge (negb b)). split; [exact (bridge_open (negb b)) |]. split.
  - intros p. unfold oand, obot, bridge. destruct b; simpl; intuition congruence.
  - intros p. unfold oor, otop, bridge. destruct b; simpl.
    + split; [intros _; exact I | intros _; left; reflexivity].
    + split; [intros _; exact I | intros _; right; reflexivity].
Qed.

Theorem complemented_is_discrete : forall U,
  complemented U -> osame U (bridge true) \/ osame U (bridge false).
Proof.
  intros U [HU [V [HV [Hdisj Hcov]]]].
  destruct (plane_connected U V HU HV
              (fun p H => proj1 (Hdisj p) H)
              (fun p => proj2 (Hcov p) I)) as [Hall | Hall].
  - left. intros p. split; [intros _; reflexivity | intros _; apply Hall].
  - right. intros p. split.
    + intros HUp. exfalso. exact (proj1 (Hdisj p) (conj HUp (Hall p))).
    + discriminate.
Qed.

Theorem discrete_iff_complemented : forall U,
  complemented U <-> exists b, osame U (bridge b).
Proof.
  intros U. split.
  - intros Hc.
    destruct (complemented_is_discrete U Hc) as [H | H];
      [exists true | exists false]; exact H.
  - intros [b Hs]. split.
    + exact (is_open_ext (bridge b) U (osame_sym U (bridge b) Hs) (bridge_open b)).
    + exists (bridge (negb b)). split; [exact (bridge_open (negb b)) |]. split.
      * intros p. split; [| intros []].
        intros [HUp HVp].
        pose proof (proj1 (Hs p) HUp) as Hb.
        unfold bridge in Hb, HVp. destruct b; simpl in *; congruence.
      * intros p. split; [intros _; exact I | intros _].
        destruct b.
        -- left. apply (proj2 (Hs p)). reflexivity.
        -- right. reflexivity.
Qed.

(* Stalkwise reformulation: an open has Boolean stalks EVERYWHERE iff it is   *)
(* discrete.  (The punctured plane fails exactly at the origin.)              *)
Theorem stalks_boolean_iff_discrete : forall U,
  is_open U ->
  ((forall p, stalk_boolean p U) <-> exists b, osame U (bridge b)).
Proof.
  intros U HU. split.
  - intros Hstalks.
    apply discrete_iff_complemented. split; [exact HU |].
    exists (onot U). split; [exact (open_onot U) |]. split.
    + intros p. split; [| intros []].
      intros [HUp Hn]. exact (onot_elim U p Hn HUp).
    + intros p. split; [intros _; exact I | intros _].
      exact (Hstalks p).
  - intros [b Hs] p.
    apply (stalk_boolean_ext (bridge b) U p
             (osame_sym U (bridge b) Hs)).
    exact (bridge_stalks_boolean b p).
Qed.

(* Field corollary (Gamma(Delta 2) = 2): a pointwise-Boolean classification   *)
(* of the plane whose classes are both perturbation-stable is constant.       *)
Definition pbridge (f : Point -> bool) : OSet := fun p => f p = true.
Definition pbridge_neg (f : Point -> bool) : OSet := fun p => f p = false.

Theorem stable_bool_field_constant : forall f : Point -> bool,
  is_open (pbridge f) -> is_open (pbridge_neg f) ->
  (forall p, f p = true) \/ (forall p, f p = false).
Proof.
  intros f Ht Hf.
  apply (plane_connected (pbridge f) (pbridge_neg f) Ht Hf).
  - intros p [H1 H2]. congruence.
  - intros p. unfold pbridge, pbridge_neg. destruct (f p); [left | right]; reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Spatial soundness of the pointwise semantics.  Evaluation at a point is    *)
(* exact on the geometric fragment (top, bottom, finite meets, arbitrary      *)
(* joins) and lax on implication/negation; the order itself is pointwise.     *)
(* This is the "well-adapted" soundness of the site: classical evaluation     *)
(* never disagrees with the topos on geometric content, and only weakens      *)
(* (never invents) implications.                                              *)
(* -------------------------------------------------------------------------- *)

Theorem stalk_sound_top : forall p, stalk_at p otop <-> True.
Proof. intros p. unfold stalk_at, otop. tauto. Qed.

Theorem stalk_sound_bot : forall p, stalk_at p obot <-> False.
Proof. intros p. unfold stalk_at, obot. tauto. Qed.

Theorem stalk_sound_and : forall U V p,
  stalk_at p (oand U V) <-> (stalk_at p U /\ stalk_at p V).
Proof. intros U V p. unfold stalk_at, oand. tauto. Qed.

Theorem stalk_sound_or : forall U V p,
  stalk_at p (oor U V) <-> (stalk_at p U \/ stalk_at p V).
Proof. intros U V p. unfold stalk_at, oor. tauto. Qed.

Theorem stalk_sound_join : forall (I : Type) (F : I -> OSet) p,
  stalk_at p (ojoin F) <-> (exists i, stalk_at p (F i)).
Proof.
  intros I F p. unfold stalk_at, ojoin.
  split; intros [i Hi]; exists i; exact Hi.
Qed.

Theorem stalk_lax_imp : forall U V p,
  stalk_at p (oimp U V) -> (stalk_at p U -> stalk_at p V).
Proof. intros U V p H Hu. exact (oimp_elim U V p H Hu). Qed.

Theorem stalk_lax_not : forall U p,
  stalk_at p (onot U) -> ~ stalk_at p U.
Proof. intros U p H Hu. exact (onot_elim U p H Hu). Qed.

(* The laxity is strict: a pointwise implication that the topos rejects.      *)
(* At the origin, "punctured plane -> bottom" holds pointwise (vacuously)     *)
(* but fails in Omega: no neighbourhood of the origin avoids the punctured    *)
(* plane.                                                                     *)
Theorem stalk_imp_strict :
  exists U V (p : Point), is_open U /\ is_open V /\
    (stalk_at p U -> stalk_at p V) /\ ~ stalk_at p (oimp U V).
Proof.
  exists punct, obot, origin.
  split; [exact punct_open |].
  split; [exact open_bot |].
  split.
  - intros Hp. exfalso. apply Hp. simpl. split; reflexivity.
  - intros Hn. exact (onot_punct_empty origin Hn).
Qed.

(* Spatiality: the subobject order of Omega is the pointwise order -- the     *)
(* topos has enough points, so stalkwise soundness is also complete for       *)
(* entailment.                                                                *)
Theorem oincl_pointwise : forall U V,
  oincl U V <-> (forall p, stalk_at p U -> stalk_at p V).
Proof. intros U V. unfold oincl, stalk_at. tauto. Qed.

(* -------------------------------------------------------------------------- *)
(* Geometric instantiation (the NTS-side well-adaptedness): strict OGC        *)
(* Interior-style predicates are truth values of Sh(R^2).                     *)
(* -------------------------------------------------------------------------- *)

(* Coordinate displacement is dominated by distance. *)
Lemma dx_le_dist : forall p q, px q - px p <= dist p q.
Proof.
  intros p q.
  apply Rle_trans with (Rabs (px q - px p)); [apply Rle_abs |].
  rewrite <- (sqrt_Rsqr_abs (px q - px p)).
  unfold dist. apply sqrt_le_1.
  - apply Rle_0_sqr.
  - apply dist_sq_nonneg.
  - unfold Rsqr, dist_sq.
    pose proof (sqr_nonneg (py p - py q)). nra.
Qed.

Definition strict_left_halfplane (cutoff : R) : OSet := fun p => px p < cutoff.

(* The strict half-plane x < cutoff is open (its closure x <= cutoff is not:  *)
(* HeytingOpens.closed_halfplane_not_open).                                   *)
Theorem strict_halfplane_open : forall cutoff,
  is_open (strict_left_halfplane cutoff).
Proof.
  intros cutoff p Hp. unfold strict_left_halfplane in *.
  exists (cutoff - px p). split; [lra |].
  intros q Hq. pose proof (dx_le_dist p q). lra.
Qed.

(* The open disk: the strict counterpart of Disk.v's closed `in_disk`.        *)
Definition open_disk (D : Disk) : OSet :=
  fun p => dist_sq (dcentre D) p < dradius D * dradius D.

Theorem open_disk_open : forall D,
  0 <= dradius D -> is_open (open_disk D).
Proof.
  intros D Hr.
  apply (is_open_ext (ball (dcentre D) (dradius D))).
  - intros p. unfold ball, open_disk.
    exact (dist_lt_iff_dist_sq_lt (dcentre D) p (dradius D) Hr).
  - apply open_ball.
Qed.

Lemma open_disk_incl_in_disk : forall D, oincl (open_disk D) (in_disk D).
Proof.
  intros D p Hp. unfold open_disk in Hp. unfold in_disk. lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions bridge_injective.
Print Assumptions bridge_implb.
Print Assumptions bridge_stalks_boolean.
Print Assumptions stalk_bridge_id.
Print Assumptions punct_stalk_not_boolean.
Print Assumptions discrete_bridge_headline.
Print Assumptions discrete_iff_complemented.
Print Assumptions stalks_boolean_iff_discrete.
Print Assumptions stable_bool_field_constant.
Print Assumptions stalk_imp_strict.
Print Assumptions oincl_pointwise.
Print Assumptions strict_halfplane_open.
Print Assumptions open_disk_open.

(* ============================================================================
   NetTopologySuite.Proofs.Flocq.HotPixel_b64_refs
   ----------------------------------------------------------------------------
   PURE-R KERNEL: the radius-parameterised and closed-pixel predicates that
   the binary64 hot-pixel membership and Liang-Barsky stories factor through.

     - `in_hot_pixel_at_radius` + unfold against `HotPixel.in_hot_pixel`
     - `in_hot_pixel_closed` (closed square, same radius)
     - `segment_touches_hot_pixel_closed` (parametric closed-pixel touch)

   This module imports NO Flocq: its Print Assumptions footprint is the
   standard Reals trio only (no `Classical_Prop.classic`), so it is
   deliberately NOT on docs/audit-exceptions.txt -- the first
   HotPixel-lineage module to leave the Category C1 block, mirroring
   InCircle_b64_exact_refs.v and Intersect_b64_exact_refs.v.

   Split out of the former 2616-line HotPixel_b64.v monolith
   (claimId: 66-a, topic: binary64, witness: hot-pixel);
   HotPixel_b64.v remains as the Require Export umbrella, so reverse
   dependencies import unchanged.  Declarations and proofs carried over
   verbatim.  The four Category C2 comparison lemmas
   (`b64_le_R_of_true` / `b64_le_complete` / `b64_lt_R_of_true` /
   `b64_lt_complete`) stay in HotPixel_b64.v: their taint is
   `Bcompare_correct` and they are not a Flocq-free surface.
   No Admitted, no Axiom, no Parameter.
   topic: binary64
   claimId: 66-a
   witness: hot-pixel
   ============================================================================ *)

From Stdlib Require Import Reals.

From NTS.Proofs Require Import Distance HotPixel.

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* `in_hot_pixel_at_radius`: variant of R-side `in_hot_pixel` that takes     *)
(* the radius directly.  Lets soundness state the rounded-pixel form        *)
(* without paying for the integer-regime exact-radius theorem.              *)
(* -------------------------------------------------------------------------- *)

Definition in_hot_pixel_at_radius (P C : Point) (r : R) : Prop :=
  px C - r <= px P < px C + r /\
  py C - r <= py P < py C + r.

Lemma in_hot_pixel_unfold :
  forall P C scale,
    in_hot_pixel P C scale
    <-> in_hot_pixel_at_radius P C (hot_pixel_radius scale).
Proof. intros. unfold in_hot_pixel, in_hot_pixel_at_radius. tauto. Qed.

(* Closed-pixel membership (soundness target for Liang-Barsky). *)
Definition in_hot_pixel_closed (P C : Point) (scale : R) : Prop :=
  px C - hot_pixel_radius scale <= px P <= px C + hot_pixel_radius scale /\
  py C - hot_pixel_radius scale <= py P <= py C + hot_pixel_radius scale.

(* `segment_touches_hot_pixel` (half-open) is from theories/HotPixel.v;
   this is the closed-pixel counterpart. *)
Definition segment_touches_hot_pixel_closed (P0 P1 C : Point) (scale : R) : Prop :=
  exists t : R, 0 <= t <= 1 /\ in_hot_pixel_closed (segment_point P0 P1 t) C scale.

Print Assumptions in_hot_pixel_unfold.

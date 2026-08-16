(* ============================================================================
   NetTopologySuite.Proofs.Flocq.Intersect_b64_exact_bridge
   ----------------------------------------------------------------------------
   PHASE 1 SESSION 6: the reference bridge + soundness typeclass, and the
   chord-paradigm scope note for future curve families.

   - `c2tight_ref_{x,y}_eq_intersect_{x,y}_R`: under int-safe inputs the
     internal C.2-tight reference equals the canonical
     `intersect_{x,y}_R (BP2P ...)` exactly.
   - `b64_intersect_point_{x,y}_forward_error_vs_intersect_{x,y}_R`: the
     Layer-4 bounds restated against the canonical closed-form reference.
   - `HasIntersect` typeclass + `BPoint` instance (the chord-chord hook),
     and `HasIntersect_sound` + its `BPoint` instance plugging in the
     C.2-tight headlines.

   Split out of the former 2888-line Intersect_b64_exact.v monolith
   (Phase 1, line-line intersection point; topic: binary64);
   Intersect_b64_exact.v remains as the Require Export umbrella, so
   reverse dependencies import unchanged.  Slice text, declarations,
   and Print Assumptions footers carried over verbatim.  No Admitted,
   no Axiom, no Parameter.
   ============================================================================ *)

From Stdlib Require Import Reals.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Lra.

From Flocq Require Import IEEE754.Binary.
From Flocq Require Import IEEE754.BinarySingleNaN.
From Flocq Require Import Core.

From NTS.Proofs        Require Import Distance Orientation.
From NTS.Proofs.Flocq  Require Import Validate_binary64.
From NTS.Proofs.Flocq  Require Import Orientation_b64.
From NTS.Proofs.Flocq  Require Import B64_bridge.
From NTS.Proofs.Flocq  Require Import Orient_b64_R.
From NTS.Proofs.Flocq  Require Import Orient_b64_sound.
From NTS.Proofs.Flocq  Require Import Orient_b64_exact.
From NTS.Proofs.Flocq  Require Import Intersect_b64.
From NTS.Proofs.Flocq  Require Import B64_lib.
From NTS.Proofs.Flocq  Require Import Intersect_b64_exact_core.
From NTS.Proofs.Flocq  Require Import Intersect_b64_exact_round_chain.
From NTS.Proofs.Flocq  Require Import Intersect_b64_exact_forward_error.

Local Open Scope R_scope.

(*                                                                            *)
(* The `BPoint` instance routes through the total b64 projections defined   *)
(* above.                                                                    *)
(*                                                                            *)
(* CHORD-PARADIGM SCOPE.  See docs/audit-phase4-curves.md.  The 4-point     *)
(* signature `T -> T -> T -> T -> binary64` is chord-paradigm-specific:    *)
(* chord-chord intersection takes two segments, i.e. four endpoints.       *)
(* A future curve-bearing variant does *not* fit this signature: the       *)
(* natural carrier for a curve is bound to the curve family, and a         *)
(* curve-curve intersection takes two *curves*, not four points.  The      *)
(* right shape is therefore a *family* of parallel typeclasses, one per   *)
(* curve family, all coexisting with `HasIntersect` (the chord case).     *)
(*                                                                            *)
(* (1) Arc-arc.  Canonical carrier is the 3-control-point triplet         *)
(*     (start, on-arc, end):                                              *)
(*                                                                            *)
(*     Class HasArcIntersect (T : Type) : Type := {                       *)
(*       arc_intersect_x          : T -> T -> binary64;                   *)
(*       arc_intersect_y          : T -> T -> binary64;                   *)
(*       arc_intersect_inputs_safe : T -> T -> Prop;                      *)
(*     }.                                                                   *)
(*                                                                            *)
(*     A future `HasArcIntersect_ArcTriplet` instance would route through *)
(*     b64 projections built on the unique-circle-through-three-points    *)
(*     Cramer's-rule analog (see Orient_b64_exact.v's dovetail block).   *)
(*                                                                            *)
(* (2) Clothoid-clothoid.  The clothoid (Euler spiral) is a curve with    *)
(*     linearly-varying curvature -- the standard transition primitive   *)
(*     in road / rail geometry.  Canonical carrier is the G^1 Hermite    *)
(*     pair: two endpoints + two endpoint tangent directions + the        *)
(*     chord length L (Bertolazzi-Frego 2015 / 2018):                    *)
(*                                                                            *)
(*     Class HasClothoidIntersect (T : Type) : Type := {                  *)
(*       clothoid_intersect_x         : T -> T -> binary64;               *)
(*       clothoid_intersect_y         : T -> T -> binary64;               *)
(*       clothoid_intersect_inputs_safe : T -> T -> Prop;                 *)
(*     }.                                                                   *)
(*                                                                            *)
(*     Unlike chord-chord and arc-arc, clothoid-clothoid intersection has *)
(*     no closed form: the intersection parameter is the root of a       *)
(*     transcendental residual involving Fresnel integrals.  The         *)
(*     intended implementation is the Halley iteration on the L-form     *)
(*     residual                                                            *)
(*                                                                            *)
(*         f(L) = L^2 * (P(L)^2 + Q(L)^2) - d^2                          *)
(*                                                                            *)
(*     with                                                                 *)
(*                                                                            *)
(*         P(L) = int_0^1 cos (L * psi(tau)) dtau                        *)
(*         Q(L) = int_0^1 sin (L * psi(tau)) dtau                        *)
(*         psi(tau) = kappa_0 * tau + (kappa_1 - kappa_0) * tau^2 / 2.   *)
(*                                                                            *)
(*     The R-side derivative identities                                    *)
(*                                                                            *)
(*         P'(L) = -T(L)        Q'(L) = R(L)                             *)
(*         R'(L) = -S2s(L)      T'(L) = S2c(L)                           *)
(*         f'(L)  = 2 L (P^2 + Q^2) + 2 L^2 (Q R - P T)                  *)
(*         f''(L) = 2 (P^2 + Q^2) + 8 L (Q R - P T)                      *)
(*                  + 2 L^2 (R^2 + T^2 - P S2c - Q S2s)                  *)
(*                                                                            *)
(*     are already formalised in the companion project                    *)
(*     `clothoid-halley-coq` (Merkator Group, 2026) under Coq 8.13.1 /    *)
(*     8.20.1 with Coquelicot 3.x, no `Admitted`, beyond the four         *)
(*     standard Coquelicot axioms.  Cited per repo's academic-citation   *)
(*     licence; not imported (Coquelicot is a separate real-analysis     *)
(*     library from Flocq, and our corpus targets Rocq 9.1.1).            *)
(*                                                                            *)
(*     Porting cost to land a `HasClothoidIntersect_ClothoidL` instance:  *)
(*                                                                            *)
(*       (a) Re-prove the six R-side derivative identities in Flocq's    *)
(*           native `Reals` framework (Coquelicot's `RInt` becomes our   *)
(*           `RiemannInt`, `is_derive` becomes Flocq's derivative        *)
(*           predicate).  ~3-5 days of mechanical translation; the       *)
(*           proof recipes (`auto_derive`, `Derive` rewrites, `ring`)    *)
(*           are tactic-name preserved.                                   *)
(*       (b) Lift the R-side residual to its binary64 evaluator (Stage-A *)
(*           filter over Halley iterates, no-overflow chain across the   *)
(*           per-iterate updates).  Symmetric to b64_orient2d's          *)
(*           treatment but with iteration-bounded composition.            *)
(*       (c) Termination proof: under the monotone-branch precondition  *)
(*           from clothoid-halley-coq's L-form, Halley converges to       *)
(*           machine precision in <= 4 iterations on the empirical 9,058- *)
(*           record corpus (Merkator paper, table 3).  In the corpus     *)
(*           that becomes a *bounded-iteration* termination lemma, not   *)
(*           a fixpoint-domain argument.                                  *)
(*                                                                            *)
(*     Differential-testing oracle: the 9,058-record golden corpus in    *)
(*     clothoid-halley-coq/data/golden_vectors.json -- bit-identical     *)
(*     across Python / C# / Java / TypeScript reference implementations  *)
(*     within 1e-9 m chord-length agreement, matching iteration counts. *)
(*     Symmetric infrastructure to oracle/extracted.ml in our corpus     *)
(*     (see Validate_binary64_extract.v): a future binary64 Halley       *)
(*     implementation can be extracted to OCaml and bit-compared against *)
(*     the golden corpus before any soundness claim is made.              *)
(*                                                                            *)
(* (3) Any further curve family (Bezier, NURBS, ...) gets its own         *)
(*     parallel typeclass on the same template.                          *)
(*                                                                            *)
(* All these typeclasses coexist on the chord layer: `HasIntersect_BPoint`*)
(* below stays as the chord-chord hook, and each future                   *)
(* `Has{Arc,Clothoid,...}Intersect_{Carrier}` is the corresponding curve  *)
(* hook.  Bridging between any curve family and the chord layer          *)
(* (subdivision to N chords with sagitta tolerance) composes refinement   *)
(* bounds with `HasIntersect_BPoint`, not a new instance of either class. *)
(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
(* Phase 1 Session 6 -- reference bridge + soundness typeclass.               *)
(*                                                                            *)
(* The Scope C.2-tight headlines state the forward-error bound against the    *)
(* internal reference `B2R(bx P0) + s_exact * B2R(b64_minus (bx P1) (bx P0))`.*)
(* Under int-safe inputs the `b64_minus` step is bit-exact (Session 1's       *)
(* `b64_intersect_dx_R`) and `cross_R_BP = cross (BP2P ...)` (Intersect_b64's *)
(* `cross_R_BP_eq_cross_BP2P`), so the reference equals                       *)
(* `intersect_x_R (BP2P P0, BP2P P1, BP2P Q0, BP2P Q1)` exactly.              *)
(*                                                                            *)
(* This section threads that bridge, restates the headlines against the       *)
(* canonical `intersect_x_R`/`intersect_y_R` references, and plugs the bound  *)
(* into a `HasIntersect_sound` typeclass layered on `HasIntersect`.           *)
(* -------------------------------------------------------------------------- *)

Lemma c2tight_ref_x_eq_intersect_x_R :
  forall P0 P1 Q0 Q1 : BPoint,
    intersect_point_inputs_int_safe P0 P1 Q0 Q1 ->
    Binary.B2R prec emax (bx P0)
    + cross_R_BP Q0 Q1 P0
      / (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1)
      * Binary.B2R prec emax (b64_minus (bx P1) (bx P0))
    = intersect_x_R (BP2P P0) (BP2P P1) (BP2P Q0) (BP2P Q1).
Proof.
  intros P0 P1 Q0 Q1 Hsafe.
  destruct (b64_intersect_dx_R _ _ _ _ Hsafe) as [Hdx _].
  rewrite Hdx.
  unfold intersect_x_R, intersect_param_s, BP2P, px.
  rewrite (cross_R_BP_eq_cross_BP2P Q0 Q1 P0).
  rewrite (cross_R_BP_eq_cross_BP2P Q0 Q1 P1).
  unfold BP2P, px.
  reflexivity.
Qed.

Lemma c2tight_ref_y_eq_intersect_y_R :
  forall P0 P1 Q0 Q1 : BPoint,
    intersect_point_inputs_int_safe P0 P1 Q0 Q1 ->
    Binary.B2R prec emax (by_ P0)
    + cross_R_BP Q0 Q1 P0
      / (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1)
      * Binary.B2R prec emax (b64_minus (by_ P1) (by_ P0))
    = intersect_y_R (BP2P P0) (BP2P P1) (BP2P Q0) (BP2P Q1).
Proof.
  intros P0 P1 Q0 Q1 Hsafe.
  destruct (b64_intersect_dy_R _ _ _ _ Hsafe) as [Hdy _].
  rewrite Hdy.
  unfold intersect_y_R, intersect_param_s, BP2P, py.
  rewrite (cross_R_BP_eq_cross_BP2P Q0 Q1 P0).
  rewrite (cross_R_BP_eq_cross_BP2P Q0 Q1 P1).
  unfold BP2P, py.
  reflexivity.
Qed.

(* Restated headline against the canonical intersect_x_R reference. *)
Theorem b64_intersect_point_x_forward_error_vs_intersect_x_R :
  forall P0 P1 Q0 Q1 : BPoint,
    intersect_point_inputs_int_safe P0 P1 Q0 Q1 ->
    Rabs (Binary.B2R prec emax (b64_intersect_point_x P0 P1 Q0 Q1)
          - intersect_x_R (BP2P P0) (BP2P P1) (BP2P Q0) (BP2P Q1))
    <= bpow radix2 29
       + bpow radix2 80
         / Rabs (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1).
Proof.
  intros P0 P1 Q0 Q1 Hsafe.
  rewrite <- (c2tight_ref_x_eq_intersect_x_R _ _ _ _ Hsafe).
  apply (b64_intersect_point_x_forward_error _ _ _ _ Hsafe).
Qed.

Theorem b64_intersect_point_y_forward_error_vs_intersect_y_R :
  forall P0 P1 Q0 Q1 : BPoint,
    intersect_point_inputs_int_safe P0 P1 Q0 Q1 ->
    Rabs (Binary.B2R prec emax (b64_intersect_point_y P0 P1 Q0 Q1)
          - intersect_y_R (BP2P P0) (BP2P P1) (BP2P Q0) (BP2P Q1))
    <= bpow radix2 29
       + bpow radix2 80
         / Rabs (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1).
Proof.
  intros P0 P1 Q0 Q1 Hsafe.
  rewrite <- (c2tight_ref_y_eq_intersect_y_R _ _ _ _ Hsafe).
  apply (b64_intersect_point_y_forward_error _ _ _ _ Hsafe).
Qed.

Class HasIntersect (T : Type) : Type := {
  intersect_x          : T -> T -> T -> T -> binary64;
  intersect_y          : T -> T -> T -> T -> binary64;
  intersect_inputs_safe : T -> T -> T -> T -> Prop;
}.

Instance HasIntersect_BPoint : HasIntersect BPoint := {
  intersect_x          := b64_intersect_point_x;
  intersect_y          := b64_intersect_point_y;
  intersect_inputs_safe := intersect_point_inputs_int_safe;
}.

(* Soundness layer: caller-facing forward-error contract.  Each instance      *)
(* supplies a reference value (`intersect_ref_x/y`) and an error bound        *)
(* (`intersect_error_bound`) that depends on the inputs; the two soundness    *)
(* obligations require the b64 result to be within the bound of the          *)
(* reference under the safety predicate.                                      *)
Class HasIntersect_sound (T : Type) `{HasIntersect T} : Type := {
  intersect_ref_x       : T -> T -> T -> T -> R;
  intersect_ref_y       : T -> T -> T -> T -> R;
  intersect_error_bound : T -> T -> T -> T -> R;
  intersect_x_sound :
    forall a b c d : T,
      intersect_inputs_safe a b c d ->
      Rabs (Binary.B2R prec emax (intersect_x a b c d)
            - intersect_ref_x a b c d)
      <= intersect_error_bound a b c d;
  intersect_y_sound :
    forall a b c d : T,
      intersect_inputs_safe a b c d ->
      Rabs (Binary.B2R prec emax (intersect_y a b c d)
            - intersect_ref_y a b c d)
      <= intersect_error_bound a b c d;
}.

Instance HasIntersect_sound_BPoint : HasIntersect_sound BPoint := {
  intersect_ref_x       := fun A B C D =>
                             intersect_x_R (BP2P A) (BP2P B) (BP2P C) (BP2P D);
  intersect_ref_y       := fun A B C D =>
                             intersect_y_R (BP2P A) (BP2P B) (BP2P C) (BP2P D);
  intersect_error_bound := fun A B C D =>
                             bpow radix2 29
                             + bpow radix2 80
                               / Rabs (cross_R_BP C D A - cross_R_BP C D B);
  intersect_x_sound     := b64_intersect_point_x_forward_error_vs_intersect_x_R;
  intersect_y_sound     := b64_intersect_point_y_forward_error_vs_intersect_y_R;
}.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions c2tight_ref_x_eq_intersect_x_R.
Print Assumptions c2tight_ref_y_eq_intersect_y_R.
Print Assumptions b64_intersect_point_x_forward_error_vs_intersect_x_R.
Print Assumptions b64_intersect_point_y_forward_error_vs_intersect_y_R.

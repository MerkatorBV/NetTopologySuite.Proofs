(* ============================================================================
   NetTopologySuite.Proofs.FrechetMaxmin
   ----------------------------------------------------------------------------
   N. Meinert, "Walking Your Frog Fast in 4 LoC", arXiv:2404.05708 (2024,
   DLR Institute of Communications and Navigation) -- the recursion-free,
   linear-memory reformulation of the DISCRETE FRECHET DISTANCE of
   Eiter & Mannila (1994), the metric JTS-adjacent trajectory analytics
   (vessel-route clustering, map matching, coastline matching) run on
   GNSS vertex chains.  Fills the Frechet half of epic #423 next to the
   Hausdorff lane (docs/hausdorff-penetration.md).

   The paper's engine is the dynamic program (its eq (1)):
       M_ij = max( min(M_{i-1,j}, M_{i-1,j-1}, M_{i,j-1}), d_ij ),
   delta_dF = M_PQ -- the "two frogs on stones" leash: the frogs may
   only advance along their curves, and the leash must cover the
   current pair; Meinert's Algorithm 2 consumes this row-by-row with
   the 4-LoC kernel  FRECHET_MAXMIN(a, x1, x2) = max(min(a, x1), x2).

   What is proved here (all pure Rmax/Rmin algebra over ARBITRARY reals
   -- no metric hypotheses needed):

   (a) KERNEL INVARIANTS of frechet_maxmin: the current distance always
       survives (M_ij >= d_ij), the kernel is monotone in the carried
       prefix value (the fact that makes the bottom-up rewrite of the
       top-down recursion sound), and the output never exceeds the
       carried/current envelope.

   (b) THE 2x2 RECURRENCE IN CLOSED FORM: unrolling eq (1) on two
       2-point curves gives  delta_dF = max(d11, d22)  identically --
       the diagonal coupling wins, the detour cells d12/d21 are
       correctly discarded by the min.  (dF_2x2_closed_form)

   (c) PADDING INVARIANCE (the paper's footnote 1, the fact that makes
       SIMD batching sound: curves in a batch are length-equalised by
       repeating vertices): unrolling eq (1) on the padded 3x2 instance
       [p1;p1;p2] vs [q1;q2] gives exactly the 2x2 value, for ALL
       distance inputs.  (dF_pad_invariant)

   (d) FRECHET SEES DIRECTION: for the 1D curves p = [0;3] against the
       REVERSED q = [3;0], every vertex of p sits exactly on a vertex
       of q (both cross distances are 0 -- the vertex SETS coincide, so
       any set distance such as the directed Hausdorff of 423-a is 0),
       yet the ordered leash is 3.  This is why trajectory analytics
       uses Frechet, not Hausdorff: a route and its reverse are the
       same set but not the same journey.  (frechet_sees_direction)

   HONEST SCOPE: the general P x Q list DP, Meinert's Theorem 1 (the
   fold/scan Algorithm 2 computes eq (1) with O(Q) memory), and the
   Eiter-Mannila sandwich  delta_F <= delta_dF <= delta_F + max(eps_p,
   eps_q)  are NOT formalised here.  The list DP with its coupling
   spec is the natural future RED claim of epic #423's Frechet side
   (sibling of 423-a), and is deliberately left to that gate.

   No `Admitted`, no `Axiom`, no `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  The 4-LoC kernel.                                                      *)
(* -------------------------------------------------------------------------- *)

(* Meinert Algorithm 2, FRECHET_MAXMIN: a = best value over the three
   admissible predecessor cells, x1 = the remaining predecessor being
   folded in, x2 = the current pair distance d_ij. *)
Definition frechet_maxmin (a x1 x2 : R) : R := Rmax (Rmin a x1) x2.

(* -------------------------------------------------------------------------- *)
(* §2  Unrolled recurrences (defined before the tactic users below).          *)
(* -------------------------------------------------------------------------- *)

(* Eq (1) unrolled for two 2-point curves with distance matrix
   (d11 d12 / d21 d22):
     M11 = d11,  M12 = max(d11, d12),  M21 = max(d11, d21),
     M22 = max( min(M12, M11, M21), d22 ). *)
Definition dF_2x2 (d11 d12 d21 d22 : R) : R :=
  Rmax (Rmin (Rmin (Rmax d11 d12) d11) (Rmax d11 d21)) d22.

(* Eq (1) unrolled for the PADDED first curve [p1; p1; p2] against
   [q1; q2]: row 2 repeats row 1's distances (d11 d12), row 3 carries
   (d21 d22).  Written without lets so the case tactic can open it. *)
Definition dF_3x2_pad (d11 d12 d21 d22 : R) : R :=
  Rmax
    (Rmin
       (Rmin
          (* M22 = max( min(M12, M11, M21), d12 ) *)
          (Rmax (Rmin (Rmin (Rmax d11 d12) d11) (Rmax d11 d11)) d12)
          (* M21 = max(M11, d11) *)
          (Rmax d11 d11))
       (* M31 = max(M21, d21) *)
       (Rmax (Rmax d11 d11) d21))
    d22.

Ltac fm_crunch :=
  unfold frechet_maxmin, dF_2x2, dF_3x2_pad, Rmax, Rmin, Rabs in *;
  repeat match goal with
         | |- context [Rle_dec ?a ?b] => destruct (Rle_dec a b)
         | H : context [Rle_dec ?a ?b] |- _ => destruct (Rle_dec a b)
         | |- context [Rcase_abs ?t] => destruct (Rcase_abs t)
         | H : context [Rcase_abs ?t] |- _ => destruct (Rcase_abs t)
         end;
  try lra.

(* -------------------------------------------------------------------------- *)
(* §3  Kernel invariants.                                                     *)
(* -------------------------------------------------------------------------- *)

(* The leash always covers the current pair: M_ij >= d_ij. *)
Lemma frechet_maxmin_ge_current : forall a x1 x2, x2 <= frechet_maxmin a x1 x2.
Proof. intros. fm_crunch. Qed.

(* Monotone in the carried prefix -- improving the predecessors can only
   improve the cell.  This is the order-independence that lets the
   top-down recursion be replaced by Meinert's bottom-up row sweep. *)
Lemma frechet_maxmin_carry_monotone : forall a a' x1 x2,
    a <= a' -> frechet_maxmin a x1 x2 <= frechet_maxmin a' x1 x2.
Proof. intros. fm_crunch. Qed.

(* ... and in the folded-in predecessor. *)
Lemma frechet_maxmin_pred_monotone : forall a x1 x1' x2,
    x1 <= x1' -> frechet_maxmin a x1 x2 <= frechet_maxmin a x1' x2.
Proof. intros. fm_crunch. Qed.

(* The output never exceeds the carried/current envelope (both bounds):
   the leash at a cell is no worse than any admissible predecessor plus
   the current pair. *)
Lemma frechet_maxmin_le_envelope : forall a x1 x2,
    frechet_maxmin a x1 x2 <= Rmax a x2 /\
    frechet_maxmin a x1 x2 <= Rmax x1 x2.
Proof. intros. split; fm_crunch. Qed.

(* -------------------------------------------------------------------------- *)
(* §4  The 2x2 closed form: the diagonal coupling wins.                       *)
(* -------------------------------------------------------------------------- *)

(* For 2-point curves the frogs jump (1,1) -> (2,2) diagonally; the min
   in eq (1) correctly discards both detours, for ALL real inputs:
   delta_dF = max(d11, d22).  No metric facts are used. *)
Lemma dF_2x2_closed_form : forall d11 d12 d21 d22,
    dF_2x2 d11 d12 d21 d22 = Rmax d11 d22.
Proof. intros. fm_crunch. Qed.

(* -------------------------------------------------------------------------- *)
(* §5  Padding invariance (Meinert footnote 1): repeating a vertex does       *)
(*     not change the discrete Frechet value -- the SIMD-batching law.        *)
(* -------------------------------------------------------------------------- *)

Lemma dF_pad_invariant : forall d11 d12 d21 d22,
    dF_3x2_pad d11 d12 d21 d22 = dF_2x2 d11 d12 d21 d22.
Proof. intros. fm_crunch. Qed.

(* -------------------------------------------------------------------------- *)
(* §6  Frechet sees direction; set distances do not.                          *)
(* -------------------------------------------------------------------------- *)

(* 1D curves p = [0; 3] and the REVERSED q = [3; 0]: both cross pairs
   coincide (d12 = d21 = 0), so the vertex sets are equal and every
   set-based distance (e.g. 423-a's directed Hausdorff) vanishes -- yet
   the ordered leash is 3: a route and its reverse are the same set of
   stones but not the same journey. *)
Lemma frechet_sees_direction :
    Rabs (0 - 0) = 0 /\
    Rabs (3 - 3) = 0 /\
    dF_2x2 (Rabs (0 - 3)) (Rabs (0 - 0)) (Rabs (3 - 3)) (Rabs (3 - 0)) = 3.
Proof. repeat split; fm_crunch. Qed.

(* MISMATCH PROBE: the closed form is NOT max of all four entries -- on
   the reversed-curve instance that reading would also give 3, so probe
   with a detour-dominant matrix instead: d12 = 7 must be discarded. *)
Lemma dF_2x2_discards_detour : dF_2x2 1 7 0 2 = 2.
Proof. fm_crunch. Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions dF_2x2_closed_form.
Print Assumptions dF_pad_invariant.
Print Assumptions frechet_sees_direction.

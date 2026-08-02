(* ============================================================================
   nts-eval micro unit — claimId 69-a (RED)
   Red planted 2026-08-02 · Green pending
   (Plan alias: OracleChecklist_W1_W5 — the issue-#69 oracle-mode
   checklist surface, documentation-as-claim.)
   ----------------------------------------------------------------------------
   ORACLE-MODE CHECKLIST W1–W5 for the SQL/MM Part 3 + OGC SFA curve
   umbrella (issue #69 / JTS#1195): five witness obligations that any
   curve-aware oracle mode must discharge, each anchored to a standard
   predicate, a curve class, and a rational witness.

   THE COVERAGE TABLE (documentation-as-claim; formal rows below):

   | row | obligation (witness)            | curve class     | SQL/MM–SFA anchor      | statement shape        |
   |-----|---------------------------------|-----------------|------------------------|------------------------|
   | W1  | closed / not-closed pair        | LineString ring | SFA ST_IsClosed        | decidable pt equality  |
   | W2  | exact squared perimeter         | LineString ring | SFA ST_Length (M-LEN)  | rational sum equality  |
   | W3  | 3-point circle membership       | CircularString  | SQL/MM ST_CircularString | dist_sq = r^2 each   |
   | W4  | point-on-curve, forward side    | circular arc    | SFA relate / R-* (65-b) | dist_sq + signed dot  |
   | W5  | closed => no pinch  (AS TABLED) | LineString ring | SQL/MM ST_IsRing       | MISSING witness — row  |
   |     |                                 |                 |                        | CONTRADICTED below     |

   RED SURFACE.  The headline claim
   (`w1_w5_coverage_table_claim` = W1 /\ W2 /\ W3 /\ W4 /\ W5-as-tabled)
   is STATED below and deliberately NOT proved — no `Admitted`, no
   `Axiom`; the claim is a named `Definition ... : Prop`, so the
   Eval -> Qed matcher reports 69-a red.  The red is SEMANTIC, not
   parse/type noise: rows W1–W4 are individually Qed at Red, and the W5
   row AS TABLED (SQL/MM ST_IsRing rendered as "every closed linestring
   is pinch-free", i.e. with the simplicity witness obligation MISSING)
   is PROVED CONTRADICTED by a rational counter-example — the pinched
   ring (0,0)-(1,0)-(0,0)-(0,1)-(0,0), closed but revisiting its start
   at an interior vertex.  Consequently the tabled conjunction is
   refutable (`w1_w5_table_as_tabled_refuted`, Qed), so the focused
   check fails on main for the right reason until Green REPAIRS the W5
   row (fold the no-pinch obligation INTO the ring predicate as a
   required witness, ST_IsRing = closed AND simple, rather than
   deriving simplicity from closedness) and closes the repaired table.
   Green target:
     Lemma w1_w5_coverage_table_complete : <repaired table>.
   (name verified unclosed corpus-wide; production home suggested
   theories/OracleCurveChecklist.v, same WITNESS tag).

   WITNESS claimId: 69-a
   topic: oracle
   Lemma (Green target): w1_w5_coverage_table_complete
   ========================================================================== *)

(* WITNESS {"claimId":"69-a","topic":"oracle","lemma":"w1_w5_coverage_table_complete","title":"Oracle-mode checklist W1-W5 covers the SQL/MM-SFA curve predicates"} *)

From Stdlib Require Import Reals Lra List Lia.
Import ListNotations.
Local Open Scope R_scope.

Record Point : Type := mkPoint { px : R; py : R }.

Definition dist_sq (p q : Point) : R :=
  (px p - px q) * (px p - px q) + (py p - py q) * (py p - py q).

Definition origin : Point := mkPoint 0 0.

(* LineString scaffolding. *)
Definition head_pt (l : list Point) : Point := hd origin l.
Definition last_pt (l : list Point) : Point := last l origin.

(* SFA ST_IsClosed: first and last control points coincide. *)
Definition closed_ls (l : list Point) : Prop := head_pt l = last_pt l.

(* No interior vertex revisits the start (one concrete simplicity
   obligation — the "pinch" degeneracy ST_IsRing must exclude). *)
Definition no_pinch (l : list Point) : Prop :=
  forall i, (0 < i)%nat -> (i < length l - 1)%nat ->
    nth i l origin <> head_pt l.

(* Squared-length aggregate for M-LEN rows (rational on rational rings). *)
Fixpoint sum_seg_sq (l : list Point) : R :=
  match l with
  | a :: ((b :: _) as tl) => dist_sq a b + sum_seg_sq tl
  | _ => 0
  end.

(* -------------------------------------------------------------------------- *)
(* Rational fixtures.                                                         *)
(* -------------------------------------------------------------------------- *)

(* Unit-square ring and an open two-point path. *)
Definition sq_ring : list Point :=
  [mkPoint 0 0; mkPoint 1 0; mkPoint 1 1; mkPoint 0 1; mkPoint 0 0].
Definition open_path : list Point := [mkPoint 0 0; mkPoint 1 0].

(* Three rational points of the unit circle (a CircularString triple). *)
Definition cs_p1 : Point := mkPoint 1 0.
Definition cs_p2 : Point := mkPoint 0 1.
Definition cs_p3 : Point := mkPoint (-1) 0.

(* The pinched ring: closed, but the interior vertex 2 revisits the start. *)
Definition pinched_ring : list Point :=
  [mkPoint 0 0; mkPoint 1 0; mkPoint 0 0; mkPoint 0 1; mkPoint 0 0].

(* -------------------------------------------------------------------------- *)
(* The five checklist rows.                                                   *)
(* -------------------------------------------------------------------------- *)

(* W1 — SFA ST_IsClosed: a closed / not-closed witness pair. *)
Definition W1_is_closed_row : Prop :=
  closed_ls sq_ring /\ ~ closed_ls open_path.

(* W2 — SFA ST_Length (M-LEN anchor), squared convention: the unit-square
   ring has squared-segment sum exactly 4. *)
Definition W2_length_row : Prop :=
  sum_seg_sq sq_ring = 4.

(* W3 — SQL/MM ST_CircularString: the three defining points lie on one
   circle (centre origin, radius 1), all rational. *)
Definition W3_circularstring_row : Prop :=
  dist_sq cs_p1 origin = 1 /\ dist_sq cs_p2 origin = 1 /\
  dist_sq cs_p3 origin = 1.

(* W4 — point-on-curve for relate/R-* rows (the 65-b carrier vocabulary):
   the apex (0,1) lies on the unit circle at the origin, on the forward
   side of the tangent t = (1,0) at the start point (1,0) — here the
   forward functional evaluates to 0 (on the dividing diameter). *)
Definition W4_point_on_curve_row : Prop :=
  dist_sq (mkPoint 0 1) origin = 1 /\
  0 <= (px (mkPoint 0 1) - px origin) * 0 + (py (mkPoint 0 1) - py origin) * 1.

(* W5 — SQL/MM ST_IsRing AS TABLED: the row renders ST_IsRing as
   "closedness alone implies pinch-freeness", i.e. the simplicity
   WITNESS OBLIGATION IS MISSING from the table.  This is the
   deliberately contradictory row. *)
Definition W5_is_ring_row_tabled : Prop :=
  forall l, closed_ls l -> no_pinch l.

(* -------------------------------------------------------------------------- *)
(* The 69-a claim (RED: stated, not closed — and refutable AS TABLED).        *)
(* -------------------------------------------------------------------------- *)

Definition w1_w5_coverage_table_claim : Prop :=
  W1_is_closed_row /\ W2_length_row /\ W3_circularstring_row /\
  W4_point_on_curve_row /\ W5_is_ring_row_tabled.

(* RED: no proof of the claim in this unit or in production — and none is
   possible AS TABLED: `w5_row_contradicted` below refutes the W5 row, so
   `w1_w5_table_as_tabled_refuted` refutes the conjunction.  Green must
   REPAIR the table (make the no-pinch witness part of the ring
   predicate: ST_IsRing = closed /\ no_pinch, not a consequence of
   closedness) and then Qed
     w1_w5_coverage_table_complete
   over the repaired rows (micro-kernel + production mirror, suggested
   theories/OracleCurveChecklist.v). *)

(* -------------------------------------------------------------------------- *)
(* Row pins (Qed at Red): W1–W4 hold individually — the ONLY red mass is      *)
(* the mis-tabled W5 row.                                                     *)
(* -------------------------------------------------------------------------- *)

Lemma w1_row_holds : W1_is_closed_row.
Proof.
  split.
  - reflexivity.
  - intros H. unfold closed_ls, head_pt, last_pt, open_path in H.
    cbn in H. injection H. lra.
Qed.

Lemma w2_row_holds : W2_length_row.
Proof.
  unfold W2_length_row, sum_seg_sq, sq_ring, dist_sq. cbn. lra.
Qed.

Lemma w3_row_holds : W3_circularstring_row.
Proof.
  unfold W3_circularstring_row, dist_sq, cs_p1, cs_p2, cs_p3, origin.
  cbn. lra.
Qed.

Lemma w4_row_holds : W4_point_on_curve_row.
Proof.
  unfold W4_point_on_curve_row, dist_sq, origin. cbn. lra.
Qed.

(* The rational counter-example: the pinched ring is closed... *)
Lemma pinched_ring_closed : closed_ls pinched_ring.
Proof. reflexivity. Qed.

(* ...but its interior vertex 2 IS the start point, so the W5 row as
   tabled is contradicted — the missing simplicity witness is exactly
   what the row forgot. *)
Lemma w5_row_contradicted : ~ W5_is_ring_row_tabled.
Proof.
  intros H.
  specialize (H pinched_ring pinched_ring_closed 2%nat).
  apply H; [ lia | cbn; lia | reflexivity ].
Qed.

(* Hence the table AS TABLED is refutable: the focused check cannot go
   Green without repairing the W5 row first. *)
Lemma w1_w5_table_as_tabled_refuted : ~ w1_w5_coverage_table_claim.
Proof.
  intros [_ [_ [_ [_ H5]]]]. exact (w5_row_contradicted H5).
Qed.

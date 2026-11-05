import FirstReturn

/-!
# Exact five-vertex adjacency and first-return block calculation

This module relates the **actual base graph** encoded in CloneGraph.lean at
n=0 to the row-source adjacency blocks of the delayed-clone spectral note.
All indices are finite, and each block entry is proved against the graph's
edge relation. The first two return-length matrices and their sum are
computed *in the Lean kernel*, not assumed as a second abstract definition.

Atom order: a,b,c. Gate order: e,f.
Base graph: e→a, e→b, b→a, a→f, f→c, c→e.

The no-extra-intermediate-walk fact comes from the nilpotence Q²=0, and
FirstReturn.lean independently checks length support for all delayed clones.

The proof does not yet identify every first-return Type-valued path in
every delayed clone with its base walk; that multiplicity/path-bijection
statement is an additional formal obligation.
-/

namespace LoopsFormal.CloneGraph.ReturnBlocks

/-- The three internal atoms, enumerated a,b,c. -/
def atom (i : Fin 3) : Vertex 0 :=
  ⟨if i.val = 0 then 2 else if i.val = 1 then 1 else 4,
    by
      by_cases hzero : i.val = 0
      · simp [hzero, size]
      · by_cases hone : i.val = 1
        · simp [hzero, hone, size]
        · simp [hzero, hone, size]⟩

/-- The two designated gate vertices, enumerated e,f. -/
def gate (i : Fin 2) : Vertex 0 :=
  ⟨if i.val = 0 then 0 else 3,
    by
      by_cases hzero : i.val = 0
      · simp [hzero, size]
      · simp [hzero, size]⟩

/-- Atom-to-atom incidence Q in the ordering a,b,c. -/
def Q (i j : Fin 3) : Nat :=
  if i.val = 1 ∧ j.val = 0 then 1 else 0

/-- Atom-to-gate incidence C (rows a,b,c; columns e,f). -/
def C (i : Fin 3) (j : Fin 2) : Nat :=
  if (i.val = 0 ∧ j.val = 1) ∨ (i.val = 2 ∧ j.val = 0)
  then 1 else 0

/-- Gate-to-atom incidence D (rows e,f; columns a,b,c). -/
def D (i : Fin 2) (j : Fin 3) : Nat :=
  if (i.val = 0 ∧ (j.val = 0 ∨ j.val = 1)) ∨
     (i.val = 1 ∧ j.val = 2)
  then 1 else 0


/-- Exhaustive (constructive) elimination of Fin 2 without mathlib. -/
private theorem fin2_all {P : Fin 2 → Prop}
    (h0 : P 0) (h1 : P 1) : ∀ i : Fin 2, P i := by
  intro i
  have hval : i.val = 0 ∨ i.val = 1 := by
    have hi := i.isLt
    omega
  cases hval with
  | inl h =>
      have heq : i = 0 := Fin.ext h
      rw [heq]
      exact h0
  | inr h =>
      have heq : i = 1 := Fin.ext h
      rw [heq]
      exact h1

/-- Exhaustive (constructive) elimination of Fin 3 without mathlib. -/
private theorem fin3_all {P : Fin 3 → Prop}
    (h0 : P 0) (h1 : P 1) (h2 : P 2) :
    ∀ i : Fin 3, P i := by
  intro i
  have hval : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 := by
    have hi := i.isLt
    omega
  cases hval with
  | inl h =>
      have heq : i = 0 := Fin.ext h
      rw [heq]
      exact h0
  | inr other =>
      cases other with
      | inl h =>
          have heq : i = 1 := Fin.ext h
          rw [heq]
          exact h1
      | inr h =>
          have heq : i = 2 := Fin.ext h
          rw [heq]
          exact h2

/-- The underlying finite graph relation is decidable by its three
explicit arithmetic edge clauses. -/
private instance edgeDecidable (n : Nat) (u v : Vertex n) :
    Decidable (Edge n u v) := by
  unfold Edge
  infer_instance

/-- All entries of Q are the actual internal-edge incidences. -/
theorem Q_matches_graph :
    ∀ i j : Fin 3, (Q i j = 1 ↔ Edge 0 (atom i) (atom j)) := by
  apply fin3_all <;> apply fin3_all <;> decide

/-- All entries of C are the actual internal-to-gate incidences. -/
theorem C_matches_graph :
    ∀ i : Fin 3, ∀ j : Fin 2,
      (C i j = 1 ↔ Edge 0 (atom i) (gate j)) := by
  apply fin3_all <;> apply fin2_all <;> decide

/-- All entries of D are the actual gate-to-internal incidences. -/
theorem D_matches_graph :
    ∀ i : Fin 2, ∀ j : Fin 3,
      (D i j = 1 ↔ Edge 0 (gate i) (atom j)) := by
  apply fin2_all <;> apply fin3_all <;> decide

/-- There is no edge directly from one gate to another. -/
theorem no_gate_edge :
    ∀ i j : Fin 2, ¬ Edge 0 (gate i) (gate j) := by
  apply fin2_all <;> apply fin2_all <;> decide

/-- Finite, explicit three-coordinate summation for the internal atoms. -/
def sumAtoms (f : Fin 3 → Nat) : Nat :=
  f 0 + f 1 + f 2

/-- Number of internal-edge length-two walks, Q². -/
def Qsq (i j : Fin 3) : Nat :=
  sumAtoms (fun a => Q i a * Q a j)

/-- No walk can traverse two internal-to-internal edges. -/
theorem Q_squared_zero : ∀ i j : Fin 3, Qsq i j = 0 := by
  decide

/-- Two-edge first returns, given by the matrix product D*C. -/
def R2 (i j : Fin 2) : Nat :=
  sumAtoms (fun a => D i a * C a j)

/-- Three-edge first returns, given by D*Q*C. -/
def R3 (i j : Fin 2) : Nat :=
  sumAtoms (fun a =>
    sumAtoms (fun b => D i a * Q a b * C b j))

/-- The two-step first-return matrix has an off-diagonal unit each way. -/
theorem R2_exact :
    ∀ i j : Fin 2,
      R2 i j = if i.val = j.val then 0 else 1 := by
  decide

/-- The three-step matrix has precisely one extra path e→b→a→f. -/
theorem R3_exact :
    ∀ i j : Fin 2,
      R3 i j = if i.val = 0 ∧ j.val = 1 then 1 else 0 := by
  decide

/-- The total two-gate return incidence, with multiplicities. -/
def R (i j : Fin 2) : Nat := R2 i j + R3 i j

/-- The exact return incidence matrix is [[0,2],[1,0]]. -/
theorem R_exact :
    ∀ i j : Fin 2,
      R i j =
        if i.val = 0 ∧ j.val = 1 then 2
        else if i.val = 1 ∧ j.val = 0 then 1
        else 0 := by
  decide

/-- In particular, the weighted reduction's unweighted matrix acts
on coordinate columns exactly as in LoopsFormal.returnStep. -/
def returnAction (v : Nat × Nat) : Nat × Nat :=
  (R 0 0 * v.1 + R 0 1 * v.2,
   R 1 0 * v.1 + R 1 1 * v.2)

theorem returnAction_matches_previous (v : Nat × Nat) :
    returnAction v = LoopsFormal.returnStep v := by
  simp [returnAction, R, R2, R3, sumAtoms,
    Q, C, D, LoopsFormal.returnStep]

/-- The new, graph-derived matrix inherits the certified
nonprimitivity theorem from LoopsFormal. -/
def iterateAction : Nat → (Nat × Nat) → (Nat × Nat)
  | 0, v => v
  | k + 1, v => returnAction (iterateAction k v)

theorem iterateAction_eq_previous (k : Nat) (v : Nat × Nat) :
    iterateAction k v = LoopsFormal.iterateReturn k v := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [iterateAction, LoopsFormal.iterateReturn]
      rw [ih, returnAction_matches_previous]

/-- The graph-derived unweighted matrix has no positive natural power. -/
theorem return_matrix_not_primitive :
    ¬ ∃ k : Nat,
       0 < (iterateAction k LoopsFormal.basis0).1 ∧
       0 < (iterateAction k LoopsFormal.basis0).2 ∧
       0 < (iterateAction k LoopsFormal.basis1).1 ∧
       0 < (iterateAction k LoopsFormal.basis1).2 := by
  intro h
  obtain ⟨k, h⟩ := h
  apply LoopsFormal.no_positive_power k
  dsimp [LoopsFormal.PowerStrictlyPositive]
  simpa only [iterateAction_eq_previous] using h

end LoopsFormal.CloneGraph.ReturnBlocks

/-!
# Lean-checked two-gate return-operator obstruction

The reduced first-return matrix R = [[0,2],[1,0]] acts on column vectors
(x,y) by (2*y,x). This file formalizes the induced linear-map iteration
over natural-number vectors and proves that no positive power has every
entry strictly positive.

This is a *narrow* formal result: it does not establish that the original
five-vertex graph and all delayed clones are primitive, nor the spectral
formula or any MLC theorem. The complete argument is explained in
research/independent_audits/clone_spectral_referee_note.md.

No axioms, proof placeholders, or external solvers are used.
-/

namespace LoopsFormal

/-- The action of the two-gate return matrix
    [ 0 2 ]
    [ 1 0 ] on a column vector. -/
def returnStep (v : Nat × Nat) : Nat × Nat :=
  (2 * v.2, v.1)

/-- Iterating the return operator, i.e. taking its natural-number powers. -/
def iterateReturn : Nat → (Nat × Nat) → (Nat × Nat)
  | 0, v => v
  | n + 1, v => returnStep (iterateReturn n v)

/-- Two successive return steps multiply both coordinates by two. -/
theorem returnStep_square (v : Nat × Nat) :
    returnStep (returnStep v) = (2 * v.1, 2 * v.2) := by
  rfl

/-- The operator preserves the property that at least one coordinate
    vanishes: each application swaps the zero coordinate. -/
theorem zero_coordinate_survives (v : Nat × Nat)
    (h : v.1 = 0 ∨ v.2 = 0) (n : Nat) :
    (iterateReturn n v).1 = 0 ∨ (iterateReturn n v).2 = 0 := by
  induction n with
  | zero =>
      simpa [iterateReturn] using h
  | succ n ih =>
      change (returnStep (iterateReturn n v)).1 = 0 ∨
        (returnStep (iterateReturn n v)).2 = 0
      cases ih with
      | inl hfirst =>
          exact Or.inr hfirst
      | inr hsecond =>
          apply Or.inl
          change 2 * (iterateReturn n v).2 = 0
          simp [hsecond]

/-- The first column of the nth matrix power is the image of (1,0). -/
def basis0 : Nat × Nat := (1, 0)

/-- The second column is the image of (0,1). -/
def basis1 : Nat × Nat := (0, 1)

/-- Neither basis column can ever acquire two strictly positive entries. -/
theorem first_column_has_zero (n : Nat) :
    (iterateReturn n basis0).1 = 0 ∨ (iterateReturn n basis0).2 = 0 := by
  exact zero_coordinate_survives basis0 (Or.inr rfl) n

theorem second_column_has_zero (n : Nat) :
    (iterateReturn n basis1).1 = 0 ∨ (iterateReturn n basis1).2 = 0 := by
  exact zero_coordinate_survives basis1 (Or.inl rfl) n

/-- A power is entrywise positive iff both basis columns are positive. -/
def PowerStrictlyPositive (n : Nat) : Prop :=
  0 < (iterateReturn n basis0).1 ∧
  0 < (iterateReturn n basis0).2 ∧
  0 < (iterateReturn n basis1).1 ∧
  0 < (iterateReturn n basis1).2

/-- No natural-number power of R is entrywise strictly positive. -/
theorem no_positive_power (n : Nat) : ¬ PowerStrictlyPositive n := by
  intro h
  have both_positive :
      0 < (iterateReturn n basis0).1 ∧
      0 < (iterateReturn n basis0).2 := ⟨h.1, h.2.1⟩
  cases first_column_has_zero n with
  | inl hz =>
      have impossible : 0 < (0 : Nat) := by
        simpa [hz] using both_positive.1
      simp at impossible
  | inr hz =>
      have impossible : 0 < (0 : Nat) := by
        simpa [hz] using both_positive.2
      simp at impossible

/-- Consequently R is not a primitive nonnegative matrix. -/
theorem two_gate_return_not_primitive :
    ¬ ∃ n : Nat, PowerStrictlyPositive n := by
  intro h
  cases h with
  | intro n hn =>
      exact no_positive_power n hn

end LoopsFormal

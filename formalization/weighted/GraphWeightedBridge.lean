import WeightedReturn
import ReturnBlocks

/-!
# Kernel bridge from the graph's counted return paths to weighted matrices

The original Lean module ReturnBlocks proves that the base five-vertex
graph's adjacency blocks Q, C, D match the actual edge relation and
that the two return-length coefficient matrices are R2=D*C and
R3=D*Q*C. The module ReturnPaths, already in the same Lake dependency
graph, certifies the corresponding first-return counts for every delay.

This file builds the real weighted matrix directly out of those already
checked *integer* coefficients. It proves the equality with the
negative-power operator in WeightedReturn.lean and inherits the
exact eigenproblem/polynomial equivalence.

No graph coefficient is simply asserted as a real-valued constant here.
-/

namespace LoopsSpectral

open LoopsFormal.CloneGraph.ReturnBlocks

noncomputable section

/-- The actual two-gate base first-return matrix acting on real
coordinate vectors, weighted by the inverse powers of *return length*.
Both diagonal entries and both off-diagonal entries use R2 and R3. -/
def fromGraphWeighted (t : ℝ) (v : ℝ × ℝ) : ℝ × ℝ :=
  (((R2 0 0 : ℕ) : ℝ) * (t ^ 2)⁻¹ * v.1 +
      ((R3 0 0 : ℕ) : ℝ) * (t ^ 3)⁻¹ * v.1 +
      ((R2 0 1 : ℕ) : ℝ) * (t ^ 2)⁻¹ * v.2 +
      ((R3 0 1 : ℕ) : ℝ) * (t ^ 3)⁻¹ * v.2,
   ((R2 1 0 : ℕ) : ℝ) * (t ^ 2)⁻¹ * v.1 +
      ((R3 1 0 : ℕ) : ℝ) * (t ^ 3)⁻¹ * v.1 +
      ((R2 1 1 : ℕ) : ℝ) * (t ^ 2)⁻¹ * v.2 +
      ((R3 1 1 : ℕ) : ℝ) * (t ^ 3)⁻¹ * v.2)

/-- The path-counted graph weights are *exactly* the negative-exponent
matrix used in the previously checked real algebra theorem. -/
theorem fromGraphWeighted_eq_weightedReturn (t : ℝ) (v : ℝ × ℝ) :
    fromGraphWeighted t v = weightedReturn t v := by
  rcases v with ⟨e, f⟩
  simp [fromGraphWeighted, weightedReturn, R2_exact, R3_exact,
    add_mul, mul_add]

/-- Same polynomial equivalence, now using the actual graph-derived
R2 and R3 coefficients in the same Lean theorem dependency chain. -/
theorem graph_weighted_eigen_iff_polynomial (n : ℕ) (t : ℝ)
    (ht : t ≠ 0) :
    (∃ e f : ℝ, f ≠ 0 ∧
       fromGraphWeighted t (e, f) = (t ^ n * e, t ^ n * f)) ↔
      t ^ (2 * n + 5) = t + 1 := by
  simpa only [fromGraphWeighted_eq_weightedReturn, WeightedEigen] using
    weighted_eigen_iff_polynomial n t ht

/-- At a positive root, the original graph-based weighted matrix
also has an explicitly positive eigenvector. -/
theorem graph_weighted_positive_witness (n : ℕ) (t : ℝ)
    (ht : 0 < t) (hp : t ^ (2 * n + 5) = t + 1) :
    ∃ e f : ℝ, 0 < e ∧ 0 < f ∧
      fromGraphWeighted t (e, f) = (t ^ n * e, t ^ n * f) := by
  obtain ⟨e, f, he, hf, h⟩ := positive_gate_eigenvector n t ht hp
  refine ⟨e, f, he, hf, ?_⟩
  simpa only [fromGraphWeighted_eq_weightedReturn, WeightedEigen] using h

end

end LoopsSpectral

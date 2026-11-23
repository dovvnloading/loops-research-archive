import Period27RealMarkov
import FiniteMarkovFibers

/-!
# Every finite inverse fiber inside the actual period-27 real partition

This module instantiates the general finite-fiber theorem with the actual
quadratic map `x ↦ x² + c`, the actual critical-orbit vertices, and the
independently kernel-checked 26-edge row predicate. Every realization premise
is discharged by an interval or orbit theorem in `Period27RealMarkov`.

For every natural horizon, every source/target edge, and every point in the
target interior, the corresponding matrix-power entry counts distinct actual
real preimages in the source interior. Existence of a parameter satisfying
the premises is supplied by the previously proved exact period-27 center.
No infinite coding, entropy, clone identification, or complex-plane statement
is inferred from this finite real-fiber result.
-/

namespace LoopsRealPeriod27.Markov

open Set LoopsFormal.Paper2 LoopsFormal.Period27

noncomputable section

/-- The finite row matrix is independent of the real parameter. Its entries
are source-row/target-column multiplicities. -/
def physicalAdjacency : Matrix (Fin 26) (Fin 26) ℕ :=
  fun i j => if RowContains i j then 1 else 0

/-- Every field of the general realization interface is proved for the
specified actual quadratic. No path-to-orbit correspondence is a premise. -/
def realizedSystem (c : ℝ) (hc : c ∈ Icc left right)
    (hclose : iterate (quadratic c) 27 0 = 0) : LoopsRealMarkov.System 26 where
  vertex := vertex c
  f := quadratic c
  next := nextRank
  row := RowContains
  rowDecidable := fun i j => inferInstance
  ordered := vertex_strictMono c hc
  vertex_step := vertex_step c hclose
  image_core := by
    intro i y hy
    have him : y ∈ Icc (vertex c (lowerRank i)) (vertex c (upperRank i)) := by
      rw [← physical_edge_image c hc hclose i]
      exact hy
    have hv := (vertex_strictMono c hc).monotone
    exact ⟨(hv (show (0 : Fin 27) ≤ lowerRank i from Fin.zero_le _)).trans him.1,
      him.2.trans (hv (show upperRank i ≤ Fin.last 26 from Fin.le_last _))⟩
  branch_injective := quadratic_injOn_edge c hc
  row_preimage := row_iff_physical_preimage c hc hclose

/-- Explicit finite-path/actual-preimage equivalence for every finite
horizon. The paths use precisely the independently checked row predicate. -/
def physicalPathFiberEquiv (c : ℝ) (hc : c ∈ Icc left right)
    (hclose : iterate (quadratic c) 27 0 = 0) (n : ℕ) (i j : Fin 26) (y : ℝ)
    (hy : y ∈ Ioo (vertex c j.castSucc) (vertex c j.succ)) :
    (realizedSystem c hc hclose).Paths n i j ≃
      {x : ℝ // x ∈ Ioo (vertex c i.castSucc) (vertex c i.succ) ∧
        iterate (quadratic c) n x = y} :=
  (realizedSystem c hc hclose).pathFiberEquiv n i j y hy

/-- Actual distinct preimages form a finite type; finiteness is derived
from the bijection and is not silently assumed by `Nat.card`. -/
theorem physical_preimage_finite (c : ℝ) (hc : c ∈ Icc left right)
    (hclose : iterate (quadratic c) 27 0 = 0) (n : ℕ) (i j : Fin 26) (y : ℝ)
    (hy : y ∈ Ioo (vertex c j.castSucc) (vertex c j.succ)) :
    Finite {x : ℝ // x ∈ Ioo (vertex c i.castSucc) (vertex c i.succ) ∧
      iterate (quadratic c) n x = y} :=
  (realizedSystem c hc hclose).physical_fiber_finite n i j y hy

/-- All-horizon physical bridge: a matrix-power entry counts distinct
actual real preimages of every interior target, with both endpoints fixed. -/
theorem physical_preimage_count (c : ℝ) (hc : c ∈ Icc left right)
    (hclose : iterate (quadratic c) 27 0 = 0) (n : ℕ) (i j : Fin 26) (y : ℝ)
    (hy : y ∈ Ioo (vertex c j.castSucc) (vertex c j.succ)) :
    Nat.card {x : ℝ // x ∈ Ioo (vertex c i.castSucc) (vertex c i.succ) ∧
      iterate (quadratic c) n x = y} = (physicalAdjacency ^ n) i j :=
  (realizedSystem c hc hclose).physical_fiber_card_eq_matrix_power n i j y hy

/-- Every actual preimage in the closed physical core belongs to exactly
one source-interior fiber. Endpoint exclusion is proved, not a convention
that silently discards endpoint preimages. -/
def physicalCoreFiberPartition (c : ℝ) (hc : c ∈ Icc left right)
    (hclose : iterate (quadratic c) 27 0 = 0) (n : ℕ) (j : Fin 26) (y : ℝ)
    (hy : y ∈ Ioo (vertex c j.castSucc) (vertex c j.succ)) :
    ((i : Fin 26) × {x : ℝ //
      x ∈ Ioo (vertex c i.castSucc) (vertex c i.succ) ∧
      iterate (quadratic c) n x = y}) ≃
    {x : ℝ // x ∈ Icc (vertex c 0) (vertex c (Fin.last 26)) ∧
      iterate (quadratic c) n x = y} :=
  (realizedSystem c hc hclose).coreFiberPartition n j y hy

theorem physical_core_preimage_finite (c : ℝ) (hc : c ∈ Icc left right)
    (hclose : iterate (quadratic c) 27 0 = 0) (n : ℕ) (j : Fin 26) (y : ℝ)
    (hy : y ∈ Ioo (vertex c j.castSucc) (vertex c j.succ)) :
    Finite {x : ℝ // x ∈ Icc (vertex c 0) (vertex c (Fin.last 26)) ∧
      iterate (quadratic c) n x = y} :=
  (realizedSystem c hc hclose).core_fiber_finite n j y hy

/-- The corresponding column sum counts all physical-core preimages.
Preimages outside the core are outside the scope of this theorem. -/
theorem physical_core_preimage_count (c : ℝ) (hc : c ∈ Icc left right)
    (hclose : iterate (quadratic c) 27 0 = 0) (n : ℕ) (j : Fin 26) (y : ℝ)
    (hy : y ∈ Ioo (vertex c j.castSucc) (vertex c j.succ)) :
    Nat.card {x : ℝ // x ∈ Icc (vertex c 0) (vertex c (Fin.last 26)) ∧
      iterate (quadratic c) n x = y} = ∑ i : Fin 26, (physicalAdjacency ^ n) i j :=
  (realizedSystem c hc hclose).core_fiber_card_eq_matrix_column_sum n j y hy

/-- The analytic premises are inhabited by an actual certified center.
The conclusion is uniform in all finite horizons, edges, and interior targets. -/
theorem exists_physical_center_with_all_fiber_counts :
    ∃ c : ℝ, c ∈ Icc left right ∧ iterate (quadratic c) 27 0 = 0 ∧
      (∀ (n : ℕ) (i j : Fin 26) (y : ℝ),
        y ∈ Ioo (vertex c j.castSucc) (vertex c j.succ) →
          Finite {x : ℝ // x ∈ Ioo (vertex c i.castSucc) (vertex c i.succ) ∧
            iterate (quadratic c) n x = y} ∧
          Nat.card {x : ℝ // x ∈ Ioo (vertex c i.castSucc) (vertex c i.succ) ∧
            iterate (quadratic c) n x = y} = (physicalAdjacency ^ n) i j) := by
  obtain ⟨c, hc, hclose, _⟩ := exists_physical_center_with_markov_rows
  refine ⟨c, hc, hclose, ?_⟩
  intro n i j y hy
  exact ⟨physical_preimage_finite c hc hclose n i j y hy,
    physical_preimage_count c hc hclose n i j y hy⟩

#print axioms realizedSystem
#print axioms physicalPathFiberEquiv
#print axioms physical_preimage_finite
#print axioms physical_preimage_count
#print axioms physicalCoreFiberPartition
#print axioms physical_core_preimage_finite
#print axioms physical_core_preimage_count
#print axioms exists_physical_center_with_all_fiber_counts

end
end LoopsRealPeriod27.Markov

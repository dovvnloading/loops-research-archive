import FullCloneEigen

/-!
# Exact row-source full adjacency matrix

The previous FullCloneEigen module directly proves an eigenvector
identity for the three-case local successor rule. Here we connect
that rule to the actual Edge relation already defined and proven
primitive in CloneGraph.lean.

This is a *full* (2n+5) x (2n+5) finite adjacency matrix. A row of
the matrix lists all outgoing edges from a vertex. We prove that
its finite row sum is exactly the local action and thus inherits
the explicit all-delay positive eigenvector.
-/

namespace LoopsSpectral

open LoopsFormal.CloneGraph

noncomputable section

/-- The true adjacency matrix of the previously formalized graph.
    It has a 1 precisely when the source-to-target directed edge
    exists, and 0 otherwise. The graph has no parallel edges. -/
def fullAdjacencyMatrix (n : ℕ) : Matrix (Vertex n) (Vertex n) ℝ := by
  classical
  exact fun u w => if Edge n u w then 1 else 0

/-- Exact matrix action, using row-source convention. -/
def fullMatrixAction (n : ℕ) (v : Vertex n → ℝ) (u : Vertex n) : ℝ :=
  ∑ w : Vertex n, fullAdjacencyMatrix n u w * v w

private theorem edge_from_nonlast_iff (n : ℕ) (u w : Vertex n)
    (hnext : u.val + 1 < size n) :
    Edge n u w ↔
      w = nextVertex n u hnext ∨
        (u.val = n ∧ w = afterTip n) := by
  unfold Edge
  constructor
  · intro h
    rcases h with hordinary | hwrap | hshortcut
    · left
      apply Fin.ext
      simpa [nextVertex] using hordinary
    · omega
    · right
      constructor
      · exact hshortcut.1
      · apply Fin.ext
        simpa [afterTip] using hshortcut.2
  · intro h
    rcases h with hordinary | ⟨htip, hskip⟩
    · left
      have hval := congrArg Fin.val hordinary
      simpa [nextVertex] using hval
    · right
      right
      refine ⟨htip, ?_⟩
      have hval := congrArg Fin.val hskip
      simpa [afterTip] using hval

private theorem edge_from_last_iff (n : ℕ) (u w : Vertex n)
    (hnot : ¬ (u.val + 1 < size n)) :
    Edge n u w ↔ w = hub n := by
  have hlast : u.val + 1 = size n := by
    have hu := u.isLt
    omega
  unfold Edge
  constructor
  · intro h
    rcases h with hordinary | hwrap | hshortcut
    · have hw := w.isLt
      omega
    · apply Fin.ext
      simpa [hub] using hwrap.2
    · have hn : u.val = n := hshortcut.1
      dsimp [size] at hlast
      omega
  · intro h
    right
    left
    constructor
    · exact hlast
    · have hv := congrArg Fin.val h
      simpa [hub] using hv

/-- A finite summation over the *actual* Edge relation agrees with
the ordinary-successor / shortcut / wrap rule at every source. -/
theorem fullMatrixAction_eq_fullCloneAction (n : ℕ)
    (v : Vertex n → ℝ) (u : Vertex n) :
    fullMatrixAction n v u = fullCloneAction n v u := by
  classical
  unfold fullMatrixAction fullAdjacencyMatrix
  simp only [ite_mul, one_mul, zero_mul]
  by_cases hnext : u.val + 1 < size n
  · by_cases htip : u.val = n
    · have hneq : nextVertex n u hnext ≠ afterTip n := by
        intro h
        have hv := congrArg Fin.val h
        dsimp [nextVertex, afterTip] at hv
        omega
      calc
        (∑ w : Vertex n, if Edge n u w then v w else 0) =
          ∑ w : Vertex n,
            ((if w = nextVertex n u hnext then v w else 0) +
             (if w = afterTip n then v w else 0)) := by
            apply Finset.sum_congr rfl
            intro w _
            simp only [edge_from_nonlast_iff n u w hnext]
            by_cases hfirst : w = nextVertex n u hnext
            · subst w
              simp [htip, hneq]
            · by_cases hsecond : w = afterTip n
              · subst w
                have hne' : afterTip n ≠ nextVertex n u hnext :=
                  Ne.symm hneq
                simp [htip, hne']
              · simp [htip, hfirst, hsecond]
        _ = v (nextVertex n u hnext) + v (afterTip n) := by
          rw [Finset.sum_add_distrib]
          simp
        _ = fullCloneAction n v u := by
          unfold fullCloneAction
          rw [dif_pos hnext, if_pos htip]
    · calc
        (∑ w : Vertex n, if Edge n u w then v w else 0) =
          ∑ w : Vertex n,
            (if w = nextVertex n u hnext then v w else 0) := by
            apply Finset.sum_congr rfl
            intro w _
            simp only [edge_from_nonlast_iff n u w hnext]
            simp [htip]
        _ = v (nextVertex n u hnext) := by simp
        _ = fullCloneAction n v u := by
          unfold fullCloneAction
          rw [dif_pos hnext, if_neg htip]
          simp
  · calc
      (∑ w : Vertex n, if Edge n u w then v w else 0) =
        ∑ w : Vertex n, (if w = hub n then v w else 0) := by
          apply Finset.sum_congr rfl
          intro w _
          simp only [edge_from_last_iff n u w hnext]
      _ = v (hub n) := by simp
      _ = fullCloneAction n v u := by simp [fullCloneAction, hnext]

/-- **Full adjacency eigenpair.** The actual finite matrix of the
    directed cloned graph has the strictly positive vector
    fullCloneVector as a real eigenvector, for every delay n. -/
theorem fullAdjacencyMatrix_eigen (n : ℕ) (t : ℝ)
    (ht : 1 < t) (hroot : t ^ (2 * n + 5) = t + 1)
    (u : Vertex n) :
    (∑ w : Vertex n,
      fullAdjacencyMatrix n u w * fullCloneVector n t w) =
        t * fullCloneVector n t u := by
  rw [← fullMatrixAction, fullMatrixAction_eq_fullCloneAction]
  exact fullCloneAction_eigen n t ht hroot u

/-- Every cloned adjacency matrix admits an explicit strictly
positive eigenpair at the unique root t∈(1,2). -/
theorem exists_full_adjacency_positive_eigenpair (n : ℕ) :
    ∃ t : ℝ, 1 < t ∧ t < 2 ∧
      ∃ v : Vertex n → ℝ,
        (∀ u, 0 < v u) ∧
        (∀ u, ∑ w : Vertex n, fullAdjacencyMatrix n u w * v w =
          t * v u) := by
  obtain ⟨t, ht, ht2, hroot⟩ := finite_clone_root_exists n
  refine ⟨t, ht, ht2, fullCloneVector n t, ?_, ?_⟩
  · exact fun u => fullCloneVector_pos n t ht u
  · exact fun u => fullAdjacencyMatrix_eigen n t ht hroot u

end

end LoopsSpectral

import CloneRoot
import GraphWeightedBridge

/-!
# Full cloned-graph eigenpair, for every delay

The explicit five-vertex graph has vertex order
  e₀,...,eₙ,b,a,f₀,...,fₙ,c
and a directed cycle plus one shortcut eₙ→a.

This file constructs a strictly positive eigenvector of the *full*
(2n+5)-vertex row-source adjacency operator, for the unique real root
t>1 satisfying t^(2n+5)=t+1. The root comes from CloneRoot.lean.

The three local adjacency cases are the ordinary forward edge, the
two edges at eₙ, and the wrap edge at c. The next task is to identify
the operator with a sum over the independently verified Edge relation
and hence with an explicit finite Matrix.mulVec expression.

No Perron spectral-radius theorem is invoked in this module.
-/

namespace LoopsSpectral

open LoopsFormal.CloneGraph

noncomputable section

/-- For an admissible successor index, construct the next vertex. -/
def nextVertex (n : ℕ) (u : Vertex n)
    (h : u.val + 1 < size n) : Vertex n :=
  ⟨u.val + 1, h⟩

/-- The full row-source adjacency action written as its local
    outgoing-neighbor formula: ordinary successor, optional shortcut
    at eₙ, or wrap from the last vertex back to e₀. -/
def fullCloneAction (n : ℕ) (v : Vertex n → ℝ) (u : Vertex n) : ℝ :=
  if h : u.val + 1 < size n then
    v (nextVertex n u h) +
      (if u.val = n then v (afterTip n) else 0)
  else
    v (hub n)

/-- Explicit full eigenvector normalized to 1 at gate e₀:
    xᵢ=tⁱ before and including eₙ; xᵢ=tⁱ/(t+1)
    afterwards. -/
def fullCloneVector (n : ℕ) (t : ℝ) (u : Vertex n) : ℝ :=
  if u.val ≤ n then t ^ u.val else t ^ u.val / (t + 1)

/-- All coordinates of the full eigenvector are strictly positive. -/
theorem fullCloneVector_pos (n : ℕ) (t : ℝ)
    (ht : 1 < t) (u : Vertex n) :
    0 < fullCloneVector n t u := by
  have htpos : 0 < t := by linarith
  have hden : 0 < t + 1 := by linarith
  unfold fullCloneVector
  split_ifs
  · exact pow_pos htpos _
  · exact div_pos (pow_pos htpos _) hden

/-- Eigenvalue equation at every vertex for the full clone action.
    This statement is quantified over every n and every graph vertex. -/
theorem fullCloneAction_eigen (n : ℕ) (t : ℝ)
    (ht : 1 < t) (hroot : t ^ (2 * n + 5) = t + 1)
    (u : Vertex n) :
    fullCloneAction n (fullCloneVector n t) u =
      t * fullCloneVector n t u := by
  have htpos : 0 < t := by linarith
  have hden : t + 1 ≠ 0 := by linarith
  by_cases hnext : u.val + 1 < size n
  · by_cases htip : u.val = n
    · have hcur : u.val ≤ n := by omega
      have hnextlarge : ¬ u.val + 1 ≤ n := by omega
      have hsklarge : ¬ n + 2 ≤ n := by omega
      have hac :
          fullCloneAction n (fullCloneVector n t) u =
            t ^ (u.val + 1) / (t + 1) +
              t ^ (n + 2) / (t + 1) := by
        simp [fullCloneAction, hnext, fullCloneVector,
          nextVertex, afterTip, htip, hnextlarge, hsklarge]
      have htarget :
          t * fullCloneVector n t u = t * t ^ u.val := by
        simp [fullCloneVector, hcur]
      rw [hac, htarget, htip]
      rw [pow_succ]
      field_simp [hden] <;> ring
    · by_cases hlow : u.val < n
      · have hcur : u.val ≤ n := by omega
        have hnextlow : u.val + 1 ≤ n := by omega
        have hac :
            fullCloneAction n (fullCloneVector n t) u =
              t ^ (u.val + 1) := by
          simp [fullCloneAction, hnext, fullCloneVector,
            nextVertex, htip, hnextlow]
        have htarget :
            t * fullCloneVector n t u = t * t ^ u.val := by
          simp [fullCloneVector, hcur]
        rw [hac, htarget, pow_succ]
        ring
      · have hcur : ¬ u.val ≤ n := by omega
        have hnex : ¬ u.val + 1 ≤ n := by omega
        have hac :
            fullCloneAction n (fullCloneVector n t) u =
              t ^ (u.val + 1) / (t + 1) := by
          simp [fullCloneAction, hnext, fullCloneVector,
            nextVertex, htip, hnex]
        have htarget :
            t * fullCloneVector n t u =
              t * (t ^ u.val / (t + 1)) := by
          simp [fullCloneVector, hcur]
        rw [hac, htarget, pow_succ]
        ring
  · have hlast : u.val = 2 * n + 4 := by
      have hv := u.isLt
      dsimp [size] at *
      omega
    have hcur : ¬ u.val ≤ n := by omega
    have hac :
        fullCloneAction n (fullCloneVector n t) u = 1 := by
      simp [fullCloneAction, hnext, fullCloneVector, hub]
    have htarget :
        t * fullCloneVector n t u =
          t * (t ^ (2 * n + 4) / (t + 1)) := by
      simp [fullCloneVector, hcur, hlast]
    rw [hac, htarget]
    have hpow :
        t * t ^ (2 * n + 4) = t ^ (2 * n + 5) := by
      rw [pow_succ]
      ring
    calc
      (1 : ℝ) = (t + 1) / (t + 1) := by
        field_simp [hden]
      _ = t ^ (2 * n + 5) / (t + 1) := by rw [hroot]
      _ = t * (t ^ (2 * n + 4) / (t + 1)) := by
        rw [← hpow]
        ring

/-- At every delay there is some full-clone eigenvalue t∈(1,2)
with a *strictly positive coordinate eigenvector*. -/
theorem exists_full_clone_positive_eigenpair (n : ℕ) :
    ∃ t : ℝ, 1 < t ∧ t < 2 ∧
      ∃ v : Vertex n → ℝ,
        (∀ u, 0 < v u) ∧
        (∀ u, fullCloneAction n v u = t * v u) := by
  obtain ⟨t, ht, ht2, hroot⟩ := finite_clone_root_exists n
  refine ⟨t, ht, ht2, fullCloneVector n t, ?_, ?_⟩
  · exact fun u => fullCloneVector_pos n t ht u
  · exact fun u => fullCloneAction_eigen n t ht hroot u

end

end LoopsSpectral

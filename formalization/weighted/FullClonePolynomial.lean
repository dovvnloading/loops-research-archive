import FullCloneSpectralMax

/-!
# A hidden exact characteristic equation in the cloned graph

Every nonzero complex eigenpair of the *actual* full 0/1 adjacency
matrix satisfies μ^(2n+5) = μ+1. This is extracted directly from the
edge rows (cycle plus one shortcut), not postulated as an eigenvalue
hypothesis. In fact the hub coordinate of every nonzero eigenvector
is nonzero, and every eigenspace is determined by that one coordinate.

The polynomial identity is independent of the positive-root hypothesis,
and covers EVERY complex eigenvalue, including possible nonreal roots.
Nothing here asserts a theorem about a KKL native return matrix.
-/

namespace LoopsSpectral

open LoopsFormal.CloneGraph

noncomputable section

private def complexAction (n : ℕ) (z : Vertex n → ℂ)
    (u : Vertex n) : ℂ :=
  if h : u.val + 1 < size n then
    z (nextVertex n u h) +
      (if u.val = n then z (afterTip n) else 0)
  else
    z (hub n)

/-- Complexification of the *same* row-source 0/1 adjacency matrix:
the only exceptional row is the shortcut tip. -/
theorem complex_full_matrix_action (n : ℕ)
    (z : Vertex n → ℂ) (u : Vertex n) :
    (∑ w : Vertex n,
      ((fullAdjacencyMatrix n u w : ℝ) : ℂ) * z w) =
        complexAction n z u := by
  classical
  have hcast (w : Vertex n) :
      ((fullAdjacencyMatrix n u w : ℝ) : ℂ) * z w =
        (if Edge n u w then z w else 0) := by
    unfold fullAdjacencyMatrix
    split_ifs <;> simp
  calc
    (∑ w : Vertex n,
      ((fullAdjacencyMatrix n u w : ℝ) : ℂ) * z w) =
        ∑ w : Vertex n, if Edge n u w then z w else 0 := by
          apply Finset.sum_congr rfl
          intro w _
          exact hcast w
    _ = complexAction n z u := by
      by_cases hnext : u.val + 1 < size n
      · by_cases htip : u.val = n
        · have hneq : nextVertex n u hnext ≠ afterTip n := by
            intro h
            have hv := congrArg Fin.val h
            dsimp [nextVertex, afterTip] at hv
            omega
          calc
            (∑ w : Vertex n, if Edge n u w then z w else 0) =
              ∑ w : Vertex n,
                ((if w = nextVertex n u hnext then z w else 0) +
                 (if w = afterTip n then z w else 0)) := by
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
            _ = z (nextVertex n u hnext) + z (afterTip n) := by
              rw [Finset.sum_add_distrib]
              simp
            _ = complexAction n z u := by
              unfold complexAction
              rw [dif_pos hnext, if_pos htip]
        · calc
            (∑ w : Vertex n, if Edge n u w then z w else 0) =
              ∑ w : Vertex n,
                (if w = nextVertex n u hnext then z w else 0) := by
                apply Finset.sum_congr rfl
                intro w _
                simp only [edge_from_nonlast_iff n u w hnext]
                simp [htip]
            _ = z (nextVertex n u hnext) := by simp
            _ = complexAction n z u := by
              unfold complexAction
              rw [dif_pos hnext, if_neg htip]
              simp
      · calc
          (∑ w : Vertex n, if Edge n u w then z w else 0) =
            ∑ w : Vertex n, (if w = hub n then z w else 0) := by
            apply Finset.sum_congr rfl
            intro w _
            simp only [edge_from_last_iff n u w hnext]
          _ = z (hub n) := by simp
          _ = complexAction n z u := by simp [complexAction, hnext]

/-- An eigenvector obeys the plain one-step recurrence at every
non-shortcut, non-wrap position. -/
private theorem complex_succ
    (n : ℕ) (μ : ℂ) (z : Vertex n → ℂ)
    (hAz : ∀ u, (∑ w : Vertex n,
      ((fullAdjacencyMatrix n u w : ℝ) : ℂ) * z w) =
        μ * z u)
    (i : ℕ) (hi : i < size n) (hnext : i + 1 < size n)
    (hnot : i ≠ n) :
    z (⟨i + 1, hnext⟩ : Vertex n) =
      μ * z (⟨i, hi⟩ : Vertex n) := by
  have h := hAz (⟨i, hi⟩ : Vertex n)
  rw [complex_full_matrix_action] at h
  unfold complexAction at h
  rw [dif_pos hnext, if_neg hnot] at h
  simpa [nextVertex] using h

/-- All vertices strictly before and including the shortcut tip are
forced by the hub coordinate, for any complex eigenvalue. -/
theorem complex_eigen_prefix
    (n : ℕ) (μ : ℂ) (z : Vertex n → ℂ)
    (hAz : ∀ u, (∑ w : Vertex n,
      ((fullAdjacencyMatrix n u w : ℝ) : ℂ) * z w) =
        μ * z u) :
    ∀ j (hj : j ≤ n),
      z (⟨j, by dsimp [size]; omega⟩ : Vertex n) =
        μ ^ j * z (hub n) := by
  intro j
  induction j with
  | zero =>
      intro hj
      simp [hub]
  | succ j ih =>
      intro hj
      have hj0 : j ≤ n := by omega
      have hs : j < size n := by dsimp [size]; omega
      have ht : j + 1 < size n := by dsimp [size]; omega
      have hnot : j ≠ n := by omega
      have he := complex_succ n μ z hAz j hs ht hnot
      calc
        z (⟨j + 1, by dsimp [size]; omega⟩ : Vertex n) =
            μ * z (⟨j, hs⟩ : Vertex n) := by
              simpa using he
        _ = μ * (μ ^ j * z (hub n)) := by
              rw [ih hj0]
        _ = μ ^ (j + 1) * z (hub n) := by
              rw [pow_succ]
              ring

/-- Every vertex after the shortcut tip is determined by the
immediately following coordinate. -/
theorem complex_eigen_suffix
    (n : ℕ) (μ : ℂ) (z : Vertex n → ℂ)
    (hAz : ∀ u, (∑ w : Vertex n,
      ((fullAdjacencyMatrix n u w : ℝ) : ℂ) * z w) =
        μ * z u) :
    ∀ j (hj : j ≤ n + 3),
      z (⟨n + 1 + j, by dsimp [size]; omega⟩ : Vertex n) =
        μ ^ j *
          z (⟨n + 1, by dsimp [size]; omega⟩ : Vertex n) := by
  intro j
  induction j with
  | zero =>
      intro hj
      simp
  | succ j ih =>
      intro hj
      have hj0 : j ≤ n + 3 := by omega
      have hs : n + 1 + j < size n := by dsimp [size]; omega
      have ht : (n + 1 + j) + 1 < size n := by dsimp [size]; omega
      have hnot : n + 1 + j ≠ n := by omega
      have he := complex_succ n μ z hAz (n + 1 + j) hs ht hnot
      have he' :
          z (⟨n + 1 + (j + 1), by dsimp [size]; omega⟩ : Vertex n) =
            μ * z (⟨n + 1 + j, hs⟩ : Vertex n) := by
        simpa [Nat.add_assoc] using he
      calc
        z (⟨n + 1 + (j + 1), by dsimp [size]; omega⟩ : Vertex n) =
            μ * z (⟨n + 1 + j, hs⟩ : Vertex n) := he'
        _ = μ * (μ ^ j *
            z (⟨n + 1, by dsimp [size]; omega⟩ : Vertex n)) := by
              rw [ih hj0]
        _ = μ ^ (j + 1) *
            z (⟨n + 1, by dsimp [size]; omega⟩ : Vertex n) := by
              rw [pow_succ]
              ring

/-- The shortcut row gives a *single* matching equation between the
two ordinary chains. -/
theorem complex_eigen_shortcut
    (n : ℕ) (μ : ℂ) (z : Vertex n → ℂ)
    (hAz : ∀ u, (∑ w : Vertex n,
      ((fullAdjacencyMatrix n u w : ℝ) : ℂ) * z w) =
        μ * z u) :
    (μ + 1) * z (⟨n + 1, by dsimp [size]; omega⟩ : Vertex n) =
      μ ^ (n + 1) * z (hub n) := by
  have hn : n + 1 < size n := by dsimp [size]; omega
  have hs : n + 2 < size n := by dsimp [size]; omega
  have ht := hAz (tip n)
  rw [complex_full_matrix_action] at ht
  unfold complexAction at ht
  dsimp [tip] at ht
  rw [dif_pos hn, if_pos rfl] at ht
  change z (⟨n + 1, hn⟩ : Vertex n) + z (afterTip n) =
    μ * z (tip n) at ht
  have he := complex_succ n μ z hAz (n + 1) hn hs (by omega)
  have he' : z (afterTip n) =
      μ * z (⟨n + 1, hn⟩ : Vertex n) := by
    simpa [afterTip] using he
  calc
    (μ + 1) * z (⟨n + 1, by dsimp [size]; omega⟩ : Vertex n) =
        z (⟨n + 1, hn⟩ : Vertex n) +
          μ * z (⟨n + 1, hn⟩ : Vertex n) := by ring
    _ = z (⟨n + 1, hn⟩ : Vertex n) + z (afterTip n) := by
          rw [he']
    _ = μ * z (tip n) := ht
    _ = μ * (μ ^ n * z (hub n)) := by
          have hp := complex_eigen_prefix n μ z hAz n (le_refl n)
          simpa [tip] using congrArg (fun x : ℂ => μ * x) hp
    _ = μ ^ (n + 1) * z (hub n) := by rw [pow_succ]; ring

/-- The last row wraps to the hub, with exact suffix length n+3. -/
theorem complex_eigen_wrap
    (n : ℕ) (μ : ℂ) (z : Vertex n → ℂ)
    (hAz : ∀ u, (∑ w : Vertex n,
      ((fullAdjacencyMatrix n u w : ℝ) : ℂ) * z w) =
        μ * z u) :
    μ ^ (n + 4) *
      z (⟨n + 1, by dsimp [size]; omega⟩ : Vertex n) =
        z (hub n) := by
  have hl : ¬ ((lastVertex n).val + 1 < size n) := by
    dsimp [lastVertex]
    have hs : 0 < size n := by dsimp [size]; omega
    omega
  have hw := hAz (lastVertex n)
  rw [complex_full_matrix_action] at hw
  unfold complexAction at hw
  rw [dif_neg hl] at hw
  have hs := complex_eigen_suffix n μ z hAz (n + 3) (le_refl _)
  have hsame :
      (⟨n + 1 + (n + 3), by dsimp [size]; omega⟩ : Vertex n) =
        lastVertex n := by
    apply Fin.ext
    dsimp [lastVertex, size]
    omega
  rw [hsame] at hs
  calc
    μ ^ (n + 4) *
        z (⟨n + 1, by dsimp [size]; omega⟩ : Vertex n) =
        μ * (μ ^ (n + 3) *
          z (⟨n + 1, by dsimp [size]; omega⟩ : Vertex n)) := by
          rw [pow_succ]
          ring
    _ = μ * z (lastVertex n) := by rw [← hs]
    _ = z (hub n) := hw.symm

/-- Every row-source eigenvector obeys an exact polynomial identity
at the hub, before any nonvanishing argument. -/
theorem complex_eigen_polynomial_times_hub
    (n : ℕ) (μ : ℂ) (z : Vertex n → ℂ)
    (hAz : ∀ u, (∑ w : Vertex n,
      ((fullAdjacencyMatrix n u w : ℝ) : ℂ) * z w) =
        μ * z u) :
    μ ^ (2 * n + 5) * z (hub n) =
      (μ + 1) * z (hub n) := by
  have ht := complex_eigen_shortcut n μ z hAz
  have hw := complex_eigen_wrap n μ z hAz
  calc
    μ ^ (2 * n + 5) * z (hub n) =
        μ ^ (n + 4) * (μ ^ (n + 1) * z (hub n)) := by
          rw [show 2 * n + 5 = (n + 4) + (n + 1) by omega, pow_add]
          ring
    _ = μ ^ (n + 4) *
        ((μ + 1) * z (⟨n + 1, by dsimp [size]; omega⟩ : Vertex n)) := by
          rw [ht]
    _ = (μ + 1) * (μ ^ (n + 4) *
        z (⟨n + 1, by dsimp [size]; omega⟩ : Vertex n)) := by ring
    _ = (μ + 1) * z (hub n) := by rw [hw]

/-- A nonzero eigenvector cannot vanish at the hub, even if the
spectral parameter is 0 or -1. -/
theorem complex_eigen_hub_nonzero
    (n : ℕ) (μ : ℂ) (z : Vertex n → ℂ)
    (hAz : ∀ u, (∑ w : Vertex n,
      ((fullAdjacencyMatrix n u w : ℝ) : ℂ) * z w) =
        μ * z u)
    (hz : ∃ u, z u ≠ 0) :
    z (hub n) ≠ 0 := by
  intro hzero
  let mid : Vertex n := ⟨n + 1, by dsimp [size]; omega⟩
  have ht : (μ + 1) * z mid = 0 := by
    simpa [mid, hzero] using complex_eigen_shortcut n μ z hAz
  have hw : μ ^ (n + 4) * z mid = 0 := by
    simpa [mid, hzero] using complex_eigen_wrap n μ z hAz
  have hmid : z mid = 0 := by
    by_cases hm : μ + 1 = 0
    · have hμ : μ ≠ 0 := by
        intro h
        simp [h] at hm
      exact (mul_eq_zero.mp hw).resolve_left (pow_ne_zero _ hμ)
    · exact (mul_eq_zero.mp ht).resolve_left hm
  obtain ⟨u, hu⟩ := hz
  by_cases hleft : u.val ≤ n
  · have he := complex_eigen_prefix n μ z hAz u.val hleft
    have heq :
        (⟨u.val, by dsimp [size]; omega⟩ : Vertex n) = u :=
      Fin.ext rfl
    rw [heq, hzero, mul_zero] at he
    exact hu he
  · have hindex : u.val - (n + 1) ≤ n + 3 := by
      have hb := u.isLt
      dsimp [size] at hb
      omega
    have he := complex_eigen_suffix n μ z hAz
      (u.val - (n + 1)) hindex
    have heq :
        (⟨n + 1 + (u.val - (n + 1)),
          by dsimp [size]; omega⟩ : Vertex n) = u := by
      apply Fin.ext
      dsimp
      omega
    rw [heq] at he
    change z u = μ ^ (u.val - (n + 1)) * z mid at he
    rw [hmid, mul_zero] at he
    exact hu he

/-- The full graph's exact complex characteristic equation, obtained
from the actual adjacency eigenvector equations for ALL delays n. -/
theorem full_clone_complex_eigenvalue_polynomial
    (n : ℕ) (μ : ℂ) (z : Vertex n → ℂ)
    (hz : ∃ u, z u ≠ 0)
    (hAz : ∀ u, (∑ w : Vertex n,
      ((fullAdjacencyMatrix n u w : ℝ) : ℂ) * z w) =
        μ * z u) :
    μ ^ (2 * n + 5) = μ + 1 := by
  have hmul := complex_eigen_polynomial_times_hub n μ z hAz
  have h0 := complex_eigen_hub_nonzero n μ z hAz hz
  have hprod : (μ ^ (2 * n + 5) - (μ + 1)) * z (hub n) = 0 := by
    calc
      (μ ^ (2 * n + 5) - (μ + 1)) * z (hub n) =
        μ ^ (2 * n + 5) * z (hub n) -
          (μ + 1) * z (hub n) := by ring
      _ = 0 := sub_eq_zero.mpr hmul
  have hdiff : μ ^ (2 * n + 5) - (μ + 1) = 0 :=
    (mul_eq_zero.mp hprod).resolve_right h0
  exact sub_eq_zero.mp hdiff

#print axioms full_clone_complex_eigenvalue_polynomial

end

end LoopsSpectral

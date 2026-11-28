import FiberSamplePacking

/-!
# Sharp order of the radius factor

Uniform grids cover the nontrivial unit interval while the radius squared
times their unnormalized quadratic energy becomes arbitrarily small.
Consequently replacing the linear radius factor by its square cannot
force a compact connected set to be a singleton.
-/

namespace Loops.FiberSampling

open Set
open scoped BigOperators

/-- The grid with `n+1` sites on the unit interval. -/
noncomputable def intervalGrid (n : ℕ) (i : Fin (n + 1)) : ℝ :=
  (i.val : ℝ) / (n : ℝ)

/-- Every grid site lies in the unit interval when the denominator is
positive. -/
theorem intervalGrid_mem {n : ℕ} (hn : 0 < n) (i : Fin (n + 1)) :
    intervalGrid n i ∈ Icc (0 : ℝ) 1 := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hi : (i.val : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast (Nat.lt_succ_iff.mp i.isLt)
  constructor
  · exact div_nonneg (Nat.cast_nonneg i.val) hnR.le
  · change (i.val : ℝ) / (n : ℝ) ≤ 1
    apply (div_le_iff₀ hnR).2
    simpa using hi

/-- The mesh radius `1/n` covers the entire interval, not merely its
sample sites. The lower grid index is chosen by the natural floor. -/
theorem intervalGrid_cover {n : ℕ} (hn : 0 < n)
    (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    ∃ i : Fin (n + 1), dist x (intervalGrid n i) ≤ 1 / (n : ℝ) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hnx : 0 ≤ (n : ℝ) * x := mul_nonneg hnR.le hx.1
  let k : ℕ := ⌊(n : ℝ) * x⌋₊
  have hk : k ≤ n := by
    apply Nat.floor_le_of_le
    nlinarith [hx.2]
  let i : Fin (n + 1) := ⟨k, Nat.lt_succ_of_le hk⟩
  have hlo : (k : ℝ) ≤ (n : ℝ) * x := Nat.floor_le hnx
  have hhi : (n : ℝ) * x < (k : ℝ) + 1 :=
    Nat.lt_floor_add_one ((n : ℝ) * x)
  have hgrid : (k : ℝ) / (n : ℝ) ≤ x := by
    apply (div_le_iff₀ hnR).2
    nlinarith
  have hupper : x < ((k : ℝ) + 1) / (n : ℝ) := by
    apply (lt_div_iff₀ hnR).2
    nlinarith
  refine ⟨i, ?_⟩
  change dist x ((k : ℝ) / (n : ℝ)) ≤ 1 / (n : ℝ)
  rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hgrid)]
  rw [add_div] at hupper
  linarith

/-- A simple exact energy bound is sufficient for the order obstruction;
no asymptotic evaluation of the sum of squares is needed. -/
theorem intervalGrid_energy_le {n : ℕ} (hn : 0 < n) :
    energy (intervalGrid n) 0 ≤ (n : ℝ) + 1 := by
  classical
  unfold energy
  calc
    (∑ i : Fin (n + 1), dist (intervalGrid n i) 0 ^ 2) ≤
        ∑ _i : Fin (n + 1), (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      have hi := intervalGrid_mem hn i
      rw [Real.dist_eq, sub_zero, abs_of_nonneg hi.1]
      simpa using pow_le_pow_left₀ hi.1 hi.2 2
    _ = (n : ℝ) + 1 := by simp

/-- Arbitrarily fine covers of the whole unit interval can have
arbitrarily small radius-squared energy. -/
theorem unit_interval_quadratic_radius_certificates
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (N : ℕ) (s : Fin N → ℝ) (r : ℝ),
      0 < r ∧ r < ε ∧
      (∀ x ∈ Icc (0 : ℝ) 1, ∃ i, dist x (s i) ≤ r) ∧
      r ^ 2 * energy s 0 < ε := by
  obtain ⟨n, hn⟩ := exists_nat_gt (max (1 : ℝ) (2 / ε))
  have hn1 : (1 : ℝ) < (n : ℝ) :=
    (le_max_left _ _).trans_lt hn
  have hn2 : 2 / ε < (n : ℝ) :=
    (le_max_right _ _).trans_lt hn
  have hnR : 0 < (n : ℝ) := by linarith
  have hnN : 0 < n := by exact_mod_cast hnR
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
  have hr : 0 < 1 / (n : ℝ) := one_div_pos.mpr hnR
  have hr1 : 1 / (n : ℝ) ≤ 1 := by
    apply (div_le_iff₀ hnR).2
    linarith
  have htwo : 2 / (n : ℝ) < ε := by
    apply (div_lt_iff₀ hnR).2
    have h := (div_lt_iff₀ hε).1 hn2
    nlinarith
  have hsmall : 1 / (n : ℝ) < ε := by
    linarith
  have henergy : (1 / (n : ℝ)) ^ 2 * energy (intervalGrid n) 0 ≤
      2 / (n : ℝ) := by
    calc
      _ ≤ (1 / (n : ℝ)) ^ 2 * ((n : ℝ) + 1) :=
        mul_le_mul_of_nonneg_left (intervalGrid_energy_le hnN) (sq_nonneg _)
      _ = (1 / (n : ℝ)) * (1 + 1 / (n : ℝ)) := by
        field_simp
        <;> ring
      _ ≤ (1 / (n : ℝ)) * 2 := by
        exact mul_le_mul_of_nonneg_left (by linarith) hr.le
      _ = 2 / (n : ℝ) := by ring
  exact ⟨n + 1, intervalGrid n, 1 / (n : ℝ), hr, hsmall,
    fun x hx => intervalGrid_cover hnN x hx, henergy.trans_lt htwo⟩

/-- A compact preconnected non-singleton satisfies every proposed
radius-squared energy certificate. Thus that weakening of the linear
radius criterion is false even for an interval. -/
theorem quadratic_radius_weakening_counterexample :
    ∃ K : Set ℝ, IsCompact K ∧ IsPreconnected K ∧ ¬ K.Subsingleton ∧
      ∀ ε > 0, ∃ (N : ℕ) (s : Fin N → ℝ) (r : ℝ),
        0 < r ∧ r < ε ∧
        (∀ x ∈ K, ∃ i, dist x (s i) ≤ r) ∧
        r ^ 2 * energy s 0 < ε := by
  refine ⟨Icc (0 : ℝ) 1, isCompact_Icc, isPreconnected_Icc, ?_, ?_⟩
  · intro h
    have hzero : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
    have hone : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
    have hbad := h hzero hone
    norm_num at hbad
  · exact unit_interval_quadratic_radius_certificates

end Loops.FiberSampling

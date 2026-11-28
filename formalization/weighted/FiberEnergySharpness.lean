import FiberEnergyCollapse

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
    simpa using mul_le_mul_of_nonneg_left hx.2 hnR.le
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
  have hsmall : 1 / (n : ℝ) < ε :=
    (div_le_div_of_nonneg_right (show (1 : ℝ) ≤ 2 by norm_num) hnR.le).trans_lt htwo
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

/-- Connectedness is essential: the compact two-point set has arbitrarily
fine linear-radius energy certificates using its exact two samples. -/
theorem disconnected_fine_energy_counterexample :
    ∃ K : Set ℝ, IsCompact K ∧ FineEnergyCertificates K ∧
      ¬ K.Subsingleton := by
  refine ⟨{(0 : ℝ), 1},
    (isCompact_singleton : IsCompact ({(1 : ℝ)} : Set ℝ)).insert 0, ?_, ?_⟩
  · intro ε hε
    let s : Fin 2 → ℝ := fun i => if i = 0 then 0 else 1
    have henergy : energy s 0 = 1 := by
      norm_num [energy, Fin.sum_univ_two, s, Real.dist_eq]
    refine ⟨2, s, 0, ε / 2, by linarith, by linarith, ?_, ?_⟩
    · rw [henergy]
      linarith
    · intro z hz
      rcases Set.mem_insert_iff.mp hz with hz | hz
      · subst z
        refine ⟨0, ?_⟩
        simpa [s] using (show (0 : ℝ) ≤ ε / 2 by linarith)
      · have hz1 : z = 1 := Set.mem_singleton_iff.mp hz
        subst z
        refine ⟨1, ?_⟩
        simpa [s] using (show (0 : ℝ) ≤ ε / 2 by linarith)
  · intro h
    have hzero : (0 : ℝ) ∈ ({(0 : ℝ), 1} : Set ℝ) := by simp
    have hone : (1 : ℝ) ∈ ({(0 : ℝ), 1} : Set ℝ) := by simp
    have hbad := h hzero hone
    norm_num at hbad

/-- One copy of the interval grid and `n*(n+1)` repeated zero samples.
The padding changes the empirical normalization but not the cover. -/
noncomputable def paddedIntervalGrid (n : ℕ)
    (i : Fin (n + 1) × Fin (n + 1)) : ℝ :=
  if i.2 = 0 then intervalGrid n i.1 else 0

/-- Zero padding does not change the unnormalized quadratic energy. -/
theorem paddedIntervalGrid_energy (n : ℕ) :
    energy (paddedIntervalGrid n) 0 = energy (intervalGrid n) 0 := by
  classical
  have hterm (i j : Fin (n + 1)) :
      dist (paddedIntervalGrid n (i, j)) 0 ^ 2 =
        if j = 0 then dist (intervalGrid n i) 0 ^ 2 else 0 := by
    by_cases hj : j = 0 <;> simp [paddedIntervalGrid, hj]
  unfold energy
  rw [Fintype.sum_prod_type]
  simp_rw [hterm]
  simp

/-- The padded family still covers every point of the same interval. -/
theorem paddedIntervalGrid_cover {n : ℕ} (hn : 0 < n)
    (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    ∃ i : Fin (n + 1) × Fin (n + 1),
      dist x (paddedIntervalGrid n i) ≤ 1 / (n : ℝ) := by
  obtain ⟨i, hi⟩ := intervalGrid_cover hn x hx
  exact ⟨(i, 0), by simpa [paddedIntervalGrid] using hi⟩

/-- Empirical normalization hides the whole interval grid among the
repeated zeros. The denominator is the actual sample-index cardinality. -/
theorem paddedIntervalGrid_normalized_energy_le {n : ℕ} (hn : 0 < n) :
    energy (paddedIntervalGrid n) 0 /
        (Fintype.card (Fin (n + 1) × Fin (n + 1)) : ℝ) ≤
      1 / ((n : ℝ) + 1) := by
  rw [paddedIntervalGrid_energy]
  simp only [Fintype.card_prod, Fintype.card_fin,
    Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have hn1 : 0 < (n : ℝ) + 1 := by positivity
  have hn10 : (n : ℝ) + 1 ≠ 0 := ne_of_gt hn1
  calc
    energy (intervalGrid n) 0 / (((n : ℝ) + 1) * ((n : ℝ) + 1)) ≤
        ((n : ℝ) + 1) / (((n : ℝ) + 1) * ((n : ℝ) + 1)) :=
      div_le_div_of_nonneg_right (intervalGrid_energy_le hn) (by positivity)
    _ = 1 / ((n : ℝ) + 1) := by
      field_simp

/-- A fixed nontrivial connected interval has full covers of arbitrarily
small radius whose normalized second moment is also arbitrarily small.
Normalized concentration therefore cannot replace the unnormalized
radius-energy budget, even when full coverage is verified. -/
theorem unit_interval_normalized_energy_certificates
    (ε : ℝ) (hε : 0 < ε) :
    ∃ n : ℕ, 0 < n ∧ ∃ r : ℝ, 0 < r ∧ r < ε ∧
      (∀ x ∈ Icc (0 : ℝ) 1,
        ∃ i : Fin (n + 1) × Fin (n + 1),
          dist x (paddedIntervalGrid n i) ≤ r) ∧
      energy (paddedIntervalGrid n) 0 /
        (Fintype.card (Fin (n + 1) × Fin (n + 1)) : ℝ) < ε := by
  obtain ⟨n, hn⟩ := exists_nat_gt (max (1 : ℝ) (1 / ε))
  have hn1 : (1 : ℝ) < (n : ℝ) :=
    (le_max_left _ _).trans_lt hn
  have hn2 : 1 / ε < (n : ℝ) :=
    (le_max_right _ _).trans_lt hn
  have hnR : 0 < (n : ℝ) := by linarith
  have hnN : 0 < n := by exact_mod_cast hnR
  have hmul : 1 < (n : ℝ) * ε := (div_lt_iff₀ hε).1 hn2
  have hr : 0 < 1 / (n : ℝ) := one_div_pos.mpr hnR
  have hsmall : 1 / (n : ℝ) < ε := by
    apply (div_lt_iff₀ hnR).2
    nlinarith
  have hrecip : 1 / ((n : ℝ) + 1) < ε := by
    apply (div_lt_iff₀ (by positivity : 0 < (n : ℝ) + 1)).2
    nlinarith
  exact ⟨n, hnN, 1 / (n : ℝ), hr, hsmall,
    fun x hx => paddedIntervalGrid_cover hnN x hx,
    (paddedIntervalGrid_normalized_energy_le hnN).trans_lt hrecip⟩

end Loops.FiberSampling

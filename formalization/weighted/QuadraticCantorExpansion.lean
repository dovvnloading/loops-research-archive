import QuadraticCantorGeometry
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add

/-!
# Quantitative derivative expansion on the actual quadratic filled set

For `8 ≤ ‖c‖`, every bounded orbit stays uniformly away from the critical
point. The derivative of the genuine `n`-fold iterate has norm at least
`4^n`, and its squared norm is at least `(2*‖c‖)^n`. Every positive-period
point is consequently repelling; no expansion or periodic-point realization
is supplied as a hypothesis.
-/

namespace QuadraticCantor

open Set QuadraticEscape

theorem filled_iterate {c z : ℂ} (hz : z ∈ filled c) (n : ℕ) :
    orbit c n z ∈ filled c := by
  change escape c (orbit c n z) = 0
  rw [escape_iterate, show escape c z = 0 from hz, mul_zero]

theorem branchDisk_norm_lower {a z : ℂ} (hz : z ∈ branchDisk a) :
    ‖a‖/2 ≤ ‖z‖ := by
  change ‖z-a‖ ≤ ‖a‖/2 at hz
  have ht := norm_sub_le z (z-a)
  have he : z-(z-a) = a := by ring
  rw [he] at ht
  linarith

/-- The separation from the critical point retains the parameter's exact
root scale rather than just the constant lower bound one. -/
theorem filled_norm_lower {c a z : ℂ} (hc : 8 ≤ ‖c‖) (ha : a^2 = -c)
    (hz : z ∈ filled c) : ‖a‖/2 ≤ ‖z‖ := by
  rcases filled_disk_cover hc ha hz with h | h
  · exact branchDisk_norm_lower h
  · simpa only [norm_neg] using branchDisk_norm_lower h

theorem filled_norm_ge_one {c z : ℂ} (hc : 8 ≤ ‖c‖) (hz : z ∈ filled c) :
    1 ≤ ‖z‖ := by
  obtain ⟨a, ha⟩ := exists_center c
  have h := filled_norm_lower hc ha hz
  have ha' := center_norm_ge_two hc ha
  linarith

/-- The successor bound improves the separation obtained from the branch disks. -/
theorem filled_norm_sq_lower {c z : ℂ} (hc : 8 ≤ ‖c‖)
    (hz : z ∈ filled c) : ‖c‖/2 ≤ ‖z‖^2 := by
  have hb := norm_bound hc (filled_forward hz)
  have ht := norm_sub_le (z^2+c) (z^2)
  have he : (z^2+c)-z^2 = c := by ring
  rw [he, norm_pow] at ht
  linarith

theorem filled_norm_ge_two {c z : ℂ} (hc : 8 ≤ ‖c‖)
    (hz : z ∈ filled c) : 2 ≤ ‖z‖ := by
  apply (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 2) (norm_nonneg z)).mp
  have h := filled_norm_sq_lower hc hz
  nlinarith

/-- The spatial derivative product along the actual orbit. -/
def orbitMultiplier (c z : ℂ) : ℕ → ℂ
  | 0 => 1
  | n+1 => 2 * orbit c n z * orbitMultiplier c z n

theorem orbit_hasDerivAt (c z : ℂ) (n : ℕ) :
    HasDerivAt (orbit c n) (orbitMultiplier c z n) z := by
  induction n with
  | zero =>
    change HasDerivAt (id : ℂ → ℂ) 1 z
    exact hasDerivAt_id z
  | succ n ih =>
    have h := HasDerivAt.add (HasDerivAt.pow ih 2) (hasDerivAt_const z c)
    have he : orbit c (n+1) = (orbit c n)^2 + fun _ => c := by
      funext w
      simp only [orbit, Pi.pow_apply, Pi.add_apply]
    rw [he]
    simpa only [orbitMultiplier, Nat.cast_ofNat, Nat.reduceSub, pow_one,
      add_zero] using h

theorem orbit_deriv_eq (c z : ℂ) (n : ℕ) :
    deriv (orbit c n) z = orbitMultiplier c z n :=
  (orbit_hasDerivAt c z n).deriv

/-- Each factor of the derivative product is at least the root scale. -/
theorem orbitMultiplier_norm_lower {c a z : ℂ} (hc : 8 ≤ ‖c‖)
    (ha : a^2 = -c) (hz : z ∈ filled c) (n : ℕ) :
    ‖a‖^n ≤ ‖orbitMultiplier c z n‖ := by
  induction n with
  | zero => simp only [orbitMultiplier, pow_zero, norm_one, le_refl]
  | succ n ih =>
    have h := filled_norm_lower hc ha (filled_iterate hz n)
    have hf : ‖a‖ ≤ 2 * ‖orbit c n z‖ := by linarith
    rw [orbitMultiplier, norm_mul, norm_mul, Complex.norm_two, pow_succ]
    calc
      ‖a‖^n * ‖a‖ = ‖a‖ * ‖a‖^n := mul_comm _ _
      _ ≤ (2 * ‖orbit c n z‖) * ‖orbitMultiplier c z n‖ :=
        mul_le_mul hf ih (by positivity) (by positivity)

theorem deriv_norm_lower_center {c a z : ℂ} (hc : 8 ≤ ‖c‖)
    (ha : a^2 = -c) (hz : z ∈ filled c) (n : ℕ) :
    ‖a‖^n ≤ ‖deriv (orbit c n) z‖ := by
  rw [orbit_deriv_eq]
  exact orbitMultiplier_norm_lower hc ha hz n

/-- A root-independent quantitative expansion statement for every horizon. -/
theorem deriv_norm_sq_lower {c z : ℂ} (hc : 8 ≤ ‖c‖)
    (hz : z ∈ filled c) (n : ℕ) :
    ‖c‖^n ≤ ‖deriv (orbit c n) z‖^2 := by
  obtain ⟨a, ha⟩ := exists_center c
  have h := pow_le_pow_left₀ (by positivity : 0 ≤ ‖a‖^n)
    (deriv_norm_lower_center hc ha hz n) 2
  have he : (‖a‖^n)^2 = ‖c‖^n := by
    rw [← pow_mul, Nat.mul_comm n 2, pow_mul, center_norm_sq ha]
  rwa [he] at h

theorem deriv_norm_lower {c z : ℂ} (hc : 8 ≤ ‖c‖)
    (hz : z ∈ filled c) (n : ℕ) :
    (2 : ℝ)^n ≤ ‖deriv (orbit c n) z‖ := by
  obtain ⟨a, ha⟩ := exists_center c
  exact (pow_le_pow_left₀ (by norm_num) (center_norm_ge_two hc ha) n).trans
    (deriv_norm_lower_center hc ha hz n)

/-- Each actual squared derivative factor is at least `2*‖c‖`. -/
theorem orbitMultiplier_norm_sq_lower {c z : ℂ} (hc : 8 ≤ ‖c‖)
    (hz : z ∈ filled c) (n : ℕ) :
    (2*‖c‖)^n ≤ ‖orbitMultiplier c z n‖^2 := by
  induction n with
  | zero => simp only [orbitMultiplier, pow_zero, norm_one, one_pow, le_refl]
  | succ n ih =>
    have h := filled_norm_sq_lower hc (filled_iterate hz n)
    have hf : 2*‖c‖ ≤ 4*‖orbit c n z‖^2 := by linarith
    have he : ‖orbitMultiplier c z (n+1)‖^2 =
        (4*‖orbit c n z‖^2)*‖orbitMultiplier c z n‖^2 := by
      rw [orbitMultiplier, norm_mul, norm_mul, Complex.norm_two]
      ring
    calc
      (2*‖c‖)^(n+1) = (2*‖c‖)*(2*‖c‖)^n := by rw [pow_succ]; ring
      _ ≤ (4*‖orbit c n z‖^2)*‖orbitMultiplier c z n‖^2 :=
        mul_le_mul hf ih (by positivity) (by positivity)
      _ = ‖orbitMultiplier c z (n+1)‖^2 := he.symm

theorem deriv_norm_sq_lower_double_parameter {c z : ℂ} (hc : 8 ≤ ‖c‖)
    (hz : z ∈ filled c) (n : ℕ) :
    (2*‖c‖)^n ≤ ‖deriv (orbit c n) z‖^2 := by
  rw [orbit_deriv_eq]
  exact orbitMultiplier_norm_sq_lower hc hz n

theorem deriv_norm_lower_four {c z : ℂ} (hc : 8 ≤ ‖c‖)
    (hz : z ∈ filled c) (n : ℕ) :
    (4 : ℝ)^n ≤ ‖deriv (orbit c n) z‖ := by
  apply (sq_le_sq₀ (by positivity : 0 ≤ (4 : ℝ)^n) (norm_nonneg _)).mp
  have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 16)
    (by linarith : 16 ≤ 2*‖c‖) n
  have he : ((4 : ℝ)^n)^2 = (16 : ℝ)^n := by
    rw [← pow_mul, Nat.mul_comm n 2, pow_mul]
    norm_num
  rw [he]
  exact h.trans (deriv_norm_sq_lower_double_parameter hc hz n)

theorem deriv_norm_gt_one {c z : ℂ} (hc : 8 ≤ ‖c‖)
    (hz : z ∈ filled c) {n : ℕ} (hn : 0 < n) :
    1 < ‖deriv (orbit c n) z‖ :=
  (one_lt_pow₀ (by norm_num : (1 : ℝ) < 2) (Nat.ne_of_gt hn)).trans_le
    (deriv_norm_lower hc hz n)

/-- Periodicity itself forces zero escape potential, for every parameter. -/
theorem periodic_mem_filled {c z : ℂ} {p : ℕ} (hp : 0 < p)
    (hper : orbit c p z = z) : z ∈ filled c := by
  have h := escape_iterate c z p
  rw [hper] at h
  have hpow : 1 < (2 : ℝ)^p := one_lt_pow₀ (by norm_num) (Nat.ne_of_gt hp)
  change escape c z = 0
  have hmul : ((2 : ℝ)^p-1) * escape c z = 0 := by nlinarith
  exact (mul_eq_zero.mp hmul).resolve_left (by linarith)

/-- Every actual positive-period return is repelling in the stated range. -/
theorem periodic_repelling {c z : ℂ} (hc : 8 ≤ ‖c‖) {p : ℕ}
    (hp : 0 < p) (hper : orbit c p z = z) :
    1 < ‖deriv (orbit c p) z‖ :=
  deriv_norm_gt_one hc (periodic_mem_filled hp hper) hp

/-- This parameter range is unconditionally in the escaping-critical regime. -/
theorem critical_escape_pos {c : ℂ} (hc : 8 ≤ ‖c‖) :
    0 < escape c 0 := by
  by_contra h
  have hz : escape c 0 = 0 :=
    le_antisymm (le_of_not_gt h) (escape_nonneg c 0)
  have hb := filled_norm_ge_one (z := 0) hc hz
  norm_num at hb

theorem parameter_escape_pos {c : ℂ} (hc : 8 ≤ ‖c‖) :
    0 < parameterEscape c := by
  rw [parameterEscape_critical]
  exact mul_pos (by norm_num) (critical_escape_pos hc)

end QuadraticCantor

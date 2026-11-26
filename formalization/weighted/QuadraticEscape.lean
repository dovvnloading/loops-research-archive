import Mathlib

/-! Uniform escape-profile estimates for the actual quadratic map.
The two-sided one-step constant is sharp on every parameter ball. -/
namespace QuadraticEscape
open Filter Topology

noncomputable section

def orbit (c : ℂ) : ℕ → ℂ → ℂ
  | 0, z => z
  | n + 1, z => (orbit c n z)^2 + c

def size (z : ℂ) : ℝ := max 1 ‖z‖

def logSize (z : ℂ) : ℝ := Real.log (size z)

def weight (n : ℕ) : ℝ := (1 / 2 : ℝ)^n

def approx (c z : ℂ) (n : ℕ) : ℝ := weight n * logSize (orbit c n z)

theorem one_le_size (z : ℂ) : 1 ≤ size z := le_max_left _ _

theorem norm_le_size (z : ℂ) : ‖z‖ ≤ size z := le_max_right _ _

theorem size_pos (z : ℂ) : 0 < size z := lt_of_lt_of_le zero_lt_one (one_le_size z)

theorem logSize_nonneg (z : ℂ) : 0 ≤ logSize z := Real.log_nonneg (one_le_size z)

theorem weight_pos (n : ℕ) : 0 < weight n := by
  unfold weight
  positivity

theorem weight_succ (n : ℕ) : weight (n+1) = weight n / 2 := by
  unfold weight
  rw [pow_succ]
  ring

/-- No restriction on the starting point: both inequalities are valid across
the cutoff at norm one. -/
theorem size_step (c z : ℂ) {C : ℝ} (hc : ‖c‖ ≤ C) :
    size (z^2+c) ≤ (1+C) * size z ^ 2 ∧
    size z ^ 2 ≤ (1+C) * size (z^2+c) := by
  have C0 : 0 ≤ C := (norm_nonneg c).trans hc
  have hsq : ‖z‖^2 ≤ size z^2 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr (norm_le_size z))
      (add_nonneg (norm_nonneg z) (size_pos z).le)]
  have oneSq : 1 ≤ size z^2 := by nlinarith [one_le_size z]
  have hforward : ‖z^2+c‖ ≤ ‖z‖^2+C := by
    calc
      ‖z^2+c‖ ≤ ‖z^2‖+‖c‖ := norm_add_le _ _
      _ ≤ ‖z‖^2+C := by rw [norm_pow]; linarith
  have hback : ‖z‖^2 ≤ ‖z^2+c‖+C := by
    calc
      ‖z‖^2 = ‖(z^2+c)-c‖ := by rw [add_sub_cancel_right, norm_pow]
      _ ≤ ‖z^2+c‖+‖c‖ := norm_sub_le _ _
      _ ≤ _ := by linarith
  have hmul : C ≤ C * size z^2 := by
    simpa using mul_le_mul_of_nonneg_left oneSq C0
  have hmul' : C ≤ C * size (z^2+c) := by
    simpa using mul_le_mul_of_nonneg_left (one_le_size (z^2+c)) C0
  constructor
  · change max 1 ‖z^2+c‖ ≤ _
    apply max_le
    · nlinarith only [oneSq, hmul, C0]
    · nlinarith only [hforward, hsq, hmul]
  · by_cases hz : ‖z‖ ≤ 1
    · have hs : size z = 1 := max_eq_left hz
      rw [hs]
      nlinarith only [one_le_size (z^2+c), hmul', C0]
    · have hs : size z = ‖z‖ := max_eq_right (le_of_lt (lt_of_not_ge hz))
      rw [hs]
      nlinarith only [hback, norm_le_size (z^2+c), hmul']

/-- Sharp uniform log defect; no large-radius split or parameter-dependent
starting-point threshold is required. -/
theorem log_step (c z : ℂ) {C : ℝ} (hc : ‖c‖ ≤ C) :
    |logSize (z^2+c) - 2*logSize z| ≤ Real.log (1+C) := by
  have hC : 0 < 1+C := by linarith [norm_nonneg c]
  obtain ⟨h₁,h₂⟩ := size_step c z hc
  have l₁ := Real.log_le_log (size_pos (z^2+c)) h₁
  have l₂ := Real.log_le_log (pow_pos (size_pos z) 2) h₂
  rw [Real.log_mul hC.ne' (pow_ne_zero _ (size_pos z).ne'), Real.log_pow] at l₁
  rw [Real.log_pow, Real.log_mul hC.ne' (size_pos (z^2+c)).ne'] at l₂
  norm_num at l₁ l₂
  unfold logSize
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The upper defect is attained at z=1 and the real parameter C. -/
theorem log_step_sharp (C : ℝ) (hC : 0 ≤ C) :
    logSize ((1 : ℂ)^2+(C : ℂ)) - 2*logSize 1 = Real.log (1+C) := by
  have hs : size ((1 : ℂ)^2+(C : ℂ)) = 1+C := by
    have he : (1 : ℂ)^2+(C : ℂ) = ((1+C : ℝ) : ℂ) := by push_cast; ring
    rw [he]
    unfold size
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ 1+C)]
    exact max_eq_right (by linarith)
  have ho : size (1 : ℂ) = 1 := by simp [size]
  simp [logSize, hs, ho]

theorem approx_step (c z : ℂ) {C : ℝ} (hc : ‖c‖ ≤ C) (n : ℕ) :
    |approx c z (n+1) - approx c z n| ≤ weight (n+1)*Real.log (1+C) := by
  have h := log_step c (orbit c n z) hc
  have he : approx c z (n+1) - approx c z n =
      weight (n+1) * (logSize ((orbit c n z)^2+c) - 2*logSize (orbit c n z)) := by
    simp only [approx, orbit, weight_succ]
    ring
  rw [he, abs_mul, abs_of_pos (weight_pos (n+1))]
  exact mul_le_mul_of_nonneg_left h (weight_pos (n+1)).le

/-- Exact finite geometric tail, valid for every point of the complex plane. -/
theorem approx_tail (c z : ℂ) {C : ℝ} (hc : ‖c‖ ≤ C) (n k : ℕ) :
    |approx c z (n+k) - approx c z n| ≤
      (weight n - weight (n+k))*Real.log (1+C) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.add_succ]
    calc
      |approx c z (n+k+1) - approx c z n| =
          |(approx c z (n+k+1)-approx c z (n+k))+
            (approx c z (n+k)-approx c z n)| := by congr 1; ring
      _ ≤ _ := abs_add_le _ _
      _ ≤ weight (n+k+1)*Real.log (1+C) +
          (weight n-weight (n+k))*Real.log (1+C) :=
        add_le_add (approx_step c z hc (n+k)) ih
      _ = _ := by rw [weight_succ]; ring

theorem weight_tendsto : Tendsto weight atTop (𝓝 0) := by
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2)
    (by norm_num : (1/2:ℝ) < 1)

theorem approx_cauchy (c z : ℂ) : CauchySeq (approx c z) := by
  let L := Real.log (1+‖c‖)
  have L0 : 0 ≤ L := Real.log_nonneg (by linarith [norm_nonneg c])
  apply cauchySeq_of_le_tendsto_0' (fun n => weight n * L)
  · intro n m hnm
    obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hnm
    rw [dist_comm, Real.dist_eq]
    exact (approx_tail c z le_rfl n k).trans (by
      dsimp [L] at *
      have hh := mul_nonneg (weight_pos (n+k)).le L0
      linarith only [hh])
  · simpa using weight_tendsto.mul (tendsto_const_nhds (x := L))

theorem exists_escape (c z : ℂ) : ∃ g : ℝ, Tendsto (approx c z) atTop (𝓝 g) :=
  cauchySeq_tendsto_of_complete (approx_cauchy c z)

def escape (c z : ℂ) : ℝ := Classical.choose (exists_escape c z)

theorem escape_tendsto (c z : ℂ) : Tendsto (approx c z) atTop (𝓝 (escape c z)) :=
  Classical.choose_spec (exists_escape c z)

/-- Explicit uniform error with the optimal one-step constant. -/
theorem escape_error (c z : ℂ) {C : ℝ} (hc : ‖c‖ ≤ C) (n : ℕ) :
    |approx c z n - escape c z| ≤ weight n * Real.log (1+C) := by
  have hL : 0 ≤ Real.log (1+C) := Real.log_nonneg (by linarith [norm_nonneg c])
  have hlim : Tendsto (fun m => |approx c z m - approx c z n|)
      atTop (𝓝 |escape c z - approx c z n|) :=
    ((escape_tendsto c z).sub tendsto_const_nhds).abs
  have hb : ∀ᶠ m in atTop, |approx c z m - approx c z n| ≤
      weight n * Real.log (1+C) := by
    apply eventually_atTop.mpr
    refine ⟨n, ?_⟩
    intro m hm
    obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hm
    exact (approx_tail c z hc n k).trans (by
      have hh := mul_nonneg (weight_pos (n+k)).le hL
      linarith only [hh])
  rw [abs_sub_comm]
  exact le_of_tendsto hlim hb

end
end QuadraticEscape

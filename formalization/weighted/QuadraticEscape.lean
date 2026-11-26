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
  have hsq : ‖z‖^2 ≤ size z^2 :=
    pow_le_pow_left₀ (norm_nonneg z) (norm_le_size z) 2
  have oneSq : 1 ≤ size z^2 := by
    simpa using pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) (one_le_size z) 2
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
            (approx c z (n+k)-approx c z n)| := by congr 1 <;> ring
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
      nlinarith only [hh])
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

/-- All finite escape approximants, and hence their limit, are nonnegative. -/
theorem approx_nonneg (c z : ℂ) (n : ℕ) : 0 ≤ approx c z n :=
  mul_nonneg (weight_pos n).le (logSize_nonneg _)

theorem escape_nonneg (c z : ℂ) : 0 ≤ escape c z :=
  ge_of_tendsto (escape_tendsto c z) (Eventually.of_forall (approx_nonneg c z))

/-- Orbit shifting concerns the genuine quadratic iterates, not a clock model. -/
theorem orbit_shift (c z : ℂ) (n : ℕ) :
    orbit c n (z^2+c) = orbit c (n+1) z := by
  induction n with
  | zero => simp [orbit]
  | succ n ih => simp only [orbit, ih]

theorem approx_shift (c z : ℂ) (n : ℕ) :
    approx c (z^2+c) n = 2*approx c z (n+1) := by
  unfold approx
  rw [orbit_shift, weight_succ]
  ring

/-- The exact Green scaling equation for the limit defined from actual iterates. -/
theorem escape_step (c z : ℂ) : escape c (z^2+c) = 2*escape c z := by
  have hs : Tendsto (fun n : ℕ => approx c z (n+1)) atTop (𝓝 (escape c z)) :=
    (tendsto_add_atTop_iff_nat 1).2 (escape_tendsto c z)
  have ht : Tendsto (fun n : ℕ => 2*approx c z (n+1)) atTop (𝓝 (2*escape c z)) :=
    tendsto_const_nhds.mul hs
  have hfun : (fun n : ℕ => 2*approx c z (n+1)) = approx c (z^2+c) :=
    funext fun n => (approx_shift c z n).symm
  rw [hfun] at ht
  exact tendsto_nhds_unique (escape_tendsto c (z^2+c)) ht

theorem escape_iterate (c z : ℂ) (n : ℕ) :
    escape c (orbit c n z) = (2:ℝ)^n * escape c z := by
  induction n with
  | zero => simp [orbit]
  | succ n ih =>
    rw [orbit, escape_step, ih, pow_succ]
    ring

/-- Zero escape rate forces a single uniform bound on the entire actual orbit. -/
theorem escape_zero_orbit_bound (c z : ℂ) (hz : escape c z = 0) (n : ℕ) :
    ‖orbit c n z‖ ≤ 1+‖c‖ := by
  have h := escape_error c z (le_refl ‖c‖) n
  rw [hz, sub_zero, abs_of_nonneg (approx_nonneg c z n)] at h
  unfold approx at h
  have hl := (mul_le_mul_left₀ (weight_pos n)).mp h
  have hsize : size (orbit c n z) ≤ 1+‖c‖ :=
    (Real.log_le_log_iff (size_pos _) (by positivity)).mp hl
  exact (norm_le_size _).trans hsize

/-- The zero locus of the actual limiting potential equals the bounded-orbit
locus, with no appeal to a pre-existing Green function. -/
theorem escape_zero_iff_bounded (c z : ℂ) :
    escape c z = 0 ↔ ∃ B : ℝ, ∀ n : ℕ, ‖orbit c n z‖ ≤ B := by
  constructor
  · intro hz
    exact ⟨1+‖c‖, escape_zero_orbit_bound c z hz⟩
  · rintro ⟨B,hB⟩
    let L := Real.log (max 1 B)
    have hupper (n : ℕ) : approx c z n ≤ weight n * L := by
      unfold approx logSize L
      apply mul_le_mul_of_nonneg_left _ (weight_pos n).le
      apply Real.log_le_log (size_pos _)
      exact max_le_max le_rfl (hB n)
    have ht : Tendsto (fun n => weight n * L) atTop (𝓝 0) := by
      simpa using weight_tendsto.mul (tendsto_const_nhds (x := L))
    exact le_antisymm (le_of_tendsto_of_tendsto' (escape_tendsto c z) ht hupper)
      (escape_nonneg c z)

/-- This yields a finite escape test with a parameter-dependent exact safe
radius. The converse is also proved: positive escape forces such a crossing. -/
theorem escape_pos_iff_crossing (c z : ℂ) :
    0 < escape c z ↔ ∃ n : ℕ, 1+‖c‖ < ‖orbit c n z‖ := by
  constructor
  · intro hp
    by_contra h
    push_neg at h
    have hz := (escape_zero_iff_bounded c z).mpr ⟨1+‖c‖, h⟩
    linarith
  · rintro ⟨n, hn⟩
    by_contra h
    have hz : escape c z = 0 := le_antisymm (le_of_not_gt h) (escape_nonneg c z)
    exact (not_le_of_gt hn) (escape_zero_orbit_bound c z hz n)

/-- Uniform convergence on every bounded parameter region, without any
bound on the starting point. -/
theorem escape_uniform (C : ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ c z : ℂ, ‖c‖ ≤ C →
      |approx c z n - escape c z| < ε := by
  have ht : Tendsto (fun n => weight n * Real.log (1+C)) atTop (𝓝 0) := by
    simpa using weight_tendsto.mul (tendsto_const_nhds (x := Real.log (1+C)))
  have he := ht.eventually (gt_mem_nhds hε)
  obtain ⟨N,hN⟩ := eventually_atTop.mp he
  exact ⟨N, fun n hn c z hc => (escape_error c z hc n).trans_lt (hN n hn)⟩

/-- Parameter potential in the normalization G(c)=g_c(c)=2 g_c(0). -/
def parameterEscape (c : ℂ) : ℝ := escape c c

theorem parameterEscape_critical (c : ℂ) :
    parameterEscape c = 2 * escape c 0 := by
  simpa [parameterEscape] using escape_step c 0

theorem parameterEscape_zero_iff (c : ℂ) :
    parameterEscape c = 0 ↔ ∃ B : ℝ, ∀ n : ℕ, ‖orbit c n 0‖ ≤ B := by
  rw [parameterEscape_critical]
  constructor
  · intro h
    exact (escape_zero_iff_bounded c 0).mp (by linarith)
  · intro h
    rw [(escape_zero_iff_bounded c 0).mpr h, mul_zero]


end
end QuadraticEscape

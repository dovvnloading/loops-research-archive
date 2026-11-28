import ParentWaveElliptic
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.FDeriv.Analytic

namespace ParentWaveElliptic

open Set Complex Metric Filter
open scoped Topology

noncomputable section

def upperHalfPlane : Set ℂ := {z | 0 < z.im}

theorem upperHalfPlane_open : IsOpen upperHalfPlane :=
  isOpen_lt continuous_const Complex.continuous_im

def upperMap (a : ℝ) (G : ℂ → ℂ) (z : ℂ) : ℂ := G (Complex.sqrt (z-(a:ℂ)))

def upperDifferential (a b c : ℝ) (z : ℂ) : ℂ :=
  (Complex.sqrt (z-(a:ℂ)) * Complex.sqrt (z-(b:ℂ)) * Complex.sqrt (z-(c:ℂ)))⁻¹

private theorem complex_sqrt_sq (z : ℂ) : (Complex.sqrt z)^2 = z := by
  rw [Complex.sqrt, ← Complex.cpow_nat_mul]
  norm_num

private theorem complex_sqrt_nonzero {z : ℂ} (hz : z ≠ 0) : Complex.sqrt z ≠ 0 := by
  intro h
  have he := complex_sqrt_sq z
  exact hz (by simpa [h] using he.symm)

theorem sqrt_sub_mem_quadrant (a : ℝ) {z : ℂ} (hz : z ∈ upperHalfPlane) :
    Complex.sqrt (z-(a:ℂ)) ∈ quadrant := by
  have hp : 0 < (z-(a:ℂ)).im := by simpa [upperHalfPlane] using hz
  have hn : |(z-(a:ℂ)).re| < ‖z-(a:ℂ)‖ := Complex.abs_re_lt_norm.mpr hp.ne'
  have hpos : 0 < (‖z-(a:ℂ)‖ + (z-(a:ℂ)).re) / 2 := by
    linarith [neg_abs_le (z-(a:ℂ)).re]
  have hneg : 0 < (‖z-(a:ℂ)‖ - (z-(a:ℂ)).re) / 2 := by
    linarith [le_abs_self (z-(a:ℂ)).re]
  change 0 < (Complex.sqrt _).re ∧ 0 < (Complex.sqrt _).im
  simp only [Complex.sqrt, Complex.cpow_inv_two_re,
    Complex.cpow_inv_two_im_eq_sqrt hp.le]
  exact ⟨Real.sqrt_pos.2 hpos, Real.sqrt_pos.2 hneg⟩

private theorem sub_real_nonzero (a : ℝ) {z : ℂ} (hz : z ∈ upperHalfPlane) :
    z-(a:ℂ) ≠ 0 := by
  intro h
  have hh := congrArg Complex.im h
  have hp : 0 < z.im := hz
  simp only [Complex.sub_im, Complex.ofReal_im, sub_zero, Complex.zero_im] at hh
  linarith

theorem sqrt_sub_hasDeriv (a : ℝ) {z : ℂ} (hz : z ∈ upperHalfPlane) :
    HasDerivAt (fun z : ℂ => Complex.sqrt (z-(a:ℂ)))
      (2*Complex.sqrt (z-(a:ℂ)))⁻¹ z := by
  have hslit : z-(a:ℂ) ∈ Complex.slitPlane :=
    Or.inr (by simpa using (show z.im ≠ 0 from (show 0 < z.im from hz).ne'))
  have hn := complex_sqrt_nonzero (sub_real_nonzero a hz)
  have hd : HasStrictDerivAt Complex.sqrt (2*Complex.sqrt (z-(a:ℂ)))⁻¹ (z-(a:ℂ)) := by
    apply HasStrictDerivAt.of_local_left_inverse
    · exact (Complex.differentiableAt_sqrt hslit).continuousAt
    · simpa using hasStrictDerivAt_pow 2 (Complex.sqrt (z-(a:ℂ)))
    · exact mul_ne_zero (by norm_num) hn
    · exact Filter.Eventually.of_forall complex_sqrt_sq
  simpa only [Function.comp_def, id_eq, mul_one] using!
    hd.hasDerivAt.comp z ((hasDerivAt_id z).sub_const (a:ℂ))

theorem upperMap_hasDeriv (a b c : ℝ) {G : ℂ → ℂ}
    (hG : ∀ t ∈ quadrant, HasDerivAt G (differential (b-a) (c-a) t) t)
    {z : ℂ} (hz : z ∈ upperHalfPlane) :
    HasDerivAt (upperMap a G) (upperDifferential a b c z) z := by
  have hd := (hG _ (sqrt_sub_mem_quadrant a hz)).comp z (sqrt_sub_hasDeriv a hz)
  have hB : (Complex.sqrt (z-(a:ℂ)))^2-((b-a:ℝ):ℂ) = z-(b:ℂ) := by
    rw [complex_sqrt_sq, Complex.ofReal_sub]
    ring
  have hC : (Complex.sqrt (z-(a:ℂ)))^2-((c-a:ℝ):ℂ) = z-(c:ℂ) := by
    rw [complex_sqrt_sq, Complex.ofReal_sub]
    ring
  convert! hd using 1
  rw [differential,hB,hC,upperDifferential]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

theorem upperMap_injective (a b c : ℝ) {G : ℂ → ℂ}
    (hG : ∀ t ∈ quadrant, HasDerivAt G (differential (b-a) (c-a) t) t) :
    InjOn (upperMap a G) upperHalfPlane := by
  intro z hz w hw he
  have hs := primitive_injective (b-a) (c-a) hG
    (sqrt_sub_mem_quadrant a hz) (sqrt_sub_mem_quadrant a hw) he
  have heq := congrArg (fun u : ℂ => u^2) hs
  simpa only [complex_sqrt_sq, sub_left_inj] using heq

theorem upperDifferential_sq (a b c : ℝ) (z : ℂ) :
    (upperDifferential a b c z)^2 =
      ((z-(a:ℂ))*(z-(b:ℂ))*(z-(c:ℂ)))⁻¹ := by
  simp only [upperDifferential, inv_pow, mul_pow, complex_sqrt_sq]

theorem upperDifferential_norm_sq (a b c : ℝ) (z : ℂ) :
    ‖upperDifferential a b c z‖^2 =
      ‖((z-(a:ℂ))*(z-(b:ℂ))*(z-(c:ℂ)))⁻¹‖ := by
  rw [← norm_pow, upperDifferential_sq]

theorem upperDifferential_nonzero (a b c : ℝ) {z : ℂ} (hz : z ∈ upperHalfPlane) :
    upperDifferential a b c z ≠ 0 := by
  apply inv_ne_zero
  exact mul_ne_zero
    (mul_ne_zero (complex_sqrt_nonzero (sub_real_nonzero a hz))
      (complex_sqrt_nonzero (sub_real_nonzero b hz)))
    (complex_sqrt_nonzero (sub_real_nonzero c hz))

end
end ParentWaveElliptic

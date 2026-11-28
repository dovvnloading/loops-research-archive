import QuadraticTwinReal

/-!
# Parameter rigidity from two quadratic equations and real-axis continuity

The two maps are the actual quadratics z ↦ z²+c and z ↦ z²+c+1.
A simultaneous intertwining function need be continuous only on the real axis.
No global continuity, injectivity, surjectivity, or normalization is assumed.

The parameter is determined up to complex conjugation.  The companion module
QuadraticTwinMLC turns this alternative into a singleton-fiber theorem and an
actual Mandelbrot connected-neighborhood-basis conclusion.
-/

namespace QuadraticTwinSemiconjugacy

noncomputable section

/-- Comparing the two actual quadratic generators forces unit covariance. -/
theorem unit_translation {c d : ℂ} (h : ℂ → ℂ)
    (hquad : ∀ z : ℂ, h (z ^ 2 + c) = h z ^ 2 + d)
    (htwin : ∀ z : ℂ, h (z ^ 2 + c + 1) = h z ^ 2 + d + 1)
    (w : ℂ) : h (w + 1) = h w + 1 := by
  obtain ⟨z, hz⟩ :=
    IsAlgClosed.exists_pow_nat_eq (w - c) (by norm_num : 0 < (2 : ℕ))
  have hzw : z ^ 2 + c = w := by
    rw [hz]
    ring
  calc
    h (w + 1) = h (z ^ 2 + c + 1) := by rw [hzw]
    _ = h z ^ 2 + d + 1 := htwin z
    _ = h (z ^ 2 + c) + 1 := by rw [hquad]
    _ = h w + 1 := by rw [hzw]

/-- Real-axis fixing and the quadratic equation identify the critical value. -/
theorem maps_parameter {c d : ℂ} (h : ℂ → ℂ)
    (hquad : ∀ z : ℂ, h (z ^ 2 + c) = h z ^ 2 + d)
    (hreal : ∀ x : ℝ, h (x : ℂ) = (x : ℂ)) : h c = d := by
  have hzero : h 0 = 0 := by simpa using hreal 0
  simpa [hzero] using hquad 0

/-- The real critical line maps to the horizontal line through the critical
value, and integer covariance extends that identity to the whole line. -/
theorem critical_line {c d : ℂ} (h : ℂ → ℂ)
    (hquad : ∀ z : ℂ, h (z ^ 2 + c) = h z ^ 2 + d)
    (hunit : ∀ z : ℂ, h (z + 1) = h z + 1)
    (hreal : ∀ x : ℝ, h (x : ℂ) = (x : ℂ))
    (t : ℝ) : h (c + (t : ℂ)) = d + (t : ℂ) := by
  have hnonneg (s : ℝ) (hs : 0 ≤ s) :
      h (c + (s : ℂ)) = d + (s : ℂ) := by
    have hsquare : (Real.sqrt s : ℂ) ^ 2 = (s : ℂ) := by
      exact_mod_cast Real.sq_sqrt hs
    have hh := hquad (Real.sqrt s : ℂ)
    rw [hreal, hsquare] at hh
    simpa only [add_comm] using hh
  obtain ⟨n, hn⟩ := exists_nat_gt (-t)
  have hpos : 0 ≤ t + (n : ℝ) := by linarith
  have h1 := hnonneg (t + (n : ℝ)) hpos
  have h2 := QuadraticTwinReal.integer_covariance h hunit
    (c + (t : ℂ)) (n : ℤ)
  push_cast at h1 h2
  rw [show c + ((t : ℂ) + (n : ℂ)) =
    (c + (t : ℂ)) + (n : ℂ) by ring] at h1
  linear_combination h1 - h2

/-- Values on the imaginary axis satisfy an exact quadratic equation. -/
theorem imaginary_square {c d : ℂ} (h : ℂ → ℂ)
    (hquad : ∀ z : ℂ, h (z ^ 2 + c) = h z ^ 2 + d)
    (hunit : ∀ z : ℂ, h (z + 1) = h z + 1)
    (hreal : ∀ x : ℝ, h (x : ℂ) = (x : ℂ))
    (y : ℝ) : h ((y : ℂ) * Complex.I) ^ 2 = -(y : ℂ) ^ 2 := by
  have harg : ((y : ℂ) * Complex.I) ^ 2 + c =
      c + ((-y ^ 2 : ℝ) : ℂ) := by
    push_cast
    rw [mul_pow, Complex.I_sq]
    ring
  have hh := hquad ((y : ℂ) * Complex.I)
  rw [harg, critical_line h hquad hunit hreal] at hh
  push_cast at hh
  linear_combination -hh

/-- Rigidity of the actual quadratic parameter under two exact intertwining
equations.  Regularity is required only on the real axis, so a linking
homeomorphism or a globally continuous map is not an implicit premise. -/
theorem parameter_eq_or_conj {c d : ℂ} (h : ℂ → ℂ)
    (hcont : Continuous (fun x : ℝ => h (x : ℂ)))
    (hquad : ∀ z : ℂ, h (z ^ 2 + c) = h z ^ 2 + d)
    (htwin : ∀ z : ℂ, h (z ^ 2 + c + 1) = h z ^ 2 + d + 1) :
    d = c ∨ d = star c := by
  have hunit := unit_translation h hquad htwin
  have hreal := QuadraticTwinReal.fixes_real h c d hcont hquad hunit
  let y : ℝ := -c.im / 2
  let v : ℂ := h ((y : ℂ) * Complex.I)
  have hv : v ^ 2 = -(y : ℂ) ^ 2 :=
    imaginary_square h hquad hunit hreal y
  have hcross : (1 + (y : ℂ) * Complex.I) ^ 2 + c =
      ((1 - y ^ 2 + c.re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [pow_two, y] <;> ring
  have hu : h (1 + (y : ℂ) * Complex.I) = 1 + v := by
    simpa [v, add_comm] using hunit ((y : ℂ) * Complex.I)
  have hh := hquad (1 + (y : ℂ) * Complex.I)
  rw [hcross, hreal, hu] at hh
  push_cast at hh
  have hd : (c.re : ℂ) = d + 2 * v := by
    linear_combination hh + hv
  have hs : (d - (c.re : ℂ)) ^ 2 + (c.im : ℂ) ^ 2 = 0 := by
    calc
      (d - (c.re : ℂ)) ^ 2 + (c.im : ℂ) ^ 2 =
          4 * v ^ 2 + (c.im : ℂ) ^ 2 := by rw [hd]; ring
      _ = -4 * (y : ℂ) ^ 2 + (c.im : ℂ) ^ 2 := by rw [hv]; ring
      _ = 0 := by dsimp [y]; push_cast; ring
  have hfactor : (d - c) * (d - star c) =
      (d - (c.re : ℂ)) ^ 2 + (c.im : ℂ) ^ 2 := by
    apply Complex.ext <;> simp [pow_two] <;> ring
  have hzero : (d - c) * (d - star c) = 0 := hfactor.trans hs
  rcases mul_eq_zero.mp hzero with hleft | hright
  · exact Or.inl (sub_eq_zero.mp hleft)
  · exact Or.inr (sub_eq_zero.mp hright)

/-- A globally continuous simultaneous semiconjugacy is a special case of
the stronger real-axis-only parameter theorem. -/
theorem parameter_eq_or_conj_of_continuous {c d : ℂ} (h : ℂ → ℂ)
    (hcont : Continuous h)
    (hquad : ∀ z : ℂ, h (z ^ 2 + c) = h z ^ 2 + d)
    (htwin : ∀ z : ℂ, h (z ^ 2 + c + 1) = h z ^ 2 + d + 1) :
    d = c ∨ d = star c := by
  exact parameter_eq_or_conj h (hcont.comp Complex.continuous_ofReal) hquad htwin

end

end QuadraticTwinSemiconjugacy

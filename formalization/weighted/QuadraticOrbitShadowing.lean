import QuadraticShadowRadius

/-!
# Uniform quadratic orbit shadowing

The norm-two specialization of the separation-dependent inverse estimate
has error at most the parameter displacement. The general construction
and compactness argument are in `QuadraticShadowRadius`.
-/

namespace QuadraticCantor

open Set QuadraticEscape

noncomputable section

/-- Of the two square roots, one gives an inverse error at most half
the target error whenever the reference point has norm at least two. -/
theorem quadratic_preimage_near (x w : ℂ) (hx : 2 ≤ ‖x‖) :
    ∃ z : ℂ, z^2 = w ∧ 2 * ‖z-x‖ ≤ ‖w-x^2‖ := by
  obtain ⟨z, hz, hcontrol⟩ := quadratic_preimage_norm_control x w
  exact ⟨z, hz,
    (mul_le_mul_of_nonneg_right hx (norm_nonneg _)).trans hcontrol⟩

/-- Every finite segment of a separated reference orbit has an actual
backward lift for the new parameter with the same uniform error budget. -/
theorem finite_orbit_shadow (c d z : ℂ)
    (hsep : ∀ n : ℕ, 2 ≤ ‖orbit c n z‖) (N : ℕ) :
    ∃ w : ℂ, ∀ n ≤ N, ‖orbit d n w-orbit c n z‖ ≤ ‖d-c‖ := by
  exact finite_orbit_shadow_budget c d z 2 ‖d-c‖ (by norm_num)
    (norm_nonneg _) hsep (by norm_num) N

/-- A single initial point realizes the error bound for every time.
No coherence of independently chosen finite roots is assumed. -/
theorem infinite_orbit_shadow (c d z : ℂ)
    (hsep : ∀ n : ℕ, 2 ≤ ‖orbit c n z‖) :
    ∃ w : ℂ, ∀ n : ℕ, ‖orbit d n w-orbit c n z‖ ≤ ‖d-c‖ := by
  exact infinite_orbit_shadow_budget c d z 2 ‖d-c‖ (by norm_num)
    (norm_nonneg _) hsep (by norm_num)

/-- A bounded separated reference orbit is shadowed by an orbit in the
genuine filled set of every new parameter, uniformly for all times. -/
theorem filled_orbit_shadow (c d z : ℂ) (hz : z ∈ filled c)
    (hsep : ∀ n : ℕ, 2 ≤ ‖orbit c n z‖) :
    ∃ w : ℂ, w ∈ filled d ∧
      ∀ n : ℕ, ‖orbit d n w-orbit c n z‖ ≤ ‖d-c‖ := by
  exact filled_orbit_shadow_budget c d z 2 ‖d-c‖ (by norm_num)
    (norm_nonneg _) hz hsep (by norm_num)

/-- Every actual bounded orbit at a parameter of norm at least eight
has a uniformly close bounded shadow at any other complex parameter. -/
theorem large_parameter_orbit_shadow (c d z : ℂ) (hc : 8 ≤ ‖c‖)
    (hz : z ∈ filled c) :
    ∃ w : ℂ, w ∈ filled d ∧
      ∀ n : ℕ, ‖orbit d n w-orbit c n z‖ ≤ ‖d-c‖ := by
  exact filled_orbit_shadow c d z hz
    (fun n => filled_norm_ge_two hc (filled_iterate hz n))

end

end QuadraticCantor

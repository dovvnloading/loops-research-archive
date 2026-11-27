import ParabolicPassageEstimate

/-!
# Uniform accuracy for the physical parabolic passage

For each requested relative accuracy, a single positive central radius
works for all sufficiently small parameters and every actual flight.
-/

namespace LoopsParabolic
open Set Function
noncomputable section

/-- The central radius depends on the desired accuracy and the fixed
parabolic point, but not on the parameter or on the flight duration. -/
theorem passage_uniform_quantitative_estimate {a ε : ℝ}
    (ha : a ∈ Icc (1/20:ℝ) (3/50)) (root : cubic a = 0)
    (hε : 0 < ε) (hεhalf : ε ≤ 1/2) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1/1000 ∧
      ∀ (t : ℝ) (k : ℕ), 0 < t → t ≤ 1/100 → t ≤ δ^2 →
      (∀ j ≤ k, (H t)^[j] 0 ∈ Icc 0 cap) →
      7/20 ≤ (H t)^[k] 0 →
      |7*(k:ℝ)*Real.sqrt t-Real.pi| ≤
        280*ε+(7*cap/δ^2)*Real.sqrt t+
          (Real.pi-2*Real.arctan (δ/(2*passageScale a t))) := by
  obtain ⟨C, hC, hrelative⟩ := passage_uniform_relative
  have hCpos : 0 < C := lt_of_lt_of_le (by norm_num) hC
  have hBpos : 0 < passageB a :=
    lt_of_lt_of_le (by norm_num) (passageB_ge_one ha)
  let δ : ℝ := min (1/1000) (min (ε/C) (ε/(8*passageB a)))
  have hδ : 0 < δ := by
    dsimp [δ]
    exact lt_min (by norm_num)
      (lt_min (div_pos hε hCpos) (div_pos hε (by positivity)))
  have hδmax : δ ≤ 1/1000 := min_le_left _ _
  have hδC : δ ≤ ε/C :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hδB : δ ≤ ε/(8*passageB a) :=
    (min_le_right _ _).trans (min_le_right _ _)
  let η := C*δ
  have hη : 0 ≤ η := mul_nonneg hCpos.le hδ.le
  have hηε : η ≤ ε := by
    have hh := (le_div_iff₀ hCpos).mp hδC
    dsimp [η]
    nlinarith only [hh]
  have hscale : 4*δ*(passageB a*(1+η)) ≤ ε := by
    have hh := (le_div_iff₀ (show 0 < 8*passageB a by positivity)).mp hδB
    have hfactor : 1+η ≤ 2 := by linarith
    calc
      4*δ*(passageB a*(1+η)) = (4*δ*passageB a)*(1+η) := by ring
      _ ≤ (4*δ*passageB a)*2 :=
        mul_le_mul_of_nonneg_left hfactor (by positivity)
      _ ≤ ε := by nlinarith only [hh]
  refine ⟨δ, hδ, hδmax, ?_⟩
  intro t k ht htmax htδ stay reached
  have hrel : ∀ x : ℝ, |x| ≤ δ →
      (1-η)*(passageA a*t+passageB a*x^2) ≤ H t (a+x)-(a+x) ∧
      H t (a+x)-(a+x) ≤ (1+η)*(passageA a*t+passageB a*x^2) := by
    intro x hx
    exact hrelative a ha root δ t x hδ.le (hδmax.trans (by norm_num)) ht.le htδ hx
  exact passage_quantitative_estimate ha root hε.le hεhalf hη hηε
    hδ hδmax ht htmax htδ hrel hscale stay reached

end
end LoopsParabolic

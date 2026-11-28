import QuadraticCanonicalScale
import QuadraticThreeEncounterLimit

/-!
# The encounter obstruction at the unique quadratic normalization scale

The scale is determined by the actual iterate. It is not a free shrinking
zoom. The conclusion concerns three selected orbit encounters, and the
hypotheses on the complete iterate use its actual coefficients of degrees
four, six and eight.
-/

namespace QuadraticCanonicalObstruction

open QuadraticFlightJet QuadraticCanonicalScale QuadraticThreeEncounterLimit
open Filter
open scoped Topology

noncomputable section

def totalSteps (k₀ k₁ k₂ k₃ : ℕ) : ℕ := k₀+1+k₁+1+k₂+1+k₃

/-- Charge in the uniquely normalized critical coordinate. -/
def canonicalCharge (c : ℂ) (N j : ℕ) : ℂ :=
  charge c c ((canonicalScale c N)^2) j

/-- A concrete obstruction at the unique same-linear-scale normalization
of the actual quadratic iterate. A flat critical eighth jet and four
neutral energy blocks cannot retain any of the three selected encounters. -/
theorem canonical_three_encounter_obstruction
    (c : ℕ → ℂ) (k₀ k₁ k₂ k₃ : ℕ → ℕ) (α β γ : ℂ)
    (hx : ∀ n j, j < totalSteps (k₀ n) (k₁ n) (k₂ n) (k₃ n) →
      orbit (c n) (c n) j ≠ 0)
    (hα : Tendsto (fun n =>
      canonicalCharge (c n) (totalSteps (k₀ n) (k₁ n) (k₂ n) (k₃ n)) (k₀ n))
      atTop (𝓝 α))
    (hβ : Tendsto (fun n =>
      canonicalCharge (c n) (totalSteps (k₀ n) (k₁ n) (k₂ n) (k₃ n)) (k₀ n+1+k₁ n))
      atTop (𝓝 β))
    (hγ : Tendsto (fun n =>
      canonicalCharge (c n) (totalSteps (k₀ n) (k₁ n) (k₂ n) (k₃ n))
        (k₀ n+1+k₁ n+1+k₂ n)) atTop (𝓝 γ))
    (h₀ : VanishingFlightEnergy
      (fun n => canonicalCharge (c n) (totalSteps (k₀ n) (k₁ n) (k₂ n) (k₃ n))) k₀)
    (h₁ : VanishingFlightEnergy
      (fun n j => canonicalCharge (c n) (totalSteps (k₀ n) (k₁ n) (k₂ n) (k₃ n))
        (k₀ n+1+j)) k₁)
    (h₂ : VanishingFlightEnergy
      (fun n j => canonicalCharge (c n) (totalSteps (k₀ n) (k₁ n) (k₂ n) (k₃ n))
        (k₀ n+1+k₁ n+1+j)) k₂)
    (h₃ : VanishingFlightEnergy
      (fun n j => canonicalCharge (c n) (totalSteps (k₀ n) (k₁ n) (k₂ n) (k₃ n))
        (k₀ n+1+k₁ n+1+k₂ n+1+j)) k₃)
    (h4 : Tendsto (fun n =>
      (canonicalCriticalReturn (c n) (totalSteps (k₀ n) (k₁ n) (k₂ n) (k₃ n))).coeff 4)
      atTop (𝓝 0))
    (h6 : Tendsto (fun n =>
      (canonicalCriticalReturn (c n) (totalSteps (k₀ n) (k₁ n) (k₂ n) (k₃ n))).coeff 6)
      atTop (𝓝 0))
    (h8 : Tendsto (fun n =>
      (canonicalCriticalReturn (c n) (totalSteps (k₀ n) (k₁ n) (k₂ n) (k₃ n))).coeff 8)
      atTop (𝓝 0)) :
    α = 0 ∧ β = 0 ∧ γ = 0 := by
  apply three_encounter_flight_limit
    (fun n => canonicalCharge (c n) (totalSteps (k₀ n) (k₁ n) (k₂ n) (k₃ n)))
    k₀ k₁ k₂ k₃ α β γ hα hβ hγ h₀.flatJet h₁.flatJet h₂.flatJet h₃.flatJet
  let N : ℕ → ℕ := fun n => totalSteps (k₀ n) (k₁ n) (k₂ n) (k₃ n)
  have e4 : (fun n => (canonicalCriticalReturn (c n) (N n)).coeff 4) =
      (fun n => (flightJet (canonicalCharge (c n) (N n)) (N n)).a) :=
    funext (fun n => canonicalCriticalReturn_coeff_four (c n) (N n) (hx n))
  have e6 : (fun n => (canonicalCriticalReturn (c n) (N n)).coeff 6) =
      (fun n => (flightJet (canonicalCharge (c n) (N n)) (N n)).b) :=
    funext (fun n => canonicalCriticalReturn_coeff_six (c n) (N n) (hx n))
  have e8 : (fun n => (canonicalCriticalReturn (c n) (N n)).coeff 8) =
      (fun n => (flightJet (canonicalCharge (c n) (N n)) (N n)).d) :=
    funext (fun n => canonicalCriticalReturn_coeff_eight (c n) (N n) (hx n))
  have hJ : JetConverges
      (fun n => flightJet (canonicalCharge (c n) (N n)) (N n)) Jet.identity := by
    refine ⟨?_, ?_, ?_⟩
    · have h : Tendsto (fun n => (canonicalCriticalReturn (c n) (N n)).coeff 4)
          atTop (𝓝 (0 : ℂ)) := h4
      simpa only [e4, Jet.identity] using h
    · have h : Tendsto (fun n => (canonicalCriticalReturn (c n) (N n)).coeff 6)
          atTop (𝓝 (0 : ℂ)) := h6
      simpa only [e6, Jet.identity] using h
    · have h : Tendsto (fun n => (canonicalCriticalReturn (c n) (N n)).coeff 8)
          atTop (𝓝 (0 : ℂ)) := h8
      simpa only [e8, Jet.identity] using h
  exact hJ

#print axioms canonical_three_encounter_obstruction

end
end QuadraticCanonicalObstruction

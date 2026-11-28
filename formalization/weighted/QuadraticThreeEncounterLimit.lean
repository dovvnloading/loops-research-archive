import QuadraticFlightJet
import QuadraticThreeEncounterAlgebra
import QuadraticFlightEnergy

/-!
# An eighth-jet obstruction for actual quadratic critical returns

The hypotheses below concern coefficients of literal, affinely normalized
quadratic iterates. Four intervening actual flights approach the identity
through degree four. If the complete critical-value flight does likewise,
three convergent encounter coefficients must all disappear.

After the critical square substitution, degrees two, three and four are
degrees four, six and eight in the original critical coordinate.
-/

namespace QuadraticThreeEncounterLimit

open QuadraticFlightJet Polynomial Filter
open scoped Topology

noncomputable section

/-- Coordinatewise convergence of the retained tangent jet. -/
def JetConverges (j : ℕ → Jet) (l : Jet) : Prop :=
  Tendsto (fun n => (j n).a) atTop (𝓝 l.a) ∧
  Tendsto (fun n => (j n).b) atTop (𝓝 l.b) ∧
  Tendsto (fun n => (j n).d) atTop (𝓝 l.d)

/-- These are coefficients of the actual polynomial, with no germ surrogate. -/
def FlatCoefficients (p : ℕ → ℂ[X]) : Prop :=
  Tendsto (fun n => (p n).coeff 2) atTop (𝓝 0) ∧
  Tendsto (fun n => (p n).coeff 3) atTop (𝓝 0) ∧
  Tendsto (fun n => (p n).coeff 4) atTop (𝓝 0)

theorem JetConverges.comp {u v : ℕ → Jet} {U V : Jet}
    (hu : JetConverges u U) (hv : JetConverges v V) :
    JetConverges (fun n => Jet.comp (u n) (v n)) (Jet.comp U V) := by
  rcases hu with ⟨hua, hub, hud⟩
  rcases hv with ⟨hva, hvb, hvd⟩
  refine ⟨hva.add hua, (hvb.add ((tendsto_const_nhds.mul hua).mul hva)).add hub, ?_⟩
  exact ((hvd.add (hua.mul ((hva.pow 2).add (tendsto_const_nhds.mul hvb)))).add
    ((tendsto_const_nhds.mul hub).mul hva)).add hud

theorem JetConverges.kick {a : ℕ → ℂ} {A : ℂ}
    (ha : Tendsto a atTop (𝓝 A)) :
    JetConverges (fun n => Jet.kick (a n)) (Jet.kick A) :=
  ⟨ha, tendsto_const_nhds, tendsto_const_nhds⟩

theorem flat_of_hasJet (p : ℕ → ℂ[X]) (j : ℕ → Jet)
    (hp : ∀ n, HasJet (p n) (j n)) (h : FlatCoefficients p) :
    JetConverges j Jet.identity := by
  rcases h with ⟨h2, h3, h4⟩
  have e2 : (fun n => (p n).coeff 2) = fun n => (j n).a :=
    funext (fun n => (hp n).coeff_two)
  have e3 : (fun n => (p n).coeff 3) = fun n => (j n).b :=
    funext (fun n => (hp n).coeff_three)
  have e4 : (fun n => (p n).coeff 4) = fun n => (j n).d :=
    funext (fun n => (hp n).coeff_four)
  refine ⟨?_, ?_, ?_⟩
  · simpa only [e2, Jet.identity] using h2
  · simpa only [e3, Jet.identity] using h3
  · simpa only [e4, Jet.identity] using h4

/-- Exact decomposition at the three selected actual step positions. -/
theorem flightJet_split (a : ℕ → ℂ) (k₀ k₁ k₂ k₃ : ℕ) :
    flightJet a (k₀+1+k₁+1+k₂+1+k₃) =
      Jet.comp (flightJet (fun j => a (k₀+1+k₁+1+k₂+1+j)) k₃)
        (Jet.comp (Jet.kick (a (k₀+1+k₁+1+k₂)))
          (Jet.comp (flightJet (fun j => a (k₀+1+k₁+1+j)) k₂)
            (Jet.comp (Jet.kick (a (k₀+1+k₁)))
              (Jet.comp (flightJet (fun j => a (k₀+1+j)) k₁)
                (Jet.comp (Jet.kick (a k₀)) (flightJet a k₀)))))) := by
  rw [flightJet_add a (k₀+1+k₁+1+k₂+1) k₃]
  change Jet.comp _ (Jet.comp _ (flightJet a (k₀+1+k₁+1+k₂))) = _
  rw [flightJet_add a (k₀+1+k₁+1) k₂]
  change Jet.comp _ (Jet.comp _ (Jet.comp _
    (Jet.comp _ (flightJet a (k₀+1+k₁))))) = _
  rw [flightJet_add a (k₀+1) k₁]
  rfl

/-- The limiting algebra is independent of how long the four intervening
flights are. Their actual jet convergence remains an explicit hypothesis. -/
theorem three_encounter_flight_limit
    (a : ℕ → ℕ → ℂ) (k₀ k₁ k₂ k₃ : ℕ → ℕ) (α β γ : ℂ)
    (hα : Tendsto (fun n => a n (k₀ n)) atTop (𝓝 α))
    (hβ : Tendsto (fun n => a n (k₀ n+1+k₁ n)) atTop (𝓝 β))
    (hγ : Tendsto (fun n => a n (k₀ n+1+k₁ n+1+k₂ n)) atTop (𝓝 γ))
    (h₀ : JetConverges (fun n => flightJet (a n) (k₀ n)) Jet.identity)
    (h₁ : JetConverges
      (fun n => flightJet (fun j => a n (k₀ n+1+j)) (k₁ n)) Jet.identity)
    (h₂ : JetConverges
      (fun n => flightJet (fun j => a n (k₀ n+1+k₁ n+1+j)) (k₂ n)) Jet.identity)
    (h₃ : JetConverges
      (fun n => flightJet (fun j => a n (k₀ n+1+k₁ n+1+k₂ n+1+j)) (k₃ n))
      Jet.identity)
    (hfull : JetConverges
      (fun n => flightJet (a n) (k₀ n+1+k₁ n+1+k₂ n+1+k₃ n)) Jet.identity) :
    α = 0 ∧ β = 0 ∧ γ = 0 := by
  have hlim := h₃.comp ((JetConverges.kick hγ).comp
    (h₂.comp ((JetConverges.kick hβ).comp
      (h₁.comp ((JetConverges.kick hα).comp h₀)))))
  simp only [Jet.identity_comp, Jet.comp_identity] at hlim
  have hlim' : JetConverges
      (fun n => flightJet (a n) (k₀ n+1+k₁ n+1+k₂ n+1+k₃ n))
      (Jet.comp (Jet.kick γ) (Jet.comp (Jet.kick β) (Jet.kick α))) := by
    simpa only [flightJet_split] using hlim
  have hA := tendsto_nhds_unique hlim'.1 hfull.1
  have hB := tendsto_nhds_unique hlim'.2.1 hfull.2.1
  have hC := tendsto_nhds_unique hlim'.2.2 hfull.2.2
  simp only [Jet.comp, Jet.kick, Jet.identity] at hA hB hC
  apply QuadraticThreeEncounterAlgebra.three_encounter_flat α β γ
  · simpa using hA
  · convert hB using 1 <;> ring
  · convert hC using 1 <;> ring

/-- An obstruction for literal actual quadratic returns, in fixed affine
critical coordinates. It applies to every sequence whose indicated orbit
segments avoid the critical point, including returns at a nonperiodic
infinitely renormalizable parameter. No renormalization existence or
parameter-fiber theorem is an assumption or conclusion here. -/
theorem actual_critical_three_encounter_obstruction
    (c s : ℕ → ℂ) (k₀ k₁ k₂ k₃ : ℕ → ℕ) (α β γ : ℂ)
    (hs : ∀ n, s n ≠ 0)
    (hx : ∀ n j, j < k₀ n+1+k₁ n+1+k₂ n+1+k₃ n → orbit (c n) (c n) j ≠ 0)
    (hα : Tendsto (fun n => charge (c n) (c n) ((s n)^2) (k₀ n)) atTop (𝓝 α))
    (hβ : Tendsto
      (fun n => charge (c n) (c n) ((s n)^2) (k₀ n+1+k₁ n)) atTop (𝓝 β))
    (hγ : Tendsto
      (fun n => charge (c n) (c n) ((s n)^2) (k₀ n+1+k₁ n+1+k₂ n))
      atTop (𝓝 γ))
    (h₀ : FlatCoefficients
      (fun n => actualBlock (c n) (c n) ((s n)^2) 0 (k₀ n)))
    (h₁ : FlatCoefficients
      (fun n => actualBlock (c n) (c n) ((s n)^2) (k₀ n+1) (k₁ n)))
    (h₂ : FlatCoefficients
      (fun n => actualBlock (c n) (c n) ((s n)^2) (k₀ n+1+k₁ n+1) (k₂ n)))
    (h₃ : FlatCoefficients
      (fun n => actualBlock (c n) (c n) ((s n)^2)
        (k₀ n+1+k₁ n+1+k₂ n+1) (k₃ n)))
    (hfull : FlatCoefficients
      (fun n => normalizedActualFlight (c n) (c n) ((s n)^2)
        (k₀ n+1+k₁ n+1+k₂ n+1+k₃ n))) :
    α = 0 ∧ β = 0 ∧ γ = 0 := by
  apply three_encounter_flight_limit
    (fun n => charge (c n) (c n) ((s n)^2)) k₀ k₁ k₂ k₃ α β γ hα hβ hγ
  · have h := flat_of_hasJet _ _ (fun n => actualBlock_hasJet
        (c n) (c n) ((s n)^2) 0 (k₀ n) (pow_ne_zero 2 (hs n))
        (fun j hj => hx n j (by omega))) h₀
    simpa only [Nat.zero_add] using h
  · exact flat_of_hasJet _ _ (fun n => actualBlock_hasJet
      (c n) (c n) ((s n)^2) (k₀ n+1) (k₁ n) (pow_ne_zero 2 (hs n))
      (fun j hj => hx n j (by omega))) h₁
  · exact flat_of_hasJet _ _ (fun n => actualBlock_hasJet
      (c n) (c n) ((s n)^2) (k₀ n+1+k₁ n+1) (k₂ n) (pow_ne_zero 2 (hs n))
      (fun j hj => hx n j (by omega))) h₂
  · exact flat_of_hasJet _ _ (fun n => actualBlock_hasJet
      (c n) (c n) ((s n)^2) (k₀ n+1+k₁ n+1+k₂ n+1) (k₃ n)
      (pow_ne_zero 2 (hs n)) (fun j hj => hx n j (by omega))) h₃
  · exact flat_of_hasJet _ _ (fun n => normalizedActualFlight_hasJet
      (c n) (c n) ((s n)^2) (k₀ n+1+k₁ n+1+k₂ n+1+k₃ n)
      (pow_ne_zero 2 (hs n)) (hx n)) hfull

#print axioms actual_critical_three_encounter_obstruction

/-- A concrete orbit-charge condition: bounded signed partial drift,
vanishing total drift, and vanishing quadratic variation. -/
def VanishingFlightEnergy (a : ℕ → ℕ → ℂ) (N : ℕ → ℕ) : Prop :=
  (∃ M : ℝ, ∀ n j, j ≤ N n → ‖QuadraticFlightEnergy.partialSum (a n) j‖ ≤ M) ∧
  Tendsto (fun n => QuadraticFlightEnergy.partialSum (a n) (N n)) atTop (𝓝 0) ∧
  Tendsto (fun n => LoopsQuadraticReciprocalFlight.energy (a n) (N n)) atTop (𝓝 0)

theorem VanishingFlightEnergy.flatJet {a : ℕ → ℕ → ℂ} {N : ℕ → ℕ}
    (h : VanishingFlightEnergy a N) :
    JetConverges (fun n => flightJet (a n) (N n)) Jet.identity := by
  rcases h with ⟨⟨M, hM⟩, hsum, henergy⟩
  simpa only [JetConverges, Jet.identity] using
    QuadraticFlightEnergy.flight_jet_tendsto_zero a N M hM hsum henergy

/-- Actual critical returns cannot hide three nonzero limiting encounters
among four blocks with bounded signed drift and vanishing quadratic energy.
Only the full return's fourth, sixth and eighth critical coefficients are
assumed to vanish; the intervening jet limits are proved from orbit data. -/
theorem actual_critical_three_encounter_energy_obstruction
    (c s : ℕ → ℂ) (k₀ k₁ k₂ k₃ : ℕ → ℕ) (α β γ : ℂ)
    (hs : ∀ n, s n ≠ 0)
    (hx : ∀ n j, j < k₀ n+1+k₁ n+1+k₂ n+1+k₃ n → orbit (c n) (c n) j ≠ 0)
    (hα : Tendsto (fun n => charge (c n) (c n) ((s n)^2) (k₀ n)) atTop (𝓝 α))
    (hβ : Tendsto
      (fun n => charge (c n) (c n) ((s n)^2) (k₀ n+1+k₁ n)) atTop (𝓝 β))
    (hγ : Tendsto
      (fun n => charge (c n) (c n) ((s n)^2) (k₀ n+1+k₁ n+1+k₂ n))
      atTop (𝓝 γ))
    (h₀ : VanishingFlightEnergy
      (fun n => charge (c n) (c n) ((s n)^2)) k₀)
    (h₁ : VanishingFlightEnergy
      (fun n j => charge (c n) (c n) ((s n)^2) (k₀ n+1+j)) k₁)
    (h₂ : VanishingFlightEnergy
      (fun n j => charge (c n) (c n) ((s n)^2) (k₀ n+1+k₁ n+1+j)) k₂)
    (h₃ : VanishingFlightEnergy
      (fun n j => charge (c n) (c n) ((s n)^2) (k₀ n+1+k₁ n+1+k₂ n+1+j)) k₃)
    (hfull : FlatCoefficients
      (fun n => normalizedActualFlight (c n) (c n) ((s n)^2)
        (k₀ n+1+k₁ n+1+k₂ n+1+k₃ n))) :
    α = 0 ∧ β = 0 ∧ γ = 0 := by
  apply three_encounter_flight_limit
    (fun n => charge (c n) (c n) ((s n)^2)) k₀ k₁ k₂ k₃ α β γ hα hβ hγ
      h₀.flatJet h₁.flatJet h₂.flatJet h₃.flatJet
  exact flat_of_hasJet _ _ (fun n => normalizedActualFlight_hasJet
    (c n) (c n) ((s n)^2) (k₀ n+1+k₁ n+1+k₂ n+1+k₃ n)
    (pow_ne_zero 2 (hs n)) (hx n)) hfull

#print axioms actual_critical_three_encounter_energy_obstruction

end
end QuadraticThreeEncounterLimit

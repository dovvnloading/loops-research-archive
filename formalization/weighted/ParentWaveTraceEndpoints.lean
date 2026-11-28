import SlitWaveModulus
import MarkedSlitTransport

/-!
# Endpoint atoms in the canonical Hausdorff traces

Deleting finitely many points preserves every weighted one-dimensional
Hausdorff integral, even for infinite density values. Consequently the
canonical full-trace modulus agrees with its open-parameter version.
This permits conformal transport inside an open chart without changing
the original wave modulus.
-/

namespace ParentWaveTraceEndpoints

open Set Function MeasureTheory Measure Filter MarkedSlitTransport SlitWaveModulus
open scoped ENNReal NNReal Topology

noncomputable section

/-- Finite exceptional sets are null for one-dimensional Hausdorff measure. -/
theorem lineLength_eq_of_finite_diff (ρ : ℂ → ℝ≥0∞) {S T : Set ℂ}
    (hsub : T ⊆ S) (hfinite : (S \ T).Finite) : lineLength ρ S = lineLength ρ T := by
  letI : NullSingletonClass (μH[1] : Measure ℂ) :=
    nullSingletonClass_hausdorff ℂ (by norm_num)
  have hnull : (μH[1] : Measure ℂ) (S \ T) = 0 := hfinite.measure_zero _
  have hae : S =ᵐ[μH[1]] T := by
    have haway : ∀ᵐ z ∂(μH[1] : Measure ℂ),z ∉ S \ T := by
      rw [ae_iff]
      change (μH[1] : Measure ℂ) {z | ¬z ∉ S \ T} = 0
      simpa only [not_not,Set.setOf_mem_eq] using hnull
    filter_upwards [haway] with z hz
    exact propext ⟨fun hs => by_contra (fun ht => hz ⟨hs,ht⟩),fun ht => hsub ht⟩
  unfold lineLength
  rw [Measure.restrict_congr_set hae]

/-- The only points lost on passing to the open parameter interval are
the two original endpoints; the curve need not be injective. -/
theorem trace_diff_interiorTrace_subset (γ : Curve) :
    trace γ \ interiorTrace γ ⊆ {γ initial,γ terminal} := by
  rintro z ⟨⟨t,rfl⟩,hnot⟩
  by_cases h0 : (t : ℝ) = 0
  · have ht : t = initial := Subtype.ext h0
    simp [ht]
  by_cases h1 : (t : ℝ) = 1
  · have ht : t = terminal := Subtype.ext h1
    simp [ht]
  have ht : t ∈ parameterInterior :=
    ⟨lt_of_le_of_ne t.2.1 (fun h => h0 h.symm),lt_of_le_of_ne t.2.2 h1⟩
  exact False.elim (hnot ⟨t,ht,rfl⟩)

/-- Every weighted canonical trace length equals its open-parameter
length, with no finiteness or density regularity hypothesis. -/
theorem lineLength_trace_eq_interiorTrace (ρ : ℂ → ℝ≥0∞) (γ : Curve) :
    lineLength ρ (trace γ) = lineLength ρ (interiorTrace γ) := by
  exact lineLength_eq_of_finite_diff ρ (interiorTrace_subset_trace γ)
    ((Set.toFinite _).subset (trace_diff_interiorTrace_subset γ))

/-- The same endpoint deletion is valid after any map; only the two
images of the endpoints can be lost. -/
theorem lineLength_image_trace_eq_interiorTrace (ρ : ℂ → ℝ≥0∞)
    (F : ℂ → ℂ) (γ : Curve) :
    lineLength ρ (F '' trace γ) = lineLength ρ (F '' interiorTrace γ) := by
  apply lineLength_eq_of_finite_diff ρ (image_mono (interiorTrace_subset_trace γ))
  apply ((Set.toFinite {γ initial,γ terminal}).image F).subset
  rintro z ⟨⟨w,hw,rfl⟩,hnot⟩
  apply mem_image_of_mem
  apply trace_diff_interiorTrace_subset γ
  exact ⟨hw,fun hwi => hnot ⟨w,hwi,rfl⟩⟩

/-- Admissibility is unchanged by deleting each curve's endpoint atoms. -/
theorem admissible_trace_iff_interiorTrace (Γ : Set Curve) (ρ : ℂ → ℝ≥0∞) :
    Admissible (traces Γ) ρ ↔ Admissible (interiorTrace '' Γ) ρ := by
  constructor
  · rintro ⟨hρ,h⟩
    refine ⟨hρ,?_⟩
    rintro S ⟨γ,hγ,rfl⟩
    rw [← lineLength_trace_eq_interiorTrace]
    exact h _ ⟨γ,hγ,rfl⟩
  · rintro ⟨hρ,h⟩
    refine ⟨hρ,?_⟩
    rintro S ⟨γ,hγ,rfl⟩
    rw [lineLength_trace_eq_interiorTrace]
    exact h _ ⟨γ,hγ,rfl⟩

/-- The exact canonical modulus is retained under open-parameter trace
transport. This equality holds for arbitrary, uncountable curve families. -/
theorem modulus_trace_eq_interiorTrace (Γ : Set Curve) :
    modulus (traces Γ) = modulus (interiorTrace '' Γ) := by
  unfold modulus
  congr 1
  funext ρ
  rw [admissible_trace_iff_interiorTrace]

end
end ParentWaveTraceEndpoints

import ParentWaveExact
import ActualParentSupremum
import ActualParentSelection

/-!
# Exact limiting optimum of the literal physical quadratic parent waves

The exact variational theorem is applied to the unchanged limiting orbit
marks and then to the existing convergence of the complete physical
slit-disk suprema. The convergence theorem is prior work.
-/

namespace ActualParentExact

open Set Filter MarkedSlitTransport SlitWaveModulus
open ActualParentSupremum ActualParentMarks ParentWaveExact
open NearTwoTip NearTwoShooting LoopsLimitingCrestParameter
open LimitingCrestQuadraticReturn
open scoped Topology ENNReal
noncomputable section

def limitCoefficient (k : ℝ) : ℝ :=
  coefficient (criticalOrbit k 2) (criticalOrbit k 5) (criticalOrbit k 3)

/-- Exact value of the archive's existing limiting canonical supremum. -/
theorem limitingParentWidth_eq_coefficient (k : ℝ) (hk : k ∈ parameterInterval) :
    limitingParentWidth k hk = ENNReal.ofReal (limitCoefficient k) := by
  exact parent_width_eq_coefficient (limitMarking k hk)

theorem limitCoefficient_pos {k : ℝ} (hk : k ∈ parameterInterval) :
    0 < limitCoefficient k :=
  coefficient_pos (limitMarking k hk)

theorem limitingParentWidth_toReal (k : ℝ) (hk : k ∈ parameterInterval) :
    (limitingParentWidth k hk).toReal = limitCoefficient k := by
  rw [limitingParentWidth_eq_coefficient, ENNReal.toReal_ofReal (limitCoefficient_pos hk).le]

/-- Attainment in the original Borel parent-wave class. -/
theorem limitingParentWidth_attained (k : ℝ) (hk : k ∈ parameterInterval) :
    ∃ Γ : Set Curve, ParentWave (limitMarking k hk) univ Γ ∧
      modulus (traces Γ) = limitingParentWidth k hk :=
  exists_parentWave_attaining_width (limitMarking k hk)

theorem limitCoefficient_eq_K (k : ℝ) (hk : k ∈ parameterInterval) :
    limitCoefficient k =
      ParentWaveEllipticK.K
        (1-(criticalOrbit k 5-criticalOrbit k 2)/(criticalOrbit k 3-criticalOrbit k 2)) /
      (2 * ParentWaveEllipticK.K
        ((criticalOrbit k 5-criticalOrbit k 2)/(criticalOrbit k 3-criticalOrbit k 2))) :=
  coefficient_eq_K (limitMarking k hk)

/-- The explicit value is the limit of the complete physical disk optima. -/
theorem physical_parent_optimum_converges_to_explicit {k : ℝ}
    (hk : k ∈ parameterInterval) (hroot : relation k = 0) (c : ℕ → ℝ)
    (hc : ∀ n, ActualTip (n+17) (c n)) :
    Tendsto (fun n => (physicalParentWidth (by omega : 17 ≤ n+17) (hc n) hk hroot).toReal)
      atTop (𝓝 (limitCoefficient k)) := by
  simpa only [limitingParentWidth_toReal] using
    physical_parent_optimum_real_converges hk hroot c hc

/-- The explicitly evaluated limit for the uniquely named F16 signed-chart
root sequence. Its equality with the archive's actual parameters is proved. -/
theorem canonical_physical_parent_optimum_converges_to_explicit {k : ℝ}
    (hk : k ∈ parameterInterval) (hroot : relation k = 0) :
    Tendsto (fun n => (physicalParentWidth (by omega : 17 ≤ n+17)
        (ActualParentSelection.canonicalSequence_actual n) hk hroot).toReal)
      atTop (𝓝 (limitCoefficient k)) :=
  physical_parent_optimum_converges_to_explicit hk hroot
    ActualParentSelection.canonicalSequence ActualParentSelection.canonicalSequence_actual

/-- The canonical signed-chart family has an explicitly evaluated positive
limiting maximum, realized by an actual wave of the original limiting class. -/
theorem exists_canonical_attained_explicit_parent_limit :
    ∃ (k : ℝ) (hk : k ∈ parameterInterval) (hroot : relation k = 0),
      ∃ Γ : Set Curve, ParentWave (limitMarking k hk) univ Γ ∧
        modulus (traces Γ) = ENNReal.ofReal (limitCoefficient k) ∧
        0 < limitCoefficient k ∧
        Tendsto
          (fun n => (physicalParentWidth (by omega : 17 ≤ n+17)
            (ActualParentSelection.canonicalSequence_actual n) hk hroot).toReal)
          atTop (𝓝 (limitCoefficient k)) := by
  obtain ⟨k,⟨hk,hroot⟩,_⟩ := exists_unique_limiting_parameter
  obtain ⟨Γ,hΓ,hwidth⟩ := limitingParentWidth_attained k hk
  exact ⟨k,hk,hroot,Γ,hΓ,
    hwidth.trans (limitingParentWidth_eq_coefficient k hk),limitCoefficient_pos hk,
    canonical_physical_parent_optimum_converges_to_explicit hk hroot⟩

/-- Constructed actual family, explicit positive limit, and a canonical
maximizer on the limiting domain, with no geometric existence premise. -/
theorem exists_attained_explicit_physical_parent_limit :
    ∃ (k : ℝ) (hk : k ∈ parameterInterval) (hroot : relation k = 0),
      ∃ (c : ℕ → ℝ) (hc : ∀ n, ActualTip (n+17) (c n)),
        ∃ Γ : Set Curve, ParentWave (limitMarking k hk) univ Γ ∧
          modulus (traces Γ) = ENNReal.ofReal (limitCoefficient k) ∧
          0 < limitCoefficient k ∧
          Tendsto
            (fun n => (physicalParentWidth (by omega : 17 ≤ n+17) (hc n) hk hroot).toReal)
            atTop (𝓝 (limitCoefficient k)) := by
  classical
  obtain ⟨k,⟨hk,hroot⟩,_⟩ := exists_unique_limiting_parameter
  choose c hc using fun n : ℕ => exists_actual_tip (n+17) (by omega)
  obtain ⟨Γ,hΓ,hwidth⟩ := limitingParentWidth_attained k hk
  exact ⟨k,hk,hroot,c,hc,Γ,hΓ,
    hwidth.trans (limitingParentWidth_eq_coefficient k hk), limitCoefficient_pos hk,
    physical_parent_optimum_converges_to_explicit hk hroot c hc⟩

end
end ActualParentExact


import UniformCrestSupport
import ActualCrestTransportLimit

/-!
# Physical crest transport from return index seventeen onward

The quantitative whole-disk support estimate removes the unspecified
large-period threshold from the archived proper-family theorem.  Every
actual tip with return index at least seventeen has the same complete
physical parent and descendant realization, including the exact density
moduli, the strict one-third ratio, and every intermediate restriction.

The limit theorem below retains those conclusions at every index of the
constructed sequence.  It uses the previously established convergence;
the new assertion is uniform physical realization from the first index.
-/

namespace UniformCrestTransport

open Set Function Filter MeasureTheory
open scoped Topology ENNReal NNReal
open NearTwoTip NearTwoShooting LimitingCrestQuadraticReturn LimitingCrest
open GlobalCrestCrossing GlobalCrestClassification GlobalCrestFinalCut
open ActualCrestPaths ActualCrestParentPaths ActualCrestWidth ActualCrestProperFamilies
open ActualCrestComponents ActualCrestTransportLimit
open CrestConformalModulus CircularCrestModulus

noncomputable section

/-- All the closed support disk, at every intermediate iterate, belongs
to the actual physical return component.  The bound starts at seventeen
and has no residual asymptotic-support hypothesis. -/
theorem all_period_support_in_archived_parent {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {z : ℂ} (hz : z ∈ initialDisk)
    {m : ℕ} (hm : m ≤ 3) :
    ((quadraticMap c)^[m*p]) ((criticalValue c p : ℂ)*z) ∈
      ThreeReturnParent.archivedParentSource c p := by
  exact physical_support_in_archived_parent hp hc
    (UniformCrestSupport.actual_strict_support hp hc) hz hm

/-- Every admissible actual parameter and every classified terminal
endpoint give complete proper physical families.  In particular, this
assertion includes the parent and descendant moduli, their literal
positive ratio, the maximal surviving component, and full ancestry. -/
theorem all_period_realize_collar {p : ℕ} (hp : 17 ≤ p) {c r α : ℝ}
    (hc : ActualTip p c) (F : Family p c)
    (hα : α ∈ Ioo (518/1000 : ℝ) (519/1000))
    (hr : r ∈ Ioo (663/10000 : ℝ) (133/2000)) (hzero : terminal F r = -1) :
    RealizedCollar hp hc F α r := by
  exact realize_collar hp hc (UniformCrestSupport.actual_strict_support hp hc)
    F hα hr hzero

/-- No actual parameter, crossing family, or terminal cut is excluded
by an unspecified late-period threshold. -/
theorem every_actual_tip_realizes_collar {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) (F : Family p c) :
    ∃ α ∈ Ioo (518/1000 : ℝ) (519/1000),
      normalizedReturn c p (α : ℂ) = (α : ℂ) ∧
      ∃ r ∈ Ioo (663/10000 : ℝ) (133/2000), terminal F r = -1 ∧
        RealizedCollar hp hc F α r := by
  obtain ⟨α,hα,hfixed,r,hr,hzero,_⟩ := actual_complete_cut_classification hp hc F
  exact ⟨α,hα,hfixed,r,hr,hzero,all_period_realize_collar hp hc F hα hr hzero⟩

/-- The original-plane families have their exact, independently defined
all-density moduli and strict ratio at every index starting at seventeen.
The denominator is the entire original circular parent. -/
theorem all_period_proper_moduli {p : ℕ} (hp : 17 ≤ p) {c r α : ℝ}
    (hc : ActualTip p c) (F : Family p c)
    (hα : α ∈ Ioo (518/1000 : ℝ) (519/1000))
    (hr : r ∈ Ioo (663/10000 : ℝ) (133/2000)) (hzero : terminal F r = -1) :
    ProperParentFamily c p (parentFamily c p) ∧
      ProperDescendantFamily c p α (descendants hp hc F r) ∧
      (modulus (parentFamily c p)).toReal =
        Real.log (2-2/(p : ℝ))/(2*Real.pi) ∧
      modulus (descendants hp hc F r) =
        ∫⁻ s in Ioo (1/16 : ℝ) r, ENNReal.ofReal (1/(s*angle F s)) ∧
      (1/3 : ℝ) < (modulus (descendants hp hc F r)).toReal /
        (modulus (parentFamily c p)).toReal := by
  have h := all_period_realize_collar hp hc F hα hr hzero
  exact ⟨h.parent_proper,h.descendant_proper,h.parent_modulus,
    h.descendant_modulus,h.positive_ratio⟩

/-- For each permitted return index the actual parameter and crossing
family exist, and their complete physical collar is realized. -/
theorem exists_proper_collar_at_every_period (p : ℕ) (hp : 17 ≤ p) :
    ∃ c : ℝ, ∃ hc : ActualTip p c, ∃ F : Family p c,
      ∃ α ∈ Ioo (518/1000 : ℝ) (519/1000),
        normalizedReturn c p (α : ℂ) = (α : ℂ) ∧
        ∃ r ∈ Ioo (663/10000 : ℝ) (133/2000), terminal F r = -1 ∧
          RealizedCollar hp hc F α r := by
  obtain ⟨c,hc⟩ := exists_actual_tip p hp
  obtain ⟨F⟩ := exists_family hp hc
  exact ⟨c,hc,F,every_actual_tip_realizes_collar hp hc F⟩

/-- One constructed actual family realizes its whole proper physical
transport for every return index `n+17`, and the very same modulus ratios
converge to the established positive limiting coefficient. -/
theorem exists_all_period_proper_physical_transport_limit :
    ∃ c : ℕ → ℝ, ∃ hc : ∀ n, ActualTip (n+17) (c n),
      ∃ F : ∀ n, Family (n+17) (c n), ∃ α radii : ℕ → ℝ,
        (∀ n, α n ∈ Ioo (518/1000 : ℝ) (519/1000) ∧
          normalizedReturn (c n) (n+17) (α n : ℂ) = (α n : ℂ) ∧
          radii n ∈ Ioo (663/10000 : ℝ) (133/2000) ∧
          terminal (F n) (radii n) = -1) ∧
        (∀ n, RealizedCollar (by omega) (hc n) (F n) (α n) (radii n)) ∧
        ∃ k₀ ∈ LoopsLimitingCrestParameter.parameterInterval,
          LoopsLimitingCrestParameter.relation k₀ = 0 ∧
          ∃ r ∈ Ioo (663/10000 : ℝ) (133/2000), crestTerminal k₀ r = -1 ∧
            Tendsto radii atTop (𝓝 r) ∧
            Tendsto (fun n => (modulus (descendants (by omega) (hc n) (F n) (radii n))).toReal /
              (modulus (parentFamily (c n) (n+17))).toReal)
              atTop (𝓝 (fullModelCoefficient k₀ r)) ∧
            (1/3 : ℝ) < fullModelCoefficient k₀ r := by
  classical
  choose c hc using fun n : ℕ => exists_actual_tip (n+17) (by omega)
  let F (n : ℕ) : Family (n+17) (c n) :=
    Classical.choice (exists_family (by omega) (hc n))
  choose α hα hfixed radii hr he hanti hunique hcomplete using
    fun n => actual_complete_cut_classification (by omega) (hc n) (F n)
  obtain ⟨k₀,⟨hk₀,hroot⟩,_⟩ := LoopsLimitingCrestParameter.exists_unique_limiting_parameter
  obtain ⟨r,hr₀,he₀,hrlim,hclim,hpositive⟩ :=
    actual_widthRatios_converge hk₀ hroot c hc F radii hr he
  refine ⟨c,hc,F,α,radii,fun n => ⟨hα n,hfixed n,hr n,he n⟩,?_,
    k₀,hk₀,hroot,r,hr₀,he₀,hrlim,?_,hpositive⟩
  · intro n
    exact all_period_realize_collar (by omega) (hc n) (F n) (hα n) (hr n) (he n)
  · have heq : (fun n => widthRatio (by omega) (hc n) (F n) (radii n)) =
        (fun n => (modulus (descendants (by omega) (hc n) (F n) (radii n))).toReal /
          (modulus (parentFamily (c n) (n+17))).toReal) := by
      funext n
      unfold widthRatio
      rw [parentWidth_eq_modulus (by omega) (hc n)]
    rwa [heq] at hclim

end
end UniformCrestTransport

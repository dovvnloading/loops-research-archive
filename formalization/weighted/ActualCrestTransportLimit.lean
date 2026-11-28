import ActualCrestProperFamilies
import ActualCrestComponents
import CircularParentModulus

/-!
# Proper physical circular families with a positive transport limit

This assembly constructs every dynamical input, proves properness for
both families used in the metric ratio, and proves the positive limit
for those same actual families. The conclusion is about literal planar
slit domains. Native ideal markings are not included in its predicates.
-/

namespace ActualCrestTransportLimit

open Set Function Filter MeasureTheory
open scoped Topology ENNReal NNReal
open NearTwoTip NearTwoShooting LimitingCrestQuadraticReturn LimitingCrest
open GlobalCrestCrossing GlobalCrestClassification GlobalCrestFinalCut
open ActualCrestPaths ActualCrestParentPaths ActualCrestWidth ActualCrestProperFamilies
open ActualCrestComponents
open CrestConformalModulus CircularCrestModulus

noncomputable section

/-- Every full parent path has its closing point on the actual target
slit and its whole simple open interior in the literal slit complement. -/
def ProperParentFamily (c : ℝ) (p : ℕ) (Γ : Set SmoothArc) : Prop :=
  ∀ γ ∈ Γ, γ 0 ∈ physicalTargetSlit c p ∧
    γ γ.duration ∈ physicalTargetSlit c p ∧
    (∀ t ∈ Ioo 0 γ.duration, γ t ∈ physicalSlitTarget c p) ∧
    InjOn γ (Ioo 0 γ.duration)

theorem parentFamily_proper {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) : ProperParentFamily c p (parentFamily c p) := by
  rintro γ ⟨ρ,hρ,hT,rfl⟩
  have hρ' : ρ ∈ Icc (criticalValue c p/16) (criticalValue c p*parentOuter p) :=
    ⟨hρ.1.le,hρ.2.le⟩
  have hend := physical_parentPath_endpoint_targetSlit hp hc hρ'
  refine ⟨hend.1,hend.2,fun t ht => physical_parentPath_open_mem_target hp hc hρ' ht,?_⟩
  intro t ht u hu he
  have hρ0 : 0 < ρ := (div_pos hc.2.1 (by norm_num)).trans hρ.1
  have hs0 : 0 < ρ/criticalValue c p := div_pos hρ0 hc.2.1
  have hmul : criticalValue c p*(ρ/criticalValue c p) = ρ := by field_simp [hc.2.1.ne']
  have hrepr (v : ℝ) := scaled_parentPath_eq c p (ρ/criticalValue c p) v
  simp only [hmul] at hrepr
  change CircularCrestEnergy.point (-((3*criticalValue c p/4 : ℝ) : ℂ)) ρ t =
    CircularCrestEnergy.point (-((3*criticalValue c p/4 : ℝ) : ℂ)) ρ u at he
  rw [← hrepr t,← hrepr u] at he
  have hdC : (criticalValue c p : ℂ) ≠ 0 := by exact_mod_cast hc.2.1.ne'
  exact parentPath_injOn hs0 ht hu (mul_left_cancel₀ hdC he)

/-- A literal physical collar realization. Both moduli are defined by
all measurable densities on the plane and the actual arclength metrics. -/
structure RealizedCollar {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) (F : Family p c) (α r : ℝ) : Prop where
  parent_proper : ProperParentFamily c p (parentFamily c p)
  descendant_proper : ProperDescendantFamily c p α (descendants hp hc F r)
  parent_modulus : (modulus (parentFamily c p)).toReal =
    Real.log (2-2/(p : ℝ))/(2*Real.pi)
  descendant_modulus : modulus (descendants hp hc F r) =
    ∫⁻ s in Ioo (1/16 : ℝ) r, ENNReal.ofReal (1/(s*angle F s))
  exact_ratio : (modulus (descendants hp hc F r)).toReal /
    (modulus (parentFamily c p)).toReal =
      CrestIntegralLimit.radialCoefficient p (realAngle F) r
  positive_ratio : (1/3 : ℝ) < (modulus (descendants hp hc F r)).toReal /
    (modulus (parentFamily c p)).toReal
  maximal_parameters : ∀ s ∈ Ioo (1/16 : ℝ) r,
    connectedComponentIn (fourthSurvivingParameters c p s) ((realAngle F s+1)/2) =
      Ioo (realAngle F s) 1
  ancestry : ∀ γ ∈ descendants hp hc F r,
    ∃ s ∈ Ioo (1/16 : ℝ) r, γ.duration = angle F s ∧
      (∀ t : ℝ, γ t = ((quadraticMap c)^[4*p])
        ((criticalValue c p : ℂ)*CircularCrestEnergy.point center s t)) ∧
      ∀ u ∈ Ioo (-1 : ℝ) 1,
        (∀ m ≤ 2, ((quadraticMap c)^[m*p])
          ((criticalValue c p : ℂ)*circlePoint s u) ∈ physicalSlitSource c p) ∧
        (((quadraticMap c)^[3*p]) ((criticalValue c p : ℂ)*circlePoint s u) ∈
          physicalSlitSource c p ↔ u ≠ realAngle F s) ∧
        (∀ m ∈ Icc (1 : ℕ) 3, ((quadraticMap c)^[m*p])
          ((criticalValue c p : ℂ)*circlePoint s u) ∈ physicalSlitTarget c p)

theorem realize_collar {p : ℕ} (hp : 17 ≤ p) {c r α : ℝ}
    (hc : ActualTip p c) (hS : StrictSupport c p) (F : Family p c)
    (hα : α ∈ Ioo (518/1000 : ℝ) (519/1000))
    (hr : r ∈ Ioo (663/10000 : ℝ) (133/2000)) (hzero : terminal F r = -1) :
    RealizedCollar hp hc F α r := by
  have hr' : r ∈ Icc (1/16 : ℝ) (133/2000) := ⟨by linarith [hr.1],hr.2.le⟩
  refine ⟨parentFamily_proper hp hc,descendants_proper hp hc hS F hα hr hzero,
    ?_,descendants_modulus hp hc hS F hr.2.le,?_,?_,?_,?_⟩
  · rw [← parentWidth_eq_modulus hp hc,parentWidth_eq hp hc]
  · rw [← parentWidth_eq_modulus hp hc]
    exact widthRatio_eq_radialCoefficient hp hc hS F hr'
  · rw [← parentWidth_eq_modulus hp hc]
    exact actual_widthRatio_gt_third hp hc hS F ⟨hr.1.le,hr.2.le⟩
  · intro s hs
    exact fourth_q_midpoint_component hp hc hS F ⟨hs.1.le,hs.2.le.trans hr.2.le⟩
      (retained_radius_gate hp hc F hr hzero hs)
  · intro γ hγ
    exact descendant_full_ancestry hp hc hS F hr hzero hγ

/-- Uniform existence of proper physical collars, with all support and
path hypotheses discharged after one common return-index threshold. -/
theorem eventually_every_actual_tip_realizes_collar :
    ∀ᶠ n : ℕ in atTop, ∀ c : ℝ, ∀ hc : ActualTip (n+17) c,
      ∀ F : Family (n+17) c,
        ∃ α ∈ Ioo (518/1000 : ℝ) (519/1000),
          normalizedReturn c (n+17) (α : ℂ) = (α : ℂ) ∧
          ∃ r ∈ Ioo (663/10000 : ℝ) (133/2000), terminal F r = -1 ∧
            RealizedCollar (by omega) hc F α r := by
  filter_upwards [eventually_all_strict_support] with n hn
  intro c hc F
  obtain ⟨α,hα,hfixed,r,hr,hzero,_⟩ :=
    actual_complete_cut_classification (by omega) hc F
  exact ⟨α,hα,hfixed,r,hr,hzero,realize_collar (by omega) hc (hn c hc) F hα hr hzero⟩

/-- The selected original-plane proper circular parents and proper
four-return descendants have an actual positive modulus-ratio limit.
Every parameter, crossing, cut and moving endpoint is constructed. -/
theorem exists_proper_physical_transport_limit :
    ∃ c : ℕ → ℝ, ∃ hc : ∀ n, ActualTip (n+17) (c n),
      ∃ F : ∀ n, Family (n+17) (c n), ∃ α radii : ℕ → ℝ,
        (∀ n, α n ∈ Ioo (518/1000 : ℝ) (519/1000) ∧
          normalizedReturn (c n) (n+17) (α n : ℂ) = (α n : ℂ) ∧
          radii n ∈ Ioo (663/10000 : ℝ) (133/2000) ∧
          terminal (F n) (radii n) = -1) ∧
        (∀ᶠ n in atTop, RealizedCollar (by omega) (hc n) (F n) (α n) (radii n)) ∧
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
  · filter_upwards [actual_strict_support c hc] with n hn
    exact realize_collar (by omega) (hc n) hn (F n) (hα n) (hr n) (he n)
  · have heq : (fun n => widthRatio (by omega) (hc n) (F n) (radii n)) =
        (fun n => (modulus (descendants (by omega) (hc n) (F n) (radii n))).toReal /
          (modulus (parentFamily (c n) (n+17))).toReal) := by
      funext n
      unfold widthRatio
      rw [parentWidth_eq_modulus (by omega) (hc n)]
    rwa [heq] at hclim

end
end ActualCrestTransportLimit

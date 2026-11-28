import TwoLevelSelection
import TwoLevelPhysicalGate
import TwoLevelOuterDomain
import LimitingCrestPersistence

/-!
# Uniform physical gates in an infinite two-level quadratic family

The outer and inner restrictions are components of complete polynomial
pullbacks in the same dynamical plane. Both periods vary. The period
separation pays for the full intermediate-orbit perturbation and the
actual critical-relation shooting, rather than assuming either estimate.
-/

namespace TwoLevelPhysicalGates

open Set Function Metric
open LimitingCrestQuadraticReturn LimitingCrest NearTwoShooting
open TwoLevelOuterChart TwoLevelConjugacy TwoLevelSelection
open TwoLevelGateDomain TwoLevelPhysicalGate ThreeReturnParent

noncomputable section

theorem selected_central_gate {p q : ℕ} (hq : 17 ≤ q)
    (hpq : 10*q+30 ≤ p) {c : ℝ} (h : Selected p q c) :
    CentralGate c (q*p) :=
  central_gate_of_estimates c (q*p) (Nat.mul_pos (by omega) (by omega))
    h.physical_scale_negative.ne h.inner_coefficient h.complete_disk_error h.complete_collision

theorem selected_phase_identity {p q : ℕ} {c : ℝ} (h : Selected p q c)
    (j : ℕ) (z : ℂ) :
    (returnCoefficient p c : ℂ)*
      ((quadraticMap c)^[j*p]) ((criticalValue c (q*p) : ℂ)*z) =
        ((outerMap c p)^[j]) ((secondScale c p q : ℂ)*z) := by
  have hA := (coefficient_negative h.first_coefficient).ne
  have hAC : (returnCoefficient p c : ℂ) ≠ 0 := by exact_mod_cast hA
  have hin : (secondScale c p q : ℂ)*z/(returnCoefficient p c : ℂ) =
      (criticalValue c (q*p) : ℂ)*z := by
    unfold secondScale
    push_cast
    field_simp [hAC]
  rw [TwoLevelConjugacy.outerMap_iterate_scale c p hA, hin]

/-- Every phase of the entire second source stays in the same actual
outer source. The inclusion is uniform over all complex source points. -/
theorem selected_phases_nested {p q : ℕ} (hq : 17 ≤ q)
    (hpq : 10*q+30 ≤ p) {c : ℝ} (h : Selected p q c)
    (j : ℕ) (hj : j ≤ q) :
    ((quadraticMap c)^[j*p]) '' physicalParentSource c (q*p) ⊆
      TwoLevelOuterDomain.source c p := by
  have hp : 17 ≤ p := by omega
  have hcentral := selected_central_gate hq hpq h
  have hA := (coefficient_negative h.first_coefficient).ne
  have hAC : (returnCoefficient p c : ℂ) ≠ 0 := by exact_mod_cast hA
  rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
  have hzR : ‖z‖ ≤ 23/20 := by
    exact (show ‖z‖ < 23/20 by
      simpa using hcentral.closure_inside (subset_closure hz)).le
  have hb := TwoLevelOuterDomain.monic_disk_in_source hp h.first_critical_orbit
    h.first_scale.1 h.first_scale.2 h.first_coefficient (h.complete_phase_disk hzR j hj)
  rw [← selected_phase_identity h j z] at hb
  have he (w : ℂ) : (returnCoefficient p c : ℂ)*w/(returnCoefficient p c : ℂ) = w := by
    field_simp [hAC]
  simpa only [he] using hb

/-- No noncentral phase of the second source returns to its physical
target before the q-th outer return. -/
theorem selected_inner_first_return {p q : ℕ} (hq : 17 ≤ q)
    (hpq : 10*q+30 ≤ p) {c : ℝ} (h : Selected p q c)
    (j : ℕ) (hj : 1 ≤ j) (hjq : j < q) :
    Disjoint (((quadraticMap c)^[j*p]) '' physicalParentSource c (q*p))
      (physicalTarget c (q*p)) := by
  have hcentral := selected_central_gate hq hpq h
  have hA := coefficient_negative h.first_coefficient
  have hAa : 0 < |returnCoefficient p c| := abs_pos.mpr hA.ne
  have hD : 0 < secondScale c p q := by linarith [h.second_scale.1, scale_pos q]
  have hproduct : |returnCoefficient p c| *|criticalValue c (q*p)| =
      secondScale c p q := by
    rw [← abs_mul, ← secondScale, abs_of_pos hD]
  apply Set.disjoint_left.mpr
  rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩ hy
  have hzR : ‖z‖ ≤ 23/20 := by
    exact (show ‖z‖ < 23/20 by
      simpa using hcentral.closure_inside (subset_closure hz)).le
  have hlow := h.noncentral_phases hzR j hj hjq
  rw [← selected_phase_identity h j z, norm_mul,
    Complex.norm_real, Real.norm_eq_abs] at hlow
  have hy' : ‖((quadraticMap c)^[j*p]) ((criticalValue c (q*p) : ℂ)*z)‖ <
      |criticalValue c (q*p)| *(23/20) := by simpa [physicalTarget] using hy
  have hm := mul_lt_mul_of_pos_left hy' hAa
  rw [← mul_assoc, hproduct] at hm
  nlinarith [h.second_scale.2, scale_small hq]

/-- Literal physical points witnessing the full radial crest interval.
The normalized return in this statement is the complete original iterate. -/
def PhysicalCorridor (c : ℝ) (n : ℕ) : Prop :=
  ∀ s ∈ Icc (63/1000 : ℝ) (33/500), ∃ u ∈ Ioo (-1/100 : ℝ) (1/100),
    circlePoint s u ∈ parentSource c n ∧
    (criticalValue c n : ℂ)*circlePoint s u ∈ physicalParentSource c n ∧
    ‖(criticalValue c n : ℂ)*circlePoint s u+((3*criticalValue c n/4 : ℝ) : ℂ)‖ =
      |criticalValue c n| *s ∧
    (normalizedReturn c n (circlePoint s u)).re = 0 ∧
    0 < (normalizedReturn c n (circlePoint s u)).im ∧
    (((normalizedReturn c n)^[2]) (circlePoint s u)).im = 0 ∧
    (((normalizedReturn c n)^[3]) (circlePoint s u)).im = 0 ∧
    (-999/1000 : ℝ) < (((normalizedReturn c n)^[3]) (circlePoint s u)).re ∧
    (((normalizedReturn c n)^[3]) (circlePoint s u)).re < -977/1000 ∧
    (((normalizedReturn c n)^[3]) (circlePoint s u)).re <
      -(((normalizedReturn c n)^[4]) 0).re

theorem selected_physical_corridor {p q : ℕ} (hq : 17 ≤ q)
    (hpq : 10*q+30 ≤ p) {c : ℝ} (h : Selected p q c) :
    PhysicalCorridor c (q*p) := by
  have hcentral := selected_central_gate hq hpq h
  intro s hs
  obtain ⟨u,hu,hr,hre,him,h2,h3,hlo,hhi,hcut⟩ := uniform_perturbed_corridor
    (normalizedReturn c (q*p)) (TwoLevelConjugacy.normalizedReturn_continuous c (q*p))
    (fun t => TwoLevelConjugacy.normalizedReturn_real c t (q*p))
    (fun t => TwoLevelConjugacy.normalizedReturn_imaginary c t (q*p)
      (Nat.mul_pos (by omega) (by omega)))
    h.inner_coefficient hs h.complete_disk_error
  have hg : circlePoint s u ∈ gateDisk := by
    change ‖circlePoint s u+(3/4 : ℂ)‖ ≤ (133/2000 : ℝ)
    rw [hr]
    linarith [hs.2]
  have hz := hcentral.full_gate_disk hg
  have hrphysical :
      ‖(criticalValue c (q*p) : ℂ)*circlePoint s u+
        ((3*criticalValue c (q*p)/4 : ℝ) : ℂ)‖ = |criticalValue c (q*p)| *s := by
    have he : (criticalValue c (q*p) : ℂ)*circlePoint s u+
        ((3*criticalValue c (q*p)/4 : ℝ) : ℂ) =
          (criticalValue c (q*p) : ℂ)*(circlePoint s u+(3/4 : ℂ)) := by
      push_cast
      ring
    rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs, hr]
  exact ⟨u, hu, hz, ⟨circlePoint s u, hz, rfl⟩, hrphysical,
    hre, him, h2, h3, hlo, hhi, hcut⟩

/-- The certified two-level geometric package, in one original dynamical plane. -/
structure PhysicalTwoLevelGate (p q : ℕ) (c : ℝ) : Prop where
  selected : Selected p q c
  outer_open : IsOpen (TwoLevelOuterDomain.source c p)
  outer_connected : IsConnected (TwoLevelOuterDomain.source c p)
  outer_compact : IsCompact (closure (TwoLevelOuterDomain.source c p))
  outer_collar : closure (TwoLevelOuterDomain.source c p) ⊆
    ball 0 (TwoLevelOuterDomain.targetRadius p/2)
  outer_image : ((quadraticMap c)^[p]) '' TwoLevelOuterDomain.source c p =
    ball 0 (TwoLevelOuterDomain.targetRadius p)
  outer_proper : IsProperMap (TwoLevelOuterDomain.sourceMap c p)
  first_outer_return : ∀ j, 1 ≤ j → j < p → ∀ z : ℂ,
    ‖z‖ ≤ TwoLevelOuterDomain.targetRadius p →
    TwoLevelOuterDomain.targetRadius p < ‖((quadraticMap c)^[j]) z‖
  outer_fibers : ∀ y ∈ ball (0 : ℂ) (TwoLevelOuterDomain.targetRadius p),
    {z : ℂ | z ∈ TwoLevelOuterDomain.source c p ∧ ((quadraticMap c)^[p]) z = y}.ncard =
      if y = ((quadraticMap c)^[p]) 0 then 1 else 2
  inner : PhysicalGate c (q*p)
  nested_phases : ∀ j ≤ q, ((quadraticMap c)^[j*p]) '' physicalParentSource c (q*p) ⊆
    TwoLevelOuterDomain.source c p
  first_inner_return : ∀ j, 1 ≤ j → j < q →
    Disjoint (((quadraticMap c)^[j*p]) '' physicalParentSource c (q*p))
      (physicalTarget c (q*p))
  corridor : PhysicalCorridor c (q*p)

/-- An infinite family with two unbounded periods has actual nested proper
two-sheeted returns and a whole physical round gate with a uniform radial
crest interval. All estimates and the original critical relation are outputs. -/
theorem exists_physical_two_level_gate (p q : ℕ)
    (hq : 17 ≤ q) (hpq : 10*q+30 ≤ p) :
    ∃ c : ℝ, PhysicalTwoLevelGate p q c := by
  have hp : 17 ≤ p := by omega
  obtain ⟨c,h⟩ := exists_selected p q hq hpq
  have hcl := TwoLevelOuterDomain.source_closure hp h.first_critical_orbit
    h.first_scale.1 h.first_scale.2 h.first_coefficient
  refine ⟨c, h, TwoLevelOuterDomain.source_open c p,
    TwoLevelOuterDomain.source_connected hp h.first_scale.1 h.first_scale.2,
    hcl.2, hcl.1, TwoLevelOuterDomain.source_image hp h.first_scale.1 h.first_scale.2,
    TwoLevelOuterDomain.sourceMap_proper c p,
    (fun j hj hjp _ hz => TwoLevelOuterDomain.outer_first_return_exclusion hp
      h.parameter_band h.first_critical_orbit h.first_scale.1 h.first_scale.2
      h.first_itinerary j hj hjp hz), ?_,
    physical_gate_of_central (selected_central_gate hq hpq h),
    selected_phases_nested hq hpq h, selected_inner_first_return hq hpq h,
    selected_physical_corridor hq hpq h⟩
  intro y hy
  simpa only [ThreeReturnParent.quadratic_iterate_zero] using
    TwoLevelOuterDomain.source_fiber_ncard hp h.first_critical_orbit
      h.first_scale.1 h.first_scale.2 h.first_coefficient hy

end
end TwoLevelPhysicalGates

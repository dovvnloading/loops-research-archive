import ActualCentralEscape
import PhysicalCentralCarrier

/-!
# Explicit complex escape in the original quadratic dynamical plane

Every definition below uses the original quadratic polynomial, its literal
critical orbit, or the canonical source component of the complete return.
The normalized escape estimate is transported by an exact semiconjugacy.
-/

namespace PhysicalCentralEscape

open Set Function Metric
open LimitingCrestQuadraticReturn NearTwoTip
open ThreeReturnDomain ThreeReturnCollar ActualThreeReturnNormalization
open ActualCentralSlit ActualCentralEscape PhysicalCentralCarrier
open SlitJoukowski LoopsParabolic

noncomputable section

/-- Exterior amplitude at the literal sixth critical return scale. -/
def physicalAmplitude (c : ℝ) (p : ℕ) (z : ℂ) : ℝ :=
  slitAmplitude (criticalValue c (6*p)) z

/-- Filled set of the actual physical restriction, using complete
quadratic iterates and the canonically selected physical source. -/
def physicalFilledSource (c : ℝ) (p : ℕ) : Set ℂ :=
  {z | ∀ n : ℕ, ((quadraticMap c)^[(3*p)*n]) z ∈ physicalSource c p}

theorem physical_radius_pos {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) : 0 < criticalValue c (6*p) := by
  rw [critical_sixth_eq_scale hp hc]
  exact mul_pos hc.2.1 (centralRadius_pos hp hc)

/-- The physical exterior amplitude is exactly the normalized one. -/
theorem physicalAmplitude_scale {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) (z : ℂ) :
    physicalAmplitude c p ((criticalValue c p : ℂ)*z) =
      slitAmplitude (centralRadius c p) z := by
  unfold physicalAmplitude slitAmplitude
  rw [critical_sixth_eq_scale hp hc]
  apply congrArg amplitude
  unfold normalize
  have he : (2 / (criticalValue c p * centralRadius c p)) * criticalValue c p =
      2 / centralRadius c p := by
    field_simp [hc.2.1.ne', (centralRadius_pos hp hc).ne']
  rw [← mul_assoc, ← Complex.ofReal_mul, he]

/-- Every normalized return iterate is the literal physical polynomial
iterate, with the original critical scale. -/
theorem physical_iterate_scale {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) (n : ℕ) (z : ℂ) :
    (criticalValue c p : ℂ) * ((threeReturn c p)^[n]) z =
      ((quadraticMap c)^[(3*p)*n]) ((criticalValue c p : ℂ)*z) := by
  have hsemi : Semiconj (fun w : ℂ => (criticalValue c p : ℂ)*w)
      (threeReturn c p) ((quadraticMap c)^[3*p]) :=
    fun w => normalized_iterate_scale c p hc.2.1.ne' 3 w
  simpa only [iterate_mul] using (hsemi.iterate_right n) z

theorem mem_physicalSource_scale_iff {p : ℕ} {c : ℝ}
    (hc : ActualTip p c) (z : ℂ) :
    (criticalValue c p : ℂ)*z ∈ physicalSource c p ↔ z ∈ source c p := by
  have hd : (criticalValue c p : ℂ) ≠ 0 := by exact_mod_cast hc.2.1.ne'
  constructor
  · rintro ⟨w, hw, he⟩
    have h : w = z := mul_left_cancel₀ hd he
    simpa only [h] using hw
  · intro hz
    exact ⟨z, hz, rfl⟩

theorem physical_filled_scale_iff {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) (z : ℂ) :
    (criticalValue c p : ℂ)*z ∈ physicalFilledSource c p ↔
      z ∈ filledSource c p := by
  change (∀ n : ℕ, ((quadraticMap c)^[(3*p)*n])
    ((criticalValue c p : ℂ)*z) ∈ physicalSource c p) ↔
      ∀ n : ℕ, ((threeReturn c p)^[n]) z ∈ source c p
  simp only [← physical_iterate_scale hp hc, mem_physicalSource_scale_iff hc]

theorem physical_filled_iff_amplitude_one {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) (z : ℂ) :
    z ∈ physicalFilledSource c p ↔ physicalAmplitude c p z = 1 := by
  have hd : (criticalValue c p : ℂ) ≠ 0 := by exact_mod_cast hc.2.1.ne'
  let w := z / (criticalValue c p : ℂ)
  have he : (criticalValue c p : ℂ)*w = z := by
    dsimp [w]
    field_simp [hd]
  rw [← he, physical_filled_scale_iff hp hc, filledSource_eq_slit hp hc,
    physicalAmplitude_scale hp hc]
  exact (slitAmplitude_eq_one_iff (centralRadius_pos hp hc) w).symm

theorem physicalFilledSource_eq_slit {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) :
    physicalFilledSource c p = realSegment (criticalValue c (6*p)) := by
  ext z
  rw [physical_filled_iff_amplitude_one hp hc]
  exact slitAmplitude_eq_one_iff (physical_radius_pos hp hc) z

/-- The complete complex filled set of the selected physical restriction
is the interval with the original third and sixth critical-orbit endpoints. -/
theorem physicalFilledSource_eq_orbit_interval {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) :
    physicalFilledSource c p =
      Complex.ofReal '' Icc (criticalValue c (3*p)) (criticalValue c (6*p)) := by
  rw [physicalFilledSource_eq_slit hp hc]
  have he : criticalValue c (3*p) = -criticalValue c (6*p) := by
    rw [critical_third_eq_negative_scale hp hc, critical_sixth_eq_scale hp hc]
    ring
  rw [he]
  rfl

/-- The explicit amplitude expands for the original complete polynomial
return, uniformly in p, throughout the physical control disk. -/
theorem physical_amplification {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {z : ℂ} (hz : ‖z‖ ≤ criticalValue c p / 6) :
    physicalAmplitude c p z ^ 7 ≤
      physicalAmplitude c p (((quadraticMap c)^[3*p]) z) ^ 6 := by
  have hd : (criticalValue c p : ℂ) ≠ 0 := by exact_mod_cast hc.2.1.ne'
  let w := z / (criticalValue c p : ℂ)
  have he : (criticalValue c p : ℂ)*w = z := by
    dsimp [w]
    field_simp [hd]
  have hw : ‖w‖ ≤ 1/6 := by
    dsimp [w]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc.2.1]
    apply (div_le_iff₀ hc.2.1).mpr
    linarith only [hz]
  have h := actual_amplification hp hc hw
  rw [← physicalAmplitude_scale hp hc w,
    ← physicalAmplitude_scale hp hc (threeReturn c p w)] at h
  rw [normalized_iterate_scale c p hc.2.1.ne' 3 w, he] at h
  exact h

/-- Explicit finite escape for the literal quadratic iterate. Its budget
uses only the actual critical orbit and the initial physical point. -/
theorem physical_finite_exponential_escape {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {z : ℂ} (N : ℕ)
    (hbudget : (16/5 : ℝ)^(6^N) < physicalAmplitude c p z ^ (7^N)) :
    ∃ n ≤ N, criticalValue c p / 6 <
      ‖((quadraticMap c)^[(3*p)*n]) z‖ := by
  have hd : (criticalValue c p : ℂ) ≠ 0 := by exact_mod_cast hc.2.1.ne'
  let w := z / (criticalValue c p : ℂ)
  have he : (criticalValue c p : ℂ)*w = z := by
    dsimp [w]
    field_simp [hd]
  have hbudget' : (16/5 : ℝ)^(6^N) <
      slitAmplitude (centralRadius c p) w ^ (7^N) := by
    rw [← physicalAmplitude_scale hp hc w, he]
    exact hbudget
  obtain ⟨n, hn, hnorm⟩ := actual_finite_exponential_escape hp hc N hbudget'
  refine ⟨n, hn, ?_⟩
  rw [← he, ← physical_iterate_scale hp hc n w, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc.2.1]
  nlinarith only [hnorm, hc.2.1]

/-- Every point outside the canonical filled set eventually exits the
fixed physical control disk. -/
theorem physical_complex_escape {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {z : ℂ} (hz : z ∉ physicalFilledSource c p) :
    ∃ n : ℕ, criticalValue c p / 6 <
      ‖((quadraticMap c)^[(3*p)*n]) z‖ := by
  have hd : (criticalValue c p : ℂ) ≠ 0 := by exact_mod_cast hc.2.1.ne'
  let w := z / (criticalValue c p : ℂ)
  have he : (criticalValue c p : ℂ)*w = z := by
    dsimp [w]
    field_simp [hd]
  have hw : w ∉ realSegment (centralRadius c p) := by
    intro hw
    have hwf : w ∈ filledSource c p := by
      rwa [filledSource_eq_slit hp hc]
    exact hz (he ▸ (physical_filled_scale_iff hp hc w).mpr hwf)
  obtain ⟨n, hnorm⟩ := actual_complex_escape hp hc hw
  refine ⟨n, ?_⟩
  rw [← he, ← physical_iterate_scale hp hc n w, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc.2.1]
  nlinarith only [hnorm, hc.2.1]

end
end PhysicalCentralEscape

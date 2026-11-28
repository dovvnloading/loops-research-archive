import ActualThreeReturnCylinders

/-!
# Identification with the orbit-defined physical central carrier

The coordinate interval used by the cylinder theorem is exactly the
archive's actual central filled interval: its endpoints are the third
and sixth critical returns of the original quadratic polynomial.
-/

namespace PhysicalCentralCarrier

open Set Function
open LimitingCrestQuadraticReturn NearTwoTip GlobalCrestSourceGates
open ActualThreeReturnNormalization ActualThreeReturnCylinders
open AngularCylinderExpansion

noncomputable section

/-- The central radius is calibrated by the literal third critical return. -/
theorem critical_third_eq_negative_scale {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) :
    criticalValue c (3*p) = -criticalValue c p*centralRadius c p := by
  have h := actualOrbit_physical c 0 p 3 hc.2.1
  simp only [Complex.ofReal_zero, mul_zero, ThreeReturnParent.quadratic_iterate_zero] at h
  have hr := Complex.ofReal_injective h
  calc
    criticalValue c (3*p) = criticalValue c p*actualOrbit c p 0 3 := hr
    _ = -criticalValue c p*centralRadius c p := by
      unfold centralRadius
      ring

/-- The signed critical relation gives the opposite physical endpoint. -/
theorem critical_sixth_eq_scale {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) :
    criticalValue c (6*p) = criticalValue c p*centralRadius c p := by
  have h := hc.2.2.2.2.1
  rw [critical_third_eq_negative_scale hp hc] at h
  linarith only [h]

theorem physicalPoint_one {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) :
    physicalPoint c p 1 = (criticalValue c (3*p) : ℂ) := by
  rw [critical_third_eq_negative_scale hp hc]
  simp only [physicalPoint, mul_one]

theorem physicalPoint_neg_one {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) :
    physicalPoint c p (-1) = (criticalValue c (6*p) : ℂ) := by
  rw [critical_sixth_eq_scale hp hc]
  apply congrArg (fun r : ℝ => (r : ℂ))
  change -criticalValue c p*centralRadius c p*(-1) =
    criticalValue c p*centralRadius c p
  ring

/-- The complete cylinder carrier is the actual central filled interval
with the original critical-orbit endpoints, rather than a supplied model. -/
theorem physicalInterval_eq {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) :
    physicalInterval c p =
      Complex.ofReal '' Icc (criticalValue c (3*p)) (criticalValue c (6*p)) := by
  have hs : 0 < criticalValue c p*centralRadius c p :=
    mul_pos hc.2.1 (centralRadius_pos hp hc)
  apply Set.ext
  intro z
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨-criticalValue c p*centralRadius c p*x, ?_, rfl⟩
    rw [critical_third_eq_negative_scale hp hc, critical_sixth_eq_scale hp hc]
    have hl := mul_le_mul_of_nonneg_left hx.1 hs.le
    have hu := mul_le_mul_of_nonneg_left hx.2 hs.le
    constructor <;> nlinarith only [hl, hu]
  · rintro ⟨r, hr, rfl⟩
    rw [critical_third_eq_negative_scale hp hc, critical_sixth_eq_scale hp hc] at hr
    refine ⟨-r/(criticalValue c p*centralRadius c p), ?_, ?_⟩
    · constructor
      · apply (le_div_iff₀ hs).mpr
        nlinarith only [hr.2]
      · apply (div_le_iff₀ hs).mpr
        nlinarith only [hr.1]
    · apply congrArg (fun s : ℝ => (s : ℂ))
      change -criticalValue c p*centralRadius c p*
        (-r/(criticalValue c p*centralRadius c p)) = r
      field_simp [hs.ne']
      <;> ring

/-- The explicit angular coordinate uses the literal sixth critical
return as its scale in the original dynamical plane. -/
def physicalAngle (c : ℝ) (p : ℕ) (z : ℂ) : ℝ :=
  Real.arccos (-z.re/criticalValue c (6*p))

/-- The physical angular coordinate agrees exactly with the cosine
coordinate under the orbit-defined normalization. -/
theorem physicalAngle_physicalPoint {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) (x : ℝ) :
    physicalAngle c p (physicalPoint c p x) = Real.arccos x := by
  have hs : 0 < criticalValue c p*centralRadius c p :=
    mul_pos hc.2.1 (centralRadius_pos hp hc)
  unfold physicalAngle
  rw [critical_sixth_eq_scale hp hc]
  simp only [physicalPoint, Complex.ofReal_re]
  apply congrArg Real.arccos
  field_simp [hs.ne']
  <;> ring

/-- The literal three-return preserves the entire physical carrier. -/
theorem physical_interval_invariant {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) :
    MapsTo ((quadraticMap c)^[3*p]) (physicalInterval c p) (physicalInterval c p) := by
  rintro z ⟨x, hx, rfl⟩
  exact ⟨centralMap c p x, (centralMap_square_bounds hp hc).mapsTo hx,
    physicalPoint_semiconj hp hc x⟩

/-- Every actual branch of the physical three-return expands the
explicit angular distance by at least `30/19`, uniformly in the
original return period.  Endpoints and the critical point are included. -/
theorem physical_angular_expansion {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {z w : ℂ}
    (hz : z ∈ physicalInterval c p) (hw : w ∈ physicalInterval c p)
    (hbranch : SameBranch z.re w.re) :
    (30/19 : ℝ)*|physicalAngle c p z-physicalAngle c p w| ≤
      |physicalAngle c p (((quadraticMap c)^[3*p]) z)-
        physicalAngle c p (((quadraticMap c)^[3*p]) w)| := by
  obtain ⟨x, hx, rfl⟩ := hz
  obtain ⟨y, hy, rfl⟩ := hw
  have ht := centralRadius_pos hp hc
  have hs := (physical_sameBranch_iff hp hc x y).mp hbranch
  have he := (centralMap_square_bounds hp hc).branch_bound hx hy hs
  have hratio : (19*centralRadius c p)/(2*(15*centralRadius c p)) = (19/30 : ℝ) := by
    field_simp [ht.ne']
    <;> ring
  rw [hratio] at he
  rw [(physicalPoint_semiconj hp hc x).symm, (physicalPoint_semiconj hp hc y).symm]
  simp only [physicalAngle_physicalPoint hp hc]
  change (30/19 : ℝ)*angleDistance x y ≤
    angleDistance (centralMap c p x) (centralMap c p y)
  nlinarith only [he]

end

end PhysicalCentralCarrier

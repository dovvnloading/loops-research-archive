import ActualThreeReturnCylinders
import CylinderCriticalHit

/-!
# A quantitative precritical mesh in the actual central interval

Every physical interval longer than the explicit depth bound contains a
point that reaches the actual critical point within that many returns.
The conclusion concerns the literal quadratic polynomial in physical
coordinates, with no straightening coordinate supplied as a hypothesis.
-/

namespace PhysicalCylinderEscape

open Set Function
open LimitingCrestQuadraticReturn NearTwoTip
open AngularCylinderExpansion ActualThreeReturnNormalization
open ActualThreeReturnCylinders

noncomputable section

/-- An explicit all-period, all-depth physical precritical-cut theorem. -/
theorem physical_precritical_mesh {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) (n : ℕ) {z w : ℂ}
    (hz : z ∈ physicalInterval c p) (hw : w ∈ physicalInterval c p)
    (horder : z.re < w.re)
    (hsize : criticalValue c p*centralRadius c p*Real.pi*(19/30 : ℝ)^n < w.re-z.re) :
    ∃ j : ℕ, j < n ∧ ∃ v : ℝ, v ∈ Ioo z.re w.re ∧
      ((quadraticMap c)^[(3*p)*j]) (v : ℂ) = 0 := by
  obtain ⟨x,hx,rfl⟩ := hz
  obtain ⟨y,hy,rfl⟩ := hw
  have ht := centralRadius_pos hp hc
  have hs : 0 < criticalValue c p*centralRadius c p := mul_pos hc.2.1 ht
  have hsn : -criticalValue c p*centralRadius c p < 0 :=
    mul_neg_of_neg_of_pos (neg_neg_of_pos hc.2.1) ht
  have hyx : y < x := by
    by_contra! h
    have hm := mul_le_mul_of_nonpos_left h hsn.le
    simp only [physicalPoint, Complex.ofReal_re] at horder
    linarith only [horder,hm]
  have hlen : (physicalPoint c p y).re-(physicalPoint c p x).re =
      criticalValue c p*centralRadius c p*(x-y) := by
    simp only [physicalPoint, Complex.ofReal_re]
    ring
  rw [hlen] at hsize
  have hthreshold : Real.pi*(19/30 : ℝ)^n < x-y :=
    (mul_lt_mul_left hs).mp (by simpa only [mul_assoc] using hsize)
  have hratio : (19*centralRadius c p)/(2*(15*centralRadius c p)) = (19/30 : ℝ) := by
    field_simp [ht.ne']
    <;> ring
  have hthreshold' : Real.pi*((19*centralRadius c p)/(2*(15*centralRadius c p)))^n < x-y := by
    rw [hratio]
    exact hthreshold
  obtain ⟨j,hj,u,hu,hzero⟩ := (centralMap_square_bounds hp hc).exists_interior_precritical
    n hy hx hyx hthreshold'
  refine ⟨j,hj,(physicalPoint c p u).re,?_,?_⟩
  · simp only [physicalPoint, Complex.ofReal_re]
    exact ⟨mul_lt_mul_of_neg_left hu.2 hsn, mul_lt_mul_of_neg_left hu.1 hsn⟩
  · have h := physicalPoint_iterate hp hc j u
    rw [hzero] at h
    simpa only [physicalPoint, Complex.ofReal_re, mul_zero, Complex.ofReal_zero] using h

/-- Every p in the analytic tail has a literal selected parameter with
the same physical precritical mesh rate at every depth. -/
theorem exists_uniform_physical_precritical_mesh (p : ℕ) (hp : 17 ≤ p) :
    ∃ c : ℝ, ActualTip p c ∧ ∀ (n : ℕ) (z w : ℂ),
      z ∈ physicalInterval c p → w ∈ physicalInterval c p → z.re < w.re →
      criticalValue c p*centralRadius c p*Real.pi*(19/30 : ℝ)^n < w.re-z.re →
      ∃ j : ℕ, j < n ∧ ∃ v : ℝ, v ∈ Ioo z.re w.re ∧
        ((quadraticMap c)^[(3*p)*j]) (v : ℂ) = 0 := by
  obtain ⟨c,hc⟩ := exists_actual_tip p hp
  exact ⟨c,hc,fun n _ _ hz hw ho hs => physical_precritical_mesh hp hc n hz hw ho hs⟩

end
end PhysicalCylinderEscape

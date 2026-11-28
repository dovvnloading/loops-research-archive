import ParentWaveElliptic
import ParentWaveEllipticBoundary
import Mathlib.Topology.Algebra.Field
import Mathlib.Analysis.Calculus.MeanValue

namespace ParentWaveElliptic

open Set Complex Metric Filter
open scoped Topology

noncomputable section

def fourthQuadrant : Set ℂ := {u | 0 < u.re ∧ u.im < 0}

theorem fourthQuadrant_open : IsOpen fourthQuadrant :=
  (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt Complex.continuous_im continuous_const)

theorem fourthQuadrant_convex : Convex ℝ fourthQuadrant :=
  (convex_halfSpace_re_gt 0).inter (convex_halfSpace_im_lt 0)

theorem fourthQuadrant_ne_zero {u : ℂ} (hu : u ∈ fourthQuadrant) : u ≠ 0 := by
  intro h
  simpa [h] using hu.1

theorem inv_mem_quadrant {u : ℂ} (hu : u ∈ fourthQuadrant) : u⁻¹ ∈ quadrant := by
  have hn := Complex.normSq_pos.mpr (fourthQuadrant_ne_zero hu)
  change 0 < (u⁻¹).re ∧ 0 < (u⁻¹).im
  simp only [Complex.inv_re, Complex.inv_im]
  exact ⟨div_pos hu.1 hn, div_pos (neg_pos.mpr hu.2) hn⟩

theorem inv_mem_fourthQuadrant {z : ℂ} (hz : z ∈ quadrant) :
    z⁻¹ ∈ fourthQuadrant := by
  have hz0 : z ≠ 0 := by
    intro h
    simpa [h] using hz.1
  have hn := Complex.normSq_pos.mpr hz0
  change 0 < (z⁻¹).re ∧ (z⁻¹).im < 0
  simp only [Complex.inv_re, Complex.inv_im]
  exact ⟨div_pos hz.1 hn, div_neg_of_neg_of_pos (neg_neg_of_pos hz.2) hn⟩

private theorem sqrt_sq (z : ℂ) : (Complex.sqrt z)^2 = z := by
  rw [Complex.sqrt, ← Complex.cpow_nat_mul]
  norm_num

private theorem sqrt_nonzero {z : ℂ} (hz : z ≠ 0) : Complex.sqrt z ≠ 0 := by
  intro h
  have he := sqrt_sq z
  exact hz (by simpa [h] using he.symm)

theorem differential_sq (B C : ℝ) (t : ℂ) :
    (differential B C t)^2 = 4 / ((t^2-(B:ℂ))*(t^2-(C:ℂ))) := by
  rw [differential, div_pow, mul_pow, sqrt_sq, sqrt_sq]
  norm_num

def invertedDifferential (B C : ℝ) (u : ℂ) : ℂ :=
  differential B C u⁻¹ * (-(u^2)⁻¹)

def infinityRoot (B C : ℝ) (u : ℂ) : ℂ :=
  2 / (Complex.sqrt (1-(B:ℂ)*u^2) * Complex.sqrt (1-(C:ℂ)*u^2))

theorem infinityRoot_sq (B C : ℝ) (u : ℂ) :
    (infinityRoot B C u)^2 = 4 / ((1-(B:ℂ)*u^2)*(1-(C:ℂ)*u^2)) := by
  rw [infinityRoot, div_pow, mul_pow, sqrt_sq, sqrt_sq]
  norm_num

theorem invertedDifferential_sq (B C : ℝ) {u : ℂ} (hu : u ≠ 0) :
    (invertedDifferential B C u)^2 = (infinityRoot B C u)^2 := by
  rw [invertedDifferential, mul_pow, differential_sq, infinityRoot_sq]
  have hB : (u⁻¹)^2-(B:ℂ) = (u^2)⁻¹*(1-(B:ℂ)*u^2) := by
    field_simp
  have hC : (u⁻¹)^2-(C:ℂ) = (u^2)⁻¹*(1-(C:ℂ)*u^2) := by
    field_simp
  rw [hB,hC]
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_sq]
  field_simp

theorem hasDerivAt_inverted (B C : ℝ) {G : ℂ → ℂ}
    (hG : ∀ t ∈ quadrant, HasDerivAt G (differential B C t) t)
    {u : ℂ} (hu : u ∈ fourthQuadrant) :
    HasDerivAt (fun u : ℂ => G u⁻¹) (invertedDifferential B C u) u := by
  exact (hG _ (inv_mem_quadrant hu)).comp u
    (hasDerivAt_inv (fourthQuadrant_ne_zero hu))

theorem infinityRoot_local_holomorphic (B C : ℝ) :
    ∃ r : ℝ, 0 < r ∧ DifferentiableOn ℂ (infinityRoot B C) (ball (0:ℂ) r) ∧
      ∀ u ∈ ball (0:ℂ) r, infinityRoot B C u ≠ 0 := by
  have hnear (A : ℝ) : ∀ᶠ u : ℂ in 𝓝 0, 1-(A:ℂ)*u^2 ∈ Complex.slitPlane := by
    have hc : ContinuousAt (fun u : ℂ => 1-(A:ℂ)*u^2) 0 := by fun_prop
    apply hc.tendsto.eventually
    simpa using Complex.isOpen_slitPlane.mem_nhds Complex.one_mem_slitPlane
  obtain ⟨r,hr,hBC⟩ := Metric.eventually_nhds_iff.mp ((hnear B).and (hnear C))
  refine ⟨r,hr,?_,?_⟩
  · intro u hu
    have hB := (hBC hu).1
    have hC := (hBC hu).2
    have hd (A : ℝ) (hA : 1-(A:ℂ)*u^2 ∈ Complex.slitPlane) :
        DifferentiableAt ℂ (fun v : ℂ => Complex.sqrt (1-(A:ℂ)*v^2)) u :=
      (Complex.differentiableAt_sqrt hA).comp u
        ((differentiableAt_const (1:ℂ)).sub ((differentiableAt_id.pow 2).const_mul (A:ℂ)))
    have hn (A : ℝ) (hA : 1-(A:ℂ)*u^2 ∈ Complex.slitPlane) :
        Complex.sqrt (1-(A:ℂ)*u^2) ≠ 0 := by
      intro h
      have he := sqrt_sq (1-(A:ℂ)*u^2)
      exact Complex.slitPlane_ne_zero hA (by simpa [h] using he.symm)
    exact ((differentiableAt_const (2:ℂ)).div ((hd B hB).mul (hd C hC))
      (mul_ne_zero (hn B hB) (hn C hC))).differentiableWithinAt
  · intro u hu
    exact div_ne_zero (by norm_num) (mul_ne_zero
      (sqrt_nonzero (Complex.slitPlane_ne_zero (hBC hu).1))
      (sqrt_nonzero (Complex.slitPlane_ne_zero (hBC hu).2)))

theorem invertedDifferential_continuous (B C : ℝ) :
    ContinuousOn (invertedDifferential B C) fourthQuadrant := by
  have hc : ContinuousOn (fun u : ℂ => differential B C u⁻¹) fourthQuadrant :=
    (differential_differentiable B C).continuousOn.comp
      (continuousOn_id.inv₀ (fun u hu => fourthQuadrant_ne_zero hu))
      (fun u hu => inv_mem_quadrant hu)
  exact hc.mul (((continuousOn_id.pow 2).inv₀
    (fun u hu => pow_ne_zero _ (fourthQuadrant_ne_zero hu))).neg)

theorem primitive_extends_at_infinity (B C : ℝ) {G : ℂ → ℂ}
    (hG : ∀ t ∈ quadrant, HasDerivAt G (differential B C t) t) :
    ∃ r : ℝ, 0 < r ∧ ∃ E : ℂ → ℂ,
      DifferentiableOn ℂ E (ball (0:ℂ) r) ∧
      EqOn (fun u : ℂ => G u⁻¹) E (ball (0:ℂ) r ∩ fourthQuadrant) := by
  obtain ⟨r,hr,hh,hn⟩ := infinityRoot_local_holomorphic B C
  refine ⟨r,hr,?_⟩
  exact ParentWaveEllipticBoundary.exists_extension_of_derivative_sq
    (isOpen_ball.inter fourthQuadrant_open)
    ((convex_ball (0:ℂ) r).inter fourthQuadrant_convex).isPreconnected
    isOpen_ball (convex_ball (0:ℂ) r) inter_subset_left
    (fun u hu => hasDerivAt_inverted B C hG hu.2)
    ((invertedDifferential_continuous B C).mono inter_subset_right)
    hh (fun u hu => hn u hu.1)
    (fun u hu => invertedDifferential_sq B C (fourthQuadrant_ne_zero hu.2))

theorem primitive_uniform_limit_at_infinity (B C : ℝ) {G : ℂ → ℂ}
    (hG : ∀ t ∈ quadrant, HasDerivAt G (differential B C t) t) :
    ∃ L : ℂ, ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧
      ∀ z ∈ quadrant, R < ‖z‖ → dist (G z) L < ε := by
  obtain ⟨r,hr,E,hE,hEq⟩ := primitive_extends_at_infinity B C hG
  refine ⟨E 0,?_⟩
  intro ε hε
  have hc : ContinuousAt E 0 :=
    ((hE 0 (mem_ball_self hr)).differentiableAt
      (isOpen_ball.mem_nhds (mem_ball_self hr))).continuousAt
  obtain ⟨δ,hδ,hclose⟩ := Metric.continuousAt_iff.mp hc ε hε
  have hη : 0 < min r δ := lt_min hr hδ
  refine ⟨(min r δ)⁻¹,inv_pos.mpr hη,?_⟩
  intro z hz hzR
  have hz0 : z ≠ 0 := by
    intro h
    simpa [h] using hz.1
  have hsmall : ‖z⁻¹‖ < min r δ := by
    rw [norm_inv]
    exact (inv_lt_comm₀ (norm_pos_iff.mpr hz0) hη).mpr hzR
  have hball : z⁻¹ ∈ ball (0:ℂ) r := by
    simpa only [mem_ball,dist_zero_right] using hsmall.trans_le (min_le_left _ _)
  have he : G z = E z⁻¹ := by
    simpa only [inv_inv] using hEq ⟨hball,inv_mem_fourthQuadrant hz⟩
  rw [he]
  apply hclose
  simpa only [dist_zero_right] using hsmall.trans_le (min_le_right _ _)

end
end ParentWaveElliptic

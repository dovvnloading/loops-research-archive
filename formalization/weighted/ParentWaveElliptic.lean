import Mathlib.Analysis.Complex.SqrtDeriv
import Mathlib.Analysis.Complex.Convex
import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Tactic

/-!
# The concrete elliptic differential in quadrant coordinates

Internal analytic development for the canonical parent width calculation.
The coordinate is `t = sqrt (z-a)`.  The differential below is the literal
pullback of `dz / sqrt ((z-a)*(z-b)*(z-c))`, with `B=b-a` and `C=c-a`.
The rectangle boundary identification and the canonical modulus comparison
must accompany this development before it gives a parent-width result.
-/

namespace ParentWaveElliptic

open Set Complex
open scoped Topology

noncomputable section

def quadrant : Set ℂ := {z | 0 < z.re ∧ 0 < z.im}

private theorem quadrant_open : IsOpen quadrant :=
  (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt continuous_const Complex.continuous_im)

private theorem quadrant_convex : Convex ℝ quadrant :=
  (convex_halfSpace_re_gt 0).inter (convex_halfSpace_im_gt 0)

def differential (B C : ℝ) (t : ℂ) : ℂ :=
  2 / (Complex.sqrt (t^2-(B:ℂ)) * Complex.sqrt (t^2-(C:ℂ)))

private theorem square_sub_im_pos (B : ℝ) {t : ℂ} (ht : t ∈ quadrant) :
    0 < (t^2-(B:ℂ)).im := by
  simp only [pow_two, Complex.sub_im, Complex.mul_im, Complex.ofReal_im, sub_zero]
  exact add_pos (mul_pos ht.1 ht.2) (mul_pos ht.2 ht.1)

private theorem sqrt_re_im_pos {z : ℂ} (hz : 0 < z.im) :
    0 < (Complex.sqrt z).re ∧ 0 < (Complex.sqrt z).im := by
  have hn : |z.re| < ‖z‖ := Complex.abs_re_lt_norm.mpr hz.ne'
  have hp : 0 < (‖z‖ + z.re) / 2 := by linarith [neg_abs_le z.re]
  have hm : 0 < (‖z‖ - z.re) / 2 := by linarith [le_abs_self z.re]
  simp only [Complex.sqrt, Complex.cpow_inv_two_re,
    Complex.cpow_inv_two_im_eq_sqrt hz.le]
  exact ⟨Real.sqrt_pos.2 hp, Real.sqrt_pos.2 hm⟩

private theorem sqrt_ne_zero_of_im_pos {z : ℂ} (hz : 0 < z.im) :
    Complex.sqrt z ≠ 0 := by
  intro heq
  have h := (sqrt_re_im_pos hz).1
  simpa [heq] using h

theorem differential_im_neg (B C : ℝ) {t : ℂ} (ht : t ∈ quadrant) :
    (differential B C t).im < 0 := by
  have hB := sqrt_re_im_pos (square_sub_im_pos B ht)
  have hC := sqrt_re_im_pos (square_sub_im_pos C ht)
  have hp : 0 < (Complex.sqrt (t^2-(B:ℂ)) *
      Complex.sqrt (t^2-(C:ℂ))).im := by
    simpa only [Complex.mul_im] using
      add_pos (mul_pos hB.1 hC.2) (mul_pos hB.2 hC.1)
  have hn : Complex.sqrt (t^2-(B:ℂ)) * Complex.sqrt (t^2-(C:ℂ)) ≠ 0 := by
    intro h
    simpa [h] using hp
  dsimp [differential]
  rw [Complex.div_im]
  change 0 * _ / _ - 2 * _ / _ < 0
  simp only [zero_mul, zero_div, zero_sub]
  exact neg_neg_of_pos (div_pos (mul_pos (by norm_num) hp)
    (Complex.normSq_pos.mpr hn))

theorem differential_differentiable (B C : ℝ) :
    DifferentiableOn ℂ (differential B C) quadrant := by
  intro t ht
  have hB := square_sub_im_pos B ht
  have hC := square_sub_im_pos C ht
  have hd (A : ℝ) (hA : 0 < (t^2-(A:ℂ)).im) :
      DifferentiableAt ℂ (fun z : ℂ => Complex.sqrt (z^2-(A:ℂ))) t :=
    (Complex.differentiableAt_sqrt (Or.inr hA.ne')).comp t
      ((differentiableAt_id.pow 2).sub_const (A:ℂ))
  exact ((differentiableAt_const (2:ℂ)).div ((hd B hB).mul (hd C hC))
    (mul_ne_zero (sqrt_ne_zero_of_im_pos hB)
      (sqrt_ne_zero_of_im_pos hC))).differentiableWithinAt

theorem exists_primitive (B C : ℝ) :
    ∃ G : ℂ → ℂ, ∀ t ∈ quadrant, HasDerivAt G (differential B C t) t := by
  obtain ⟨G,hG⟩ := quadrant_convex.exists_forall_hasDerivWithinAt
    (differential_differentiable B C)
  exact ⟨G, fun t ht => (hG t ht).hasDerivAt (quadrant_open.mem_nhds ht)⟩

theorem primitive_injective (B C : ℝ) {G : ℂ → ℂ}
    (hG : ∀ t ∈ quadrant, HasDerivAt G (differential B C t) t) :
    InjOn G quadrant := by
  intro z hz w hw heq
  by_contra hzw
  have hn : z-w ≠ 0 := sub_ne_zero.mpr hzw
  let segmentPoint (s : ℝ) : ℂ := w+(s:ℂ)*(z-w)
  have hseg (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) : segmentPoint s ∈ quadrant := by
    have h := quadrant_convex.lineMap_mem hw hz hs
    convert h using 1
    simp only [segmentPoint, AffineMap.lineMap_apply, Complex.real_smul,
      vsub_eq_sub, vadd_eq_add]
    ring
  let ψ (s : ℝ) : ℝ := -((G (segmentPoint s)-G w)/(z-w)).im
  have hψ (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) :
      HasDerivAt ψ (-(differential B C (segmentPoint s)).im) s := by
    have hd := ((hG (segmentPoint s) (hseg s hs)).comp (s:ℂ)
      (((hasDerivAt_id (s:ℂ)).mul_const (z-w)).const_add w)).sub_const (G w)
    have hq := hd.div_const (z-w)
    have hqc : HasDerivAt
        (fun x : ℂ => (G (w+x*(z-w))-G w)/(z-w))
        (differential B C (segmentPoint s)) (s:ℂ) := by
      simpa only [Function.comp_def, id_eq, one_mul, mul_div_cancel_right₀ _ hn] using! hq
    exact ((Complex.imCLM.hasFDerivAt.comp_hasDerivAt s hqc.comp_ofReal).neg)
  have hm : StrictMonoOn ψ (Icc (0:ℝ) 1) :=
    strictMonoOn_of_deriv_pos (convex_Icc 0 1)
      (fun s hs => (hψ s hs).continuousAt.continuousWithinAt)
      (fun s hs => by
        rw [(hψ s (interior_subset hs)).deriv]
        exact neg_pos.mpr (differential_im_neg B C (hseg s (interior_subset hs))))
  have hlt := hm (by norm_num : (0:ℝ) ∈ Icc (0:ℝ) 1)
    (by norm_num : (1:ℝ) ∈ Icc (0:ℝ) 1) (by norm_num)
  have he : w+(1:ℂ)*(z-w) = z := by ring
  simpa [ψ, segmentPoint, he, heq] using hlt

theorem exists_injective_primitive (B C : ℝ) :
    ∃ G : ℂ → ℂ, InjOn G quadrant ∧
      ∀ t ∈ quadrant, HasDerivAt G (differential B C t) t := by
  obtain ⟨G,hG⟩ := exists_primitive B C
  exact ⟨G,primitive_injective B C hG,hG⟩

end
end ParentWaveElliptic

import SlitPotentialLength
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.Convex

/-!
# Sharp local slope after reflection across the real line

A primitive holomorphic in the upper half-plane and continuous up to its
boundary has the expected local slope after even reflection.  The proof
first bounds derivatives on an upper half-ball, applies the convex mean
value theorem, extends the Lipschitz bound to the boundary by continuity,
and composes with the nonexpansive folding map.  No differentiability of
the reflected potential on the real axis is assumed.
-/

namespace SlitPotentialReflection

open Set Filter Metric Complex SlitPotentialLength
open scoped Topology NNReal ENNReal

noncomputable section

/-- Reflection of the lower half-plane into the upper half-plane. -/
def fold (z : ℂ) : ℂ := ⟨z.re, |z.im|⟩

@[simp] theorem fold_re (z : ℂ) : (fold z).re = z.re := rfl
@[simp] theorem fold_im (z : ℂ) : (fold z).im = |z.im| := rfl

theorem fold_im_nonneg (z : ℂ) : 0 ≤ (fold z).im := abs_nonneg _

theorem fold_eq_self {z : ℂ} (hz : 0 ≤ z.im) : fold z = z :=
  Complex.ext rfl (abs_of_nonneg hz)

theorem fold_lipschitz : LipschitzWith 1 fold := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro z w
  simp only [NNReal.coe_one, one_mul, dist_eq_norm]
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, fold_re, fold_im]
  have h := (sq_le_sq₀ (abs_nonneg (|z.im| - |w.im|))
    (abs_nonneg (z.im - w.im))).mpr (abs_abs_sub_abs_le_abs_sub z.im w.im)
  simp only [sq_abs] at h
  nlinarith

theorem fold_continuous : Continuous fold := fold_lipschitz.continuous

theorem norm_fold_sub_real (z : ℂ) (a : ℝ) :
    ‖fold z - (a : ℂ)‖ = ‖z - (a : ℂ)‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.ofReal_re, Complex.ofReal_im, fold_re, fold_im, sub_zero]
  nlinarith [sq_abs z.im]

private theorem upper_halfball_lipschitz {F F' : ℂ → ℂ}
    (hc : ContinuousOn F {z | 0 ≤ z.im})
    (hd : ∀ z : ℂ, 0 < z.im → HasDerivAt F (F' z) z)
    {x : ℂ} {r : ℝ} {K : ℝ≥0}
    (hK : ∀ z ∈ ball x r, ‖F' z‖₊ ≤ K) :
    LipschitzOnWith K F (ball x r ∩ {z : ℂ | 0 ≤ z.im}) := by
  let U := ball x r ∩ {z : ℂ | 0 < z.im}
  have hU : Convex ℝ U := (convex_ball x r).inter (convex_halfSpace_im_gt 0)
  have hLip : LipschitzOnWith K F U :=
    hU.lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun z hz => (hd z hz.2).hasDerivWithinAt) (fun z hz => hK z hz.1)
  have hcl : closure U ⊆ {z : ℂ | 0 ≤ z.im} := by
    rw [← Complex.closure_setOf_lt_im]
    exact closure_mono inter_subset_right
  have hsub : ball x r ∩ {z : ℂ | 0 ≤ z.im} ⊆ closure U := by
    rw [← Complex.closure_setOf_lt_im]
    exact isOpen_ball.inter_closure
  exact (LipschitzOnWith.closure (hc.mono hcl) hLip).mono hsub

/-- The real part of an upper-half-plane primitive, normalized by a
positive number and reflected evenly, has local slope bounded by the
normalized modulus of its complex derivative, including on the axis. -/
theorem localSlopeBound_fold_re {F F' : ℂ → ℂ} {S : Set ℂ}
    (hc : ContinuousOn F {z | 0 ≤ z.im})
    (hd : ∀ z : ℂ, 0 < z.im → HasDerivAt F (F' z) z)
    (hF' : ∀ x ∈ S, ContinuousAt F' (fold x))
    {B : ℝ} (hB : 0 < B) :
    LocalSlopeBound (fun z => (F (fold z)).re / B)
      (fun z => ‖F' (fold z)‖ / B) S := by
  intro x hx L hL
  have hLB : ‖F' (fold x)‖ < L * B := (div_lt_iff₀ hB).mp hL
  have hL0 : 0 ≤ L := le_of_lt ((div_nonneg (norm_nonneg _) hB.le).trans_lt hL)
  have hnear : ∀ᶠ z in 𝓝 (fold x), ‖F' z‖ < L * B :=
    (hF' x hx).norm.eventually (gt_mem_nhds hLB)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hnear
  have hLip := upper_halfball_lipschitz hc hd (x := fold x) (r := r)
    (K := Real.toNNReal (L * B)) (fun z hz =>
      (Real.le_toNNReal_iff_coe_le (mul_nonneg hL0 hB.le)).mpr (hball hz).le)
  refine ⟨ball x r, ball_mem_nhds x hr, ?_⟩
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro y hy z hz
  have hfy : fold y ∈ ball (fold x) r :=
    (fold_lipschitz.dist_le_mul y x).trans_lt (by simpa using hy)
  have hfz : fold z ∈ ball (fold x) r :=
    (fold_lipschitz.dist_le_mul z x).trans_lt (by simpa using hz)
  have hFdist := hLip.dist_le_mul (fold y) ⟨hfy, fold_im_nonneg y⟩
    (fold z) ⟨hfz, fold_im_nonneg z⟩
  rw [Real.coe_toNNReal _ (mul_nonneg hL0 hB.le)] at hFdist
  have hfold : dist (fold y) (fold z) ≤ dist y z := by
    simpa using fold_lipschitz.dist_le_mul y z
  have hre : |(F (fold y)).re - (F (fold z)).re| ≤
      dist (F (fold y)) (F (fold z)) := by
    simpa only [dist_eq_norm, Complex.sub_re] using
      Complex.abs_re_le_norm (F (fold y) - F (fold z))
  rw [Real.coe_toNNReal _ hL0, Real.dist_eq, ← sub_div, abs_div, abs_of_pos hB]
  apply (div_le_iff₀ hB).mpr
  calc
    |(F (fold y)).re - (F (fold z)).re| ≤
        (L * B) * dist (fold y) (fold z) := hre.trans hFdist
    _ ≤ (L * B) * dist y z := mul_le_mul_of_nonneg_left hfold (mul_nonneg hL0 hB.le)
    _ = (L * dist y z) * B := by ring

end
end SlitPotentialReflection

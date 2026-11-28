import ParentWavePhysicalChart

/-!
# Recognition of the physical electrodes by the elliptic boundary map

A point on either open vertical rectangle side has exactly the required
literal real preimage. These converses identify the endpoints of the
maximizing foliation with the original slit and its left terminal ray.
-/

namespace ParentWavePhysicalBoundary

open Set Complex
open ParentWaveElliptic ParentWaveEllipticSides ParentWaveEllipticImage
open ParentWaveEllipticClosed ParentWavePhysicalChart ParentWaveRectangle

noncomputable section

private theorem sqrt_sq (z : ℂ) : Complex.sqrt z ^ 2 = z :=
  Complex.cpow_nat_inv_pow z (by decide : (2 : ℕ) ≠ 0)

theorem quadrant_zero_side_preimage (B C : ℝ) (hB : 0 < B) (hBC : B < C)
    {G E : ℂ → ℂ} {L : ℂ}
    (hG : ∀ t ∈ quadrant, HasDerivAt G (differential B C t) t)
    (hE : ContinuousOn E (closure quadrant)) (hGE : EqOn G E quadrant)
    (hinfty : UniformLimitAtInfinity E (closure quadrant) L)
    {t : ℂ} (ht : t ∈ closure quadrant)
    (hre : (E t).re = (E (Real.sqrt B : ℂ)).re)
    (him : (E (Real.sqrt C : ℂ)).im < (E t).im ∧
      (E t).im < (E (Real.sqrt B : ℂ)).im) :
    t.im = 0 ∧ Real.sqrt B < t.re ∧ t.re < Real.sqrt C := by
  have hcl := ht
  rw [closure_quadrant] at hcl
  have hnot : t ∉ quadrant := by
    intro hq
    have h := mapsTo_rectangle B C hB hBC hG hE hGE hinfty hq
    exact (ne_of_lt h.1) hre.symm
  have htr : 0 < t.re := by
    by_contra htr
    have hr : t.re = 0 := le_antisymm (le_of_not_gt htr) hcl.1
    have he : t = (t.im:ℂ)*Complex.I := by
      simpa only [hr,Complex.ofReal_zero,zero_add] using (Complex.re_add_im t).symm
    have hside := (imaginary_side B C hB hBC hG hE hGE).2 t.im hcl.2 0 (by simp)
    simp only [Complex.ofReal_zero,zero_mul,← he] at hside
    have hw := (side_lengths_pos B C hB hBC hG hE hGE).1
    linarith
  have hti : t.im = 0 := by
    by_contra hti
    exact hnot ⟨htr,lt_of_le_of_ne hcl.2 (Ne.symm hti)⟩
  have he : t = (t.re:ℂ) := by
    simpa only [hti,Complex.ofReal_zero,zero_mul,add_zero] using (Complex.re_add_im t).symm
  refine ⟨hti,?_,?_⟩
  · by_contra hb
    have hle : t.re ≤ Real.sqrt B := le_of_not_gt hb
    have hi := (first_side B C hB hBC hG hE hGE).2 t.re ⟨hcl.1,hle⟩
      (Real.sqrt B) ⟨Real.sqrt_nonneg B,le_rfl⟩
    rw [← he] at hi
    linarith [him.2]
  · by_contra hc
    have hle : Real.sqrt C ≤ t.re := le_of_not_gt hc
    have hi := (last_side B C hB hBC hG hE hGE).2 t.re hle (Real.sqrt C) (by simp)
    rw [← he] at hi
    linarith [him.1]

theorem quadrant_width_side_preimage (B C : ℝ) (hB : 0 < B) (hBC : B < C)
    {G E : ℂ → ℂ} {L : ℂ}
    (hG : ∀ t ∈ quadrant, HasDerivAt G (differential B C t) t)
    (hE : ContinuousOn E (closure quadrant)) (hGE : EqOn G E quadrant)
    (hinfty : UniformLimitAtInfinity E (closure quadrant) L)
    {t : ℂ} (ht : t ∈ closure quadrant)
    (hre : (E t).re = (E 0).re)
    (him : (E (Real.sqrt C : ℂ)).im < (E t).im ∧
      (E t).im < (E (Real.sqrt B : ℂ)).im) :
    t.re = 0 ∧ 0 < t.im := by
  have hcl := ht
  rw [closure_quadrant] at hcl
  have hnot : t ∉ quadrant := by
    intro hq
    have h := mapsTo_rectangle B C hB hBC hG hE hGE hinfty hq
    exact (ne_of_lt h.2.1) hre
  have htr : t.re = 0 := by
    by_contra htr
    have hr : 0 < t.re := lt_of_le_of_ne hcl.1 (Ne.symm htr)
    have hi : t.im = 0 := by
      by_contra hi
      exact hnot ⟨hr,lt_of_le_of_ne hcl.2 (Ne.symm hi)⟩
    have he : t = (t.re:ℂ) := by
      simpa only [hi,Complex.ofReal_zero,zero_mul,add_zero] using (Complex.re_add_im t).symm
    have hb := real_boundary_re_upper B C hB hBC hG hE hGE hinfty hr
    rw [← he] at hb
    linarith
  refine ⟨htr,?_⟩
  by_contra hi
  have hi0 : t.im = 0 := le_antisymm (le_of_not_gt hi) hcl.2
  have ht0 : t = 0 := Complex.ext (by simpa using htr) (by simpa using hi0)
  have htop := (first_side B C hB hBC hG hE hGE).2 0
    ⟨le_rfl,Real.sqrt_nonneg B⟩ (Real.sqrt B) ⟨Real.sqrt_nonneg B,le_rfl⟩
  simp only [Complex.ofReal_zero] at htop
  rw [ht0,htop] at him
  exact (lt_irrefl _) him.2

theorem forward_zero_side_preimage (a b c : ℝ) (hab : a < b) (hbc : b < c)
    {E : ℂ → ℂ} {L : ℂ}
    (hE : ∀ t ∈ quadrant, HasDerivAt E (differential (b-a) (c-a) t) t)
    (hc : ContinuousOn E (closure quadrant))
    (hinfty : UniformLimitAtInfinity E (closure quadrant) L)
    {z : ℂ} (hz : z ∈ closedUpperHalfPlane)
    (hre : (forward a (b-a) E z).re = 0)
    (him : (forward a (b-a) E z).im ∈ Ioo (-height (b-a) (c-a) E) 0) :
    z.im = 0 ∧ b < z.re ∧ z.re < c := by
  let t := Complex.sqrt (z-(a:ℂ))
  have ht : t ∈ closure quadrant := sqrt_sub_mem_closed a hz
  have hr : (E t).re = (E (Real.sqrt (b-a) : ℂ)).re := by
    change (E t - E (Real.sqrt (b-a) : ℂ)).re = 0 at hre
    simpa only [Complex.sub_re,sub_eq_zero] using hre
  have hi : (E (Real.sqrt (c-a) : ℂ)).im < (E t).im ∧
      (E t).im < (E (Real.sqrt (b-a) : ℂ)).im := by
    change -( (E (Real.sqrt (b-a) : ℂ)).im - (E (Real.sqrt (c-a) : ℂ)).im) <
      (E t - E (Real.sqrt (b-a) : ℂ)).im ∧
      (E t - E (Real.sqrt (b-a) : ℂ)).im < 0 at him
    simp only [Complex.sub_im] at him
    constructor <;> linarith [him.1,him.2]
  obtain ⟨hti,htB,htC⟩ := quadrant_zero_side_preimage (b-a) (c-a)
    (by linarith) (by linarith) hE hc (fun _ _ => rfl) hinfty ht hr hi
  have hs : t^2 = z-(a:ℂ) := sqrt_sq _
  have hsi := congrArg Complex.im hs
  have hsr := congrArg Complex.re hs
  simp only [pow_two,Complex.mul_im,Complex.mul_re,hti,mul_zero,zero_mul,
    add_zero,sub_zero,Complex.sub_im,Complex.sub_re,Complex.ofReal_im,
    Complex.ofReal_re] at hsi hsr
  have htre : 0 ≤ t.re := by
    have h := ht
    rw [closure_quadrant] at h
    exact h.1
  have hsB := (sq_lt_sq₀ (Real.sqrt_nonneg (b-a)) htre).mpr htB
  have hsC := (sq_lt_sq₀ htre (Real.sqrt_nonneg (c-a))).mpr htC
  rw [Real.sq_sqrt (by linarith : 0 ≤ b-a)] at hsB
  rw [Real.sq_sqrt (by linarith : 0 ≤ c-a)] at hsC
  exact ⟨hsi.symm,by nlinarith only [hsB,hsC,hsr],
    by nlinarith only [hsB,hsC,hsr]⟩

theorem forward_width_side_preimage (a b c : ℝ) (hab : a < b) (hbc : b < c)
    {E : ℂ → ℂ} {L : ℂ}
    (hE : ∀ t ∈ quadrant, HasDerivAt E (differential (b-a) (c-a) t) t)
    (hc : ContinuousOn E (closure quadrant))
    (hinfty : UniformLimitAtInfinity E (closure quadrant) L)
    {z : ℂ} (hz : z ∈ closedUpperHalfPlane)
    (hre : (forward a (b-a) E z).re = width (b-a) E)
    (him : (forward a (b-a) E z).im ∈ Ioo (-height (b-a) (c-a) E) 0) :
    z.im = 0 ∧ z.re < a := by
  let t := Complex.sqrt (z-(a:ℂ))
  have ht : t ∈ closure quadrant := sqrt_sub_mem_closed a hz
  have hr : (E t).re = (E 0).re := by
    change (E t - E (Real.sqrt (b-a) : ℂ)).re =
      (E 0).re - (E (Real.sqrt (b-a) : ℂ)).re at hre
    simp only [Complex.sub_re] at hre
    linarith
  have hi : (E (Real.sqrt (c-a) : ℂ)).im < (E t).im ∧
      (E t).im < (E (Real.sqrt (b-a) : ℂ)).im := by
    change -((E (Real.sqrt (b-a) : ℂ)).im - (E (Real.sqrt (c-a) : ℂ)).im) <
      (E t - E (Real.sqrt (b-a) : ℂ)).im ∧
      (E t - E (Real.sqrt (b-a) : ℂ)).im < 0 at him
    simp only [Complex.sub_im] at him
    constructor <;> linarith [him.1,him.2]
  obtain ⟨htr,hti⟩ := quadrant_width_side_preimage (b-a) (c-a)
    (by linarith) (by linarith) hE hc (fun _ _ => rfl) hinfty ht hr hi
  have hs : t^2 = z-(a:ℂ) := sqrt_sq _
  have hsi := congrArg Complex.im hs
  have hsr := congrArg Complex.re hs
  simp only [pow_two,Complex.mul_im,Complex.mul_re,htr,mul_zero,zero_mul,
    add_zero,zero_sub,Complex.sub_im,Complex.sub_re,Complex.ofReal_im,
    Complex.ofReal_re,sub_zero] at hsi hsr
  exact ⟨hsi.symm,by nlinarith only [hsr,sq_pos_of_pos hti]⟩

end
end ParentWavePhysicalBoundary


import ParentWaveEllipticImage

/-!+# The finite closed rectangle chart

The continuous elliptic extension is injective on the whole finite closed
quadrant.  Its image contains every point of the closed rectangle except
the single corner belonging to infinity.
-/

namespace ParentWaveEllipticClosed

open Set Complex Filter
open scoped Topology
open ParentWaveElliptic ParentWaveEllipticSides ParentWaveEllipticImage ParentWaveRectangle

noncomputable section

theorem real_boundary_injective (B C : ℝ) (hB : 0 < B) (hBC : B < C)
    {G E : ℂ → ℂ}
    (hG : ∀ t ∈ quadrant, HasDerivAt G (differential B C t) t)
    (hE : ContinuousOn E (closure quadrant)) (hGE : EqOn G E quadrant) :
    InjOn (fun x : ℝ => E (x:ℂ)) (Ici 0) := by
  have hfirst := first_side B C hB hBC hG hE hGE
  have hmiddle := middle_side B C hB hBC hG hE hGE
  have hlast := last_side B C hB hBC hG hE hGE
  have hsBC := Real.sqrt_lt_sqrt hB.le hBC
  have hB0 := Real.sqrt_nonneg B
  have hC0 := Real.sqrt_nonneg C
  have htopbottom : (E (Real.sqrt C : ℂ)).im < (E (Real.sqrt B : ℂ)).im :=
    hmiddle.1 ⟨le_rfl,hsBC.le⟩ ⟨hsBC.le,le_rfl⟩ hsBC
  have hneq (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : x < y) : E (x:ℂ) ≠ E (y:ℂ) := by
    intro he
    have hre := congrArg Complex.re he
    have him := congrArg Complex.im he
    by_cases hyB : y ≤ Real.sqrt B
    · exact (ne_of_lt (hfirst.1 ⟨hx,le_trans hxy.le hyB⟩ ⟨hy,hyB⟩ hxy)) hre.symm
    by_cases hCx : Real.sqrt C ≤ x
    · exact (ne_of_lt (hlast.1 hCx (le_trans hCx hxy.le) hxy)) hre
    have hBy : Real.sqrt B < y := lt_of_not_ge hyB
    have hxC : x < Real.sqrt C := lt_of_not_ge hCx
    by_cases hxB : x ≤ Real.sqrt B
    · have hxTop := hfirst.2 x ⟨hx,hxB⟩ (Real.sqrt B) ⟨hB0,le_rfl⟩
      by_cases hyC : y ≤ Real.sqrt C
      · have hylt := hmiddle.1 ⟨le_rfl,hsBC.le⟩ ⟨hBy.le,hyC⟩ hBy
        linarith
      · have hyBottom := hlast.2 y (lt_of_not_ge hyC).le (Real.sqrt C) (by simp)
        linarith
    have hBx : Real.sqrt B < x := lt_of_not_ge hxB
    by_cases hyC : y ≤ Real.sqrt C
    · exact (ne_of_lt (hmiddle.1 ⟨hBx.le,hxC.le⟩ ⟨hBy.le,hyC⟩ hxy)) him.symm
    · have hxlt := hmiddle.1 ⟨hBx.le,hxC.le⟩ ⟨hsBC.le,le_rfl⟩ hxC
      have hyBottom := hlast.2 y (lt_of_not_ge hyC).le (Real.sqrt C) (by simp)
      linarith
  intro x hx y hy he
  rcases lt_trichotomy x y with h | h | h
  · exact False.elim (hneq x y hx hy h he)
  · exact h
  · exact False.elim (hneq y x hy hx h he.symm)

theorem real_boundary_re_upper (B C : ℝ) (hB : 0 < B) (hBC : B < C)
    {G E : ℂ → ℂ} {L : ℂ}
    (hG : ∀ t ∈ quadrant, HasDerivAt G (differential B C t) t)
    (hE : ContinuousOn E (closure quadrant)) (hGE : EqOn G E quadrant)
    (hinfty : UniformLimitAtInfinity E (closure quadrant) L)
    {x : ℝ} (hx : 0 < x) : (E (x:ℂ)).re < (E 0).re := by
  have hsBC := Real.sqrt_lt_sqrt hB.le hBC
  have hfirst := first_side B C hB hBC hG hE hGE
  have hmiddle := middle_side B C hB hBC hG hE hGE
  have hlast := last_side B C hB hBC hG hE hGE
  by_cases hxB : x ≤ Real.sqrt B
  · simpa only [Complex.ofReal_zero] using
      hfirst.1 ⟨le_rfl,Real.sqrt_nonneg B⟩ ⟨hx.le,hxB⟩ hx
  by_cases hxC : x ≤ Real.sqrt C
  · have hr := hmiddle.2 x ⟨(lt_of_not_ge hxB).le,hxC⟩
      (Real.sqrt B) ⟨le_rfl,hsBC.le⟩
    rw [hr]
    exact sub_pos.mp (side_lengths_pos B C hB hBC hG hE hGE).1
  have hCx : Real.sqrt C < x := lt_of_not_ge hxC
  have hlim := Complex.continuous_re.continuousAt.tendsto.comp (real_axis_tendsto hinfty)
  have hle : (E ((x+1:ℝ):ℂ)).re ≤ L.re := ge_of_tendsto hlim (by
    filter_upwards [eventually_ge_atTop (x+1)] with t ht
    exact hlast.1.monotoneOn (by linarith : Real.sqrt C ≤ x+1)
      (show Real.sqrt C ≤ t by linarith) ht)
  have hlt := hlast.1 hCx.le (by linarith : Real.sqrt C ≤ x+1) (by linarith : x < x+1)
  have hL := (infinity_corner B C hB hBC hG hE hGE hinfty).1
  exact hL ▸ lt_of_lt_of_le hlt hle

private theorem real_imaginary_meet (B C : ℝ) (hB : 0 < B) (hBC : B < C)
    {G E : ℂ → ℂ} {L : ℂ}
    (hG : ∀ t ∈ quadrant, HasDerivAt G (differential B C t) t)
    (hE : ContinuousOn E (closure quadrant)) (hGE : EqOn G E quadrant)
    (hinfty : UniformLimitAtInfinity E (closure quadrant) L)
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (he : E (x:ℂ) = E ((y:ℂ)*Complex.I)) : x = 0 ∧ y = 0 := by
  have hxy := imaginary_side B C hB hBC hG hE hGE
  have hx0 : x = 0 := by
    by_contra hx0
    have hr := real_boundary_re_upper B C hB hBC hG hE hGE hinfty
      (lt_of_le_of_ne hx (Ne.symm hx0))
    have hyR := hxy.2 y hy 0 (by simp)
    simp only [Complex.ofReal_zero,zero_mul] at hyR
    rw [he,hyR] at hr
    exact lt_irrefl _ hr
  refine ⟨hx0,?_⟩
  apply hxy.1.injOn hy (by simp)
  simpa only [hx0,Complex.ofReal_zero,zero_mul] using (congrArg Complex.im he).symm

/-- The actual primitive extension is one-to-one even at all finite
boundary points.  The missing infinite corner is the only excluded end. -/
theorem extension_injective_closed (B C : ℝ) (hB : 0 < B) (hBC : B < C)
    {G E : ℂ → ℂ} {L : ℂ}
    (hG : ∀ t ∈ quadrant, HasDerivAt G (differential B C t) t)
    (hE : ContinuousOn E (closure quadrant)) (hGE : EqOn G E quadrant)
    (hinfty : UniformLimitAtInfinity E (closure quadrant) L) :
    InjOn E (closure quadrant) := by
  intro z hz w hw he
  by_cases hzq : z ∈ quadrant
  · by_cases hwq : w ∈ quadrant
    · exact primitive_injective B C (extension_hasDerivAt B C hG hGE) hzq hwq he
    · exact False.elim ((finite_boundary_not_mem_rectangle B C hB hBC hG hE hGE w ⟨hw,hwq⟩)
        (he ▸ mapsTo_rectangle B C hB hBC hG hE hGE hinfty hzq))
  by_cases hwq : w ∈ quadrant
  · exact False.elim ((finite_boundary_not_mem_rectangle B C hB hBC hG hE hGE z ⟨hz,hzq⟩)
      (he.symm ▸ mapsTo_rectangle B C hB hBC hG hE hGE hinfty hwq))
  have hzcl := hz
  have hwcl := hw
  rw [closure_quadrant] at hzcl hwcl
  have axes (v : ℂ) (hv : v ∈ closure quadrant) (hn : v ∉ quadrant) :
      v.im = 0 ∨ v.re = 0 := by
    rw [closure_quadrant] at hv
    by_cases hi : v.im = 0
    · exact Or.inl hi
    · right
      by_contra hr
      exact hn ⟨lt_of_le_of_ne hv.1 (Ne.symm hr),lt_of_le_of_ne hv.2 (Ne.symm hi)⟩
  have real_eq (v : ℂ) (hv : v.im = 0) : v = (v.re:ℂ) := by
    simpa only [hv,Complex.ofReal_zero,zero_mul,add_zero] using (Complex.re_add_im v).symm
  have imag_eq (v : ℂ) (hv : v.re = 0) : v = (v.im:ℂ)*Complex.I := by
    simpa only [hv,Complex.ofReal_zero,zero_add] using (Complex.re_add_im v).symm
  rcases axes z hz hzq with hzi | hzr <;> rcases axes w hw hwq with hwi | hwr
  · have hz' := real_eq z hzi
    have hw' := real_eq w hwi
    have hcoord := real_boundary_injective B C hB hBC hG hE hGE hzcl.1 hwcl.1
      (by simpa only [← hz',← hw'] using he)
    exact Complex.ext hcoord (hzi.trans hwi.symm)
  · have hz' := real_eq z hzi
    have hw' := imag_eq w hwr
    have hcoord := real_imaginary_meet B C hB hBC hG hE hGE hinfty hzcl.1 hwcl.2
      (by simpa only [← hz',← hw'] using he)
    exact Complex.ext (hcoord.1.trans hwr.symm) (hzi.trans hcoord.2.symm)
  · have hz' := imag_eq z hzr
    have hw' := real_eq w hwi
    have hcoord := real_imaginary_meet B C hB hBC hG hE hGE hinfty hwcl.1 hzcl.2
      (by simpa only [← hz',← hw'] using he.symm)
    exact Complex.ext (hzr.trans hcoord.1.symm) (hcoord.2.trans hwi.symm)
  · have hz' := imag_eq z hzr
    have hw' := imag_eq w hwr
    have hcoord := (imaginary_side B C hB hBC hG hE hGE).1.injOn hzcl.2 hwcl.2
      (by simpa only [← hz',← hw'] using congrArg Complex.im he)
    exact Complex.ext (hzr.trans hwr.symm) hcoord

/-- Every finite point of the closed target rectangle except its
infinite corner has a finite preimage in the closed quadrant. -/
theorem closed_rectangle_covered (B C : ℝ) (hB : 0 < B) (hBC : B < C)
    {G E : ℂ → ℂ} {L : ℂ}
    (hG : ∀ t ∈ quadrant, HasDerivAt G (differential B C t) t)
    (hE : ContinuousOn E (closure quadrant)) (hGE : EqOn G E quadrant)
    (hinfty : UniformLimitAtInfinity E (closure quadrant) L) :
    closure (rectangle B C E) \ {L} ⊆ E '' closure quadrant := by
  intro y hy
  have hyim : y ∈ closure (E '' closure quadrant) := by
    apply closure_mono (image_mono (show quadrant ⊆ closure quadrant from subset_closure))
    rw [image_eq_rectangle B C hB hBC hG hE hGE hinfty]
    exact hy.1
  have hc : ContinuousOn E (closure (closure quadrant)) := by simpa only [closure_closure] using hE
  exact mem_image_of_mem_closure (V := {L}ᶜ) hc
    (fun z hz => by rw [closure_closure] at hz; exact False.elim (hz.2 hz.1))
    hinfty (by simp) hy.2 hyim

end
end ParentWaveEllipticClosed

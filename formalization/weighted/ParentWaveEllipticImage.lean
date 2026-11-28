import ParentWaveEllipticSides
import ParentWaveBoundaryInverse
import Mathlib.Analysis.Complex.OpenMapping

/-!+# The actual image of the elliptic quadrant primitive

The sign of the imaginary part of the literal derivative controls the two
interior coordinates.  Combined with the four boundary sides and the unique
value at infinity, it identifies the complete rectangle image.
-/

namespace ParentWaveEllipticImage

open Set Complex Filter
open scoped Topology
open ParentWaveElliptic ParentWaveEllipticSides ParentWaveRectangle

noncomputable section

def rectangle (B C : ℝ) (E : ℂ → ℂ) : Set ℂ :=
  {z | (E (Real.sqrt B : ℂ)).re < z.re ∧ z.re < (E 0).re ∧
    (E (Real.sqrt C : ℂ)).im < z.im ∧ z.im < (E (Real.sqrt B : ℂ)).im}

private theorem quadrant_open : IsOpen quadrant :=
  (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt continuous_const Complex.continuous_im)

private theorem quadrant_convex : Convex ℝ quadrant :=
  (convex_halfSpace_re_gt 0).inter (convex_halfSpace_im_gt 0)

theorem extension_hasDerivAt (B C : ℝ) {G E : ℂ → ℂ}
    (hG : ∀ t ∈ quadrant, HasDerivAt G (differential B C t) t)
    (hGE : EqOn G E quadrant) :
    ∀ t ∈ quadrant, HasDerivAt E (differential B C t) t := by
  intro t ht
  apply (hG t ht).congr_of_eventuallyEq
  filter_upwards [quadrant_open.mem_nhds ht] with z hz
  exact (hGE hz).symm

private theorem ray_tendsto {E : ℂ → ℂ} {L : ℂ}
    (hinfty : UniformLimitAtInfinity E (closure quadrant) L)
    (ψ : ℝ → ℂ) (a : ℝ)
    (hψ : ∀ s, a ≤ s → ψ s ∈ closure quadrant)
    (hn : ∀ s, a ≤ s → s ≤ ‖ψ s‖) :
    Tendsto (fun s => E (ψ s)) atTop (𝓝 L) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨R,hR⟩ := hinfty ε hε
  filter_upwards [eventually_ge_atTop a,eventually_gt_atTop R] with s hsa hsR
  exact hR (ψ s) (hψ s hsa) (lt_of_lt_of_le hsR (hn s hsa))

theorem real_axis_tendsto {E : ℂ → ℂ} {L : ℂ}
    (hinfty : UniformLimitAtInfinity E (closure quadrant) L) :
    Tendsto (fun s : ℝ => E (s:ℂ)) atTop (𝓝 L) :=
  ray_tendsto hinfty (fun s => (s:ℂ)) 0
    (fun s hs => by rw [closure_quadrant]; exact ⟨hs,by simp⟩)
    (fun s hs => by simp [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hs])

theorem imaginary_axis_tendsto {E : ℂ → ℂ} {L : ℂ}
    (hinfty : UniformLimitAtInfinity E (closure quadrant) L) :
    Tendsto (fun s : ℝ => E ((s:ℂ)*Complex.I)) atTop (𝓝 L) :=
  ray_tendsto hinfty (fun s => (s:ℂ)*Complex.I) 0
    (fun s hs => by rw [closure_quadrant]; simpa using hs)
    (fun s hs => by simp [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hs])

theorem infinity_corner (B C : ℝ) (hB : 0 < B) (hBC : B < C)
    {G E : ℂ → ℂ} {L : ℂ}
    (hG : ∀ t ∈ quadrant, HasDerivAt G (differential B C t) t)
    (hE : ContinuousOn E (closure quadrant)) (hGE : EqOn G E quadrant)
    (hinfty : UniformLimitAtInfinity E (closure quadrant) L) :
    L.re = (E 0).re ∧ L.im = (E (Real.sqrt C : ℂ)).im := by
  constructor
  · have hlim := Complex.continuous_re.continuousAt.tendsto.comp
      (imaginary_axis_tendsto hinfty)
    have hc : Tendsto (fun s : ℝ => (E ((s:ℂ)*Complex.I)).re) atTop (𝓝 (E 0).re) :=
      tendsto_const_nhds.congr' (by
        filter_upwards [eventually_ge_atTop (0:ℝ)] with s hs
        simpa only [Complex.ofReal_zero,zero_mul] using
          ((imaginary_side B C hB hBC hG hE hGE).2 s hs 0 (by simp)).symm)
    exact tendsto_nhds_unique hlim hc
  · have hlim := Complex.continuous_im.continuousAt.tendsto.comp (real_axis_tendsto hinfty)
    have hc : Tendsto (fun s : ℝ => (E (s:ℂ)).im) atTop
        (𝓝 (E (Real.sqrt C : ℂ)).im) :=
      tendsto_const_nhds.congr' (by
        filter_upwards [eventually_ge_atTop (Real.sqrt C)] with s hs
        exact ((last_side B C hB hBC hG hE hGE).2 s hs (Real.sqrt C) (by simp)).symm)
    exact tendsto_nhds_unique hlim hc

private theorem strictMonoOn_lt_limit {f : ℝ → ℝ} {a L : ℝ}
    (hm : StrictMonoOn f (Ici a)) (hlim : Tendsto f atTop (𝓝 L))
    {s : ℝ} (hs : a ≤ s) : f s < L := by
  have hle (t : ℝ) (ht : a ≤ t) : f t ≤ L :=
    ge_of_tendsto hlim (by
      filter_upwards [eventually_ge_atTop t] with u hu
      exact hm.monotoneOn ht (le_trans ht hu) hu)
  exact lt_of_lt_of_le (hm hs (by linarith : a ≤ s+1) (by linarith))
    (hle (s+1) (by linarith))

private theorem strictAntiOn_limit_lt {f : ℝ → ℝ} {a L : ℝ}
    (hm : StrictAntiOn f (Ici a)) (hlim : Tendsto f atTop (𝓝 L))
    {s : ℝ} (hs : a ≤ s) : L < f s := by
  have hle (t : ℝ) (ht : a ≤ t) : L ≤ f t :=
    le_of_tendsto hlim (by
      filter_upwards [eventually_ge_atTop t] with u hu
      exact hm.antitoneOn ht (le_trans ht hu) hu)
  exact lt_of_le_of_lt (hle (s+1) (by linarith))
    (hm hs (by linarith : a ≤ s+1) (by linarith))

theorem vertical_re_strictMono (B C : ℝ) {E : ℂ → ℂ}
    (hG : ∀ t ∈ quadrant, HasDerivAt E (differential B C t) t)
    (hE : ContinuousOn E (closure quadrant)) {x : ℝ} (hx : 0 < x) :
    StrictMonoOn (fun y : ℝ => (E ((x:ℂ)+(y:ℂ)*Complex.I)).re) (Ici 0) := by
  have hcont : ContinuousOn (fun y : ℝ => E ((x:ℂ)+(y:ℂ)*Complex.I)) (Ici 0) :=
    hE.comp (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).continuousOn
      (fun y hy => by rw [closure_quadrant]; simpa using And.intro hx.le hy)
  apply strictMonoOn_of_deriv_pos (convex_Ici _) (Complex.continuous_re.comp_continuousOn hcont)
  intro y hy
  rw [interior_Ici] at hy
  have hz : (x:ℂ)+(y:ℂ)*Complex.I ∈ quadrant := by simpa [quadrant] using And.intro hx hy
  have hφ : HasDerivAt (fun y : ℝ => (x:ℂ)+(y:ℂ)*Complex.I) Complex.I y := by
    simpa using! ((Complex.ofRealCLM.hasDerivAt (x := y)).mul_const Complex.I).const_add (x:ℂ)
  have hd := (hG _ hz).scomp y hφ
  have hr := Complex.reCLM.hasFDerivAt.comp_hasDerivAt y hd
  have h : HasDerivAt (fun y : ℝ => (E ((x:ℂ)+(y:ℂ)*Complex.I)).re)
      (-(differential B C ((x:ℂ)+(y:ℂ)*Complex.I)).im) y := by
    simpa only [Function.comp_def,smul_eq_mul,Complex.reCLM_apply,Complex.mul_re,
      Complex.I_re,Complex.I_im,zero_mul,one_mul,zero_sub] using! hr
  change 0 < deriv (fun y : ℝ => (E ((x:ℂ)+(y:ℂ)*Complex.I)).re) y
  rw [h.deriv]
  exact neg_pos.mpr (differential_im_neg B C hz)

theorem horizontal_im_strictAnti (B C : ℝ) {E : ℂ → ℂ}
    (hG : ∀ t ∈ quadrant, HasDerivAt E (differential B C t) t)
    (hE : ContinuousOn E (closure quadrant)) {y : ℝ} (hy : 0 < y) :
    StrictAntiOn (fun x : ℝ => (E ((x:ℂ)+(y:ℂ)*Complex.I)).im) (Ici 0) := by
  have hcont : ContinuousOn (fun x : ℝ => E ((x:ℂ)+(y:ℂ)*Complex.I)) (Ici 0) :=
    hE.comp (Complex.continuous_ofReal.add continuous_const).continuousOn
      (fun x hx => by rw [closure_quadrant]; simpa using And.intro hx hy.le)
  apply strictAntiOn_of_deriv_neg (convex_Ici _) (Complex.continuous_im.comp_continuousOn hcont)
  intro x hx
  rw [interior_Ici] at hx
  have hz : (x:ℂ)+(y:ℂ)*Complex.I ∈ quadrant := by simpa [quadrant] using And.intro hx hy
  have hφ : HasDerivAt (fun x : ℝ => (x:ℂ)+(y:ℂ)*Complex.I) 1 x := by
    simpa using! (Complex.ofRealCLM.hasDerivAt (x := x)).add_const ((y:ℂ)*Complex.I)
  have hd := (hG _ hz).scomp x hφ
  have hr := Complex.imCLM.hasFDerivAt.comp_hasDerivAt x hd
  have h : HasDerivAt (fun x : ℝ => (E ((x:ℂ)+(y:ℂ)*Complex.I)).im)
      (differential B C ((x:ℂ)+(y:ℂ)*Complex.I)).im x := by
    simpa only [Function.comp_def,one_smul,Complex.imCLM_apply] using! hr
  change deriv (fun x : ℝ => (E ((x:ℂ)+(y:ℂ)*Complex.I)).im) x < 0
  rw [h.deriv]
  exact differential_im_neg B C hz

theorem real_boundary_re_lower (B C : ℝ) (hB : 0 < B) (hBC : B < C)
    {G E : ℂ → ℂ}
    (hG : ∀ t ∈ quadrant, HasDerivAt G (differential B C t) t)
    (hE : ContinuousOn E (closure quadrant)) (hGE : EqOn G E quadrant)
    {x : ℝ} (hx : 0 ≤ x) :
    (E (Real.sqrt B : ℂ)).re ≤ (E (x:ℂ)).re := by
  have hsBC := Real.sqrt_lt_sqrt hB.le hBC
  by_cases hfirst : x ≤ Real.sqrt B
  · exact (first_side B C hB hBC hG hE hGE).1.antitoneOn
      ⟨hx,hfirst⟩ ⟨Real.sqrt_nonneg B,le_rfl⟩ hfirst
  have hBx : Real.sqrt B < x := lt_of_not_ge hfirst
  by_cases hmiddle : x ≤ Real.sqrt C
  · exact ((middle_side B C hB hBC hG hE hGE).2 x ⟨hBx.le,hmiddle⟩
      (Real.sqrt B) ⟨le_rfl,hsBC.le⟩).symm.le
  have hCx : Real.sqrt C ≤ x := (lt_of_not_ge hmiddle).le
  have hleft := (middle_side B C hB hBC hG hE hGE).2 (Real.sqrt C)
    ⟨hsBC.le,le_rfl⟩ (Real.sqrt B) ⟨le_rfl,hsBC.le⟩
  rw [← hleft]
  exact (last_side B C hB hBC hG hE hGE).1.monotoneOn (by simp) hCx hCx

theorem imaginary_boundary_im_upper (B C : ℝ) (hB : 0 < B) (hBC : B < C)
    {G E : ℂ → ℂ}
    (hG : ∀ t ∈ quadrant, HasDerivAt G (differential B C t) t)
    (hE : ContinuousOn E (closure quadrant)) (hGE : EqOn G E quadrant)
    {y : ℝ} (hy : 0 ≤ y) :
    (E ((y:ℂ)*Complex.I)).im ≤ (E (Real.sqrt B : ℂ)).im := by
  have htop := (first_side B C hB hBC hG hE hGE).2 0
    ⟨le_rfl,Real.sqrt_nonneg B⟩ (Real.sqrt B) ⟨Real.sqrt_nonneg B,le_rfl⟩
  have htop' : (E 0).im = (E (Real.sqrt B : ℂ)).im := by simpa using htop
  have h := (imaginary_side B C hB hBC hG hE hGE).1.antitoneOn
    (show (0:ℝ) ∈ Ici 0 by simp) hy hy
  simpa only [Complex.ofReal_zero,zero_mul,htop'] using h

/-- The strict interior rectangle bounds follow from coordinate
monotonicity of the actual primitive and its single limit at infinity. -/
theorem mapsTo_rectangle (B C : ℝ) (hB : 0 < B) (hBC : B < C)
    {G E : ℂ → ℂ} {L : ℂ}
    (hG : ∀ t ∈ quadrant, HasDerivAt G (differential B C t) t)
    (hE : ContinuousOn E (closure quadrant)) (hGE : EqOn G E quadrant)
    (hinfty : UniformLimitAtInfinity E (closure quadrant) L) :
    MapsTo E quadrant (rectangle B C E) := by
  have hEd := extension_hasDerivAt B C hG hGE
  have hL := infinity_corner B C hB hBC hG hE hGE hinfty
  intro z hz
  have hvert := vertical_re_strictMono B C hEd hE hz.1
  have hhor := horizontal_im_strictAnti B C hEd hE hz.2
  have hvl : Tendsto (fun s : ℝ => E ((z.re:ℂ)+(s:ℂ)*Complex.I)) atTop (𝓝 L) :=
    ray_tendsto hinfty (fun s => (z.re:ℂ)+(s:ℂ)*Complex.I) 0
      (fun s hs => by rw [closure_quadrant]; simpa using And.intro hz.1.le hs)
      (fun s _ => by simpa using Complex.im_le_norm ((z.re:ℂ)+(s:ℂ)*Complex.I))
  have hhl : Tendsto (fun s : ℝ => E ((s:ℂ)+(z.im:ℂ)*Complex.I)) atTop (𝓝 L) :=
    ray_tendsto hinfty (fun s => (s:ℂ)+(z.im:ℂ)*Complex.I) 0
      (fun s hs => by rw [closure_quadrant]; simpa using And.intro hs hz.2.le)
      (fun s _ => by simpa using Complex.re_le_norm ((s:ℂ)+(z.im:ℂ)*Complex.I))
  have hlow := hvert (show (0:ℝ) ∈ Ici 0 by simp) hz.2.le hz.2
  have hright := strictMonoOn_lt_limit hvert
    (Complex.continuous_re.continuousAt.tendsto.comp hvl) hz.2.le
  have hbottom := strictAntiOn_limit_lt hhor
    (Complex.continuous_im.continuousAt.tendsto.comp hhl) hz.1.le
  have hupp := hhor (show (0:ℝ) ∈ Ici 0 by simp) hz.1.le hz.1
  simp only [Complex.ofReal_zero,zero_mul,add_zero,zero_add,Complex.re_add_im] at hlow hright hbottom hupp
  change (E (Real.sqrt B : ℂ)).re < (E z).re ∧ (E z).re < (E 0).re ∧
    (E (Real.sqrt C : ℂ)).im < (E z).im ∧ (E z).im < (E (Real.sqrt B : ℂ)).im
  exact ⟨lt_of_le_of_lt (real_boundary_re_lower B C hB hBC hG hE hGE hz.1.le) hlow,
    hL.1 ▸ hright,hL.2 ▸ hbottom,
    lt_of_lt_of_le hupp (imaginary_boundary_im_upper B C hB hBC hG hE hGE hz.2.le)⟩

theorem finite_boundary_not_mem_rectangle (B C : ℝ) (hB : 0 < B) (hBC : B < C)
    {G E : ℂ → ℂ}
    (hG : ∀ t ∈ quadrant, HasDerivAt G (differential B C t) t)
    (hE : ContinuousOn E (closure quadrant)) (hGE : EqOn G E quadrant) :
    ∀ z ∈ closure quadrant \ quadrant, E z ∉ rectangle B C E := by
  intro z hz hrect
  have hcl := hz.1
  rw [closure_quadrant] at hcl
  change (E (Real.sqrt B : ℂ)).re < (E z).re ∧ (E z).re < (E 0).re ∧
    (E (Real.sqrt C : ℂ)).im < (E z).im ∧ (E z).im < (E (Real.sqrt B : ℂ)).im at hrect
  by_cases hx : z.re = 0
  · have he : z = (z.im:ℂ)*Complex.I := by
      simpa only [hx,Complex.ofReal_zero,zero_add] using (Complex.re_add_im z).symm
    have hr := (imaginary_side B C hB hBC hG hE hGE).2 z.im hcl.2 0 (by simp)
    simp only [Complex.ofReal_zero,zero_mul,← he] at hr
    exact (ne_of_lt hrect.2.1) hr
  have hy : z.im = 0 := by
    by_contra hy
    exact hz.2 ⟨lt_of_le_of_ne hcl.1 (Ne.symm hx),lt_of_le_of_ne hcl.2 (Ne.symm hy)⟩
  have he : z = (z.re:ℂ) := by
    simpa only [hy,Complex.ofReal_zero,zero_mul,add_zero] using (Complex.re_add_im z).symm
  have hsBC := Real.sqrt_lt_sqrt hB.le hBC
  by_cases hfirst : z.re ≤ Real.sqrt B
  · have hi := (first_side B C hB hBC hG hE hGE).2 z.re ⟨hcl.1,hfirst⟩
      (Real.sqrt B) ⟨Real.sqrt_nonneg B,le_rfl⟩
    rw [← he] at hi
    exact (ne_of_lt hrect.2.2.2) hi
  have hBx : Real.sqrt B ≤ z.re := (lt_of_not_ge hfirst).le
  by_cases hmiddle : z.re ≤ Real.sqrt C
  · have hr := (middle_side B C hB hBC hG hE hGE).2 z.re ⟨hBx,hmiddle⟩
      (Real.sqrt B) ⟨le_rfl,hsBC.le⟩
    rw [← he] at hr
    exact (ne_of_lt hrect.1) hr.symm
  have hi := (last_side B C hB hBC hG hE hGE).2 z.re
    (lt_of_not_ge hmiddle).le (Real.sqrt C) (by simp)
  rw [← he] at hi
  exact (ne_of_lt hrect.2.2.1) hi.symm

theorem primitive_open_image (B C : ℝ) {E : ℂ → ℂ}
    (hG : ∀ t ∈ quadrant, HasDerivAt E (differential B C t) t) :
    IsOpen (E '' quadrant) := by
  have ha : AnalyticOnNhd ℂ E quadrant :=
    (show DifferentiableOn ℂ E quadrant from
      fun z hz => (hG z hz).differentiableAt.differentiableWithinAt).analyticOnNhd quadrant_open
  rcases ha.is_constant_or_isOpen quadrant_convex.isPreconnected with ⟨w,hw⟩ | ho
  · have h1 : (1:ℂ)+Complex.I ∈ quadrant := by norm_num [quadrant]
    have h2 : (2:ℂ)+Complex.I ∈ quadrant := by norm_num [quadrant]
    have he := primitive_injective B C hG h1 h2 ((hw _ h1).trans (hw _ h2).symm)
    have hr := congrArg Complex.re he
    norm_num at hr
  · exact ho quadrant Subset.rfl quadrant_open

theorem rectangle_convex (B C : ℝ) (E : ℂ → ℂ) : Convex ℝ (rectangle B C E) :=
  (convex_halfSpace_re_gt _).inter ((convex_halfSpace_re_lt _).inter
    ((convex_halfSpace_im_gt _).inter (convex_halfSpace_im_lt _)))

/-- The literal primitive fills exactly the rectangle determined by
its three finite vertices; no boundary values are missing inside. -/
theorem image_eq_rectangle (B C : ℝ) (hB : 0 < B) (hBC : B < C)
    {G E : ℂ → ℂ} {L : ℂ}
    (hG : ∀ t ∈ quadrant, HasDerivAt G (differential B C t) t)
    (hE : ContinuousOn E (closure quadrant)) (hGE : EqOn G E quadrant)
    (hinfty : UniformLimitAtInfinity E (closure quadrant) L) :
    E '' quadrant = rectangle B C E := by
  have hL := infinity_corner B C hB hBC hG hE hGE hinfty
  apply image_eq_of_boundary_and_infinity
    ⟨(1:ℂ)+Complex.I,by norm_num [quadrant]⟩ (rectangle_convex B C E).isPreconnected
    (mapsTo_rectangle B C hB hBC hG hE hGE hinfty)
    (primitive_open_image B C (extension_hasDerivAt B C hG hGE)) hE
    (finite_boundary_not_mem_rectangle B C hB hBC hG hE hGE)
  · intro ε hε
    obtain ⟨R,hR⟩ := hinfty ε hε
    exact ⟨R,fun z hz => hR z (subset_closure hz)⟩
  · intro h
    exact (ne_of_lt h.2.1) hL.1

end
end ParentWaveEllipticImage

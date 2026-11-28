import ParentWaveEllipticClosed
import ParentWaveEllipticChart
import CrestConformalModulus

/-!
# The normalized physical upper-half-plane chart

This chart is the literal elliptic primitive composed with `sqrt(z-a)`.
Its normalization places the ending electrode on the left vertical side
and the exterior real ray on the right vertical side of the rectangle.
-/

namespace ParentWavePhysicalChart

open Set Complex Filter
open scoped Topology
open ParentWaveElliptic ParentWaveEllipticSides ParentWaveEllipticImage
open ParentWaveEllipticClosed ParentWaveRectangle

noncomputable section

def closedUpperHalfPlane : Set ℂ := {z | 0 ≤ z.im}

def openRectangle (I J : ℝ) : Set ℂ := {z | z.re ∈ Ioo 0 I ∧ z.im ∈ Ioo (-J) 0}

def width (B : ℝ) (E : ℂ → ℂ) : ℝ := (E 0).re - (E (Real.sqrt B : ℂ)).re

def height (B C : ℝ) (E : ℂ → ℂ) : ℝ :=
  (E (Real.sqrt B : ℂ)).im - (E (Real.sqrt C : ℂ)).im

def offset (B : ℝ) (E : ℂ → ℂ) : ℂ := E (Real.sqrt B : ℂ)

def forward (a B : ℝ) (E : ℂ → ℂ) (z : ℂ) : ℂ :=
  E (Complex.sqrt (z-(a:ℂ))) - offset B E

theorem dimensions_pos (B C : ℝ) (hB : 0 < B) (hBC : B < C)
    {E : ℂ → ℂ}
    (hE : ∀ t ∈ quadrant, HasDerivAt E (differential B C t) t)
    (hc : ContinuousOn E (closure quadrant)) :
    0 < width B E ∧ 0 < height B C E :=
  side_lengths_pos B C hB hBC hE hc (fun _ _ => rfl)

private theorem sqrt_sq (z : ℂ) : Complex.sqrt z ^ 2 = z :=
  Complex.cpow_nat_inv_pow z (by decide : (2:ℕ) ≠ 0)

theorem sqrt_mem_closed_quadrant {z : ℂ} (hz : 0 ≤ z.im) :
    Complex.sqrt z ∈ closure quadrant := by
  rw [closure_quadrant]
  change 0 ≤ (Complex.sqrt z).re ∧ 0 ≤ (Complex.sqrt z).im
  simp only [Complex.sqrt,Complex.cpow_inv_two_re,Complex.cpow_inv_two_im_eq_sqrt hz]
  exact ⟨Real.sqrt_nonneg _,Real.sqrt_nonneg _⟩

theorem sqrt_square_closed {t : ℂ} (ht : t ∈ closure quadrant) :
    Complex.sqrt (t^2) = t := by
  have htc := ht
  rw [closure_quadrant] at htc
  change 0 ≤ t.re ∧ 0 ≤ t.im at htc
  have hp : 0 ≤ (t^2).im := by
    simp only [pow_two,Complex.mul_im]
    exact add_nonneg (mul_nonneg htc.1 htc.2) (mul_nonneg htc.2 htc.1)
  have hs := sqrt_mem_closed_quadrant hp
  rw [closure_quadrant] at hs
  change 0 ≤ (Complex.sqrt (t^2)).re ∧ 0 ≤ (Complex.sqrt (t^2)).im at hs
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (sqrt_sq (t^2)) with he | he
  · exact he
  · have hr := congrArg Complex.re he
    have hi := congrArg Complex.im he
    simp only [Complex.neg_re,Complex.neg_im] at hr hi
    have ht0 : t = 0 := Complex.ext (by simp only [Complex.zero_re]; linarith [htc.1,hs.1])
      (by simp only [Complex.zero_im]; linarith [htc.2,hs.2])
    simp [ht0]

theorem square_translate_mem_closed (a : ℝ) {t : ℂ} (ht : t ∈ closure quadrant) :
    t^2+(a:ℂ) ∈ closedUpperHalfPlane := by
  rw [closure_quadrant] at ht
  change 0 ≤ (t^2+(a:ℂ)).im
  simp only [pow_two,Complex.add_im,Complex.ofReal_im,add_zero,Complex.mul_im]
  exact add_nonneg (mul_nonneg ht.1 ht.2) (mul_nonneg ht.2 ht.1)

theorem sqrt_sub_mem_closed (a : ℝ) {z : ℂ} (hz : z ∈ closedUpperHalfPlane) :
    Complex.sqrt (z-(a:ℂ)) ∈ closure quadrant := by
  apply sqrt_mem_closed_quadrant
  simpa only [Complex.sub_im,Complex.ofReal_im,sub_zero] using (show 0 ≤ z.im from hz)

theorem sqrt_sub_image_upper (a : ℝ) :
    (fun z : ℂ => Complex.sqrt (z-(a:ℂ))) '' upperHalfPlane = quadrant := by
  apply Subset.antisymm
  · rintro t ⟨z,hz,rfl⟩
    exact sqrt_sub_mem_quadrant a hz
  · intro t ht
    refine ⟨t^2+(a:ℂ),?_,?_⟩
    · change 0 < (t^2+(a:ℂ)).im
      simp only [pow_two,Complex.add_im,Complex.ofReal_im,add_zero,Complex.mul_im]
      exact add_pos (mul_pos ht.1 ht.2) (mul_pos ht.2 ht.1)
    · simpa only [add_sub_cancel_right] using sqrt_square_closed (subset_closure ht)

theorem forward_continuous_closed (a B : ℝ) {E : ℂ → ℂ}
    (hc : ContinuousOn E (closure quadrant)) :
    ContinuousOn (forward a B E) closedUpperHalfPlane := by
  have hs : ContinuousOn (fun z : ℂ => Complex.sqrt (z-(a:ℂ))) closedUpperHalfPlane :=
    continuousOn_sqrt_upper.comp (continuous_id.sub continuous_const).continuousOn
      (fun z hz => by
        change 0 ≤ (z-(a:ℂ)).im
        simpa only [Complex.sub_im,Complex.ofReal_im,sub_zero] using (show 0 ≤ z.im from hz))
  exact (hc.comp hs (fun z hz => sqrt_sub_mem_closed a hz)).sub continuousOn_const

theorem forward_hasDeriv (a b c : ℝ) {E : ℂ → ℂ}
    (hE : ∀ t ∈ quadrant, HasDerivAt E (differential (b-a) (c-a) t) t)
    {z : ℂ} (hz : z ∈ upperHalfPlane) :
    HasDerivAt (forward a (b-a) E) (upperDifferential a b c z) z :=
  (upperMap_hasDeriv a b c hE hz).sub_const (offset (b-a) E)

theorem forward_injective_closed (a b c : ℝ) (hab : a < b) (hbc : b < c)
    {E : ℂ → ℂ} {L : ℂ}
    (hE : ∀ t ∈ quadrant, HasDerivAt E (differential (b-a) (c-a) t) t)
    (hc : ContinuousOn E (closure quadrant))
    (hinfty : UniformLimitAtInfinity E (closure quadrant) L) :
    InjOn (forward a (b-a) E) closedUpperHalfPlane := by
  intro z hz w hw he
  have hi := extension_injective_closed (b-a) (c-a) (sub_pos.mpr hab)
    (sub_lt_sub_right hbc a) hE hc (fun _ _ => rfl) hinfty
  have hsq := hi (sqrt_sub_mem_closed a hz) (sqrt_sub_mem_closed a hw) (sub_left_inj.mp he)
  have hh := congrArg (fun t : ℂ => t^2) hsq
  simpa only [sqrt_sq,sub_left_inj] using hh

private theorem isOpenMap_restrict_of_hasDeriv
    {U : Set ℂ} (hU : IsOpen U) {f d : ℂ → ℂ}
    (hd : ∀ z ∈ U, HasDerivAt f (d z) z)
    (hn : ∀ z ∈ U, d z ≠ 0) : IsOpenMap (U.restrict f) := by
  have ha : AnalyticOnNhd ℂ f U :=
    (show DifferentiableOn ℂ f U from
      fun z hz => (hd z hz).differentiableAt.differentiableWithinAt).analyticOnNhd hU
  intro V hV
  have hVo : IsOpen ((Subtype.val : U → ℂ) '' V) := hU.isOpenMap_subtype_val V hV
  have him : IsOpen (f '' ((Subtype.val : U → ℂ) '' V)) := by
    apply isOpen_iff_mem_nhds.mpr
    rintro y ⟨x,⟨u,hu,rfl⟩,rfl⟩
    have hs := (ha u u.property).hasStrictDerivAt.congr_deriv (hd u u.property).deriv
    rw [← hs.map_nhds_eq (hn u u.property)]
    exact image_mem_map (hVo.mem_nhds ⟨u,hu,rfl⟩)
  simpa only [image_image,Set.restrict] using him

def conformalChart (a b c : ℝ) (E : ℂ → ℂ)
    (hE : ∀ t ∈ quadrant, HasDerivAt E (differential (b-a) (c-a) t) t) :
    CrestConformalModulus.ConformalChart := by
  let f := forward a (b-a) E
  have hi : InjOn f upperHalfPlane := by
    intro z hz w hw he
    exact upperMap_injective a b c hE hz hw (sub_left_inj.mp he)
  have hd : ∀ z ∈ upperHalfPlane, HasDerivAt f (upperDifferential a b c z) z :=
    fun z hz => forward_hasDeriv a b c hE hz
  have hc : ContinuousOn (upperDifferential a b c) upperHalfPlane := by
    have hdiff : DifferentiableOn ℂ f upperHalfPlane :=
      fun z hz => (hd z hz).differentiableAt.differentiableWithinAt
    apply (hdiff.deriv upperHalfPlane_open).continuousOn.congr
    exact fun z hz => (hd z hz).deriv.symm
  exact {
    homeomorph := OpenPartialHomeomorph.ofContinuousOpenRestrict
      (hi.toPartialEquiv f upperHalfPlane)
      (fun z hz => (hd z hz).continuousAt.continuousWithinAt)
      (isOpenMap_restrict_of_hasDeriv upperHalfPlane_open hd
        (fun z hz => upperDifferential_nonzero a b c hz)) upperHalfPlane_open
    derivative := upperDifferential a b c
    hasDeriv := hd
    derivative_continuous := hc
    derivative_ne_zero := fun z hz => upperDifferential_nonzero a b c hz }

@[simp] theorem conformalChart_source (a b c : ℝ) (E : ℂ → ℂ)
    (hE : ∀ t ∈ quadrant, HasDerivAt E (differential (b-a) (c-a) t) t) :
    (conformalChart a b c E hE).homeomorph.source = upperHalfPlane := rfl

@[simp] theorem conformalChart_apply (a b c : ℝ) (E : ℂ → ℂ)
    (hE : ∀ t ∈ quadrant, HasDerivAt E (differential (b-a) (c-a) t) t) (z : ℂ) :
    (conformalChart a b c E hE).homeomorph z = forward a (b-a) E z := rfl

@[simp] theorem conformalChart_derivative (a b c : ℝ) (E : ℂ → ℂ)
    (hE : ∀ t ∈ quadrant, HasDerivAt E (differential (b-a) (c-a) t) t) :
    (conformalChart a b c E hE).derivative = upperDifferential a b c := rfl

theorem normalized_mem_rectangle_iff (B C : ℝ) (E : ℂ → ℂ) (z : ℂ) :
    z-offset B E ∈ openRectangle (width B E) (height B C E) ↔
      z ∈ ParentWaveEllipticImage.rectangle B C E := by
  change (0 < z.re-(E (Real.sqrt B : ℂ)).re ∧
      z.re-(E (Real.sqrt B : ℂ)).re < (E 0).re-(E (Real.sqrt B : ℂ)).re) ∧
      (-((E (Real.sqrt B : ℂ)).im-(E (Real.sqrt C : ℂ)).im) <
        z.im-(E (Real.sqrt B : ℂ)).im ∧ z.im-(E (Real.sqrt B : ℂ)).im < 0) ↔ _
  change _ ↔ (E (Real.sqrt B : ℂ)).re < z.re ∧ z.re < (E 0).re ∧
    (E (Real.sqrt C : ℂ)).im < z.im ∧ z.im < (E (Real.sqrt B : ℂ)).im
  constructor
  · rintro ⟨⟨h1,h2⟩,h3,h4⟩
    exact ⟨by linarith,by linarith,by linarith,by linarith⟩
  · rintro ⟨h1,h2,h3,h4⟩
    exact ⟨⟨by linarith,by linarith⟩,by linarith,by linarith⟩

theorem forward_image_upper (a b c : ℝ) (hab : a < b) (hbc : b < c)
    {E : ℂ → ℂ} {L : ℂ}
    (hE : ∀ t ∈ quadrant, HasDerivAt E (differential (b-a) (c-a) t) t)
    (hc : ContinuousOn E (closure quadrant))
    (hinfty : UniformLimitAtInfinity E (closure quadrant) L) :
    forward a (b-a) E '' upperHalfPlane = openRectangle (width (b-a) E) (height (b-a) (c-a) E) := by
  have hraw := image_eq_rectangle (b-a) (c-a) (sub_pos.mpr hab)
    (sub_lt_sub_right hbc a) hE hc (fun _ _ => rfl) hinfty
  apply Subset.antisymm
  · rintro y ⟨z,hz,rfl⟩
    apply (normalized_mem_rectangle_iff (b-a) (c-a) E _).mpr
    rw [← hraw]
    exact ⟨Complex.sqrt (z-(a:ℂ)),sqrt_sub_mem_quadrant a hz,rfl⟩
  · intro y hy
    have hyraw : y+offset (b-a) E ∈ ParentWaveEllipticImage.rectangle (b-a) (c-a) E := by
      apply (normalized_mem_rectangle_iff (b-a) (c-a) E _).mp
      simpa only [add_sub_cancel_right] using hy
    rw [← hraw] at hyraw
    obtain ⟨t,ht,hEt⟩ := hyraw
    rw [← sqrt_sub_image_upper a] at ht
    obtain ⟨z,hz,ht⟩ := ht
    refine ⟨z,hz,?_⟩
    change E (Complex.sqrt (z-(a:ℂ))) - offset (b-a) E = y
    change Complex.sqrt (z-(a:ℂ)) = t at ht
    rw [ht,hEt,add_sub_cancel_right]

theorem conformalChart_target (a b c : ℝ) (hab : a < b) (hbc : b < c)
    {E : ℂ → ℂ} {L : ℂ}
    (hE : ∀ t ∈ quadrant, HasDerivAt E (differential (b-a) (c-a) t) t)
    (hc : ContinuousOn E (closure quadrant))
    (hinfty : UniformLimitAtInfinity E (closure quadrant) L) :
    (conformalChart a b c E hE).homeomorph.target =
      openRectangle (width (b-a) E) (height (b-a) (c-a) E) :=
  forward_image_upper a b c hab hbc hE hc hinfty

private theorem sqrt_real_nonneg {x : ℝ} (hx : 0 ≤ x) :
    Complex.sqrt (x:ℂ) = (Real.sqrt x : ℂ) := by
  simpa only [Complex.ofReal_re] using Complex.sqrt_of_nonneg (Complex.zero_le_real.mpr hx)

private theorem sqrt_real_nonpos {x : ℝ} (hx : x ≤ 0) :
    Complex.sqrt (x:ℂ) = (Real.sqrt (-x) : ℂ)*Complex.I := by
  have he : (x:ℂ) = -((-x:ℝ):ℂ) := by simp
  rw [he,Complex.sqrt_neg_of_nonneg (Complex.zero_le_real.mpr (neg_nonneg.mpr hx)),
    sqrt_real_nonneg (neg_nonneg.mpr hx),mul_comm]

theorem forward_ending_atom (a b c : ℝ) (hab : a < b) (hbc : b < c)
    {E : ℂ → ℂ}
    (hE : ∀ t ∈ quadrant, HasDerivAt E (differential (b-a) (c-a) t) t)
    (hc : ContinuousOn E (closure quadrant))
    {x : ℝ} (hx : x ∈ Ioo b c) :
    (forward a (b-a) E (x:ℂ)).re = 0 ∧
      (forward a (b-a) E (x:ℂ)).im ∈ Ioo (-height (b-a) (c-a) E) 0 := by
  have hB := sub_pos.mpr hab
  have hC := sub_pos.mpr (lt_trans hab hbc)
  have hxa : 0 < x-a := sub_pos.mpr (lt_trans hab hx.1)
  have hsB := Real.sqrt_lt_sqrt hB.le (sub_lt_sub_right hx.1 a)
  have hsC := Real.sqrt_lt_sqrt hxa.le (sub_lt_sub_right hx.2 a)
  have hsBC := Real.sqrt_lt_sqrt hB.le (sub_lt_sub_right hbc a)
  have hm := middle_side (b-a) (c-a) hB (sub_lt_sub_right hbc a) hE hc (fun _ _ => rfl)
  have hre := hm.2 (Real.sqrt (x-a)) ⟨hsB.le,hsC.le⟩ (Real.sqrt (b-a)) ⟨le_rfl,hsBC.le⟩
  have him0 := hm.1 ⟨le_rfl,hsBC.le⟩ ⟨hsB.le,hsC.le⟩ hsB
  have him1 := hm.1 ⟨hsB.le,hsC.le⟩ ⟨hsBC.le,le_rfl⟩ hsC
  simp only [forward,← Complex.ofReal_sub,sqrt_real_nonneg hxa.le,
    Complex.sub_re,Complex.sub_im,offset,height]
  exact ⟨sub_eq_zero.mpr hre,by constructor <;> linarith⟩

theorem imaginary_boundary_im_lower (B C : ℝ) (hB : 0 < B) (hBC : B < C)
    {E : ℂ → ℂ} {L : ℂ}
    (hE : ∀ t ∈ quadrant, HasDerivAt E (differential B C t) t)
    (hc : ContinuousOn E (closure quadrant))
    (hinfty : UniformLimitAtInfinity E (closure quadrant) L)
    {s : ℝ} (hs : 0 ≤ s) :
    (E (Real.sqrt C : ℂ)).im < (E ((s:ℂ)*Complex.I)).im := by
  have hm := (imaginary_side B C hB hBC hE hc (fun _ _ => rfl)).1
  have hlim := Complex.continuous_im.continuousAt.tendsto.comp (imaginary_axis_tendsto hinfty)
  have hle : L.im ≤ (E (((s+1:ℝ):ℂ)*Complex.I)).im := le_of_tendsto hlim (by
    filter_upwards [eventually_ge_atTop (s+1)] with t ht
    exact hm.antitoneOn (show 0 ≤ s+1 by linarith) (show 0 ≤ t by linarith) ht)
  have hlt := hm hs (show 0 ≤ s+1 by linarith) (show s < s+1 by linarith)
  have hL := (infinity_corner B C hB hBC hE hc (fun _ _ => rfl) hinfty).2
  exact hL ▸ lt_of_le_of_lt hle hlt

theorem forward_left_ray (a b c : ℝ) (hab : a < b) (hbc : b < c)
    {E : ℂ → ℂ} {L : ℂ}
    (hE : ∀ t ∈ quadrant, HasDerivAt E (differential (b-a) (c-a) t) t)
    (hc : ContinuousOn E (closure quadrant))
    (hinfty : UniformLimitAtInfinity E (closure quadrant) L)
    {x : ℝ} (hx : x < a) :
    (forward a (b-a) E (x:ℂ)).re = width (b-a) E ∧
      (forward a (b-a) E (x:ℂ)).im ∈ Ioo (-height (b-a) (c-a) E) 0 := by
  have hB := sub_pos.mpr hab
  have hBC := sub_lt_sub_right hbc a
  have hs : 0 < Real.sqrt (a-x) := Real.sqrt_pos.mpr (sub_pos.mpr hx)
  have hm := imaginary_side (b-a) (c-a) hB hBC hE hc (fun _ _ => rfl)
  have hre := hm.2 (Real.sqrt (a-x)) hs.le 0 (by simp)
  have him0 := hm.1 (show (0:ℝ) ∈ Ici 0 by simp) hs.le hs
  have him1 := imaginary_boundary_im_lower (b-a) (c-a) hB hBC hE hc hinfty hs.le
  have htop := (first_side (b-a) (c-a) hB hBC hE hc (fun _ _ => rfl)).2 0
    ⟨le_rfl,Real.sqrt_nonneg _⟩ (Real.sqrt (b-a)) ⟨Real.sqrt_nonneg _,le_rfl⟩
  simp only [Complex.ofReal_zero,zero_mul] at hre him0 htop
  have hroot : Complex.sqrt ((x:ℂ)-(a:ℂ)) = (Real.sqrt (a-x):ℂ)*Complex.I := by
    simpa only [← Complex.ofReal_sub,neg_sub] using sqrt_real_nonpos (sub_nonpos.mpr hx.le)
  simp only [forward,hroot,Complex.sub_re,Complex.sub_im,offset,width,height]
  exact ⟨by rw [hre],by constructor <;> linarith⟩

end
end ParentWavePhysicalChart

import ParentWaveEllipticBoundary
import ParentWaveEllipticInfinity
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Topology.Order.DenselyOrdered

/-!+# Boundary sides of the canonical elliptic rectangle

The continuous extension of the actual primitive has derivatives along the
open real and imaginary boundary sides.  These derivatives are the literal
boundary values of the original elliptic differential.
-/

namespace ParentWaveEllipticSides

open Set Complex Filter
open scoped Topology
open ParentWaveElliptic

noncomputable section

private theorem quadrant_open : IsOpen quadrant :=
  (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt continuous_const Complex.continuous_im)

theorem closure_quadrant : closure quadrant = {z : ℂ | 0 ≤ z.re ∧ 0 ≤ z.im} := by
  have hq : quadrant = Complex.equivRealProdCLM.toHomeomorph ⁻¹'
      ((Ioi (0:ℝ)) ×ˢ (Ioi (0:ℝ))) := rfl
  rw [hq, ← Complex.equivRealProdCLM.toHomeomorph.isOpenMap.preimage_closure_eq_closure_preimage
    Complex.equivRealProdCLM.continuous, closure_prod_eq, closure_Ioi]
  rfl

private theorem sqrt_sq (z : ℂ) : Complex.sqrt z ^ 2 = z :=
  Complex.cpow_nat_inv_pow z (by decide : (2:ℕ) ≠ 0)

private theorem sqrt_ne {z : ℂ} (hz : z ≠ 0) : Complex.sqrt z ≠ 0 := by
  intro h
  exact hz (by simpa [h] using (sqrt_sq z).symm)

theorem continuousOn_sqrt_upper :
    ContinuousOn Complex.sqrt {z : ℂ | 0 ≤ z.im} := by
  let f (z : ℂ) : ℂ := (Real.sqrt ((‖z‖+z.re)/2) : ℂ) +
    (Real.sqrt ((‖z‖-z.re)/2) : ℂ) * Complex.I
  have hf : Continuous f := by dsimp [f]; fun_prop
  apply hf.continuousOn.congr
  intro z hz
  have hz' : 0 ≤ z.im := hz
  simpa only [f,if_pos hz',one_mul] using (Complex.sqrt_eq_real_add_ite (a := z))

theorem differential_continuousWithinAt_closed (B C : ℝ) {x : ℂ}
    (hx : x ∈ closure quadrant)
    (hxB : x ^ 2 ≠ (B:ℂ)) (hxC : x ^ 2 ≠ (C:ℂ)) :
    ContinuousWithinAt (differential B C) (closure quadrant) x := by
  have hp (A : ℝ) : MapsTo (fun t : ℂ => t^2-(A:ℂ)) (closure quadrant)
      {z : ℂ | 0 ≤ z.im} := by
    intro t ht
    rw [closure_quadrant] at ht
    simp only [mem_setOf_eq,pow_two,Complex.sub_im,Complex.ofReal_im,sub_zero,Complex.mul_im]
    exact add_nonneg (mul_nonneg ht.1 ht.2) (mul_nonneg ht.2 ht.1)
  have hs (A : ℝ) : ContinuousWithinAt (fun t : ℂ => Complex.sqrt (t^2-(A:ℂ)))
      (closure quadrant) x :=
    ContinuousWithinAt.comp (f := fun t : ℂ => t^2-(A:ℂ))
      (continuousOn_sqrt_upper (x^2-(A:ℂ)) (hp A hx))
      ((continuous_id.pow 2).sub continuous_const).continuousWithinAt (hp A)
  exact continuousWithinAt_const.div ((hs B).mul (hs C))
    (mul_ne_zero (sqrt_ne (sub_ne_zero.mpr hxB)) (sqrt_ne (sub_ne_zero.mpr hxC)))

private theorem local_extensions_eq {U T : Set ℂ} (hTo : IsOpen T)
    {G E H : ℂ → ℂ} (hE : ContinuousOn E (closure U))
    (hGE : EqOn G E U) (hH : ContinuousOn H T) (hGH : EqOn G H (U ∩ T)) :
    EqOn E H (closure U ∩ T) := by
  intro z hz
  haveI : NeBot (𝓝[U] z) := mem_closure_iff_nhdsWithin_neBot.mp hz.1
  have he : Tendsto G (𝓝[U] z) (𝓝 (E z)) :=
    ((hE z hz.1).mono subset_closure).congr' (by
      filter_upwards [self_mem_nhdsWithin] with t ht
      exact (hGE ht).symm)
  have hh : Tendsto G (𝓝[U] z) (𝓝 (H z)) :=
    (((hH z hz.2).continuousAt (hTo.mem_nhds hz.2)).tendsto.mono_left nhdsWithin_le_nhds).congr' (by
      filter_upwards [self_mem_nhdsWithin,nhdsWithin_le_nhds (hTo.mem_nhds hz.2)] with t ht htT
      exact (hGH ⟨ht,htT⟩).symm)
  exact tendsto_nhds_unique he hh

private theorem local_extension_deriv (B C : ℝ) {G H : ℂ → ℂ}
    (hG : ∀ t ∈ quadrant, HasDerivAt G (differential B C t) t)
    {x : ℂ} {ε : ℝ} (hε : 0 < ε)
    (hH : DifferentiableOn ℂ H (Metric.ball x ε))
    (hGH : EqOn G H (quadrant ∩ Metric.ball x ε))
    (hx : x ∈ closure quadrant)
    (hxB : x ^ 2 ≠ (B:ℂ)) (hxC : x ^ 2 ≠ (C:ℂ)) :
    HasDerivAt H (differential B C x) x := by
  have he (z : ℂ) (hz : z ∈ quadrant ∩ Metric.ball x ε) :
      deriv H z = differential B C z := by
    have hEq : H =ᶠ[𝓝 z] G := by
      filter_upwards [(quadrant_open.inter Metric.isOpen_ball).mem_nhds hz] with t ht
      exact (hGH ht).symm
    exact ((hG z hz.1).congr_of_eventuallyEq hEq).deriv
  haveI : NeBot (𝓝[quadrant] x) := mem_closure_iff_nhdsWithin_neBot.mp hx
  have hdc : ContinuousAt (deriv H) x :=
    (((hH.deriv Metric.isOpen_ball) x (Metric.mem_ball_self hε)).differentiableAt
      (Metric.ball_mem_nhds x hε)).continuousAt
  have hlim : Tendsto (deriv H) (𝓝[quadrant] x) (𝓝 (differential B C x)) :=
    ((differential_continuousWithinAt_closed B C hx hxB hxC).mono subset_closure).congr' (by
      filter_upwards [self_mem_nhdsWithin,
        nhdsWithin_le_nhds (Metric.ball_mem_nhds x hε)] with t ht htε
      exact (he t ⟨ht,htε⟩).symm)
  have hderiv : deriv H x = differential B C x :=
    tendsto_nhds_unique (hdc.tendsto.mono_left nhdsWithin_le_nhds) hlim
  exact ((hH x (Metric.mem_ball_self hε)).differentiableAt
    (Metric.ball_mem_nhds x hε)).hasDerivAt.congr_deriv hderiv

/-- A smooth trace in the closed quadrant inherits the actual elliptic
derivative, including at a regular boundary point. -/
theorem boundary_trace_hasDerivAt (B C : ℝ) {G E : ℂ → ℂ}
    (hG : ∀ t ∈ quadrant, HasDerivAt G (differential B C t) t)
    (hE : ContinuousOn E (closure quadrant)) (hGE : EqOn G E quadrant)
    {φ : ℝ → ℂ} {v : ℂ} {s : ℝ} (hφ : HasDerivAt φ v s)
    (hφq : ∀ᶠ t in 𝓝 s, φ t ∈ closure quadrant)
    (hx : φ s ∈ closure quadrant)
    (hxB : (φ s) ^ 2 ≠ (B:ℂ)) (hxC : (φ s) ^ 2 ≠ (C:ℂ)) :
    HasDerivAt (fun t => E (φ t)) (differential B C (φ s) * v) s := by
  obtain ⟨ε,hε,H,hH,hGH⟩ :=
    ParentWaveEllipticBoundary.exists_regular_extension B C hxB hxC hG
  have he : EqOn E H (closure quadrant ∩ Metric.ball (φ s) ε) :=
    local_extensions_eq Metric.isOpen_ball hE hGE hH.continuousOn hGH
  have hd : HasDerivAt H (differential B C (φ s)) (φ s) :=
    local_extension_deriv B C hG hε hH hGH hx hxB hxC
  have hEq : (fun t => E (φ t)) =ᶠ[𝓝 s] (fun t => H (φ t)) := by
    filter_upwards [hφq,hφ.continuousAt (Metric.ball_mem_nhds (φ s) hε)] with t ht htb
    exact he ⟨ht,htb⟩
  simpa only [Function.comp_def,smul_eq_mul,mul_comm] using
    (hd.scomp s hφ).congr_of_eventuallyEq hEq

theorem real_trace_hasDerivAt (B C : ℝ) {G E : ℂ → ℂ}
    (hG : ∀ t ∈ quadrant, HasDerivAt G (differential B C t) t)
    (hE : ContinuousOn E (closure quadrant)) (hGE : EqOn G E quadrant)
    {s : ℝ} (hs : 0 < s) (hsB : s ^ 2 ≠ B) (hsC : s ^ 2 ≠ C) :
    HasDerivAt (fun t : ℝ => E (t:ℂ)) (differential B C (s:ℂ)) s := by
  have hx : (s:ℂ) ∈ closure quadrant := by
    rw [closure_quadrant]
    exact ⟨hs.le,by simp⟩
  have hφq : ∀ᶠ (t : ℝ) in 𝓝 s, (t:ℂ) ∈ closure quadrant := by
    filter_upwards [Ioi_mem_nhds hs] with t ht
    rw [closure_quadrant]
    exact ⟨ht.le,by simp⟩
  have hφ : HasDerivAt (fun t : ℝ => (t:ℂ)) 1 s := by
    simpa using! Complex.ofRealCLM.hasDerivAt (x := s)
  simpa only [mul_one] using boundary_trace_hasDerivAt B C hG hE hGE
    hφ hφq hx
    (by simpa only [← Complex.ofReal_pow,ne_eq,Complex.ofReal_inj] using hsB)
    (by simpa only [← Complex.ofReal_pow,ne_eq,Complex.ofReal_inj] using hsC)

theorem imaginary_trace_hasDerivAt (B C : ℝ) (hB : 0 < B) (hC : 0 < C)
    {G E : ℂ → ℂ}
    (hG : ∀ t ∈ quadrant, HasDerivAt G (differential B C t) t)
    (hE : ContinuousOn E (closure quadrant)) (hGE : EqOn G E quadrant)
    {s : ℝ} (hs : 0 < s) :
    HasDerivAt (fun t : ℝ => E ((t:ℂ)*Complex.I))
      (differential B C ((s:ℂ)*Complex.I) * Complex.I) s := by
  have hx : (s:ℂ)*Complex.I ∈ closure quadrant := by
    rw [closure_quadrant]
    simpa using hs.le
  have hφq : ∀ᶠ (t : ℝ) in 𝓝 s, (t:ℂ)*Complex.I ∈ closure quadrant := by
    filter_upwards [Ioi_mem_nhds hs] with t ht
    rw [closure_quadrant]
    simpa using ht.le
  have hn (A : ℝ) (hA : 0 < A) : ((s:ℂ)*Complex.I)^2 ≠ (A:ℂ) := by
    intro he
    have hre := congrArg Complex.re he
    simp [mul_pow,← Complex.ofReal_pow] at hre
    nlinarith [sq_nonneg s]
  have hφ : HasDerivAt (fun t : ℝ => (t:ℂ)) 1 s := by
    simpa using! Complex.ofRealCLM.hasDerivAt (x := s)
  simpa only [one_mul] using boundary_trace_hasDerivAt B C hG hE hGE
    (hφ.mul_const Complex.I) hφq hx (hn B hB) (hn C hC)

private theorem sqrt_real_nonneg {a : ℝ} (ha : 0 ≤ a) :
    Complex.sqrt (a:ℂ) = (Real.sqrt a : ℂ) := by
  simpa only [Complex.ofReal_re] using
    Complex.sqrt_of_nonneg (Complex.zero_le_real.mpr ha)

private theorem sqrt_real_nonpos {a : ℝ} (ha : a ≤ 0) :
    Complex.sqrt (a:ℂ) = Complex.I * (Real.sqrt (-a) : ℂ) := by
  have hneg : (a:ℂ) = -((-a:ℝ):ℂ) := by simp
  rw [hneg,Complex.sqrt_neg_of_nonneg (Complex.zero_le_real.mpr (neg_nonneg.mpr ha)),
    sqrt_real_nonneg (neg_nonneg.mpr ha)]

theorem differential_real_first (B C s : ℝ) (hsB : s^2 < B) (hsC : s^2 < C) :
    differential B C (s:ℂ) =
      -((2 / (Real.sqrt (B-s^2) * Real.sqrt (C-s^2)) : ℝ) : ℂ) := by
  have h1 := sqrt_real_nonpos (sub_nonpos.mpr hsB.le)
  have h2 := sqrt_real_nonpos (sub_nonpos.mpr hsC.le)
  simp only [neg_sub] at h1 h2
  have hden (a b : ℝ) : (Complex.I*(a:ℂ))*(Complex.I*(b:ℂ)) = -((a*b:ℝ):ℂ) := by
    push_cast
    calc
      _ = Complex.I^2*((a:ℂ)*(b:ℂ)) := by ring
      _ = _ := by simp
  simp only [differential,← Complex.ofReal_pow,← Complex.ofReal_sub,h1,h2,hden]
  simp [div_neg]

theorem differential_real_middle (B C s : ℝ) (hBs : B < s^2) (hsC : s^2 < C) :
    differential B C (s:ℂ) =
      -((2 / (Real.sqrt (s^2-B) * Real.sqrt (C-s^2)) : ℝ) : ℂ) * Complex.I := by
  have h1 := sqrt_real_nonneg (sub_nonneg.mpr hBs.le)
  have h2 := sqrt_real_nonpos (sub_nonpos.mpr hsC.le)
  simp only [neg_sub] at h2
  have hden (a b : ℝ) : (a:ℂ)*(Complex.I*(b:ℂ)) = ((a*b:ℝ):ℂ)*Complex.I := by
    push_cast
    ring
  simp only [differential,← Complex.ofReal_pow,← Complex.ofReal_sub,h1,h2,hden]
  simp [← div_div,Complex.div_I]

theorem differential_real_last (B C s : ℝ) (hBs : B < s^2) (hCs : C < s^2) :
    differential B C (s:ℂ) =
      ((2 / (Real.sqrt (s^2-B) * Real.sqrt (s^2-C)) : ℝ) : ℂ) := by
  simp only [differential,← Complex.ofReal_pow,← Complex.ofReal_sub,
    sqrt_real_nonneg (sub_nonneg.mpr hBs.le),sqrt_real_nonneg (sub_nonneg.mpr hCs.le),
    ← Complex.ofReal_mul]
  simp

theorem differential_imaginary (B C s : ℝ) (hB : 0 < B) (hC : 0 < C) :
    differential B C ((s:ℂ)*Complex.I) =
      -((2 / (Real.sqrt (s^2+B) * Real.sqrt (s^2+C)) : ℝ) : ℂ) := by
  have hsA (A : ℝ) : ((s:ℂ)*Complex.I)^2-(A:ℂ) = ((-s^2-A:ℝ):ℂ) := by
    simp [mul_pow,← Complex.ofReal_pow]
  have h1 := sqrt_real_nonpos (show -s^2-B ≤ 0 by nlinarith [sq_nonneg s])
  have h2 := sqrt_real_nonpos (show -s^2-C ≤ 0 by nlinarith [sq_nonneg s])
  simp only [neg_sub,sub_neg_eq_add] at h1 h2
  have hden (a b : ℝ) : (Complex.I*(a:ℂ))*(Complex.I*(b:ℂ)) = -((a*b:ℝ):ℂ) := by
    push_cast
    calc
      _ = Complex.I^2*((a:ℂ)*(b:ℂ)) := by ring
      _ = _ := by simp
  simp only [differential,hsA,h1,h2,hden]
  simp [add_comm,div_neg]

private theorem constant_on_of_derivative_zero {D : Set ℝ} {f : ℝ → ℝ}
    (hD : Convex ℝ D) (hf : ContinuousOn f D)
    (hd : ∀ s ∈ interior D, HasDerivAt f 0 s) :
    ∀ x ∈ D, ∀ y ∈ D, f x = f y := by
  have hm : MonotoneOn f D := monotoneOn_of_hasDerivWithinAt_nonneg hD hf
    (fun s hs => (hd s hs).hasDerivWithinAt) (by intros; exact le_rfl)
  have ha : AntitoneOn f D := antitoneOn_of_hasDerivWithinAt_nonpos hD hf
    (fun s hs => (hd s hs).hasDerivWithinAt) (by intros; exact le_rfl)
  intro x hx y hy
  rcases le_total x y with h | h
  · exact le_antisymm (hm hx hy h) (ha hx hy h)
  · exact le_antisymm (ha hy hx h) (hm hy hx h)

private theorem horizontal_negative {D : Set ℝ} {f : ℝ → ℂ} {v : ℝ → ℝ}
    (hD : Convex ℝ D) (hf : ContinuousOn f D)
    (hd : ∀ s ∈ interior D, HasDerivAt f (-(v s : ℂ)) s)
    (hv : ∀ s ∈ interior D, 0 < v s) :
    StrictAntiOn (fun s => (f s).re) D ∧
      ∀ x ∈ D, ∀ y ∈ D, (f x).im = (f y).im := by
  constructor
  · apply strictAntiOn_of_deriv_neg hD (Complex.continuous_re.comp_continuousOn hf)
    intro s hs
    have h := Complex.reCLM.hasFDerivAt.comp_hasDerivAt s (hd s hs)
    have hh : HasDerivAt (fun s => (f s).re) (-v s) s := by simpa using! h
    change deriv (fun s => (f s).re) s < 0
    rw [hh.deriv]
    exact neg_neg_of_pos (hv s hs)
  · apply constant_on_of_derivative_zero hD (Complex.continuous_im.comp_continuousOn hf)
    intro s hs
    simpa using! Complex.imCLM.hasFDerivAt.comp_hasDerivAt s (hd s hs)

private theorem horizontal_positive {D : Set ℝ} {f : ℝ → ℂ} {v : ℝ → ℝ}
    (hD : Convex ℝ D) (hf : ContinuousOn f D)
    (hd : ∀ s ∈ interior D, HasDerivAt f ((v s : ℂ)) s)
    (hv : ∀ s ∈ interior D, 0 < v s) :
    StrictMonoOn (fun s => (f s).re) D ∧
      ∀ x ∈ D, ∀ y ∈ D, (f x).im = (f y).im := by
  constructor
  · apply strictMonoOn_of_deriv_pos hD (Complex.continuous_re.comp_continuousOn hf)
    intro s hs
    have h := Complex.reCLM.hasFDerivAt.comp_hasDerivAt s (hd s hs)
    have hh : HasDerivAt (fun s => (f s).re) (v s) s := by simpa using! h
    change 0 < deriv (fun s => (f s).re) s
    rw [hh.deriv]
    exact hv s hs
  · apply constant_on_of_derivative_zero hD (Complex.continuous_im.comp_continuousOn hf)
    intro s hs
    simpa using! Complex.imCLM.hasFDerivAt.comp_hasDerivAt s (hd s hs)

private theorem vertical_negative {D : Set ℝ} {f : ℝ → ℂ} {v : ℝ → ℝ}
    (hD : Convex ℝ D) (hf : ContinuousOn f D)
    (hd : ∀ s ∈ interior D, HasDerivAt f (-(v s : ℂ)*Complex.I) s)
    (hv : ∀ s ∈ interior D, 0 < v s) :
    StrictAntiOn (fun s => (f s).im) D ∧
      ∀ x ∈ D, ∀ y ∈ D, (f x).re = (f y).re := by
  constructor
  · apply strictAntiOn_of_deriv_neg hD (Complex.continuous_im.comp_continuousOn hf)
    intro s hs
    have h := Complex.imCLM.hasFDerivAt.comp_hasDerivAt s (hd s hs)
    have hh : HasDerivAt (fun s => (f s).im) (-v s) s := by simpa using! h
    change deriv (fun s => (f s).im) s < 0
    rw [hh.deriv]
    exact neg_neg_of_pos (hv s hs)
  · apply constant_on_of_derivative_zero hD (Complex.continuous_re.comp_continuousOn hf)
    intro s hs
    simpa using! Complex.reCLM.hasFDerivAt.comp_hasDerivAt s (hd s hs)

private theorem real_trace_continuousOn {E : ℂ → ℂ}
    (hE : ContinuousOn E (closure quadrant)) :
    ContinuousOn (fun s : ℝ => E (s:ℂ)) (Ici 0) :=
  hE.comp Complex.continuous_ofReal.continuousOn (fun s hs => by
    rw [closure_quadrant]
    exact ⟨hs,by simp⟩)

private theorem imaginary_trace_continuousOn {E : ℂ → ℂ}
    (hE : ContinuousOn E (closure quadrant)) :
    ContinuousOn (fun s : ℝ => E ((s:ℂ)*Complex.I)) (Ici 0) :=
  hE.comp (Complex.continuous_ofReal.mul continuous_const).continuousOn (fun s hs => by
    rw [closure_quadrant]
    simpa using hs)

theorem first_side (B C : ℝ) (hB : 0 < B) (hBC : B < C)
    {G E : ℂ → ℂ}
    (hG : ∀ t ∈ quadrant, HasDerivAt G (differential B C t) t)
    (hE : ContinuousOn E (closure quadrant)) (hGE : EqOn G E quadrant) :
    StrictAntiOn (fun s : ℝ => (E (s:ℂ)).re) (Icc 0 (Real.sqrt B)) ∧
      ∀ x ∈ Icc 0 (Real.sqrt B), ∀ y ∈ Icc 0 (Real.sqrt B),
        (E (x:ℂ)).im = (E (y:ℂ)).im := by
  have hs (s : ℝ) (hs : s ∈ interior (Icc 0 (Real.sqrt B))) :
      0 < s ∧ s^2 < B ∧ s^2 < C := by
    rw [interior_Icc] at hs
    have hsq := Real.sq_sqrt hB.le
    have hb : s ^ 2 < B := by
      rw [← hsq]
      exact (sq_lt_sq₀ hs.1.le (Real.sqrt_nonneg B)).mpr hs.2
    exact ⟨hs.1,hb,lt_trans hb hBC⟩
  apply horizontal_negative (v := fun s => 2/(Real.sqrt (B-s^2)*Real.sqrt (C-s^2)))
    (convex_Icc _ _) ((real_trace_continuousOn hE).mono (fun _ h => h.1))
  · intro s hsi
    rcases hs s hsi with ⟨hs0,hsB,hsC⟩
    simpa only [differential_real_first B C s hsB hsC] using
      real_trace_hasDerivAt B C hG hE hGE hs0 hsB.ne hsC.ne
  · intro s hsi
    rcases hs s hsi with ⟨hs0,hsB,hsC⟩
    exact div_pos (by norm_num)
      (mul_pos (Real.sqrt_pos.mpr (sub_pos.mpr hsB))
        (Real.sqrt_pos.mpr (sub_pos.mpr hsC)))

theorem middle_side (B C : ℝ) (hB : 0 < B) (hBC : B < C)
    {G E : ℂ → ℂ}
    (hG : ∀ t ∈ quadrant, HasDerivAt G (differential B C t) t)
    (hE : ContinuousOn E (closure quadrant)) (hGE : EqOn G E quadrant) :
    StrictAntiOn (fun s : ℝ => (E (s:ℂ)).im) (Icc (Real.sqrt B) (Real.sqrt C)) ∧
      ∀ x ∈ Icc (Real.sqrt B) (Real.sqrt C), ∀ y ∈ Icc (Real.sqrt B) (Real.sqrt C),
        (E (x:ℂ)).re = (E (y:ℂ)).re := by
  have hC := lt_trans hB hBC
  have hs (s : ℝ) (hs : s ∈ interior (Icc (Real.sqrt B) (Real.sqrt C))) :
      0 < s ∧ B < s^2 ∧ s^2 < C := by
    rw [interior_Icc] at hs
    have hsB := Real.sqrt_pos.mpr hB
    have hsC := Real.sqrt_pos.mpr hC
    have hsqB := Real.sq_sqrt hB.le
    have hsqC := Real.sq_sqrt hC.le
    have hs0 := lt_trans hsB hs.1
    have hb : B < s ^ 2 := by
      rw [← hsqB]
      exact (sq_lt_sq₀ (Real.sqrt_nonneg B) hs0.le).mpr hs.1
    have hc : s ^ 2 < C := by
      rw [← hsqC]
      exact (sq_lt_sq₀ hs0.le (Real.sqrt_nonneg C)).mpr hs.2
    exact ⟨hs0,hb,hc⟩
  apply vertical_negative (v := fun s => 2/(Real.sqrt (s^2-B)*Real.sqrt (C-s^2)))
    (convex_Icc _ _) ((real_trace_continuousOn hE).mono
      (fun _ h => le_trans (Real.sqrt_nonneg B) h.1))
  · intro s hsi
    rcases hs s hsi with ⟨hs0,hBs,hsC⟩
    simpa only [differential_real_middle B C s hBs hsC] using
      real_trace_hasDerivAt B C hG hE hGE hs0 hBs.ne' hsC.ne
  · intro s hsi
    rcases hs s hsi with ⟨hs0,hBs,hsC⟩
    exact div_pos (by norm_num)
      (mul_pos (Real.sqrt_pos.mpr (sub_pos.mpr hBs))
        (Real.sqrt_pos.mpr (sub_pos.mpr hsC)))

theorem last_side (B C : ℝ) (hB : 0 < B) (hBC : B < C)
    {G E : ℂ → ℂ}
    (hG : ∀ t ∈ quadrant, HasDerivAt G (differential B C t) t)
    (hE : ContinuousOn E (closure quadrant)) (hGE : EqOn G E quadrant) :
    StrictMonoOn (fun s : ℝ => (E (s:ℂ)).re) (Ici (Real.sqrt C)) ∧
      ∀ x ∈ Ici (Real.sqrt C), ∀ y ∈ Ici (Real.sqrt C),
        (E (x:ℂ)).im = (E (y:ℂ)).im := by
  have hC := lt_trans hB hBC
  have hs (s : ℝ) (hs : s ∈ interior (Ici (Real.sqrt C))) :
      0 < s ∧ B < s^2 ∧ C < s^2 := by
    rw [interior_Ici] at hs
    have hs0 := lt_trans (Real.sqrt_pos.mpr hC) hs
    have hc : C < s ^ 2 := by
      rw [← Real.sq_sqrt hC.le]
      exact (sq_lt_sq₀ (Real.sqrt_nonneg C) hs0.le).mpr hs
    exact ⟨hs0,lt_trans hBC hc,hc⟩
  apply horizontal_positive (v := fun s => 2/(Real.sqrt (s^2-B)*Real.sqrt (s^2-C)))
    (convex_Ici _) ((real_trace_continuousOn hE).mono
      (fun _ h => le_trans (Real.sqrt_nonneg C) h))
  · intro s hsi
    rcases hs s hsi with ⟨hs0,hBs,hCs⟩
    simpa only [differential_real_last B C s hBs hCs] using
      real_trace_hasDerivAt B C hG hE hGE hs0 hBs.ne' hCs.ne'
  · intro s hsi
    rcases hs s hsi with ⟨hs0,hBs,hCs⟩
    exact div_pos (by norm_num)
      (mul_pos (Real.sqrt_pos.mpr (sub_pos.mpr hBs))
        (Real.sqrt_pos.mpr (sub_pos.mpr hCs)))

theorem imaginary_side (B C : ℝ) (hB : 0 < B) (hBC : B < C)
    {G E : ℂ → ℂ}
    (hG : ∀ t ∈ quadrant, HasDerivAt G (differential B C t) t)
    (hE : ContinuousOn E (closure quadrant)) (hGE : EqOn G E quadrant) :
    StrictAntiOn (fun s : ℝ => (E ((s:ℂ)*Complex.I)).im) (Ici 0) ∧
      ∀ x ∈ Ici (0:ℝ), ∀ y ∈ Ici (0:ℝ),
        (E ((x:ℂ)*Complex.I)).re = (E ((y:ℂ)*Complex.I)).re := by
  have hC := lt_trans hB hBC
  apply vertical_negative (v := fun s => 2/(Real.sqrt (s^2+B)*Real.sqrt (s^2+C)))
    (convex_Ici _) (imaginary_trace_continuousOn hE)
  · intro s hsi
    rw [interior_Ici] at hsi
    simpa only [differential_imaginary B C s hB hC] using
      imaginary_trace_hasDerivAt B C hB hC hG hE hGE hsi
  · intro s _
    exact div_pos (by norm_num)
      (mul_pos (Real.sqrt_pos.mpr (by nlinarith [sq_nonneg s]))
        (Real.sqrt_pos.mpr (by nlinarith [sq_nonneg s])))

theorem side_lengths_pos (B C : ℝ) (hB : 0 < B) (hBC : B < C)
    {G E : ℂ → ℂ}
    (hG : ∀ t ∈ quadrant, HasDerivAt G (differential B C t) t)
    (hE : ContinuousOn E (closure quadrant)) (hGE : EqOn G E quadrant) :
    0 < (E 0).re - (E (Real.sqrt B : ℂ)).re ∧
      0 < (E (Real.sqrt B : ℂ)).im - (E (Real.sqrt C : ℂ)).im := by
  have hsB := Real.sqrt_pos.mpr hB
  have hsBC := Real.sqrt_lt_sqrt hB.le hBC
  constructor
  · have h := (first_side B C hB hBC hG hE hGE).1
      (show (0:ℝ) ∈ Icc 0 (Real.sqrt B) from ⟨le_rfl,hsB.le⟩)
      (show Real.sqrt B ∈ Icc 0 (Real.sqrt B) from ⟨hsB.le,le_rfl⟩) hsB
    simpa only [Complex.ofReal_zero,sub_pos] using h
  · exact sub_pos.mpr ((middle_side B C hB hBC hG hE hGE).1
      ⟨le_rfl,hsBC.le⟩ ⟨hsBC.le,le_rfl⟩ hsBC)

end
end ParentWaveEllipticSides

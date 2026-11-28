import ParentWaveElliptic
import Mathlib.Topology.Algebra.Field
import Mathlib.Topology.ExtendFrom

/-!+# Finite boundary regularization of the canonical elliptic primitive

The square-root coordinates at the finite vertices remove the singularities
of the concrete differential.  Matching squared derivatives on a connected
sector is enough to select a single sign and obtain an analytic extension.
-/

namespace ParentWaveEllipticBoundary

open Set Complex
open scoped Topology

noncomputable section

/-- A holomorphic square root of the squared derivative gives a genuine
extension, with its sign fixed on the entire connected overlap. -/
theorem exists_extension_of_derivative_sq
    {S T : Set ℂ} (hSo : IsOpen S) (hSc : IsPreconnected S)
    (hTo : IsOpen T) (hTc : Convex ℝ T) (hST : S ⊆ T)
    {f d h : ℂ → ℂ}
    (hf : ∀ z ∈ S, HasDerivAt f (d z) z)
    (hd : ContinuousOn d S) (hh : DifferentiableOn ℂ h T)
    (hne : ∀ z ∈ S, h z ≠ 0)
    (hsq : ∀ z ∈ S, d z ^ 2 = h z ^ 2) :
    ∃ E : ℂ → ℂ, DifferentiableOn ℂ E T ∧ EqOn f E S := by
  obtain ⟨H,hH⟩ := hTc.exists_forall_hasDerivWithinAt hh
  have hHa : ∀ z ∈ T, HasDerivAt H (h z) z :=
    fun z hz => (hH z hz).hasDerivAt (hTo.mem_nhds hz)
  have hf' : DifferentiableOn ℂ f S :=
    fun z hz => (hf z hz).differentiableAt.differentiableWithinAt
  have hH' : DifferentiableOn ℂ H T :=
    fun z hz => (hHa z hz).differentiableAt.differentiableWithinAt
  rcases hSc.eq_or_eq_neg_of_sq_eq hd (hh.continuousOn.mono hST)
      (fun z hz => hsq z hz) (fun hz => hne _ hz) with he | he
  · obtain ⟨c,hc⟩ := hSo.exists_eq_add_of_deriv_eq hSc hf' (hH'.mono hST)
      (fun z hz => by rw [(hf z hz).deriv, (hHa z (hST hz)).deriv]; exact he hz)
    exact ⟨fun z => H z+c,hH'.add_const c,hc⟩
  · have hneg : ∀ z ∈ T, HasDerivAt (fun z => -H z) (-h z) z :=
      fun z hz => (hHa z hz).neg
    obtain ⟨c,hc⟩ := hSo.exists_eq_add_of_deriv_eq hSc hf' (hH'.neg.mono hST)
      (fun z hz => by
        change deriv f z = deriv (fun z => -H z) z
        rw [(hf z hz).deriv, (hneg z (hST hz)).deriv]
        exact he hz)
    exact ⟨fun z => -H z+c,hH'.neg.add_const c,hc⟩

private theorem sqrt_sq (z : ℂ) : Complex.sqrt z ^ 2 = z :=
  Complex.cpow_nat_inv_pow z (by decide : (2 : ℕ) ≠ 0)

/-- Normalize the value of a nonzero holomorphic function before taking
the principal square root, so the branch cut stays outside a small ball. -/
theorem exists_local_square_root {T : Set ℂ} (hTo : IsOpen T)
    {R : ℂ → ℂ} (hR : DifferentiableOn ℂ R T)
    {x : ℂ} (hx : x ∈ T) (hn : R x ≠ 0) :
    ∃ ε > 0, Metric.ball x ε ⊆ T ∧ ∃ h : ℂ → ℂ,
      DifferentiableOn ℂ h (Metric.ball x ε) ∧
      (∀ z ∈ Metric.ball x ε, h z ≠ 0) ∧
      ∀ z ∈ Metric.ball x ε, h z ^ 2 = R z := by
  have hRx : DifferentiableAt ℂ R x :=
    (hR x hx).differentiableAt (hTo.mem_nhds hx)
  have hc : ContinuousAt (fun z => (R z / R x).re) x :=
    Complex.continuous_re.continuousAt.comp (hRx.continuousAt.div_const (R x))
  have hp : 0 < (R x / R x).re := by simp [hn]
  have hev : ∀ᶠ z in 𝓝 x, z ∈ T ∧ 0 < (R z / R x).re :=
    Filter.Eventually.and (hTo.mem_nhds hx) (hc (Ioi_mem_nhds hp))
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp hev
  let h (z : ℂ) := Complex.sqrt (R x) * Complex.sqrt (R z / R x)
  have hsquare (z : ℂ) : h z ^ 2 = R z := by
    dsimp [h]
    rw [mul_pow, sqrt_sq, sqrt_sq]
    field_simp
  refine ⟨ε,hε,fun z hz => (hball hz).1,h,?_,?_,?_⟩
  · intro z hz
    exact ((differentiableAt_const (Complex.sqrt (R x))).mul
      ((Complex.differentiableAt_sqrt (Or.inl (hball hz).2)).comp z
        (((hR z (hball hz).1).differentiableAt
          (hTo.mem_nhds (hball hz).1)).div_const (R x)))).differentiableWithinAt
  · intro z hz he
    have hzero : R z = 0 := by simpa [he] using (hsquare z).symm
    have hpos := (hball hz).2
    simp [hzero] at hpos
  · exact fun z _ => hsquare z

private theorem quadrant_open : IsOpen ParentWaveElliptic.quadrant :=
  (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt continuous_const Complex.continuous_im)

private theorem quadrant_convex : Convex ℝ ParentWaveElliptic.quadrant :=
  (convex_halfSpace_re_gt 0).inter (convex_halfSpace_im_gt 0)

/-- The actual elliptic primitive extends holomorphically in the local
square-root coordinate at either finite branch vertex. -/
theorem exists_vertex_extension (r A : ℝ) (hr : 0 < r) (hA : r ^ 2 ≠ A)
    {G : ℂ → ℂ}
    (hG : ∀ t ∈ ParentWaveElliptic.quadrant,
      HasDerivAt G (ParentWaveElliptic.differential (r ^ 2) A t) t) :
    ∃ ε > 0, ∃ E : ℂ → ℂ, DifferentiableOn ℂ E (Metric.ball 0 ε) ∧
      EqOn (fun u => G ((r : ℂ) + u ^ 2)) E
        (ParentWaveElliptic.quadrant ∩ Metric.ball 0 ε) := by
  let p (u : ℂ) := (r : ℂ) + u ^ 2
  let Q (u : ℂ) := (2*(r : ℂ)+u^2) * (p u ^ 2-(A : ℂ))
  let R (u : ℂ) := 16 / Q u
  let T : Set ℂ := {u | Q u ≠ 0 ∧ 0 < (p u).re}
  have hp : Differentiable ℂ p := by dsimp [p]; fun_prop
  have hQ : Differentiable ℂ Q := by dsimp [Q]; fun_prop
  have hTo : IsOpen T :=
    (isOpen_ne.preimage hQ.continuous).inter
      (isOpen_lt continuous_const (Complex.continuous_re.comp hp.continuous))
  have hQ0 : Q 0 ≠ 0 := by
    dsimp [Q,p]
    simpa only [zero_pow (by decide : (2:ℕ) ≠ 0), add_zero,
      ← Complex.ofReal_pow, ← Complex.ofReal_sub, ← Complex.ofReal_mul,
      ← Complex.ofReal_ofNat, ne_eq, Complex.ofReal_eq_zero] using
      mul_ne_zero (mul_ne_zero (by norm_num : (2:ℝ) ≠ 0) hr.ne') (sub_ne_zero.mpr hA)
  have hT0 : (0:ℂ) ∈ T := by
    exact ⟨hQ0,by simpa [p] using hr⟩
  have hR : DifferentiableOn ℂ R T := by
    intro u hu
    exact ((differentiableAt_const (16:ℂ)).div (hQ u) hu.1).differentiableWithinAt
  have hR0 : R 0 ≠ 0 := div_ne_zero (by norm_num) hQ0
  obtain ⟨ε,hε,hball,h,hh,hhn,hhsq⟩ := exists_local_square_root hTo hR hT0 hR0
  let S := ParentWaveElliptic.quadrant ∩ Metric.ball (0:ℂ) ε
  have hSo : IsOpen S := quadrant_open.inter Metric.isOpen_ball
  have hSc : Convex ℝ S := quadrant_convex.inter (convex_ball 0 ε)
  have hpS (u : ℂ) (hu : u ∈ S) : p u ∈ ParentWaveElliptic.quadrant := by
    refine ⟨(hball hu.2).2,?_⟩
    simp only [p,pow_two,Complex.add_im,Complex.ofReal_im,zero_add,Complex.mul_im]
    exact add_pos (mul_pos hu.1.1 hu.1.2) (mul_pos hu.1.2 hu.1.1)
  let d (u : ℂ) := ParentWaveElliptic.differential (r^2) A (p u) * (2*u)
  have hd (u : ℂ) (hu : u ∈ S) : HasDerivAt (fun u => G (p u)) (d u) u := by
    simpa only [d,p,Nat.cast_ofNat,pow_one,mul_one,Function.comp_def,id_eq,
      show (2:ℕ)-1=1 from rfl] using
      (hG (p u) (hpS u hu)).comp u (((hasDerivAt_id u).pow 2).const_add (r:ℂ))
  have hdc : ContinuousOn d S := by
    intro u hu
    have hdiff := ((ParentWaveElliptic.differential_differentiable (r^2) A
      (p u) (hpS u hu)).differentiableAt (quadrant_open.mem_nhds (hpS u hu))).comp u (hp u)
    exact (hdiff.continuousAt.mul ((continuous_const.mul continuous_id).continuousAt)).continuousWithinAt
  have hdsq (u : ℂ) (hu : u ∈ S) : d u ^ 2 = h u ^ 2 := by
    rw [hhsq u hu.2]
    have hun : u ≠ 0 := by
      intro he
      have hi := hu.1.2
      simp [he] at hi
    have hfac : p u ^ 2 - ((r ^ 2 : ℝ) : ℂ) = u ^ 2 * (2*(r:ℂ)+u^2) := by
      simp only [p, Complex.ofReal_pow]
      ring
    dsimp [d,ParentWaveElliptic.differential,R,Q]
    rw [mul_pow,div_pow,mul_pow,sqrt_sq,sqrt_sq,hfac]
    field_simp
    ring
  obtain ⟨E,hE,he⟩ := exists_extension_of_derivative_sq hSo hSc.isPreconnected
    Metric.isOpen_ball (convex_ball 0 ε) inter_subset_right hd hdc hh
      (fun u hu => hhn u hu.2) hdsq
  exact ⟨ε,hε,E,hE,he⟩

private theorem sqrt_mem_quadrant {z : ℂ} (hz : 0 < z.im) :
    Complex.sqrt z ∈ ParentWaveElliptic.quadrant := by
  have hn : |z.re| < ‖z‖ := Complex.abs_re_lt_norm.mpr hz.ne'
  have hp : 0 < (‖z‖ + z.re) / 2 := by linarith [neg_abs_le z.re]
  have hm : 0 < (‖z‖ - z.re) / 2 := by linarith [le_abs_self z.re]
  change 0 < (Complex.sqrt z).re ∧ 0 < (Complex.sqrt z).im
  simp only [Complex.sqrt, Complex.cpow_inv_two_re,
    Complex.cpow_inv_two_im_eq_sqrt hz.le]
  exact ⟨Real.sqrt_pos.2 hp, Real.sqrt_pos.2 hm⟩

/-- The extension at a branch vertex controls every approach from the
quadrant, including approaches tangent to either adjacent boundary side. -/
theorem exists_vertex_limit (r A : ℝ) (hr : 0 < r) (hA : r ^ 2 ≠ A)
    {G : ℂ → ℂ}
    (hG : ∀ t ∈ ParentWaveElliptic.quadrant,
      HasDerivAt G (ParentWaveElliptic.differential (r ^ 2) A t) t) :
    ∃ L : ℂ, Filter.Tendsto G (𝓝[ParentWaveElliptic.quadrant] (r:ℂ)) (𝓝 L) := by
  obtain ⟨ε,hε,E,hE,he⟩ := exists_vertex_extension r A hr hA hG
  let u (t : ℂ) := Complex.sqrt (t-(r:ℂ))
  have hu : Filter.Tendsto u (𝓝 (r:ℂ)) (𝓝 (0:ℂ)) := by
    have hs : ContinuousAt Complex.sqrt ((r:ℂ)-(r:ℂ)) :=
      Complex.continuousAt_sqrt (Or.inl (by simp))
    have ht : ContinuousAt (fun t : ℂ => t-(r:ℂ)) (r:ℂ) :=
      continuousAt_id.sub continuousAt_const
    have hc : ContinuousAt u (r:ℂ) :=
      ContinuousAt.comp (f := fun t : ℂ => t-(r:ℂ)) hs ht
    simpa [u] using hc.tendsto
  have huq : Filter.Tendsto u (𝓝[ParentWaveElliptic.quadrant] (r:ℂ)) (𝓝 (0:ℂ)) :=
    hu.mono_left nhdsWithin_le_nhds
  have hEc : ContinuousAt E (0:ℂ) :=
    ((hE 0 (Metric.mem_ball_self hε)).differentiableAt
      (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hε))).continuousAt
  refine ⟨E 0,(hEc.tendsto.comp huq).congr' ?_⟩
  filter_upwards [self_mem_nhdsWithin, huq (Metric.ball_mem_nhds 0 hε)] with t ht htu
  have hut : u t ∈ ParentWaveElliptic.quadrant :=
    sqrt_mem_quadrant (by simpa [Complex.sub_im] using ht.2)
  have hh := he ⟨hut,htu⟩
  simpa [u,sqrt_sq,add_sub_cancel] using hh.symm

/-- Away from the two branch vertices, the literal elliptic primitive
extends holomorphically across every finite boundary point. -/
theorem exists_regular_extension (B C : ℝ) {x : ℂ}
    (hxB : x ^ 2 ≠ (B:ℂ)) (hxC : x ^ 2 ≠ (C:ℂ))
    {G : ℂ → ℂ}
    (hG : ∀ t ∈ ParentWaveElliptic.quadrant,
      HasDerivAt G (ParentWaveElliptic.differential B C t) t) :
    ∃ ε > 0, ∃ E : ℂ → ℂ, DifferentiableOn ℂ E (Metric.ball x ε) ∧
      EqOn G E (ParentWaveElliptic.quadrant ∩ Metric.ball x ε) := by
  let Q (u : ℂ) := (u ^ 2-(B:ℂ)) * (u ^ 2-(C:ℂ))
  let R (u : ℂ) := 4 / Q u
  let T : Set ℂ := {u | Q u ≠ 0}
  have hQ : Differentiable ℂ Q := by dsimp [Q]; fun_prop
  have hTo : IsOpen T := isOpen_ne.preimage hQ.continuous
  have hx : x ∈ T := mul_ne_zero (sub_ne_zero.mpr hxB) (sub_ne_zero.mpr hxC)
  have hR : DifferentiableOn ℂ R T := by
    intro u hu
    exact ((differentiableAt_const (4:ℂ)).div (hQ u) hu).differentiableWithinAt
  have hRx : R x ≠ 0 := div_ne_zero (by norm_num) hx
  obtain ⟨ε,hε,hball,h,hh,hhn,hhsq⟩ := exists_local_square_root hTo hR hx hRx
  let S := ParentWaveElliptic.quadrant ∩ Metric.ball x ε
  have hSo : IsOpen S := quadrant_open.inter Metric.isOpen_ball
  have hSc : Convex ℝ S := quadrant_convex.inter (convex_ball x ε)
  have hdsq (u : ℂ) (hu : u ∈ S) :
      ParentWaveElliptic.differential B C u ^ 2 = h u ^ 2 := by
    rw [hhsq u hu.2]
    dsimp [ParentWaveElliptic.differential,R,Q]
    rw [div_pow,mul_pow,sqrt_sq,sqrt_sq]
    norm_num
  obtain ⟨E,hE,he⟩ := exists_extension_of_derivative_sq hSo hSc.isPreconnected
    Metric.isOpen_ball (convex_ball x ε) inter_subset_right
      (fun u hu => hG u hu.1)
      ((ParentWaveElliptic.differential_differentiable B C).continuousOn.mono inter_subset_left)
      hh (fun u hu => hhn u hu.2) hdsq
  exact ⟨ε,hε,E,hE,he⟩

theorem exists_regular_limit (B C : ℝ) {x : ℂ}
    (hxB : x ^ 2 ≠ (B:ℂ)) (hxC : x ^ 2 ≠ (C:ℂ))
    {G : ℂ → ℂ}
    (hG : ∀ t ∈ ParentWaveElliptic.quadrant,
      HasDerivAt G (ParentWaveElliptic.differential B C t) t) :
    ∃ L : ℂ, Filter.Tendsto G (𝓝[ParentWaveElliptic.quadrant] x) (𝓝 L) := by
  obtain ⟨ε,hε,E,hE,he⟩ := exists_regular_extension B C hxB hxC hG
  have hEc : ContinuousAt E x :=
    ((hE x (Metric.mem_ball_self hε)).differentiableAt
      (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hε))).continuousAt
  refine ⟨E x,(hEc.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_⟩
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Metric.ball_mem_nhds x hε)] with t ht htb
  exact (he ⟨ht,htb⟩).symm

private theorem root_eq_positive {x : ℂ} {B : ℝ}
    (hx : 0 ≤ x.re) (hB : 0 < B) (hsq : x ^ 2 = (B:ℂ)) :
    x = (Real.sqrt B : ℂ) := by
  have he : (Real.sqrt B : ℂ)^2 = (B:ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hB.le]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hsq.trans he.symm) with he | he
  · exact he
  · have hre := congrArg Complex.re he
    simp only [Complex.neg_re,Complex.ofReal_re] at hre
    have hp := Real.sqrt_pos.mpr hB
    linarith

/-- Every approach from the quadrant has a finite limit at every point
of its finite closure, including both elliptic branch vertices. -/
theorem exists_finite_boundary_limit (B C : ℝ) (hB : 0 < B) (hBC : B < C)
    {G : ℂ → ℂ}
    (hG : ∀ t ∈ ParentWaveElliptic.quadrant,
      HasDerivAt G (ParentWaveElliptic.differential B C t) t)
    {x : ℂ} (hx : x ∈ closure ParentWaveElliptic.quadrant) :
    ∃ L : ℂ, Filter.Tendsto G (𝓝[ParentWaveElliptic.quadrant] x) (𝓝 L) := by
  have hxre : 0 ≤ x.re :=
    closure_minimal (fun _ h => h.1.le)
      (isClosed_le continuous_const Complex.continuous_re) hx
  by_cases hxB : x ^ 2 = (B:ℂ)
  · rw [root_eq_positive hxre hB hxB]
    apply exists_vertex_limit (Real.sqrt B) C (Real.sqrt_pos.mpr hB)
      (by simpa only [Real.sq_sqrt hB.le] using hBC.ne)
    simpa only [Real.sq_sqrt hB.le] using hG
  by_cases hxC : x ^ 2 = (C:ℂ)
  · have hC := lt_trans hB hBC
    rw [root_eq_positive hxre hC hxC]
    apply exists_vertex_limit (Real.sqrt C) B (Real.sqrt_pos.mpr hC)
      (by simpa only [Real.sq_sqrt hC.le] using hBC.ne')
    intro t ht
    simpa only [Real.sq_sqrt hC.le, ParentWaveElliptic.differential,mul_comm] using hG t ht
  exact exists_regular_limit B C hxB hxC hG

/-- A global continuous extension to the closed quadrant, agreeing with
the actual primitive at every interior point. -/
theorem exists_continuous_closed_quadrant_extension
    (B C : ℝ) (hB : 0 < B) (hBC : B < C)
    {G : ℂ → ℂ}
    (hG : ∀ t ∈ ParentWaveElliptic.quadrant,
      HasDerivAt G (ParentWaveElliptic.differential B C t) t) :
    ∃ E : ℂ → ℂ, ContinuousOn E (closure ParentWaveElliptic.quadrant) ∧
      EqOn G E ParentWaveElliptic.quadrant := by
  have hc : ContinuousOn G ParentWaveElliptic.quadrant :=
    fun t ht => (hG t ht).continuousAt.continuousWithinAt
  refine ⟨extendFrom ParentWaveElliptic.quadrant G,?_,?_⟩
  · exact continuousOn_extendFrom (fun _ h => h)
      (fun x hx => exists_finite_boundary_limit B C hB hBC hG hx)
  · exact fun x hx => (extendFrom_extends hc x hx).symm

end
end ParentWaveEllipticBoundary

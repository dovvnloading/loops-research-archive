import TelescopeReturnMonodromy
import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap

/-!
# Every winding integer occurs locally in an actual quadratic return

One target coordinate and one physical involution work for every target
neighborhood. In each such neighborhood one positive radius and one
physical source basepoint work for all integers. Explicit lifted paths
realize exactly those winding integers, including negative winding and
zero. The two possible physical endpoints are determined by parity.
-/

namespace LoopsTelescopeMonodromyRealization

open Set Function
open QuadraticEscape LoopsSaturatedTelescope LoopsTelescopeRamification
open LoopsTelescopeCollar LoopsTelescopeConformalInverse
open LoopsTelescopeReturnMonodromy LoopsSquarePathMonodromy

noncomputable section

/-- Every signed integer is realized by an actual regular loop in every
neighborhood of the return's critical value. The radius and source
basepoint are independent of that integer; the target coordinate and
deck involution are independent of the neighborhood as well. Every
complete lift closes precisely for even winding and switches precisely
for odd winding. -/
theorem quadratic_return_all_local_windings (c : ℂ) (a b : ℕ)
    (A B D V : Set ℂ) (x : ℂ) (hx0 : orbit c a x = 0)
    (hVo : IsOpen V) (hVc : IsPreconnected V) (hv : orbit c b c ∈ V)
    (hD : D = connectedComponentIn (orbit c b ⁻¹' V) c)
    (hB : B = connectedComponentIn ((fun w : ℂ => w^2+c) ⁻¹' D) 0)
    (hA : A = connectedComponentIn (orbit c a ⁻¹' B) x)
    (hpinj : InjOn (orbit c a) A) (hrinj : InjOn (orbit c b) D) :
    ∃ (C : ReturnCoordinate c a b A V) (τ : ℂ → ℂ),
      AnalyticOnNhd ℂ τ A ∧ MapsTo τ A A ∧
      (∀ z ∈ A, τ (τ z) = z) ∧
      (∀ z ∈ A, orbit c a (τ z) = -(orbit c a z)) ∧
      ∀ W : Set ℂ, IsOpen W → orbit c b c ∈ W →
        ∃ r : ℝ, 0 < r ∧ ∃ z : ℂ, z ∈ A ∧
          ∀ n : ℤ, ∃ γ Γ : C(unitInterval, ℂ),
            ∃ (hγV : ∀ t, γ t ∈ V)
              (hγreg : ∀ t, γ t ≠ orbit c b c) (hγloop : γ 1 = γ 0),
              (∀ t, γ t ∈ W) ∧ Γ 0 = z ∧
              (∀ t, Γ t ∈ A ∧ orbit c (a+1+b) (Γ t) = γ t ∧
                orbit c a (Γ t) =
                  circleMap 0 r (Real.pi * (n : ℝ) * (t : ℝ))) ∧
              C.path γ hγV = exponentialLoop ((r : ℂ)^2) n ∧
              C.winding γ hγV hγreg hγloop = n ∧
              (∀ Θ : C(unitInterval, ℂ), (∀ t, Θ t ∈ A) →
                (∀ t, orbit c (a+1+b) (Θ t) = γ t) →
                (Θ 1 = Θ 0 ↔ Even n) ∧ (Θ 1 = τ (Θ 0) ↔ Odd n)) := by
  obtain ⟨C, τ, hτa, hτmap, hτinv, hτprefix, hmonodromy⟩ :=
    quadratic_return_monodromy c a b A B D V x hx0 hVo hVc hv
      hD hB hA hpinj hrinj
  have hc : c ∈ D := by
    rw [hD]
    exact mem_connectedComponentIn hv
  have h0 : (0 : ℂ) ∈ B := by
    rw [hB]
    exact mem_connectedComponentIn (by simpa using hc)
  have hDo : IsOpen D := by
    rw [hD]
    exact (hVo.preimage (quadratic_orbit_continuous c b)).connectedComponentIn
  have hBo : IsOpen B := by
    rw [hB]
    exact (hDo.preimage ((continuous_id.pow 2).add continuous_const)).connectedComponentIn
  have hAo : IsOpen A := by
    rw [hA]
    exact (hBo.preimage (quadratic_orbit_continuous c a)).connectedComponentIn
  have hBc : IsPreconnected B := by
    rw [hB]
    exact isPreconnected_connectedComponentIn
  have hAp : orbit c a '' A = B := by
    rw [hA]
    exact orbit_component_image c a B hBo hBc x (by simpa [hx0] using h0)
  obtain ⟨g, hgmap, _hgleft, hgright, hga, _hgd⟩ :=
    orbit_conformal_inverse c a A B hAo hpinj hAp
  have hgcont : ContinuousOn g B := fun z hz =>
    (hga z hz).continuousAt.continuousWithinAt
  let Q : ℂ → ℂ := fun z => orbit c b (z^2+c)
  have hQcont : Continuous Q :=
    (quadratic_orbit_continuous c b).comp ((continuous_id.pow 2).add continuous_const)
  refine ⟨C, τ, hτa, hτmap, hτinv, hτprefix, ?_⟩
  intro W hW hvW
  let U := B ∩ Q ⁻¹' W
  have hU : IsOpen U := hBo.inter (hW.preimage hQcont)
  have hU0 : (0 : ℂ) ∈ U := ⟨h0, by simpa [Q] using hvW⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU 0 hU0
  let r : ℝ := ε / 2
  have hr : 0 < r := by dsimp [r]; positivity
  have hrU : (r : ℂ) ∈ U := by
    apply hball
    rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hr]
    dsimp [r]
    linarith
  refine ⟨r, hr, g r, hgmap hrU.1, ?_⟩
  intro n
  let η : C(unitInterval, ℂ) :=
    ⟨fun t => circleMap 0 r (Real.pi * (n : ℝ) * (t : ℝ)), by
      dsimp [circleMap]
      fun_prop⟩
  have hηU (t : unitInterval) : η t ∈ U := by
    apply hball
    rw [Metric.mem_ball, dist_zero_right]
    change ‖circleMap 0 r (Real.pi * (n : ℝ) * (t : ℝ))‖ < ε
    rw [norm_circleMap_zero, abs_of_pos hr]
    dsimp [r]
    linarith
  have hηB (t : unitInterval) : η t ∈ B := (hηU t).1
  have hηD (t : unitInterval) : (η t)^2+c ∈ D := by
    have ht := hηB t
    rw [hB] at ht
    exact connectedComponentIn_subset ((fun w : ℂ => w^2+c) ⁻¹' D) 0 ht
  have hηne (t : unitInterval) : η t ≠ 0 := circleMap_ne_center (ne_of_gt hr)
  let Γ : C(unitInterval, ℂ) :=
    ⟨fun t => g (η t), hgcont.comp_continuous η.continuous hηB⟩
  have hΓA (t : unitInterval) : Γ t ∈ A := hgmap (hηB t)
  have hΓprefix (t : unitInterval) : orbit c a (Γ t) = η t := hgright (hηB t)
  let γ : C(unitInterval, ℂ) := ⟨fun t => Q (η t), hQcont.comp η.continuous⟩
  have hΓlift (t : unitInterval) : orbit c (a+1+b) (Γ t) = γ t := by
    rw [quadratic_orbit_add c (a+1) b (Γ t)]
    change orbit c b ((orbit c a (Γ t))^2+c) = Q (η t)
    rw [hΓprefix]
  have hγV (t : unitInterval) : γ t ∈ V := by
    have ht := hηD t
    rw [hD] at ht
    exact connectedComponentIn_subset (orbit c b ⁻¹' V) c ht
  have hsquare (t : unitInterval) : C.toFun (γ t) = (η t)^2 := by
    rw [← hΓlift t, C.square _ (hΓA t), hΓprefix]
  have hγreg (t : unitInterval) : γ t ≠ orbit c b c := by
    intro he
    have hz : C.toFun (γ t) = 0 := (C.zero_iff _ (hγV t)).mpr he
    rw [hsquare] at hz
    exact pow_ne_zero 2 (hηne t) hz
  have hpath : C.path γ hγV = exponentialLoop ((r : ℂ)^2) n := by
    ext t
    change C.toFun (γ t) = _
    rw [hsquare]
    change (circleMap 0 r (Real.pi * (n : ℝ) * (t : ℝ)))^2 = _
    simp only [circleMap_zero, mul_pow, ← Complex.exp_nat_mul]
    change (r : ℂ)^2 * Complex.exp ((2 : ℂ) *
      (((Real.pi * (n : ℝ) * (t : ℝ) : ℝ) : ℂ) * Complex.I)) =
      (r : ℂ)^2 * Complex.exp ((n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) *
        (t : ℝ))
    congr 2
    push_cast
    ring
  have hγloop : γ 1 = γ 0 := by
    apply C.injective (hγV 1) (hγV 0)
    change C.path γ hγV 1 = C.path γ hγV 0
    rw [hpath, exponentialLoop_one, exponentialLoop_zero]
  have hrne : ((r : ℂ)^2) ≠ 0 := by
    apply pow_ne_zero 2
    exact_mod_cast ne_of_gt hr
  have hwinding : C.winding γ hγV hγreg hγloop = n := by
    have hcongr (δ : C(unitInterval, ℂ)) (hδ : ∀ t, δ t ≠ 0)
        (hδloop : δ 1 = δ 0) (he : δ = exponentialLoop ((r : ℂ)^2) n) :
        windingNumber δ hδ hδloop = n := by
      subst δ
      exact windingNumber_exponentialLoop _ hrne n
    exact hcongr (C.path γ hγV) (C.path_ne_zero γ hγV hγreg)
      (congrArg C.toFun hγloop) hpath
  refine ⟨γ, Γ, hγV, hγreg, hγloop, fun t => (hηU t).2, ?_,
    fun t => ⟨hΓA t, hΓlift t, hΓprefix t⟩, hpath, hwinding, ?_⟩
  · simp [Γ, η, circleMap]
  · intro Θ hΘA hΘlift
    simpa only [hwinding] using
      hmonodromy γ hγV hγreg hγloop Θ hΘA hΘlift

end

end LoopsTelescopeMonodromyRealization

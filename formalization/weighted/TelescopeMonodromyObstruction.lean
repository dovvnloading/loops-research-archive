import TelescopePathPairing
import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap

/-!
# Physical monodromy in every punctured critical-value neighborhood

A half-circle in the actual critical-stage domain is transported through
the conformal prefix inverse and the actual return. Its target is a loop,
but every complete lift changes sheet. The loop can be confined to any
open neighborhood of the propagated critical value. Consequently even a
local continuous right inverse on a punctured neighborhood is impossible.
-/

namespace LoopsTelescopeMonodromyObstruction

open Set Function
open QuadraticEscape LoopsSaturatedTelescope LoopsTelescopeRamification
open LoopsTelescopeCollar LoopsTelescopeConformalInverse
open LoopsTelescopeDeckInvolution LoopsTelescopeUnbranchedCover

noncomputable section

private theorem small_half_circle (U : Set ℂ) (hU : IsOpen U) (h0 : (0 : ℂ) ∈ U) :
    ∃ r : ℝ, 0 < r ∧ ∃ η : C(unitInterval, ℂ),
      (∀ t, η t = circleMap 0 r (Real.pi * (t : ℝ))) ∧
      (∀ t, η t ∈ U) ∧ (∀ t, η t ≠ 0) ∧ η 1 = -(η 0) := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU 0 h0
  let r : ℝ := ε / 2
  have hr : 0 < r := by dsimp [r]; positivity
  let η : C(unitInterval, ℂ) :=
    ⟨fun t => circleMap 0 r (Real.pi * (t : ℝ)), by
      dsimp [circleMap]
      fun_prop⟩
  refine ⟨r, hr, η, fun _ => rfl, ?_, ?_, ?_⟩
  · intro t
    apply hball
    rw [Metric.mem_ball, dist_zero_right]
    change ‖circleMap 0 r (Real.pi * (t : ℝ))‖ < ε
    rw [norm_circleMap_zero, abs_of_pos hr]
    dsimp [r]
    linarith
  · intro t
    exact circleMap_ne_center (ne_of_gt hr)
  · simp [η, circleMap, Complex.exp_pi_mul_I]

/-- Every open neighborhood of the propagated critical value contains an
actual return loop with no closed lift in the full selected component.
The proof constructs its lift explicitly: its prefix coordinate is a
small positive-radius half-circle. No loop, covering, or phase-switching
hypothesis is assumed. -/
theorem quadratic_return_small_switching_loop (c : ℂ) (a b : ℕ)
    (A B D V : Set ℂ) (x : ℂ) (hx0 : orbit c a x = 0)
    (hVo : IsOpen V) (hVc : IsPreconnected V) (hv : orbit c b c ∈ V)
    (hD : D = connectedComponentIn (orbit c b ⁻¹' V) c)
    (hB : B = connectedComponentIn ((fun w : ℂ => w^2+c) ⁻¹' D) 0)
    (hA : A = connectedComponentIn (orbit c a ⁻¹' B) x)
    (hpinj : InjOn (orbit c a) A) (hrinj : InjOn (orbit c b) D)
    (W : Set ℂ) (hW : IsOpen W) (hvW : orbit c b c ∈ W) :
    ∃ r : ℝ, 0 < r ∧ ∃ γ Γ : C(unitInterval, ℂ),
      (∀ t, γ t ∈ V ∩ W ∧ γ t ≠ orbit c b c) ∧
      γ 1 = γ 0 ∧
      (∀ t, Γ t ∈ A ∧ orbit c (a+1+b) (Γ t) = γ t ∧
        orbit c a (Γ t) = circleMap 0 r (Real.pi * (t : ℝ))) ∧
      (∀ Θ : C(unitInterval, ℂ),
        (∀ t, Θ t ∈ A) →
        (∀ t, orbit c (a+1+b) (Θ t) = γ t) → Θ 1 ≠ Θ 0) := by
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
  let U := B ∩ Q ⁻¹' W
  have hU : IsOpen U := hBo.inter (hW.preimage hQcont)
  have hU0 : (0 : ℂ) ∈ U := ⟨h0, by simpa [Q] using hvW⟩
  obtain ⟨r, hr, η, hηformula, hηU, hηne, hηend⟩ := small_half_circle U hU hU0
  have hηB (t : unitInterval) : η t ∈ B := (hηU t).1
  have hηD (t : unitInterval) : (η t)^2+c ∈ D := by
    have ht := hηB t
    rw [hB] at ht
    exact connectedComponentIn_subset ((fun w : ℂ => w^2+c) ⁻¹' D) 0 ht
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
  have hγW (t : unitInterval) : γ t ∈ W := (hηU t).2
  have hγreg (t : unitInterval) : γ t ≠ orbit c b c := by
    intro he
    have hh : (η t)^2+c = c := hrinj (hηD t) hc he
    have hz : (η t)^2 = 0 := add_right_cancel (show (η t)^2+c = 0+c by simpa using hh)
    exact pow_ne_zero 2 (hηne t) hz
  have hγloop : γ 1 = γ 0 := by
    change Q (η 1) = Q (η 0)
    rw [hηend]
    simp [Q]
  have hΓne : Γ 1 ≠ Γ 0 := by
    intro he
    have hηeq : η 1 = η 0 := by
      rw [← hΓprefix 1, ← hΓprefix 0, he]
    rw [hηend] at hηeq
    have hz : (2 : ℂ) * η 0 = 0 := by linear_combination -hηeq
    exact hηne 0 ((mul_eq_zero.mp hz).resolve_left (by norm_num))
  obtain ⟨τ, hτan, hτmap, hτinv, _hτprefix, _hτfixed, hτfiber, _, _⟩ :=
    quadratic_return_analytic_involution c a b A B D hc hAo hB hAp hpinj hrinj
  have hτcont : ContinuousOn τ A := fun z hz =>
    (hτan z hz).continuousAt.continuousWithinAt
  let Γ' : C(unitInterval, ℂ) :=
    ⟨fun t => τ (Γ t), hτcont.comp_continuous Γ.continuous hΓA⟩
  have hΓ'A (t : unitInterval) : Γ' t ∈ A := hτmap (hΓA t)
  have hΓ'lift (t : unitInterval) : orbit c (a+1+b) (Γ' t) = γ t :=
    ((hτfiber (Γ t) (hΓA t) (Γ' t) (hΓ'A t)).mpr (Or.inr rfl)).trans (hΓlift t)
  have hΓ'ne : Γ' 1 ≠ Γ' 0 := by
    intro he
    apply hΓne
    have hh := congrArg τ he
    change τ (τ (Γ 1)) = τ (τ (Γ 0)) at hh
    simpa only [hτinv _ (hΓA 1), hτinv _ (hΓA 0)] using hh
  refine ⟨r, hr, γ, Γ, fun t => ⟨⟨hγV t, hγW t⟩, hγreg t⟩, hγloop,
    fun t => ⟨hΓA t, hΓlift t, (hΓprefix t).trans (hηformula t)⟩, ?_⟩
  intro Θ hΘA hΘlift
  have hstart : orbit c (a+1+b) (Θ 0) = orbit c (a+1+b) (Γ 0) :=
    (hΘlift 0).trans (hΓlift 0).symm
  rcases (hτfiber (Γ 0) (hΓA 0) (Θ 0) (hΘA 0)).mp hstart with he | he
  · have hu := quadratic_return_unique_path_lift c a b A B D V x hx0 hVo hVc hv
      hD hB hA hpinj hrinj γ hγV hγreg (Γ 0) (hΓA 0) (hΓlift 0)
    have hEq : Θ = Γ := hu.unique ⟨hΘA, hΘlift, he⟩ ⟨hΓA, hΓlift, rfl⟩
    simpa only [hEq] using hΓne
  · have hu := quadratic_return_unique_path_lift c a b A B D V x hx0 hVo hVc hv
      hD hB hA hpinj hrinj γ hγV hγreg (Γ' 0) (hΓ'A 0) (hΓ'lift 0)
    have hEq : Θ = Γ' := hu.unique ⟨hΘA, hΘlift, he⟩ ⟨hΓ'A, hΓ'lift, rfl⟩
    simpa only [hEq] using hΓ'ne

/-- There is no continuous choice of one actual return preimage on any
punctured neighborhood of its critical value. This conclusion is local
in the target and uses the full physical selected source component. -/
theorem quadratic_return_no_punctured_section (c : ℂ) (a b : ℕ)
    (A B D V : Set ℂ) (x : ℂ) (hx0 : orbit c a x = 0)
    (hVo : IsOpen V) (hVc : IsPreconnected V) (hv : orbit c b c ∈ V)
    (hD : D = connectedComponentIn (orbit c b ⁻¹' V) c)
    (hB : B = connectedComponentIn ((fun w : ℂ => w^2+c) ⁻¹' D) 0)
    (hA : A = connectedComponentIn (orbit c a ⁻¹' B) x)
    (hpinj : InjOn (orbit c a) A) (hrinj : InjOn (orbit c b) D)
    (W : Set ℂ) (hW : IsOpen W) (hvW : orbit c b c ∈ W) :
    ¬ ∃ s : ℂ → ℂ,
      ContinuousOn s ((V ∩ W) \ {orbit c b c}) ∧
      MapsTo s ((V ∩ W) \ {orbit c b c}) A ∧
      ∀ v ∈ ((V ∩ W) \ {orbit c b c}), orbit c (a+1+b) (s v) = v := by
  rintro ⟨s, hscont, hsmap, hsright⟩
  obtain ⟨_, _, γ, _, hγ, hγloop, _, hswitch⟩ :=
    quadratic_return_small_switching_loop c a b A B D V x hx0 hVo hVc hv
      hD hB hA hpinj hrinj W hW hvW
  have hγS (t : unitInterval) : γ t ∈ ((V ∩ W) \ {orbit c b c}) := hγ t
  let Θ : C(unitInterval, ℂ) :=
    ⟨fun t => s (γ t), hscont.comp_continuous γ.continuous hγS⟩
  apply hswitch Θ (fun t => hsmap (hγS t)) (fun t => hsright _ (hγS t))
  exact congrArg s hγloop

end

end LoopsTelescopeMonodromyObstruction

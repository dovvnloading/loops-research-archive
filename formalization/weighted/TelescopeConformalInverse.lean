import TelescopeRamification
import QuadraticExtremalMultiplier
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
import Mathlib.Analysis.Complex.Conformal

/-!
# Conformal inverse branches of actual quadratic orbit restrictions

An injective restriction on an open physical domain has a complex analytic
inverse on its entire image.  The inverse is constructed, its derivative is
the reciprocal of the actual orbit derivative, and chronological concatenation
agrees with composition of the selected inverse branches.
-/

namespace LoopsTelescopeConformalInverse

open Set Function Filter
open scoped Topology
open QuadraticEscape LoopsTelescopeRamification LoopsSaturatedTelescope

noncomputable section

/-- The actual spatial derivative is nonzero exactly when the orbit has
no critical encounter before the final time. -/
theorem orbit_deriv_ne_zero_iff (c x : ℂ) (n : ℕ) :
    deriv (orbit c n) x ≠ 0 ↔ ∀ j < n, orbit c j x ≠ 0 := by
  have htwo : (2 : ℂ) ≠ 0 := by norm_num
  rw [multiplier_eq_deriv]
  induction n with
  | zero => simp [multiplier]
  | succ n ih =>
    simp only [multiplier, mul_ne_zero_iff, htwo, true_and, ih]
    constructor
    · rintro ⟨hn, hbefore⟩ j hj
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with h | h
      · exact hbefore j h
      · simpa [h] using hn
    · intro h
      exact ⟨h n (Nat.lt_succ_self n), fun j hj => h j (Nat.lt_succ_of_lt hj)⟩

/-- Open-domain injectivity supplies actual conformality; absence of
critical points is derived from the physical restriction. -/
theorem orbit_conformal_of_open_injective (c : ℂ) (n : ℕ) (U : Set ℂ)
    (hU : IsOpen U) (hinj : InjOn (orbit c n) U) :
    ∀ x ∈ U, ConformalAt (orbit c n) x := by
  intro x hx
  exact (orbit_analytic c n x).differentiableAt.conformalAt
    ((orbit_deriv_ne_zero_iff c x n).mpr
      (orbit_injOn_no_critical_visits c n U hU hinj x hx))

/-- A canonical actual inverse is analytic on the whole open target,
with the precise inverse derivative and conformality at every target
point.  No simply connected target or boundary landing is assumed. -/
theorem orbit_conformal_inverse (c : ℂ) (n : ℕ) (U V : Set ℂ)
    (hU : IsOpen U) (hinj : InjOn (orbit c n) U)
    (himage : orbit c n '' U = V) :
    ∃ g : ℂ → ℂ,
      MapsTo g V U ∧
      LeftInvOn g (orbit c n) U ∧
      RightInvOn g (orbit c n) V ∧
      AnalyticOnNhd ℂ g V ∧
      ∀ y ∈ V,
        HasDerivAt g (deriv (orbit c n) (g y))⁻¹ y ∧ ConformalAt g y := by
  let f := orbit c n
  let g := Function.invFunOn f U
  have honto : SurjOn f U V := by
    intro y hy
    rw [← himage] at hy
    exact hy
  have hmap : MapsTo g V U := honto.mapsTo_invFunOn
  have hleft : LeftInvOn g f U := hinj.leftInvOn_invFunOn
  have hright : RightInvOn g f V := honto.rightInvOn_invFunOn
  have hlocal (x : ℂ) (hx : x ∈ U) :
      (g ∘ f) =ᶠ[𝓝 x] id :=
    Filter.Eventually.mono (hU.mem_nhds hx) (fun _ hz => hleft hz)
  have hnonzero (x : ℂ) (hx : x ∈ U) : deriv f x ≠ 0 :=
    (orbit_deriv_ne_zero_iff c x n).mpr
      (orbit_injOn_no_critical_visits c n U hU hinj x hx)
  refine ⟨g, hmap, hleft, hright, ?_, ?_⟩
  · intro y hy
    have hx : g y ∈ U := hmap hy
    have hcomp : AnalyticAt ℂ (g ∘ f) (g y) :=
      analyticAt_id.congr (Filter.EventuallyEq.symm (hlocal (g y) hx))
    have hg := (analyticAt_comp_iff_of_deriv_ne_zero
      (orbit_analytic c n (g y)) (hnonzero (g y) hx)).mp hcomp
    change AnalyticAt ℂ g (f (g y)) at hg
    rwa [hright hy] at hg
  · intro y hy
    have hx : g y ∈ U := hmap hy
    have hd : HasDerivAt g (deriv f (g y))⁻¹ (f (g y)) :=
      ((orbit_analytic c n (g y)).hasStrictDerivAt.to_local_left_inverse
        (hnonzero (g y) hx) (hlocal (g y) hx)).hasDerivAt
    have hdy : HasDerivAt g (deriv f (g y))⁻¹ y := by
      simpa only [hright hy] using hd
    refine ⟨hdy, hdy.differentiableAt.conformalAt ?_⟩
    rw [hdy.deriv]
    exact inv_ne_zero (hnonzero (g y) hx)

/-- Refining the physical source does not change its selected inverse
at any retained target point, provided the larger restriction is
injective. -/
theorem orbit_inverse_restriction_agreement (c : ℂ) (n : ℕ)
    (U W : Set ℂ) (hUW : U ⊆ W) (hinj : InjOn (orbit c n) W) :
    EqOn (Function.invFunOn (orbit c n) U)
      (Function.invFunOn (orbit c n) W) (orbit c n '' U) := by
  rintro y ⟨x, hx, rfl⟩
  rw [(hinj.mono hUW).leftInvOn_invFunOn hx,
    hinj.leftInvOn_invFunOn (hUW hx)]

/-- The inverse of a genuine concatenated orbit segment is the
composition of its selected suffix and prefix inverses, in reverse
chronological order.  The intermediate physical image is retained
explicitly; no independent branch choices enter this identity. -/
theorem orbit_inverse_concatenation (c : ℂ) (a b : ℕ)
    (U V W : Set ℂ) (hprefix : orbit c a '' U = V)
    (hsuffix : orbit c b '' V = W)
    (hpinj : InjOn (orbit c a) U) (hsinj : InjOn (orbit c b) V) :
    EqOn (Function.invFunOn (orbit c (a+b)) U)
      (Function.invFunOn (orbit c a) U ∘ Function.invFunOn (orbit c b) V) W := by
  have hreturn : InjOn (orbit c (a+b)) U := by
    intro x hx z hz h
    apply hpinj hx hz
    apply hsinj
    · rw [← hprefix]
      exact ⟨x, hx, rfl⟩
    · rw [← hprefix]
      exact ⟨z, hz, rfl⟩
    · simpa only [quadratic_orbit_add] using h
  intro y hy
  have hyimage : y ∈ orbit c b '' V := hsuffix.symm ▸ hy
  obtain ⟨v, hv, rfl⟩ := hyimage
  have hvimage : v ∈ orbit c a '' U := hprefix.symm ▸ hv
  obtain ⟨x, hx, rfl⟩ := hvimage
  change Function.invFunOn (orbit c (a+b)) U (orbit c b (orbit c a x)) =
    Function.invFunOn (orbit c a) U
      (Function.invFunOn (orbit c b) V (orbit c b (orbit c a x)))
  rw [hsinj.leftInvOn_invFunOn hv, hpinj.leftInvOn_invFunOn hx,
    ← quadratic_orbit_add, hreturn.leftInvOn_invFunOn hx]

end

end LoopsTelescopeConformalInverse

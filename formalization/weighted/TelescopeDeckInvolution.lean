import TelescopeConformalInverse

/-!
# The analytic involution of an actual one-critical quadratic return

The selected prefix inverse conjugates physical reflection to a single
analytic involution on the complete return domain. Its orbits are exactly
the full return fibers. Its fixed point is the unique point whose prefix
lands at zero, and the involution has derivative minus one there.

This is the involution of the specified physical return restriction; it
does not identify a separately prescribed relative-cover deck marking.
-/

namespace LoopsTelescopeDeckInvolution

open Set Function
open QuadraticEscape LoopsSaturatedTelescope LoopsTelescopeRamification
open LoopsTelescopeConformalInverse

noncomputable section

/-- An open univalent prefix and an injective suffix around the actual
critical quadratic component determine an analytic involution. Its complete
two-point orbits, with one critical fixed point, are precisely the fibers
of the actual composite iterate. -/
theorem quadratic_return_analytic_involution (c : ℂ) (a b : ℕ)
    (A B D : Set ℂ) (hc : c ∈ D) (hA : IsOpen A)
    (hB : B = connectedComponentIn ((fun w : ℂ => w^2+c) ⁻¹' D) 0)
    (hponto : orbit c a '' A = B)
    (hpinj : InjOn (orbit c a) A) (hrinj : InjOn (orbit c b) D) :
    ∃ τ : ℂ → ℂ,
      AnalyticOnNhd ℂ τ A ∧ MapsTo τ A A ∧
      (∀ z ∈ A, τ (τ z) = z) ∧
      (∀ z ∈ A, orbit c a (τ z) = -(orbit c a z)) ∧
      (∀ z ∈ A, τ z = z ↔ orbit c a z = 0) ∧
      (∀ z ∈ A, ∀ w ∈ A,
        orbit c (a+1+b) w = orbit c (a+1+b) z ↔ w=z ∨ w=τ z) ∧
      (∀ z ∈ A, HasDerivAt τ
        ((deriv (orbit c a) (τ z))⁻¹ * -(deriv (orbit c a) z)) z) ∧
      (∀ z ∈ A, orbit c a z = 0 → HasDerivAt τ (-1) z) := by
  obtain ⟨g, hgmap, hgleft, hgright, hga, hgd⟩ :=
    orbit_conformal_inverse c a A B hA hpinj hponto
  let τ : ℂ → ℂ := fun z => g (-(orbit c a z))
  have hprefix (z : ℂ) (hz : z ∈ A) : orbit c a z ∈ B := by
    rw [← hponto]
    exact ⟨z, hz, rfl⟩
  have hneg (z : ℂ) (hz : z ∈ A) : -(orbit c a z) ∈ B := by
    have hpz := hprefix z hz
    rw [hB] at hpz ⊢
    exact quadratic_critical_component_symmetric c D hc (orbit c a z) hpz
  have hτmap : MapsTo τ A A := fun z hz => hgmap (hneg z hz)
  have hreflect (z : ℂ) (hz : z ∈ A) :
      orbit c a (τ z) = -(orbit c a z) := hgright (hneg z hz)
  have hfixed (z : ℂ) (hz : z ∈ A) : τ z=z ↔ orbit c a z=0 := by
    constructor
    · intro he
      have hh := hreflect z hz
      rw [he] at hh
      have hzero : (2 : ℂ) * orbit c a z = 0 := by linear_combination hh
      exact (mul_eq_zero.mp hzero).resolve_left (by norm_num)
    · intro he
      apply hpinj (hτmap hz) hz
      rw [hreflect z hz, he, neg_zero]
  have hderiv (z : ℂ) (hz : z ∈ A) :
      HasDerivAt τ
        ((deriv (orbit c a) (τ z))⁻¹ * -(deriv (orbit c a) z)) z := by
    exact (hgd _ (hneg z hz)).1.comp z
      (orbit_analytic c a z).differentiableAt.hasDerivAt.neg
  refine ⟨τ, ?_, hτmap, ?_, hreflect, hfixed, ?_, hderiv, ?_⟩
  · intro z hz
    exact (hga _ (hneg z hz)).comp
      (f := fun w : ℂ => -(orbit c a w)) (x := z) (orbit_analytic c a z).neg
  · intro z hz
    change g (-(orbit c a (τ z))) = z
    rw [hreflect z hz, neg_neg]
    exact hgleft hz
  · intro z hz w hw
    obtain ⟨y, hy, hpy, _, hfiber⟩ :=
      quadratic_segment_fiber_pair c a b A B D hc hB hponto hpinj hrinj z hz
    have hyτ : y = τ z :=
      hpinj hy (hτmap hz) (hpy.trans (hreflect z hz).symm)
    simpa only [hyτ] using hfiber w hw
  · intro z hz hzero
    have hτz : τ z = z := (hfixed z hz).mpr hzero
    have hnonzero : deriv (orbit c a) z ≠ 0 :=
      (orbit_deriv_ne_zero_iff c z a).mpr
        (orbit_injOn_no_critical_visits c a A hA hpinj z hz)
    have hd := hderiv z hz
    rw [hτz] at hd
    have he : (deriv (orbit c a) z)⁻¹ * -(deriv (orbit c a) z) = -1 := by
      rw [mul_neg, inv_mul_cancel₀ hnonzero]
    rw [he] at hd
    exact hd

end

end LoopsTelescopeDeckInvolution

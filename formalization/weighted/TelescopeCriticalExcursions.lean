import TelescopePathPairing
import Mathlib.Topology.Connected.TotallyDisconnected

/-!
# Critical excursions in an actual one-critical quadratic return

Regular paths have two global lifts. A visit to the critical value changes
the continuation problem: the two sheets meet, and their next choices can
be independent. This file constructs one actual critical excursion and
classifies its complete continuous physical lifts.
-/

namespace LoopsTelescopeCriticalExcursions

open Set Function
open QuadraticEscape LoopsSaturatedTelescope LoopsTelescopeRamification
open LoopsTelescopeConformalInverse LoopsTelescopeDeckInvolution
open LoopsTelescopeUnbranchedCover

noncomputable section

private def bump (r : ℝ) (t : unitInterval) : ℂ :=
  ((r * 4 * (t : ℝ) * (1 - (t : ℝ))) : ℝ)

private theorem bump_continuous (r : ℝ) : Continuous (bump r) := by
  unfold bump
  fun_prop

private theorem bump_norm_le (r : ℝ) (hr : 0 ≤ r) (t : unitInterval) :
    ‖bump r t‖ ≤ r := by
  have ht0 := t.property.1
  have ht1 := t.property.2
  have hnonneg : 0 ≤ r * 4 * (t : ℝ) * (1 - (t : ℝ)) := by positivity
  have hquad : 4 * (t : ℝ) * (1 - (t : ℝ)) ≤ 1 := by nlinarith [sq_nonneg (2 * (t : ℝ) - 1)]
  have hmul := mul_le_mul_of_nonneg_left hquad hr
  simpa only [bump, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnonneg]
    using (show r * 4 * (t : ℝ) * (1 - (t : ℝ)) ≤ r by nlinarith)

private theorem bump_eq_zero_iff (r : ℝ) (hr : 0 < r) (t : unitInterval) :
    bump r t = 0 ↔ t = 0 ∨ t = 1 := by
  constructor
  · intro h
    have he : r * 4 * (t : ℝ) * (1 - (t : ℝ)) = 0 := by
      exact_mod_cast h
    rcases mul_eq_zero.mp he with h | h
    · have ht : (t : ℝ) = 0 :=
        (mul_eq_zero.mp h).resolve_left (mul_ne_zero (ne_of_gt hr) (by norm_num))
      exact Or.inl (Subtype.ext ht)
    · exact Or.inr (Subtype.ext (by linarith))
  · rintro (rfl | rfl) <;> simp [bump]

private theorem bump_midpoint (r : ℝ) :
    bump r (⟨1/2, by constructor <;> norm_num⟩ : unitInterval) = (r : ℂ) := by
  simp only [bump]
  push_cast
  ring

/-- A continuous square root of a nonvanishing path on the interior of
the unit interval has one sign throughout that interior. The two zero
endpoints are dealt with separately by the actual return construction. -/
theorem continuous_square_root_interior_choice
    (p e : unitInterval → ℂ) (hp : Continuous p) (he : Continuous e)
    (hne : ∀ t ∈ Ioo (0 : unitInterval) 1, e t ≠ 0)
    (hsq : ∀ t, p t ^ 2 = e t ^ 2) :
    EqOn p e (Ioo 0 1) ∨ EqOn p (fun t => -(e t)) (Ioo 0 1) := by
  let S : Set unitInterval := Ioo 0 1
  let q : unitInterval → ℂ := fun t => p t / e t
  have hqc : ContinuousOn q S := hp.continuousOn.div he.continuousOn hne
  have hqm : MapsTo q S ({1, -1} : Set ℂ) := by
    intro t ht
    rcases (sq_eq_sq_iff_eq_or_eq_neg).mp (hsq t) with h | h
    · simp [q, h, hne t ht]
    · simp [q, h, hne t ht]
  obtain ⟨v, hv, hqv⟩ := (isPreconnected_Ioo : IsPreconnected S).eqOn_const_of_mapsTo
    (Set.toFinite ({1, -1} : Set ℂ)).isDiscrete hqc hqm (by simp)
  rcases hv with hv | hv
  · have hv1 : v = 1 := hv
    left
    intro t ht
    have hh := hqv ht
    change p t / e t = v at hh
    rw [hv1] at hh
    exact (div_eq_one_iff_eq (hne t ht)).mp hh
  · have hvn : v = -1 := by simpa using hv
    right
    intro t ht
    have hh := hqv ht
    change p t / e t = v at hh
    rw [hvn] at hh
    exact (div_eq_iff (hne t ht)).mp hh |>.trans (by ring)

/-- Every actual selected one-critical return contains a target loop
which visits the propagated critical value only at its endpoints. It has
exactly two continuous lifts in the complete physical return source,
both based at the critical anchor. -/
theorem quadratic_return_critical_excursion
    (c : ℂ) (a b : ℕ) (A B D V : Set ℂ) (x : ℂ)
    (hx0 : orbit c a x = 0)
    (hVo : IsOpen V) (hVc : IsPreconnected V) (hv : orbit c b c ∈ V)
    (hD : D = connectedComponentIn (orbit c b ⁻¹' V) c)
    (hB : B = connectedComponentIn ((fun w : ℂ => w^2+c) ⁻¹' D) 0)
    (hA : A = connectedComponentIn (orbit c a ⁻¹' B) x)
    (hpinj : InjOn (orbit c a) A) (hrinj : InjOn (orbit c b) D) :
    ∃ (hxA : x ∈ A) (γ : Path (orbit c b c) (orbit c b c)),
      (∀ t, γ t ∈ V) ∧
      (∀ t, γ t = orbit c b c ↔ t = 0 ∨ t = 1) ∧
      ∃ L₀ L₁ : Path (⟨x, hxA⟩ : A) ⟨x, hxA⟩,
        L₀ ≠ L₁ ∧
        ∀ L : Path (⟨x, hxA⟩ : A) ⟨x, hxA⟩,
          (∀ t, orbit c (a+1+b) (L t) = γ t) ↔ L = L₀ ∨ L = L₁ := by
  have hcD : c ∈ D := by rw [hD]; exact mem_connectedComponentIn hv
  have h0B : (0 : ℂ) ∈ B := by
    rw [hB]
    exact mem_connectedComponentIn (by simpa using hcD)
  have hxA : x ∈ A := by rw [hA]; exact mem_connectedComponentIn (hx0.symm ▸ h0B)
  have hDo : IsOpen D := by
    rw [hD]
    exact (hVo.preimage (quadratic_orbit_continuous c b)).connectedComponentIn
  have hBo : IsOpen B := by
    rw [hB]
    exact (hDo.preimage ((continuous_id.pow 2).add continuous_const)).connectedComponentIn
  have hAo : IsOpen A := by
    rw [hA]
    exact (hBo.preimage (quadratic_orbit_continuous c a)).connectedComponentIn
  have hBc : IsPreconnected B := by rw [hB]; exact isPreconnected_connectedComponentIn
  have hAp : orbit c a '' A = B := by
    rw [hA]
    exact orbit_component_image c a B hBo hBc x (hx0.symm ▸ h0B)
  obtain ⟨g, hgmap, hgleft, hgright, hga, _⟩ :=
    orbit_conformal_inverse c a A B hAo hpinj hAp
  have hg0 : g 0 = x := by rw [← hx0]; exact hgleft hxA
  obtain ⟨ε, hε, hεB⟩ := Metric.isOpen_iff.mp hBo 0 h0B
  let r : ℝ := ε / 2
  have hr : 0 < r := half_pos hε
  have heB (t : unitInterval) : bump r t ∈ B := by
    apply hεB
    rw [Metric.mem_ball, dist_zero_right]
    exact lt_of_le_of_lt (bump_norm_le r hr.le t) (by dsimp [r]; linarith)
  have hneB (t : unitInterval) : -(bump r t) ∈ B := by
    rw [hB] at heB ⊢
    exact quadratic_critical_component_symmetric c D hcD _ (heB t)
  have hqD (t : unitInterval) : (bump r t)^2+c ∈ D := by
    have ht := heB t
    rw [hB] at ht
    exact connectedComponentIn_subset _ _ ht
  have hγV (t : unitInterval) : orbit c b ((bump r t)^2+c) ∈ V := by
    have ht := hqD t
    rw [hD] at ht
    exact connectedComponentIn_subset _ _ ht
  let γ : Path (orbit c b c) (orbit c b c) :=
    { toFun := fun t => orbit c b ((bump r t)^2+c)
      continuous_toFun := (quadratic_orbit_continuous c b).comp
        (((bump_continuous r).pow 2).add continuous_const)
      source' := by simp [bump]
      target' := by simp [bump] }
  let L₀ : Path (⟨x, hxA⟩ : A) ⟨x, hxA⟩ :=
    { toFun := fun t => ⟨g (bump r t), hgmap (heB t)⟩
      continuous_toFun := (hga.continuousOn.comp_continuous (bump_continuous r) heB).subtype_mk _
      source' := by apply Subtype.ext; simpa [bump] using hg0
      target' := by apply Subtype.ext; simpa [bump] using hg0 }
  let L₁ : Path (⟨x, hxA⟩ : A) ⟨x, hxA⟩ :=
    { toFun := fun t => ⟨g (-(bump r t)), hgmap (hneB t)⟩
      continuous_toFun := (hga.continuousOn.comp_continuous
        (bump_continuous r).neg hneB).subtype_mk _
      source' := by apply Subtype.ext; simpa [bump] using hg0
      target' := by apply Subtype.ext; simpa [bump] using hg0 }
  have hL₀ (t : unitInterval) : orbit c a (L₀ t) = bump r t := hgright (heB t)
  have hL₁ (t : unitInterval) : orbit c a (L₁ t) = -(bump r t) := hgright (hneB t)
  have hreturn₀ (t : unitInterval) : orbit c (a+1+b) (L₀ t) = γ t := by
    rw [quadratic_orbit_add c (a+1) b]
    change orbit c b ((orbit c a (L₀ t))^2+c) = γ t
    rw [hL₀]
    rfl
  have hreturn₁ (t : unitInterval) : orbit c (a+1+b) (L₁ t) = γ t := by
    rw [quadratic_orbit_add c (a+1) b]
    change orbit c b ((orbit c a (L₁ t))^2+c) = γ t
    rw [hL₁, neg_sq]
    rfl
  refine ⟨hxA, γ, hγV, ?_, L₀, L₁, ?_, ?_⟩
  · intro t
    change orbit c b ((bump r t)^2+c) = orbit c b c ↔ _
    constructor
    · intro ht
      have he := hrinj (hqD t) hcD ht
      have hz : bump r t = 0 := pow_eq_zero (by linear_combination he)
      exact (bump_eq_zero_iff r hr t).mp hz
    · rintro (rfl | rfl) <;> simp [bump]
  · intro he
    let t : unitInterval := ⟨1/2, by constructor <;> norm_num⟩
    have hp : bump r t = -(bump r t) :=
      (hL₀ t).symm.trans ((congrArg (fun L : Path (⟨x, hxA⟩ : A) ⟨x, hxA⟩ =>
        orbit c a (L t)) he).trans (hL₁ t))
    rw [bump_midpoint] at hp
    have hrr : r = -r := by exact_mod_cast hp
    linarith
  · intro L
    constructor
    · intro hL
      let p : unitInterval → ℂ := fun t => orbit c a (L t)
      have hpc : Continuous p := (quadratic_orbit_continuous c a).comp
        (continuous_subtype_val.comp L.continuous)
      have hsquare (t : unitInterval) : p t ^ 2 = bump r t ^ 2 := by
        have hpB : p t ∈ B := hAp ▸ mem_image_of_mem _ (L t).property
        have hpD : (p t)^2+c ∈ D := by
          rw [hB] at hpB
          exact connectedComponentIn_subset _ _ hpB
        have he : orbit c b ((p t)^2+c) = orbit c b ((bump r t)^2+c) := by
          simpa only [quadratic_orbit_add, orbit] using hL t
        exact add_right_cancel (hrinj hpD (hqD t) he)
      have hnonzero (t : unitInterval) (ht : t ∈ Ioo (0 : unitInterval) 1) :
          bump r t ≠ 0 := by
        intro hz
        rcases (bump_eq_zero_iff r hr t).mp hz with hz | hz
        · exact (ne_of_gt ht.1) hz
        · exact (ne_of_lt ht.2) hz
      have hext (Q : Path (⟨x, hxA⟩ : A) ⟨x, hxA⟩)
          (hQ : ∀ t ∈ Ioo (0 : unitInterval) 1, p t = orbit c a (Q t)) : L = Q := by
        apply Path.ext
        funext t
        by_cases ht0 : t = 0
        · simp [ht0]
        by_cases ht1 : t = 1
        · simp [ht1]
        apply Subtype.ext
        apply hpinj (L t).property (Q t).property
        exact hQ t ⟨lt_of_le_of_ne (show (0 : unitInterval) ≤ t from bot_le) (Ne.symm ht0),
          lt_of_le_of_ne (show t ≤ (1 : unitInterval) from le_top) ht1⟩
      rcases continuous_square_root_interior_choice p (bump r) hpc
          (bump_continuous r) hnonzero hsquare with hp | hp
      · exact Or.inl (hext L₀ (fun t ht => (hp ht).trans (hL₀ t).symm))
      · exact Or.inr (hext L₁ (fun t ht => (hp ht).trans (hL₁ t).symm))
    · rintro (rfl | rfl)
      · exact hreturn₀
      · exact hreturn₁

end

end LoopsTelescopeCriticalExcursions

import TelescopeUnbranchedCover

/-!
# The two coherent physical lifts of every regular return path

One analytic deck involution, fixed independently of the path, exchanges
the two continuous lifts of every target path avoiding the propagated
critical value. The lifts never meet. Every continuous lift in the full
physical return component is one of these two entire paths.
-/

namespace LoopsTelescopePathPairing

open Set Function
open QuadraticEscape LoopsSaturatedTelescope LoopsTelescopeRamification
open LoopsTelescopeCollar LoopsTelescopeDeckInvolution
open LoopsTelescopeUnbranchedCover

noncomputable section

/-- A single analytic physical deck involution pairs every regular
target path's exactly two continuous lifts. The pairing holds at every
time, and there is no third lift or switching between the two phases.
Neither a covering nor a lift is assumed in the hypotheses. -/
theorem quadratic_return_deck_paired_paths (c : ℂ) (a b : ℕ)
    (A B D V : Set ℂ) (x : ℂ) (hx0 : orbit c a x = 0)
    (hVo : IsOpen V) (hVc : IsPreconnected V) (hv : orbit c b c ∈ V)
    (hD : D = connectedComponentIn (orbit c b ⁻¹' V) c)
    (hB : B = connectedComponentIn ((fun w : ℂ => w^2+c) ⁻¹' D) 0)
    (hA : A = connectedComponentIn (orbit c a ⁻¹' B) x)
    (hpinj : InjOn (orbit c a) A) (hrinj : InjOn (orbit c b) D) :
    ∃ τ : ℂ → ℂ,
      AnalyticOnNhd ℂ τ A ∧ MapsTo τ A A ∧
      (∀ z ∈ A, τ (τ z) = z) ∧
      (∀ z ∈ A, orbit c a (τ z) = -(orbit c a z)) ∧
      ∀ γ : C(unitInterval, ℂ),
        (∀ t, γ t ∈ V) → (∀ t, γ t ≠ orbit c b c) →
        ∃ Γ₀ Γ₁ : C(unitInterval, ℂ),
          (∀ t, Γ₀ t ∈ A ∧ Γ₁ t ∈ A) ∧
          (∀ t, orbit c (a+1+b) (Γ₀ t) = γ t ∧
            orbit c (a+1+b) (Γ₁ t) = γ t) ∧
          (∀ t, Γ₁ t = τ (Γ₀ t) ∧ Γ₀ t ≠ Γ₁ t) ∧
          (∀ Γ : C(unitInterval, ℂ),
            ((∀ t, Γ t ∈ A) ∧ (∀ t, orbit c (a+1+b) (Γ t) = γ t)) ↔
              Γ = Γ₀ ∨ Γ = Γ₁) ∧
          Nat.card {Γ : C(unitInterval, ℂ) //
            (∀ t, Γ t ∈ A) ∧ (∀ t, orbit c (a+1+b) (Γ t) = γ t)} = 2 := by
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
  obtain ⟨_, honto, _, _⟩ :=
    selected_saturated_return_full_degree c a b A B D V x hx0 hVo hVc hv
      hD hB hA hpinj hrinj
  obtain ⟨τ, hτan, hτmap, hτinv, hτprefix, hτfixed, hτfiber, _, _⟩ :=
    quadratic_return_analytic_involution c a b A B D hc hAo hB hAp hpinj hrinj
  refine ⟨τ, hτan, hτmap, hτinv, hτprefix, ?_⟩
  intro γ hγV hγreg
  have hγimage : γ 0 ∈ orbit c (a+1+b) '' A := honto.symm ▸ hγV 0
  obtain ⟨z, hz, hzγ⟩ := hγimage
  obtain ⟨Γ₀, hΓ₀, huniq₀⟩ :=
    quadratic_return_unique_path_lift c a b A B D V x hx0 hVo hVc hv
      hD hB hA hpinj hrinj γ hγV hγreg z hz hzγ
  have hτcont : ContinuousOn τ A := fun w hw =>
    (hτan w hw).continuousAt.continuousWithinAt
  let Γ₁ : C(unitInterval, ℂ) :=
    ⟨fun t => τ (Γ₀ t), hτcont.comp_continuous Γ₀.continuous hΓ₀.1⟩
  have hΓ₁A (t : unitInterval) : Γ₁ t ∈ A := hτmap (hΓ₀.1 t)
  have hΓ₁lift (t : unitInterval) : orbit c (a+1+b) (Γ₁ t) = γ t :=
    ((hτfiber (Γ₀ t) (hΓ₀.1 t) (Γ₁ t) (hΓ₁A t)).mpr (Or.inr rfl)).trans
      (hΓ₀.2.1 t)
  have hΓ₁zero : Γ₁ 0 = τ z := by
    change τ (Γ₀ 0) = τ z
    rw [hΓ₀.2.2]
  have hdisjoint (t : unitInterval) : Γ₀ t ≠ Γ₁ t := by
    intro he
    have hzero : orbit c a (Γ₀ t) = 0 :=
      (hτfixed (Γ₀ t) (hΓ₀.1 t)).mp he.symm
    apply hγreg t
    rw [← hΓ₀.2.1 t, quadratic_orbit_add c (a+1) b (Γ₀ t)]
    change orbit c b ((orbit c a (Γ₀ t))^2+c) = orbit c b c
    simp [hzero]
  have hτzvalue : orbit c (a+1+b) (τ z) = γ 0 :=
    ((hτfiber z hz (τ z) (hτmap hz)).mpr (Or.inr rfl)).trans hzγ
  have hclass (Γ : C(unitInterval, ℂ)) :
      ((∀ t, Γ t ∈ A) ∧ (∀ t, orbit c (a+1+b) (Γ t) = γ t)) ↔
        Γ = Γ₀ ∨ Γ = Γ₁ := by
    constructor
    · intro hΓ
      have hstart : orbit c (a+1+b) (Γ 0) = orbit c (a+1+b) z :=
        (hΓ.2 0).trans hzγ.symm
      rcases (hτfiber z hz (Γ 0) (hΓ.1 0)).mp hstart with he | he
      · exact Or.inl (huniq₀ Γ ⟨hΓ.1, hΓ.2, he⟩)
      · have hu := quadratic_return_unique_path_lift c a b A B D V x hx0 hVo hVc hv
          hD hB hA hpinj hrinj γ hγV hγreg (τ z) (hτmap hz) hτzvalue
        exact Or.inr (hu.unique ⟨hΓ.1, hΓ.2, he⟩ ⟨hΓ₁A, hΓ₁lift, hΓ₁zero⟩)
    · rintro (rfl | rfl)
      · exact ⟨hΓ₀.1, hΓ₀.2.1⟩
      · exact ⟨hΓ₁A, hΓ₁lift⟩
  refine ⟨Γ₀, Γ₁, fun t => ⟨hΓ₀.1 t, hΓ₁A t⟩,
    fun t => ⟨hΓ₀.2.1 t, hΓ₁lift t⟩, fun t => ⟨rfl, hdisjoint t⟩, hclass, ?_⟩
  let P : C(unitInterval, ℂ) → Prop := fun Γ =>
    (∀ t, Γ t ∈ A) ∧ (∀ t, orbit c (a+1+b) (Γ t) = γ t)
  let L₀ : {Γ // P Γ} := ⟨Γ₀, hΓ₀.1, hΓ₀.2.1⟩
  let L₁ : {Γ // P Γ} := ⟨Γ₁, hΓ₁A, hΓ₁lift⟩
  apply Nat.card_eq_two_iff.mpr
  refine ⟨L₀, L₁, ?_, ?_⟩
  · intro he
    exact hdisjoint 0 (congrArg (fun L : {Γ // P Γ} => L.val 0) he)
  · apply Set.eq_univ_of_forall
    intro L
    rcases (hclass L.val).mp L.property with he | he
    · exact Or.inl (Subtype.ext he)
    · exact Or.inr (Subtype.ext he)

end

end LoopsTelescopePathPairing

import CriticalPhaseCensus
import TelescopeDeckInvolution

/-!
# Critical-crossing phase of an actual selected quadratic return

The regular-path theorem in TelescopePathPairing forbids the propagated
critical value. Here the full space of continuous physical lifts is
classified by open phase cuts on its complement, with no finiteness or
isolation hypothesis on the critical encounters.
-/

namespace LoopsTelescopeCriticalPhase

open Set Function
open QuadraticEscape LoopsSaturatedTelescope LoopsTelescopeRamification
open LoopsTelescopeDeckInvolution LoopsCriticalPhase

noncomputable section

/-- For an actual one-critical return, meeting its propagated critical
value is exactly meeting the unique zero of the univalent prefix. -/
theorem quadratic_return_critical_value_iff (c : ℂ) (a b : ℕ)
    (A B D : Set ℂ) (hc : c ∈ D)
    (hB : B = connectedComponentIn ((fun w : ℂ => w ^ 2 + c) ⁻¹' D) 0)
    (hponto : orbit c a '' A = B) (hrinj : InjOn (orbit c b) D)
    (z : ℂ) (hz : z ∈ A) :
    orbit c (a + 1 + b) z = orbit c b c ↔ orbit c a z = 0 := by
  have hpz : orbit c a z ∈ B := hponto ▸ mem_image_of_mem _ hz
  have hqz : (orbit c a z) ^ 2 + c ∈ D := by
    rw [hB] at hpz
    exact connectedComponentIn_subset ((fun w : ℂ => w ^ 2 + c) ⁻¹' D) 0 hpz
  rw [quadratic_orbit_add c (a + 1) b z]
  change orbit c b ((orbit c a z) ^ 2 + c) = orbit c b c ↔ orbit c a z = 0
  constructor
  · intro h
    have hs := hrinj hqz hc h
    have hzsq : (orbit c a z) ^ 2 = 0 := by linear_combination hs
    rcases mul_eq_zero.mp (by simpa only [pow_two] using hzsq) with he | he
    · exact he
    · exact he
  · intro h
    simp [h]

/-- Continuous physical lifts of the target trace of a reference lift.
Membership retains the actual source component, not a symbolic sheet label. -/
def PhysicalLifts {X : Type*} [TopologicalSpace X]
    (c : ℂ) (n : ℕ) (A : Set ℂ) (Γ : C(X, ℂ)) :=
  {Λ : C(X, ℂ) // (∀ t, Λ t ∈ A) ∧
    ∀ t, orbit c n (Λ t) = orbit c n (Γ t)}

/-- The full space of continuous physical lifts of any reference trace
is exactly the space of phase cuts on its regular locus. This includes
arbitrary parameter spaces and arbitrarily accumulating critical encounters.
The same analytic involution works for every reference trace. -/
theorem quadratic_return_phase_classification
    {X : Type*} [TopologicalSpace X]
    (c : ℂ) (a b : ℕ) (A B D : Set ℂ) (hc : c ∈ D) (hA : IsOpen A)
    (hB : B = connectedComponentIn ((fun w : ℂ => w ^ 2 + c) ⁻¹' D) 0)
    (hponto : orbit c a '' A = B)
    (hpinj : InjOn (orbit c a) A) (hrinj : InjOn (orbit c b) D) :
    ∃ τ : ℂ → ℂ,
      AnalyticOnNhd ℂ τ A ∧ MapsTo τ A A ∧
      (∀ z ∈ A, τ (τ z) = z) ∧
      ∀ (Γ : C(X, ℂ)), (∀ t, Γ t ∈ A) →
        ∃ e : PhysicalLifts c (a + 1 + b) A Γ ≃
            PhaseCut {t | orbit c (a + 1 + b) (Γ t) ≠ orbit c b c},
          ∀ (Λ : PhysicalLifts c (a + 1 + b) A Γ) t,
            t ∈ (e Λ).carrier ↔
              Λ.val t = τ (Γ t) ∧
                orbit c (a + 1 + b) (Γ t) ≠ orbit c b c := by
  obtain ⟨τ, hτan, hτmap, hτinv, _, hτfixed, hτfiber, _, _⟩ :=
    quadratic_return_analytic_involution c a b A B D hc hA hB hponto hpinj hrinj
  refine ⟨τ, hτan, hτmap, hτinv, ?_⟩
  intro Γ hΓ
  let Τ : C(X, ℂ) := ⟨fun t => τ (Γ t),
    hτan.continuousOn.comp_continuous Γ.continuous hΓ⟩
  have hΤ (t : X) : Τ t ∈ A := hτmap (hΓ t)
  have hregular (t : X) : Τ t ≠ Γ t ↔
      orbit c (a + 1 + b) (Γ t) ≠ orbit c b c := by
    exact not_congr ((hτfixed (Γ t) (hΓ t)).trans
      (quadratic_return_critical_value_iff c a b A B D hc hB hponto hrinj
        (Γ t) (hΓ t)).symm)
  have hR : {t | Τ t ≠ Γ t} =
      {t | orbit c (a + 1 + b) (Γ t) ≠ orbit c b c} := by
    ext t
    exact hregular t
  let e₀ : PhysicalLifts c (a + 1 + b) A Γ ≃
      {Λ : C(X, ℂ) // ∀ t, Λ t = Τ t ∨ Λ t = Γ t} :=
    { toFun := fun Λ => ⟨Λ.val, fun t => by
        rcases (hτfiber (Γ t) (hΓ t) (Λ.val t) (Λ.property.1 t)).mp
            (Λ.property.2 t) with he | he
        · exact Or.inr he
        · exact Or.inl he⟩
      invFun := fun Λ => ⟨Λ.val, (fun t => by
          rcases Λ.property t with he | he
          · rw [he]
            exact hΤ t
          · rw [he]
            exact hΓ t), fun t => by
          apply (hτfiber (Γ t) (hΓ t) (Λ.val t) (by
            rcases Λ.property t with he | he
            · rw [he]
              exact hΤ t
            · rw [he]
              exact hΓ t)).mpr
          rcases Λ.property t with he | he
          · exact Or.inr he
          · exact Or.inl he⟩
      left_inv := by intro Λ; rfl
      right_inv := by intro Λ; rfl }
  let e := (e₀.trans (phaseChoiceEquiv Τ Γ)).trans (phaseCutCongr hR)
  refine ⟨e, ?_⟩
  intro Λ t
  simp only [e, Equiv.trans_apply, phaseCutCongr_carrier, phaseChoiceEquiv_carrier]
  change (Λ.val t = Τ t ∧ Τ t ≠ Γ t) ↔ _
  exact and_congr Iff.rfl (hregular t)

/-- The exact number of physical lifts is exponential in the number of
regular excursions, even though the return itself has degree two. -/
theorem quadratic_return_excursion_lift_count
    {X ι : Type*} [TopologicalSpace X] [Fintype ι]
    (c : ℂ) (a b : ℕ) (A B D : Set ℂ) (hc : c ∈ D) (hA : IsOpen A)
    (hB : B = connectedComponentIn ((fun w : ℂ => w ^ 2 + c) ⁻¹' D) 0)
    (hponto : orbit c a '' A = B)
    (hpinj : InjOn (orbit c a) A) (hrinj : InjOn (orbit c b) D)
    (Γ : C(X, ℂ)) (hΓ : ∀ t, Γ t ∈ A) (U : ι → Set X)
    (hopen : ∀ i, IsOpen (U i)) (hconn : ∀ i, IsPreconnected (U i))
    (hne : ∀ i, (U i).Nonempty)
    (hdis : Pairwise (fun i j => Disjoint (U i) (U j)))
    (hcover : {t | orbit c (a + 1 + b) (Γ t) ≠ orbit c b c} = ⋃ i, U i) :
    Nat.card (PhysicalLifts c (a + 1 + b) A Γ) = 2 ^ Fintype.card ι := by
  obtain ⟨_, _, _, _, hclass⟩ :=
    quadratic_return_phase_classification (X := X) c a b A B D
      hc hA hB hponto hpinj hrinj
  obtain ⟨e, _⟩ := hclass Γ hΓ
  exact (Nat.card_congr e).trans
    (phaseCut_excursion_count _ U hopen hconn hne hdis hcover)

end

end LoopsTelescopeCriticalPhase

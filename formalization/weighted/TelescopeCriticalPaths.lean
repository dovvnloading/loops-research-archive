import TelescopeCriticalPhase
import TelescopeCriticalLift
import CriticalPhaseExcursions

/-!
# Complete critical-crossing classification without an assumed reference lift

Existence and phase classification are assembled for the actual selected
return. The reference lift is constructed with any prescribed initial inverse
point. An independent target path is the input to the exact lift census.
-/

namespace LoopsTelescopeCriticalPaths

open Set Function
open QuadraticEscape LoopsSaturatedTelescope LoopsTelescopeRamification
open LoopsTelescopeCollar LoopsTelescopeCriticalPhase LoopsCriticalPhase
open LoopsTelescopeCriticalLift

noncomputable section

/-- All continuous lifts in the actual source of an independently given
target path. -/
def TargetLifts {X : Type*} [TopologicalSpace X]
    (c : ℂ) (n : ℕ) (A : Set ℂ) (γ : C(X, ℂ)) :=
  {Λ : C(X, ℂ) // (∀ t, Λ t ∈ A) ∧ ∀ t, orbit c n (Λ t) = γ t}

/-- Changing from a target trace to one of its physical reference lifts
preserves the entire lift, not merely its endpoints. -/
def targetReferenceEquiv {X : Type*} [TopologicalSpace X]
    (c : ℂ) (n : ℕ) (A : Set ℂ) (γ Γ : C(X, ℂ))
    (hΓ : ∀ t, orbit c n (Γ t) = γ t) :
    TargetLifts c n A γ ≃ PhysicalLifts c n A Γ where
  toFun := fun Λ => ⟨Λ.val, Λ.property.1,
    fun t => (Λ.property.2 t).trans (hΓ t).symm⟩
  invFun := fun Λ => ⟨Λ.val, Λ.property.1,
    fun t => (Λ.property.2 t).trans (hΓ t)⟩
  left_inv := by intro Λ; rfl
  right_inv := by intro Λ; rfl

/-- Every target path has a constructed reference lift with the prescribed
initial point, and its full lift space is exactly the regular-time phase-cut
space. Arbitrarily accumulating branch-value encounters are permitted. -/
theorem quadratic_return_all_path_classification (c : ℂ) (a b : ℕ)
    (A B D V : Set ℂ) (x : ℂ) (hx0 : orbit c a x = 0)
    (hVo : IsOpen V) (hVc : IsPreconnected V) (hv : orbit c b c ∈ V)
    (hD : D = connectedComponentIn (orbit c b ⁻¹' V) c)
    (hB : B = connectedComponentIn ((fun w : ℂ => w ^ 2 + c) ⁻¹' D) 0)
    (hA : A = connectedComponentIn (orbit c a ⁻¹' B) x)
    (hpinj : InjOn (orbit c a) A) (hrinj : InjOn (orbit c b) D)
    (γ : C(unitInterval, ℂ)) (hγV : ∀ t, γ t ∈ V)
    (z : ℂ) (hz : z ∈ A) (hzγ : orbit c (a + 1 + b) z = γ 0) :
    ∃ Γ : TargetLifts c (a + 1 + b) A γ,
      Γ.val 0 = z ∧
      Nonempty (TargetLifts c (a + 1 + b) A γ ≃
        PhaseCut {t | γ t ≠ orbit c b c}) ∧
      Nonempty (TargetLifts c (a + 1 + b) A γ ≃
        (RegularExcursions {t | γ t ≠ orbit c b c} → Bool)) := by
  obtain ⟨Γ, hΓA, hΓR, hΓ0⟩ :=
    quadratic_return_path_lift_with_critical_crossings c a b A B D V x hx0
      hVo hVc hv hD hB hA hpinj hrinj γ hγV z hz hzγ
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
  obtain ⟨_, _, _, _, hclass⟩ :=
    quadratic_return_phase_classification (X := unitInterval) c a b A B D
      hc hAo hB hAp hpinj hrinj
  obtain ⟨e, _⟩ := hclass Γ hΓA
  have hR : {t | orbit c (a + 1 + b) (Γ t) ≠ orbit c b c} =
      {t | γ t ≠ orbit c b c} := by
    ext t
    rw [hΓR t]
  let E := ((targetReferenceEquiv c (a + 1 + b) A γ Γ hΓR).trans e).trans
    (phaseCutCongr hR)
  letI : LocallyPathConnectedSpace unitInterval :=
    (convex_Icc (0 : ℝ) 1).locallyPathConnectedSpace
  obtain ⟨eR⟩ := phaseCut_regularExcursions_equiv {t | γ t ≠ orbit c b c}
    (isClosed_eq γ.continuous continuous_const).isOpen_compl
  exact ⟨⟨Γ, hΓA, hΓR⟩, hΓ0, ⟨E⟩, ⟨E.trans eR⟩⟩

/-- The target path itself determines the exact lift count. No continuous
reference lift, phase label, or noncritical-time finiteness is assumed;
the finite excursion decomposition is an actual open connected partition. -/
theorem quadratic_return_target_excursion_count
    {ι : Type*} [Fintype ι] (c : ℂ) (a b : ℕ)
    (A B D V : Set ℂ) (x : ℂ) (hx0 : orbit c a x = 0)
    (hVo : IsOpen V) (hVc : IsPreconnected V) (hv : orbit c b c ∈ V)
    (hD : D = connectedComponentIn (orbit c b ⁻¹' V) c)
    (hB : B = connectedComponentIn ((fun w : ℂ => w ^ 2 + c) ⁻¹' D) 0)
    (hA : A = connectedComponentIn (orbit c a ⁻¹' B) x)
    (hpinj : InjOn (orbit c a) A) (hrinj : InjOn (orbit c b) D)
    (γ : C(unitInterval, ℂ)) (hγV : ∀ t, γ t ∈ V)
    (U : ι → Set unitInterval)
    (hopen : ∀ i, IsOpen (U i)) (hconn : ∀ i, IsPreconnected (U i))
    (hne : ∀ i, (U i).Nonempty)
    (hdis : Pairwise (fun i j => Disjoint (U i) (U j)))
    (hcover : {t | γ t ≠ orbit c b c} = ⋃ i, U i) :
    Nat.card (TargetLifts c (a + 1 + b) A γ) = 2 ^ Fintype.card ι := by
  obtain ⟨_, honto, _, _⟩ :=
    selected_saturated_return_full_degree c a b A B D V x hx0
      hVo hVc hv hD hB hA hpinj hrinj
  obtain ⟨z, hz, hzγ⟩ := honto.symm ▸ hγV 0
  obtain ⟨_, _, ⟨e⟩, _⟩ :=
    quadratic_return_all_path_classification c a b A B D V x hx0
      hVo hVc hv hD hB hA hpinj hrinj γ hγV z hz hzγ
  exact (Nat.card_congr e).trans
    (phaseCut_excursion_count _ U hopen hconn hne hdis hcover)

end

end LoopsTelescopeCriticalPaths

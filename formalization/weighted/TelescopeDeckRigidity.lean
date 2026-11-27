import TelescopeDeckInvolution
import Mathlib.Analysis.Analytic.IsolatedZeros

/-!
# Rigidity and transport of the actual quadratic return involution

Every analytic self-map preserving the fibers of a one-critical return
is globally the identity or its canonical involution. A single regular
marked point determines which one. Complete fiber pairings are intrinsic
to the actual return and intertwine under bijective fiber identifications.
No identification of a separately prescribed relative-cover marking is
assumed or established.
-/

namespace LoopsTelescopeDeckRigidity

open Set Function
open QuadraticEscape LoopsSaturatedTelescope LoopsTelescopeRamification
open LoopsTelescopeConformalInverse LoopsTelescopeDeckInvolution

noncomputable section

private theorem analytic_pair_choice_rigid (A : Set ℂ) (hA : IsPreconnected A)
    (f g h : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f A)
    (hg : AnalyticOnNhd ℂ g A) (hh : AnalyticOnNhd ℂ h A)
    (hchoice : ∀ z ∈ A, f z = g z ∨ f z = h z) :
    EqOn f g A ∨ EqOn f h A := by
  have hproduct : ∀ z ∈ A, (f z - g z) * (f z - h z) = 0 := by
    intro z hz
    rcases hchoice z hz with he | he <;> simp [he]
  rcases (hf.sub hg).eq_zero_or_eq_zero_of_mul_eq_zero
      (hf.sub hh) hproduct hA with he | he
  · exact Or.inl (fun z hz => sub_eq_zero.mp (he z hz))
  · exact Or.inr (fun z hz => sub_eq_zero.mp (he z hz))

private theorem one_critical_source_preconnected (c : ℂ) (a : ℕ)
    (A B D : Set ℂ) (hA : IsOpen A)
    (hB : B = connectedComponentIn ((fun w : ℂ => w^2+c) ⁻¹' D) 0)
    (hponto : orbit c a '' A = B) (hpinj : InjOn (orbit c a) A) :
    IsPreconnected A := by
  obtain ⟨g, hgmap, hgleft, _, hga, _⟩ :=
    orbit_conformal_inverse c a A B hA hpinj hponto
  have hBA : g '' B = A := by
    apply Subset.antisymm
    · rintro _ ⟨y, hy, rfl⟩
      exact hgmap hy
    · intro z hz
      refine ⟨orbit c a z, ?_, hgleft hz⟩
      rw [← hponto]
      exact ⟨z, hz, rfl⟩
  have hBc : IsPreconnected B := by
    rw [hB]
    exact isPreconnected_connectedComponentIn
  rw [← hBA]
  exact hBc.image g hga.continuousOn

/-- The complete actual one-critical return has an intrinsic analytic
involution, and its only analytic fiber-preserving self-maps are this
involution and the identity. Injectivity, surjectivity, and involutivity
of a candidate self-map are not hypotheses. Source connectedness follows
from the actual univalent prefix onto its selected critical component. -/
theorem quadratic_return_deck_classification (c : ℂ) (a b : ℕ)
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
      ∀ σ : ℂ → ℂ, AnalyticOnNhd ℂ σ A → MapsTo σ A A →
        (∀ z ∈ A, orbit c (a+1+b) (σ z) = orbit c (a+1+b) z) →
        (EqOn σ id A ∨ EqOn σ τ A) ∧
        (∀ z ∈ A, σ (σ z) = z) ∧ BijOn σ A A := by
  obtain ⟨τ, hτa, hτmap, hτinv, hτprefix, hτfixed, hτfiber, _, _⟩ :=
    quadratic_return_analytic_involution c a b A B D hc hA hB hponto hpinj hrinj
  refine ⟨τ, hτa, hτmap, hτinv, hτprefix, hτfixed, hτfiber, ?_⟩
  intro σ hσa hσmap hσfiber
  have hAc := one_critical_source_preconnected c a A B D hA hB hponto hpinj
  have hchoice : EqOn σ id A ∨ EqOn σ τ A := by
    apply analytic_pair_choice_rigid A hAc σ id τ hσa
      (fun _ _ => analyticAt_id) hτa
    intro z hz
    exact (hτfiber z hz (σ z) (hσmap hz)).mp (hσfiber z hz)
  have hinv : ∀ z ∈ A, σ (σ z) = z := by
    intro z hz
    rcases hchoice with hid | hτ
    · exact (hid (hσmap hz)).trans (hid hz)
    · calc
        σ (σ z) = τ (σ z) := hτ (hσmap hz)
        _ = τ (τ z) := congrArg τ (hτ hz)
        _ = z := hτinv z hz
  refine ⟨hchoice, hinv, hσmap, ?_, ?_⟩
  · intro z hz w hw he
    exact (hinv z hz).symm.trans ((congrArg σ he).trans (hinv w hw))
  · intro z hz
    exact ⟨σ z, hσmap hz, hinv z hz⟩

/-- Agreement at a single regular source mark identifies two analytic
fiber-preserving self-maps on the whole actual return domain. The regular
condition is essential: the identity and the involution agree at the
critical point. No bijectivity assumptions on either map are needed. -/
theorem quadratic_return_deck_marked_unique (c : ℂ) (a b : ℕ)
    (A B D : Set ℂ) (hc : c ∈ D) (hA : IsOpen A)
    (hB : B = connectedComponentIn ((fun w : ℂ => w^2+c) ⁻¹' D) 0)
    (hponto : orbit c a '' A = B)
    (hpinj : InjOn (orbit c a) A) (hrinj : InjOn (orbit c b) D)
    (σ ρ : ℂ → ℂ) (hσa : AnalyticOnNhd ℂ σ A) (hρa : AnalyticOnNhd ℂ ρ A)
    (hσmap : MapsTo σ A A) (hρmap : MapsTo ρ A A)
    (hσfiber : ∀ z ∈ A, orbit c (a+1+b) (σ z) = orbit c (a+1+b) z)
    (hρfiber : ∀ z ∈ A, orbit c (a+1+b) (ρ z) = orbit c (a+1+b) z)
    (x : ℂ) (hx : x ∈ A) (hxreg : orbit c a x ≠ 0) (hmark : σ x = ρ x) :
    EqOn σ ρ A := by
  obtain ⟨τ, _, _, _, _, hτfixed, _, hclass⟩ :=
    quadratic_return_deck_classification c a b A B D hc hA hB hponto hpinj hrinj
  have hτne : τ x ≠ x := fun he => hxreg ((hτfixed x hx).mp he)
  rcases (hclass σ hσa hσmap hσfiber).1 with hσ | hσ <;>
    rcases (hclass ρ hρa hρmap hρfiber).1 with hρ | hρ
  · exact fun z hz => (hσ hz).trans (hρ hz).symm
  · exact (hτne ((hρ hx).symm.trans (hmark.symm.trans (hσ hx)))).elim
  · exact (hτne ((hσ hx).symm.trans (hmark.trans (hρ hx)))).elim
  · exact fun z hz => (hσ hz).trans (hρ hz).symm

/-- Two complete pairings of the fibers of the same actual return
coincide, even if obtained from different stage factorizations or inverse
choices. This is pointwise and does not require analyticity or connectedness. -/
theorem quadratic_return_pairing_unique (c : ℂ) (n : ℕ)
    (A : Set ℂ) (τ ρ : ℂ → ℂ) (hτmap : MapsTo τ A A) (hρmap : MapsTo ρ A A)
    (hτfiber : ∀ z ∈ A, ∀ w ∈ A,
      orbit c n w = orbit c n z ↔ w=z ∨ w=τ z)
    (hρfiber : ∀ z ∈ A, ∀ w ∈ A,
      orbit c n w = orbit c n z ↔ w=z ∨ w=ρ z) :
    EqOn τ ρ A := by
  intro z hz
  have hτR : orbit c n (τ z) = orbit c n z :=
    (hτfiber z hz (τ z) (hτmap hz)).mpr (Or.inr rfl)
  rcases (hρfiber z hz (τ z) (hτmap hz)).mp hτR with he | he
  · have hρR : orbit c n (ρ z) = orbit c n z :=
      (hρfiber z hz (ρ z) (hρmap hz)).mpr (Or.inr rfl)
    rcases (hτfiber z hz (ρ z) (hρmap hz)).mp hρR with hr | hr
    · exact he.trans hr.symm
    · exact hr.symm
  · exact he

/-- A bijection of actual return sources which identifies precisely
their complete fibers automatically transports the canonical pairing,
including the critical singleton fiber. A target-coordinate conjugacy
with an injective target map supplies the fiber equivalence hypothesis. -/
theorem quadratic_return_pairing_conjugacy (c d : ℂ) (n m : ℕ)
    (A E : Set ℂ) (τ ρ h : ℂ → ℂ)
    (hτmap : MapsTo τ A A) (hρmap : MapsTo ρ E E)
    (hτfiber : ∀ z ∈ A, ∀ w ∈ A,
      orbit c n w = orbit c n z ↔ w=z ∨ w=τ z)
    (hρfiber : ∀ z ∈ E, ∀ w ∈ E,
      orbit d m w = orbit d m z ↔ w=z ∨ w=ρ z)
    (hh : BijOn h A E)
    (hidentify : ∀ z ∈ A, ∀ w ∈ A,
      orbit c n w = orbit c n z ↔ orbit d m (h w) = orbit d m (h z)) :
    ∀ z ∈ A, h (τ z) = ρ (h z) := by
  intro z hz
  have hzE : h z ∈ E := hh.mapsTo hz
  have hτR : orbit c n (τ z) = orbit c n z :=
    (hτfiber z hz (τ z) (hτmap hz)).mpr (Or.inr rfl)
  have hpair := (hρfiber (h z) hzE (h (τ z)) (hh.mapsTo (hτmap hz))).mp
    ((hidentify z hz (τ z) (hτmap hz)).mp hτR)
  rcases hpair with he | he
  · obtain ⟨w, hw, hwe⟩ := hh.surjOn (hρmap hzE)
    have hwR : orbit d m (h w) = orbit d m (h z) := by
      rw [hwe]
      exact (hρfiber (h z) hzE (ρ (h z)) (hρmap hzE)).mpr (Or.inr rfl)
    have hwpre := (hidentify z hz w hw).mpr hwR
    rcases (hτfiber z hz w hw).mp hwpre with hwz | hwτ
    · rw [hwz] at hwe
      exact he.trans hwe
    · rw [hwτ] at hwe
      exact hwe
  · exact he

end

end LoopsTelescopeDeckRigidity

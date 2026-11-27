import TelescopeUnbranchedCover
import Mathlib.Analysis.Complex.BranchLogRoot
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Convex.Topology
import Mathlib.Topology.Order.ProjIcc

/-!
# Continuous physical return lifts through arbitrary critical encounters

The regular-time components choose independent square-root branches. At
every zero, including an accumulation point of regular excursions, their
norm tends to zero. Pulling this construction through the actual univalent
suffix and prefix produces a continuous lift in the full selected return
component for every continuous target path and every initial inverse point.
-/

namespace LoopsTelescopeCriticalLift

open Set Function Filter
open scoped Topology
open QuadraticEscape LoopsSaturatedTelescope LoopsTelescopeRamification
open LoopsTelescopeCollar LoopsTelescopeConformalInverse
open LoopsTelescopeUnbranchedCover

noncomputable section

/-- Roots are selected by the actual connected component of nonzero
times. No finiteness or isolation of the zero set is required. -/
theorem real_path_continuous_square_root (g : ℝ → ℂ) (hg : Continuous g) :
    ∃ r : ℝ → ℂ, Continuous r ∧ ∀ t, (r t)^2 = g t := by
  classical
  let R : Set ℝ := {t | g t ≠ 0}
  have hRo : IsOpen R := (isClosed_eq hg continuous_const).isOpen_compl
  let Components := {U : Set ℝ // ∃ t ∈ R, U = connectedComponentIn R t}
  have hex (U : Components) :
      ∃ r : ℝ → ℂ, ContinuousOn r (U : Set ℝ) ∧ ∀ t, (r t)^2 = g t := by
    obtain ⟨t, ht, hU⟩ := U.property
    have hUo : IsOpen (U : Set ℝ) := by
      rw [hU]
      exact hRo.connectedComponentIn
    have hUc : IsPreconnected (U : Set ℝ) := by
      rw [hU]
      exact isPreconnected_connectedComponentIn
    have hUn : (U : Set ℝ).Nonempty := by
      rw [hU]
      exact ⟨t, mem_connectedComponentIn ht⟩
    have hUR : (U : Set ℝ) ⊆ R := by
      rw [hU]
      exact connectedComponentIn_subset R t
    letI : ContractibleSpace (U : Set ℝ) := hUc.convex.contractibleSpace hUn
    have hUs : IsSimplyConnected (U : Set ℝ) := by
      change SimplyConnectedSpace (U : Set ℝ)
      infer_instance
    have hUzero : 0 ∉ g '' (U : Set ℝ) := by
      rintro ⟨y, hy, hgy⟩
      exact hUR hy hgy
    exact Complex.exists_continuousOn_pow_eq hUs hUo hg.continuousOn hUzero
      (n := 2) (by decide)
  choose root hroot_cont hroot_pow using hex
  let index (t : ℝ) (ht : t ∈ R) : Components :=
    ⟨connectedComponentIn R t, t, ht, rfl⟩
  let r : ℝ → ℂ := fun t => if ht : t ∈ R then root (index t ht) t else 0
  have hrpow (t : ℝ) : (r t)^2 = g t := by
    by_cases ht : t ∈ R
    · simpa only [r, dif_pos ht] using hroot_pow (index t ht) t
    · have hgt : g t = 0 := by
        by_contra hn
        exact ht hn
      simp only [r, dif_neg ht, zero_pow (by decide : 2 ≠ 0), hgt]
  have hrnorm (t : ℝ) : ‖r t‖ = Real.sqrt ‖g t‖ := by
    calc
      ‖r t‖ = Real.sqrt (‖r t‖^2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ = Real.sqrt ‖g t‖ := by rw [← norm_pow, hrpow t]
  refine ⟨r, continuous_iff_continuousAt.mpr ?_, hrpow⟩
  intro t
  by_cases ht : t ∈ R
  · let U : Components := index t ht
    have htU : t ∈ (U : Set ℝ) := mem_connectedComponentIn ht
    have hUo : IsOpen (U : Set ℝ) := hRo.connectedComponentIn
    apply ((hroot_cont U).continuousAt (hUo.mem_nhds htU)).congr_of_eventuallyEq
    filter_upwards [hUo.mem_nhds htU] with y hy
    change y ∈ connectedComponentIn R t at hy
    have hyR : y ∈ R := connectedComponentIn_subset R t hy
    have hindex : index y hyR = U := by
      apply Subtype.ext
      exact (connectedComponentIn_eq hy).symm
    change (if hy : y ∈ R then root (index y hy) y else 0) = root U y
    rw [dif_pos hyR, hindex]
  · have hgt : g t = 0 := by
      by_contra hn
      exact ht hn
    have hrt : r t = 0 := by simp only [r, dif_neg ht]
    change Tendsto r (𝓝 t) (𝓝 (r t))
    rw [hrt]
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have hc : Continuous (fun y => Real.sqrt ‖g y‖) :=
      Real.continuous_sqrt.comp hg.norm
    simpa only [hrnorm, hgt, norm_zero, Real.sqrt_zero] using
      (hc.continuousAt (x := t)).tendsto

/-- Every continuous complex path has a continuous square root with any
prescribed initial root, including paths with arbitrary zero sets. -/
theorem interval_path_continuous_square_root (γ : C(unitInterval, ℂ))
    (z : ℂ) (hz : z^2 = γ 0) :
    ∃ r : C(unitInterval, ℂ), (∀ t, (r t)^2 = γ t) ∧ r 0 = z := by
  let e : ℝ → ℂ := fun t => γ (Set.projIcc 0 1 (by norm_num) t)
  have he : Continuous e := γ.continuous.comp continuous_projIcc
  obtain ⟨r, hrcont, hrpow⟩ := real_path_continuous_square_root e he
  let ρ : C(unitInterval, ℂ) :=
    ⟨fun t => r (t : ℝ), hrcont.comp continuous_subtype_val⟩
  have hρpow (t : unitInterval) : (ρ t)^2 = γ t := by
    simpa [ρ, e] using hrpow (t : ℝ)
  have hprod : (ρ 0-z)*(ρ 0+z)=0 := by
    linear_combination (hρpow 0) - hz
  rcases mul_eq_zero.mp hprod with h | h
  · exact ⟨ρ, hρpow, sub_eq_zero.mp h⟩
  · let σ : C(unitInterval, ℂ) := ⟨fun t => -(ρ t), ρ.continuous.neg⟩
    refine ⟨σ, ?_, ?_⟩
    · intro t
      simpa [σ] using hρpow t
    · change -(ρ 0) = z
      linear_combination -h

/-- Every continuous target path in an actual saturated one-critical
return has a continuous lift in the entire selected source for each
specified starting inverse point. Critical encounters may accumulate;
neither avoiding the critical value nor a finite partition is assumed. -/
theorem quadratic_return_path_lift_with_critical_crossings (c : ℂ) (a b : ℕ)
    (A B D V : Set ℂ) (x : ℂ) (hx0 : orbit c a x = 0)
    (hVo : IsOpen V) (hVc : IsPreconnected V) (hv : orbit c b c ∈ V)
    (hD : D = connectedComponentIn (orbit c b ⁻¹' V) c)
    (hB : B = connectedComponentIn ((fun w : ℂ => w^2+c) ⁻¹' D) 0)
    (hA : A = connectedComponentIn (orbit c a ⁻¹' B) x)
    (hpinj : InjOn (orbit c a) A) (hrinj : InjOn (orbit c b) D)
    (γ : C(unitInterval, ℂ)) (hγV : ∀ t, γ t ∈ V)
    (z : ℂ) (hz : z ∈ A) (hzγ : orbit c (a+1+b) z = γ 0) :
    ∃ Γ : C(unitInterval, ℂ),
      (∀ t, Γ t ∈ A) ∧ (∀ t, orbit c (a+1+b) (Γ t) = γ t) ∧ Γ 0 = z := by
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
  have hDr : orbit c b '' D = V := by
    rw [hD]
    exact orbit_component_image c b V hVo hVc c hv
  obtain ⟨p, hpmap, hpleft, hpright, hpa, _⟩ :=
    orbit_conformal_inverse c a A B hAo hpinj hAp
  obtain ⟨s, hsmap, hsleft, hsright, hsa, _⟩ :=
    orbit_conformal_inverse c b D V hDo hrinj hDr
  let β : C(unitInterval, ℂ) :=
    ⟨fun t => s (γ t)-c,
      (hsa.continuousOn.comp_continuous γ.continuous hγV).sub continuous_const⟩
  have hpz : orbit c a z ∈ B := by
    rw [← hAp]
    exact ⟨z, hz, rfl⟩
  have hqz : (orbit c a z)^2+c ∈ D := by
    rw [hB] at hpz
    exact connectedComponentIn_subset ((fun w : ℂ => w^2+c) ⁻¹' D) 0 hpz
  have hβ0 : (orbit c a z)^2 = β 0 := by
    change (orbit c a z)^2 = s (γ 0)-c
    rw [← hzγ, quadratic_orbit_add c (a+1) b z]
    change (orbit c a z)^2 = s (orbit c b ((orbit c a z)^2+c))-c
    rw [hsleft hqz]
    ring
  obtain ⟨δ, hδpow, hδ0⟩ := interval_path_continuous_square_root β (orbit c a z) hβ0
  let W := (fun w : ℂ => w^2+c) ⁻¹' D
  have hδW : Set.range δ ⊆ W := by
    rintro _ ⟨t, rfl⟩
    change (δ t)^2+c ∈ D
    rw [hδpow t]
    simpa [β] using hsmap (hγV t)
  have hcomponent : connectedComponentIn W (orbit c a z) = B := by
    have hmem : orbit c a z ∈ connectedComponentIn W 0 := by
      rw [← hB]
      exact hpz
    exact (connectedComponentIn_eq hmem).symm.trans hB.symm
  have hδB (t : unitInterval) : δ t ∈ B := by
    rw [← hcomponent]
    exact (isPreconnected_range δ.continuous).subset_connectedComponentIn
      ⟨0, hδ0⟩ hδW ⟨t, rfl⟩
  let Γ : C(unitInterval, ℂ) :=
    ⟨fun t => p (δ t), hpa.continuousOn.comp_continuous δ.continuous hδB⟩
  refine ⟨Γ, fun t => hpmap (hδB t), ?_, ?_⟩
  · intro t
    rw [quadratic_orbit_add c (a+1) b (Γ t)]
    change orbit c b ((orbit c a (p (δ t)))^2+c) = γ t
    rw [hpright (hδB t), hδpow t]
    change orbit c b ((s (γ t)-c)+c) = γ t
    rw [sub_add_cancel]
    exact hsright (hγV t)
  · change p (δ 0) = z
    rw [hδ0]
    exact hpleft hz

end

end LoopsTelescopeCriticalLift

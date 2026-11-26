import TelescopeUnivalentCollars

/-!
# Constructing an open one-critical return from compact actual cores

The compact cores are selected components of the actual quadratic pullbacks.
Injectivity and absence of critical encounters are imposed only on the
compact prefix and suffix cores. A single open connected target then yields
compatible open stages, injective prefix and suffix, and a proper full return
of total analytic multiplicity two. No Jordan-curve or simple-connectivity
claim is made about these constructed open sets.
-/

namespace LoopsTelescopeCompactReturn

open Set Function Metric
open scoped BigOperators
open QuadraticEscape LoopsSaturatedTelescope LoopsTelescopeRamification
open LoopsTelescopeCollar LoopsTelescopeUnivalentCollars
open LoopsQuadraticCylinderCensus

/-- Compact conditions on the actual prefix and suffix cores produce
compatible open stages and a full return of total analytic multiplicity two.
The two univalent stages remain injective on their compact closures and
can be confined to prescribed ambient neighborhoods. -/
theorem compact_one_critical_return_collar (c : ℂ) (a b : ℕ)
    (K A0 B0 D0 WA WD : Set ℂ) (x : ℂ)
    (hK : IsCompact K) (hKconn : IsPreconnected K)
    (hx0 : orbit c a x = 0) (hv : orbit c b c ∈ K)
    (hD0 : D0 = connectedComponentIn (orbit c b ⁻¹' K) c)
    (hB0 : B0 = connectedComponentIn ((fun w : ℂ => w^2+c) ⁻¹' D0) 0)
    (hA0 : A0 = connectedComponentIn (orbit c a ⁻¹' B0) x)
    (hWA : IsOpen WA) (hAWA : A0 ⊆ WA)
    (hWD : IsOpen WD) (hDWD : D0 ⊆ WD)
    (hpinj : InjOn (orbit c a) A0)
    (hpcrit : ∀ z ∈ A0, ∀ j < a, orbit c j z ≠ 0)
    (hrinj : InjOn (orbit c b) D0)
    (hrcrit : ∀ z ∈ D0, ∀ j < b, orbit c j z ≠ 0) :
    ∃ V : Set ℂ, IsOpen V ∧ IsPreconnected V ∧ K ⊆ V ∧
      let D := connectedComponentIn (orbit c b ⁻¹' V) c
      let B := connectedComponentIn ((fun w : ℂ => w^2+c) ⁻¹' D) 0
      let A := connectedComponentIn (orbit c a ⁻¹' B) x
      IsOpen A ∧ IsOpen B ∧ IsOpen D ∧
      A0 ⊆ A ∧ B0 ⊆ B ∧ D0 ⊆ D ∧
      IsCompact (closure A) ∧ closure A ⊆ WA ∧
      IsCompact (closure B) ∧ IsCompact (closure D) ∧ closure D ⊆ WD ∧
      InjOn (orbit c a) (closure A) ∧ InjOn (orbit c b) (closure D) ∧
      A = connectedComponentIn (orbit c (a+1+b) ⁻¹' V) x ∧
      orbit c (a+1+b) '' A = V ∧
      (∃ hmap : MapsTo (orbit c (a+1+b)) A V,
        IsProperMap (MapsTo.restrict (orbit c (a+1+b)) A V hmap)) ∧
      (∀ L : Set ℂ, IsCompact L → L ⊆ V →
        IsCompact (A ∩ orbit c (a+1+b) ⁻¹' L)) ∧
      ∀ v ∈ V, (∑ z ∈ localFiber c (a+1+b) A v,
        analyticOrderNatAt (fun w => orbit c (a+1+b) w-v) z) = 2 := by
  let q : ℂ → ℂ := fun w => w^2+c
  have hpq : IsProperMap q := orbit_proper c 1
  have hcD0 : c ∈ D0 := by
    rw [hD0]
    exact mem_connectedComponentIn hv
  have hD0c : IsCompact D0 := by
    rw [hD0]
    exact proper_component_compact (orbit c b) (orbit_proper c b) K hK c hv
  have hq0 : q 0 ∈ D0 := by simpa [q] using hcD0
  have h0B0 : (0 : ℂ) ∈ B0 := by
    rw [hB0]
    exact mem_connectedComponentIn hq0
  have hB0c : IsCompact B0 := by
    rw [hB0]
    exact proper_component_compact q hpq D0 hD0c 0 hq0
  have hxB0 : orbit c a x ∈ B0 := hx0.symm ▸ h0B0
  obtain ⟨δA, hδA, hmarginA⟩ :=
    selected_univalent_collar_margin c a B0 WA x hB0c hxB0 hWA
      (hA0 ▸ hAWA) (hA0 ▸ hpinj) (hA0 ▸ hpcrit)
  obtain ⟨δB, hδB, hmarginB⟩ :=
    proper_component_upper_semicontinuous q hpq D0 hD0c 0 hq0
      (thickening δA B0) isOpen_thickening
      (by
        change connectedComponentIn ((fun w : ℂ => w^2+c) ⁻¹' D0) 0 ⊆
          thickening δA B0
        rw [← hB0]
        exact self_subset_thickening hδA B0)
  have hDambient : D0 ⊆ WD ∩ thickening δB D0 :=
    fun z hz => ⟨hDWD hz, self_subset_thickening hδB D0 hz⟩
  obtain ⟨δ, hδ, hmarginD⟩ :=
    selected_univalent_collar_margin c b K (WD ∩ thickening δB D0) c hK hv
      (hWD.inter isOpen_thickening) (by simpa only [← hD0] using hDambient)
      (hD0 ▸ hrinj) (hD0 ▸ hrcrit)
  obtain ⟨V, hV, hVconn, hKV, hVnear⟩ :=
    connected_open_target_neighborhood K hKconn (orbit c b c) hv δ hδ
  let D := connectedComponentIn (orbit c b ⁻¹' V) c
  let B := connectedComponentIn (q ⁻¹' D) 0
  let A := connectedComponentIn (orbit c a ⁻¹' B) x
  obtain ⟨hDo, hDcore, hDc, hDsub, hDI⟩ := hmarginD V hV hKV hVnear
  have hD0D : D0 ⊆ D := hD0.symm ▸ hDcore
  have hDnear : D ⊆ cthickening δB D0 := by
    intro z hz
    exact thickening_subset_cthickening δB D0 (hDsub (subset_closure hz)).2
  have hBo : IsOpen B := (hDo.preimage hpq.continuous).connectedComponentIn
  have hB0B : B0 ⊆ B := by
    rw [hB0]
    exact connectedComponentIn_mono 0 (preimage_mono hD0D)
  have hBnear : B ⊆ cthickening δA B0 :=
    (hmarginB D hDnear).trans (thickening_subset_cthickening δA B0)
  obtain ⟨hAo, hAcore, hAc, hAsub, hAI⟩ := hmarginA B hBo hB0B hBnear
  have hA0A : A0 ⊆ A := hA0.symm ▸ hAcore
  have hBc : IsCompact (closure B) := by
    apply (hpq.isCompact_preimage hDc).of_isClosed_subset isClosed_closure
    apply closure_minimal _ (isClosed_closure.preimage hpq.continuous)
    intro z hz
    exact subset_closure (connectedComponentIn_subset _ _ hz)
  obtain ⟨hsat, honto, hproper, hdegree⟩ :=
    selected_saturated_return_full_degree c a b A B D V x hx0 hV hVconn
      (hKV hv) rfl rfl rfl (hAI.mono subset_closure) (hDI.mono subset_closure)
  have hproperMap : ∃ hmap : MapsTo (orbit c (a+1+b)) A V,
      IsProperMap (MapsTo.restrict (orbit c (a+1+b)) A V hmap) := by
    rw [hsat]
    refine ⟨fun z hz => connectedComponentIn_subset _ _ hz, ?_⟩
    exact orbit_component_proper c (a+1+b) V x hV
  exact ⟨V, hV, hVconn, hKV, hAo, hBo, hDo, hA0A, hB0B, hD0D,
    hAc, hAsub, hBc, hDc, fun z hz => (hDsub hz).1,
    hAI, hDI, hsat, honto, hproperMap, hproper, hdegree⟩

/-- If the compact return core is already inside the interior of the
compact target, the constructed proper degree-two return is compactly
contained in its open connected target. Simple connectivity of the open
sets remains a separate question. The interior-containment hypothesis
is additional; in particular, it is not supplied by an empty-interior target. -/
theorem compactly_contained_one_critical_return (c : ℂ) (a b : ℕ)
    (K A0 B0 D0 : Set ℂ) (x : ℂ)
    (hK : IsCompact K) (hKconn : IsPreconnected K)
    (hx0 : orbit c a x = 0) (hv : orbit c b c ∈ K)
    (hD0 : D0 = connectedComponentIn (orbit c b ⁻¹' K) c)
    (hB0 : B0 = connectedComponentIn ((fun w : ℂ => w^2+c) ⁻¹' D0) 0)
    (hA0 : A0 = connectedComponentIn (orbit c a ⁻¹' B0) x)
    (hAint : A0 ⊆ interior K)
    (hpinj : InjOn (orbit c a) A0)
    (hpcrit : ∀ z ∈ A0, ∀ j < a, orbit c j z ≠ 0)
    (hrinj : InjOn (orbit c b) D0)
    (hrcrit : ∀ z ∈ D0, ∀ j < b, orbit c j z ≠ 0) :
    ∃ V A : Set ℂ, IsOpen V ∧ IsPreconnected V ∧ K ⊆ V ∧
      IsOpen A ∧ IsPreconnected A ∧ A0 ⊆ A ∧
      A = connectedComponentIn (orbit c (a+1+b) ⁻¹' V) x ∧
      IsCompact (closure A) ∧ closure A ⊆ V ∧
      orbit c (a+1+b) '' A = V ∧
      (∃ hmap : MapsTo (orbit c (a+1+b)) A V,
        IsProperMap (MapsTo.restrict (orbit c (a+1+b)) A V hmap)) ∧
      (∀ L : Set ℂ, IsCompact L → L ⊆ V →
        IsCompact (A ∩ orbit c (a+1+b) ⁻¹' L)) ∧
      ∀ v ∈ V, (∑ z ∈ localFiber c (a+1+b) A v,
        analyticOrderNatAt (fun w => orbit c (a+1+b) w-v) z) = 2 := by
  obtain ⟨V, hV, hVc, hKV, hAo, _, _, hA0A, _, _, hAc, hAsub,
      _, _, _, _, _, hsat, honto, hproperMap, hproper, hdegree⟩ :=
    compact_one_critical_return_collar c a b K A0 B0 D0 (interior K) univ x
      hK hKconn hx0 hv hD0 hB0 hA0 isOpen_interior hAint
      isOpen_univ (subset_univ D0) hpinj hpcrit hrinj hrcrit
  let D := connectedComponentIn (orbit c b ⁻¹' V) c
  let B := connectedComponentIn ((fun w : ℂ => w^2+c) ⁻¹' D) 0
  let A := connectedComponentIn (orbit c a ⁻¹' B) x
  exact ⟨V, A, hV, hVc, hKV, hAo, isPreconnected_connectedComponentIn,
    hA0A, hsat, hAc, hAsub.trans (interior_subset.trans hKV),
    honto, hproperMap, hproper, hdegree⟩

end LoopsTelescopeCompactReturn

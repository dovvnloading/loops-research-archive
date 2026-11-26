import QuadraticCriticalTrapping
import QuadraticInverseOpen

/-!
# Parameter-stable proper returns across one actual critical step

Compact injective prefix and suffix cores construct one fixed open terminal
target and a parameter neighborhood. The entire moving middle quadratic
pullback is trapped in the prefix inverse collar. The moving critical value
is retained by continuity, and the assembled return is the full physical
pullback component with total analytic multiplicity two at every target.
-/

namespace LoopsTelescopeParameterReturn

open Set Function
open scoped BigOperators
open QuadraticEscape LoopsSaturatedTelescope LoopsTelescopeRamification
open LoopsTelescopeCollar LoopsTelescopeUnivalentCollars
open LoopsQuadraticCylinderCensus LoopsQuadraticParameterInverse
open LoopsQuadraticCriticalTrapping LoopsQuadraticInverseOpen

noncomputable section

/-- Compact actual one-critical data construct a common terminal target
and a parameter family of complete proper degree-two returns. Trapping of
the full middle pullback and retention of the moving critical value are
conclusions. The common source closures remain inside prescribed ambient
neighborhoods. -/
theorem quadratic_parameter_one_critical_return
    (c : ℂ) (a b : ℕ) (K A0 B0 D0 WA WD : Set ℂ) (x : ℂ)
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
    ∃ (P V : Set ℂ) (ξ : ℂ → ℂ),
      IsOpen P ∧ c ∈ P ∧ IsOpen V ∧ IsPreconnected V ∧ K ⊆ V ∧
      IsCompact (closure V) ∧ AnalyticOnNhd ℂ ξ P ∧ ξ c = x ∧
      ∀ d ∈ P, orbit d a (ξ d) = 0 ∧ orbit d b d ∈ V ∧
        let D := connectedComponentIn (orbit d b ⁻¹' V) d
        let B := connectedComponentIn ((fun w : ℂ => w^2+d) ⁻¹' D) 0
        let A := connectedComponentIn (orbit d a ⁻¹' B) (ξ d)
        IsOpen A ∧ IsOpen B ∧ IsOpen D ∧
        IsCompact (closure A) ∧ closure A ⊆ WA ∧
        IsCompact (closure B) ∧ IsCompact (closure D) ∧ closure D ⊆ WD ∧
        B = (fun w : ℂ => w^2+d) ⁻¹' D ∧
        InjOn (orbit d a) (closure A) ∧ InjOn (orbit d b) (closure D) ∧
        A = connectedComponentIn (orbit d (a+1+b) ⁻¹' V) (ξ d) ∧
        orbit d (a+1+b) '' A = V ∧
        (∃ hmap : MapsTo (orbit d (a+1+b)) A V,
          IsProperMap (MapsTo.restrict (orbit d (a+1+b)) A V hmap)) ∧
        (∀ L : Set ℂ, IsCompact L → L ⊆ V →
          IsCompact (A ∩ orbit d (a+1+b) ⁻¹' L)) ∧
        ∀ v ∈ V, (∑ z ∈ localFiber d (a+1+b) A v,
          analyticOrderNatAt (fun w => orbit d (a+1+b) w-v) z) = 2 := by
  have hcD0 : c ∈ D0 := by
    rw [hD0]
    exact mem_connectedComponentIn hv
  have hD0conn : IsPreconnected D0 := by
    rw [hD0]
    exact isPreconnected_connectedComponentIn
  have hD0compact : IsCompact D0 := by
    rw [hD0]
    exact proper_component_compact (orbit c b) (orbit_proper c b) K hK c hv
  have h0B0 : (0 : ℂ) ∈ B0 := by
    rw [hB0]
    exact mem_connectedComponentIn (by simpa using hcD0)
  have hB0conn : IsPreconnected B0 := by
    rw [hB0]
    exact isPreconnected_connectedComponentIn
  have hB0compact : IsCompact B0 := by
    rw [hB0]
    exact proper_component_compact (fun w : ℂ => w^2+c) (orbit_proper c 1)
      D0 hD0compact 0 (by simpa using hcD0)
  have hxB0 : orbit c a x ∈ B0 := hx0.symm ▸ h0B0
  have hxA0 : x ∈ A0 := by
    rw [hA0]
    exact mem_connectedComponentIn hxB0
  have hA0compact : IsCompact A0 := by
    rw [hA0]
    exact proper_component_compact (orbit c a) (orbit_proper c a)
      B0 hB0compact x hxB0
  have hpimage : orbit c a '' A0 = B0 := by
    rw [hA0]
    exact quadratic_compact_component_image c a B0 x hB0compact hB0conn hxB0
      (hA0 ▸ hpinj) (hA0 ▸ hpcrit)
  have hsimage : orbit c b '' D0 = K := by
    rw [hD0]
    exact quadratic_compact_component_image c b K c hK hKconn hv
      (hD0 ▸ hrinj) (hD0 ▸ hrcrit)
  obtain ⟨Pp, Up, Vp, gp, hPp, hcPp, hUp, hAUp, hUpcompact, hUpWA,
      hVp, hpVp, hgpa, hgpbranch, hgpbase, hgpder⟩ :=
    quadratic_compact_parameter_inverse_family c a A0 WA hA0compact hWA hAWA
      hpinj hpcrit
  have hB0Vp : B0 ⊆ Vp := by
    rw [← hpimage]
    exact hpVp
  have h0Vp : (0 : ℂ) ∈ Vp := hB0Vp h0B0
  have hB0full : B0 = (fun w : ℂ => w^2+c) ⁻¹' D0 := by
    rw [hB0]
    exact quadratic_critical_component_eq_preimage c D0 hD0conn hcD0
  obtain ⟨Pt, Vt, hPt, hcPt, hVt, hD0Vt, htrap⟩ :=
    quadratic_full_preimage_parameter_neighborhood c D0 Vp hD0compact hVp
      (by rw [← hB0full]; exact hB0Vp)
  obtain ⟨Ps, Us, Vs, gs, hPs, hcPs, hUs, hDUs, hUscompact, hUsambient,
      hVs, hsVs, hgsa, hgsbranch, hgsbase, hgsder⟩ :=
    quadratic_compact_parameter_inverse_family c b D0 (WD ∩ Vt) hD0compact
      (hWD.inter hVt) (fun z hz => ⟨hDWD hz, hD0Vt hz⟩) hrinj hrcrit
  have hKVs : K ⊆ Vs := by
    rw [← hsimage]
    exact hsVs
  obtain ⟨V, hV, hVconn, hKV, hVcompact, hclV⟩ :=
    connected_precompact_target_neighborhood K Vs hK hKconn (orbit c b c) hv
      hVs hKVs
  have hcriticalContinuous : Continuous (fun d : ℂ => orbit d b d) :=
    (orbit_continuous b).comp (continuous_id.prodMk continuous_id)
  let P : Set ℂ := Pp ∩ (Pt ∩ (Ps ∩ (Us ∩ (fun d : ℂ => orbit d b d) ⁻¹' V)))
  have hP : IsOpen P :=
    hPp.inter (hPt.inter (hPs.inter (hUs.inter (hV.preimage hcriticalContinuous))))
  have hcP : c ∈ P := ⟨hcPp, hcPt, hcPs, hDUs hcD0, hKV hv⟩
  let ξ : ℂ → ℂ := fun d => gp d 0
  have hξ : AnalyticOnNhd ℂ ξ P := by
    intro d hd
    exact (hgpa (d, 0) ⟨hd.1, h0Vp⟩).comp
      (f := fun e : ℂ => (e, (0 : ℂ))) (x := d)
      (analyticAt_id.prod analyticAt_const)
  have hξc : ξ c = x := by
    change gp c 0 = x
    rw [← hx0]
    exact (hgpbranch c hcPp).2.1 (hAUp hxA0)
  refine ⟨P, V, ξ, hP, hcP, hV, hVconn, hKV, hVcompact, hξ, hξc, ?_⟩
  intro d hd
  have hdp : d ∈ Pp := hd.1
  have hdt : d ∈ Pt := hd.2.1
  have hds : d ∈ Ps := hd.2.2.1
  have hdUs : d ∈ Us := hd.2.2.2.1
  have hdV : orbit d b d ∈ V := hd.2.2.2.2
  have hξzero : orbit d a (ξ d) = 0 := (hgpbranch d hdp).2.2 h0Vp
  refine ⟨hξzero, hdV, ?_⟩
  let D := connectedComponentIn (orbit d b ⁻¹' V) d
  let B := connectedComponentIn ((fun w : ℂ => w^2+d) ⁻¹' D) 0
  let A := connectedComponentIn (orbit d a ⁻¹' B) (ξ d)
  have hgscont : ContinuousOn (gs d) Vs := by
    intro y hy
    have hsana : AnalyticAt ℂ (gs d) y :=
      (hgsa (d, y) ⟨hds, hy⟩).comp
        (f := fun w : ℂ => (d, w)) (x := y)
        (analyticAt_const.prod analyticAt_id)
    exact hsana.continuousAt.continuousWithinAt
  have hanchor : gs d (orbit d b d) = d := (hgsbranch d hds).2.1 hdUs
  obtain ⟨hDimage, hDopen, hDconn, hDcompact, hDclosure, hDonto, hDI⟩ :=
    quadratic_inverse_open_component d b Us Vs V (gs d) hUs hV hVconn
      hVcompact hclV hgscont (hgsbranch d hds).1
      (hgsbranch d hds).2.1 (hgsbranch d hds).2.2 (orbit d b d) hdV
  have hDimage' : gs d '' V = D := by
    simpa only [D, hanchor] using hDimage
  have hDo : IsOpen D := by simpa only [hDimage'] using hDopen
  have hDc : IsCompact (closure D) := by simpa only [hDimage'] using hDcompact
  have hDclUs : closure D ⊆ Us := by simpa only [hDimage'] using hDclosure
  have hDinj : InjOn (orbit d b) (closure D) := by
    simpa only [hDimage'] using hDI
  have hDWD : closure D ⊆ WD := fun z hz =>
    (hUsambient (subset_closure (hDclUs hz))).1
  have hDVt : closure D ⊆ Vt := fun z hz =>
    (hUsambient (subset_closure (hDclUs hz))).2
  have hdD : d ∈ D := mem_connectedComponentIn hdV
  have hDpreconn : IsPreconnected D := isPreconnected_connectedComponentIn
  have hBfull : B = (fun w : ℂ => w^2+d) ⁻¹' D :=
    quadratic_critical_component_eq_preimage d D hDpreconn hdD
  have hqproper : IsProperMap (fun w : ℂ => w^2+d) := orbit_proper d 1
  have hBo : IsOpen B := (hDo.preimage hqproper.continuous).connectedComponentIn
  have hBconn : IsPreconnected B := isPreconnected_connectedComponentIn
  have h0B : (0 : ℂ) ∈ B := mem_connectedComponentIn (by simpa using hdD)
  have hBclpre : closure B ⊆ (fun w : ℂ => w^2+d) ⁻¹' closure D := by
    apply closure_minimal _ (isClosed_closure.preimage hqproper.continuous)
    intro z hz
    exact subset_closure (connectedComponentIn_subset
      ((fun w : ℂ => w^2+d) ⁻¹' D) 0 hz)
  have hBc : IsCompact (closure B) :=
    (hqproper.isCompact_preimage hDc).of_isClosed_subset isClosed_closure hBclpre
  have hBclVp : closure B ⊆ Vp := fun z hz => htrap d hdt (hDVt (hBclpre hz))
  have hgpcont : ContinuousOn (gp d) Vp := by
    intro y hy
    have hpana : AnalyticAt ℂ (gp d) y :=
      (hgpa (d, y) ⟨hdp, hy⟩).comp
        (f := fun w : ℂ => (d, w)) (x := y)
        (analyticAt_const.prod analyticAt_id)
    exact hpana.continuousAt.continuousWithinAt
  obtain ⟨hAimage, hAopen, hAconn, hAcompact, hAclosure, hAonto, hAI⟩ :=
    quadratic_inverse_open_component d a Up Vp B (gp d) hUp hBo hBconn
      hBc hBclVp hgpcont (hgpbranch d hdp).1
      (hgpbranch d hdp).2.1 (hgpbranch d hdp).2.2 0 h0B
  have hAimage' : gp d '' B = A := hAimage
  have hAo : IsOpen A := by simpa only [hAimage'] using hAopen
  have hAc : IsCompact (closure A) := by simpa only [hAimage'] using hAcompact
  have hAclUp : closure A ⊆ Up := by simpa only [hAimage'] using hAclosure
  have hAinj : InjOn (orbit d a) (closure A) := by
    simpa only [hAimage'] using hAI
  have hAWA' : closure A ⊆ WA := fun z hz =>
    hUpWA (subset_closure (hAclUp hz))
  obtain ⟨hsat, honto, hproper, hdegree⟩ :=
    selected_saturated_return_full_degree d a b A B D V (ξ d) hξzero hV hVconn
      hdV rfl rfl rfl (hAinj.mono subset_closure) (hDinj.mono subset_closure)
  have hproperMap : ∃ hmap : MapsTo (orbit d (a+1+b)) A V,
      IsProperMap (MapsTo.restrict (orbit d (a+1+b)) A V hmap) := by
    rw [hsat]
    refine ⟨fun z hz =>
      connectedComponentIn_subset (orbit d (a+1+b) ⁻¹' V) (ξ d) hz, ?_⟩
    exact orbit_component_proper d (a+1+b) V (ξ d) hV
  exact ⟨hAo, hBo, hDo, hAc, hAWA', hBc, hDc, hDWD, hBfull,
    hAinj, hDinj, hsat, honto, hproperMap, hproper, hdegree⟩

/-- If the original compact prefix lies in the interior of the compact
terminal target, the constructed returns remain compactly contained in one
fixed target throughout an open parameter neighborhood. -/
theorem quadratic_parameter_compactly_contained_return
    (c : ℂ) (a b : ℕ) (K A0 B0 D0 : Set ℂ) (x : ℂ)
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
    ∃ (P V : Set ℂ) (ξ : ℂ → ℂ),
      IsOpen P ∧ c ∈ P ∧ IsOpen V ∧ IsPreconnected V ∧ K ⊆ V ∧
      IsCompact (closure V) ∧ AnalyticOnNhd ℂ ξ P ∧ ξ c = x ∧
      ∀ d ∈ P, orbit d a (ξ d) = 0 ∧ orbit d b d ∈ V ∧
        let A := connectedComponentIn (orbit d (a+1+b) ⁻¹' V) (ξ d)
        IsOpen A ∧ IsPreconnected A ∧ IsCompact (closure A) ∧ closure A ⊆ V ∧
        orbit d (a+1+b) '' A = V ∧
        (∃ hmap : MapsTo (orbit d (a+1+b)) A V,
          IsProperMap (MapsTo.restrict (orbit d (a+1+b)) A V hmap)) ∧
        (∀ L : Set ℂ, IsCompact L → L ⊆ V →
          IsCompact (A ∩ orbit d (a+1+b) ⁻¹' L)) ∧
        ∀ v ∈ V, (∑ z ∈ localFiber d (a+1+b) A v,
          analyticOrderNatAt (fun w => orbit d (a+1+b) w-v) z) = 2 := by
  obtain ⟨P, V, ξ, hP, hcP, hV, hVconn, hKV, hVc, hξ, hξc, hfamily⟩ :=
    quadratic_parameter_one_critical_return c a b K A0 B0 D0 (interior K) univ x
      hK hKconn hx0 hv hD0 hB0 hA0 isOpen_interior hAint
      isOpen_univ (subset_univ D0) hpinj hpcrit hrinj hrcrit
  refine ⟨P, V, ξ, hP, hcP, hV, hVconn, hKV, hVc, hξ, hξc, ?_⟩
  intro d hd
  obtain ⟨hξzero, hdV, hAo, _, _, hAc, hAint', _, _, _, _, _, _,
      hsat, honto, hproperMap, hproper, hdegree⟩ := hfamily d hd
  refine ⟨hξzero, hdV, ?_⟩
  have hcontain := hAint'.trans (interior_subset.trans hKV)
  rw [hsat] at hAo hAc hcontain honto hproperMap hproper hdegree
  exact ⟨hAo, isPreconnected_connectedComponentIn, hAc, hcontain,
    honto, hproperMap, hproper, hdegree⟩

end

end LoopsTelescopeParameterReturn

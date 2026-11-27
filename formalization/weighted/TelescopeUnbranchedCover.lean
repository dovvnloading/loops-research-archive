import TelescopeDeckInvolution
import TelescopeCollarRecognition
import Mathlib.Topology.Homotopy.Lifting

/-!
# The actual two-sheet covering away from a one-critical return value

The full physical return component is proper. Its only critical value is
the image of the distinguished quadratic critical point. The analytic
inverse function theorem and properness therefore construct evenly covered
neighborhoods, with exactly two sheets, at every other target point.
-/

namespace LoopsTelescopeUnbranchedCover

open Set Function Filter
open scoped Topology
open QuadraticEscape LoopsSaturatedTelescope LoopsTelescopeRamification
open LoopsTelescopeCollar LoopsTelescopeConformalInverse
open LoopsTelescopeDeckInvolution LoopsQuadraticCylinderCensus

noncomputable section

private theorem analytic_restriction_local_homeomorph
    (f : ℂ → ℂ) (A V : Set ℂ) (hA : IsOpen A) (hV : IsOpen V)
    (hm : MapsTo f A V) (hf : Continuous f) (ho : IsOpenMap f)
    (S : Set V)
    (ha : ∀ z ∈ A, AnalyticAt ℂ f z)
    (hn : ∀ z : A, MapsTo.restrict f A V hm z ∈ S → deriv f z ≠ 0) :
    IsLocalHomeomorphOn (MapsTo.restrict f A V hm)
      ((MapsTo.restrict f A V hm) ⁻¹' S) := by
  let F := MapsTo.restrict f A V hm
  have hF : Continuous F := (hf.comp continuous_subtype_val).subtype_mk _
  have hFo : IsOpenMap F :=
    hV.isOpenEmbedding_subtypeVal.isOpenMap_iff.mpr (ho.restrict hA)
  apply (isLocalHomeomorphOn_iff_isOpenEmbedding_restrict _).mpr
  intro z hz
  have hstrict := (ha z z.property).hasStrictDerivAt.hasStrictFDerivAt_equiv (hn z hz)
  let e := hstrict.toOpenPartialHomeomorph f
  have hez : (z : ℂ) ∈ e.source := hstrict.mem_toOpenPartialHomeomorph_source
  let U : Set A := ((↑) : A → ℂ) ⁻¹' e.source
  have hU : IsOpen U := e.open_source.preimage continuous_subtype_val
  have hzU : z ∈ U := hez
  refine ⟨U, hU.mem_nhds hzU, ?_⟩
  apply Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
  · exact hF.comp continuous_subtype_val
  · intro u v huv
    apply Subtype.ext
    apply Subtype.ext
    apply e.injOn u.property v.property
    exact congrArg Subtype.val huv
  · exact hFo.restrict hU

private theorem restriction_fiber_finite (c : ℂ) (n : ℕ)
    (A V : Set ℂ) (hm : MapsTo (orbit c n) A V) (v : V) :
    ((MapsTo.restrict (orbit c n) A V hm) ⁻¹' {v}).Finite := by
  have hfinite : (((↑) : A → ℂ) ⁻¹' (↑(localFiber c n A v) : Set ℂ)).Finite :=
    (localFiber c n A v).finite_toSet.preimage Subtype.val_injective.injOn
  apply hfinite.subset
  intro z hz
  apply (mem_localFiber_orbit c n A v z).mpr
  exact ⟨z.property, congrArg Subtype.val hz⟩

/-- Away from the propagated critical value, the derivative of the actual
one-critical return is nonzero at every point of its full source. -/
theorem quadratic_return_offcritical_deriv (c : ℂ) (a b : ℕ)
    (A B D : Set ℂ) (hA : IsOpen A) (hD : IsOpen D)
    (hB : B = connectedComponentIn ((fun w : ℂ => w^2+c) ⁻¹' D) 0)
    (hponto : orbit c a '' A = B)
    (hpinj : InjOn (orbit c a) A) (hrinj : InjOn (orbit c b) D)
    (z : ℂ) (hz : z ∈ A)
    (hv : orbit c (a+1+b) z ≠ orbit c b c) :
    deriv (orbit c (a+1+b)) z ≠ 0 := by
  have hpz : orbit c a z ∈ B := by
    rw [← hponto]
    exact ⟨z, hz, rfl⟩
  have hqz : orbit c (a+1) z ∈ D := by
    rw [hB] at hpz
    exact connectedComponentIn_subset ((fun w : ℂ => w^2+c) ⁻¹' D) 0 hpz
  have hp : criticalVisits c z a = 0 :=
    (criticalVisits_zero_iff c z a).mpr
      (orbit_injOn_no_critical_visits c a A hA hpinj z hz)
  have hs : criticalVisits c (orbit c (a+1) z) b = 0 :=
    (criticalVisits_zero_iff c (orbit c (a+1) z) b).mpr
      (orbit_injOn_no_critical_visits c b D hD hrinj _ hqz)
  have hzero : orbit c a z ≠ 0 := by
    intro he
    apply hv
    rw [quadratic_orbit_add c (a+1) b z]
    change orbit c b ((orbit c a z)^2+c) = orbit c b c
    simp [he]
  apply (orbit_deriv_ne_zero_iff c z (a+1+b)).mpr
  apply (criticalVisits_zero_iff c z (a+1+b)).mp
  rw [criticalVisits_add, criticalVisits_succ, hp, hs, if_neg hzero]

/-- A proper restriction of an actual iterate is a covering over any
target set whose inverse points have nonzero derivative. The local
homeomorphisms are constructed by the analytic inverse theorem. -/
theorem orbit_restriction_cover_of_regular (c : ℂ) (n : ℕ)
    (A V : Set ℂ) (hA : IsOpen A) (hV : IsOpen V)
    (hm : MapsTo (orbit c n) A V)
    (hp : IsProperMap (MapsTo.restrict (orbit c n) A V hm))
    (S : Set V)
    (hn : ∀ z : A, MapsTo.restrict (orbit c n) A V hm z ∈ S →
      deriv (orbit c n) z ≠ 0) :
    IsCoveringMapOn (MapsTo.restrict (orbit c n) A V hm) S := by
  apply hp.isClosedMap.isCoveringMapOn_of_isLocalHomeomorphOn
  · exact fun v _ => restriction_fiber_finite c n A V hm v
  · apply analytic_restriction_local_homeomorph (orbit c n) A V hA hV hm
      (quadratic_orbit_continuous c n)
    · rw [orbit_map_eq_iterate]
      exact quadratic_iterate_open c n
    · exact fun z _ => orbit_analytic c n z
    · exact hn

/-- A saturated actual one-critical return becomes a genuine two-sheet
covering after removing its unique critical value. Properness, local
trivializations, and the two-sheet fiber type are conclusions. -/
theorem quadratic_return_two_sheet_cover (c : ℂ) (a b : ℕ)
    (A B D V : Set ℂ) (x : ℂ) (hx0 : orbit c a x = 0)
    (hVo : IsOpen V) (hVc : IsPreconnected V) (hv : orbit c b c ∈ V)
    (hD : D = connectedComponentIn (orbit c b ⁻¹' V) c)
    (hB : B = connectedComponentIn ((fun w : ℂ => w^2+c) ⁻¹' D) 0)
    (hA : A = connectedComponentIn (orbit c a ⁻¹' B) x)
    (hpinj : InjOn (orbit c a) A) (hrinj : InjOn (orbit c b) D) :
    ∃ hm : MapsTo (orbit c (a+1+b)) A V,
      IsProperMap (MapsTo.restrict (orbit c (a+1+b)) A V hm) ∧
      IsCoveringMapOn (MapsTo.restrict (orbit c (a+1+b)) A V hm)
        {v : V | (v : ℂ) ≠ orbit c b c} ∧
      (∀ v : V, (v : ℂ) ≠ orbit c b c →
        IsEvenlyCovered (MapsTo.restrict (orbit c (a+1+b)) A V hm) v (Fin 2)) ∧
      IsCoveringMap
        ({v : V | (v : ℂ) ≠ orbit c b c}.restrictPreimage
          (MapsTo.restrict (orbit c (a+1+b)) A V hm)) := by
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
  obtain ⟨hsat, honto, _, _⟩ :=
    selected_saturated_return_full_degree c a b A B D V x hx0 hVo hVc hv
      hD hB hA hpinj hrinj
  have hm : MapsTo (orbit c (a+1+b)) A V := fun z hz =>
    honto ▸ mem_image_of_mem _ hz
  have hp : IsProperMap (MapsTo.restrict (orbit c (a+1+b)) A V hm) := by
    rcases hsat with rfl
    exact orbit_component_proper c (a+1+b) V x hVo
  let F := MapsTo.restrict (orbit c (a+1+b)) A V hm
  let S : Set V := {v | (v : ℂ) ≠ orbit c b c}
  have hcover : IsCoveringMapOn F S :=
    orbit_restriction_cover_of_regular c (a+1+b) A V hAo hVo hm hp S
      (fun z hz => quadratic_return_offcritical_deriv c a b A B D hAo hDo hB
        hAp hpinj hrinj z z.property hz)
  refine ⟨hm, hp, hcover, ?_, hcover.isCoveringMap_restrictPreimage⟩
  intro v hvne
  have heven := hcover v hvne
  have hfinite := restriction_fiber_finite c (a+1+b) A V hm v
  letI : Finite (F ⁻¹' {v}) := hfinite
  letI : DiscreteTopology (F ⁻¹' {v}) := heven.discreteTopology_fiber
  obtain ⟨z, w, hzw, hfiber⟩ :=
    quadratic_return_noncritical_fiber c a b A B D hc hB hAp hpinj hrinj v
      (honto.symm ▸ v.property) hvne
  have hz : z ∈ A ∧ orbit c (a+1+b) z = v := by
    change z ∈ {z | z ∈ A ∧ orbit c (a+1+b) z = v}
    rw [hfiber]
    simp
  have hw : w ∈ A ∧ orbit c (a+1+b) w = v := by
    change w ∈ {z | z ∈ A ∧ orbit c (a+1+b) z = v}
    rw [hfiber]
    simp
  let Z : F ⁻¹' {v} := ⟨⟨z, hz.1⟩, Subtype.ext hz.2⟩
  let W : F ⁻¹' {v} := ⟨⟨w, hw.1⟩, Subtype.ext hw.2⟩
  have hcard : Nat.card (F ⁻¹' {v}) = 2 := by
    apply Nat.card_eq_two_iff.mpr
    refine ⟨Z, W, ?_, ?_⟩
    · intro he
      exact hzw (congrArg (fun q : F ⁻¹' {v} => ((q : A) : ℂ)) he)
    · apply Set.eq_univ_of_forall
      intro q
      have hq : ((q : A) : ℂ) ∈ {z | z ∈ A ∧ orbit c (a+1+b) z = v} :=
        ⟨q.val.property, congrArg Subtype.val q.property⟩
      rw [hfiber] at hq
      rcases hq with hq | hq
      · exact Or.inl (Subtype.ext (Subtype.ext hq))
      · exact Or.inr (Subtype.ext (Subtype.ext hq))
  exact heven.of_fiber_homeomorph (Finite.equivFinOfCardEq hcard).toHomeomorphOfDiscrete

/-- Every continuous physical target path avoiding the propagated
critical value has exactly one continuous lift in the full return
component for each specified starting inverse point. The whole path,
not only a finite list of its points, stays in that component. -/
theorem quadratic_return_unique_path_lift (c : ℂ) (a b : ℕ)
    (A B D V : Set ℂ) (x : ℂ) (hx0 : orbit c a x = 0)
    (hVo : IsOpen V) (hVc : IsPreconnected V) (hv : orbit c b c ∈ V)
    (hD : D = connectedComponentIn (orbit c b ⁻¹' V) c)
    (hB : B = connectedComponentIn ((fun w : ℂ => w^2+c) ⁻¹' D) 0)
    (hA : A = connectedComponentIn (orbit c a ⁻¹' B) x)
    (hpinj : InjOn (orbit c a) A) (hrinj : InjOn (orbit c b) D)
    (γ : C(unitInterval, ℂ))
    (hγV : ∀ t, γ t ∈ V) (hγreg : ∀ t, γ t ≠ orbit c b c)
    (z : ℂ) (hz : z ∈ A) (hzγ : orbit c (a+1+b) z = γ 0) :
    ∃! Γ : C(unitInterval, ℂ),
      (∀ t, Γ t ∈ A) ∧ (∀ t, orbit c (a+1+b) (Γ t) = γ t) ∧ Γ 0 = z := by
  obtain ⟨hm, _, _, _, hcover⟩ :=
    quadratic_return_two_sheet_cover c a b A B D V x hx0 hVo hVc hv
      hD hB hA hpinj hrinj
  let F := MapsTo.restrict (orbit c (a+1+b)) A V hm
  let S : Set V := {v | (v : ℂ) ≠ orbit c b c}
  let E : Set A := F ⁻¹' S
  let p : E → S := S.restrictPreimage F
  have hp : IsCoveringMap p := hcover
  let γ' : C(unitInterval, S) :=
    ⟨fun t => ⟨⟨γ t, hγV t⟩, hγreg t⟩,
      (γ.continuous.subtype_mk hγV).subtype_mk hγreg⟩
  have hzE : (⟨z, hz⟩ : A) ∈ E := by
    change orbit c (a+1+b) z ≠ orbit c b c
    rw [hzγ]
    exact hγreg 0
  let e : E := ⟨⟨z, hz⟩, hzE⟩
  have hγ0 : γ' 0 = p e := by
    apply Subtype.ext
    apply Subtype.ext
    exact hzγ.symm
  let Λ : C(unitInterval, E) := hp.liftPath γ' e hγ0
  let Γ : C(unitInterval, ℂ) :=
    ⟨fun t => ((Λ t : A) : ℂ),
      continuous_subtype_val.comp (continuous_subtype_val.comp Λ.continuous)⟩
  have hΓ (t : unitInterval) : orbit c (a+1+b) (Γ t) = γ t :=
    congrArg (fun v : S => ((v : V) : ℂ))
      (congrFun (hp.liftPath_lifts γ' e hγ0) t)
  have hΓ0 : Γ 0 = z :=
    congrArg (fun q : E => ((q : A) : ℂ)) (hp.liftPath_zero γ' e hγ0)
  refine ⟨Γ, ⟨fun t => (Λ t).val.property, hΓ, hΓ0⟩, ?_⟩
  intro Θ hΘ
  have hΘE (t : unitInterval) : (⟨Θ t, hΘ.1 t⟩ : A) ∈ E := by
    change orbit c (a+1+b) (Θ t) ≠ orbit c b c
    rw [hΘ.2.1 t]
    exact hγreg t
  let Θ' : C(unitInterval, E) :=
    ⟨fun t => ⟨⟨Θ t, hΘ.1 t⟩, hΘE t⟩,
      (Θ.continuous.subtype_mk hΘ.1).subtype_mk hΘE⟩
  have hΘlift : p ∘ Θ' = γ' := by
    funext t
    apply Subtype.ext
    apply Subtype.ext
    exact hΘ.2.1 t
  have hΘ0 : Θ' 0 = e := by
    apply Subtype.ext
    apply Subtype.ext
    exact hΘ.2.2
  have hΘeq : Θ' = Λ := (hp.eq_liftPath_iff' hγ0).mpr ⟨hΘlift, hΘ0⟩
  ext t
  exact congrArg (fun q : E => ((q : A) : ℂ))
    (congrArg (fun H : C(unitInterval, E) => H t) hΘeq)

end

end LoopsTelescopeUnbranchedCover

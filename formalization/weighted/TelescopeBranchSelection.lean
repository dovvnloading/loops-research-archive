import TelescopeReturnMonodromy
import SquareRootSelection

/-!
# Exact selection of a physical inverse branch on a retained domain

For an open connected retained target avoiding the critical value, a
prescribed physical initial sheet extends to a continuous inverse section
exactly when all its based coordinate loops have even winding. The section
is then analytic and unique among all continuous sections with that initial
value. The square-root construction is proved to stay in the actual
critical component using full return surjectivity and its sign symmetry.
-/

namespace LoopsTelescopeBranchSelection

open Set Function
open QuadraticEscape LoopsSaturatedTelescope LoopsTelescopeRamification
open LoopsTelescopeCollar LoopsTelescopeConformalInverse
open LoopsTelescopeReturnMonodromy LoopsSquarePathMonodromy LoopsSquareRootSelection

noncomputable section

/-- The parity test on every actual based loop in a retained physical
target, using the constructed critical coordinate. -/
def RetainedEvenLoops {c : ℂ} {a b : ℕ} {A V : Set ℂ}
    (C : ReturnCoordinate c a b A V) (U : Set ℂ) (hUV : U ⊆ V)
    (hUreg : ∀ y ∈ U, y ≠ orbit c b c) (y : U) : Prop :=
  ∀ γ : Path y y,
    Even (windingNumber
      ((domainMap C.toFun U (C.analytic.mono hUV).continuousOn).comp γ)
      (fun t he => hUreg (γ t) (γ t).property
        ((C.zero_iff (γ t) (hUV (γ t).property)).mp he)) (by simp))

/-- Any continuous physical inverse section forces even winding for
every retained based loop. No connectedness or analyticity of the
section is needed for this necessary direction. -/
theorem continuous_section_forces_even_loops {c : ℂ} {a b : ℕ} {A V : Set ℂ}
    (C : ReturnCoordinate c a b A V) (U : Set ℂ) (hUV : U ⊆ V)
    (hUreg : ∀ y ∈ U, y ≠ orbit c b c) (y : U)
    (σ : ℂ → ℂ) (hσcont : ContinuousOn σ U) (hσmap : MapsTo σ U A)
    (hσright : RightInvOn σ (orbit c (a+1+b)) U) :
    RetainedEvenLoops C U hUV hUreg y := by
  let S := domainMap C.toFun U (C.analytic.mono hUV).continuousOn
  have hSzero (v : U) : S v ≠ 0 := fun he =>
    hUreg v v.property ((C.zero_iff v (hUV v.property)).mp he)
  let P : C(U, ℂ) :=
    ⟨fun v => orbit c a (σ v), (quadratic_orbit_continuous c a).comp
      (continuousOn_iff_continuous_restrict.mp hσcont)⟩
  have hsquare (v : U) : P v ^ 2 = S v := by
    change (orbit c a (σ v))^2 = C.toFun v
    rw [← C.square (σ v) (hσmap v.property), hσright v.property]
  exact even_loops_of_continuous_square_root S P hSzero hsquare y

/-- The exact physical branch-selection criterion. On an open connected
retained target, the even-loop test constructs an analytic section through
the prescribed actual source point, unique among all continuous physical
sections with that anchor. In particular simple connectedness is not
assumed, and the square-root image is not assumed to be in the chosen
critical component. -/
theorem quadratic_return_unique_analytic_section_iff_even_loops
    (c : ℂ) (a b : ℕ) (A B D V : Set ℂ) (x : ℂ)
    (hx0 : orbit c a x = 0)
    (hVo : IsOpen V) (hVc : IsPreconnected V) (hv : orbit c b c ∈ V)
    (hD : D = connectedComponentIn (orbit c b ⁻¹' V) c)
    (hB : B = connectedComponentIn ((fun w : ℂ => w^2+c) ⁻¹' D) 0)
    (hA : A = connectedComponentIn (orbit c a ⁻¹' B) x)
    (hpinj : InjOn (orbit c a) A) (hrinj : InjOn (orbit c b) D)
    (C : ReturnCoordinate c a b A V)
    (U : Set ℂ) (hU : IsOpen U) (hUc : IsPreconnected U) (hUV : U ⊆ V)
    (hUreg : ∀ y ∈ U, y ≠ orbit c b c) (y : U)
    (z : ℂ) (hz : z ∈ A) (hbase : orbit c (a+1+b) z = y) :
    (∃ σ : ℂ → ℂ,
      AnalyticOnNhd ℂ σ U ∧ MapsTo σ U A ∧
      RightInvOn σ (orbit c (a+1+b)) U ∧ σ y = z ∧
      ∀ θ : ℂ → ℂ, ContinuousOn θ U → MapsTo θ U A →
        RightInvOn θ (orbit c (a+1+b)) U → θ y = z → EqOn θ σ U) ↔
      RetainedEvenLoops C U hUV hUreg y := by
  constructor
  · rintro ⟨σ, hσan, hσmap, hσright, _, _⟩
    exact continuous_section_forces_even_loops C U hUV hUreg y σ
      hσan.continuousOn hσmap hσright
  · intro heven
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
    obtain ⟨_, honto, _, _⟩ := selected_saturated_return_full_degree
      c a b A B D V x hx0 hVo hVc hv hD hB hA hpinj hrinj
    have hreturnMap : MapsTo (orbit c (a+1+b)) A V := fun w hw =>
      honto ▸ mem_image_of_mem _ hw
    have hprefixMap : MapsTo (orbit c a) A B := fun w hw =>
      hAp ▸ mem_image_of_mem _ hw
    obtain ⟨g, hgmap, hgleft, hgright, hga, _hgd⟩ :=
      orbit_conformal_inverse c a A B hAo hpinj hAp
    have hCzero (v : ℂ) (hvU : v ∈ U) : C.toFun v ≠ 0 := fun he =>
      hUreg v hvU ((C.zero_iff v (hUV hvU)).mp he)
    have hrootbase : (orbit c a z)^2 = C.toFun y := by
      rw [← hbase]
      exact (C.square z hz).symm
    obtain ⟨ξ, hξan, hξbase, hξsquare⟩ :=
      (analytic_square_root_iff_even_loops C.toFun U hU hUc
        (C.analytic.mono hUV) hCzero y (orbit c a z) hrootbase).mpr heven
    have hξB (v : ℂ) (hvU : v ∈ U) : ξ v ∈ B := by
      have himage : v ∈ orbit c (a+1+b) '' A := honto.symm ▸ hUV hvU
      obtain ⟨w, hw, hFw⟩ := himage
      have hsq : (ξ v)^2 = (orbit c a w)^2 := by
        rw [hξsquare v hvU, ← hFw, C.square w hw]
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with he | he
      · rw [he]
        exact hprefixMap hw
      · rw [he]
        have hpw := hprefixMap hw
        rw [hB] at hpw ⊢
        exact quadratic_critical_component_symmetric c D hc (orbit c a w) hpw
    let σ : ℂ → ℂ := fun v => g (ξ v)
    have hσan : AnalyticOnNhd ℂ σ U := fun v hvU =>
      (hga _ (hξB v hvU)).comp (hξan v hvU)
    have hσmap : MapsTo σ U A := fun v hvU => hgmap (hξB v hvU)
    have hσprefix (v : ℂ) (hvU : v ∈ U) : orbit c a (σ v) = ξ v :=
      hgright (hξB v hvU)
    have hσright : RightInvOn σ (orbit c (a+1+b)) U := by
      intro v hvU
      apply C.injective (hreturnMap (hσmap hvU)) (hUV hvU)
      rw [C.square _ (hσmap hvU), hσprefix v hvU, hξsquare v hvU]
    have hσbase : σ y = z := by
      change g (ξ y) = z
      rw [hξbase]
      exact hgleft hz
    refine ⟨σ, hσan, hσmap, hσright, hσbase, ?_⟩
    intro θ hθcont hθmap hθright hθbase
    letI : LocallyPathConnectedSpace U := hU.locallyPathConnectedSpace
    letI : ConnectedSpace U := isConnected_iff_connectedSpace.mp ⟨⟨y, y.property⟩, hUc⟩
    letI : PathConnectedSpace U := PathConnectedSpace.of_locallyPathConnectedSpace
    let S := domainMap C.toFun U (C.analytic.mono hUV).continuousOn
    have hSzero (v : U) : S v ≠ 0 := hCzero v v.property
    let P : C(U, ℂ) :=
      ⟨fun v => orbit c a (θ v), (quadratic_orbit_continuous c a).comp
        (continuousOn_iff_continuous_restrict.mp hθcont)⟩
    have hPsquare (v : U) : P v ^ 2 = S v := by
      change (orbit c a (θ v))^2 = C.toFun v
      rw [← C.square (θ v) (hθmap v.property), hθright v.property]
    have hPbase : P y = orbit c a z := congrArg (orbit c a) hθbase
    have huniq := unique_continuous_square_root_of_even_loops
      S hSzero y (orbit c a z) hrootbase heven
    have hPξ : P = domainMap ξ U hξan.continuousOn :=
      huniq.unique ⟨hPbase, hPsquare⟩ ⟨hξbase, fun v => hξsquare v v.property⟩
    intro v hvU
    apply hpinj (hθmap hvU) (hσmap hvU)
    have he := congrArg (fun H : C(U, ℂ) => H ⟨v, hvU⟩) hPξ
    exact he.trans (hσprefix v hvU).symm

/-- Mere continuous section existence is equivalent to the same exact
parity test. The preceding theorem additionally supplies analyticity and
uniqueness for that prescribed physical starting sheet. -/
theorem quadratic_return_continuous_section_iff_even_loops
    (c : ℂ) (a b : ℕ) (A B D V : Set ℂ) (x : ℂ)
    (hx0 : orbit c a x = 0)
    (hVo : IsOpen V) (hVc : IsPreconnected V) (hv : orbit c b c ∈ V)
    (hD : D = connectedComponentIn (orbit c b ⁻¹' V) c)
    (hB : B = connectedComponentIn ((fun w : ℂ => w^2+c) ⁻¹' D) 0)
    (hA : A = connectedComponentIn (orbit c a ⁻¹' B) x)
    (hpinj : InjOn (orbit c a) A) (hrinj : InjOn (orbit c b) D)
    (C : ReturnCoordinate c a b A V)
    (U : Set ℂ) (hU : IsOpen U) (hUc : IsPreconnected U) (hUV : U ⊆ V)
    (hUreg : ∀ y ∈ U, y ≠ orbit c b c) (y : U)
    (z : ℂ) (hz : z ∈ A) (hbase : orbit c (a+1+b) z = y) :
    (∃ σ : ℂ → ℂ, ContinuousOn σ U ∧ MapsTo σ U A ∧
      RightInvOn σ (orbit c (a+1+b)) U ∧ σ y = z) ↔
      RetainedEvenLoops C U hUV hUreg y := by
  constructor
  · rintro ⟨σ, hσcont, hσmap, hσright, _⟩
    exact continuous_section_forces_even_loops C U hUV hUreg y σ hσcont hσmap hσright
  · intro heven
    obtain ⟨σ, hσan, hσmap, hσright, hσbase, _⟩ :=
      (quadratic_return_unique_analytic_section_iff_even_loops
        c a b A B D V x hx0 hVo hVc hv hD hB hA hpinj hrinj C
        U hU hUc hUV hUreg y z hz hbase).mpr heven
    exact ⟨σ, hσan.continuousOn, hσmap, hσright, hσbase⟩

end

end LoopsTelescopeBranchSelection

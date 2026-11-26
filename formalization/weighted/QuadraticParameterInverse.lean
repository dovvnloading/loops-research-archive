import QuadraticParameterUnivalence
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic

/-!
# Joint analytic inverse families on a common parameter-target collar

The skew map retains the actual quadratic parameter as its first
coordinate. Compact-core injectivity and preterminal critical avoidance
produce one product neighborhood on which the selected inverse depends
complex analytically on both the parameter and the target. The source
closure stays inside any prescribed open ambient neighborhood.
-/

namespace LoopsQuadraticParameterInverse

open Set Function Filter
open scoped Topology
open QuadraticEscape LoopsSaturatedTelescope LoopsTelescopeRamification
open LoopsTelescopeConformalInverse LoopsQuadraticParameterUnivalence

noncomputable section

/-- The actual quadratic orbit, with its parameter retained. -/
def skewOrbit (n : ℕ) (p : ℂ × ℂ) : ℂ × ℂ :=
  (p.1, orbit p.1 n p.2)

private def skewStep (p : ℂ × ℂ) : ℂ × ℂ :=
  (p.1, p.2 ^ 2 + p.1)

private def stepLinearEquiv (z : ℂ) (hz : z ≠ 0) :
    (ℂ × ℂ) ≃L[ℂ] (ℂ × ℂ) where
  toFun p := (p.1, p.1 + (2*z)*p.2)
  invFun q := (q.1, (q.2-q.1)/(2*z))
  map_add' := by
    intro p q
    ext <;> simp <;> ring
  map_smul' := by
    intro a p
    ext <;> simp [smul_eq_mul] <;> ring
  left_inv := by
    intro p
    ext <;> simp <;> field_simp [hz] <;> ring
  right_inv := by
    intro p
    ext <;> simp <;> field_simp [hz] <;> ring
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

private theorem skewStep_hasStrictFDerivAt (p : ℂ × ℂ) (hp : p.2 ≠ 0) :
    HasStrictFDerivAt skewStep
      (stepLinearEquiv p.2 hp : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ)) p := by
  have hfst : HasStrictFDerivAt (fun q : ℂ × ℂ => q.1)
      (ContinuousLinearMap.fst ℂ ℂ ℂ) p := hasStrictFDerivAt_fst
  have hsnd : HasStrictFDerivAt (fun q : ℂ × ℂ => q.2)
      (ContinuousLinearMap.snd ℂ ℂ ℂ) p := hasStrictFDerivAt_snd
  convert hfst.prodMk ((hsnd.mul hsnd).add hfst) using 1
  · funext q
    simp only [skewStep, pow_two]
  · ext q <;> simp [stepLinearEquiv] <;> ring

/-- Joint complex analyticity of the parameter-retaining iterate. -/
theorem quadratic_skew_analytic (n : ℕ) (p : ℂ × ℂ) :
    AnalyticAt ℂ (skewOrbit n) p := by
  have horbit : ∀ k : ℕ,
      AnalyticAt ℂ (fun q : ℂ × ℂ => orbit q.1 k q.2) p := by
    intro k
    induction k with
    | zero => exact analyticAt_snd
    | succ k ih => exact (ih.pow 2).add analyticAt_fst
  exact analyticAt_fst.prodMk (horbit n)

/-- Every critical-free physical orbit segment has an invertible
joint derivative, including parameter variation. -/
theorem quadratic_skew_locally_invertible (n : ℕ) (p : ℂ × ℂ)
    (hcrit : ∀ j < n, orbit p.1 j p.2 ≠ 0) :
    ∃ e : (ℂ × ℂ) ≃L[ℂ] (ℂ × ℂ),
      HasStrictFDerivAt (skewOrbit n) (e : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ)) p := by
  induction n with
  | zero =>
    exact ⟨ContinuousLinearEquiv.refl ℂ (ℂ × ℂ), hasStrictFDerivAt_id p⟩
  | succ n ih =>
    obtain ⟨e, he⟩ := ih (fun j hj => hcrit j (by omega))
    let q := skewOrbit n p
    have hq : q.2 ≠ 0 := hcrit n (by omega)
    let e' := stepLinearEquiv q.2 hq
    refine ⟨e.trans e', ?_⟩
    have hh := (skewStep_hasStrictFDerivAt q hq).comp p he
    simpa only [skewStep, skewOrbit, orbit, Function.comp_def] using hh

/-- On an open injective branch, the actual skew iterate has an open
image and one inverse analytic in both coordinates on that entire image. -/
theorem quadratic_skew_univalent_inverse (n : ℕ) (S : Set (ℂ × ℂ))
    (hS : IsOpen S) (hinj : InjOn (skewOrbit n) S)
    (hcrit : ∀ p ∈ S, ∀ j < n, orbit p.1 j p.2 ≠ 0) :
    IsOpen (skewOrbit n '' S) ∧
      ∃ G : (ℂ × ℂ) → (ℂ × ℂ),
        MapsTo G (skewOrbit n '' S) S ∧
        LeftInvOn G (skewOrbit n) S ∧
        RightInvOn G (skewOrbit n) (skewOrbit n '' S) ∧
        AnalyticOnNhd ℂ G (skewOrbit n '' S) := by
  have hopen : IsOpen (skewOrbit n '' S) := by
    apply isOpen_iff_mem_nhds.mpr
    rintro _ ⟨p, hp, rfl⟩
    obtain ⟨e, he⟩ := quadratic_skew_locally_invertible n p (hcrit p hp)
    rw [← he.map_nhds_eq_of_equiv]
    apply Filter.mem_map.mpr
    exact Filter.mem_of_superset (hS.mem_nhds hp) (fun q hq => ⟨q, hq, rfl⟩)
  let G := Function.invFunOn (skewOrbit n) S
  have honto : SurjOn (skewOrbit n) S (skewOrbit n '' S) := by
    intro y hy
    exact hy
  have hmap : MapsTo G (skewOrbit n '' S) S := honto.mapsTo_invFunOn
  have hleft : LeftInvOn G (skewOrbit n) S := hinj.leftInvOn_invFunOn
  have hright : RightInvOn G (skewOrbit n) (skewOrbit n '' S) :=
    honto.rightInvOn_invFunOn
  refine ⟨hopen, G, hmap, hleft, hright, ?_⟩
  intro y hy
  have hx : G y ∈ S := hmap hy
  obtain ⟨e, he⟩ := quadratic_skew_locally_invertible n (G y) (hcrit (G y) hx)
  have hlocal : ∀ᶠ p in 𝓝 (G y), G (skewOrbit n p) = p :=
    Filter.Eventually.mono (hS.mem_nhds hx) (fun p hp => hleft hp)
  have hlinverse :
      AnalyticAt ℂ (he.localInverse (skewOrbit n) e (G y)) (skewOrbit n (G y)) := by
    exact (he.toOpenPartialHomeomorph (skewOrbit n)).analyticAt_symm'
      he.mem_toOpenPartialHomeomorph_source (quadratic_skew_analytic n (G y))
      he.hasFDerivAt.fderiv
  have hag : AnalyticAt ℂ G (skewOrbit n (G y)) :=
    hlinverse.congr (he.localInverse_unique hlocal).symm
  rwa [hright hy] at hag

/-- Compact-core data construct a common open target collar and a
jointly analytic inverse family. The original compact core is recovered
exactly at the base parameter; the inverse is also conformal in the
target variable at every nearby parameter. -/
theorem quadratic_compact_parameter_inverse_family
    (c : ℂ) (n : ℕ) (C W : Set ℂ)
    (hC : IsCompact C) (hW : IsOpen W) (hCW : C ⊆ W)
    (hI : InjOn (orbit c n) C)
    (hcrit : ∀ z ∈ C, ∀ j < n, orbit c j z ≠ 0) :
    ∃ (P U V : Set ℂ) (g : ℂ → ℂ → ℂ),
      IsOpen P ∧ c ∈ P ∧ IsOpen U ∧ C ⊆ U ∧
      IsCompact (closure U) ∧ closure U ⊆ W ∧
      IsOpen V ∧ orbit c n '' C ⊆ V ∧
      AnalyticOnNhd ℂ (fun p : ℂ × ℂ => g p.1 p.2) (P ×ˢ V) ∧
      (∀ d ∈ P,
        MapsTo (g d) V U ∧
        LeftInvOn (g d) (orbit d n) U ∧
        RightInvOn (g d) (orbit d n) V) ∧
      g c '' (orbit c n '' C) = C ∧
      ∀ d ∈ P, ∀ y ∈ V,
        HasDerivAt (g d) (deriv (orbit d n) (g d y))⁻¹ y ∧
        ConformalAt (g d) y := by
  obtain ⟨P₀, U, hP₀, hcP₀, hU, hCU, hUc, hUW, δ, hδ, hfamily⟩ :=
    quadratic_parameter_univalent_neighborhood_within c n C W hC hW hCW hI hcrit
  let S := P₀ ×ˢ U
  have hSinj : InjOn (skewOrbit n) S := by
    intro p hp q hq he
    have hec : p.1 = q.1 := congrArg Prod.fst he
    apply Prod.ext hec
    apply (hfamily q.1 hq.1).1 (subset_closure hp.2) (subset_closure hq.2)
    have hes := congrArg Prod.snd he
    simpa only [skewOrbit, hec] using hes
  have hScrit : ∀ p ∈ S, ∀ j < n, orbit p.1 j p.2 ≠ 0 := by
    intro p hp
    exact (hfamily p.1 hp.1).2.1 p.2 (subset_closure hp.2)
  obtain ⟨hT, G, hGmap, hGleft, hGright, hGanalytic⟩ :=
    quadratic_skew_univalent_inverse n S (hP₀.prod hU) hSinj hScrit
  have hK : IsCompact (orbit c n '' C) :=
    hC.image (quadratic_orbit_continuous c n)
  have hbase : ({c} : Set ℂ) ×ˢ (orbit c n '' C) ⊆ skewOrbit n '' S := by
    rintro ⟨d, y⟩ ⟨hd, z, hz, hzy⟩
    have hdc : d = c := Set.mem_singleton_iff.mp hd
    subst d
    exact ⟨(c, z), ⟨hcP₀, hCU hz⟩, Prod.ext rfl hzy⟩
  obtain ⟨P₁, V, hP₁, hV, hcP₁, hKV, hPV⟩ :=
    generalized_tube_lemma isCompact_singleton hK hT hbase
  let P := P₀ ∩ P₁
  let g : ℂ → ℂ → ℂ := fun d y => (G (d, y)).2
  have hcP : c ∈ P := ⟨hcP₀, hcP₁ (by simp)⟩
  have htarget (d y : ℂ) (hd : d ∈ P) (hy : y ∈ V) :
      (d, y) ∈ skewOrbit n '' S := hPV ⟨hd.2, hy⟩
  have hbranch : ∀ d ∈ P,
      MapsTo (g d) V U ∧ LeftInvOn (g d) (orbit d n) U ∧
      RightInvOn (g d) (orbit d n) V := by
    intro d hd
    refine ⟨?_, ?_, ?_⟩
    · intro y hy
      exact (hGmap (htarget d y hd hy)).2
    · intro z hz
      exact congrArg Prod.snd (hGleft (show (d, z) ∈ S from ⟨hd.1, hz⟩))
    · intro y hy
      have hright := hGright (htarget d y hd hy)
      have hfst : (G (d, y)).1 = d := congrArg Prod.fst hright
      have hsnd := congrArg Prod.snd hright
      simpa only [skewOrbit, hfst] using hsnd
  have hcore : g c '' (orbit c n '' C) = C := by
    apply Subset.antisymm
    · rintro _ ⟨y, ⟨z, hz, rfl⟩, rfl⟩
      rw [(hbranch c hcP).2.1 (hCU hz)]
      exact hz
    · intro z hz
      exact ⟨orbit c n z, ⟨z, hz, rfl⟩, (hbranch c hcP).2.1 (hCU hz)⟩
  refine ⟨P, U, V, g, hP₀.inter hP₁, hcP, hU, hCU, hUc, hUW,
    hV, hKV, ?_, hbranch, hcore, ?_⟩
  · intro p hp
    exact (hGanalytic (htarget p.1 p.2 hp.1 hp.2)).snd
  · intro d hd y hy
    have hx : g d y ∈ U := (hbranch d hd).1 hy
    have hnonzero : deriv (orbit d n) (g d y) ≠ 0 :=
      (orbit_deriv_ne_zero_iff d (g d y) n).mpr
        ((hfamily d hd.1).2.1 (g d y) (subset_closure hx))
    have hlocal : (g d ∘ orbit d n) =ᶠ[𝓝 (g d y)] id :=
      Filter.Eventually.mono (hU.mem_nhds hx) (fun z hz => (hbranch d hd).2.1 hz)
    have hder := ((orbit_analytic d n (g d y)).hasStrictDerivAt.to_local_left_inverse
      hnonzero hlocal).hasDerivAt
    have hdy : HasDerivAt (g d) (deriv (orbit d n) (g d y))⁻¹ y := by
      simpa only [(hbranch d hd).2.2 hy] using hder
    refine ⟨hdy, hdy.differentiableAt.conformalAt ?_⟩
    rw [hdy.deriv]
    exact inv_ne_zero hnonzero

/-- A continuous inverse over a compact connected target fills the
entire physical preimage component through its moving anchor. The proof
uses compactness to rule out continuation through the boundary of U. -/
theorem quadratic_inverse_compact_component
    (c : ℂ) (n : ℕ) (U K : Set ℂ) (g : ℂ → ℂ)
    (hU : IsOpen U) (hK : IsCompact K) (hKconn : IsPreconnected K)
    (hg : ContinuousOn g K) (hmap : MapsTo g K U)
    (hleft : LeftInvOn g (orbit c n) U)
    (hright : RightInvOn g (orbit c n) K)
    (y : ℂ) (hy : y ∈ K) :
    g '' K = connectedComponentIn (orbit c n ⁻¹' K) (g y) := by
  let T := connectedComponentIn (orbit c n ⁻¹' K) (g y)
  have hanchor : g y ∈ T := mem_connectedComponentIn (by
    change orbit c n (g y) ∈ K
    rwa [hright hy])
  have hpre : T ⊆ orbit c n ⁻¹' K := connectedComponentIn_subset _ _
  have hclosed : IsClosed (g '' K) := (hK.image_of_continuousOn hg).isClosed
  have himageU : g '' K ⊆ U := by
    rintro z ⟨w, hw, rfl⟩
    exact hmap hw
  have hTU : T ⊆ U := by
    intro z hz
    by_contra hzU
    have hcover : T ⊆ U ∪ (g '' K)ᶜ := by
      intro w hw
      by_cases hwU : w ∈ U
      · exact Or.inl hwU
      · exact Or.inr (fun hwi => hwU (himageU hwi))
    obtain ⟨w, hwT, hwU, hwi⟩ :=
      isPreconnected_connectedComponentIn U (g '' K)ᶜ hU hclosed.isOpen_compl
        hcover ⟨g y, hanchor, hmap hy⟩
        ⟨z, hz, fun hzi => hzU (himageU hzi)⟩
    exact hwi ⟨orbit c n w, hpre hwT, hleft hwU⟩
  apply Subset.antisymm
  · apply (hKconn.image g hg).subset_connectedComponentIn
    · exact ⟨y, hy, rfl⟩
    · rintro z ⟨w, hw, rfl⟩
      change orbit c n (g w) ∈ K
      rwa [hright hw]
  · intro z hz
    exact ⟨orbit c n z, hpre hz, hleft (hTU hz)⟩

/-- Every compact connected subtarget of a common analytic collar has
an exact moving selected component. The anchor moves by the same
inverse family; no fixed physical anchor is silently reused. -/
theorem quadratic_inverse_family_compact_component
    (n : ℕ) (P U V : Set ℂ) (g : ℂ → ℂ → ℂ)
    (hU : IsOpen U)
    (hana : AnalyticOnNhd ℂ (fun p : ℂ × ℂ => g p.1 p.2) (P ×ˢ V))
    (hbranch : ∀ d ∈ P,
      MapsTo (g d) V U ∧ LeftInvOn (g d) (orbit d n) U ∧
      RightInvOn (g d) (orbit d n) V)
    (d : ℂ) (hd : d ∈ P) (K : Set ℂ)
    (hK : IsCompact K) (hKconn : IsPreconnected K) (hKV : K ⊆ V)
    (y : ℂ) (hy : y ∈ K) :
    g d '' K = connectedComponentIn (orbit d n ⁻¹' K) (g d y) := by
  have hcont : ContinuousOn (g d) K := by
    intro w hw
    have hi : AnalyticAt ℂ (fun z : ℂ => (d, z)) w :=
      analyticAt_const.prodMk analyticAt_id
    have ha : AnalyticAt ℂ (g d) w := (hana (d, w) ⟨hd, hKV hw⟩).comp hi
    exact ha.continuousAt.continuousWithinAt
  exact quadratic_inverse_compact_component d n U K (g d) hU hK hKconn hcont
    (fun w hw => (hbranch d hd).1 (hKV hw))
    (hbranch d hd).2.1 (fun w hw => (hbranch d hd).2.2 (hKV hw)) y hy

end
end LoopsQuadraticParameterInverse

import SquarePathMonodromy
import Mathlib.Topology.Connected.LocallyPathConnected
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic

/-!
# Exact square-root selection on retained domains

An actual nonzero continuous function admits a globally consistent
square-root branch with a prescribed initial phase exactly when every
based loop has even exponential-cover winding. Simple connectedness is
not required. For analytic functions on open complex domains, the
selected continuous branch is analytic.
-/

namespace LoopsSquareRootSelection

open Set Function Topology
open scoped Topology
open LoopsSquarePathMonodromy

noncomputable section

/-- A covering lift is globally well defined exactly when its
based-loop monodromies fix the prescribed starting point. This form
uses actual path lifts rather than an assumed fundamental-group map. -/
theorem unique_continuous_lift_of_closed_loops
    {E Y X : Type*} [TopologicalSpace E] [TopologicalSpace Y]
    [TopologicalSpace X] [PathConnectedSpace X] [LocallyPathConnectedSpace X]
    {p : E → Y} (cov : IsCoveringMap p) (f : C(X, Y))
    (a : X) (e : E) (he : p e = f a)
    (hclosed : ∀ γ : Path a a,
      cov.liftPath (f.comp γ) e (by simp [he]) 1 = e) :
    ∃! F : C(X, E), F a = e ∧ p ∘ F = f := by
  refine cov.isLocalHomeomorph.existsUnique_continuousMap_lifts f a e he
    (fun γ γ0 => ?_) (fun γ γ' Γ Γ' γ0 γ'0 Γ0 Γ'0 Γlift Γ'lift γend => ?_)
  · simpa [and_comm] using cov.exists_path_lifts (f.comp γ) e (by simp [γ0, he])
  · rw [(cov.eq_liftPath_iff' (by simp [γ0, he])).mpr ⟨Γlift, Γ0⟩,
      (cov.eq_liftPath_iff' (by simp [γ'0, he])).mpr ⟨Γ'lift, Γ'0⟩]
    let pγ : Path a (γ 1) := ⟨γ, γ0, rfl⟩
    let pγ' : Path a (γ 1) := ⟨γ', γ'0, γend.symm⟩
    change (cov.monodromy (.mk (pγ.map f.continuous)) ⟨e, he⟩).1 =
      (cov.monodromy (.mk (pγ'.map f.continuous)) ⟨e, he⟩).1
    rw [← Subtype.ext_iff]
    apply (cov.monodromy_bijective (.mk (pγ'.map f.continuous).symm)).1
    simp_rw [← cov.monodromy_trans_apply, ← Path.Homotopic.Quotient.mk_trans]
    conv_rhs => rw [← Path.Homotopic.Quotient.eq.2 ⟨.reflTransSymm _⟩,
      Path.Homotopic.Quotient.mk_refl, cov.monodromy_refl]
    rw [Path.map_symm, ← Path.map_trans]
    apply Subtype.ext
    exact hclosed (pγ.trans pγ'.symm)

/-- Regard a nonzero continuous function as a map to the punctured plane. -/
def puncturedMap {X : Type*} [TopologicalSpace X]
    (s : C(X, ℂ)) (hzero : ∀ x, s x ≠ 0) : C(X, {z : ℂ // z ≠ 0}) :=
  ⟨fun x => ⟨s x, hzero x⟩, s.continuous.subtype_mk _⟩

/-- Every based-loop winding must be even for an actual continuous
square-root branch. This direction needs no connectedness hypothesis. -/
theorem even_loops_of_continuous_square_root
    {X : Type*} [TopologicalSpace X] (s R : C(X, ℂ))
    (hzero : ∀ x, s x ≠ 0) (hsquare : ∀ x, R x ^ 2 = s x) (a : X) :
    ∀ γ : Path a a,
      Even (windingNumber (s.comp γ) (fun t => hzero (γ t)) (by simp)) := by
  intro γ
  apply (square_lift_closed_iff_even (s.comp γ) (R.comp γ)
    (fun t => hzero (γ t)) (by simp) (fun t => hsquare (γ t))).mp
  simp

/-- Even winding for every actual based loop constructs the unique
global continuous square root with any prescribed initial phase. -/
theorem unique_continuous_square_root_of_even_loops
    {X : Type*} [TopologicalSpace X] [PathConnectedSpace X]
    [LocallyPathConnectedSpace X] (s : C(X, ℂ))
    (hzero : ∀ x, s x ≠ 0) (a : X) (r : ℂ) (hr : r ^ 2 = s a)
    (heven : ∀ γ : Path a a,
      Even (windingNumber (s.comp γ) (fun t => hzero (γ t)) (by simp))) :
    ∃! R : C(X, ℂ), R a = r ∧ ∀ x, R x ^ 2 = s x := by
  let p : {z : ℂ // z ≠ 0} → {z : ℂ // z ≠ 0} :=
    fun z => ⟨(z : ℂ)^2, pow_ne_zero 2 z.property⟩
  have hcov : IsCoveringMap p := isCoveringMap_npow (𝕜 := ℂ) 2 (by norm_num)
  have hrzero : r ≠ 0 := by
    intro h
    apply hzero a
    rw [← hr, h]
    norm_num
  let e : {z : ℂ // z ≠ 0} := ⟨r, hrzero⟩
  let f := puncturedMap s hzero
  have he : p e = f a := Subtype.ext hr
  have hclosed (γ : Path a a) :
      hcov.liftPath (f.comp γ) e (by simp [he]) 1 = e := by
    let Γ := hcov.liftPath (f.comp γ) e (by simp [he])
    let η : C(unitInterval, ℂ) :=
      ⟨fun t => (Γ t : ℂ), continuous_subtype_val.comp Γ.continuous⟩
    have hlift (t : unitInterval) : η t ^ 2 = (s.comp γ) t :=
      congrArg Subtype.val (congrFun (hcov.liftPath_lifts (f.comp γ) e (by simp [he])) t)
    have hend : η 1 = η 0 :=
      (square_lift_closed_iff_even (s.comp γ) η (fun t => hzero (γ t))
        (by simp) hlift).mpr (heven γ)
    apply Subtype.ext
    exact hend.trans (congrArg Subtype.val (hcov.liftPath_zero (f.comp γ) e (by simp [he])))
  obtain ⟨F, hF, huniq⟩ := unique_continuous_lift_of_closed_loops hcov f a e he hclosed
  let R : C(X, ℂ) := ⟨fun x => (F x : ℂ), continuous_subtype_val.comp F.continuous⟩
  refine ⟨R, ⟨congrArg Subtype.val hF.1, fun x =>
    congrArg Subtype.val (congrFun hF.2 x)⟩, ?_⟩
  intro S hS
  have hSzero (x : X) : S x ≠ 0 := by
    intro h
    apply hzero x
    rw [← hS.2 x, h]
    norm_num
  let G := puncturedMap S hSzero
  have hG : G = F := huniq G ⟨Subtype.ext hS.1, by
    funext x
    exact Subtype.ext (hS.2 x)⟩
  apply ContinuousMap.ext
  intro x
  exact congrArg Subtype.val (congrArg (fun H : C(X, {z : ℂ // z ≠ 0}) => H x) hG)

/-- Exact existence criterion on arbitrary path-connected, locally
path-connected spaces: all actual based loops have even winding. -/
theorem continuous_square_root_iff_even_loops
    {X : Type*} [TopologicalSpace X] [PathConnectedSpace X]
    [LocallyPathConnectedSpace X] (s : C(X, ℂ))
    (hzero : ∀ x, s x ≠ 0) (a : X) (r : ℂ) (hr : r ^ 2 = s a) :
    (∃ R : C(X, ℂ), R a = r ∧ ∀ x, R x ^ 2 = s x) ↔
      ∀ γ : Path a a,
        Even (windingNumber (s.comp γ) (fun t => hzero (γ t)) (by simp)) := by
  constructor
  · rintro ⟨R, _, hR⟩
    exact even_loops_of_continuous_square_root s R hzero hR a
  · intro heven
    exact (unique_continuous_square_root_of_even_loops s hzero a r hr heven).exists

/-- A continuous choice of square root of an analytic nonzero function
is automatically analytic, on every open domain where it is chosen. -/
theorem continuous_square_root_analytic (s R : ℂ → ℂ) (U : Set ℂ)
    (hU : IsOpen U) (hs : AnalyticOnNhd ℂ s U) (hR : ContinuousOn R U)
    (hzero : ∀ z ∈ U, s z ≠ 0) (hsquare : ∀ z ∈ U, R z ^ 2 = s z) :
    AnalyticOnNhd ℂ R U := by
  intro z hz
  have hRzero : R z ≠ 0 := by
    intro h
    apply hzero z hz
    rw [← hsquare z hz, h]
    norm_num
  let f : ℂ → ℂ := fun w => w ^ 2
  have hf : AnalyticAt ℂ f (R z) := analyticAt_id.pow 2
  have hd : deriv f (R z) ≠ 0 := by
    change deriv (fun w : ℂ => w ^ 2) (R z) ≠ 0
    rw [deriv_pow_field]
    norm_num only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
    exact mul_ne_zero (show (2 : ℂ) ≠ 0 by norm_num) hRzero
  let g := hf.hasStrictDerivAt.localInverse f (deriv f (R z)) (R z) hd
  have hg : AnalyticAt ℂ g (s z) := by
    rw [← hsquare z hz]
    exact hf.analyticAt_localInverse hd
  have hinverse : ∀ᶠ w in 𝓝 (R z), g (w ^ 2) = w :=
    hf.hasStrictDerivAt.eventually_left_inverse hd
  have heq : (g ∘ s) =ᶠ[𝓝 z] R := by
    filter_upwards [(hR.continuousAt (hU.mem_nhds hz)).eventually hinverse,
      hU.mem_nhds hz] with w hw hwU
    change g (s w) = R w
    rw [← hsquare w hwU]
    exact hw
  exact (hg.comp (hs z hz)).congr heq

/-- Restriction of an ambient continuous function to its actual domain. -/
def domainMap (s : ℂ → ℂ) (U : Set ℂ) (hs : ContinuousOn s U) : C(U, ℂ) :=
  ⟨fun z => s z, continuousOn_iff_continuous_restrict.mp hs⟩

/-- Exact analytic branch criterion on an open connected retained domain.
The domain can have holes: precisely its actual coordinate loops must
have even winding. The initial phase is prescribed, not inferred from
an arbitrary choice of square root. -/
theorem analytic_square_root_iff_even_loops
    (s : ℂ → ℂ) (U : Set ℂ) (hU : IsOpen U) (hUc : IsPreconnected U)
    (hs : AnalyticOnNhd ℂ s U) (hzero : ∀ z ∈ U, s z ≠ 0)
    (a : U) (r : ℂ) (hr : r ^ 2 = s a) :
    (∃ R : ℂ → ℂ, AnalyticOnNhd ℂ R U ∧ R a = r ∧
      ∀ z ∈ U, R z ^ 2 = s z) ↔
      ∀ γ : Path a a,
        Even (windingNumber ((domainMap s U hs.continuousOn).comp γ)
          (fun t => hzero (γ t) (γ t).property) (by simp)) := by
  classical
  letI : LocallyPathConnectedSpace U := hU.locallyPathConnectedSpace
  letI : ConnectedSpace U := isConnected_iff_connectedSpace.mp ⟨⟨a, a.property⟩, hUc⟩
  letI : PathConnectedSpace U := PathConnectedSpace.of_locallyPathConnectedSpace
  let S := domainMap s U hs.continuousOn
  have hSzero (z : U) : S z ≠ 0 := hzero z z.property
  constructor
  · rintro ⟨R, hRa, _, hRsquare⟩
    exact even_loops_of_continuous_square_root S
      (domainMap R U hRa.continuousOn) hSzero (fun z => hRsquare z z.property) a
  · intro heven
    obtain ⟨R₀, hR₀, _⟩ := unique_continuous_square_root_of_even_loops S hSzero a r hr heven
    let R : ℂ → ℂ := fun z => if hz : z ∈ U then R₀ ⟨z, hz⟩ else 0
    have hRval (z : U) : R z = R₀ z := by simp [R, z.property]
    have hRc : ContinuousOn R U := by
      rw [continuousOn_iff_continuous_restrict]
      have heq : U.restrict R = R₀ := funext hRval
      rw [heq]
      exact R₀.continuous
    have hRsquare (z : ℂ) (hz : z ∈ U) : R z ^ 2 = s z := by
      rw [hRval ⟨z, hz⟩]
      exact hR₀.2 ⟨z, hz⟩
    exact ⟨R, continuous_square_root_analytic s R U hU hs hRc hzero hRsquare,
      (hRval a).trans hR₀.1, hRsquare⟩

end

end LoopsSquareRootSelection

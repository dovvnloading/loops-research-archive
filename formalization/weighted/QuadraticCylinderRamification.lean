import QuadraticCriticalFiberCensus

/-!
# Ramification and stability of actual quadratic pullback components

All pullbacks in this file are inverse images in the complex plane.
The simply connected target is an explicit hypothesis, not a symbolic
cylinder label. The critical-orbit obstruction does not require it.
-/

namespace LoopsQuadraticCylinderRamification

open Set Function
open LoopsQuadraticCylinderCensus LoopsQuadraticCriticalFiberCensus
open LoopsStationarySeparatorTransport

abbrev quad (c : ℂ) (z : ℂ) : ℂ := z^2+c

theorem quadratic_global_component_image (c : ℂ) (n : ℕ) (V : Set ℂ)
    (hVo : IsOpen V) (hVc : IsPreconnected V) (x : ℂ)
    (hx : (quad c)^[n] x ∈ V) :
    (quad c)^[n] '' connectedComponentIn ((quad c)^[n] ⁻¹' V) x = V := by
  let f := (quad c)^[n]
  have hf := quadratic_iterate_proper c n
  exact localized_component_image f (f ⁻¹' V) V
    (quadratic_iterate_open c n) hf.isClosedMap (hVo.preimage hf.continuous)
    hVc (fun _ hz => hz) (fun _ hz => hz.2) x hx

/-- An injective open restriction onto its image is a homeomorphism
of the actual subspaces, so simple connectivity can be transported. -/
theorem open_restriction_homeomorph (f : ℂ → ℂ) (S V : Set ℂ)
    (hf : Continuous f) (hfo : IsOpenMap f) (hS : IsOpen S)
    (he : f '' S = V) (hi : InjOn f S) :
    ∃ e : S ≃ₜ V, ∀ x : S, (e x : ℂ) = f x := by
  have hm : MapsTo f S V := by
    intro x hx
    rw [← he]
    exact ⟨x, hx, rfl⟩
  let g : S → V := fun x => ⟨f x, hm x.property⟩
  have hg : Continuous g := (hf.comp continuous_subtype_val).subtype_mk _
  have hgo : IsOpenMap g := (hfo.comp hS.isOpenMap_subtype_val).subtype_mk _
  have hgi : Injective g := by
    intro a b hab
    apply Subtype.ext
    exact hi a.property b.property (congrArg Subtype.val hab)
  have hgs : Surjective g := by
    intro y
    have hy : (y : ℂ) ∈ f '' S := he.symm ▸ y.property
    obtain ⟨x, hx, hxy⟩ := hy
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  exact ⟨(Equiv.ofBijective g ⟨hgi, hgs⟩).toHomeomorphOfContinuousOpen hg hgo,
    fun _ => rfl⟩

/-- Every component over a simply connected open target avoiding
the first n postcritical values is a genuine univalent sheet, and
the component itself is simply connected. No Jordan boundary is assumed. -/
theorem quadratic_iterate_univalent_component (c : ℂ) (n : ℕ) :
    ∀ (V : Set ℂ), IsOpen V → IsSimplyConnected V →
      (∀ k < n, (quad c)^[k] c ∉ V) → ∀ x : ℂ, (quad c)^[n] x ∈ V →
      InjOn ((quad c)^[n]) (connectedComponentIn ((quad c)^[n] ⁻¹' V) x) ∧
      IsSimplyConnected (connectedComponentIn ((quad c)^[n] ⁻¹' V) x) := by
  induction n with
  | zero =>
    intro V hVo hVc _ x hx
    let C := connectedComponentIn ((quad c)^[0] ⁻¹' V) x
    have hi : InjOn ((quad c)^[0]) C := by
      intro a _ b _ hab
      simpa using hab
    have hf := quadratic_iterate_proper c 0
    have hCo : IsOpen C := (hVo.preimage hf.continuous).connectedComponentIn
    have he := quadratic_global_component_image c 0 V hVo hVc.isPathConnected.isPreconnected x hx
    obtain ⟨e, _⟩ := open_restriction_homeomorph ((quad c)^[0]) C V
      hf.continuous (quadratic_iterate_open c 0) hCo he hi
    letI : SimplyConnectedSpace V := hVc
    exact ⟨hi, e.toHomotopyEquiv.simplyConnectedSpace⟩
  | succ n ih =>
    intro V hVo hVc hcrit x hx
    let f := quad c
    let T := f^[n] ⁻¹' V
    let D := connectedComponentIn T (f x)
    let C := connectedComponentIn (f^[n+1] ⁻¹' V) x
    have hxD : f^[n] (f x) ∈ V := by
      simpa only [Function.iterate_succ_apply, f] using hx
    have hD := ih V hVo hVc (fun k hk => hcrit k (by omega)) (f x) hxD
    have hDo : IsOpen D :=
      (hVo.preimage (quadratic_iterate_proper c n).continuous).connectedComponentIn
    have hcD : c ∉ D := by
      intro hc
      exact hcrit n (by omega) (connectedComponentIn_subset T (f x) hc)
    have hsub : f '' C ⊆ T := by
      rintro _ ⟨z, hz, rfl⟩
      have hzV : f^[n+1] z ∈ V := connectedComponentIn_subset (f^[n+1] ⁻¹' V) x hz
      simpa only [T, mem_preimage, Function.iterate_succ_apply] using hzV
    have hpc : IsPreconnected (f '' C) :=
      isPreconnected_connectedComponentIn.image f (quadratic_proper c).continuous.continuousOn
    have hmap : MapsTo f C D := by
      have hh : f x ∈ f '' C := ⟨x, mem_connectedComponentIn hx, rfl⟩
      have hCD : f '' C ⊆ D := hpc.subset_connectedComponentIn hh hsub
      intro z hz
      exact hCD ⟨z, hz, rfl⟩
    have hfi : InjOn f C := quadratic_injOn_over_simplyConnected c C D
      isPreconnected_connectedComponentIn hD.2 hDo hcD hmap
    have hi : InjOn (f^[n+1]) C := by
      intro a ha b hb hab
      apply hfi ha hb
      apply hD.1 (hmap ha) (hmap hb)
      simpa only [Function.iterate_succ_apply] using hab
    have hf := quadratic_iterate_proper c (n+1)
    have hCo : IsOpen C := (hVo.preimage hf.continuous).connectedComponentIn
    have he := quadratic_global_component_image c (n+1) V hVo hVc.isPathConnected.isPreconnected x hx
    obtain ⟨e, _⟩ := open_restriction_homeomorph (f^[n+1]) C V
      hf.continuous (quadratic_iterate_open c (n+1)) hCo he hi
    letI : SimplyConnectedSpace V := hVc
    exact ⟨hi, e.toHomotopyEquiv.simplyConnectedSpace⟩

/-- Any open neighborhood of a point whose first n orbit positions
hit zero contains distinct points with equal n-th iterate. This uses
openness of the actual prefix, not a formal ramification label. -/
theorem quadratic_critical_hit_noninjective (c : ℂ) (n m : ℕ)
    (S : Set ℂ) (hS : IsOpen S) (x : ℂ) (hx : x ∈ S)
    (hm : m < n) (hz : (quad c)^[m] x = 0) :
    ¬ InjOn ((quad c)^[n]) S := by
  let f := quad c
  have hW : IsOpen (f^[m] '' S) := quadratic_iterate_open c m S hS
  have h0 : (0 : ℂ) ∈ f^[m] '' S := ⟨x, hx, hz⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hW 0 h0
  let a : ℂ := (ε/2 : ℝ)
  have ha0 : a ≠ 0 := by
    dsimp [a]
    exact_mod_cast (ne_of_gt (half_pos hε))
  have ha : a ∈ Metric.ball (0 : ℂ) ε := by
    rw [Metric.mem_ball, dist_zero_right]
    dsimp [a]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (half_pos hε)]
    linarith
  have hna : -a ∈ Metric.ball (0 : ℂ) ε := by
    simpa only [Metric.mem_ball, dist_zero_right, norm_neg] using ha
  obtain ⟨u, hu, hue⟩ := hball ha
  obtain ⟨v, hv, hve⟩ := hball hna
  have hfactor (z : ℂ) : f^[n] z = f^[n-m] (f^[m] z) := by
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel hm.le]
  have he : f^[n] u = f^[n] v := by
    rw [hfactor u, hfactor v, hue, hve]
    exact (quadratic_positive_iterate_even c (n-m) (by omega) a).symm
  intro hi
  have huv := hi hu hv he
  have hsign : a = -a := hue.symm.trans (huv ▸ hve)
  apply ha0
  linear_combination (1/2 : ℂ)*hsign

theorem quadratic_iterate_surjective (c : ℂ) (n : ℕ) :
    Surjective ((quad c)^[n]) := by
  induction n with
  | zero => exact fun y => ⟨y, rfl⟩
  | succ n ih =>
    rw [Function.iterate_succ]
    exact ih.comp (quadratic_surjective c)

/-- A postcritical target value forces at least one nonunivalent
global pullback component, even without simple connectivity. -/
theorem quadratic_postcritical_component_obstruction (c : ℂ) (n k : ℕ)
    (V : Set ℂ) (hVo : IsOpen V) (hk : k < n)
    (hcrit : (quad c)^[k] c ∈ V) :
    ∃ x : ℂ, (quad c)^[n] x ∈ V ∧
      ¬ InjOn ((quad c)^[n]) (connectedComponentIn ((quad c)^[n] ⁻¹' V) x) := by
  let f := quad c
  let m := n-(k+1)
  obtain ⟨x, hx⟩ := quadratic_iterate_surjective c m 0
  have hn : k+1+m = n := by dsimp [m]; omega
  have he : f^[n] x = f^[k] c := by
    calc
      f^[n] x = f^[k+1+m] x := by rw [hn]
      _ = f^[k+1] (f^[m] x) := Function.iterate_add_apply f (k+1) m x
      _ = f^[k] c := by rw [hx, Function.iterate_succ_apply]; simp [f, quad]
  have hxV : f^[n] x ∈ V := he.symm ▸ hcrit
  let S := connectedComponentIn (f^[n] ⁻¹' V) x
  have hS : IsOpen S :=
    (hVo.preimage (quadratic_iterate_proper c n).continuous).connectedComponentIn
  exact ⟨x, hxV, quadratic_critical_hit_noninjective c n m S hS x
    (mem_connectedComponentIn hxV) (by dsimp [m]; omega) hx⟩

/-- Exact global univalence criterion on an open simply connected
target: every component is injective if and only if the target avoids
all postcritical values through the indicated finite horizon. -/
theorem quadratic_all_components_univalent_iff (c : ℂ) (n : ℕ)
    (V : Set ℂ) (hVo : IsOpen V) (hVc : IsSimplyConnected V) :
    (∀ x : ℂ, (quad c)^[n] x ∈ V →
      InjOn ((quad c)^[n]) (connectedComponentIn ((quad c)^[n] ⁻¹' V) x)) ↔
      ∀ k < n, (quad c)^[k] c ∉ V := by
  constructor
  · intro hi k hk hcrit
    obtain ⟨x, hx, hbad⟩ := quadratic_postcritical_component_obstruction c n k V hVo hk hcrit
    exact hbad (hi x hx)
  · intro hcrit x hx
    exact (quadratic_iterate_univalent_component c n V hVo hVc hcrit x hx).1

end LoopsQuadraticCylinderRamification

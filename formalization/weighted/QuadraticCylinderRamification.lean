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
    have he := quadratic_global_component_image c 0 V hVo hVc.isPathConnected.isConnected.isPreconnected x hx
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
    have he := quadratic_global_component_image c (n+1) V hVo hVc.isPathConnected.isConnected.isPreconnected x hx
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
  have hsign : a = -a := hue.symm.trans ((congrArg (f^[m]) huv).trans hve)
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


/-- Distinct actual global components consume distinct inverse points
over every target point. The estimate includes critical target fibers. -/
theorem quadratic_component_anchor_bound (c : ℂ) (n : ℕ) (V : Set ℂ)
    (hVo : IsOpen V) (hVc : IsPreconnected V) (y : ℂ) (hy : y ∈ V)
    (A : Finset ℂ) (hA : ∀ a ∈ A, (quad c)^[n] a ∈ V)
    (hdist : ∀ a ∈ A, ∀ b ∈ A,
      connectedComponentIn ((quad c)^[n] ⁻¹' V) a =
        connectedComponentIn ((quad c)^[n] ⁻¹' V) b → a = b) :
    A.card ≤ (globalFiber c n y).card := by
  classical
  let f := (quad c)^[n]
  let S := f ⁻¹' V
  have hhit (a : A) : ∃ z ∈ connectedComponentIn S (a : ℂ), f z = y := by
    have he := quadratic_global_component_image c n V hVo hVc (a : ℂ)
      (hA a a.property)
    have hh : y ∈ f '' connectedComponentIn S (a : ℂ) := he.symm ▸ hy
    exact hh
  choose g hg hgf using hhit
  have hgi : Injective g := by
    intro a b hab
    apply Subtype.ext
    apply hdist a a.property b b.property
    calc
      connectedComponentIn S (a : ℂ) = connectedComponentIn S (g a) :=
        connectedComponentIn_eq (hg a)
      _ = connectedComponentIn S (g b) := congrArg (connectedComponentIn S) hab
      _ = connectedComponentIn S (b : ℂ) := (connectedComponentIn_eq (hg b)).symm
  let B := Finset.univ.image g
  have hBc : B.card = A.card := by
    simp only [B, Finset.card_image_of_injective _ hgi, Finset.card_univ,
      Fintype.card_coe]
  have hsub : B ⊆ globalFiber c n y := by
    intro z hz
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hz
    exact (mem_globalFiber c n y (g a)).2 (hgf a)
  rw [← hBc]
  exact Finset.card_le_card hsub

/-- A connected target containing a postcritical value must merge
at least two distinct points of any regular fiber it contains.
No assumption about the topology of the target boundary is used. -/
theorem quadratic_postcritical_target_merges_regular_fiber (c : ℂ) (n k : ℕ)
    (V : Set ℂ) (hVo : IsOpen V) (hVc : IsPreconnected V)
    (y : ℂ) (hy : y ∈ V)
    (hreg : ∀ j < n, (quad c)^[j] c ≠ y)
    (hk : k < n) (hcrit : (quad c)^[k] c ∈ V) :
    ∃ a b : ℂ, a ≠ b ∧ (quad c)^[n] a = y ∧ (quad c)^[n] b = y ∧
      connectedComponentIn ((quad c)^[n] ⁻¹' V) a =
        connectedComponentIn ((quad c)^[n] ⁻¹' V) b := by
  classical
  by_contra h
  let A := globalFiber c n y
  have hA : ∀ a ∈ A, (quad c)^[n] a ∈ V := by
    intro a ha
    rw [(mem_globalFiber c n y a).1 ha]
    exact hy
  have hdist : ∀ a ∈ A, ∀ b ∈ A,
      connectedComponentIn ((quad c)^[n] ⁻¹' V) a =
        connectedComponentIn ((quad c)^[n] ⁻¹' V) b → a = b := by
    intro a ha b hb hab
    by_contra hne
    exact h ⟨a, b, hne, (mem_globalFiber c n y a).1 ha,
      (mem_globalFiber c n y b).1 hb, hab⟩
  let z := (quad c)^[k] c
  have hbound := quadratic_component_anchor_bound c n V hVo hVc z hcrit A hA hdist
  have hAc : A.card = 2^n := (globalFiber_full_card_iff c y n).2 hreg
  have hlt : (globalFiber c n z).card ≠ 2^n := by
    intro he
    exact ((globalFiber_full_card_iff c z n).1 he k hk) rfl
  have he := globalFiber_card_exact c z n
  omega

/-- A varying connected target enlargement creates no component
missing all earlier components: each new component hits the old base
point and hence contains a full old component. -/
theorem quadratic_enlargement_component_surjective (c : ℂ) (n : ℕ)
    (U V : Set ℂ) (hUV : U ⊆ V) (hVo : IsOpen V) (hVc : IsPreconnected V)
    (y : ℂ) (hy : y ∈ U) (x : ℂ) (hx : (quad c)^[n] x ∈ V) :
    ∃ a : ℂ, (quad c)^[n] a = y ∧
      connectedComponentIn ((quad c)^[n] ⁻¹' U) a ⊆
        connectedComponentIn ((quad c)^[n] ⁻¹' V) x := by
  let f := (quad c)^[n]
  have he := quadratic_global_component_image c n V hVo hVc x hx
  have hh : y ∈ f '' connectedComponentIn (f ⁻¹' V) x := he.symm ▸ hUV hy
  obtain ⟨a, ha, haf⟩ := hh
  have hsub : f ⁻¹' U ⊆ f ⁻¹' V := fun _ hz => hUV hz
  refine ⟨a, haf, ?_⟩
  rw [connectedComponentIn_eq ha]
  exact connectedComponentIn_mono a hsub

/-- For nested open simply connected targets, starting with a
postcritical-free target, a merger of old components occurs exactly
when the enlarged target includes a postcritical value. The merger
can be witnessed over any chosen point of the old target. -/
theorem quadratic_enlargement_merger_iff (c : ℂ) (n : ℕ)
    (U V : Set ℂ) (hUV : U ⊆ V)
    (hUo : IsOpen U) (hUc : IsSimplyConnected U)
    (hVo : IsOpen V) (hVc : IsSimplyConnected V)
    (hreg : ∀ k < n, (quad c)^[k] c ∉ U)
    (y : ℂ) (hy : y ∈ U) :
    (∃ a b : ℂ, (quad c)^[n] a = y ∧ (quad c)^[n] b = y ∧
      connectedComponentIn ((quad c)^[n] ⁻¹' U) a ≠
        connectedComponentIn ((quad c)^[n] ⁻¹' U) b ∧
      connectedComponentIn ((quad c)^[n] ⁻¹' V) a =
        connectedComponentIn ((quad c)^[n] ⁻¹' V) b) ↔
      ∃ k < n, (quad c)^[k] c ∈ V := by
  let f := (quad c)^[n]
  constructor
  · rintro ⟨a, b, ha, hb, hdist, hmerge⟩
    by_contra h
    have hcrit : ∀ k < n, (quad c)^[k] c ∉ V :=
      fun k hk hz => h ⟨k, hk, hz⟩
    have haV : f a ∈ V := by
      change (quad c)^[n] a ∈ V
      rw [ha]
      exact hUV hy
    have hbV : f b ∈ V := by
      change (quad c)^[n] b ∈ V
      rw [hb]
      exact hUV hy
    have hi := (quadratic_iterate_univalent_component c n V hVo hVc hcrit a haV).1
    have hbc : b ∈ connectedComponentIn (f ⁻¹' V) a := by
      rw [hmerge]
      exact mem_connectedComponentIn hbV
    have hab := hi (mem_connectedComponentIn haV) hbc (ha.trans hb.symm)
    exact hdist (congrArg (connectedComponentIn (f ⁻¹' U)) hab)
  · rintro ⟨k, hk, hcrit⟩
    have hyreg : ∀ j < n, (quad c)^[j] c ≠ y :=
      fun j hj he => hreg j hj (he.symm ▸ hy)
    obtain ⟨a, b, hab, ha, hb, hmerge⟩ :=
      quadratic_postcritical_target_merges_regular_fiber c n k V hVo
        hVc.isPathConnected.isConnected.isPreconnected y (hUV hy) hyreg hk hcrit
    refine ⟨a, b, ha, hb, ?_, hmerge⟩
    intro he
    have haU : f a ∈ U := by
      change (quad c)^[n] a ∈ U
      rw [ha]
      exact hy
    have hbU : f b ∈ U := by
      change (quad c)^[n] b ∈ U
      rw [hb]
      exact hy
    have hbc : b ∈ connectedComponentIn (f ⁻¹' U) a := by
      rw [he]
      exact mem_connectedComponentIn hbU
    have hi := (quadratic_iterate_univalent_component c n U hUo hUc hreg a haU).1
    exact hab (hi (mem_connectedComponentIn haU) hbc (ha.trans hb.symm))

end LoopsQuadraticCylinderRamification

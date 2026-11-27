import StationaryUniqueBranch

/-!
# Exact all-depth inverse census of the geometric quotient

The only exceptional one-step target is the image of the unique fixed
point of the descended involution. The correction counts every visit of
that actual model critical orbit, including repeated visits. No target
fiber of the physical quotient is required to be a singleton.
-/

namespace LoopsStationaryBranchCensus

open Set Function Classical

noncomputable section
variable {Y : Type*}

/-- A set-theoretic choice of one predecessor, with no continuity claim. -/
def inverseChoice (G : Y → Y) (hG : Surjective G) (y : Y) : Y :=
  Classical.choose (hG y)

theorem inverseChoice_spec (G : Y → Y) (hG : Surjective G) (y : Y) :
    G (inverseChoice G hG y) = y := Classical.choose_spec (hG y)

theorem inverseChoice_injective (G : Y → Y) (hG : Surjective G) :
    Injective (inverseChoice G hG) := by
  intro x y h
  calc
    x = G (inverseChoice G hG x) := (inverseChoice_spec G hG x).symm
    _ = G (inverseChoice G hG y) := congrArg G h
    _ = y := inverseChoice_spec G hG y

/-- Symmetry preserves the forward image because the two model
predecessor points exhaust the same fiber. -/
theorem model_symmetry_preserves (G S : Y → Y)
    (hpair : ∀ y : Y, G ⁻¹' {G y} = {y, S y}) (y : Y) :
    G (S y) = G y := by
  have h : S y ∈ ({y, S y} : Set Y) := Or.inr rfl
  rw [← hpair y] at h
  exact h

/-- The selected inverse of the critical value is forced; no
choice ambiguity remains there. -/
theorem inverseChoice_critical (G S : Y → Y) (hG : Surjective G)
    (hpair : ∀ y : Y, G ⁻¹' {G y} = {y, S y})
    (o : Y) (hfix : ∀ y : Y, S y = y ↔ y = o) :
    inverseChoice G hG (G o) = o := by
  have h : inverseChoice G hG (G o) ∈ G ⁻¹' {G o} :=
    inverseChoice_spec G hG (G o)
  rw [hpair o, (hfix o).mpr rfl] at h
  rcases h with h | h <;> exact h

/-- Distinct inverse points, recursively generated with the critical
duplicate removed from the second branch. -/
def modelFiber (G S : Y → Y) (hG : Surjective G) (v : Y) : ℕ → Y → Finset Y
  | 0, y => {y}
  | n+1, y =>
      (modelFiber G S hG v n y).image (inverseChoice G hG) ∪
      ((modelFiber G S hG v n y).erase v).image
        (fun w => S (inverseChoice G hG w))

/-- The recursion enumerates the full model inverse fiber, including
all targets on the postcritical orbit. -/
theorem mem_modelFiber (G S : Y → Y) (hG : Surjective G)
    (hpair : ∀ y : Y, G ⁻¹' {G y} = {y, S y})
    (o : Y) (hfix : ∀ y : Y, S y = y ↔ y = o)
    (n : ℕ) (y z : Y) :
    z ∈ modelFiber G S hG (G o) n y ↔ (G^[n]) z = y := by
  induction n generalizing z with
  | zero => simp [modelFiber]
  | succ n ih =>
    simp only [modelFiber, Finset.mem_union, Finset.mem_image, Finset.mem_erase]
    constructor
    · rintro (⟨w, hw, rfl⟩ | ⟨w, ⟨_, hw⟩, rfl⟩)
      · rw [Function.iterate_succ_apply, inverseChoice_spec G hG w]
        exact (ih w).mp hw
      · rw [Function.iterate_succ_apply,
          model_symmetry_preserves G S hpair, inverseChoice_spec G hG w]
        exact (ih w).mp hw
    · intro hz
      let w := G z
      have hw : w ∈ modelFiber G S hG (G o) n y := by
        apply (ih w).mpr
        simpa only [Function.iterate_succ_apply, w] using hz
      have hp : z ∈ G ⁻¹' {G (inverseChoice G hG w)} := by
        change G z = G (inverseChoice G hG w)
        rw [inverseChoice_spec G hG w]
      rw [hpair (inverseChoice G hG w)] at hp
      rcases hp with hp | hp
      · exact Or.inl ⟨w, hw, hp.symm⟩
      · by_cases hc : w = G o
        · have hr : inverseChoice G hG w = o := by
            rw [hc]
            exact inverseChoice_critical G S hG hpair o hfix
          have he : z = inverseChoice G hG w := by
            rw [hp, hr, (hfix o).mpr rfl]
          exact Or.inl ⟨w, hw, he.symm⟩
        · exact Or.inr ⟨w, ⟨hc, hw⟩, hp.symm⟩

/-- No duplicate survives between the two inverse packets after
the unique critical target is deleted from the second packet. -/
theorem model_inverse_branches_disjoint (G S : Y → Y) (hG : Surjective G)
    (hpair : ∀ y : Y, G ⁻¹' {G y} = {y, S y})
    (o : Y) (hfix : ∀ y : Y, S y = y ↔ y = o) (A : Finset Y) :
    Disjoint (A.image (inverseChoice G hG))
      ((A.erase (G o)).image (fun w => S (inverseChoice G hG w))) := by
  apply Finset.disjoint_left.mpr
  intro z hz hz'
  obtain ⟨a, _, hza⟩ := Finset.mem_image.mp hz
  obtain ⟨b, hb, hzb⟩ := Finset.mem_image.mp hz'
  have hbne := (Finset.mem_erase.mp hb).1
  have he : inverseChoice G hG a = S (inverseChoice G hG b) :=
    hza.trans hzb.symm
  have hab : a = b := by
    calc
      a = G (inverseChoice G hG a) := (inverseChoice_spec G hG a).symm
      _ = G (S (inverseChoice G hG b)) := congrArg G he
      _ = G (inverseChoice G hG b) := model_symmetry_preserves G S hpair _
      _ = b := inverseChoice_spec G hG b
  subst a
  have hr : inverseChoice G hG b = o := (hfix _).mp he.symm
  apply hbne
  calc
    b = G (inverseChoice G hG b) := (inverseChoice_spec G hG b).symm
    _ = G o := congrArg G hr

/-- Every depth adds precisely one lost inverse point when that
depth's critical orbit value is the target. -/
theorem modelFiber_card_step (G S : Y → Y) (hG : Surjective G)
    (hS : Involutive S)
    (hpair : ∀ y : Y, G ⁻¹' {G y} = {y, S y})
    (o : Y) (hfix : ∀ y : Y, S y = y ↔ y = o) (y : Y) (n : ℕ) :
    (modelFiber G S hG (G o) (n+1) y).card +
      (if (G^[n]) (G o) = y then 1 else 0) =
      2*(modelFiber G S hG (G o) n y).card := by
  have hsecond : Injective (fun w => S (inverseChoice G hG w)) :=
    hS.injective.comp (inverseChoice_injective G hG)
  rw [modelFiber,
    Finset.card_union_of_disjoint (model_inverse_branches_disjoint G S hG hpair o hfix _),
    Finset.card_image_of_injective _ (inverseChoice_injective G hG),
    Finset.card_image_of_injective _ hsecond]
  by_cases hc : G o ∈ modelFiber G S hG (G o) n y
  · have he := (mem_modelFiber G S hG hpair o hfix n y (G o)).mp hc
    rw [if_pos he, Finset.card_erase_of_mem hc]
    have hp : 0 < (modelFiber G S hG (G o) n y).card := Finset.card_pos.mpr ⟨G o, hc⟩
    omega
  · have he : (G^[n]) (G o) ≠ y :=
      fun h => hc ((mem_modelFiber G S hG hpair o hfix n y (G o)).mpr h)
    have herase : (modelFiber G S hG (G o) n y).erase (G o) =
        modelFiber G S hG (G o) n y := by
      ext z
      simp only [Finset.mem_erase]
      constructor
      · exact fun h => h.2
      · intro hz
        exact ⟨fun h => hc (h ▸ hz), hz⟩
    rw [if_neg he, herase]
    omega

/-- The intrinsic model defect records the projected critical orbit,
not the number of physical points in a quotient fiber. -/
def modelCriticalDefect (G : Y → Y) (v y : Y) : ℕ → ℕ
  | 0 => 0
  | n+1 => 2*modelCriticalDefect G v y n +
      (if (G^[n]) v = y then 1 else 0)

/-- Exact model degree at every target and every finite depth, even
when the target's full physical quotient fiber is nontrivial. -/
theorem modelFiber_card_exact (G S : Y → Y) (hG : Surjective G)
    (hS : Involutive S)
    (hpair : ∀ y : Y, G ⁻¹' {G y} = {y, S y})
    (o : Y) (hfix : ∀ y : Y, S y = y ↔ y = o) (y : Y) (n : ℕ) :
    (modelFiber G S hG (G o) n y).card + modelCriticalDefect G (G o) y n = 2^n := by
  induction n with
  | zero => simp [modelFiber, modelCriticalDefect]
  | succ n ih =>
    have h := modelFiber_card_step G S hG hS hpair o hfix y n
    rw [modelCriticalDefect, pow_succ (2 : ℕ) n]
    omega

theorem modelCriticalDefect_zero_iff (G : Y → Y) (v y : Y) (n : ℕ) :
    modelCriticalDefect G v y n = 0 ↔ ∀ k < n, (G^[k]) v ≠ y := by
  induction n with
  | zero => simp [modelCriticalDefect]
  | succ n ih =>
    constructor
    · intro hd k hk
      have hprev : modelCriticalDefect G v y n = 0 := by
        simp only [modelCriticalDefect] at hd
        omega
      by_cases hkn : k = n
      · subst k
        intro he
        simp [modelCriticalDefect, he] at hd
      · exact ih.mp hprev k (by omega)
    · intro h
      have hprev := ih.mpr (fun k hk => h k (by omega))
      simp [modelCriticalDefect, hprev, h n (by omega)]

/-- Full binary cardinality is equivalent to avoiding the finite
postcritical set in the model, with no singleton-anchor hypothesis. -/
theorem modelFiber_full_card_iff (G S : Y → Y) (hG : Surjective G)
    (hS : Involutive S)
    (hpair : ∀ y : Y, G ⁻¹' {G y} = {y, S y})
    (o : Y) (hfix : ∀ y : Y, S y = y ↔ y = o) (y : Y) (n : ℕ) :
    (modelFiber G S hG (G o) n y).card = 2^n ↔
      ∀ k < n, (G^[k]) (G o) ≠ y := by
  rw [← modelCriticalDefect_zero_iff G (G o) y n]
  have h := modelFiber_card_exact G S hG hS hpair o hfix y n
  omega

/-- A source-facing certificate, independent of the chosen inverse
selector: all model predecessors are enumerated and counted exactly. -/
theorem model_inverse_census (G S : Y → Y) (hG : Surjective G)
    (hS : Involutive S)
    (hpair : ∀ y : Y, G ⁻¹' {G y} = {y, S y})
    (o : Y) (hfix : ∀ y : Y, S y = y ↔ y = o) (y : Y) (n : ℕ) :
    ∃ M : Finset Y, (∀ z, z ∈ M ↔ (G^[n]) z = y) ∧
      M.card + modelCriticalDefect G (G o) y n = 2^n :=
  ⟨modelFiber G S hG (G o) n y, mem_modelFiber G S hG hpair o hfix n y,
    modelFiber_card_exact G S hG hS hpair o hfix y n⟩

/-- If the physical map is injective on every geometric fiber
except the critical one, a target avoiding the finite projected
postcritical set loses no predecessor labels under the quotient.
The target itself need not have a singleton geometric fiber. -/
theorem inverse_projection_injective_of_branch_avoidance
    {X : Type*} (p : X → Y) (F : X → X) (G : Y → Y)
    (hs : Semiconj p F G) (o : Y)
    (hinj : ∀ y : Y, y ≠ o → InjOn F (p ⁻¹' {y}))
    (n : ℕ) (a : X) :
    (∀ k < n, (G^[k]) (G o) ≠ p a) →
      InjOn p ((F^[n]) ⁻¹' {a}) := by
  induction n with
  | zero =>
    intro _ x hx z hz _
    exact (show x = a from hx).trans (show z = a from hz).symm
  | succ n ih =>
    intro havoid x hx z hz hpxz
    change (F^[n+1]) x = a at hx
    change (F^[n+1]) z = a at hz
    have hx' : (F^[n]) (F x) = a := by
      simpa only [Function.iterate_succ_apply] using hx
    have hz' : (F^[n]) (F z) = a := by
      simpa only [Function.iterate_succ_apply] using hz
    have hforward : p (F x) = p (F z) :=
      (hs x).trans ((congrArg G hpxz).trans (hs z).symm)
    have hFxz : F x = F z :=
      ih (fun k hk => havoid k (Nat.lt_succ_of_lt hk)) hx' hz' hforward
    have hnoncritical : p x ≠ o := by
      intro he
      have h : (G^[n+1]) (p x) = p a :=
        (hs.iterate_right (n+1) x).symm.trans (congrArg p hx)
      rw [he, Function.iterate_succ_apply] at h
      exact havoid n (Nat.lt_succ_self n) h
    exact hinj (p x) hnoncritical rfl hpxz.symm hFxz

section ActualQuadratic

variable [TopologicalSpace Y] [T2Space Y]
open LoopsStationaryFiberDynamics LoopsStationaryUniqueBranch

/-- Exact all-depth model ramification for the actual filled
quadratic, at every target without a singleton geometric fiber
assumption. The exceptional orbit is the projection of the actual
critical value, and all repeated encounters are retained. -/
theorem quadratic_filled_model_inverse_census
    (c : ℂ) (p : quadraticFilled c → Y) (G : Y → Y)
    (hp : Continuous p) (hsurj : Surjective p)
    (hs : Semiconj p (quadraticFilledMap c) G)
    (hf : ∀ y : Y, IsPreconnected (p ⁻¹' {y}))
    (hlight : ∀ y : Y, IsTotallyDisconnected (G ⁻¹' {y}))
    (crit : quadraticFilled c) (hcrit : (crit : ℂ) = 0)
    (hKi : interior (quadraticFilled c) = ∅) (y : Y) (n : ℕ) :
    ∃ M : Finset Y, (∀ z, z ∈ M ↔ (G^[n]) z = y) ∧
      M.card + modelCriticalDefect G (p (quadraticFilledMap c crit)) y n = 2^n ∧
      (M.card = 2^n ↔
        ∀ k < n, (G^[k]) (p (quadraticFilledMap c crit)) ≠ y) := by
  obtain ⟨S, _, hSi, _, _, hpair, hfix⟩ :=
    quadratic_filled_unique_model_involution c p G hp hsurj hs hf hlight
      crit hcrit hKi
  have hG : Surjective G := by
    intro z
    obtain ⟨x, hx⟩ := hsurj z
    obtain ⟨w, hw⟩ := LoopsTerminalFiberExclusion.quadratic_filled_map_surjective c x
    refine ⟨p w, ?_⟩
    rw [← hs w, hw, hx]
  rw [hs crit]
  exact ⟨modelFiber G S hG (G (p crit)) n y,
    mem_modelFiber G S hG hpair (p crit) hfix n y,
    modelFiber_card_exact G S hG hSi hpair (p crit) hfix y n,
    modelFiber_full_card_iff G S hG hSi hpair (p crit) hfix y n⟩

/-- A finite proposed model inverse census is exhaustive exactly
when its intrinsic ramification-adjusted cardinality reaches the
full degree. Completeness is valid at critical targets as well. -/
theorem quadratic_filled_model_census_complete
    (c : ℂ) (p : quadraticFilled c → Y) (G : Y → Y)
    (hp : Continuous p) (hsurj : Surjective p)
    (hs : Semiconj p (quadraticFilledMap c) G)
    (hf : ∀ y : Y, IsPreconnected (p ⁻¹' {y}))
    (hlight : ∀ y : Y, IsTotallyDisconnected (G ⁻¹' {y}))
    (crit : quadraticFilled c) (hcrit : (crit : ℂ) = 0)
    (hKi : interior (quadraticFilled c) = ∅)
    (y : Y) (n : ℕ) (A : Finset Y)
    (hA : ∀ z ∈ A, (G^[n]) z = y) :
    (∀ z : Y, (G^[n]) z = y → z ∈ A) ↔
      A.card + modelCriticalDefect G (p (quadraticFilledMap c crit)) y n = 2^n := by
  obtain ⟨M, hM, hcount, _⟩ := quadratic_filled_model_inverse_census
    c p G hp hsurj hs hf hlight crit hcrit hKi y n
  have hAM : A ⊆ M := fun z hz => (hM z).mpr (hA z hz)
  constructor
  · intro hexhaust
    have hMA : M ⊆ A := fun z hz => hexhaust z ((hM z).mp hz)
    have heq : A = M := Finset.Subset.antisymm hAM hMA
    rwa [heq]
  · intro hcountA
    have heq : A = M := Finset.eq_of_subset_of_card_le hAM (by omega)
    intro z hz
    rw [heq]
    exact (hM z).mpr hz

/-- Outside the finite projected postcritical set, the entire
actual n-step inverse fiber projects bijectively onto the entire
model inverse fiber. This removes the old singleton-target-anchor
restriction from exact predecessor-label transport. -/
theorem quadratic_filled_regular_inverse_projection_bijOn
    (c : ℂ) (p : quadraticFilled c → Y) (G : Y → Y)
    (hp : Continuous p) (hsurj : Surjective p)
    (hs : Semiconj p (quadraticFilledMap c) G)
    (hf : ∀ y : Y, IsPreconnected (p ⁻¹' {y}))
    (hlight : ∀ y : Y, IsTotallyDisconnected (G ⁻¹' {y}))
    (crit : quadraticFilled c) (hcrit : (crit : ℂ) = 0)
    (hKi : interior (quadraticFilled c) = ∅)
    (n : ℕ) (a : quadraticFilled c)
    (havoid : ∀ k < n, (G^[k]) (p (quadraticFilledMap c crit)) ≠ p a) :
    BijOn p (((quadraticFilledMap c)^[n]) ⁻¹' {a})
      ((G^[n]) ⁻¹' {p a}) := by
  have hinj := inverse_projection_injective_of_branch_avoidance
    p (quadraticFilledMap c) G hs (p crit)
    (quadratic_noncritical_geometric_fiber_injective c p hp hf crit hcrit hKi)
    n a (by simpa only [hs crit] using havoid)
  have hproj := LoopsStationaryLightModel.model_iterate_preimage_projection
    p (quadraticFilledMap c) G hs
    (LoopsStationaryLightModel.quadratic_filled_light_fiber_image c p G
      hp hsurj hs hf hlight) a n
  refine ⟨?_, hinj, ?_⟩
  · intro x hx
    change (G^[n]) (p x) = p a
    rw [← hs.iterate_right n x, hx]
  · intro y hy
    rw [hproj] at hy
    exact hy

end ActualQuadratic

end
end LoopsStationaryBranchCensus

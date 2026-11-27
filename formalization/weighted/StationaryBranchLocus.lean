import StationaryUniqueBranch

/-!
# The exact local injectivity locus of the geometric model

The unique coincident-pair point is a genuine obstruction to local
injectivity when it is not isolated. This last premise is essential:
the one-point quotient has a fixed involution and an injective map.
-/

namespace LoopsStationaryBranchLocus

open Set Function
open LoopsStationaryFiberDynamics LoopsStationaryUniqueBranch

variable {Y : Type*} [TopologicalSpace Y] [T2Space Y]

/-- Local injectivity is expressed on an actual open neighborhood. -/
def HasInjectiveNeighborhood (G : Y → Y) (y : Y) : Prop :=
  ∃ U : Set Y, IsOpen U ∧ y ∈ U ∧ InjOn G U

/-- Away from pair coincidence, Hausdorff separation of the two
inverse points gives an injective neighborhood. No model openness
or prescribed local inverse is used. -/
theorem injective_neighborhood_of_nonfixed_pair
    (G S : Y → Y) (hS : Continuous S)
    (hpair : ∀ y : Y, G ⁻¹' {G y} = {y, S y})
    (y : Y) (hne : S y ≠ y) : HasInjectiveNeighborhood G y := by
  obtain ⟨U, V, hU, hV, hyU, hSyV, hUV⟩ := t2_separation hne.symm
  refine ⟨U ∩ S ⁻¹' V, hU.inter (hV.preimage hS), ⟨hyU, hSyV⟩, ?_⟩
  intro x hx z hz he
  have hzpair : z ∈ G ⁻¹' {G x} := he.symm
  rw [hpair x, mem_insert_iff, mem_singleton_iff] at hzpair
  rcases hzpair with h | h
  · exact h.symm
  · exact False.elim ((Set.disjoint_left.mp hUV) hz.1 (h.symm ▸ hx.2))

/-- An injective neighborhood of the unique fixed pair point would
make that point isolated. The contradiction is produced inside the
intersection of the neighborhood and its reflected preimage. -/
theorem nonisolated_fixed_pair_no_injective_neighborhood
    (G S : Y → Y) (k : Y) (hS : Continuous S)
    (hpair : ∀ y : Y, G ⁻¹' {G y} = {y, S y})
    (hfixed : ∀ y : Y, S y = y ↔ y = k)
    (hnotiso : ¬ IsOpen ({k} : Set Y)) :
    ¬ HasInjectiveNeighborhood G k := by
  rintro ⟨U, hU, hkU, hinj⟩
  have hSk : S k = k := (hfixed k).mpr rfl
  have he : U ∩ S ⁻¹' U = ({k} : Set Y) := by
    ext y
    constructor
    · intro hy
      have hSy : S y ∈ G ⁻¹' {G y} := by
        rw [hpair y]
        exact Or.inr rfl
      have hge : G (S y) = G y := hSy
      have hye : S y = y := hinj hy.2 hy.1 hge
      exact (hfixed y).mp hye
    · intro hy
      have hyk : y = k := hy
      subst y
      exact ⟨hkU, hSk.symm ▸ hkU⟩
  apply hnotiso
  rw [← he]
  exact hU.inter (hU.preimage hS)

/-- The entire local injectivity locus is the complement of the
nonisolated unique coincident-pair point. -/
theorem model_local_injectivity_locus
    (G S : Y → Y) (k : Y) (hS : Continuous S)
    (hpair : ∀ y : Y, G ⁻¹' {G y} = {y, S y})
    (hfixed : ∀ y : Y, S y = y ↔ y = k)
    (hnotiso : ¬ IsOpen ({k} : Set Y)) (y : Y) :
    HasInjectiveNeighborhood G y ↔ y ≠ k := by
  constructor
  · intro hy he
    subst y
    exact nonisolated_fixed_pair_no_injective_neighborhood
      G S k hS hpair hfixed hnotiso hy
  · intro hy
    exact injective_neighborhood_of_nonfixed_pair G S hS hpair y
      (fun h => hy ((hfixed y).mp h))

/-- A nontrivial connected Hausdorff model has no isolated point;
this supplies the extra premise without importing a branch theorem. -/
theorem singleton_not_open_of_preconnected [PreconnectedSpace Y] [Nontrivial Y]
    (k : Y) : ¬ IsOpen ({k} : Set Y) := by
  intro ho
  have hc : IsClopen ({k} : Set Y) := ⟨isClosed_singleton, ho⟩
  have hall : (univ : Set Y) ⊆ ({k} : Set Y) :=
    isPreconnected_univ.subset_isClopen hc ⟨k, mem_univ k, Set.mem_singleton k⟩
  obtain ⟨y, hy⟩ := exists_ne k
  exact hy (hall (mem_univ y))

/-- The local injectivity locus of an actual quadratic geometric
model is exactly the complement of the projected physical critical
point, provided that point is not isolated. No local branch property
is an input. -/
theorem quadratic_model_local_injectivity_locus
    (c : ℂ) (p : quadraticFilled c → Y) (G : Y → Y)
    (hp : Continuous p) (hsurj : Surjective p)
    (hs : Semiconj p (quadraticFilledMap c) G)
    (hf : ∀ y : Y, IsPreconnected (p ⁻¹' {y}))
    (hlight : ∀ y : Y, IsTotallyDisconnected (G ⁻¹' {y}))
    (crit : quadraticFilled c) (hcrit : (crit : ℂ) = 0)
    (hKi : interior (quadraticFilled c) = ∅)
    (hnotiso : ¬ IsOpen ({p crit} : Set Y)) (y : Y) :
    HasInjectiveNeighborhood G y ↔ y ≠ p crit := by
  obtain ⟨S, hSc, _, _, _, hpair, hfixed⟩ :=
    quadratic_filled_unique_model_involution c p G hp hsurj hs hf hlight crit hcrit hKi
  exact model_local_injectivity_locus G S (p crit) hSc hpair hfixed hnotiso y

/-- For a nontrivial connected geometric model, nonisolation is a
conclusion of topology. The sole failure of local injectivity is
therefore the projection of the actual quadratic critical point. -/
theorem quadratic_connected_model_unique_branch
    [PreconnectedSpace Y] [Nontrivial Y]
    (c : ℂ) (p : quadraticFilled c → Y) (G : Y → Y)
    (hp : Continuous p) (hsurj : Surjective p)
    (hs : Semiconj p (quadraticFilledMap c) G)
    (hf : ∀ y : Y, IsPreconnected (p ⁻¹' {y}))
    (hlight : ∀ y : Y, IsTotallyDisconnected (G ⁻¹' {y}))
    (crit : quadraticFilled c) (hcrit : (crit : ℂ) = 0)
    (hKi : interior (quadraticFilled c) = ∅) (y : Y) :
    HasInjectiveNeighborhood G y ↔ y ≠ p crit := by
  exact quadratic_model_local_injectivity_locus c p G hp hsurj hs hf hlight
    crit hcrit hKi (singleton_not_open_of_preconnected (p crit)) y

end LoopsStationaryBranchLocus

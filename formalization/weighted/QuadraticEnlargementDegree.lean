import QuadraticComponentFiberDegree

/-!
# Exact degree accounting for actual quadratic component mergers

A finite census is obtained from one actual inverse fiber, even if that
fiber is critical. The census is independent of the anchor target point.
No simple connectivity or assumption that old components are univalent
is required for conservation.
-/

namespace LoopsQuadraticEnlargementDegree

open Set Function Classical
open LoopsQuadraticCylinderCensus LoopsQuadraticCylinderRamification
open LoopsQuadraticComponentFiberDegree
open scoped BigOperators

noncomputable section

/-- All old components that have an inverse point in the selected
enlarged component over y. The entries are actual planar subsets. -/
def mergerCensus (c : ℂ) (n : ℕ) (U V : Set ℂ) (x y : ℂ) :
    Finset (Set ℂ) := by
  classical
  exact (localFiber c n (connectedComponentIn ((quad c)^[n] ⁻¹' V) x) y).image
    (connectedComponentIn ((quad c)^[n] ⁻¹' U))

/-- A single fiber enumerates precisely all old components inside
the enlarged one, including when the chosen fiber is critical. -/
theorem mem_mergerCensus (c : ℂ) (n : ℕ) (U V : Set ℂ)
    (hUV : U ⊆ V) (hUo : IsOpen U) (hUc : IsPreconnected U)
    (x y : ℂ) (hy : y ∈ U) (D : Set ℂ) :
    D ∈ mergerCensus c n U V x y ↔
      ∃ a ∈ connectedComponentIn ((quad c)^[n] ⁻¹' V) x,
        (quad c)^[n] a ∈ U ∧
          D = connectedComponentIn ((quad c)^[n] ⁻¹' U) a := by
  classical
  let f := (quad c)^[n]
  let B := connectedComponentIn (f ⁻¹' V) x
  let g := connectedComponentIn (f ⁻¹' U)
  change D ∈ (localFiber c n B y).image g ↔
    ∃ a ∈ B, f a ∈ U ∧ D = g a
  constructor
  · intro h
    obtain ⟨a, ha, hD⟩ := Finset.mem_image.mp h
    obtain ⟨haB, hay⟩ := (mem_localFiber c n B y a).mp ha
    have haU : f a ∈ U := by
      change ((fun w : ℂ => w^2+c)^[n]) a ∈ U
      rw [hay]
      exact hy
    exact ⟨a, haB, haU, hD.symm⟩
  · rintro ⟨a, haB, haU, rfl⟩
    have he := quadratic_global_component_image c n U hUo hUc a haU
    have hh : y ∈ f '' g a := he.symm ▸ hy
    obtain ⟨b, hb, hby⟩ := hh
    have hsub : g a ⊆ B := by
      change connectedComponentIn (f ⁻¹' U) a ⊆ connectedComponentIn (f ⁻¹' V) x
      rw [connectedComponentIn_eq haB]
      exact connectedComponentIn_mono a (preimage_mono hUV)
    exact Finset.mem_image.mpr
      ⟨b, (mem_localFiber c n B y b).mpr ⟨hsub hb, hby⟩,
        (connectedComponentIn_eq hb).symm⟩

/-- The census is geometric: changing the anchor target, even to a
postcritical value, cannot change the family of old components. -/
theorem mergerCensus_independent (c : ℂ) (n : ℕ) (U V : Set ℂ)
    (hUV : U ⊆ V) (hUo : IsOpen U) (hUc : IsPreconnected U)
    (x y z : ℂ) (hy : y ∈ U) (hz : z ∈ U) :
    mergerCensus c n U V x y = mergerCensus c n U V x z := by
  ext D
  rw [mem_mergerCensus c n U V hUV hUo hUc x y hy D,
    mem_mergerCensus c n U V hUV hUo hUc x z hz D]

/-- The entire enlarged inverse fiber partitions into the exact old
component fibers. This counts distinct inverse points at every y,
without requiring a regular value. -/
theorem mergerCensus_fiber_partition (c : ℂ) (n : ℕ) (U V : Set ℂ)
    (hUV : U ⊆ V) (x y : ℂ) (hy : y ∈ U) :
    (∑ D ∈ mergerCensus c n U V x y, (localFiber c n D y).card) =
      (localFiber c n (connectedComponentIn ((quad c)^[n] ⁻¹' V) x) y).card := by
  classical
  let f := (quad c)^[n]
  let B := connectedComponentIn (f ⁻¹' V) x
  let g := connectedComponentIn (f ⁻¹' U)
  let F := localFiber c n B y
  change (∑ D ∈ F.image g, (localFiber c n D y).card) = F.card
  have hfilter (D : Set ℂ) (hD : D ∈ F.image g) :
      F.filter (fun a => g a = D) = localFiber c n D y := by
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hD
    have haB := ((mem_localFiber c n B y a).mp ha).1
    have hsub : g a ⊆ B := by
      change connectedComponentIn (f ⁻¹' U) a ⊆ connectedComponentIn (f ⁻¹' V) x
      rw [connectedComponentIn_eq haB]
      exact connectedComponentIn_mono a (preimage_mono hUV)
    ext z
    simp only [F, Finset.mem_filter, mem_localFiber]
    constructor
    · rintro ⟨⟨hzB, hzy⟩, hgz⟩
      have hzU : f z ∈ U := by
        change ((fun w : ℂ => w^2+c)^[n]) z ∈ U
        rw [hzy]
        exact hy
      have hzC : z ∈ g z := mem_connectedComponentIn hzU
      exact ⟨hgz ▸ hzC, hzy⟩
    · rintro ⟨hz, hzy⟩
      exact ⟨⟨hsub hz, hzy⟩, (connectedComponentIn_eq hz).symm⟩
  calc
    (∑ D ∈ F.image g, (localFiber c n D y).card) =
        ∑ D ∈ F.image g, (F.filter (fun a => g a = D)).card := by
      apply Finset.sum_congr rfl
      intro D hD
      rw [hfilter D hD]
    _ = F.card := (Finset.card_eq_sum_card_image g F).symm

/-- Every actual old component in the census carries positive
distinct-point mass at the chosen anchor, even if it is critical. -/
theorem mergerCensus_positive_mass (c : ℂ) (n : ℕ) (U V : Set ℂ)
    (x y : ℂ) (hy : y ∈ U) (D : Set ℂ)
    (hD : D ∈ mergerCensus c n U V x y) :
    0 < (localFiber c n D y).card := by
  classical
  let f := (quad c)^[n]
  let B := connectedComponentIn (f ⁻¹' V) x
  let g := connectedComponentIn (f ⁻¹' U)
  change D ∈ (localFiber c n B y).image g at hD
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hD
  have hay := ((mem_localFiber c n B y a).mp ha).2
  have haU : f a ∈ U := by
    change ((fun w : ℂ => w^2+c)^[n]) a ∈ U
    rw [hay]
    exact hy
  exact Finset.card_pos.mpr
    ⟨a, (mem_localFiber c n (g a) y a).mpr ⟨mem_connectedComponentIn haU, hay⟩⟩

/-- A partially declared actual component family is complete exactly
when its fiber mass reaches the full enlarged fiber. Unlike counting
one representative per component, this remains valid for ramified
components and at critical targets. -/
theorem mergerCensus_complete_iff_mass (c : ℂ) (n : ℕ) (U V : Set ℂ)
    (hUV : U ⊆ V) (x y : ℂ) (hy : y ∈ U)
    (T : Finset (Set ℂ)) (hT : T ⊆ mergerCensus c n U V x y) :
    T = mergerCensus c n U V x y ↔
      (∑ D ∈ T, (localFiber c n D y).card) =
        (localFiber c n (connectedComponentIn ((quad c)^[n] ⁻¹' V) x) y).card := by
  classical
  have he := mergerCensus_fiber_partition c n U V hUV x y hy
  constructor
  · intro h
    rw [h]
    exact he
  · intro h
    ext D
    constructor
    · exact fun hd => hT hd
    · intro hd
      by_contra hn
      have hlt := Finset.sum_lt_sum_of_subset
        (f := fun E : Set ℂ => (localFiber c n E y).card) hT hd hn
        (mergerCensus_positive_mass c n U V x y hy D hd)
        (fun _ _ _ => Nat.zero_le _)
      rw [h, he] at hlt
      exact (lt_irrefl _ hlt)

/-- At a regular target the exact partition is conservation of the
intrinsic enlarged degree, with one positive degree for each actual
old component. Neither target has to be simply connected. -/
theorem mergerCensus_degree_conservation (c : ℂ) (n : ℕ) (U V : Set ℂ)
    (hUV : U ⊆ V) (hVo : IsOpen V) (hVc : IsPreconnected V)
    (x y : ℂ) (hx : (quad c)^[n] x ∈ V) (hy : y ∈ U)
    (hreg : ∀ k < n, (quad c)^[k] c ≠ y) :
    (∑ D ∈ mergerCensus c n U V x y, (localFiber c n D y).card) =
      2 ^ componentReflectionRank c V n x := by
  rw [mergerCensus_fiber_partition c n U V hUV x y hy]
  exact quadratic_component_regular_degree c V hVo hVc n x hx y (hUV hy) hreg

/-- If all old components have the same reflection rank, the exact
number of merged components times their common degree is the enlarged
degree. In particular this is not merely a pair-collision criterion. -/
theorem mergerCensus_uniform_rank_count (c : ℂ) (n : ℕ) (U V : Set ℂ)
    (hUV : U ⊆ V) (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hVo : IsOpen V) (hVc : IsPreconnected V)
    (x y : ℂ) (hx : (quad c)^[n] x ∈ V) (hy : y ∈ U)
    (hreg : ∀ k < n, (quad c)^[k] c ≠ y) (d : ℕ)
    (hr : ∀ a ∈ connectedComponentIn ((quad c)^[n] ⁻¹' V) x,
      (quad c)^[n] a ∈ U → componentReflectionRank c U n a = d) :
    (mergerCensus c n U V x y).card * 2^d =
      2 ^ componentReflectionRank c V n x := by
  classical
  have hdeg (D : Set ℂ) (hD : D ∈ mergerCensus c n U V x y) :
      (localFiber c n D y).card = 2^d := by
    obtain ⟨a, haB, haU, rfl⟩ :=
      (mem_mergerCensus c n U V hUV hUo hUc x y hy D).mp hD
    rw [quadratic_component_regular_degree c U hUo hUc n a haU y hy hreg,
      hr a haB haU]
  have he := Finset.sum_const_nat hdeg
  rw [← he]
  exact mergerCensus_degree_conservation c n U V hUV hVo hVc x y hx hy hreg

/-- At arbitrary old and enlarged ranks, completeness of a declared
family can be certified by the enlarged regular degree rather than
a separately enumerated global fiber. -/
theorem mergerCensus_complete_iff_degree (c : ℂ) (n : ℕ) (U V : Set ℂ)
    (hUV : U ⊆ V) (hVo : IsOpen V) (hVc : IsPreconnected V)
    (x y : ℂ) (hx : (quad c)^[n] x ∈ V) (hy : y ∈ U)
    (hreg : ∀ k < n, (quad c)^[k] c ≠ y)
    (T : Finset (Set ℂ)) (hT : T ⊆ mergerCensus c n U V x y) :
    T = mergerCensus c n U V x y ↔
      (∑ D ∈ T, (localFiber c n D y).card) = 2 ^ componentReflectionRank c V n x := by
  rw [← quadratic_component_regular_degree c V hVo hVc n x hx y (hUV hy) hreg]
  exact mergerCensus_complete_iff_mass c n U V hUV x y hy T hT

end
end LoopsQuadraticEnlargementDegree

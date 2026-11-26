import PrimeEndSectorImpressions

/-!
# Critical-cycle exclusion and exact external footprint transport

The complex maps below are the archive's actual quadratic iterates.
The native puzzle and angular chart interfaces remain hypotheses.
-/

namespace LoopsDecorationCriticalCycle

open Set
open QuadraticEscape LoopsSaturatedTelescope

/-- Surjectivity around a cycle propagates a noninjective return to every
phase. No injectivity of the intermediate arrows is needed. -/
theorem quadratic_phase_return_noninjective (c : ℂ) (i j : ℕ)
    (A B : Set ℂ) (hAB : orbit c i '' A = B)
    (hBA : orbit c j '' B = A)
    (hA : ¬ InjOn (orbit c (i+j)) A) :
    ¬ InjOn (orbit c (j+i)) B := by
  intro hB
  have hg : InjOn (orbit c j) B := by
    intro u hu v hv h
    apply hB hu hv
    rw [quadratic_orbit_add, quadratic_orbit_add, h]
  have hf : InjOn (orbit c i) A := by
    intro x hx y hy h
    have hx' : x ∈ orbit c j '' B := by rw [hBA]; exact hx
    have hy' : y ∈ orbit c j '' B := by rw [hBA]; exact hy
    obtain ⟨u, hu, hux⟩ := hx'
    obtain ⟨v, hv, hvy⟩ := hy'
    have huv : u = v := by
      apply hB hu hv
      rw [quadratic_orbit_add, quadratic_orbit_add, hux, hvy, h]
    exact hux.symm.trans ((congrArg (orbit c j) huv).trans hvy)
  apply hA
  intro x hx y hy h
  apply hf hx hy
  have hx' : orbit c i x ∈ B := by
    rw [← hAB]
    exact ⟨x, hx, rfl⟩
  have hy' : orbit c i y ∈ B := by
    rw [← hAB]
    exact ⟨y, hy, rfl⟩
  apply hg hx' hy'
  simpa only [quadratic_orbit_add] using h

/-- A collision in a return persists under every later quadratic iterate,
even when the original set is not invariant. -/
theorem quadratic_noninjective_persists (c : ℂ) (S : Set ℂ)
    (p N : ℕ) (hle : p ≤ N) (hp : ¬ InjOn (orbit c p) S) :
    ¬ InjOn (orbit c N) S := by
  intro hN
  apply hp
  intro x hx y hy h
  apply hN hx hy
  have htime : N = p + (N-p) := by omega
  rw [htime, quadratic_orbit_add, quadratic_orbit_add, h]

/-- A connected continuum that avoids a closed puzzle frontier cannot
meet both the puzzle and its exterior. -/
theorem preconnected_avoids_frontier {X : Type*} [TopologicalSpace X]
    (Q B : Set X) (hQ : IsClosed Q) (hB : IsPreconnected B)
    (hfront : Disjoint B (frontier Q)) (hmeet : (Q ∩ B).Nonempty) :
    B ⊆ interior Q := by
  have hcov : B ⊆ interior Q ∪ Qᶜ := by
    intro x hx
    by_cases hq : x ∈ Q
    · left
      by_contra hi
      have hb : x ∈ frontier Q := by
        change x ∈ closure Q ∧ x ∉ interior Q
        exact ⟨subset_closure hq, hi⟩
      exact Set.disjoint_left.mp hfront hx hb
    · exact Or.inr hq
  have hd : Disjoint (interior Q) Qᶜ := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact hy (interior_subset hx)
  rcases IsPreconnected.subset_or_subset isOpen_interior
    hQ.isOpen_compl hd hcov hB with h | h
  · exact h
  · obtain ⟨x, hxQ, hxB⟩ := hmeet
    exact False.elim (h hxB hxQ)

/-- Every injective sufficiently deep physical cylinder excludes the
entire connected phase of the critical cycle, provided its frontier
misses that phase. The transport of noninjectivity is proved above. -/
theorem quadratic_cycle_phase_exclusion (c : ℂ) (i j N : ℕ)
    (A B Q : Set ℂ) (hAB : orbit c i '' A = B)
    (hBA : orbit c j '' B = A)
    (hA : ¬ InjOn (orbit c (i+j)) A)
    (hdepth : j+i ≤ N) (hQ : IsClosed Q)
    (hB : IsPreconnected B) (hfront : Disjoint B (frontier Q))
    (hinj : InjOn (orbit c N) Q) : Disjoint Q B := by
  apply Set.disjoint_left.mpr
  intro x hxQ hxB
  have hsub : B ⊆ Q :=
    (preconnected_avoids_frontier Q B hQ hB hfront ⟨x, hxQ, hxB⟩).trans
      interior_subset
  have hn := quadratic_noninjective_persists c B (j+i) N hdepth
    (quadratic_phase_return_noninjective c i j A B hAB hBA hA)
  apply hn
  intro u hu v hv he
  exact hinj (hsub hu) (hsub hv) he

/-- The filled locus is defined by the archive's actual escape potential,
whose zero locus has already been identified with bounded orbits. -/
def filledLocus (c : ℂ) : Set ℂ := {z | escape c z = 0}

/-- The exact physical exterior trace commutes with every quadratic
iterate, without any injectivity or local connectivity assumption. -/
theorem quadratic_exterior_image (c : ℂ) (n : ℕ) (Q : Set ℂ) :
    orbit c n '' (Q \\ filledLocus c) = (orbit c n '' Q) \\ filledLocus c := by
  have hz (z : ℂ) : orbit c n z ∈ filledLocus c ↔ z ∈ filledLocus c := by
    change escape c (orbit c n z) = 0 ↔ escape c z = 0
    rw [escape_iterate]
    constructor
    · intro h
      exact (mul_eq_zero.mp h).resolve_left (by positivity)
    · intro h
      rw [h, mul_zero]
  apply Subset.antisymm
  · rintro y ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx.1, rfl⟩, fun h => hx.2 ((hz x).mp h)⟩
  · rintro y ⟨⟨x, hx, rfl⟩, hy⟩
    exact ⟨x, ⟨hx, fun h => hy ((hz x).mpr h)⟩, rfl⟩

/-- A single injective angular branch on the initial footprint, mapping
every deeper footprint onto the corresponding target, induces an exact
bijection of the limiting footprints. No compactness or limit exchange
is needed; uniqueness in the initial footprint identifies all lifts. -/
theorem nested_angular_bijOn {X Y : Type*} (D : X → Y)
    (A : ℕ → Set X) (B : ℕ → Set Y)
    (ha : Antitone A) (hinj : InjOn D (A 0))
    (hmap : ∀ n, D '' A n = B n) :
    BijOn D (⋂ n, A n) (⋂ n, B n) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    apply mem_iInter.mpr
    intro n
    rw [← hmap n]
    exact ⟨x, mem_iInter.mp hx n, rfl⟩
  · intro x hx y hy h
    exact hinj (mem_iInter.mp hx 0) (mem_iInter.mp hy 0) h
  · intro y hy
    have hy0 : y ∈ D '' A 0 := by rw [hmap 0]; exact mem_iInter.mp hy 0
    obtain ⟨x, hx0, hxy⟩ := hy0
    refine ⟨x, mem_iInter.mpr (fun n => ?_), hxy⟩
    have hyn : y ∈ D '' A n := by rw [hmap n]; exact mem_iInter.mp hy n
    obtain ⟨z, hz, hzy⟩ := hyn
    have hzx : z = x := hinj (ha (Nat.zero_le n) hz) hx0 (hzy.trans hxy.symm)
    simpa only [hzx] using hz

/-- Two retained target angles obstruct ordinary whole-trace cofinality
at every source center, and the source angles are obtained by the
limiting branch rather than posited separately. -/
theorem nested_angular_obstruction_transfer {X Y : Type*} [MetricSpace X]
    (D : X → Y) (A : ℕ → Set X) (B : ℕ → Set Y) (H : ℕ → ℝ)
    (ha : Antitone A) (hinj : InjOn D (A 0))
    (hmap : ∀ n, D '' A n = B n) (hp : ∀ n, 0 < H n)
    (u v : Y) (hne : u ≠ v) (hu : u ∈ ⋂ n, B n) (hv : v ∈ ⋂ n, B n) :
    ∀ θ, ¬ PrimeEndSectorFilters.Cofinal A H θ := by
  obtain ⟨_, _, hsurj⟩ := nested_angular_bijOn D A B ha hinj hmap
  obtain ⟨x, hx, hxu⟩ := hsurj hu
  obtain ⟨y, hy, hyv⟩ := hsurj hv
  have hxy : x ≠ y := by
    intro h
    apply hne
    exact hxu.symm.trans ((congrArg D h).trans hyv)
  exact PrimeEndSectorFilters.two_angles_obstruct A H hp hxy hx hy

end LoopsDecorationCriticalCycle

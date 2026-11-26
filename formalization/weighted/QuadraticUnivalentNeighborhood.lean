import SaturatedTelescope

/-!
# Open univalent neighborhoods of actual quadratic compacta

Injectivity on a compact set and avoidance of every preterminal critical
encounter extend to injectivity on an open neighborhood. The proof uses
the exact reflected-pair description of quadratic collisions and compact
separation, and does not posit an inverse branch on a neighborhood.
-/

namespace LoopsQuadraticUnivalentNeighborhood

open Set QuadraticEscape LoopsSaturatedTelescope

/-- A compact set on which one quadratic step is injective has an open
univalent neighborhood if it avoids the critical point. -/
theorem quadratic_step_univalent_neighborhood (c : ℂ) (C : Set ℂ)
    (hC : IsCompact C) (hI : InjOn (fun z : ℂ => z^2+c) C)
    (hzero : ∀ z ∈ C, z ≠ 0) :
    ∃ U : Set ℂ, IsOpen U ∧ C ⊆ U ∧ InjOn (fun z : ℂ => z^2+c) U := by
  have hneg : IsCompact ((fun z : ℂ => -z) '' C) := hC.image continuous_neg
  have hdis : Disjoint C ((fun z : ℂ => -z) '' C) := by
    apply Set.disjoint_left.mpr
    rintro z hz ⟨w, hw, hwz⟩
    have heq : w^2+c = z^2+c := by
      rw [← hwz]
      ring
    have hw_eq : w = z := hI hw hz heq
    have hz0 : z = 0 := by
      rw [hw_eq] at hwz
      linear_combination (-1/2 : ℂ) * hwz
    exact hzero z hz hz0
  obtain ⟨U, V, hU, hV, hCU, hCV, hUV⟩ :=
    normal_separation hC.isClosed hneg.isClosed hdis
  refine ⟨U ∩ (fun z : ℂ => -z) ⁻¹' V, hU.inter (hV.preimage continuous_neg), ?_, ?_⟩
  · intro z hz
    exact ⟨hCU hz, hCV ⟨z, hz, rfl⟩⟩
  · intro z hz w hw heq
    rcases (quadratic_eq_iff c z w).mp heq with hzw | hzw
    · exact hzw
    · have hzV : z ∈ V := by
        rw [hzw]
        exact hw.2
      exact False.elim (Set.disjoint_left.mp hUV hz.1 hzV)

/-- Compact injectivity and absence of all preterminal visits to zero
produce one open domain on which the actual full iterate is injective.
No neighborhood injectivity or critical-value exclusion is assumed. -/
theorem quadratic_compact_univalent_neighborhood (c : ℂ) (n : ℕ) (C : Set ℂ)
    (hC : IsCompact C) (hI : InjOn (orbit c n) C)
    (hcrit : ∀ x ∈ C, ∀ j < n, orbit c j x ≠ 0) :
    ∃ U : Set ℂ, IsOpen U ∧ C ⊆ U ∧ InjOn (orbit c n) U := by
  induction n with
  | zero =>
    exact ⟨univ, isOpen_univ, subset_univ C, fun _ _ _ _ h => h⟩
  | succ n ih =>
    have hprefix : InjOn (orbit c n) C := by
      intro x hx y hy hxy
      apply hI hx hy
      change (orbit c n x)^2+c = (orbit c n y)^2+c
      rw [hxy]
    obtain ⟨U, hU, hCU, hIU⟩ :=
      ih hprefix (fun x hx j hj => hcrit x hx j (by omega))
    have himage : IsCompact (orbit c n '' C) :=
      hC.image (quadratic_orbit_continuous c n)
    have hstep : InjOn (fun z : ℂ => z^2+c) (orbit c n '' C) := by
      rintro z ⟨x, hx, rfl⟩ w ⟨y, hy, rfl⟩ heq
      have hxy : x = y := hI hx hy heq
      rw [hxy]
    have hzero : ∀ z ∈ orbit c n '' C, z ≠ 0 := by
      rintro z ⟨x, hx, rfl⟩
      exact hcrit x hx n (by omega)
    obtain ⟨V, hV, hCV, hIV⟩ :=
      quadratic_step_univalent_neighborhood c (orbit c n '' C) himage hstep hzero
    refine ⟨U ∩ orbit c n ⁻¹' V,
      hU.inter (hV.preimage (quadratic_orbit_continuous c n)), ?_, ?_⟩
    · intro x hx
      exact ⟨hCU hx, hCV ⟨x, hx, rfl⟩⟩
    · intro x hx y hy heq
      exact hIU hx.1 hy.1 (hIV hx.2 hy.2 heq)

/-- The open univalent neighborhood can be confined to any prescribed
open ambient set containing the compact spine. -/
theorem quadratic_compact_univalent_neighborhood_within (c : ℂ) (n : ℕ)
    (C W : Set ℂ) (hC : IsCompact C) (hW : IsOpen W) (hCW : C ⊆ W)
    (hI : InjOn (orbit c n) C)
    (hcrit : ∀ x ∈ C, ∀ j < n, orbit c j x ≠ 0) :
    ∃ U : Set ℂ, IsOpen U ∧ C ⊆ U ∧ U ⊆ W ∧ InjOn (orbit c n) U := by
  obtain ⟨U, hU, hCU, hIU⟩ :=
    quadratic_compact_univalent_neighborhood c n C hC hI hcrit
  exact ⟨U ∩ W, hU.inter hW, fun x hx => ⟨hCU hx, hCW hx⟩,
    inter_subset_right, hIU.mono inter_subset_left⟩

end LoopsQuadraticUnivalentNeighborhood

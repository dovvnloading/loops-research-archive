import FiberSamplePacking

/-!
# Connected fibers force sampling energy

Connectedness is used only through the intermediate value theorem for a
distance function. A finite cover must witness many separated radial
levels. Those witnesses are distinct sample indices, and a fixed
proportion of the levels remain far from any proposed center.

The theorem is independent of quadratic dynamics. Applying it to
parameter fibers requires proving the stated connectedness and sampling
hypotheses for the actual fibers.
-/

namespace Loops.FiberSampling

open Set

/-- A connected set covered by finitely many radius-`r` sample balls
cannot have large diameter and small unnormalized quadratic sample
energy simultaneously. The center need not lie in the connected set
and the samples need not lie there either. -/
theorem connected_cubic_energy_bound
    {X I : Type*} [PseudoMetricSpace X] [Fintype I]
    (K : Set X) (hK : IsPreconnected K) (s : I → X) (a : X)
    (r : ℝ) (hr : 0 < r)
    (hcover : ∀ z ∈ K, ∃ i, dist z (s i) ≤ r)
    (x y : X) (hx : x ∈ K) (hy : y ∈ K)
    (hscale : r ≤ dist x y / 8) :
    dist x y ^ 3 ≤ 1024 * r * energy s a := by
  classical
  let D : ℝ := dist x y
  have hD : 0 ≤ D := dist_nonneg
  have hscale' : r ≤ D / 8 := hscale
  have hend : ∃ b ∈ K, ∃ c ∈ K,
      dist b c = D ∧ D / 2 ≤ dist b a := by
    by_cases h : D / 2 ≤ dist x a
    · exact ⟨x, hx, y, hy, rfl, h⟩
    · refine ⟨y, hy, x, hx, ?_, ?_⟩
      · exact dist_comm y x
      · have ht := dist_triangle x a y
        rw [dist_comm a y] at ht
        change D ≤ dist x a + dist y a at ht
        linarith
  obtain ⟨b, hb, c, hc, hbc, hba⟩ := hend
  let N : ℕ := ⌊D / (16 * r)⌋₊
  have hden : 0 < 16 * r := by positivity
  have hN : (N : ℝ) * (16 * r) ≤ D := by
    apply (le_div_iff₀ hden).mp
    exact Nat.floor_le (div_nonneg hD hden.le)
  have hNsucc : D < ((N : ℝ) + 1) * (16 * r) := by
    apply (div_lt_iff₀ hden).mp
    exact Nat.lt_floor_add_one (D / (16 * r))
  have hlevel_bound (j : Fin (N + 1)) :
      4 * r * (j.val : ℝ) ≤ D / 4 := by
    have hj : (j.val : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast Nat.le_of_lt_succ j.isLt
    have hm := mul_le_mul_of_nonneg_left hj
      (by positivity : 0 ≤ 4 * r)
    nlinarith only [hm, hN]
  have hpoints (j : Fin (N + 1)) :
      ∃ z ∈ K, dist b z = 4 * r * (j.val : ℝ) := by
    have hlevel : 4 * r * (j.val : ℝ) ∈
        Icc (dist b b) (dist b c) := by
      constructor
      · rw [dist_self]
        positivity
      · rw [hbc]
        have hj := hlevel_bound j
        linarith
    exact hK.intermediate_value hb hc
      (f := fun z : X => dist b z)
      (continuous_const.dist continuous_id).continuousOn hlevel
  choose p hpK hpdist using hpoints
  have hsep (i j : Fin (N + 1)) (hij : i ≠ j) :
      2 * r < dist (p i) (p j) := by
    have hne : i.val ≠ j.val := fun he => hij (Fin.ext he)
    rcases lt_or_gt_of_ne hne with hij' | hji'
    · have hijR : (i.val : ℝ) + 1 ≤ (j.val : ℝ) := by
        exact_mod_cast Nat.succ_le_of_lt hij'
      have ht := dist_triangle b (p i) (p j)
      rw [hpdist i, hpdist j] at ht
      have hm := mul_le_mul_of_nonneg_left hijR
        (by positivity : 0 ≤ 4 * r)
      nlinarith only [ht, hm, hr]
    · have hjiR : (j.val : ℝ) + 1 ≤ (i.val : ℝ) := by
        exact_mod_cast Nat.succ_le_of_lt hji'
      have ht := dist_triangle b (p j) (p i)
      rw [hpdist i, hpdist j, dist_comm (p j) (p i)] at ht
      have hm := mul_le_mul_of_nonneg_left hjiR
        (by positivity : 0 ≤ 4 * r)
      nlinarith only [ht, hm, hr]
  obtain ⟨f, hfi, hfnear⟩ := exists_injective_samples p s r hsep
    (fun j => hcover (p j) (hpK j))
  have hfar (j : Fin (N + 1)) :
      D / 8 ≤ dist (s (f j)) a := by
    have hpbound := hlevel_bound j
    have hnear := hfnear j
    have ht1 := dist_triangle b (p j) a
    have ht2 := dist_triangle (p j) (s (f j)) a
    rw [hpdist j] at ht1
    linarith
  have hE := packing_energy_lower_bound s a f hfi (D / 8)
    (div_nonneg hD (by norm_num)) hfar
  simp only [Fintype.card_fin, Nat.cast_add, Nat.cast_one] at hE
  have hE' : ((N : ℝ) + 1) * D ^ 2 ≤ 64 * energy s a := by
    nlinarith only [hE]
  have hprod := mul_le_mul_of_nonneg_right hNsucc.le (sq_nonneg D)
  have hprodE := mul_le_mul_of_nonneg_left hE'
    (by positivity : 0 ≤ 16 * r)
  change D ^ 3 ≤ 1024 * r * energy s a
  nlinarith only [hprod, hprodE]

/-- A certified finite upper bound on sampling energy supplies a
stopping test at any prescribed positive pair-distance tolerance. -/
theorem finite_energy_certificate
    {X I : Type*} [PseudoMetricSpace X] [Fintype I]
    (K : Set X) (hK : IsPreconnected K) (s : I → X) (a : X)
    (r δ B : ℝ) (hr : 0 < r) (hδ : 0 < δ)
    (hscale : r ≤ δ / 8)
    (hcover : ∀ z ∈ K, ∃ i, dist z (s i) ≤ r)
    (henergy : energy s a ≤ B)
    (hbudget : 1024 * r * B < δ ^ 3) :
    ∀ x ∈ K, ∀ y ∈ K, dist x y < δ := by
  intro x hx y hy
  by_contra hnot
  have hlarge : δ ≤ dist x y := le_of_not_gt hnot
  have hscale' : r ≤ dist x y / 8 := by linarith
  have hbound := connected_cubic_energy_bound K hK s a r hr
    hcover x y hx hy hscale'
  have henergy' : 1024 * r * energy s a ≤ 1024 * r * B :=
    mul_le_mul_of_nonneg_left henergy (by positivity)
  have hpoly : 0 ≤ dist x y ^ 2 + dist x y * δ + δ ^ 2 :=
    add_nonneg
      (add_nonneg (sq_nonneg _) (mul_nonneg dist_nonneg hδ.le))
      (sq_nonneg _)
  have hcubic : δ ^ 3 ≤ dist x y ^ 3 := by
    have hm := mul_nonneg (sub_nonneg.mpr hlarge) hpoly
    nlinarith only [hm]
  linarith

/-- An actual enclosure by cells and a radius bound throughout each
cell imply the covering premise. This theorem does not assert that
a proposed list of cells encloses an unspecified geometric set. -/
theorem sample_cover_of_enclosing_cells
    {X I : Type*} [PseudoMetricSpace X]
    (K : Set X) (cell : I → Set X) (s : I → X) (r : ℝ)
    (henclose : K ⊆ ⋃ i, cell i)
    (hcell : ∀ i, ∀ z ∈ cell i, dist z (s i) ≤ r) :
    ∀ z ∈ K, ∃ i, dist z (s i) ≤ r := by
  intro z hz
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (henclose hz)
  exact ⟨i, hcell i z hi⟩

/-- The complete finite stopping interface: enclosure, cell radius
bounds, and an upper energy budget certify the requested tolerance. -/
theorem finite_cell_energy_certificate
    {X I : Type*} [PseudoMetricSpace X] [Fintype I]
    (K : Set X) (hK : IsPreconnected K)
    (cell : I → Set X) (s : I → X) (a : X)
    (r δ B : ℝ) (hr : 0 < r) (hδ : 0 < δ)
    (hscale : r ≤ δ / 8)
    (henclose : K ⊆ ⋃ i, cell i)
    (hcell : ∀ i, ∀ z ∈ cell i, dist z (s i) ≤ r)
    (henergy : energy s a ≤ B)
    (hbudget : 1024 * r * B < δ ^ 3) :
    ∀ x ∈ K, ∀ y ∈ K, dist x y < δ :=
  finite_energy_certificate K hK s a r δ B hr hδ hscale
    (sample_cover_of_enclosing_cells K cell s r henclose hcell)
    henergy hbudget


end Loops.FiberSampling

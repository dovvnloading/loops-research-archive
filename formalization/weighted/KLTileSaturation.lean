import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Exact central saturation and retained collars in logarithmic tiles

The first coordinate is the marked angle, with all integer translates
retained. The second coordinate is positive exterior height. Puzzle
height and carrier height are deliberately different parameters.

These are coordinate theorems. Physical projections and their dynamical
identities are treated separately in `ChebyshevDecoration`.
-/

namespace LoopsKLTileSaturation

open Set

/-- The full universal-cover tile retains every winding sheet. -/
def tile (H : ℝ) : Set (ℝ × ℝ) := {z | 0 < z.2 ∧ z.2 < H}

/-- The central gluing seam of a single marked component. -/
def seam (a b h : ℝ) : Set (ℝ × ℝ) :=
  {z | a < z.1 ∧ z.1 < b ∧ 0 < z.2 ∧ z.2 < h}

/-- A source tile truncates only the height of the target seam. -/
theorem tile_inter_seam (H A B t : ℝ) :
    tile H ∩ seam A B t = seam A B (min H t) := by
  ext z
  simp only [tile, seam, mem_inter_iff, mem_setOf_eq, lt_min_iff]
  tauto

/-- A nondegenerate seam contains its explicit midpoint. -/
theorem seam_midpoint (a b h : ℝ) (hab : a < b) (hh : 0 < h) :
    ((a + b) / 2, h / 2) ∈ seam a b h := by
  dsimp [seam]
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

/-- The full overlap equation has an exact endpoint and height
criterion. Strict angular enlargement cannot be repaired by changing
only the carrier height. -/
theorem full_saturation_iff (H a b h A B t : ℝ)
    (hab : a < b) (hh : 0 < h) (hhH : h ≤ H) (hht : h ≤ t)
    (hAa : A ≤ a) (hbB : b ≤ B) :
    tile H ∩ seam A B t = seam a b h ↔
      a = A ∧ b = B ∧ h = min H t := by
  constructor
  · intro heq
    have ha : a = A := by
      apply le_antisymm _ hAa
      by_contra! hlt
      have hz : ((A + a) / 2, h / 2) ∈ tile H ∩ seam A B t := by
        dsimp [tile, seam]
        constructor
        · constructor <;> linarith
        · constructor
          · linarith
          constructor
          · linarith
          constructor <;> linarith
      rw [heq] at hz
      have hx := hz.1
      dsimp at hx
      linarith
    have hb : b = B := by
      apply le_antisymm hbB
      by_contra! hlt
      have hz : ((b + B) / 2, h / 2) ∈ tile H ∩ seam A B t := by
        dsimp [tile, seam]
        constructor
        · constructor <;> linarith
        · constructor
          · linarith
          constructor
          · linarith
          constructor <;> linarith
      rw [heq] at hz
      have hx := hz.2.1
      dsimp at hx
      linarith
    have hheight : h = min H t := by
      apply le_antisymm (le_min hhH hht)
      by_contra! hlt
      have hH := min_le_left H t
      have ht := min_le_right H t
      have hz : ((a + b) / 2, (h + min H t) / 2) ∈
          tile H ∩ seam A B t := by
        dsimp [tile, seam]
        constructor
        · constructor <;> linarith
        · constructor
          · linarith
          constructor
          · linarith
          constructor <;> linarith
      rw [heq] at hz
      have hy := hz.2.2.2
      dsimp at hy
      linarith
    exact ⟨ha, hb, hheight⟩
  · rintro ⟨rfl, rfl, hhmin⟩
    rw [tile_inter_seam, ← hhmin]

/-- Every positive full-angular inner collar retains the angular
obstruction. Once both central heights exceed the collar height,
reflection is equivalent to equality of the angular footprints. -/
theorem full_angular_collar_saturation_iff (δ a b h A B t : ℝ)
    (hab : a < b) (hδ : 0 < δ) (hδh : δ ≤ h) (hht : h ≤ t)
    (hAa : A ≤ a) (hbB : b ≤ B) :
    tile δ ∩ seam A B t = tile δ ∩ seam a b h ↔
      a = A ∧ b = B := by
  have hδt : δ ≤ t := hδh.trans hht
  rw [tile_inter_seam δ a b h, min_eq_left hδh]
  rw [full_saturation_iff δ a b δ A B t hab hδ le_rfl hδt hAa hbB]
  simp [min_eq_left hδt]

/-- The defect has three exact channels: the left angular enlargement,
the right angular enlargement, and excess height. Endpoint equalities
are retained because the seams are open. -/
theorem saturation_defect_exact (H a b h A B t : ℝ) :
    (tile H ∩ seam A B t) \ seam a b h =
      {z | z ∈ tile H ∩ seam A B t ∧
        (z.1 ≤ a ∨ b ≤ z.1 ∨ h ≤ z.2)} := by
  ext z
  simp only [mem_diff, mem_setOf_eq]
  constructor
  · rintro ⟨hz, hnot⟩
    refine ⟨hz, ?_⟩
    have hpos : 0 < z.2 := hz.1.1
    by_contra! hn
    exact hnot ⟨hn.1, hn.2.1, hpos, hn.2.2⟩
  · rintro ⟨hz, hbad⟩
    refine ⟨hz, ?_⟩
    intro hs
    rcases hbad with hleft | hright | hheight
    · exact (not_lt_of_ge hleft) hs.1
    · exact (not_lt_of_ge hright) hs.2.1
    · exact (not_lt_of_ge hheight) hs.2.2.2

/-- A retained set restores central reflection exactly when it avoids
the computed defect. This permits angular trimming as well as height
trimming, without silently discarding any retained point. -/
theorem retained_saturation_iff (C : Set (ℝ × ℝ))
    (H a b h A B t : ℝ) (hCH : C ⊆ tile H)
    (hAa : A ≤ a) (hbB : b ≤ B) (hht : h ≤ t) :
    C ∩ seam A B t = C ∩ seam a b h ↔
      Disjoint C ((tile H ∩ seam A B t) \ seam a b h) := by
  constructor
  · intro heq
    apply Set.disjoint_left.mpr
    intro z hzC hzD
    have hzS : z ∈ C ∩ seam a b h := by
      rw [← heq]
      exact ⟨hzC, hzD.1.2⟩
    exact hzD.2 hzS.2
  · intro hd
    ext z
    constructor
    · rintro ⟨hzC, hzT⟩
      refine ⟨hzC, ?_⟩
      by_contra hn
      exact Set.disjoint_left.mp hd hzC ⟨⟨hCH hzC, hzT⟩, hn⟩
    · rintro ⟨hzC, hzS⟩
      exact ⟨hzC, lt_of_le_of_lt hAa hzS.1,
        lt_of_lt_of_le hzS.2.1 hbB, hzS.2.2.1,
        lt_of_lt_of_le hzS.2.2.2 hht⟩

/-- The ordinary direct left and right branches both miss the same
target angular channel. The height is arbitrary, not a finite sample. -/
theorem direct_branch_angular_defect (h t : ℝ) (hh : 0 < h)
    (ht : 0 < t) (hth : t < h) :
    ((1 / 4 : ℝ), t) ∈ tile (2 * h) ∩ seam (1 / 6) (1 / 3) (4 * h) ∧
      ((1 / 4 : ℝ), t) ∉ seam (7 / 24) (1 / 3) h ∧
      ((1 / 4 : ℝ), t) ∉ seam (1 / 6) (5 / 24) h := by
  constructor
  · dsimp [tile, seam]
    constructor
    · exact ⟨ht, by linarith⟩
    · exact ⟨by norm_num, by norm_num, ht, by linarith⟩
  constructor
  · intro hz
    have hx := hz.1
    norm_num at hx
  · intro hz
    have hx := hz.2.1
    norm_num at hx

/-- Every positive full-angular collar contains a strictly positive
height witness against both direct-branch saturation equations. -/
theorem direct_branch_defect_in_every_collar (h δ : ℝ)
    (hh : 0 < h) (hδ : 0 < δ) :
    ∃ t : ℝ, 0 < t ∧ t < δ ∧
      ((1 / 4 : ℝ), t) ∈ tile (2 * h) ∩ seam (1 / 6) (1 / 3) (4 * h) ∧
      ((1 / 4 : ℝ), t) ∉ seam (7 / 24) (1 / 3) h ∧
      ((1 / 4 : ℝ), t) ∉ seam (1 / 6) (5 / 24) h := by
  let t := min h δ / 2
  have hp : 0 < min h δ := lt_min hh hδ
  have hth : t < h := by dsimp [t]; linarith [min_le_left h δ]
  have htδ : t < δ := by dsimp [t]; linarith [min_le_right h δ]
  have ht : 0 < t := by dsimp [t]; linarith
  exact ⟨t, ht, htδ, direct_branch_angular_defect h t hh ht hth⟩

/-- There is also an interior radial defect on the source's own
angular footprint. It is distinct from the angular collar obstruction. -/
theorem direct_branch_radial_defect (h : ℝ) (hh : 0 < h) :
    ((5 / 16 : ℝ), 3 * h / 2) ∈
      tile (2 * h) ∩ seam (1 / 6) (1 / 3) (4 * h) ∧
      ((5 / 16 : ℝ), 3 * h / 2) ∉ seam (7 / 24) (1 / 3) h := by
  constructor
  · dsimp [tile, seam]
    constructor
    · constructor <;> linarith
    · exact ⟨by norm_num, by norm_num, by linarith, by linarith⟩
  · intro hz
    have hy := hz.2.2.2
    dsimp at hy
    linarith

end LoopsKLTileSaturation

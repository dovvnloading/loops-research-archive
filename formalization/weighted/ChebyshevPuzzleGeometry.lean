import ChebyshevDecoration
import LogarithmicTileGeometry
import Mathlib.Analysis.Convex.Contractible
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

/-!
# Topological disks in the actual Chebyshev dynamical plane

Signed-height rectangles include the real spine. The physical
Joukowski-exponential chart is an open embedding on every rectangle
whose angular closure stays inside one half turn. Its compact closed
rectangle is embedded as well, retaining all boundary points.
-/

namespace LoopsChebyshevPuzzleGeometry

open Set Topology LoopsChebyshevDecoration LoopsLogarithmicTileGeometry

noncomputable section

/-- Angle-height coordinates, with the full unwrapped real angle. -/
def logCoord : (ℝ × ℝ) ≃ₜ ℂ where
  toFun u := (u.2 : ℂ) + ((2 * Real.pi * u.1 : ℝ) : ℂ) * Complex.I
  invFun z := (z.im / (2 * Real.pi), z.re)
  left_inv u := by
    apply Prod.ext
    · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
        Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one,
        mul_zero, zero_add, add_zero]
      field_simp [Real.pi_ne_zero] <;> ring
    · simp
  right_inv z := by
    change (z.re : ℂ) + ((2 * Real.pi * (z.im / (2 * Real.pi)) : ℝ) : ℂ) *
      Complex.I = z
    have hcancel : 2 * Real.pi * (z.im / (2 * Real.pi)) = z.im := by
      field_simp [Real.pi_ne_zero]
    rw [hcancel]
    exact Complex.re_add_im z
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

def signedRectangle (a b r : ℝ) : Set (ℝ × ℝ) :=
  Ioo a b ×ˢ Ioo (-r) r

def closedSignedRectangle (a b r : ℝ) : Set (ℝ × ℝ) :=
  Icc a b ×ˢ Icc (-r) r

def closedPuzzle (a b r : ℝ) : Set ℂ :=
  (fun u : ℝ × ℝ => point u.1 u.2) '' closedSignedRectangle a b r

/-- The concrete point map is continuous on the whole coordinate
plane, including height zero. -/
theorem point_pair_continuous :
    Continuous (fun u : ℝ × ℝ => point u.1 u.2) := by
  exact joukowski_exp_continuous.comp logCoord.continuous_toFun

/-- The physical point map is globally open. -/
theorem point_pair_isOpenMap :
    IsOpenMap (fun u : ℝ × ℝ => point u.1 u.2) := by
  exact joukowski_exp_isOpenMap.comp logCoord.isOpenMap

/-- The previously defined physical puzzle is the image of its whole
signed rectangle, not only its exterior sectors. -/
theorem puzzle_eq_rectangle_image (a b r : ℝ) :
    puzzle a b r =
      (fun u : ℝ × ℝ => point u.1 u.2) '' signedRectangle a b r := by
  ext z
  constructor
  · rintro ⟨theta, t, ha, hb, ht, hr, he⟩
    exact ⟨(theta, t), ⟨⟨ha, hb⟩, ⟨ht, hr⟩⟩, he⟩
  · rintro ⟨u, ⟨⟨ha, hb⟩, ⟨ht, hr⟩⟩, he⟩
    exact ⟨u.1, u.2, ha, hb, ht, hr, he⟩

/-- Actual puzzle domains are open in the physical complex plane. -/
theorem puzzle_isOpen (a b r : ℝ) : IsOpen (puzzle a b r) := by
  rw [puzzle_eq_rectangle_image]
  exact point_pair_isOpenMap _ (isOpen_Ioo.prod isOpen_Ioo)

/-- The whole geometric puzzle, including its ray and height edges,
is compact. -/
theorem closedPuzzle_isCompact (a b r : ℝ) :
    IsCompact (closedPuzzle a b r) :=
  (isCompact_Icc.prod isCompact_Icc).image point_pair_continuous

/-- Closed geometric edges cannot be omitted when testing whether a
point lies outside the source puzzle. -/
theorem closure_puzzle_subset (a b r : ℝ) :
    closure (puzzle a b r) ⊆ closedPuzzle a b r := by
  apply closure_minimal ?_ (closedPuzzle_isCompact a b r).isClosed
  rw [puzzle_eq_rectangle_image]
  apply image_mono
  intro u hu
  exact ⟨⟨hu.1.1.le, hu.1.2.le⟩, ⟨hu.2.1.le, hu.2.2.le⟩⟩

/-- The embedded closed rectangle is exactly the physical closure
of the open puzzle domain. -/
theorem puzzle_closure_eq_closedPuzzle (a b r : ℝ)
    (hab : a < b) (hr : 0 < r) :
    closure (puzzle a b r) = closedPuzzle a b r := by
  apply Subset.antisymm (closure_puzzle_subset a b r)
  have hrect : closure (signedRectangle a b r) = closedSignedRectangle a b r := by
    simp only [signedRectangle, closedSignedRectangle, closure_prod_eq,
      closure_Ioo hab.ne, closure_Ioo (show -r ≠ r by linarith)]
  change (fun u : ℝ × ℝ => point u.1 u.2) '' closedSignedRectangle a b r ⊆ _
  rw [← hrect, puzzle_eq_rectangle_image]
  exact image_closure_subset_closure_image point_pair_continuous

/-- The physical map embeds the complete open signed rectangle. -/
theorem signed_rectangle_open_embedding (a b r : ℝ)
    (ha : 0 ≤ a) (hb : b ≤ 1/2) :
    IsOpenEmbedding
      (fun u : signedRectangle a b r => point u.val.1 u.val.2) := by
  apply IsOpenEmbedding.of_continuous_injective_isOpenMap
    (point_pair_continuous.comp continuous_subtype_val)
  · intro u v he
    apply Subtype.ext
    obtain ⟨hangle, hheight⟩ := point_injective_half_turn
      (ha.trans_lt u.property.1.1) (u.property.1.2.trans_le hb)
      (ha.trans_lt v.property.1.1) (v.property.1.2.trans_le hb) he
    exact Prod.ext hangle hheight
  · exact point_pair_isOpenMap.comp
      (isOpen_Ioo.prod isOpen_Ioo).isOpenMap_subtype_val

/-- Every nonempty ordinary puzzle rectangle in the half-turn chart
gives a simply connected physical domain. -/
theorem puzzle_isSimplyConnected (a b r : ℝ)
    (ha : 0 ≤ a) (hb : b ≤ 1/2) (hab : a < b) (hr : 0 < r) :
    IsSimplyConnected (puzzle a b r) := by
  have hne : (signedRectangle a b r).Nonempty := by
    refine ⟨((a + b) / 2, 0), ?_⟩
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, hr⟩⟩
  have hc : Convex ℝ (signedRectangle a b r) :=
    (convex_Ioo a b).prod (convex_Ioo (-r) r)
  letI : ContractibleSpace (signedRectangle a b r) := hc.contractibleSpace hne
  let f : signedRectangle a b r → ℂ := fun u => point u.val.1 u.val.2
  have hf : IsEmbedding f := (signed_rectangle_open_embedding a b r ha hb).isEmbedding
  have hrange : range f = puzzle a b r := by
    ext z
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨u.val.1, u.val.2, u.property.1.1, u.property.1.2,
        u.property.2.1, u.property.2.2, rfl⟩
    · rintro ⟨theta, t, hta, htb, htr, hrt, rfl⟩
      exact ⟨⟨(theta, t), ⟨⟨hta, htb⟩, ⟨htr, hrt⟩⟩⟩, rfl⟩
  let e : signedRectangle a b r ≃ₜ puzzle a b r :=
    hf.toHomeomorph.trans (Homeomorph.setCongr hrange)
  exact e.toHomotopyEquiv.simplyConnectedSpace_iff.mp inferInstance

/-- The complete compact rectangle embeds, so the image's boundary
cannot identify different sides or vertices of this rectangle. -/
theorem closed_rectangle_embedding (a b r : ℝ)
    (ha : 0 < a) (hb : b < 1/2) :
    IsClosedEmbedding
      (fun u : closedSignedRectangle a b r => point u.val.1 u.val.2) := by
  have hc : IsCompact (closedSignedRectangle a b r) :=
    isCompact_Icc.prod isCompact_Icc
  letI : CompactSpace (closedSignedRectangle a b r) :=
    isCompact_iff_compactSpace.mp hc
  apply (point_pair_continuous.comp continuous_subtype_val).isClosedEmbedding
  intro u v he
  apply Subtype.ext
  obtain ⟨hangle, hheight⟩ := point_injective_half_turn
    (ha.trans_le u.property.1.1) (u.property.1.2.trans_lt hb)
    (ha.trans_le v.property.1.1) (v.property.1.2.trans_lt hb) he
  exact Prod.ext hangle hheight

/-- The actual quarter-angle point misses both closed direct-branch
puzzles, at every signed height. Thus the overlap defect also survives
the closed geometric-piece convention. -/
theorem quarter_outside_branch_closures (h t : ℝ) :
    point (1/4) t ∉ closure (leftDomain h) ∧
      point (1/4) t ∉ closure (rightDomain h) := by
  constructor
  · intro hmem
    obtain ⟨u, hu, he⟩ := closure_puzzle_subset (7/24) (1/3) (h/8) hmem
    obtain ⟨ha, _⟩ := point_injective_half_turn
      (by norm_num : (0 : ℝ) < 1/4) (by norm_num : (1/4 : ℝ) < 1/2)
      (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 7/24) hu.1.1)
      (lt_of_le_of_lt hu.1.2 (by norm_num : (1/3 : ℝ) < 1/2)) he.symm
    linarith [hu.1.1]
  · intro hmem
    obtain ⟨u, hu, he⟩ := closure_puzzle_subset (1/6) (5/24) (h/8) hmem
    obtain ⟨ha, _⟩ := point_injective_half_turn
      (by norm_num : (0 : ℝ) < 1/4) (by norm_num : (1/4 : ℝ) < 1/2)
      (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1/6) hu.1.1)
      (lt_of_le_of_lt hu.1.2 (by norm_num : (5/24 : ℝ) < 1/2)) he.symm
    linarith [hu.1.2]

end
end LoopsChebyshevPuzzleGeometry

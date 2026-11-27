import ChebyshevFibers
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Analysis.Complex.Convex

/-!
# Based logarithmic tile lifts

The exterior Chebyshev projection is the actual analytic map
`z ↦ J (Complex.exp z)`. On the positive-real-part side, its reciprocal
fiber alternative is impossible. The usual uniqueness of a based
covering lift then recovers the entire tile inclusion from its physical
projection and one anchor. Coordinate identity is a conclusion.
-/

namespace LoopsLogarithmicTileLift

open Set Function LoopsChebyshev

noncomputable section

/-- An annular universal tile in logarithmic coordinates. -/
def logarithmicTile (H : ℝ) : Set ℂ :=
  {z | 0 < z.re ∧ z.re < H}

/-- The tile is preconnected even when its height makes it empty. -/
theorem logarithmicTile_preconnected (H : ℝ) :
    IsPreconnected (logarithmicTile H) := by
  exact ((convex_halfSpace_re_gt 0).inter
    (convex_halfSpace_re_lt H)).isPreconnected

/-- Equality of exterior physical images recovers equality of the
exponential coordinates. The reciprocal alternative belongs to the
opposite side of the unit circle. -/
theorem joukowski_exp_eq_iff {z w : ℂ} (hz : 0 < z.re) (hw : 0 < w.re) :
    J (Complex.exp z) = J (Complex.exp w) ↔ Complex.exp z = Complex.exp w := by
  constructor
  · intro h
    apply exterior_joukowski_injective ?_ ?_ h
    · rw [Complex.norm_exp]
      exact Real.one_lt_exp_iff.mpr hz
    · rw [Complex.norm_exp]
      exact Real.one_lt_exp_iff.mpr hw
  · exact congrArg J

/-- The complete exterior logarithmic fiber retains the integer deck
coordinate; no quotient of that coordinate is taken. -/
theorem joukowski_exp_fiber {z w : ℂ} (hz : 0 < z.re) (hw : 0 < w.re) :
    J (Complex.exp z) = J (Complex.exp w) ↔
      ∃ k : ℤ, z = w + k * (2 * Real.pi * Complex.I) := by
  rw [joukowski_exp_eq_iff hz hw, Complex.exp_eq_exp_iff_exists_int]

/-- This is the covering uniqueness theorem specialized to the
exponential projection, allowing any preconnected source set. -/
theorem exponential_lifts_eqOn (S : Set ℂ) (hS : IsPreconnected S)
    (L M : ℂ → ℂ) (hL : ContinuousOn L S) (hM : ContinuousOn M S)
    (hp : ∀ z ∈ S, Complex.exp (L z) = Complex.exp (M z))
    (a : ℂ) (ha : a ∈ S) (haLM : L a = M a) :
    EqOn L M S := by
  apply Complex.isCoveringMap_exp.eqOn_of_comp_eqOn hS hL hM
    (a := a) ?_ ha haLM
  intro z hz
  exact Subtype.ext (hp z hz)

/-- A continuous exponential lift of the identity has one constant
integer deck displacement throughout a connected tile. -/
theorem exponential_lift_constant_deck (S : Set ℂ) (hS : IsPreconnected S)
    (L : ℂ → ℂ) (hL : ContinuousOn L S)
    (hp : ∀ z ∈ S, Complex.exp (L z) = Complex.exp z)
    (a : ℂ) (ha : a ∈ S) :
    ∃ k : ℤ, ∀ z ∈ S, L z = z + k * (2 * Real.pi * Complex.I) := by
  obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.mp (hp a ha)
  refine ⟨k, ?_⟩
  apply exponential_lifts_eqOn S hS L
    (fun z => z + k * (2 * Real.pi * Complex.I)) hL
    (continuous_id.add continuous_const).continuousOn ?_ a ha hk
  intro z hz
  apply (hp z hz).trans
  symm
  exact Complex.exp_eq_exp_iff_exists_int.mpr ⟨k, rfl⟩

/-- Commutation with the physical exterior projection permits only a
single constant deck displacement on the entire connected source. -/
theorem joukowski_lift_constant_deck (S : Set ℂ) (hS : IsPreconnected S)
    (L : ℂ → ℂ) (hL : ContinuousOn L S)
    (hsource : ∀ z ∈ S, 0 < z.re)
    (htarget : ∀ z ∈ S, 0 < (L z).re)
    (hp : ∀ z ∈ S, J (Complex.exp (L z)) = J (Complex.exp z))
    (a : ℂ) (ha : a ∈ S) :
    ∃ k : ℤ, ∀ z ∈ S, L z = z + k * (2 * Real.pi * Complex.I) := by
  exact exponential_lift_constant_deck S hS L hL
    (fun z hz => (joukowski_exp_eq_iff (htarget z hz) (hsource z hz)).mp (hp z hz))
    a ha

/-- A based lift commuting with the physical Joukowski projection is
forced to agree with the identity throughout its preconnected source.
The positivity hypotheses specify the genuine exterior sheets. -/
theorem joukowski_based_lift_eqOn (S : Set ℂ) (hS : IsPreconnected S)
    (L : ℂ → ℂ) (hL : ContinuousOn L S)
    (hsource : ∀ z ∈ S, 0 < z.re)
    (htarget : ∀ z ∈ S, 0 < (L z).re)
    (hp : ∀ z ∈ S, J (Complex.exp (L z)) = J (Complex.exp z))
    (a : ℂ) (ha : a ∈ S) (hanchor : L a = a) :
    EqOn L id S := by
  apply exponential_lifts_eqOn S hS L id hL continuous_id.continuousOn
    (fun z hz => (joukowski_exp_eq_iff (htarget z hz) (hsource z hz)).mp (hp z hz))
    a ha hanchor

/-- For an actual map between logarithmic tiles, continuity, equality
of physical projections, and one based anchor determine its entire
coordinate map. No identity formula for the map is an input. -/
theorem logarithmicTile_based_lift_eqOn (H H' : ℝ)
    (L : ℂ → ℂ) (hL : ContinuousOn L (logarithmicTile H))
    (hmap : MapsTo L (logarithmicTile H) (logarithmicTile H'))
    (hp : ∀ z ∈ logarithmicTile H,
      J (Complex.exp (L z)) = J (Complex.exp z))
    (a : ℂ) (ha : a ∈ logarithmicTile H) (hanchor : L a = a) :
    EqOn L id (logarithmicTile H) := by
  exact joukowski_based_lift_eqOn (logarithmicTile H)
    (logarithmicTile_preconnected H) L hL
    (fun _ hz => hz.1) (fun z hz => (hmap hz).1) hp a ha hanchor

end
end LoopsLogarithmicTileLift

import KLTileSaturation
import ChebyshevDecoration
import LogarithmicTileLift
import ChebyshevPuzzleGeometry

/-!
# Full overlap failure for based physical Chebyshev tile lifts

The tile map is arbitrary: it is recovered from its continuity,
commutation with the physical projection, and one based anchor.
Every positive full-angular collar then contains the explicit defect.
-/

namespace LoopsChebyshevTileSaturation

open Set Function LoopsKLTileSaturation LoopsChebyshevDecoration
open LoopsLogarithmicTileLift LoopsChebyshev

noncomputable section

/-- Convert a marked angle and height to an unquotiented logarithm. -/
def logCoord (p : ℝ × ℝ) : ℂ :=
  (p.2 : ℂ) + ((2 * Real.pi * p.1 : ℝ) : ℂ) * Complex.I

/-- A single central seam in the full logarithmic tile. -/
def logSeam (a b h : ℝ) : Set ℂ := logCoord '' seam a b h

theorem logCoord_re (p : ℝ × ℝ) : (logCoord p).re = p.2 := by
  simp [logCoord]

theorem logCoord_im (p : ℝ × ℝ) : (logCoord p).im = 2 * Real.pi * p.1 := by
  simp [logCoord]

/-- The unquotiented coordinate retains its full sheet label. -/
theorem logCoord_injective : Injective logCoord := by
  intro p q he
  have ht := congrArg Complex.re he
  have ha := congrArg Complex.im he
  rw [logCoord_re, logCoord_re] at ht
  rw [logCoord_im, logCoord_im] at ha
  have hθ : p.1 = q.1 :=
    mul_left_cancel₀ (show (2 * Real.pi : ℝ) ≠ 0 by positivity) ha
  exact Prod.ext hθ ht

theorem logCoord_mem_logSeam (p : ℝ × ℝ) (a b h : ℝ) :
    logCoord p ∈ logSeam a b h ↔ p ∈ seam a b h := by
  constructor
  · rintro ⟨q, hq, he⟩
    exact (logCoord_injective he) ▸ hq
  · intro hp
    exact ⟨p, hp, rfl⟩

/-- The coordinate's projection is the genuine quadratic-plane point. -/
theorem logCoord_physical (theta t : ℝ) :
    J (Complex.exp (logCoord (theta, t))) = point theta t := rfl

/-- Any based physical inclusion lift has a defect in every positive
full-angular collar. Both direct seams fail, with the same physical
point in the parent and outside both whole source puzzle domains. -/
theorem based_lift_collar_defect (h δ : ℝ) (hh : 0 < h) (hδ : 0 < δ)
    (L : ℂ → ℂ) (hL : ContinuousOn L (logarithmicTile (h/4)))
    (hmap : MapsTo L (logarithmicTile (h/4)) (logarithmicTile h))
    (hp : ∀ z ∈ logarithmicTile (h/4),
      J (Complex.exp (L z)) = J (Complex.exp z))
    (a : ℂ) (ha : a ∈ logarithmicTile (h/4)) (hanchor : L a = a) :
    ∃ t : ℝ, 0 < t ∧ t < δ ∧ t < h/8 ∧
      logCoord (1/4, t) ∈ logarithmicTile (h/4) ∧
      L (logCoord (1/4, t)) ∈ logSeam (1/6) (1/3) (h/2) ∧
      logCoord (1/4, t) ∉ logSeam (7/24) (1/3) (h/8) ∧
      logCoord (1/4, t) ∉ logSeam (1/6) (5/24) (h/8) ∧
      J (Complex.exp (L (logCoord (1/4, t)))) ∈ parentDomain h ∧
      J (Complex.exp (L (logCoord (1/4, t)))) ∉ leftDomain h ∧
      J (Complex.exp (L (logCoord (1/4, t)))) ∉ rightDomain h := by
  obtain ⟨t, ht, htδ, hth, _, _, _, _⟩ :=
    arbitrarily_thin_physical_overlap_defect hh hδ
  obtain ⟨hparent, hleft, hright⟩ := quarter_whole_domain_defect hh ht hth
  have hz : logCoord (1/4, t) ∈ logarithmicTile (h/4) := by
    change 0 < (logCoord (1/4, t)).re ∧ (logCoord (1/4, t)).re < h/4
    rw [logCoord_re]
    exact ⟨ht, by linarith⟩
  have heq : L (logCoord (1/4, t)) = logCoord (1/4, t) :=
    logarithmicTile_based_lift_eqOn (h/4) h L hL hmap hp a ha hanchor hz
  refine ⟨t, ht, htδ, hth, hz, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [heq, logCoord_mem_logSeam]
    exact ⟨by norm_num, by norm_num, ht, by linarith⟩
  · rw [logCoord_mem_logSeam]
    intro hs
    have hbad := hs.1
    norm_num at hbad
  · rw [logCoord_mem_logSeam]
    intro hs
    have hbad := hs.2.1
    norm_num at hbad
  · simpa only [heq, logCoord_physical] using hparent
  · simpa only [heq, logCoord_physical] using hleft
  · simpa only [heq, logCoord_physical] using hright

/-- The exact full-reflection equation fails even after intersection
with an arbitrarily thin positive-height full-angular collar. -/
theorem based_lift_collar_reflection_fails (h δ : ℝ) (hh : 0 < h) (hδ : 0 < δ)
    (L : ℂ → ℂ) (hL : ContinuousOn L (logarithmicTile (h/4)))
    (hmap : MapsTo L (logarithmicTile (h/4)) (logarithmicTile h))
    (hp : ∀ z ∈ logarithmicTile (h/4),
      J (Complex.exp (L z)) = J (Complex.exp z))
    (a : ℂ) (ha : a ∈ logarithmicTile (h/4)) (hanchor : L a = a) :
    logarithmicTile (min δ (h/4)) ∩ L ⁻¹' logSeam (1/6) (1/3) (h/2) ≠
      logarithmicTile (min δ (h/4)) ∩ logSeam (7/24) (1/3) (h/8) ∧
    logarithmicTile (min δ (h/4)) ∩ L ⁻¹' logSeam (1/6) (1/3) (h/2) ≠
      logarithmicTile (min δ (h/4)) ∩ logSeam (1/6) (5/24) (h/8) := by
  obtain ⟨t, ht, htδ, hth, hz, htarget, hleft, hright, _⟩ :=
    based_lift_collar_defect h δ hh hδ L hL hmap hp a ha hanchor
  have hcollar : logCoord (1/4, t) ∈ logarithmicTile (min δ (h/4)) := by
    change 0 < (logCoord (1/4, t)).re ∧
      (logCoord (1/4, t)).re < min δ (h/4)
    rw [logCoord_re]
    exact ⟨ht, lt_min htδ (by linarith)⟩
  have hmem : logCoord (1/4, t) ∈
      logarithmicTile (min δ (h/4)) ∩ L ⁻¹' logSeam (1/6) (1/3) (h/2) :=
    ⟨hcollar, htarget⟩
  constructor
  · intro he
    rw [he] at hmem
    exact hleft hmem.2
  · intro he
    rw [he] at hmem
    exact hright hmem.2

/-- A concrete unconditional instance: the ordinary inclusion of
logarithmic tiles. Its witnesses project outside the entire source
puzzle domains, including their real central intervals. -/
theorem ordinary_inclusion_counterexample (h δ : ℝ) (hh : 0 < h) (hδ : 0 < δ) :
    ∃ z : ℂ,
      z ∈ logarithmicTile (min δ (h/4)) ∧
      z ∈ logSeam (1/6) (1/3) (h/2) ∧
      z ∉ logSeam (7/24) (1/3) (h/8) ∧
      z ∉ logSeam (1/6) (5/24) (h/8) ∧
      J (Complex.exp z) ∈ parentDomain h ∧
      J (Complex.exp z) ∉ closure (leftDomain h) ∧
      J (Complex.exp z) ∉ closure (rightDomain h) ∧
      J (Complex.exp z) ∉ LoopsParabolic.realSegment 2 := by
  obtain ⟨t, ht, htδ, hth, _, _, _, hext⟩ :=
    arbitrarily_thin_physical_overlap_defect hh hδ
  obtain ⟨hp, _, _⟩ := quarter_whole_domain_defect hh ht hth
  obtain ⟨hl, hr⟩ := LoopsChebyshevPuzzleGeometry.quarter_outside_branch_closures h t
  refine ⟨logCoord (1/4, t), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change 0 < (logCoord (1/4, t)).re ∧
      (logCoord (1/4, t)).re < min δ (h/4)
    rw [logCoord_re]
    exact ⟨ht, lt_min htδ (by linarith)⟩
  · rw [logCoord_mem_logSeam]
    exact ⟨by norm_num, by norm_num, ht, by linarith⟩
  · rw [logCoord_mem_logSeam]
    intro hs
    have hbad := hs.1
    norm_num at hbad
  · rw [logCoord_mem_logSeam]
    intro hs
    have hbad := hs.2.1
    norm_num at hbad
  · simpa only [logCoord_physical] using hp
  · simpa only [logCoord_physical] using hl
  · simpa only [logCoord_physical] using hr
  · simpa only [logCoord_physical] using hext

/-- The ordinary inclusion is a nonvacuous member of the based-lift
class, with its anchor in the left branch's actual gluing seam. -/
theorem ordinary_inclusion_is_based_lift (h : ℝ) (hh : 0 < h) :
    ContinuousOn (id : ℂ → ℂ) (logarithmicTile (h/4)) ∧
      MapsTo (id : ℂ → ℂ) (logarithmicTile (h/4)) (logarithmicTile h) ∧
      logCoord (5/16, h/16) ∈ logarithmicTile (h/4) ∧
      logCoord (5/16, h/16) ∈ logSeam (7/24) (1/3) (h/8) ∧
      (∀ z ∈ logarithmicTile (h/4),
        J (Complex.exp (id z)) = J (Complex.exp z)) ∧
      id (logCoord (5/16, h/16)) = logCoord (5/16, h/16) := by
  refine ⟨continuous_id.continuousOn, ?_, ?_, ?_, by intros; rfl, rfl⟩
  · intro z hz
    exact ⟨hz.1, by change z.re < h; linarith [hz.2]⟩
  · change 0 < (logCoord (5/16, h/16)).re ∧
      (logCoord (5/16, h/16)).re < h/4
    rw [logCoord_re]
    constructor <;> linarith
  · rw [logCoord_mem_logSeam]
    exact ⟨by norm_num, by norm_num, by linarith, by linarith⟩

/-- The defect is independent of open-versus-closed seam conventions.
Any source gluing sets projecting into the closed source pieces fail
reflection against a target overlap containing the parent open seam.
This also allows either source seam's finite boundary points. -/
theorem based_lift_closed_piece_reflection_fails (h δ : ℝ)
    (hh : 0 < h) (hδ : 0 < δ)
    (L : ℂ → ℂ) (hL : ContinuousOn L (logarithmicTile (h/4)))
    (hmap : MapsTo L (logarithmicTile (h/4)) (logarithmicTile h))
    (hp : ∀ z ∈ logarithmicTile (h/4),
      J (Complex.exp (L z)) = J (Complex.exp z))
    (a : ℂ) (ha : a ∈ logarithmicTile (h/4)) (hanchor : L a = a)
    (SL SR T : Set ℂ)
    (hSL : MapsTo (fun z => J (Complex.exp z)) SL (closure (leftDomain h)))
    (hSR : MapsTo (fun z => J (Complex.exp z)) SR (closure (rightDomain h)))
    (hT : logSeam (1/6) (1/3) (h/2) ⊆ T) :
    logarithmicTile (min δ (h/4)) ∩ L ⁻¹' T ≠
      logarithmicTile (min δ (h/4)) ∩ SL ∧
    logarithmicTile (min δ (h/4)) ∩ L ⁻¹' T ≠
      logarithmicTile (min δ (h/4)) ∩ SR := by
  obtain ⟨t, ht, htδ, hth, _, htarget, _, _, _⟩ :=
    based_lift_collar_defect h δ hh hδ L hL hmap hp a ha hanchor
  have hcollar : logCoord (1/4, t) ∈ logarithmicTile (min δ (h/4)) := by
    change 0 < (logCoord (1/4, t)).re ∧
      (logCoord (1/4, t)).re < min δ (h/4)
    rw [logCoord_re]
    exact ⟨ht, lt_min htδ (by linarith)⟩
  have hmem : logCoord (1/4, t) ∈
      logarithmicTile (min δ (h/4)) ∩ L ⁻¹' T := ⟨hcollar, hT htarget⟩
  obtain ⟨hleft, hright⟩ :=
    LoopsChebyshevPuzzleGeometry.quarter_outside_branch_closures h t
  constructor
  · intro he
    rw [he] at hmem
    have hbad := hSL hmem.2
    exact hleft hbad
  · intro he
    rw [he] at hmem
    have hbad := hSR hmem.2
    exact hright hbad

end

end LoopsChebyshevTileSaturation

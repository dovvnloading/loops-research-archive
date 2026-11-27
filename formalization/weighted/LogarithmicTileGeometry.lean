import ChebyshevFibers
import Mathlib.Analysis.Complex.OpenMapping

/-!
# Analytic geometry of the physical logarithmic projection

The same entire function describes both positive and negative signed
heights. Its global openness turns open logarithmic puzzle rectangles
into open subsets of the actual complex dynamical plane.
-/

namespace LoopsLogarithmicTileGeometry

open Set Topology LoopsChebyshev

noncomputable section

/-- The physical Chebyshev projection is entire across height zero. -/
theorem joukowski_exp_analytic :
    AnalyticOnNhd ℂ (fun z : ℂ => J (Complex.exp z)) univ := by
  have hd : Differentiable ℂ (fun z : ℂ => J (Complex.exp z)) := fun z =>
    ((joukowski_hasDerivAt (Complex.exp_ne_zero z)).comp z
      (Complex.hasDerivAt_exp z)).differentiableAt
  exact hd.differentiableOn.analyticOnNhd isOpen_univ

/-- Continuity also holds across the physical real segment. -/
theorem joukowski_exp_continuous :
    Continuous (fun z : ℂ => J (Complex.exp z)) := by
  exact continuous_iff_continuousAt.mpr fun z =>
    (joukowski_exp_analytic z (mem_univ z)).continuousAt

/-- Openness comes from the actual entire projection, including its
critical values; it is not imposed on a coordinate model. -/
theorem joukowski_exp_isOpenMap :
    IsOpenMap (fun z : ℂ => J (Complex.exp z)) := by
  rcases joukowski_exp_analytic.is_constant_or_isOpenMap with ⟨w, hw⟩ | ho
  · have he := (hw 0).trans (hw (Real.pi * Complex.I)).symm
    norm_num [J, Complex.exp_pi_mul_I] at he
  · exact ho

/-- Any open signed-height rectangle has an open physical image. -/
theorem joukowski_exp_image_open (U : Set ℂ) (hU : IsOpen U) :
    IsOpen ((fun z : ℂ => J (Complex.exp z)) '' U) :=
  joukowski_exp_isOpenMap U hU

/-- An injective signed-height chart is an open embedding into the
physical plane. The injectivity input may be checked on its exact
angular interval, rather than imposed on the whole periodic cover. -/
theorem joukowski_exp_open_embedding (U : Set ℂ) (hU : IsOpen U)
    (hinj : InjOn (fun z : ℂ => J (Complex.exp z)) U) :
    IsOpenEmbedding (fun z : U => J (Complex.exp (z : ℂ))) := by
  exact IsOpenEmbedding.of_continuous_injective_isOpenMap
    (joukowski_exp_continuous.comp continuous_subtype_val) hinj.injective
    (joukowski_exp_isOpenMap.comp hU.isOpenMap_subtype_val)

/-- Injection on a compact closed puzzle rectangle gives a closed
embedding of the whole rectangle, including all boundary points. -/
theorem joukowski_exp_compact_embedding (K : Set ℂ) (hK : IsCompact K)
    (hinj : InjOn (fun z : ℂ => J (Complex.exp z)) K) :
    IsClosedEmbedding (fun z : K => J (Complex.exp (z : ℂ))) := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  exact (joukowski_exp_continuous.comp continuous_subtype_val).isClosedEmbedding
    hinj.injective

end
end LoopsLogarithmicTileGeometry

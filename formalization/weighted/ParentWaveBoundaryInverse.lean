import ParentWaveRectangle
import Mathlib.Topology.Sequences
import Mathlib.Tactic

/-!
# The continuous inverse at the finite boundary of the parent chart

A continuous injective extension on the closed source has a continuous
inverse away from the common value approached at infinity.  This supplies
endpoint continuity for inverse images of closed rectangle crossings.
-/

namespace ParentWaveBoundaryInverse

open Set Function Filter Metric Bornology ParentWaveRectangle
open scoped Topology

noncomputable section

/-- Continuity at finite boundary points propagates a uniform infinite-end
limit from a source to its closure. -/
theorem uniformLimitAtInfinity_closure {f : ℂ → ℂ} {U : Set ℂ} {L : ℂ}
    (hcont : ContinuousOn f (closure U))
    (hinfty : UniformLimitAtInfinity f U L) :
    UniformLimitAtInfinity f (closure U) L := by
  intro ε hε
  obtain ⟨R,hR⟩ := hinfty (ε/2) (by positivity)
  refine ⟨R,?_⟩
  intro z hz hzR
  obtain ⟨u,hu,huz⟩ := mem_closure_iff_seq_limit.mp hz
  have hwithin : Tendsto u atTop (𝓝[closure U] z) :=
    tendsto_nhdsWithin_iff.mpr ⟨huz,
      Eventually.of_forall fun n => subset_closure (hu n)⟩
  have hfu : Tendsto (fun n => f (u n)) atTop (𝓝 (f z)) :=
    (hcont z hz).tendsto.comp hwithin
  have hfar : ∀ᶠ n in atTop, R < ‖u n‖ :=
    huz.eventually ((isOpen_lt continuous_const continuous_norm).mem_nhds hzR)
  have hball : f z ∈ closedBall L (ε/2) :=
    isClosed_closedBall.mem_of_tendsto hfu (hfar.mono fun n hn => (hR _ (hu n) hn).le)
  exact (mem_closedBall.mp hball).trans_lt (by linarith)

/-- Inverting a continuous injective closed-source map is continuous on
any part of its image that omits its uniform infinite-end value. -/
theorem continuousOn_invFunOn_of_uniformLimit {f : ℂ → ℂ} {S V : Set ℂ} {L : ℂ}
    (hS : IsClosed S) (hcont : ContinuousOn f S) (hinj : InjOn f S)
    (hinfty : UniformLimitAtInfinity f S L) (hV : V ⊆ f '' S) (hL : L ∉ V) :
    ContinuousOn (invFunOn f S) V := by
  rw [continuousOn_iff_continuous_restrict, continuous_iff_seqContinuous]
  intro v y hv
  apply tendsto_of_subseq_tendsto
  intro ns hns
  let z : ℕ → ℂ := fun n => invFunOn f S (v (ns n))
  have hz (n : ℕ) : z n ∈ S := invFunOn_mem (hV (v (ns n)).property)
  have hy : invFunOn f S y ∈ S := invFunOn_mem (hV y.property)
  have heq (n : ℕ) : f (z n) = v (ns n) := invFunOn_eq (hV (v (ns n)).property)
  have htarget : Tendsto (fun n => (v (ns n) : ℂ)) atTop (𝓝 (y : ℂ)) :=
    (continuous_subtype_val.tendsto y).comp (hv.comp hns)
  have hzy : Tendsto (fun n => f (z n)) atTop (𝓝 (y : ℂ)) := by
    simpa only [heq] using htarget
  have hyL : (y : ℂ) ≠ L := by
    intro he
    exact hL (he ▸ y.property)
  obtain ⟨R,hR⟩ := eventually_bounded_of_image_tendsto hinfty hyL hz hzy
  obtain ⟨x,_,φ,hφ,hφx⟩ :=
    tendsto_subseq_of_frequently_bounded (isBounded_closedBall (x := (0 : ℂ)) (r := R))
      hR.frequently
  have hx : x ∈ S := hS.mem_of_tendsto hφx (Eventually.of_forall fun n => hz (φ n))
  have hwithin : Tendsto (z ∘ φ) atTop (𝓝[S] x) :=
    tendsto_nhdsWithin_iff.mpr ⟨hφx, Eventually.of_forall fun n => hz (φ n)⟩
  have hfx : Tendsto (fun n => f (z (φ n))) atTop (𝓝 (f x)) :=
    (hcont x hx).tendsto.comp hwithin
  have hfy : Tendsto (fun n => f (z (φ n))) atTop (𝓝 (y : ℂ)) :=
    hzy.comp hφ.tendsto_atTop
  have hxy : x = invFunOn f S y :=
    hinj hx hy ((tendsto_nhds_unique hfx hfy).trans (invFunOn_eq (hV y.property)).symm)
  refine ⟨φ,?_⟩
  change Tendsto (fun n => invFunOn f S (v (ns (φ n)))) atTop
    (𝓝 (invFunOn f S y))
  simpa only [z, hxy, Function.comp_def] using hφx

/-- The form used by the parent chart: the infinite-end hypothesis is
required only in the open source, while the inverse includes finite sides. -/
theorem continuousOn_invFunOn_closure {f : ℂ → ℂ} {U V : Set ℂ} {L : ℂ}
    (hcont : ContinuousOn f (closure U)) (hinj : InjOn f (closure U))
    (hinfty : UniformLimitAtInfinity f U L) (hV : V ⊆ f '' closure U) (hL : L ∉ V) :
    ContinuousOn (invFunOn f (closure U)) V :=
  continuousOn_invFunOn_of_uniformLimit isClosed_closure hcont hinj
    (uniformLimitAtInfinity_closure hcont hinfty) hV hL

end

end ParentWaveBoundaryInverse

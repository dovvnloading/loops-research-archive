import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.MetricSpace.Sequences
import Mathlib.Topology.Connected.Clopen

/-!
# Recognizing the complete image of a conformal rectangle chart

A finite boundary extension and one uniform limit at infinity prevent
an interior target value from being lost at the source boundary. The
open image is consequently relatively closed in the connected target.
This module supplies the topological completion step for the explicit
parent condenser chart.
-/

namespace ParentWaveRectangle

open Set Function Filter Metric Bornology
open scoped Topology

noncomputable section

/-- Uniform convergence at the unbounded end of the specified source.
No values of the extension outside that source are constrained. -/
def UniformLimitAtInfinity (f : ℂ → ℂ) (U : Set ℂ) (L : ℂ) : Prop :=
  ∀ ε > 0, ∃ R : ℝ, ∀ z ∈ U, R < ‖z‖ → dist (f z) L < ε

/-- A target value different from the infinite-end value has bounded
preimages along every convergent source sequence. -/
theorem eventually_bounded_of_image_tendsto {f : ℂ → ℂ} {U : Set ℂ} {L y : ℂ}
    (hinfty : UniformLimitAtInfinity f U L) (hy : y ≠ L)
    {z : ℕ → ℂ} (hz : ∀ n, z n ∈ U)
    (hzy : Tendsto (fun n => f (z n)) atTop (𝓝 y)) :
    ∃ R : ℝ, ∀ᶠ n in atTop, z n ∈ closedBall (0 : ℂ) R := by
  have hd : 0 < dist y L := dist_pos.mpr hy
  have he : 0 < dist y L/3 := by positivity
  obtain ⟨R,hR⟩ := hinfty (dist y L/3) he
  refine ⟨R,?_⟩
  filter_upwards [hzy.eventually (ball_mem_nhds y he)] with n hn
  rw [mem_closedBall,dist_zero_right]
  by_contra hbad
  have hfar : R < ‖z n‖ := lt_of_not_ge hbad
  have hL := hR (z n) (hz n) hfar
  have hy' : dist (f (z n)) y < dist y L/3 := hn
  have htri := dist_triangle y (f (z n)) L
  rw [dist_comm y (f (z n))] at htri
  linarith

/-- Any finite target-cluster value outside the image of the finite
boundary and distinct from the infinite-end value is attained inside. -/
theorem mem_image_of_mem_closure {f : ℂ → ℂ} {U V : Set ℂ} {L y : ℂ}
    (hcont : ContinuousOn f (closure U))
    (hboundary : ∀ z ∈ closure U \ U, f z ∉ V)
    (hinfty : UniformLimitAtInfinity f U L) (hL : L ∉ V)
    (hy : y ∈ V) (hycl : y ∈ closure (f '' U)) : y ∈ f '' U := by
  obtain ⟨u,hu,huy⟩ := mem_closure_iff_seq_limit.mp hycl
  choose z hz hzu using hu
  have hzy : Tendsto (fun n => f (z n)) atTop (𝓝 y) := by
    simpa only [hzu] using huy
  have hyL : y ≠ L := by
    intro he
    exact hL (he ▸ hy)
  obtain ⟨R,hR⟩ := eventually_bounded_of_image_tendsto hinfty hyL hz hzy
  obtain ⟨x,_,φ,hφ,hφx⟩ :=
    tendsto_subseq_of_frequently_bounded (isBounded_closedBall (x := (0 : ℂ)) (r := R))
      hR.frequently
  have hxcl : x ∈ closure U :=
    isClosed_closure.mem_of_tendsto hφx
      (Eventually.of_forall (fun n => subset_closure (hz (φ n))))
  have hwithin : Tendsto (z ∘ φ) atTop (𝓝[closure U] x) :=
    tendsto_nhdsWithin_iff.mpr ⟨hφx,
      Eventually.of_forall (fun n => subset_closure (hz (φ n)))⟩
  have hfx : Tendsto (fun n => f (z (φ n))) atTop (𝓝 (f x)) :=
    (hcont x hxcl).tendsto.comp hwithin
  have hfy : Tendsto (fun n => f (z (φ n))) atTop (𝓝 y) :=
    hzy.comp hφ.tendsto_atTop
  have he : f x = y := tendsto_nhds_unique hfx hfy
  have hxU : x ∈ U := by
    by_contra hx
    exact (hboundary x ⟨hxcl,hx⟩) (he ▸ hy)
  exact ⟨x,hxU,he⟩

/-- The complete rectangle-image criterion. Openness is supplied by
the actual nonvanishing holomorphic derivative; all other hypotheses
refer to its literal extension, source, target, and infinite-end value. -/
theorem image_eq_of_boundary_and_infinity {f : ℂ → ℂ} {U V : Set ℂ} {L : ℂ}
    (hU : U.Nonempty) (hV : IsPreconnected V) (hmap : MapsTo f U V)
    (hopen : IsOpen (f '' U)) (hcont : ContinuousOn f (closure U))
    (hboundary : ∀ z ∈ closure U \ U, f z ∉ V)
    (hinfty : UniformLimitAtInfinity f U L) (hL : L ∉ V) : f '' U = V := by
  letI : PreconnectedSpace V := isPreconnected_iff_preconnectedSpace.mp hV
  have hpre : (Subtype.val ⁻¹' closure (f '' U) : Set V) =
      Subtype.val ⁻¹' (f '' U) := by
    ext y
    change (y : ℂ) ∈ closure (f '' U) ↔ (y : ℂ) ∈ f '' U
    exact ⟨mem_image_of_mem_closure hcont hboundary hinfty hL y.2,
      fun hy => subset_closure hy⟩
  have hclosed : IsClosed (Subtype.val ⁻¹' (f '' U) : Set V) := by
    rw [← hpre]
    exact isClosed_closure.preimage continuous_subtype_val
  have hopen' : IsOpen (Subtype.val ⁻¹' (f '' U) : Set V) :=
    hopen.preimage continuous_subtype_val
  have hnonempty : (Subtype.val ⁻¹' (f '' U) : Set V).Nonempty := by
    obtain ⟨z,hz⟩ := hU
    exact ⟨⟨f z,hmap hz⟩,z,hz,rfl⟩
  have hall := (show IsClopen (Subtype.val ⁻¹' (f '' U) : Set V) from
    ⟨hclosed,hopen'⟩).eq_univ hnonempty
  apply Subset.antisymm
  · rintro y ⟨z,hz,rfl⟩
    exact hmap hz
  · intro y hy
    have hmem : (⟨y,hy⟩ : V) ∈ (Subtype.val ⁻¹' (f '' U) : Set V) := by
      rw [hall]
      exact mem_univ _
    exact hmem

end
end ParentWaveRectangle

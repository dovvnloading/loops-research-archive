import QuadraticActualShadow

/-!
# Uniform quadratic flight limits through the critical coordinate origin

Reciprocal coordinates omit zero. The actual normalized orbit is exactly
zero there, so the estimates extend to the original coordinate. Bounded
partial sums then supply a fixed disk on which convergence is uniform.
-/

namespace QuadraticOriginalShadow

open QuadraticFlightJet QuadraticActualShadow LoopsQuadraticReciprocalFlight
open Filter
open scoped Topology

noncomputable section

theorem reciprocal_mobius_identity (u T : ℂ) (hu : u ≠ 0) :
    (u⁻¹-T)⁻¹ = u / (1-T*u) := by
  have h : u⁻¹-T = (1-T*u)/u := by field_simp [hu] <;> ring
  rw [h, inv_div]

/-- The actual orbit estimates extend uniformly through the omitted
reciprocal point because both the orbit and the limiting map fix zero. -/
theorem actual_original_uniform_limit
    (c x σ : ℕ → ℂ) (N : ℕ → ℕ) (K : Set ℂ) (T : ℂ)
    (hσ : ∀ k, σ k ≠ 0)
    (hx : ∀ k j, j < N k → orbit (c k) (x k) j ≠ 0)
    (δ : ℝ) (hδ : 0 < δ)
    (hsep : ∀ k v, v ∈ K → ∀ j, j ≤ N k →
      δ ≤ ‖driver (charge (c k) (x k) (σ k)) v j‖)
    (hsmall : ∀ k, energy (charge (c k) (x k) (σ k)) (N k) ≤ δ^2 / 16)
    (henergy : Tendsto (fun k => energy (charge (c k) (x k) (σ k)) (N k))
      atTop (𝓝 0))
    (hsum : Tendsto (fun k => ∑ j ∈ Finset.range (N k),
      charge (c k) (x k) (σ k) j) atTop (𝓝 T)) :
    TendstoUniformlyOn (fun k u =>
      (orbit (c k) (x k + σ k*u) (N k) - orbit (c k) (x k) (N k)) /
        transport (c k) (x k) (σ k) (N k))
      (fun u => u/(1-T*u)) atTop {u : ℂ | u = 0 ∨ u⁻¹ ∈ K} := by
  have hlim := actual_quadratic_mobius_uniform_limit c x σ N K T
    hσ hx δ hδ hsep hsmall henergy hsum
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hlim) ε hε] with k hk
  intro u hu
  by_cases hu0 : u = 0
  · subst u
    simpa using hε
  · have hK : u⁻¹ ∈ K := hu.resolve_left hu0
    simpa only [inv_inv, reciprocal_mobius_identity u T hu0] using hk u⁻¹ hK

/-- Bounded signed partial sums, not bounded absolute variation, give a
common disk for the geometric limit of actual quadratic flights. -/
theorem actual_mobius_uniform_disk
    (c x σ : ℕ → ℂ) (N : ℕ → ℕ) (T : ℂ)
    (hσ : ∀ k, σ k ≠ 0)
    (hx : ∀ k j, j < N k → orbit (c k) (x k) j ≠ 0)
    (B δ : ℝ) (hB : 0 ≤ B) (hδ : 0 < δ)
    (hpartial : ∀ k j, j ≤ N k →
      ‖∑ i ∈ Finset.range j, charge (c k) (x k) (σ k) i‖ ≤ B)
    (hsmall : ∀ k, energy (charge (c k) (x k) (σ k)) (N k) ≤ δ^2 / 16)
    (henergy : Tendsto (fun k => energy (charge (c k) (x k) (σ k)) (N k))
      atTop (𝓝 0))
    (hsum : Tendsto (fun k => ∑ j ∈ Finset.range (N k),
      charge (c k) (x k) (σ k) j) atTop (𝓝 T)) :
    TendstoUniformlyOn (fun k u =>
      (orbit (c k) (x k + σ k*u) (N k) - orbit (c k) (x k) (N k)) /
        transport (c k) (x k) (σ k) (N k))
      (fun u => u/(1-T*u)) atTop (Metric.closedBall 0 (1/(B+δ))) := by
  let K : Set ℂ := {v : ℂ | B+δ ≤ ‖v‖}
  have hsep : ∀ k v, v ∈ K → ∀ j, j ≤ N k →
      δ ≤ ‖driver (charge (c k) (x k) (σ k)) v j‖ := by
    intro k v hv j hj
    have hp := hpartial k j hj
    have ht := norm_add_le
      (v - ∑ i ∈ Finset.range j, charge (c k) (x k) (σ k) i)
      (∑ i ∈ Finset.range j, charge (c k) (x k) (σ k) i)
    rw [sub_add_cancel] at ht
    change B+δ ≤ ‖v‖ at hv
    dsimp [driver]
    linarith
  have hlim := actual_original_uniform_limit c x σ N K T hσ hx δ hδ
    hsep hsmall henergy hsum
  apply hlim.mono
  intro u hu
  by_cases hu0 : u = 0
  · exact Or.inl hu0
  · apply Or.inr
    have hpos : 0 < B+δ := by linarith
    have hnorm : ‖u‖ ≤ 1/(B+δ) := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hu
    have hm : ‖u‖*(B+δ) ≤ 1 := (le_div_iff₀ hpos).mp hnorm
    have hunorm : 0 < ‖u‖ := norm_pos_iff.mpr hu0
    have hi : B+δ ≤ 1/‖u‖ := (le_div_iff₀ hunorm).mpr (by nlinarith)
    change B+δ ≤ ‖u⁻¹‖
    simpa only [norm_inv, one_div] using hi

/-- The origin is also retained in the actual critical return: the limit
is the even rational map `z² / (1-T*z²)`, with its genuine value zero at zero. -/
theorem critical_original_uniform_limit
    (c s : ℕ → ℂ) (N : ℕ → ℕ) (K : Set ℂ) (T : ℂ)
    (hs : ∀ k, s k ≠ 0)
    (hx : ∀ k j, j < N k → orbit (c k) (c k) j ≠ 0)
    (δ : ℝ) (hδ : 0 < δ)
    (hsep : ∀ k v, v ∈ K → ∀ j, j ≤ N k →
      δ ≤ ‖driver (charge (c k) (c k) ((s k)^2)) v j‖)
    (hsmall : ∀ k, energy (charge (c k) (c k) ((s k)^2)) (N k) ≤ δ^2 / 16)
    (henergy : Tendsto (fun k => energy (charge (c k) (c k) ((s k)^2)) (N k))
      atTop (𝓝 0))
    (hsum : Tendsto (fun k => ∑ j ∈ Finset.range (N k),
      charge (c k) (c k) ((s k)^2) j) atTop (𝓝 T)) :
    TendstoUniformlyOn (fun k z =>
      (orbit (c k) (s k*z) (N k+1) - orbit (c k) 0 (N k+1)) /
        transport (c k) (c k) ((s k)^2) (N k))
      (fun z => z^2/(1-T*z^2)) atTop {z : ℂ | z = 0 ∨ (z^2)⁻¹ ∈ K} := by
  have hlim := actual_original_uniform_limit c c (fun k => (s k)^2)
    N K T (fun k => pow_ne_zero 2 (hs k)) hx δ hδ hsep hsmall henergy hsum
  have hcomp := hlim.comp (fun z : ℂ => z^2)
  have hdomain : (fun z : ℂ => z^2) ⁻¹' {u : ℂ | u = 0 ∨ u⁻¹ ∈ K} =
      {z : ℂ | z = 0 ∨ (z^2)⁻¹ ∈ K} := by
    ext z
    simp
  rw [hdomain] at hcomp
  apply hcomp.congr
  exact Eventually.of_forall (fun k z _ => by
    dsimp only [Function.comp_def]
    rw [← normalizedActualFlight_eval,
      critical_return_quotient (c k) (s k) z (N k) (hs k) (hx k)])

end
end QuadraticOriginalShadow

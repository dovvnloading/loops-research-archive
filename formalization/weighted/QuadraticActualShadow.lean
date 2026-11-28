import QuadraticFlightJet
import QuadraticReciprocalFlight

/-!
# Möbius limits of actual quadratic orbit flights

The coefficient sequence is the transported tangent charge of the literal
quadratic orbit. Every estimate below is stated for an actual quadratic
iterate, with its source and target normalization displayed explicitly.
-/

namespace QuadraticActualShadow

open Polynomial Filter
open scoped Topology
open QuadraticFlightJet LoopsQuadraticReciprocalFlight

noncomputable section

theorem flight_eval_eq_forward (a : ℕ → ℂ) (u : ℂ) (n : ℕ) :
    (flight a n).eval u = forward a u n := by
  induction n with
  | zero => simp [flight, forward]
  | succ n ih => simp [flight, forward, ih]

/-- The normalization used in the polynomial theorem is exactly the displayed
ratio of two actual orbit values and the transported tangent scale. -/
theorem normalizedActualFlight_eval (c x σ u : ℂ) (n : ℕ) :
    (normalizedActualFlight c x σ n).eval u =
      (orbit c (x + σ*u) n - orbit c x n) / transport c x σ n := by
  simp only [normalizedActualFlight, eval_mul, eval_C, eval_sub, eval_comp,
    eval_add, eval_X, iteratePoly_eval]
  rw [div_eq_mul_inv]
  ring

/-- Quantitative Möbius shadowing of the actual family `z ↦ z^2+c`.
There is no bound on the number of iterates or on the absolute charge sum. -/
theorem actual_quadratic_shadow (c x σ v : ℂ) (N : ℕ)
    (hσ : σ ≠ 0) (hx : ∀ j < N, orbit c x j ≠ 0)
    (δ : ℝ) (hδ : 0 < δ)
    (hsep : ∀ j ≤ N, δ ≤ ‖driver (charge c x σ) v j‖)
    (hE : energy (charge c x σ) N ≤ δ^2 / 16)
    (n : ℕ) (hn : n ≤ N) :
    ‖(orbit c (x + σ*v⁻¹) n - orbit c x n) / transport c x σ n -
        (driver (charge c x σ) v n)⁻¹‖ ≤
      (4 / δ^3) * energy (charge c x σ) n := by
  rw [← normalizedActualFlight_eval c x σ v⁻¹ n,
    normalizedActualFlight_eq_flight c x σ n hσ (fun j hj => hx j (by omega)),
    flight_eval_eq_forward]
  exact forward_mobius_shadow (charge c x σ) v N δ hδ hsep hE n hn

/-- Exact evaluation of the even critical pullback of an actual flight. -/
theorem critical_return_eval (c s z : ℂ) (n : ℕ) (hs : s ≠ 0)
    (hx : ∀ j < n, orbit c c j ≠ 0) :
    orbit c (s*z) (n+1) = orbit c 0 (n+1) +
      transport c c (s^2) n * (normalizedActualFlight c c (s^2) n).eval (z^2) := by
  have h := congrArg (fun P : ℂ[X] => P.eval z)
    (critical_return_identity c s n hs hx)
  simpa only [eval_comp, eval_mul, eval_C, eval_X, eval_add, eval_pow,
    iteratePoly_eval] using h

theorem critical_return_quotient (c s z : ℂ) (n : ℕ) (hs : s ≠ 0)
    (hx : ∀ j < n, orbit c c j ≠ 0) :
    (orbit c (s*z) (n+1) - orbit c 0 (n+1)) / transport c c (s^2) n =
      (normalizedActualFlight c c (s^2) n).eval (z^2) := by
  have ht := transport_ne_zero c c (s^2) n (pow_ne_zero 2 hs) hx
  apply (div_eq_iff ht).mpr
  rw [critical_return_eval c s z n hs hx]
  ring

/-- Finite shadowing stated directly at the critical point of the actual
quadratic family. The leading square is retained exactly. -/
theorem critical_return_shadow (c s z : ℂ) (n : ℕ) (hs : s ≠ 0)
    (hx : ∀ j < n, orbit c c j ≠ 0)
    (δ : ℝ) (hδ : 0 < δ)
    (hsep : ∀ j ≤ n, δ ≤ ‖driver (charge c c (s^2)) ((z^2)⁻¹) j‖)
    (hE : energy (charge c c (s^2)) n ≤ δ^2 / 16) :
    ‖(orbit c (s*z) (n+1) - orbit c 0 (n+1)) / transport c c (s^2) n -
        (driver (charge c c (s^2)) ((z^2)⁻¹) n)⁻¹‖ ≤
      (4 / δ^3) * energy (charge c c (s^2)) n := by
  rw [critical_return_quotient c s z n hs hx,
    normalizedActualFlight_eq_flight c c (s^2) n (pow_ne_zero 2 hs) hx,
    flight_eval_eq_forward]
  simpa only [inv_inv] using
    forward_mobius_shadow (charge c c (s^2)) ((z^2)⁻¹) n δ hδ hsep hE n le_rfl

/-- Small square sums force an actual quadratic orbit flight to converge to
a Möbius map when its partial-sum driver stays separated from its pole.
The parameters, starting points, scales and return times may all vary. -/
theorem actual_quadratic_mobius_limit
    (c x σ : ℕ → ℂ) (N : ℕ → ℕ) (v T : ℂ)
    (hσ : ∀ k, σ k ≠ 0)
    (hx : ∀ k j, j < N k → orbit (c k) (x k) j ≠ 0)
    (δ : ℝ) (hδ : 0 < δ)
    (hsep : ∀ k j, j ≤ N k →
      δ ≤ ‖driver (charge (c k) (x k) (σ k)) v j‖)
    (hsmall : ∀ k, energy (charge (c k) (x k) (σ k)) (N k) ≤ δ^2 / 16)
    (henergy : Tendsto (fun k => energy (charge (c k) (x k) (σ k)) (N k))
      atTop (𝓝 0))
    (hsum : Tendsto (fun k => ∑ j ∈ Finset.range (N k),
      charge (c k) (x k) (σ k) j) atTop (𝓝 T)) :
    Tendsto (fun k =>
      (orbit (c k) (x k + σ k*v⁻¹) (N k) - orbit (c k) (x k) (N k)) /
        transport (c k) (x k) (σ k) (N k)) atTop (𝓝 (v-T)⁻¹) := by
  let F : ℕ → ℂ := fun k =>
    (orbit (c k) (x k + σ k*v⁻¹) (N k) - orbit (c k) (x k) (N k)) /
      transport (c k) (x k) (σ k) (N k)
  let D : ℕ → ℂ := fun k => driver (charge (c k) (x k) (σ k)) v (N k)
  have hD : Tendsto D atTop (𝓝 (v-T)) := by
    exact tendsto_const_nhds.sub hsum
  have hDlower : δ ≤ ‖v-T‖ := by
    have hc : Tendsto (fun _ : ℕ => δ) atTop (𝓝 δ) := tendsto_const_nhds
    exact le_of_tendsto_of_tendsto' hc hD.norm (fun k => hsep k (N k) le_rfl)
  have hDnz : v-T ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le hδ hDlower)
  have hInv : Tendsto (fun k => (D k)⁻¹) atTop (𝓝 (v-T)⁻¹) := hD.inv₀ hDnz
  have hbound : ∀ k, ‖F k - (D k)⁻¹‖ ≤
      (4 / δ^3) * energy (charge (c k) (x k) (σ k)) (N k) := by
    intro k
    exact actual_quadratic_shadow (c k) (x k) (σ k) v (N k) (hσ k)
      (hx k) δ hδ (hsep k) (hsmall k) (N k) le_rfl
  have he0 : Tendsto (fun k =>
      (4 / δ^3) * energy (charge (c k) (x k) (σ k)) (N k)) atTop (𝓝 0) := by
    have hc : Tendsto (fun _ : ℕ => (4 / δ^3)) atTop (𝓝 (4 / δ^3)) :=
      tendsto_const_nhds
    simpa only [mul_zero] using hc.mul henergy
  have herror : Tendsto (fun k => F k - (D k)⁻¹) atTop (𝓝 0) :=
    squeeze_zero_norm hbound he0
  have hlim : Tendsto F atTop (𝓝 (v-T)⁻¹) := by
    simpa only [sub_add_cancel, zero_add] using herror.add hInv
  exact hlim

/-- The same geometric limit for the actual critical return, including the
source scaling and the derivative normalization of the remaining flight. -/
theorem critical_return_mobius_limit
    (c s : ℕ → ℂ) (N : ℕ → ℕ) (z T : ℂ)
    (hs : ∀ k, s k ≠ 0)
    (hx : ∀ k j, j < N k → orbit (c k) (c k) j ≠ 0)
    (δ : ℝ) (hδ : 0 < δ)
    (hsep : ∀ k j, j ≤ N k →
      δ ≤ ‖driver (charge (c k) (c k) ((s k)^2)) ((z^2)⁻¹) j‖)
    (hsmall : ∀ k, energy (charge (c k) (c k) ((s k)^2)) (N k) ≤ δ^2 / 16)
    (henergy : Tendsto (fun k => energy (charge (c k) (c k) ((s k)^2)) (N k))
      atTop (𝓝 0))
    (hsum : Tendsto (fun k => ∑ j ∈ Finset.range (N k),
      charge (c k) (c k) ((s k)^2) j) atTop (𝓝 T)) :
    Tendsto (fun k =>
      (orbit (c k) (s k*z) (N k+1) - orbit (c k) 0 (N k+1)) /
        transport (c k) (c k) ((s k)^2) (N k))
      atTop (𝓝 (((z^2)⁻¹-T)⁻¹)) := by
  have hlim := actual_quadratic_mobius_limit c c (fun k => (s k)^2) N
    ((z^2)⁻¹) T (fun k => pow_ne_zero 2 (hs k)) hx δ hδ
    hsep hsmall henergy hsum
  have heq : (fun k =>
      (orbit (c k) (c k + (s k)^2*((z^2)⁻¹)⁻¹) (N k) -
        orbit (c k) (c k) (N k)) / transport (c k) (c k) ((s k)^2) (N k)) =
      (fun k => (orbit (c k) (s k*z) (N k+1) - orbit (c k) 0 (N k+1)) /
        transport (c k) (c k) ((s k)^2) (N k)) := by
    funext k
    rw [inv_inv, ← normalizedActualFlight_eval,
      critical_return_quotient (c k) (s k) z (N k) (hs k) (hx k)]
  rw [heq] at hlim
  exact hlim

private theorem inverse_driver_difference (v S T : ℂ) (δ : ℝ) (hδ : 0 < δ)
    (hS : δ ≤ ‖v-S‖) (hT : δ ≤ ‖v-T‖) :
    ‖(v-S)⁻¹ - (v-T)⁻¹‖ ≤ ‖S-T‖ / δ^2 := by
  have hvS : v-S ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le hδ hS)
  have hvT : v-T ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le hδ hT)
  have hid : (v-S)⁻¹ - (v-T)⁻¹ = (S-T) / ((v-S)*(v-T)) := by
    field_simp [hvS, hvT] <;> ring
  have hp : δ^2 ≤ ‖v-S‖ * ‖v-T‖ := by
    have hm := mul_le_mul hS hT (le_of_lt hδ) (norm_nonneg (v-S))
    nlinarith
  rw [hid, norm_div, norm_mul]
  exact div_le_div_of_nonneg_left (norm_nonneg _) (by positivity) hp

/-- The error to a fixed Möbius target separates square-sum error from the
endpoint error of the signed complex charge sum. -/
theorem actual_quadratic_shadow_to_target (c x σ v T : ℂ) (N : ℕ)
    (hσ : σ ≠ 0) (hx : ∀ j < N, orbit c x j ≠ 0)
    (δ : ℝ) (hδ : 0 < δ)
    (hsep : ∀ j ≤ N, δ ≤ ‖driver (charge c x σ) v j‖)
    (hE : energy (charge c x σ) N ≤ δ^2 / 16)
    (hT : δ ≤ ‖v-T‖) :
    ‖(orbit c (x + σ*v⁻¹) N - orbit c x N) / transport c x σ N - (v-T)⁻¹‖ ≤
      (4 / δ^3) * energy (charge c x σ) N +
        ‖(∑ j ∈ Finset.range N, charge c x σ j)-T‖ / δ^2 := by
  have hf := actual_quadratic_shadow c x σ v N hσ hx δ hδ hsep hE N le_rfl
  have hi := inverse_driver_difference v
    (∑ j ∈ Finset.range N, charge c x σ j) T δ hδ (hsep N le_rfl) hT
  have ht := norm_add_le
    ((orbit c (x + σ*v⁻¹) N - orbit c x N) / transport c x σ N -
      (driver (charge c x σ) v N)⁻¹)
    ((driver (charge c x σ) v N)⁻¹ - (v-T)⁻¹)
  have hid :
      ((orbit c (x + σ*v⁻¹) N - orbit c x N) / transport c x σ N -
        (driver (charge c x σ) v N)⁻¹) +
      ((driver (charge c x σ) v N)⁻¹ - (v-T)⁻¹) =
      (orbit c (x + σ*v⁻¹) N - orbit c x N) / transport c x σ N - (v-T)⁻¹ := by
    ring
  rw [hid] at ht
  exact ht.trans (add_le_add hf hi)

/-- Genuine uniform geometric convergence of actual quadratic flights on
any set of reciprocal inputs with a shared separation constant. -/
theorem actual_quadratic_mobius_uniform_limit
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
    TendstoUniformlyOn (fun k v =>
      (orbit (c k) (x k + σ k*v⁻¹) (N k) - orbit (c k) (x k) (N k)) /
        transport (c k) (x k) (σ k) (N k))
      (fun v => (v-T)⁻¹) atTop K := by
  let S : ℕ → ℂ := fun k => ∑ j ∈ Finset.range (N k),
    charge (c k) (x k) (σ k) j
  let B : ℕ → ℝ := fun k =>
    (4 / δ^3) * energy (charge (c k) (x k) (σ k)) (N k) + ‖S k-T‖ / δ^2
  have he0 : Tendsto (fun k =>
      (4 / δ^3) * energy (charge (c k) (x k) (σ k)) (N k)) atTop (𝓝 0) := by
    have hc : Tendsto (fun _ : ℕ => (4 / δ^3)) atTop (𝓝 (4 / δ^3)) :=
      tendsto_const_nhds
    simpa only [mul_zero] using hc.mul henergy
  have hs0 : Tendsto (fun k => ‖S k-T‖) atTop (𝓝 0) := by
    have hc : Tendsto (fun _ : ℕ => T) atTop (𝓝 T) := tendsto_const_nhds
    simpa [S] using (hsum.sub hc).norm
  have hsdiv : Tendsto (fun k => ‖S k-T‖ / δ^2) atTop (𝓝 0) := by
    have hc : Tendsto (fun _ : ℕ => δ^2) atTop (𝓝 (δ^2)) := tendsto_const_nhds
    have hdiv := hs0.div hc (pow_ne_zero 2 (ne_of_gt hδ))
    have hfun : ((fun k : ℕ => ‖S k-T‖) / (fun _ : ℕ => δ^2)) =
        (fun k : ℕ => ‖S k-T‖ / δ^2) := by
      funext k
      rfl
    rw [hfun] at hdiv
    simpa only [zero_div] using hdiv
  have hB : Tendsto B atTop (𝓝 0) := by
    simpa only [zero_add] using he0.add hsdiv
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [hB.eventually (gt_mem_nhds hε)] with k hk
  intro v hv
  have hD : Tendsto (fun l => driver (charge (c l) (x l) (σ l)) v (N l))
      atTop (𝓝 (v-T)) := tendsto_const_nhds.sub hsum
  have hT : δ ≤ ‖v-T‖ := by
    have hc : Tendsto (fun _ : ℕ => δ) atTop (𝓝 δ) := tendsto_const_nhds
    exact le_of_tendsto_of_tendsto' hc hD.norm (fun l => hsep l v hv (N l) le_rfl)
  have hb := actual_quadratic_shadow_to_target (c k) (x k) (σ k) v T (N k)
    (hσ k) (hx k) δ hδ (hsep k v hv) (hsmall k) hT
  rw [dist_eq_norm, norm_sub_rev]
  exact lt_of_le_of_lt hb hk

/-- Uniform convergence for the actual critical return on the inverse-square
pullback of the separated reciprocal-input set. -/
theorem critical_return_mobius_uniform_limit
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
      (fun z => ((z^2)⁻¹-T)⁻¹) atTop {z : ℂ | (z^2)⁻¹ ∈ K} := by
  have hlim := actual_quadratic_mobius_uniform_limit c c (fun k => (s k)^2)
    N K T (fun k => pow_ne_zero 2 (hs k)) hx δ hδ hsep hsmall henergy hsum
  apply (hlim.comp (fun z : ℂ => (z^2)⁻¹)).congr
  exact Eventually.of_forall (fun k z _ => by
    dsimp only [Function.comp_def]
    rw [inv_inv, ← normalizedActualFlight_eval,
      critical_return_quotient (c k) (s k) z (N k) (hs k) (hx k)])

end
end QuadraticActualShadow

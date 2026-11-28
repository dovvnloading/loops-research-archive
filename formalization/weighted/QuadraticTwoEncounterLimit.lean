import QuadraticFlightJet
import QuadraticMobiusEncounter

/-!
# Two encounters cannot disappear inside actual Möbius flight limits

Three consecutive blocks are literal normalized iterates of `z ↦ z^2+c`.
They may converge locally uniformly to nonidentity parabolic Möbius maps.
If the full actual return converges to the identity germ, the two intervening
quadratic encounter coefficients must tend to zero.
-/

namespace QuadraticTwoEncounterLimit

open QuadraticFlightJet Polynomial Filter
open scoped Topology

noncomputable section

/-- Locally uniform convergence on an open set controls moving input points. -/
theorem locally_uniform_moving_eval
    (F : ℕ → ℂ → ℂ) (f : ℂ → ℂ) (U : Set ℂ) (hU : IsOpen U)
    (q : ℂ) (hq : q ∈ U)
    (hF : TendstoLocallyUniformlyOn F f atTop U)
    (hf : ContinuousAt f q) (z : ℕ → ℂ) (hz : Tendsto z atTop (𝓝 q)) :
    Tendsto (fun n => F n (z n)) atTop (𝓝 (f q)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hhalf : 0 < ε / 2 := by positivity
  obtain ⟨V, hV, hFV⟩ :=
    (Metric.tendstoLocallyUniformlyOn_iff.mp hF) (ε/2) hhalf q hq
  have hV' : V ∈ 𝓝 q := by rwa [hU.nhdsWithin_eq hq] at hV
  have hsmall := (Metric.tendsto_nhds.mp (hf.tendsto.comp hz)) (ε/2) hhalf
  filter_upwards [hFV, hz.eventually hV', hsmall] with n hn hzn hfn
  have hclose := hn (z n) hzn
  have ht := dist_triangle (F n (z n)) (f (z n)) (f q)
  rw [dist_comm (F n (z n)) (f (z n))] at ht
  linarith

private theorem mobius_continuousAt (t u : ℂ) (hu : 1-t*u ≠ 0) :
    ContinuousAt (QuadraticMobiusEncounter.flight t) u := by
  have hd : ContinuousAt (fun z : ℂ => 1-t*z) u := by fun_prop
  have hi : ContinuousAt (id : ℂ → ℂ) u := continuousAt_id
  have hdiv := hi.div hd hu
  have hfun : ((id : ℂ → ℂ) / (fun z : ℂ => 1-t*z)) =
      QuadraticMobiusEncounter.flight t := by
    funext z
    rfl
  rw [hfun] at hdiv
  exact hdiv

theorem flight_eval_succ (a : ℕ → ℂ) (n : ℕ) (u : ℂ) :
    (flight a (n+1)).eval u =
      QuadraticMobiusEncounter.encounter (a n) ((flight a n).eval u) := by
  simp [flight, QuadraticMobiusEncounter.encounter]

/-- Exact ordered evaluation split, retaining both selected quadratic steps. -/
theorem flight_two_encounter_split (a : ℕ → ℂ) (k₀ k₁ k₂ : ℕ) (u : ℂ) :
    (flight a (k₀+1+k₁+1+k₂)).eval u =
      (flight (fun j => a (k₀+1+k₁+1+j)) k₂).eval
        (QuadraticMobiusEncounter.encounter (a (k₀+1+k₁))
          ((flight (fun j => a (k₀+1+j)) k₁).eval
            (QuadraticMobiusEncounter.encounter (a k₀) ((flight a k₀).eval u)))) := by
  rw [flight_add a (k₀+1+k₁+1) k₂, eval_comp, flight_eval_succ,
    flight_add a (k₀+1) k₁, eval_comp, flight_eval_succ]

/-- The split is an identity of actual normalized quadratic iterates. -/
theorem actual_two_encounter_split (c x σ : ℂ) (k₀ k₁ k₂ : ℕ) (u : ℂ)
    (hσ : σ ≠ 0)
    (hx : ∀ j < k₀+1+k₁+1+k₂, orbit c x j ≠ 0) :
    (normalizedActualFlight c x σ (k₀+1+k₁+1+k₂)).eval u =
      (actualBlock c x σ (k₀+1+k₁+1) k₂).eval
        (QuadraticMobiusEncounter.encounter (charge c x σ (k₀+1+k₁))
          ((actualBlock c x σ (k₀+1) k₁).eval
            (QuadraticMobiusEncounter.encounter (charge c x σ k₀)
              ((actualBlock c x σ 0 k₀).eval u)))) := by
  rw [normalizedActualFlight_eq_flight c x σ _ hσ hx,
    actualBlock_eq_flight c x σ (k₀+1+k₁+1) k₂ hσ hx,
    actualBlock_eq_flight c x σ (k₀+1) k₁ hσ (fun j hj => hx j (by omega)),
    actualBlock_eq_flight c x σ 0 k₀ hσ (fun j hj => hx j (by omega))]
  simpa only [Nat.zero_add] using
    flight_two_encounter_split (charge c x σ) k₀ k₁ k₂ u

/-- A geometric obstruction for the actual quadratic family at unbounded
return times. Only local neighborhoods of zero are assumed; no block is
required to converge across a pole of its limiting Möbius map. -/
theorem actual_critical_two_encounter_obstruction
    (c s : ℕ → ℂ) (k₀ k₁ k₂ : ℕ → ℕ) (α β σ τ ρ : ℂ)
    (U₀ U₁ U₂ U : Set ℂ)
    (hU₀ : IsOpen U₀) (hU₁ : IsOpen U₁) (hU₂ : IsOpen U₂) (hU : IsOpen U)
    (h0₀ : (0 : ℂ) ∈ U₀) (h0₁ : (0 : ℂ) ∈ U₁)
    (h0₂ : (0 : ℂ) ∈ U₂) (h0 : (0 : ℂ) ∈ U)
    (hs : ∀ n, s n ≠ 0)
    (hx : ∀ n j, j < k₀ n+1+k₁ n+1+k₂ n → orbit (c n) (c n) j ≠ 0)
    (hα : Tendsto (fun n => charge (c n) (c n) ((s n)^2) (k₀ n)) atTop (𝓝 α))
    (hβ : Tendsto (fun n => charge (c n) (c n) ((s n)^2) (k₀ n+1+k₁ n))
      atTop (𝓝 β))
    (h₀ : TendstoLocallyUniformlyOn
      (fun n u => (actualBlock (c n) (c n) ((s n)^2) 0 (k₀ n)).eval u)
      (QuadraticMobiusEncounter.flight σ) atTop U₀)
    (h₁ : TendstoLocallyUniformlyOn
      (fun n u => (actualBlock (c n) (c n) ((s n)^2) (k₀ n+1) (k₁ n)).eval u)
      (QuadraticMobiusEncounter.flight τ) atTop U₁)
    (h₂ : TendstoLocallyUniformlyOn
      (fun n u => (actualBlock (c n) (c n) ((s n)^2)
        (k₀ n+1+k₁ n+1) (k₂ n)).eval u)
      (QuadraticMobiusEncounter.flight ρ) atTop U₂)
    (hfull : TendstoLocallyUniformlyOn
      (fun n u => (normalizedActualFlight (c n) (c n) ((s n)^2)
        (k₀ n+1+k₁ n+1+k₂ n)).eval u) (fun u => u) atTop U) :
    α = 0 ∧ β = 0 ∧ σ+τ+ρ = 0 := by
  let a : ℕ → ℂ := fun n => charge (c n) (c n) ((s n)^2) (k₀ n)
  let b : ℕ → ℂ := fun n => charge (c n) (c n) ((s n)^2) (k₀ n+1+k₁ n)
  let F₀ : ℕ → ℂ → ℂ := fun n u =>
    (actualBlock (c n) (c n) ((s n)^2) 0 (k₀ n)).eval u
  let F₁ : ℕ → ℂ → ℂ := fun n u =>
    (actualBlock (c n) (c n) ((s n)^2) (k₀ n+1) (k₁ n)).eval u
  let F₂ : ℕ → ℂ → ℂ := fun n u =>
    (actualBlock (c n) (c n) ((s n)^2) (k₀ n+1+k₁ n+1) (k₂ n)).eval u
  let w₁ : ℂ → ℂ := fun u =>
    QuadraticMobiusEncounter.encounter α (QuadraticMobiusEncounter.flight σ u)
  let w₂ : ℂ → ℂ := fun u =>
    QuadraticMobiusEncounter.encounter β (QuadraticMobiusEncounter.flight τ (w₁ u))
  have hp₀ : ContinuousAt (QuadraticMobiusEncounter.flight σ) 0 :=
    mobius_continuousAt σ 0 (by simp)
  have hw₁ : ContinuousAt w₁ 0 := by
    have ha : ContinuousAt (fun _ : ℂ => α) 0 := continuousAt_const
    simpa only [w₁, QuadraticMobiusEncounter.encounter] using
      hp₀.add (ha.mul (hp₀.pow 2))
  have hw₁zero : w₁ 0 = 0 := by
    simp [w₁, QuadraticMobiusEncounter.encounter, QuadraticMobiusEncounter.flight]
  have hp₁ : ContinuousAt (fun u => QuadraticMobiusEncounter.flight τ (w₁ u)) 0 :=
    (mobius_continuousAt τ (w₁ 0) (by rw [hw₁zero]; simp)).comp 0 hw₁
  have hw₂ : ContinuousAt w₂ 0 := by
    have hb : ContinuousAt (fun _ : ℂ => β) 0 := continuousAt_const
    simpa only [w₂, QuadraticMobiusEncounter.encounter] using
      hp₁.add (hb.mul (hp₁.pow 2))
  have hw₂zero : w₂ 0 = 0 := by
    simp [w₂, hw₁zero, QuadraticMobiusEncounter.encounter,
      QuadraticMobiusEncounter.flight]
  have hm₁ : ∀ᶠ u in 𝓝 0, w₁ u ∈ U₁ :=
    hw₁.tendsto.eventually (by rw [hw₁zero]; exact hU₁.mem_nhds h0₁)
  have hm₂ : ∀ᶠ u in 𝓝 0, w₂ u ∈ U₂ :=
    hw₂.tendsto.eventually (by rw [hw₂zero]; exact hU₂.mem_nhds h0₂)
  have hc₁ : ContinuousAt (fun u : ℂ => 1-τ*w₁ u) 0 :=
    continuousAt_const.sub (continuousAt_const.mul hw₁)
  have hc₂ : ContinuousAt (fun u : ℂ => 1-ρ*w₂ u) 0 :=
    continuousAt_const.sub (continuousAt_const.mul hw₂)
  have hd₁ : ∀ᶠ u in 𝓝 0, 1-τ*w₁ u ≠ 0 :=
    hc₁.eventually_ne (by rw [hw₁zero]; simp)
  have hd₂ : ∀ᶠ u in 𝓝 0, 1-ρ*w₂ u ≠ 0 :=
    hc₂.eventually_ne (by rw [hw₂zero]; simp)
  apply QuadraticMobiusEncounter.two_encounter_composition_identity_germ α β σ τ ρ
  filter_upwards [hU₀.mem_nhds h0₀, hU.mem_nhds h0, hm₁, hm₂, hd₁, hd₂]
    with u hu₀ hu hwu₁ hwu₂ hdu₁ hdu₂
  have hF₀ : Tendsto (fun n => F₀ n u) atTop
      (𝓝 (QuadraticMobiusEncounter.flight σ u)) := h₀.tendsto_at hu₀
  have hA : Tendsto (fun n => QuadraticMobiusEncounter.encounter (a n) (F₀ n u))
      atTop (𝓝 (w₁ u)) := by
    simpa only [a, w₁, QuadraticMobiusEncounter.encounter] using
      hF₀.add (hα.mul (hF₀.pow 2))
  have hF₁ : Tendsto
      (fun n => F₁ n (QuadraticMobiusEncounter.encounter (a n) (F₀ n u)))
      atTop (𝓝 (QuadraticMobiusEncounter.flight τ (w₁ u))) :=
    locally_uniform_moving_eval F₁ (QuadraticMobiusEncounter.flight τ) U₁ hU₁
      (w₁ u) hwu₁ h₁ (mobius_continuousAt τ (w₁ u) hdu₁) _ hA
  have hB : Tendsto
      (fun n => QuadraticMobiusEncounter.encounter (b n)
        (F₁ n (QuadraticMobiusEncounter.encounter (a n) (F₀ n u))))
      atTop (𝓝 (w₂ u)) := by
    simpa only [b, w₂, QuadraticMobiusEncounter.encounter] using
      hF₁.add (hβ.mul (hF₁.pow 2))
  have hF₂ : Tendsto
      (fun n => F₂ n (QuadraticMobiusEncounter.encounter (b n)
        (F₁ n (QuadraticMobiusEncounter.encounter (a n) (F₀ n u)))))
      atTop (𝓝 (QuadraticMobiusEncounter.flight ρ (w₂ u))) :=
    locally_uniform_moving_eval F₂ (QuadraticMobiusEncounter.flight ρ) U₂ hU₂
      (w₂ u) hwu₂ h₂ (mobius_continuousAt ρ (w₂ u) hdu₂) _ hB
  have hsplit :
      (fun n => (normalizedActualFlight (c n) (c n) ((s n)^2)
        (k₀ n+1+k₁ n+1+k₂ n)).eval u) =
      (fun n => F₂ n (QuadraticMobiusEncounter.encounter (b n)
        (F₁ n (QuadraticMobiusEncounter.encounter (a n) (F₀ n u))))) := by
    funext n
    simpa only [F₀, F₁, F₂, a, b] using
      actual_two_encounter_split (c n) (c n) ((s n)^2) (k₀ n) (k₁ n) (k₂ n) u
        (pow_ne_zero 2 (hs n)) (hx n)
  rw [← hsplit] at hF₂
  exact tendsto_nhds_unique hF₂ (hfull.tendsto_at hu)

end
end QuadraticTwoEncounterLimit

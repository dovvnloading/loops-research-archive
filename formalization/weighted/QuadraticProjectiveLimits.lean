import QuadraticProjectiveSeparation
import QuadraticProjectiveContinuity

/-!
# Actual quadratic configurations distinguished by their finite projective jet

The exact algebraic separation factor is a unit at the center.  Its
continuity proves that the two actual ordered critical configurations at
the same multiplier differ throughout a punctured parameter neighborhood.
The coefficient limit below is the analytic reading of the already proved
finite polynomial jet, not a geometric compactness hypothesis.
-/

noncomputable section

namespace LoopsQuadraticProjective

open Polynomial Filter
open scoped Topology

theorem continuousAt_periodTwoMultiplier (t : ℂ) :
    ContinuousAt periodTwoMultiplier t := by
  exact (continuousAt_const.mul continuousAt_id).mul
    (continuousAt_const.add continuousAt_id)

theorem continuousAt_periodTwoError_zero : ContinuousAt periodTwoError 0 := by
  apply continuousAt_const.div
    (continuousAt_const.mul ((continuousAt_const.add continuousAt_id).pow 3))
  norm_num

theorem periodTwo_one_add_eventually_ne_zero :
    ∀ᶠ t : ℂ in 𝓝 0, t+1 ≠ 0 := by
  exact (continuousAt_id.add continuousAt_const).eventually_ne (by norm_num)

theorem main_den_at_periodTwo_eventually_ne_zero (k : ℕ) (hk : 1 ≤ k) :
    ∀ᶠ t : ℂ in 𝓝 0, (denPoly 0 k).eval (periodTwoMultiplier t) ≠ 0 := by
  exact denPoly_eventually_ne_zero k hk continuousAt_const
    (continuousAt_periodTwoMultiplier 0) (by simp [periodTwoMultiplier])

theorem periodTwo_den_eventually_ne_zero (k : ℕ) (hk : 1 ≤ k) :
    ∀ᶠ t : ℂ in 𝓝 0,
      (denPoly (periodTwoError t) k).eval (periodTwoMultiplier t) ≠ 0 := by
  exact denPoly_eventually_ne_zero k hk continuousAt_periodTwoError_zero
    (continuousAt_periodTwoMultiplier 0) (by simp [periodTwoMultiplier])

/-- The exact actual-family separation factor is continuous at the center. -/
theorem separationUnit_continuousAt_zero (k : ℕ) (hk : 1 ≤ k)
    (U : ℂ[X]) (Q : (ℂ[X])[X]) :
    ContinuousAt (separationUnit k U Q) 0 := by
  have hq := continuousAt_periodTwoMultiplier 0
  have he := continuousAt_periodTwoError_zero
  have hD₁ : (denPoly 0 k).eval (periodTwoMultiplier 0) ≠ 0 := by
    rw [show periodTwoMultiplier 0 = 0 by simp [periodTwoMultiplier], denPoly_eval_zero 0 k hk]
    norm_num
  have hD₂ : (denPoly (periodTwoError 0) k).eval (periodTwoMultiplier 0) ≠ 0 := by
    rw [show periodTwoMultiplier 0 = 0 by simp [periodTwoMultiplier],
      denPoly_eval_zero (periodTwoError 0) k hk]
    norm_num
  have hfirst := (continuousAt_bivariate_eval Q he hq).div
    (continuousAt_denPoly k he hq) hD₂
  have hlast := (U.continuousAt.comp hq).div
    ((denPoly 0 k).continuousAt.comp hq) hD₁
  have hmiddle : ContinuousAt (fun t : ℂ =>
      (3+3*t+t^2)/(512*(1+t)^4)) 0 := by
    apply ((continuousAt_const.add (continuousAt_const.mul continuousAt_id)).add
      (continuousAt_id.pow 2)).div
        (continuousAt_const.mul ((continuousAt_const.add continuousAt_id).pow 4))
    norm_num
  exact continuousAt_const.add (hq.mul ((hfirst.add hmiddle).sub hlast))

/-- Exact finite-order separation of the two actual quadratic return charts:
the multiplier-normalized difference has coefficient 1/128. -/
theorem criticalClock_separation_coefficient (k : ℕ) (hk : 3 ≤ k) :
    Tendsto (fun t : ℂ =>
      (criticalClock (periodTwoParameter t) (2*k) -
        criticalClock (mainParameter (periodTwoMultiplier t)) k) /
          (periodTwoMultiplier t)^2) (𝓝[≠] 0) (𝓝 (1/128 : ℂ)) := by
  obtain ⟨U, Q, hR⟩ := criticalClock_separation_unit k hk
  have hlim := (separationUnit_continuousAt_zero k (by omega) U Q).tendsto
  rw [separationUnit_zero] at hlim
  apply (hlim.mono_left nhdsWithin_le_nhds).congr'
  have hD₁ : ∀ᶠ t : ℂ in 𝓝[≠] 0,
      (denPoly 0 k).eval (periodTwoMultiplier t) ≠ 0 :=
    (main_den_at_periodTwo_eventually_ne_zero k (by omega)).filter_mono nhdsWithin_le_nhds
  have hD₂ : ∀ᶠ t : ℂ in 𝓝[≠] 0,
      (denPoly (periodTwoError t) k).eval (periodTwoMultiplier t) ≠ 0 :=
    (periodTwo_den_eventually_ne_zero k (by omega)).filter_mono nhdsWithin_le_nhds
  have ht1 : ∀ᶠ t : ℂ in 𝓝[≠] 0, t+1 ≠ 0 :=
    periodTwo_one_add_eventually_ne_zero.filter_mono nhdsWithin_le_nhds
  filter_upwards [hD₁, hD₂, ht1, self_mem_nhdsWithin] with t hd₁ hd₂ ht1 ht
  have ht0 : t ≠ 0 := ht
  rw [hR t ht0 ht1 hd₁ hd₂]
  have hq := periodTwoMultiplier_ne_zero t ht0 ht1
  field_simp

/-- The actual ordered critical configurations cannot have equal cross-ratios
near the two centers when their true return multipliers agree. -/
theorem criticalClock_eventually_separated (k : ℕ) (hk : 3 ≤ k) :
    ∀ᶠ t : ℂ in 𝓝 0, t ≠ 0 →
      criticalClock (periodTwoParameter t) (2*k) ≠
        criticalClock (mainParameter (periodTwoMultiplier t)) k := by
  obtain ⟨U, Q, hR⟩ := criticalClock_separation_unit k hk
  have hu := (separationUnit_continuousAt_zero k (by omega) U Q).eventually_ne
    (show separationUnit k U Q 0 ≠ 0 by rw [separationUnit_zero]; norm_num)
  filter_upwards [hu, main_den_at_periodTwo_eventually_ne_zero k (by omega),
    periodTwo_den_eventually_ne_zero k (by omega), periodTwo_one_add_eventually_ne_zero]
    with t hut hd₁ hd₂ ht1
  intro ht heq
  have hprod := mul_ne_zero (pow_ne_zero 2 (periodTwoMultiplier_ne_zero t ht ht1)) hut
  apply hprod
  rw [← hR t ht ht1 hd₁ hd₂, heq, sub_self]

end LoopsQuadraticProjective

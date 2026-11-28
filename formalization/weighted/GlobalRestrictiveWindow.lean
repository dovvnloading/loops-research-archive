import GlobalPositiveWindow

/-!
# Global restrictive intervals and their exact inverse endpoints

The hypotheses describe the literal real quadratic map on the entire
interval determined by its critical return.  No near-minus-two parameter
window or small return scale is included among the hypotheses.
-/

namespace GlobalRestrictiveWindow

open Set Function
open NearTwoInverse NearTwoShooting LimitingCrestQuadraticReturn

noncomputable section

def realMap (c x : ℝ) : ℝ := x ^ 2 + c

def returnInterval (c : ℝ) (p : ℕ) : Set ℝ :=
  Icc (-criticalValue c p) (criticalValue c p)

/-- A genuine invariant real return interval with the positive first
itinerary.  All intermediate signs hold on the whole physical interval.
The return is the literal p-th iterate, not an assigned symbolic map. -/
structure PositiveRestrictiveReturn (c : ℝ) (p : ℕ) : Prop where
  parameter_band : c ∈ Icc (-2 : ℝ) (-1)
  return_pos : 0 < criticalValue c p
  negative_first : ∀ x ∈ returnInterval c p, realMap c x < 0
  positive_phases : ∀ j : ℕ, 2 ≤ j → j < p →
    ∀ x ∈ returnInterval c p, 0 < (realMap c)^[j] x
  invariant : MapsTo ((realMap c)^[p]) (returnInterval c p) (returnInterval c p)

theorem PositiveRestrictiveReturn.zero_mem {c : ℝ} {p : ℕ}
    (h : PositiveRestrictiveReturn c p) : 0 ∈ returnInterval c p := by
  constructor <;> linarith [h.return_pos]

theorem PositiveRestrictiveReturn.right_mem {c : ℝ} {p : ℕ}
    (h : PositiveRestrictiveReturn c p) :
    criticalValue c p ∈ returnInterval c p := by
  exact ⟨by linarith [h.return_pos], le_rfl⟩

/-- The full interval hypothesis supplies the global critical itinerary
needed for the independent inverse-shooting localization theorem. -/
theorem PositiveRestrictiveReturn.critical_prefix {c : ℝ} {p : ℕ}
    (h : PositiveRestrictiveReturn c p) :
    ∀ j : ℕ, 2 ≤ j → j ≤ p → 0 < criticalValue c j := by
  intro j hj hjp
  rcases eq_or_lt_of_le hjp with rfl | hjp
  · exact h.return_pos
  · exact h.positive_phases j hj hjp 0 h.zero_mem

/-- Exponential parameter localization is a conclusion of the global
restrictive-interval hypotheses. -/
theorem PositiveRestrictiveReturn.parameter_upper {c : ℝ} {p : ℕ}
    (hp : 17 ≤ p) (h : PositiveRestrictiveReturn c p) :
    c < -2 + 20 * scale p :=
  GlobalPositiveWindow.nonnegative_itinerary_parameter_upper hp h.parameter_band
    (fun j hj hjp => (h.critical_prefix j hj hjp).le)

theorem PositiveRestrictiveReturn.square_return_lt {c : ℝ} {p : ℕ}
    (h : PositiveRestrictiveReturn c p) : (criticalValue c p) ^ 2 < -c := by
  have hn := h.negative_first (criticalValue c p) h.right_mem
  dsimp [realMap] at hn
  linarith

/-- This initial scale bound follows solely from the first negative
phase and the original real parameter range. -/
theorem PositiveRestrictiveReturn.return_lt_three_halves {c : ℝ} {p : ℕ}
    (h : PositiveRestrictiveReturn c p) : criticalValue c p < 3 / 2 := by
  have hs := h.square_return_lt
  have hc := h.parameter_band.1
  nlinarith [h.return_pos]

theorem PositiveRestrictiveReturn.endpoint_return_mem {c : ℝ} {p : ℕ}
    (h : PositiveRestrictiveReturn c p) :
    (realMap c)^[p] (criticalValue c p) ∈ returnInterval c p :=
  h.invariant h.right_mem

private theorem inverse_positive_iterate (c x : ℝ) (n : ℕ)
    (h : ∀ j : ℕ, j < n → 0 ≤ (realMap c)^[j] x) :
    back c n ((realMap c)^[n] x) = x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hn := h n (by omega)
    have hb : B c ((realMap c)^[n+1] x) = (realMap c)^[n] x := by
      rw [Function.iterate_succ_apply']
      simp only [B, realMap, add_sub_cancel_right, Real.sqrt_sq_eq_abs,
        abs_of_nonneg hn]
    change (B c)^[n+1] ((realMap c)^[n+1] x) = x
    rw [Function.iterate_succ_apply, hb]
    exact ih (fun j hj => h j (by omega))

/-- Reverse reconstruction on a whole admissible source interval.
The first inverse step recovers the absolute value of the negative first
phase; every other step is forced by the positive physical itinerary. -/
theorem PositiveRestrictiveReturn.inverse_endpoint {c x : ℝ} {p : ℕ}
    (hp : 2 ≤ p) (h : PositiveRestrictiveReturn c p)
    (hx : x ∈ returnInterval c p) :
    back c (p-1) ((realMap c)^[p] x) = -realMap c x := by
  have htail : ∀ j : ℕ, j < p-2 →
      0 ≤ (realMap c)^[j] ((realMap c)^[2] x) := by
    intro j hj
    rw [← Function.iterate_add_apply]
    exact (h.positive_phases (j+2) (by omega) (by omega) x hx).le
  have hback := inverse_positive_iterate c ((realMap c)^[2] x) (p-2) htail
  rw [← Function.iterate_add_apply, Nat.sub_add_cancel hp] at hback
  have hexp : p-1 = (p-2)+1 := by omega
  rw [hexp, back_succ, hback]
  have hn := h.negative_first x hx
  simp only [show (2 : ℕ) = 1+1 from rfl, Function.iterate_succ_apply',
    Function.iterate_one, B, realMap, add_sub_cancel_right,
    Real.sqrt_sq_eq_abs, abs_of_neg hn]

theorem PositiveRestrictiveReturn.critical_inverse {c : ℝ} {p : ℕ}
    (hp : 2 ≤ p) (h : PositiveRestrictiveReturn c p) :
    back c (p-1) (criticalValue c p) = -c := by
  simpa only [realMap, criticalValue, zero_pow (by decide : 2 ≠ 0), zero_add]
    using h.inverse_endpoint hp h.zero_mem

theorem PositiveRestrictiveReturn.return_endpoint_inverse {c : ℝ} {p : ℕ}
    (hp : 2 ≤ p) (h : PositiveRestrictiveReturn c p) :
    back c (p-1) ((realMap c)^[p] (criticalValue c p)) =
      -c - (criticalValue c p)^2 := by
  have he := h.inverse_endpoint hp h.right_mem
  dsimp [realMap] at he ⊢
  linarith only [he]

/-- The square of the physical return scale is exactly the inverse
branch displacement between two points of the same restrictive interval.
This identity supplies the input for a quantitative inverse contraction. -/
theorem PositiveRestrictiveReturn.inverse_displacement {c : ℝ} {p : ℕ}
    (hp : 2 ≤ p) (h : PositiveRestrictiveReturn c p) :
    (criticalValue c p)^2 =
      back c (p-1) (criticalValue c p) -
      back c (p-1) ((realMap c)^[p] (criticalValue c p)) := by
  rw [h.critical_inverse hp, h.return_endpoint_inverse hp]
  ring

end

end GlobalRestrictiveWindow

import AnnularModeContraction
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Order.Basic

/-!
# The accumulated annular response clock

The multiplicative comparison radius of the one-collar variational estimate
has an exact projective coordinate. In that coordinate every collar multiplies
by the square of its attenuation factor. Consequently arbitrarily large
terminal comparison radii are forgotten when the accumulated collar lengths
diverge. No summability condition on the individual attenuations is used.

This file proves the scalar clock consumed by the variational comparison.
It makes no separate assertion identifying an arbitrary quadratic carrier
with a chain of annuli.
-/

namespace AnnularResponseClock

open Filter
open scoped Topology BigOperators
open AnnularModeContraction

noncomputable section

/-- The projective radius of a comparison factor at least one. -/
def projective (a : ℝ) : ℝ := (a - 1) / (a + 1)

/-- Recover a comparison factor from a projective radius below one. -/
def fromProjective (t : ℝ) : ℝ := (1 + t) / (1 - t)

theorem projective_nonneg {a : ℝ} (ha : 1 ≤ a) : 0 ≤ projective a := by
  exact div_nonneg (sub_nonneg.mpr ha) (by linarith)

theorem projective_lt_one {a : ℝ} (ha : 1 ≤ a) : projective a < 1 := by
  have hden : 0 < a + 1 := by linarith
  apply (div_lt_one hden).2
  linarith

theorem fromProjective_one_le {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    1 ≤ fromProjective t := by
  apply (le_div_iff₀ (sub_pos.mpr ht1)).2
  nlinarith

theorem fromProjective_projective {a : ℝ} (ha : 1 ≤ a) :
    fromProjective (projective a) = a := by
  have hden : a + 1 ≠ 0 := by linarith
  have hp : 1 - projective a ≠ 0 := ne_of_gt (sub_pos.mpr (projective_lt_one ha))
  apply (div_eq_iff hp).2
  dsimp [projective]
  field_simp [hden]
  <;> ring

theorem projective_fromProjective {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    projective (fromProjective t) = t := by
  have hden : 1 - t ≠ 0 := ne_of_gt (sub_pos.mpr ht1)
  have ha := fromProjective_one_le ht0 ht1
  have hsum : fromProjective t + 1 ≠ 0 := by linarith
  apply (div_eq_iff hsum).2
  dsimp [fromProjective]
  field_simp [hden]
  <;> ring

/-- The inverse projective coordinate is increasing throughout its domain. -/
theorem fromProjective_mono {s t : ℝ} (hst : s ≤ t) (ht : t < 1) :
    fromProjective s ≤ fromProjective t := by
  have hs : 0 < 1 - s := by linarith
  have ht' : 0 < 1 - t := by linarith
  apply (div_le_div_iff₀ hs ht').2
  nlinarith

/-- Exact conversion of projective uncertainty into multiplicative error. -/
theorem fromProjective_sub_one {t : ℝ} (ht : t < 1) :
    fromProjective t - 1 = 2 * t / (1 - t) := by
  have hden : 1 - t ≠ 0 := ne_of_gt (sub_pos.mpr ht)
  dsimp [fromProjective]
  field_simp [hden]
  <;> ring

/-- The comparison radius after the first `n` collars. -/
def radiusIterate (r : ℕ → ℝ) (a : ℝ) : ℕ → ℝ
  | 0 => a
  | n + 1 => radiusStep (r n) (radiusIterate r a n)

/-- The exact projective loss through a finite collar chain. -/
def prefixProduct (r : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∏ i ∈ Finset.range n, (r i) ^ 2

theorem prefixProduct_zero (r : ℕ → ℝ) : prefixProduct r 0 = 1 := by
  simp [prefixProduct]

theorem prefixProduct_succ (r : ℕ → ℝ) (n : ℕ) :
    prefixProduct r (n + 1) = prefixProduct r n * (r n) ^ 2 := by
  simp [prefixProduct, Finset.prod_range_succ]

theorem prefixProduct_nonneg (r : ℕ → ℝ) (n : ℕ) :
    0 ≤ prefixProduct r n := by
  exact Finset.prod_nonneg fun _ _ => sq_nonneg _

private theorem square_lt_one {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    r ^ 2 < 1 := by
  have hm := mul_le_mul_of_nonneg_left hr1.le hr0
  nlinarith

theorem prefixProduct_le_one (r : ℕ → ℝ)
    (hr0 : ∀ i, 0 ≤ r i) (hr1 : ∀ i, r i < 1) (n : ℕ) :
    prefixProduct r n ≤ 1 := by
  induction n with
  | zero => simp [prefixProduct]
  | succ n ih =>
      rw [prefixProduct_succ]
      calc
        prefixProduct r n * (r n) ^ 2 ≤ 1 * 1 :=
          mul_le_mul ih (square_lt_one (hr0 n) (hr1 n)).le
            (sq_nonneg _) zero_le_one
        _ = 1 := one_mul 1

/-- Every nonempty chain has a finite universal comparison factor. -/
theorem prefixProduct_lt_one (r : ℕ → ℝ)
    (hr0 : ∀ i, 0 ≤ r i) (hr1 : ∀ i, r i < 1) {n : ℕ} (hn : 0 < n) :
    prefixProduct r n < 1 := by
  cases n with
  | zero => omega
  | succ n =>
      rw [prefixProduct_succ]
      calc
        prefixProduct r n * (r n) ^ 2 ≤ 1 * (r n) ^ 2 :=
          mul_le_mul_of_nonneg_right (prefixProduct_le_one r hr0 hr1 n)
            (sq_nonneg _)
        _ = (r n) ^ 2 := one_mul _
        _ < 1 := square_lt_one (hr0 n) (hr1 n)

theorem radiusIterate_one_le (r : ℕ → ℝ)
    (hr0 : ∀ i, 0 ≤ r i) (hr1 : ∀ i, r i < 1)
    {a : ℝ} (ha : 1 ≤ a) (n : ℕ) : 1 ≤ radiusIterate r a n := by
  induction n with
  | zero => exact ha
  | succ n ih =>
      exact radiusStep_one_le (r := r n) (a := radiusIterate r a n)
        (hr0 n) (hr1 n) ih

/-- The exact product law holds at every finite depth. -/
theorem radiusIterate_projective (r : ℕ → ℝ)
    (hr0 : ∀ i, 0 ≤ r i) (hr1 : ∀ i, r i < 1)
    {a : ℝ} (ha : 1 ≤ a) (n : ℕ) :
    projective (radiusIterate r a n) = prefixProduct r n * projective a := by
  induction n with
  | zero => simp [radiusIterate, prefixProduct]
  | succ n ih =>
      have hstep := radiusStep_crossRatio (r := r n) (a := radiusIterate r a n)
        (hr0 n) (hr1 n) (radiusIterate_one_le r hr0 hr1 ha n)
      change projective (radiusStep (r n) (radiusIterate r a n)) = _
      change projective (radiusStep (r n) (radiusIterate r a n)) =
        (r n) ^ 2 * projective (radiusIterate r a n) at hstep
      rw [hstep, ih, prefixProduct_succ]
      ring

/-- Closed form for the actual recursive comparison factors. -/
theorem radiusIterate_formula (r : ℕ → ℝ)
    (hr0 : ∀ i, 0 ≤ r i) (hr1 : ∀ i, r i < 1)
    {a : ℝ} (ha : 1 ≤ a) (n : ℕ) :
    radiusIterate r a n = fromProjective (prefixProduct r n * projective a) := by
  calc
    radiusIterate r a n = fromProjective (projective (radiusIterate r a n)) :=
      (fromProjective_projective (radiusIterate_one_le r hr0 hr1 ha n)).symm
    _ = _ := congrArg fromProjective (radiusIterate_projective r hr0 hr1 ha n)

/-- The upper bound is independent of the starting comparison factor. -/
theorem radiusIterate_le_universal (r : ℕ → ℝ)
    (hr0 : ∀ i, 0 ≤ r i) (hr1 : ∀ i, r i < 1)
    {a : ℝ} (ha : 1 ≤ a) {n : ℕ} (hn : 0 < n) :
    radiusIterate r a n ≤ fromProjective (prefixProduct r n) := by
  rw [radiusIterate_formula r hr0 hr1 ha n]
  apply fromProjective_mono _ (prefixProduct_lt_one r hr0 hr1 hn)
  calc
    prefixProduct r n * projective a ≤ prefixProduct r n * 1 :=
      mul_le_mul_of_nonneg_left (projective_lt_one ha).le (prefixProduct_nonneg r n)
    _ = prefixProduct r n := mul_one _

theorem radiusIterate_error_bound (r : ℕ → ℝ)
    (hr0 : ∀ i, 0 ≤ r i) (hr1 : ∀ i, r i < 1)
    {a : ℝ} (ha : 1 ≤ a) {n : ℕ} (hn : 0 < n) :
    0 ≤ radiusIterate r a n - 1 ∧
      radiusIterate r a n - 1 ≤ 2 * prefixProduct r n / (1 - prefixProduct r n) := by
  constructor
  · exact sub_nonneg.mpr (radiusIterate_one_le r hr0 hr1 ha n)
  · rw [← fromProjective_sub_one (prefixProduct_lt_one r hr0 hr1 hn)]
    exact sub_le_sub_right (radiusIterate_le_universal r hr0 hr1 ha hn) 1

theorem fromProjective_tendsto_one {p : ℕ → ℝ}
    (hp : Tendsto p atTop (𝓝 0)) :
    Tendsto (fun n => fromProjective (p n)) atTop (𝓝 1) := by
  have hnum : Tendsto (fun n => 1 + p n) atTop (𝓝 ((1 : ℝ) + 0)) :=
    tendsto_const_nhds.add hp
  have hden : Tendsto (fun n => 1 - p n) atTop (𝓝 ((1 : ℝ) - 0)) :=
    tendsto_const_nhds.sub hp
  simpa only [Pi.div_apply, fromProjective, add_zero, sub_zero, div_one] using
    hnum.div hden (by norm_num : (1 : ℝ) - 0 ≠ 0)

/-- Terminal data may vary with the horizon and need not have any uniform
bound. Vanishing projective products still force the root comparison to one. -/
theorem varying_terminal_radius_tendsto_one (r : ℕ → ℝ)
    (hr0 : ∀ i, 0 ≤ r i) (hr1 : ∀ i, r i < 1)
    (hp : Tendsto (prefixProduct r) atTop (𝓝 0))
    (a : ℕ → ℝ) (ha : ∀ n, 1 ≤ a n) :
    Tendsto (fun n => radiusIterate r (a n) n) atTop (𝓝 1) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds (fromProjective_tendsto_one hp)
  · exact Eventually.of_forall fun n => radiusIterate_one_le r hr0 hr1 (ha n) n
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    exact radiusIterate_le_universal r hr0 hr1 (ha n) (by omega)

/-- Accumulated conformal logarithmic length. -/
def totalLength (L : ℕ → ℝ) (n : ℕ) : ℝ := ∑ i ∈ Finset.range n, L i

theorem totalLength_succ (L : ℕ → ℝ) (n : ℕ) :
    totalLength L (n + 1) = totalLength L n + L n := by
  simp [totalLength, Finset.sum_range_succ]

/-- The projective loss is governed by total length, exactly. -/
theorem prefixProduct_exp (L : ℕ → ℝ) (n : ℕ) :
    prefixProduct (fun i => Real.exp (-L i)) n = Real.exp (-(2 * totalLength L n)) := by
  induction n with
  | zero => simp [prefixProduct, totalLength]
  | succ n ih =>
      rw [prefixProduct_succ, ih, totalLength_succ, pow_two, ← Real.exp_add,
        ← Real.exp_add]
      congr 1
      ring

theorem radiusIterate_exponential_formula (L : ℕ → ℝ)
    (hL : ∀ i, 0 < L i) {a : ℝ} (ha : 1 ≤ a) (n : ℕ) :
    radiusIterate (fun i => Real.exp (-L i)) a n =
      fromProjective (Real.exp (-(2 * totalLength L n)) * projective a) := by
  rw [radiusIterate_formula (fun i => Real.exp (-L i))
    (fun i => (Real.exp_pos _).le)
    (fun i => Real.exp_lt_one_iff.mpr (by linarith [hL i])) ha n,
    prefixProduct_exp]

theorem exponential_universal_bound (L : ℕ → ℝ)
    (hL : ∀ i, 0 < L i) {a : ℝ} (ha : 1 ≤ a) {n : ℕ} (hn : 0 < n) :
    radiusIterate (fun i => Real.exp (-L i)) a n ≤
      fromProjective (Real.exp (-(2 * totalLength L n))) := by
  have h := radiusIterate_le_universal (fun i => Real.exp (-L i))
    (fun i => (Real.exp_pos _).le)
    (fun i => Real.exp_lt_one_iff.mpr (by linarith [hL i])) ha hn
  simpa only [prefixProduct_exp] using h

/-- Divergence of accumulated length suffices; the individual attenuation
factors are not assumed summable. -/
theorem exponential_product_tendsto_zero (L : ℕ → ℝ)
    (hL : Tendsto (totalLength L) atTop atTop) :
    Tendsto (prefixProduct (fun i => Real.exp (-L i))) atTop (𝓝 0) := by
  have hclock : Tendsto (fun n => 2 * totalLength L n) atTop atTop :=
    hL.const_mul_atTop (by norm_num : (0 : ℝ) < 2)
  have h := Real.tendsto_exp_neg_atTop_nhds_zero.comp hclock
  have hfun : prefixProduct (fun i => Real.exp (-L i)) =
      (fun n => Real.exp (-(2 * totalLength L n))) := funext (prefixProduct_exp L)
  rw [hfun]
  exact h

/-- All-depth terminal-independence of the annular comparison radius. -/
theorem divergent_length_forgets_terminal_radius (L : ℕ → ℝ)
    (hpos : ∀ i, 0 < L i) (hdiv : Tendsto (totalLength L) atTop atTop)
    (a : ℕ → ℝ) (ha : ∀ n, 1 ≤ a n) :
    Tendsto (fun n => radiusIterate (fun i => Real.exp (-L i)) (a n) n)
      atTop (𝓝 1) := by
  exact varying_terminal_radius_tendsto_one (fun i => Real.exp (-L i))
    (fun i => (Real.exp_pos _).le)
    (fun i => Real.exp_lt_one_iff.mpr (by linarith [hpos i]))
    (exponential_product_tendsto_zero L hdiv) a ha

end
end AnnularResponseClock

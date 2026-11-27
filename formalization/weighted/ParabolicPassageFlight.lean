import ParabolicTipRate
import Mathlib

/-!
# Finite elapsed-time and angular accounting

A quadratic lower drift bounds the time omitted outside a central flight
interval.  Angular increments telescope over the retained interval with
an exact elapsed-time error factor.  No passage-time asymptotic is an input.
-/

namespace LoopsParabolic

open Set Function
open scoped BigOperators

noncomputable section

/-- Finite elapsed drift is exactly the difference of the endpoint positions. -/
theorem passage_sum_drift (w : ℕ → ℝ) (k : ℕ) :
    (∑ j ∈ Finset.range k, (w (j+1)-w j)) = w k-w 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    ring

/-- The same telescope on an arbitrary consecutive time interval. -/
theorem passage_sum_drift_Ico (w : ℕ → ℝ) (l m : ℕ) (hlm : l ≤ m) :
    (∑ j ∈ Finset.Ico l m, (w (j+1)-w j)) = w m-w l := by
  induction m with
  | zero =>
    have hl : l = 0 := by omega
    subst l
    simp
  | succ m ih =>
    by_cases h : l ≤ m
    · rw [Finset.sum_Ico_succ_top h, ih h]
      ring
    · have hl : l = m+1 := by omega
      subst l
      simp

/-- The steps whose initial positions are outside a fixed bottleneck. -/
def passageOuterTimes (w : ℕ → ℝ) (a δ : ℝ) (k : ℕ) : Finset ℕ :=
  (Finset.range k).filter (fun j => δ ≤ |w j-a|)

/-- A quadratic lower drift bounds the number of outer steps independently
of the total flight time.  No bound on the central elapsed time is used. -/
theorem passage_outer_time_budget (w : ℕ → ℝ) (a δ : ℝ) (k : ℕ)
    (hδ : 0 ≤ δ)
    (hstep : ∀ j < k, (w j-a)^2 ≤ w (j+1)-w j) :
    (passageOuterTimes w a δ k).card * δ^2 ≤ w k-w 0 := by
  have hnonneg : ∀ j ∈ Finset.range k, 0 ≤ w (j+1)-w j := by
    intro j hj
    exact (sq_nonneg (w j-a)).trans (hstep j (Finset.mem_range.mp hj))
  have hfirst :
      (∑ j ∈ passageOuterTimes w a δ k, δ^2) ≤
        ∑ j ∈ passageOuterTimes w a δ k, (w (j+1)-w j) := by
    apply Finset.sum_le_sum
    intro j hj
    have hm := Finset.mem_filter.mp hj
    have hs := pow_le_pow_left₀ hδ hm.2 2
    rw [sq_abs] at hs
    exact hs.trans (hstep j (Finset.mem_range.mp hm.1))
  have hsecond :
      (∑ j ∈ passageOuterTimes w a δ k, (w (j+1)-w j)) ≤
        ∑ j ∈ Finset.range k, (w (j+1)-w j) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.filter_subset (fun j => δ ≤ |w j-a|) (Finset.range k))
    intro j hj _
    exact hnonneg j hj
  calc
    (passageOuterTimes w a δ k).card * δ^2 =
        ∑ j ∈ passageOuterTimes w a δ k, δ^2 := by simp
    _ ≤ ∑ j ∈ passageOuterTimes w a δ k, (w (j+1)-w j) := hfirst
    _ ≤ ∑ j ∈ Finset.range k, (w (j+1)-w j) := hsecond
    _ = w k-w 0 := passage_sum_drift w k

/-- Steps before and after a declared central interval are controlled by
the same outside-time budget. -/
theorem passage_complement_time_budget (w : ℕ → ℝ) (a δ : ℝ)
    (k l m : ℕ) (hδ : 0 ≤ δ)
    (hstep : ∀ j < k, (w j-a)^2 ≤ w (j+1)-w j)
    (hout : ∀ j < k, j ∉ Finset.Ico l m → δ ≤ |w j-a|) :
    ((k-(m-l) : ℕ) : ℝ) * δ^2 ≤ w k-w 0 := by
  have hcover : Finset.range k ⊆
      Finset.Ico l m ∪ passageOuterTimes w a δ k := by
    intro j hj
    by_cases hcentral : j ∈ Finset.Ico l m
    · exact Finset.mem_union.mpr (Or.inl hcentral)
    · apply Finset.mem_union.mpr
      right
      exact Finset.mem_filter.mpr ⟨hj, hout j (Finset.mem_range.mp hj) hcentral⟩
  have hcard := (Finset.card_le_card hcover).trans
    (Finset.card_union_le (Finset.Ico l m) (passageOuterTimes w a δ k))
  simp only [Finset.card_range, Nat.card_Ico] at hcard
  have hnat : k-(m-l) ≤ (passageOuterTimes w a δ k).card := by omega
  have hreal : ((k-(m-l) : ℕ) : ℝ) ≤
      ((passageOuterTimes w a δ k).card : ℝ) := by exact_mod_cast hnat
  exact (mul_le_mul_of_nonneg_right hreal (sq_nonneg δ)).trans
    (passage_outer_time_budget w a δ k hδ hstep)

/-- Constant lower and upper angular step estimates telescope over any
consecutive retained interval with its exact number of steps. -/
theorem passage_angle_sandwich (θ : ℕ → ℝ) (l m : ℕ) (hlm : l ≤ m)
    (L U : ℝ)
    (hstep : ∀ j ∈ Finset.Ico l m,
      L ≤ θ (j+1)-θ j ∧ θ (j+1)-θ j ≤ U) :
    ((m-l : ℕ) : ℝ)*L ≤ θ m-θ l ∧
      θ m-θ l ≤ ((m-l : ℕ) : ℝ)*U := by
  have hlo : (∑ j ∈ Finset.Ico l m, L) ≤
      ∑ j ∈ Finset.Ico l m, (θ (j+1)-θ j) := by
    exact Finset.sum_le_sum (fun j hj => (hstep j hj).1)
  have hup : (∑ j ∈ Finset.Ico l m, (θ (j+1)-θ j)) ≤
      ∑ j ∈ Finset.Ico l m, U := by
    exact Finset.sum_le_sum (fun j hj => (hstep j hj).2)
  rw [passage_sum_drift_Ico θ l m hlm] at hlo hup
  simpa using And.intro hlo hup

/-- Relative one-step angular errors retain their exact elapsed-time
factor after telescoping. -/
theorem passage_angle_error (θ : ℕ → ℝ) (l m : ℕ) (hlm : l ≤ m)
    (u ε : ℝ)
    (hstep : ∀ j ∈ Finset.Ico l m,
      |(θ (j+1)-θ j)-u| ≤ ε*u) :
    |((m-l : ℕ) : ℝ)*u-(θ m-θ l)| ≤
      ε*((m-l : ℕ) : ℝ)*u := by
  have hs := passage_angle_sandwich θ l m hlm (u-ε*u) (u+ε*u) (by
    intro j hj
    have h := abs_le.mp (hstep j hj)
    constructor <;> linarith)
  apply abs_le.mpr
  constructor <;> nlinarith only [hs.1, hs.2]


end

end LoopsParabolic

import ParabolicTipRate
import Mathlib

/-!
# Finite-flight localization for the actual parabolic channel

The outer-time estimate is a finite telescoping estimate.  The crossing
lemmas use the true reflected quadratic iterate and the existing channel
bounds, so no passage-time asymptotic is an input.
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

theorem passage_outer_time_bound (w : ℕ → ℝ) (a δ D : ℝ) (k : ℕ)
    (hδ : 0 < δ)
    (hstep : ∀ j < k, (w j-a)^2 ≤ w (j+1)-w j)
    (hspan : w k-w 0 ≤ D) :
    ((passageOuterTimes w a δ k).card : ℝ) ≤ D/δ^2 := by
  apply (le_div_iff₀ (by positivity : 0 < δ^2)).mpr
  exact (passage_outer_time_budget w a δ k hδ.le hstep).trans hspan

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

/-- Explicit prefix and suffix estimates give the elapsed-time error made
by retaining only the central interval. -/
theorem passage_missing_time_budget (w : ℕ → ℝ) (a δ D : ℝ)
    (k l m : ℕ) (hlm : l ≤ m) (hmk : m ≤ k) (hδ : 0 ≤ δ)
    (hstep : ∀ j < k, (w j-a)^2 ≤ w (j+1)-w j)
    (hleft : ∀ j < l, w j ≤ a-δ)
    (hright : ∀ j, m ≤ j → j < k → a+δ ≤ w j)
    (hspan : w k-w 0 ≤ D) :
    ((l+(k-m) : ℕ) : ℝ) * δ^2 ≤ D := by
  have hout : ∀ j < k, j ∉ Finset.Ico l m → δ ≤ |w j-a| := by
    intro j hj hnot
    by_cases hjl : j < l
    · linarith [hleft j hjl, neg_abs_le (w j-a)]
    · have hmj : m ≤ j := by
        simp only [Finset.mem_Ico] at hnot
        omega
      linarith [hright j hmj hj, le_abs_self (w j-a)]
  have h := passage_complement_time_budget w a δ k l m hδ hstep hout
  have he : k-(m-l) = l+(k-m) := by omega
  rw [he] at h
  exact h.trans hspan

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

/-- A finite orbit segment has a first crossing whenever its endpoints
lie on opposite sides of the threshold. -/
theorem passage_first_hit (w : ℕ → ℝ) (k : ℕ) (r : ℝ)
    (hstart : w 0 < r) (hfinish : r ≤ w k) :
    ∃ m : ℕ, 0 < m ∧ m ≤ k ∧ r ≤ w m ∧ ∀ j < m, w j < r := by
  have hex : ∃ j : ℕ, j ≤ k ∧ r ≤ w j := ⟨k, le_rfl, hfinish⟩
  let m := Nat.find hex
  have hm : m ≤ k ∧ r ≤ w m := Nat.find_spec hex
  have hmpos : 0 < m := by
    by_contra h
    have he : m = 0 := by omega
    rw [he] at hm
    exact (not_le_of_gt hstart) hm.2
  refine ⟨m, hmpos, hm.1, hm.2, ?_⟩
  intro j hj
  by_contra! hrj
  have hle : m ≤ j := Nat.find_min' hex ⟨by omega, hrj⟩
  omega

/-- Consecutive nonnegative increments imply monotonicity through the
finite stopping time, without any assumption after that time. -/
theorem passage_mono_upto (w : ℕ → ℝ) (k : ℕ)
    (hstep : ∀ j < k, w j ≤ w (j+1)) :
    ∀ i j : ℕ, i ≤ j → j ≤ k → w i ≤ w j := by
  intro i j hij hjk
  induction j with
  | zero =>
    have hi : i = 0 := by omega
    subst i
    exact le_rfl
  | succ j ih =>
    by_cases h : i ≤ j
    · exact (ih h (by omega)).trans (hstep j (by omega))
    · have hi : i = j+1 := by omega
      subst i
      exact le_rfl

/-- Outside the channel center, the true physical flight has uniformly
bounded elapsed time for every fixed positive window. -/
theorem channel_outer_time_bound {t a δ : ℝ} {k : ℕ}
    (ht : t ∈ Icc 0 (1/100 : ℝ))
    (ha : a ∈ Icc (1/20 : ℝ) (3/50)) (root : cubic a = 0)
    (hδ : 0 < δ)
    (stay : ∀ j ≤ k, (H t)^[j] 0 ∈ Icc 0 cap) :
    ((passageOuterTimes (fun j => (H t)^[j] 0) a δ k).card : ℝ) ≤ cap/δ^2 := by
  apply passage_outer_time_bound (fun j => (H t)^[j] 0) a δ cap k hδ
  · intro j hj
    have hl := (channel_quadratic_step ht (stay j (by omega)) ha root).1
    rw [Function.iterate_succ_apply']
    linarith [ht.1]
  · simpa using (stay k le_rfl).2

/-- A step entering the lower bottleneck wall cannot jump across its
negative half: monotonicity compares it with the true step at the wall. -/
theorem channel_lower_wall_step {t a δ y : ℝ}
    (ht : t ∈ Icc 0 (1/100 : ℝ))
    (ha : a ∈ Icc (1/20 : ℝ) (3/50)) (root : cubic a = 0)
    (hδ : 0 ≤ δ) (hδa : δ ≤ a)
    (hy : y ∈ Icc 0 cap) (hbelow : y ≤ a-δ)
    (hsmall : 10*t+20*δ^2 ≤ δ/2) :
    H t y ≤ a-δ/2 := by
  have hedge : a-δ ∈ Icc 0 cap := by
    constructor
    · linarith
    · unfold cap
      linarith [ha.2]
  have hmono := channel_mono ht hy hedge hbelow
  have hup := (channel_quadratic_step ht hedge ha root).2
  have hs : (a-δ-a)^2 = δ^2 := by ring
  rw [hs] at hup
  linarith

/-- Every step starting inside the fixed central window ends in the
twice-sized window once its quadratic overshoot is small enough. -/
theorem channel_central_step_upper {t a δ y : ℝ}
    (ht : t ∈ Icc 0 (1/100 : ℝ))
    (ha : a ∈ Icc (1/20 : ℝ) (3/50)) (root : cubic a = 0)
    (hy : y ∈ Icc 0 cap) (hcentral : |y-a| ≤ δ)
    (hsmall : 10*t+20*δ^2 ≤ δ) :
    H t y ≤ a+2*δ := by
  have hδ : 0 ≤ δ := (abs_nonneg (y-a)).trans hcentral
  have hs := pow_le_pow_left₀ (abs_nonneg (y-a)) hcentral 2
  rw [sq_abs] at hs
  have hup := (channel_quadratic_step ht hy ha root).2
  have hyup := (abs_le.mp hcentral).2
  linarith

end

end LoopsParabolic

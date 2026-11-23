import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FunProp

/-!
# The period-three channel at the real parabolic parameter −7/4

The reflected third iterate drifts by at least t/2 on the full entrance
corridor when c = −7/4 + t. At t = 0 a fixed point traps the critical orbit.
-/
namespace LoopsParabolic

open Set Function Filter Topology
noncomputable section

def quad (c x : ℝ) : ℝ := x^2 + c

/-- Reflection of the third iterate of the quadratic polynomial. -/
def H (t y : ℝ) : ℝ :=
  (7/4-t) - (((7/4-t-y^2)^2 - (7/4-t))^2)

theorem reflected (t y : ℝ) : H t y = -((quad (-7/4+t))^[3] (-y)) := by
  simp only [Function.iterate_succ_apply, Function.iterate_zero, id_eq, H, quad]
  ring

@[fun_prop] theorem continuous_H {f g : ℝ → ℝ} (hf : Continuous f)
    (hg : Continuous g) : Continuous (fun x => H (f x) (g x)) := by
  unfold H
  fun_prop

@[fun_prop] theorem continuous_H_iter (n : ℕ) {f g : ℝ → ℝ}
    (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun x => (H (f x))^[n] (g x)) := by
  induction n with
  | zero => simpa using hg
  | succ n ih =>
    simp only [Function.iterate_succ_apply']
    exact continuous_H hf ih

def cap : ℝ := 2/5
def cubic (y : ℝ) : ℝ := -8*y^3+4*y^2+18*y-1

theorem parabolic_identity (y : ℝ) :
    H 0 y - y = (7-4*y^2-4*y) * (cubic y)^2 / 256 := by
  unfold H cubic
  ring

private theorem inner_lower {y t : ℝ} (hy : y ∈ Icc 0 cap)
    (ht : t ∈ Icc 0 (1/100 : ℝ)) : 3/2 ≤ 7/4-t-y^2 := by
  obtain ⟨h₁,h₂⟩ := hy
  unfold cap at h₂
  nlinarith [sq_le_sq' (by linarith : -(2/5 : ℝ) ≤ y) h₂, ht.2]

theorem channel_mono {t : ℝ} (ht : t ∈ Icc 0 (1/100 : ℝ)) :
    MonotoneOn (H t) (Icc 0 cap) := by
  intro x hx y hy hxy
  have hs := pow_le_pow_left₀ hx.1 hxy 2
  have h₁ := inner_lower hy ht
  have hp := pow_le_pow_left₀ (by linarith : 0 ≤ 7/4-t-y^2)
    (by linarith : 7/4-t-y^2 ≤ 7/4-t-x^2) 2
  have h₂ : 0 ≤ (7/4-t-y^2)^2-(7/4-t) := by
    nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 3/2) h₁ 2, ht.1]
  unfold H
  have hh := pow_le_pow_left₀ h₂ (by linarith :
    (7/4-t-y^2)^2-(7/4-t) ≤ (7/4-t-x^2)^2-(7/4-t)) 2
  linarith

/-- A lower bound for every channel step, including the parabolic bottleneck. -/
theorem channel_drift {t y : ℝ} (ht : t ∈ Icc 0 (1/100 : ℝ))
    (hy : y ∈ Icc 0 cap) : y+t/2 ≤ H t y := by
  have h₁ := inner_lower hy ht
  have h₀ := inner_lower hy (show (0:ℝ) ∈ Icc 0 (1/100 : ℝ) by constructor <;> norm_num)
  let A := 7/4-y^2
  let B := A^2-7/4
  let C := (A-t)^2-(7/4-t)
  have ha : 3/2 ≤ A := by dsimp [A]; linarith
  have hat : 3/2 ≤ A-t := by dsimp [A]; linarith
  have hb : 1/2 ≤ B := by
    dsimp [B]; nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 3/2) ha 2]
  have hc : 1/2 ≤ C := by
    dsimp [C]; nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 3/2) hat 2, ht.1]
  have hfac : 3/2 ≤ 2*A-1-t := by linarith [ht.2]
  have hprod := mul_le_mul hfac (show 1 ≤ B+C by linarith) (by norm_num) (by linarith)
  have hdiff : H t y - H 0 y = t*((2*A-1-t)*(B+C)-1) := by
    dsimp [H,A,B,C]; ring
  have h₃ := mul_le_mul_of_nonneg_left
    (show (1:ℝ)/2 ≤ (2*A-1-t)*(B+C)-1 by linarith) ht.1
  have hcap := hy.2
  unfold cap at hcap
  have hcoef : 0 ≤ 7-4*y^2-4*y := by
    nlinarith [sq_le_sq' (by linarith [hy.1] : -(2/5 : ℝ) ≤ y) hcap]
  have hnonneg : 0 ≤ H 0 y-y := by rw [parabolic_identity]; positivity
  linarith

/-- Parameter-continuous recording of the approach to the first exit. -/
def flight (t z : ℝ) : ℕ → ℝ
  | 0 => z
  | k+1 => min cap (H t (flight t z k))

abbrev track (t : ℝ) := flight t 0

@[fun_prop] theorem continuous_flight (k : ℕ) {f g : ℝ → ℝ}
    (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun t => flight (f t) (g t) k) := by
  induction k with
  | zero => exact hg
  | succ k ih => exact continuous_const.min (continuous_H hf ih)

@[fun_prop] theorem continuous_track (k : ℕ) : Continuous (fun t => track t k) := by
  induction k with
  | zero => exact continuous_const
  | succ k ih => exact continuous_const.min (continuous_H continuous_id ih)

theorem flight_mem {t z : ℝ} (ht : t ∈ Icc 0 (1/100 : ℝ)) (hz : z ∈ Icc 0 cap)
    (k : ℕ) : flight t z k ∈ Icc 0 cap := by
  induction k with
  | zero => exact hz
  | succ k ih =>
    refine ⟨le_min (by norm_num [cap]) ?_, min_le_left _ _⟩
    linarith [channel_drift ht ih, ih.1, ht.1]

theorem flight_steps {t z : ℝ} (ht : t ∈ Icc 0 (1/100 : ℝ)) (hz : z ∈ Icc 0 cap) :
    Monotone (flight t z) := by
  apply monotone_nat_of_le_succ
  intro k
  apply le_min (flight_mem ht hz k).2
  linarith [channel_drift ht (flight_mem ht hz k), ht.1]

theorem flight_true {k : ℕ} {t z : ℝ} (ht : t ∈ Icc 0 (1/100 : ℝ))
    (hz : z ∈ Icc 0 cap) (hk : flight t z k < cap) :
    (H t)^[k] z = flight t z k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih (lt_of_le_of_lt
      (flight_steps ht hz (Nat.le_succ k)) hk)]
    change min cap (H t (flight t z k)) < cap at hk
    change _ = min cap _
    exact (min_eq_right (lt_of_not_ge (fun h => by rw [min_eq_left h] at hk; exact lt_irrefl _ hk)).le).symm

theorem flight_compare {t z w : ℝ} (ht : t ∈ Icc 0 (1/100 : ℝ))
    (hz : z ∈ Icc 0 cap) (hw : w ∈ Icc 0 cap) (h : z ≤ w) (k : ℕ) :
    flight t z k ≤ flight t w k := by
  induction k with
  | zero => exact h
  | succ k ih => exact min_le_min_left _ (channel_mono ht (flight_mem ht hz k)
      (flight_mem ht hw k) ih)

theorem flight_shift (t z : ℝ) (k : ℕ) :
    flight t (min cap (H t z)) k = flight t z (k+1) := by
  induction k with
  | zero => rfl
  | succ k ih => change min cap (H t _) = min cap (H t _); rw [ih]

theorem track_mem {t : ℝ} (ht : t ∈ Icc 0 (1/100 : ℝ)) (k : ℕ) :
    track t k ∈ Icc 0 cap := flight_mem ht (by constructor <;> norm_num [cap]) k

theorem track_step {t : ℝ} (ht : t ∈ Icc 0 (1/100 : ℝ)) (k : ℕ) :
    track t k ≤ track t (k+1) := by
  apply le_min (track_mem ht k).2
  linarith [channel_drift ht (track_mem ht k), ht.1]

theorem track_true {k : ℕ} {t : ℝ} (ht : t ∈ Icc 0 (1/100 : ℝ))
    (hk : track t k < cap) : (H t)^[k] 0 = track t k :=
  flight_true ht (by constructor <;> norm_num [cap]) hk

theorem parabolic_trap (k : ℕ) : track 0 k ≤ 3/50 := by
  have hcont : Continuous cubic := by unfold cubic; fun_prop
  obtain ⟨a,ha,he⟩ := intermediate_value_Icc (by norm_num : (1/20:ℝ) ≤ 3/50)
    hcont.continuousOn (show (0:ℝ) ∈ Icc (cubic (1/20)) (cubic (3/50)) by
      constructor <;> norm_num [cubic])
  have ha0 : 0 ≤ a := by linarith [ha.1]
  have hac : a ≤ cap := by unfold cap; linarith [ha.2]
  have hfix := parabolic_identity a
  rw [he] at hfix
  have hfix' : H 0 a = a := by linarith
  have ht : (0:ℝ) ∈ Icc 0 (1/100 : ℝ) := by constructor <;> norm_num
  suffices h : track 0 k ≤ a from h.trans ha.2
  induction k with
  | zero => exact ha0
  | succ k ih =>
    apply (min_le_right _ _).trans
    exact (channel_mono ht (track_mem ht k) ⟨ha0,hac⟩ ih).trans hfix'.le

end
end LoopsParabolic

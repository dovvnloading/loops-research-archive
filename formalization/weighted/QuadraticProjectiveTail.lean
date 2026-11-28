import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# Normalized critical-orbit tails

Polynomial identities for the normalized quartic return map.  The actual
quadratic-family identifications are proved in `QuadraticProjectiveActual`.
-/

noncomputable section

namespace LoopsQuadraticProjective

open Polynomial

/-- The critical orbit after removing its forced power of the multiplier. -/
def a (e : ℂ) : ℕ → ℂ[X]
  | 0 => C (-1 / 2)
  | n + 1 => a e n + X ^ n * (a e n) ^ 2 *
      (1 + C e * X ^ 2 * (1 + X ^ n * a e n) ^ 2)

/-- Increment of the normalized orbit, without its forced multiplier power. -/
def inc (e : ℂ) (n : ℕ) : ℂ[X] :=
  (a e n) ^ 2 * (1 + C e * X ^ 2 * (1 + X ^ n * a e n) ^ 2)

/-- The exact divided difference between two normalized orbit marks. -/
def H (e : ℂ) (m : ℕ) : ℕ → ℂ[X]
  | 0 => 0
  | k + 1 => H e m k + X ^ k * inc e (m + k)

@[simp] theorem a_zero (e : ℂ) : a e 0 = C (-1 / 2) := rfl

theorem a_succ (e : ℂ) (n : ℕ) :
    a e (n + 1) = a e n + X ^ n * inc e n := by
  simp only [a, inc, mul_assoc]

@[simp] theorem H_zero (e : ℂ) (m : ℕ) : H e m 0 = 0 := rfl

theorem H_succ (e : ℂ) (m k : ℕ) :
    H e m (k + 1) = H e m k + X ^ k * inc e (m + k) := rfl

/-- Exact telescope, retaining the vanishing multiplier power. -/
theorem a_add (e : ℂ) (m k : ℕ) :
    a e (m + k) = a e m + X ^ m * H e m k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.add_succ, a_succ, ih, H_succ, pow_add]
    ring

/-- The first normalized mark has a nonzero constant term. -/
theorem a_one_eval_zero (e : ℂ) : (a e 1).eval 0 = -1 / 4 := by
  norm_num [a]

/-- All positive normalized orbit marks have the same constant term. -/
theorem a_eval_zero (e : ℂ) (n : ℕ) (hn : 1 ≤ n) :
    (a e n).eval 0 = -1 / 4 := by
  cases n with
  | zero => omega
  | succ n =>
    induction n with
    | zero => exact a_one_eval_zero e
    | succ n ih =>
      rw [a_succ]
      simpa using ih (by omega)

theorem inc_eval_zero (e : ℂ) (n : ℕ) (hn : 1 ≤ n) :
    (inc e n).eval 0 = 1 / 16 := by
  simp only [inc, eval_mul, eval_pow, eval_add, eval_one, eval_C, eval_X]
  rw [a_eval_zero e n hn]
  norm_num

/-- Every nonempty divided tail starting after the first mark is a unit at zero. -/
theorem H_eval_zero (e : ℂ) (m k : ℕ) (hm : 1 ≤ m) (hk : 1 ≤ k) :
    (H e m k).eval 0 = 1 / 16 := by
  cases k with
  | zero => omega
  | succ k =>
    induction k with
    | zero => simpa [H] using inc_eval_zero e m hm
    | succ k ih =>
      rw [H_succ]
      simpa using ih (by omega)

/-- Agreement through degree two, expressed without power-series machinery. -/
def JetEq (p q : ℂ[X]) : Prop := (X : ℂ[X]) ^ 3 ∣ p - q

theorem JetEq.refl (p : ℂ[X]) : JetEq p p := by
  exact ⟨0, by ring⟩

theorem JetEq.symm {p q : ℂ[X]} (h : JetEq p q) : JetEq q p := by
  obtain ⟨r, hr⟩ := h
  exact ⟨-r, by linear_combination -hr⟩

theorem JetEq.trans {p q r : ℂ[X]} (hpq : JetEq p q) (hqr : JetEq q r) :
    JetEq p r := by
  obtain ⟨u, hu⟩ := hpq
  obtain ⟨v, hv⟩ := hqr
  exact ⟨u + v, by linear_combination hu + hv⟩

theorem JetEq.add {p q r s : ℂ[X]} (hpq : JetEq p q) (hrs : JetEq r s) :
    JetEq (p + r) (q + s) := by
  obtain ⟨u, hu⟩ := hpq
  obtain ⟨v, hv⟩ := hrs
  exact ⟨u + v, by linear_combination hu + hv⟩

theorem JetEq.mul {p q r s : ℂ[X]} (hpq : JetEq p q) (hrs : JetEq r s) :
    JetEq (p * r) (q * s) := by
  obtain ⟨u, hu⟩ := hpq
  obtain ⟨v, hv⟩ := hrs
  exact ⟨u * r + q * v, by linear_combination r * hu + q * hv⟩

theorem JetEq.pow {p q : ℂ[X]} (h : JetEq p q) (n : ℕ) : JetEq (p ^ n) (q ^ n) := by
  induction n with
  | zero => exact JetEq.refl _
  | succ n ih => simpa only [pow_succ] using ih.mul h

theorem JetEq.of_eq {p q : ℂ[X]} (h : p = q) : JetEq p q := by
  subst q
  exact JetEq.refl _

theorem jet_X_pow (n : ℕ) (hn : 3 ≤ n) : JetEq ((X : ℂ[X]) ^ n) 0 := by
  simpa only [JetEq, sub_zero] using pow_dvd_pow (X : ℂ[X]) hn

/-- A quadratic polynomial recording exactly three Taylor coefficients. -/
def jetPoly (u v w : ℂ) : ℂ[X] := C u + C v * X + C w * X ^ 2

theorem jetPoly_add (u v w r s t : ℂ) :
    jetPoly u v w + jetPoly r s t = jetPoly (u + r) (v + s) (w + t) := by
  simp only [jetPoly, map_add]
  ring

theorem jetPoly_mul (u v w r s t : ℂ) :
    JetEq (jetPoly u v w * jetPoly r s t)
      (jetPoly (u * r) (u * s + v * r) (u * t + v * s + w * r)) := by
  refine ⟨C (v * t + w * s) + C (w * t) * X, ?_⟩
  simp only [jetPoly, map_add, map_mul]
  ring

theorem jetPoly_congr {u v w r s t : ℂ} (hu : u = r) (hv : v = s) (hw : w = t) :
    jetPoly u v w = jetPoly r s t := by rw [hu, hv, hw]

theorem jetPoly_sq (u v w : ℂ) :
    JetEq ((jetPoly u v w) ^ 2)
      (jetPoly (u ^ 2) (2 * u * v) (v ^ 2 + 2 * u * w)) := by
  have h := jetPoly_mul u v w u v w
  rw [← pow_two] at h
  apply h.trans
  apply JetEq.of_eq
  apply jetPoly_congr <;> ring

theorem jet_X_mul (u v w : ℂ) :
    JetEq (X * jetPoly u v w) (jetPoly 0 u v) := by
  simpa [jetPoly] using jetPoly_mul 0 1 0 u v w

theorem jet_X_sq_mul (u v w : ℂ) :
    JetEq (X ^ 2 * jetPoly u v w) (jetPoly 0 0 u) := by
  simpa [jetPoly] using jetPoly_mul 0 0 1 u v w

theorem a_one (e : ℂ) : a e 1 = jetPoly (-1 / 4) 0 (e / 16) := by
  have h₁ : (C (-1 / 2 : ℂ) : ℂ[X]) + C (-1 / 2 : ℂ) ^ 2 = C (-1 / 4 : ℂ) := by
    rw [← map_pow, ← map_add]
    norm_num
  have h₂ : (C (-1 / 2 : ℂ) : ℂ[X]) ^ 2 * (1 + C (-1 / 2 : ℂ)) ^ 2 =
      C (1 / 16 : ℂ) := by
    rw [← C_1, ← map_add, ← map_pow, ← map_pow, ← map_mul]
    norm_num
  calc
    a e 1 = (C (-1 / 2 : ℂ) + C (-1 / 2 : ℂ) ^ 2) +
        C e * X ^ 2 * (C (-1 / 2 : ℂ) ^ 2 * (1 + C (-1 / 2 : ℂ)) ^ 2) := by
      simp only [a, pow_zero, one_mul]
      ring
    _ = C (-1 / 4 : ℂ) + C e * X ^ 2 * C (1 / 16 : ℂ) := by rw [h₁, h₂]
    _ = jetPoly (-1 / 4) 0 (e / 16) := by
      rw [show e / 16 = e * (1 / 16) by ring]
      simp only [jetPoly, map_zero, zero_mul, add_zero, map_mul]
      ring

/-- The quartic term starts above the retained jet after the first iterate. -/
theorem a_succ_jet (e : ℂ) (n : ℕ) (hn : 1 ≤ n) :
    JetEq (a e (n + 1)) (a e n + X ^ n * (a e n) ^ 2) := by
  have h := (jet_X_pow (n + 2) (by omega)).mul
    (JetEq.refl (C e * (a e n) ^ 2 * (1 + X ^ n * a e n) ^ 2))
  have hh := (JetEq.refl (a e n + X ^ n * (a e n) ^ 2)).add h
  convert hh using 1 <;> (try simp only [a, pow_add]) <;> ring

theorem a_two_jet (e : ℂ) : JetEq (a e 2) (jetPoly (-1 / 4) (1 / 16) (e / 16)) := by
  have hs : JetEq ((a e 1) ^ 2) (jetPoly (1 / 16) 0 (-e / 32)) := by
    rw [a_one]
    apply (jetPoly_sq (-1 / 4) 0 (e / 16)).trans
    apply JetEq.of_eq
    apply jetPoly_congr <;> ring
  have hx := (JetEq.refl (X : ℂ[X])).mul hs
  have hx' := hx.trans (jet_X_mul (1 / 16) 0 (-e / 32))
  have ha := (JetEq.of_eq (a_one e)).add hx'
  apply (a_succ_jet e 1 (by omega)).trans
  simpa only [pow_one, jetPoly_add, add_zero, zero_add] using ha

theorem a_three_jet (e : ℂ) :
    JetEq (a e 3) (jetPoly (-1 / 4) (1 / 16) ((1 + e) / 16)) := by
  have hs := (a_two_jet e).pow 2
  have hs' := hs.trans (jetPoly_sq (-1 / 4) (1 / 16) (e / 16))
  have hx := (JetEq.refl ((X : ℂ[X]) ^ 2)).mul hs'
  have hx' := hx.trans (jet_X_sq_mul ((-1 / 4) ^ 2)
    (2 * (-1 / 4) * (1 / 16)) ((1 / 16) ^ 2 + 2 * (-1 / 4) * (e / 16)))
  have ha := (a_two_jet e).add hx'
  apply (a_succ_jet e 2 (by omega)).trans
  apply ha.trans
  apply JetEq.of_eq
  rw [jetPoly_add]
  apply jetPoly_congr <;> ring

/-- Stabilization of the full quadratic jet at every return clock at least three. -/
theorem a_jet (e : ℂ) (k : ℕ) (hk : 3 ≤ k) :
    JetEq (a e k) (jetPoly (-1 / 4) (1 / 16) ((1 + e) / 16)) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  induction j with
  | zero => simpa using a_three_jet e
  | succ j ih =>
    rw [Nat.add_succ, a_succ]
    have h := (jet_X_pow (3 + j) (by omega)).mul (JetEq.refl (inc e (3 + j)))
    simpa using (ih (by omega)).add h

theorem inc_jet (e : ℂ) (n : ℕ) (hn : 3 ≤ n) :
    JetEq (inc e n) (jetPoly (1 / 16) (-1 / 32) ((8 * e - 7) / 256)) := by
  have ha := a_jet e n hn
  have hs := (ha.pow 2).trans (jetPoly_sq (-1 / 4) (1 / 16) ((1 + e) / 16))
  have hx := (jet_X_pow n hn).mul (JetEq.refl (a e n))
  have ht : JetEq ((1 + X ^ n * a e n) ^ 2) 1 := by
    simpa using ((JetEq.refl (1 : ℂ[X])).add hx).pow 2
  have hf : JetEq (1 + C e * X ^ 2 * (1 + X ^ n * a e n) ^ 2)
      (jetPoly 1 0 e) := by
    simpa [jetPoly] using (JetEq.refl (1 : ℂ[X])).add
      ((JetEq.refl (C e * X ^ 2)).mul ht)
  have hp := hs.mul hf
  have hm := jetPoly_mul ((-1 / 4) ^ 2) (2 * (-1 / 4) * (1 / 16))
    ((1 / 16) ^ 2 + 2 * (-1 / 4) * ((1 + e) / 16)) 1 0 e
  apply (hp.trans hm).trans
  apply JetEq.of_eq
  apply jetPoly_congr <;> ring

theorem H_three_jet (e : ℂ) (m : ℕ) (hm : 3 ≤ m) :
    JetEq (H e m 3) (jetPoly (1 / 16) (1 / 32) ((1 + 8 * e) / 256)) := by
  have h₀ := inc_jet e m hm
  have h₁ := ((JetEq.refl (X : ℂ[X])).mul (inc_jet e (m + 1) (by omega))).trans
    (jet_X_mul (1 / 16) (-1 / 32) ((8 * e - 7) / 256))
  have h₂ := ((JetEq.refl ((X : ℂ[X]) ^ 2)).mul (inc_jet e (m + 2) (by omega))).trans
    (jet_X_sq_mul (1 / 16) (-1 / 32) ((8 * e - 7) / 256))
  have hh := (h₀.add h₁).add h₂
  have hr : H e m 3 = inc e m + X * inc e (m + 1) + X ^ 2 * inc e (m + 2) := by
    simp [H]
  rw [hr]
  apply hh.trans
  apply JetEq.of_eq
  rw [jetPoly_add, jetPoly_add]
  apply jetPoly_congr <;> ring

/-- Every tail of length at least three has the same retained jet. -/
theorem H_long_jet (e : ℂ) (m k : ℕ) (hm : 3 ≤ m) (hk : 3 ≤ k) :
    JetEq (H e m k) (jetPoly (1 / 16) (1 / 32) ((1 + 8 * e) / 256)) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  induction j with
  | zero => simpa using H_three_jet e m hm
  | succ j ih =>
    rw [Nat.add_succ, H_succ]
    have h := (jet_X_pow (3 + j) (by omega)).mul (JetEq.refl (inc e (m + (3 + j))))
    simpa using (ih (by omega)).add h

/-- The normalized return-clock tail has an explicit, stabilized quadratic jet. -/
theorem H_jet (e : ℂ) (k : ℕ) (hk : 3 ≤ k) :
    JetEq (H e k k) (jetPoly (1 / 16) (1 / 32) ((1 + 8 * e) / 256)) :=
  H_long_jet e k k hk hk

end LoopsQuadraticProjective

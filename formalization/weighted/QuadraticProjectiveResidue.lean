import QuadraticProjectiveAlgebra
import QuadraticProjectiveTail

/-!
# The finite part of a critical-orbit projective configuration

The nonsingular quotient below retains the nonlinear correction after the
multiplier pole has been removed. Actual quadratic-family identifications
are made in `QuadraticProjectiveActual`.
-/

noncomputable section

namespace LoopsQuadraticProjective

open Polynomial

/-- A normalized mark; its zero-th member is the critical point. -/
def normalizedMark (e q : ℂ) (n : ℕ) : ℂ :=
  1 + 2*q^n*(a e n).eval q

/-- Four consecutive return-clock marks, anchored at the critical point. -/
def normalizedClock (e q : ℂ) (k : ℕ) : ℂ :=
  crossRatio 0 (normalizedMark e q k) (normalizedMark e q (2*k))
    (normalizedMark e q (3*k))

/-- Polynomial unit in the denominator of the finite part. -/
def denPoly (e : ℂ) (k : ℕ) : ℂ[X] :=
  (1 + 2*X^k*a e k)*(a e (2*k) - X^k*a e (3*k))

/-- Polynomial numerator of the finite part. -/
def remPoly (e : ℂ) (k : ℕ) : ℂ[X] :=
  H e k k + 2*a e k*a e (2*k) - 2*X^k*a e k*a e (3*k) -
    (X^k)^2*H e (2*k) k - 2*(X^k)^2*a e k*a e (3*k) +
    2*(X^k)^3*a e (2*k)*a e (3*k)

/-- The three coefficients which remove the singular projective jet. -/
def correctionPoly (e : ℂ) : ℂ[X] :=
  jetPoly (3/4) (1/16) (e/16)

theorem denPoly_eval (e q : ℂ) (k : ℕ) :
    (denPoly e k).eval q =
      clockDen (q^k) ((a e k).eval q) ((a e (2*k)).eval q)
        ((a e (3*k)).eval q) := by
  simp [denPoly, clockDen]

theorem remPoly_eval (e q : ℂ) (k : ℕ) :
    (remPoly e k).eval q =
      clockRem (q^k) ((a e k).eval q) ((a e (2*k)).eval q)
        ((a e (3*k)).eval q) ((H e k k).eval q) ((H e (2*k) k).eval q) := by
  simp [remPoly, clockRem]

/-- The finite-part denominator is nonzero at the center, for every clock. -/
theorem denPoly_eval_zero (e : ℂ) (k : ℕ) (hk : 1 ≤ k) :
    (denPoly e k).eval 0 = -1/4 := by
  have hk0 : k ≠ 0 := by omega
  have h2 : 1 ≤ 2*k := by omega
  simp [denPoly, hk0, a_eval_zero e (2*k) h2]

/-- The critical endpoint and nonlinear increment contribute the numerator 3/16. -/
theorem remPoly_eval_zero (e : ℂ) (k : ℕ) (hk : 1 ≤ k) :
    (remPoly e k).eval 0 = 3/16 := by
  have hk0 : k ≠ 0 := by omega
  have h2 : 1 ≤ 2*k := by omega
  simp [remPoly, hk0, a_eval_zero e k hk, a_eval_zero e (2*k) h2,
    H_eval_zero e k k hk hk]
  <;> norm_num

/-- Exact cancellation of the singular multiplier power on its full algebraic domain. -/
theorem normalizedClock_regular_part (e q : ℂ) (k : ℕ)
    (hq : q ≠ 0) (hD : (denPoly e k).eval q ≠ 0) :
    normalizedClock e q k + (q^k)⁻¹ =
      (remPoly e k).eval q / (denPoly e k).eval q := by
  have hB := congrArg (Polynomial.eval q) (a_add e k k)
  simp only [eval_add, eval_mul, eval_pow, eval_X] at hB
  have hB' : (a e (2*k)).eval q =
      (a e k).eval q + q^k*(H e k k).eval q := by
    simpa only [two_mul] using hB
  have hC := congrArg (Polynomial.eval q) (a_add e (2*k) k)
  simp only [eval_add, eval_mul, eval_pow, eval_X] at hC
  have h2 : q^(2*k) = (q^k)^2 := by rw [Nat.mul_comm 2 k, pow_mul]
  have h3 : q^(3*k) = (q^k)^3 := by rw [Nat.mul_comm 3 k, pow_mul]
  have hC' : (a e (3*k)).eval q =
      (a e (2*k)).eval q + (q^k)^2*(H e (2*k) k).eval q := by
    rw [h2] at hC
    convert hC using 1 <;> congr 2 <;> omega
  have hd : clockDen (q^k) ((a e k).eval q) ((a e (2*k)).eval q)
      ((a e (3*k)).eval q) ≠ 0 := by rwa [← denPoly_eval]
  have hr := crossRatio_scaled_regular_part 1 (q^k) ((a e k).eval q)
    ((a e (2*k)).eval q) ((a e (3*k)).eval q)
    ((H e k k).eval q) ((H e (2*k) k).eval q)
    one_ne_zero (pow_ne_zero k hq) hd hB' hC'
  simpa only [normalizedClock, normalizedMark, h2, h3, one_mul,
    denPoly_eval, remPoly_eval] using hr

theorem JetEq.neg {p q : ℂ[X]} (h : JetEq p q) : JetEq (-p) (-q) := by
  obtain ⟨r, hr⟩ := h
  exact ⟨-r, by linear_combination -hr⟩

theorem JetEq.sub {p q r s : ℂ[X]} (hpq : JetEq p q) (hrs : JetEq r s) :
    JetEq (p-r) (q-s) := by
  simpa only [sub_eq_add_neg] using hpq.add hrs.neg

/-- The clock denominator has the stabilized orbit jet. -/
theorem denPoly_jet (e : ℂ) (k : ℕ) (hk : 3 ≤ k) :
    JetEq (denPoly e k) (jetPoly (-1/4) (1/16) ((1+e)/16)) := by
  have hx := jet_X_pow k hk
  have ht : JetEq (2*X^k*a e k) 0 := by
    simpa using ((JetEq.refl (2 : ℂ[X])).mul hx).mul (JetEq.refl (a e k))
  have hu : JetEq (X^k*a e (3*k)) 0 := by
    simpa using hx.mul (JetEq.refl (a e (3*k)))
  have hf : JetEq (1+2*X^k*a e k) 1 := by
    simpa using (JetEq.refl (1 : ℂ[X])).add ht
  have hg := (a_jet e (2*k) (by omega)).sub hu
  simpa [denPoly] using hf.mul hg

/-- The nonlinear divided tail survives in the finite-part numerator. -/
theorem remPoly_jet (e : ℂ) (k : ℕ) (hk : 3 ≤ k) :
    JetEq (remPoly e k) (jetPoly (3/16) (-1/32) ((-13-8*e)/256)) := by
  let s := jetPoly (-1/4) (1/16) ((1+e)/16)
  have hx := jet_X_pow k hk
  have h₁ : JetEq (2*X^k*a e k*a e (3*k)) 0 := by
    simpa using (((JetEq.refl (2 : ℂ[X])).mul hx).mul
      (JetEq.refl (a e k))).mul (JetEq.refl (a e (3*k)))
  have h₂ : JetEq ((X^k)^2*H e (2*k) k) 0 := by
    simpa using (hx.pow 2).mul (JetEq.refl (H e (2*k) k))
  have h₃ : JetEq (2*(X^k)^2*a e k*a e (3*k)) 0 := by
    simpa using (((JetEq.refl (2 : ℂ[X])).mul (hx.pow 2)).mul
      (JetEq.refl (a e k))).mul (JetEq.refl (a e (3*k)))
  have h₄ : JetEq (2*(X^k)^3*a e (2*k)*a e (3*k)) 0 := by
    simpa using (((JetEq.refl (2 : ℂ[X])).mul (hx.pow 3)).mul
      (JetEq.refl (a e (2*k)))).mul (JetEq.refl (a e (3*k)))
  have hp := ((JetEq.refl (2 : ℂ[X])).mul (a_jet e k hk)).mul
    (a_jet e (2*k) (by omega))
  have he : JetEq (remPoly e k)
      (jetPoly (1/16) (1/32) ((1+8*e)/256) + 2*s*s) := by
    simpa [remPoly, s] using
      (((((H_jet e k hk).add hp).sub h₁).sub h₂).sub h₃).add h₄
  have hs := jetPoly_sq (-1/4 : ℂ) (1/16) ((1+e)/16)
  have hss : JetEq (2*s*s)
      (jetPoly ((-1/4)^2) (2*(-1/4)*(1/16))
        ((1/16)^2+2*(-1/4)*((1+e)/16)) +
       jetPoly ((-1/4)^2) (2*(-1/4)*(1/16))
        ((1/16)^2+2*(-1/4)*((1+e)/16))) := by
    convert hs.add hs using 1 <;> (try rfl)
    dsimp [s]
    ring
  apply (he.trans ((JetEq.refl _).add hss)).trans
  apply JetEq.of_eq
  rw [jetPoly_add, jetPoly_add]
  apply jetPoly_congr <;> ring

/-- Exact cubic cancellation: the retained projective jet records quartic curvature. -/
theorem residue_cubic_dvd (e : ℂ) (k : ℕ) (hk : 3 ≤ k) :
    (X : ℂ[X])^3 ∣ remPoly e k + correctionPoly e * denPoly e k := by
  have hd := (JetEq.refl (correctionPoly e)).mul (denPoly_jet e k hk)
  have hm := jetPoly_mul (3/4 : ℂ) (1/16) (e/16)
    (-1/4) (1/16) ((1+e)/16)
  have hh := (remPoly_jet e k hk).add (hd.trans hm)
  have hzero : JetEq (remPoly e k + correctionPoly e * denPoly e k) 0 := by
    apply hh.trans
    apply JetEq.of_eq
    rw [jetPoly_add]
    have hz : jetPoly (0 : ℂ) 0 0 = 0 := by simp [jetPoly]
    rw [← hz]
    apply jetPoly_congr <;> ring
  simpa only [JetEq, sub_zero] using hzero

/-- A single polynomial remainder, valid for all multipliers for a fixed return shape. -/
theorem exists_residue_factor (e : ℂ) (k : ℕ) (hk : 3 ≤ k) :
    ∃ U : ℂ[X], ∀ q : ℂ,
      (remPoly e k).eval q +
        (3/4 + q/16 + e*q^2/16) * (denPoly e k).eval q = q^3*U.eval q := by
  obtain ⟨U, hU⟩ := residue_cubic_dvd e k hk
  refine ⟨U, fun q => ?_⟩
  have h := congrArg (Polynomial.eval q) hU
  simp only [eval_add, eval_mul, eval_pow, eval_X, correctionPoly, jetPoly, eval_C] at h
  convert h using 1 <;> ring

/-- The complete singular jet, as an exact rational identity with a polynomial remainder. -/
theorem normalizedClock_cubic_remainder (e : ℂ) (k : ℕ) (hk : 3 ≤ k) :
    ∃ U : ℂ[X], ∀ q : ℂ, q ≠ 0 → (denPoly e k).eval q ≠ 0 →
      normalizedClock e q k + (q^k)⁻¹ + 3/4 + q/16 + e*q^2/16 =
        q^3 * U.eval q / (denPoly e k).eval q := by
  obtain ⟨U, hU⟩ := exists_residue_factor e k hk
  refine ⟨U, fun q hq hD => ?_⟩
  rw [normalizedClock_regular_part e q k hq hD]
  apply (eq_div_iff hD).2
  have h := hU q
  field_simp at *
  linear_combination h

end LoopsQuadraticProjective

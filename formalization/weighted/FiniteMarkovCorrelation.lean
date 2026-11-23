import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.BigOperators
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Finite stationary endpoint laws and observable correlations

Every probabilistic premise is explicit. A stochastic matrix and a stationary
probability vector define nonnegative, normalized two-time endpoint laws at
every integer horizon. A complex right eigenmode has zero stationary mean
when its eigenvalue is not one; its endpoint correlation is exactly the
corresponding eigenvalue power times its positive second moment.

The lazy clock is a separate matrix: (I + P) / 2. Its stationary law is the
same, but its eigenvalue is (1 + lambda) / 2. No identification between a
matrix endpoint law and an external physical measure is hidden here. For
the constructed affine clone map that identification is a separate written
cylinder/change-of-variables proof in clone_renewal_clock_20261123.md.
-/

namespace LoopsMarkovCorrelation

noncomputable section

open scoped BigOperators
open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Row-source transition probabilities, including normalization. -/
structure Stochastic (P : Matrix ι ι ℝ) : Prop where
  nonneg : ∀ i j, 0 ≤ P i j
  rowsum : ∀ i, ∑ j, P i j = 1

/-- A probability vector invariant under the same transition matrix. -/
structure Stationary (P : Matrix ι ι ℝ) (π : ι → ℝ) : Prop where
  nonneg : ∀ i, 0 ≤ π i
  total : ∑ i, π i = 1
  invariant : ∀ j, ∑ i, π i * P i j = π j

def complexify (P : Matrix ι ι ℝ) : Matrix ι ι ℂ := fun i j => (P i j : ℂ)

def joint (P : Matrix ι ι ℝ) (π : ι → ℝ) (q : ℕ) (i j : ι) : ℝ :=
  π i * (P ^ q) i j

def mean (π : ι → ℝ) (g : ι → ℂ) : ℂ := ∑ i, (π i : ℂ) * g i

def secondMoment (π : ι → ℝ) (g : ι → ℂ) : ℝ :=
  ∑ i, π i * Complex.normSq (g i)

def correlation (P : Matrix ι ι ℝ) (π : ι → ℝ) (g : ι → ℂ) (q : ℕ) : ℂ :=
  ∑ i, ∑ j, (joint P π q i j : ℂ) * (starRingEnd ℂ) (g i) * g j

omit [DecidableEq ι] in
theorem complexify_mul (P Q : Matrix ι ι ℝ) :
    complexify (P * Q) = complexify P * complexify Q := by
  ext i j
  simp [complexify, Matrix.mul_apply, Complex.ofReal_sum]

theorem complexify_pow (P : Matrix ι ι ℝ) (q : ℕ) :
    complexify (P ^ q) = complexify P ^ q := by
  induction q with
  | zero =>
      ext i j
      by_cases h : i = j <;> simp [complexify, h]
  | succ q ih => rw [pow_succ, complexify_mul, ih, pow_succ]

theorem mode_power (Q : Matrix ι ι ℂ) (g : ι → ℂ) (μ : ℂ)
    (hmode : Q *ᵥ g = μ • g) (q : ℕ) :
    (Q ^ q) *ᵥ g = (μ ^ q) • g := by
  induction q with
  | zero => simp
  | succ q ih =>
      rw [pow_succ, ← Matrix.mulVec_mulVec, hmode, Matrix.mulVec_smul, ih,
        smul_smul]
      simp [pow_succ, mul_comm]

theorem stochastic_pow (P : Matrix ι ι ℝ) (hP : Stochastic P) (q : ℕ) :
    Stochastic (P ^ q) := by
  induction q with
  | zero =>
      constructor
      · intro i j
        by_cases h : i = j <;> simp [h]
      · intro i
        change (∑ j, if i = j then (1 : ℝ) else 0) = 1
        simp
  | succ q ih =>
      rw [pow_succ]
      constructor
      · intro i j
        exact Finset.sum_nonneg (fun k _ => mul_nonneg (ih.nonneg i k) (hP.nonneg k j))
      · intro i
        simp only [Matrix.mul_apply]
        rw [Finset.sum_comm]
        simp_rw [← Finset.mul_sum, hP.rowsum, mul_one]
        exact ih.rowsum i

theorem stationary_pow (P : Matrix ι ι ℝ) (π : ι → ℝ)
    (hπ : Stationary P π) (q : ℕ) : Stationary (P ^ q) π := by
  refine ⟨hπ.nonneg, hπ.total, ?_⟩
  have hv : π ᵥ* P = π := funext hπ.invariant
  have hp : π ᵥ* (P ^ q) = π := by
    induction q with
    | zero => simp
    | succ q ih => rw [pow_succ, ← Matrix.vecMul_vecMul, ih, hv]
  exact fun j => congrFun hp j

/-- These are genuine two-time probability laws, with both marginals equal
to the explicitly supplied stationary probability vector. -/
theorem joint_probability (P : Matrix ι ι ℝ) (π : ι → ℝ)
    (hP : Stochastic P) (hπ : Stationary P π) (q : ℕ) :
    (∀ i j, 0 ≤ joint P π q i j) ∧
      (∑ i, ∑ j, joint P π q i j) = 1 ∧
      (∀ i, ∑ j, joint P π q i j = π i) ∧
      (∀ j, ∑ i, joint P π q i j = π j) := by
  have hpow := stochastic_pow P hP q
  have hleft (i : ι) : ∑ j, joint P π q i j = π i := by
    simp only [joint, ← Finset.mul_sum, hpow.rowsum, mul_one]
  refine ⟨?_, ?_, hleft, ?_⟩
  · intro i j
    exact mul_nonneg (hπ.nonneg i) (hpow.nonneg i j)
  · simpa only [hleft] using hπ.total
  · exact (stationary_pow P π hπ q).invariant

omit [DecidableEq ι] in
private theorem complex_stationary (P : Matrix ι ι ℝ) (π : ι → ℝ)
    (hπ : Stationary P π) (j : ι) :
    (∑ i, (π i : ℂ) * complexify P i j) = (π j : ℂ) := by
  have h := congrArg Complex.ofReal (hπ.invariant j)
  simpa [complexify, Complex.ofReal_sum] using h

omit [DecidableEq ι] in
/-- Stationarity forces every non-unit right mode to have zero mean. -/
theorem mode_centered (P : Matrix ι ι ℝ) (π : ι → ℝ)
    (hπ : Stationary P π) (g : ι → ℂ) (μ : ℂ)
    (hmode : complexify P *ᵥ g = μ • g) (hμ : μ ≠ 1) :
    mean π g = 0 := by
  have hm : μ * mean π g = mean π g := by
    calc
      μ * mean π g = ∑ i, (π i : ℂ) * (μ * g i) := by
        simp only [mean, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = ∑ i, (π i : ℂ) * ((complexify P *ᵥ g) i) := by
        rw [hmode]
        rfl
      _ = mean π g := by
        simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, mean]
        rw [Finset.sum_comm]
        simp_rw [← mul_assoc, ← Finset.sum_mul, complex_stationary P π hπ]
  have hz : (μ - 1) * mean π g = 0 := by rw [sub_mul, one_mul, hm, sub_self]
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hμ)

/-- Algebraic correlation identity; `joint_probability` supplies its
probabilistic meaning when the stochastic and stationary premises hold. -/
theorem mode_correlation (P : Matrix ι ι ℝ) (π : ι → ℝ)
    (g : ι → ℂ) (μ : ℂ) (hmode : complexify P *ᵥ g = μ • g) (q : ℕ) :
    correlation P π g q = μ ^ q * (secondMoment π g : ℂ) := by
  have hp : complexify (P ^ q) *ᵥ g = (μ ^ q) • g := by
    rw [complexify_pow]
    exact mode_power _ _ _ hmode q
  calc
    correlation P π g q =
        ∑ i, (π i : ℂ) * (starRingEnd ℂ) (g i) * ((complexify (P ^ q) *ᵥ g) i) := by
      unfold correlation joint
      apply Finset.sum_congr rfl
      intro i _
      simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, complexify,
        Complex.ofReal_mul]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = μ ^ q * (secondMoment π g : ℂ) := by
      rw [hp]
      simp only [Pi.smul_apply, smul_eq_mul, secondMoment, Complex.ofReal_sum,
        Complex.ofReal_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [Complex.normSq_eq_conj_mul_self]
      ring

omit [DecidableEq ι] in
theorem secondMoment_pos (π : ι → ℝ) (g : ι → ℂ)
    (hπ : ∀ i, 0 < π i) (hg : ∃ i, g i ≠ 0) : 0 < secondMoment π g := by
  obtain ⟨i, hi⟩ := hg
  have hterm : 0 < π i * Complex.normSq (g i) :=
    mul_pos (hπ i) (Complex.normSq_pos.mpr hi)
  exact lt_of_lt_of_le hterm (Finset.single_le_sum
    (fun j _ => mul_nonneg (hπ j).le (Complex.normSq_nonneg (g j)))
    (Finset.mem_univ i))

/-- Normalization consumes the independently proved nonzero second moment. -/
theorem normalized_mode_correlation (P : Matrix ι ι ℝ) (π : ι → ℝ)
    (hπpos : ∀ i, 0 < π i) (g : ι → ℂ) (hg : ∃ i, g i ≠ 0) (μ : ℂ)
    (hmode : complexify P *ᵥ g = μ • g) (q : ℕ) :
    correlation P π g q / (secondMoment π g : ℂ) = μ ^ q := by
  have hden : (secondMoment π g : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (secondMoment_pos π g hπpos hg))
  apply (div_eq_iff hden).mpr
  exact mode_correlation P π g μ hmode q

/-- Independent fair Bernoulli holding produces a distinct transition
matrix, while retaining the same states and stationary measure. -/
def lazyTransition (P : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  (1 / 2 : ℝ) • (1 + P)

theorem lazy_stochastic (P : Matrix ι ι ℝ) (hP : Stochastic P) :
    Stochastic (lazyTransition P) := by
  constructor
  · intro i j
    change 0 ≤ (1 / 2 : ℝ) * ((1 : Matrix ι ι ℝ) i j + P i j)
    apply mul_nonneg (by norm_num)
    apply add_nonneg _ (hP.nonneg i j)
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  · intro i
    simp only [lazyTransition, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul,
      ← Finset.mul_sum, Finset.sum_add_distrib, hP.rowsum]
    have he : (∑ j, (1 : Matrix ι ι ℝ) i j) = 1 := by
      change (∑ j, if i = j then (1 : ℝ) else 0) = 1
      simp
    rw [he]
    norm_num

theorem lazy_stationary (P : Matrix ι ι ℝ) (π : ι → ℝ)
    (hπ : Stationary P π) : Stationary (lazyTransition P) π := by
  refine ⟨hπ.nonneg, hπ.total, ?_⟩
  intro j
  change (∑ i, π i * ((1 / 2 : ℝ) * ((1 : Matrix ι ι ℝ) i j + P i j))) = π j
  calc
    _ = (1 / 2 : ℝ) *
        ((∑ i, π i * (1 : Matrix ι ι ℝ) i j) + ∑ i, π i * P i j) := by
      simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
      congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;> ring
    _ = π j := by
      rw [hπ.invariant]
      have he : (∑ i, π i * (1 : Matrix ι ι ℝ) i j) = π j := by
        change (∑ i, π i * (if i = j then (1 : ℝ) else 0)) = π j
        simp
      rw [he]
      ring

omit [Fintype ι] in
private theorem complexify_lazy (P : Matrix ι ι ℝ) :
    complexify (lazyTransition P) = (1 / 2 : ℂ) • (1 + complexify P) := by
  ext i j
  by_cases h : i = j <;>
    simp [complexify, lazyTransition, h]

/-- The eigenvalue changes under the fair holding clock. It is not
determined by the original eigenvalue modulus or the mean clock alone. -/
theorem lazy_mode (P : Matrix ι ι ℝ) (g : ι → ℂ) (μ : ℂ)
    (hmode : complexify P *ᵥ g = μ • g) :
    complexify (lazyTransition P) *ᵥ g = ((1 + μ) / 2) • g := by
  rw [complexify_lazy, Matrix.smul_mulVec, Matrix.add_mulVec, Matrix.one_mulVec,
    hmode]
  ext i
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  ring

theorem lazy_mode_correlation (P : Matrix ι ι ℝ) (π : ι → ℝ)
    (g : ι → ℂ) (μ : ℂ) (hmode : complexify P *ᵥ g = μ • g) (q : ℕ) :
    correlation (lazyTransition P) π g q =
      ((1 + μ) / 2) ^ q * (secondMoment π g : ℂ) := by
  exact mode_correlation _ π g _ (lazy_mode P g μ hmode) q

/-- The centered, nondegenerate finite observable certificate. Probability
normalization of each endpoint law is proved separately by `joint_probability`.
Strict positivity of the stationary masses is consumed, not silently inferred. -/
theorem stationary_mode_correlation (P : Matrix ι ι ℝ) (π : ι → ℝ)
    (hπ : Stationary P π) (hπpos : ∀ i, 0 < π i)
    (g : ι → ℂ) (hg : ∃ i, g i ≠ 0) (μ : ℂ)
    (hmode : complexify P *ᵥ g = μ • g) (hμ : μ ≠ 1) :
    mean π g = 0 ∧ 0 < secondMoment π g ∧
      (∀ q, correlation P π g q = μ ^ q * (secondMoment π g : ℂ)) ∧
      (∀ q, correlation (lazyTransition P) π g q =
        ((1 + μ) / 2) ^ q * (secondMoment π g : ℂ)) := by
  exact ⟨mode_centered P π hπ g μ hmode hμ, secondMoment_pos π g hπpos hg,
    mode_correlation P π g μ hmode, lazy_mode_correlation P π g μ hmode⟩

#print axioms joint_probability
#print axioms mode_centered
#print axioms mode_correlation
#print axioms secondMoment_pos
#print axioms normalized_mode_correlation
#print axioms lazy_stochastic
#print axioms lazy_stationary
#print axioms lazy_mode
#print axioms stationary_mode_correlation

end

end LoopsMarkovCorrelation

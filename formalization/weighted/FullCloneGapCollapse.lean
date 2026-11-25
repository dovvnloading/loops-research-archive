import FullCloneCharpoly
import CloneRootRate

/-!
# No uniform absolute or relative spectral gap in the actual clone family

The exact characteristic-root product, after removing the simple leading
root, forces a different eigenvalue of modulus at least 1/t. Combining
this with the existing strict gap and root-excess bound gives, for every
delay n, a nonleading actual eigenvalue μ with

  0 < t - ‖μ‖ < 1/(n+2).

The existence statement directly rules out a uniform gap, and implies
the same bound for t minus the largest nonleading eigenvalue modulus.
No numerical roots, assumed determinant identity, fractional power, or
external Perron theorem enters the proof.

AI assistance: OpenAI GPT-6 Astra Pro, proof construction and API audit.
-/

namespace LoopsSpectral

open LoopsFormal.CloneGraph
open Polynomial

noncomputable section

private theorem product_norm_le_one (s : Multiset ℂ)
    (h : ∀ z ∈ s, ‖z‖ ≤ 1) :
    (s.map (fun z : ℂ => ‖z‖)).prod ≤ 1 := by
  revert h
  induction s using Multiset.induction_on with
  | empty => intro h; simp
  | @cons z s ih =>
      intro h
      have hz : ‖z‖ ≤ 1 := h z (by simp)
      have hs : (s.map (fun w : ℂ => ‖w‖)).prod ≤ 1 := by
        apply ih
        intro w hw
        exact h w (by simp [hw])
      simp only [Multiset.map_cons, Multiset.prod_cons]
      calc
        ‖z‖ * (s.map (fun w : ℂ => ‖w‖)).prod ≤ ‖z‖ * 1 :=
          mul_le_mul_of_nonneg_left hs (norm_nonneg z)
        _ ≤ 1 := by simpa using hz

/-- The simple leading root cannot absorb the whole Vieta product.
At least one different scalar root has modulus at least its reciprocal. -/
theorem clone_exists_nonleading_root_modulus_ge_inv (n : ℕ) (t : ℝ)
    (ht : 1 < t) (hroot : t ^ (2 * n + 5) = t + 1) :
    ∃ μ : ℂ, μ ^ (2 * n + 5) = μ + 1 ∧ μ ≠ (t : ℂ) ∧
      1 / t ≤ ‖μ‖ := by
  classical
  have ht0 : 0 < t := by linarith
  have htc : (t : ℂ) ^ (2 * n + 5) = (t : ℂ) + 1 := by
    exact_mod_cast hroot
  have hp : cloneCharPolynomial n ≠ 0 := (cloneCharPolynomial_monic n).ne_zero
  have htmem : (t : ℂ) ∈ (cloneCharPolynomial n).roots := by
    apply (Polynomial.mem_roots hp).mpr
    simp [Polynomial.IsRoot, cloneCharPolynomial, htc]
  let rest : Multiset ℂ := (cloneCharPolynomial n).roots.erase (t : ℂ)
  have hcons : (t : ℂ) ::ₘ rest = (cloneCharPolynomial n).roots :=
    Multiset.cons_erase htmem
  have ht_not_mem : (t : ℂ) ∉ rest := by
    have h := cloneCharPolynomial_roots_nodup n
    rw [← hcons] at h
    exact (Multiset.nodup_cons.mp h).1
  have hrest_ne : rest ≠ 0 := by
    intro hzero
    have hcard := congrArg Multiset.card hcons
    rw [hzero] at hcard
    simp only [Multiset.card_cons, Multiset.card_zero] at hcard
    rw [cloneCharPolynomial_card_roots] at hcard
    omega
  have hprod : t * (rest.map (fun z : ℂ => ‖z‖)).prod = 1 := by
    have h := cloneCharPolynomial_norm_product n
    rw [← hcons] at h
    simpa only [Multiset.map_cons, Multiset.prod_cons, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos ht0] using h
  have hinv : 1 / t < 1 := (div_lt_one ht0).mpr ht
  have hexists : ∃ μ ∈ rest, 1 / t ≤ ‖μ‖ := by
    by_contra hnone
    push_neg at hnone
    obtain ⟨μ, hμ⟩ := Multiset.exists_mem_of_ne_zero hrest_ne
    obtain ⟨s, hs⟩ := Multiset.exists_cons_of_mem hμ
    have hsprod : (s.map (fun z : ℂ => ‖z‖)).prod ≤ 1 := by
      apply product_norm_le_one
      intro z hz
      have hzrest : z ∈ rest := by
        rw [hs]
        simp [hz]
      exact le_trans (le_of_lt (hnone z hzrest)) (le_of_lt hinv)
    have hsmall : (rest.map (fun z : ℂ => ‖z‖)).prod < 1 / t := by
      rw [hs, Multiset.map_cons, Multiset.prod_cons]
      calc
        ‖μ‖ * (s.map (fun z : ℂ => ‖z‖)).prod ≤ ‖μ‖ * 1 :=
          mul_le_mul_of_nonneg_left hsprod (norm_nonneg μ)
        _ < 1 / t := by simpa using hnone μ hμ
    have h := mul_lt_mul_of_pos_left hsmall ht0
    have hinverse : t * (1 / t) = 1 := by field_simp [ne_of_gt ht0]
    rw [hprod, hinverse] at h
    exact lt_irrefl _ h
  obtain ⟨μ, hμ, hbound⟩ := hexists
  refine ⟨μ, ?_, ?_, hbound⟩
  · have hμroot := (Polynomial.mem_roots hp).mp (Multiset.mem_of_mem_erase hμ)
    have h : μ ^ (2 * n + 5) - (μ + 1) = 0 := by
      simpa [Polynomial.IsRoot, cloneCharPolynomial] using hμroot
    exact sub_eq_zero.mp h
  · intro heq
    subst μ
    exact ht_not_mem hμ

/-- For every delay there is an actual nonleading eigenvalue whose
absolute separation is strictly below the archived 1/(n+2) bound. -/
theorem full_clone_nonleading_eigenvalue_close (n : ℕ) (t : ℝ)
    (ht : 1 < t) (hroot : t ^ (2 * n + 5) = t + 1) :
    ∃ μ : ℂ, Module.End.HasEigenvalue (complexFullAdjacencyMatrix n).mulVecLin μ ∧
      μ ≠ (t : ℂ) ∧ 0 < t - ‖μ‖ ∧ t - ‖μ‖ < 1 / ((n : ℝ) + 2) := by
  obtain ⟨μ, hμroot, hμne, hμbound⟩ :=
    clone_exists_nonleading_root_modulus_ge_inv n t ht hroot
  obtain ⟨z, hz, hAz⟩ := clone_polynomial_root_is_eigenvalue n μ hμroot
  have hstrict : ‖μ‖ < t := full_clone_strict_complex_spectral_gap
    n t ht hroot μ z hz hAz hμne
  have ht0 : 0 < t := by linarith
  have hinverse : t * (1 / t) = 1 := by field_simp [ne_of_gt ht0]
  have hsq : 0 < (t - 1) ^ 2 := sq_pos_of_pos (by linarith)
  have hinvgap : t - 1 / t < 2 * (t - 1) := by
    apply (mul_lt_mul_left ht0).mp
    nlinarith
  have hexcess := clone_root_excess_bound n t ht hroot
  have hcoeff : ((2 * n + 4 : ℕ) : ℝ) = 2 * ((n : ℝ) + 2) := by
    push_cast
    ring
  rw [hcoeff] at hexcess
  have hden : 0 < (n : ℝ) + 2 := by positivity
  have hexcess_div : 2 * (t - 1) ≤ 1 / ((n : ℝ) + 2) := by
    apply (le_div_iff₀ hden).mpr
    nlinarith
  refine ⟨μ, clone_root_has_actual_eigenvalue n μ hμroot, hμne,
    sub_pos.mpr hstrict, ?_⟩
  calc
    t - ‖μ‖ ≤ t - 1 / t := by linarith
    _ < 2 * (t - 1) := hinvgap
    _ ≤ 1 / ((n : ℝ) + 2) := hexcess_div

/-- There is no positive uniform absolute spectral gap in the actual
cloned graph family. This is a full tolerance-quantified theorem. -/
theorem full_clone_absolute_gap_can_approach_zero (ε : ℝ) (hε : 0 < ε) :
    ∃ n : ℕ, ∃ t : ℝ, ∃ μ : ℂ,
      1 < t ∧ t ^ (2 * n + 5) = t + 1 ∧
      Module.End.HasEigenvalue (complexFullAdjacencyMatrix n).mulVecLin μ ∧
      μ ≠ (t : ℂ) ∧ 0 < t - ‖μ‖ ∧ t - ‖μ‖ < ε := by
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / ε)
  obtain ⟨t, ht, _, hroot⟩ := finite_clone_root_exists n
  obtain ⟨μ, heigen, hne, hpos, hgap⟩ :=
    full_clone_nonleading_eigenvalue_close n t ht hroot
  have hnε : 1 < (n : ℝ) * ε := (div_lt_iff₀ hε).mp hn
  have hden : 0 < (n : ℝ) + 2 := by positivity
  have hsmall : 1 / ((n : ℝ) + 2) < ε := by
    apply (div_lt_iff₀ hden).mpr
    nlinarith
  exact ⟨n, t, μ, ht, hroot, heigen, hne, hpos, lt_trans hgap hsmall⟩

/-- The actual family has no positive uniform relative spectral gap. -/
theorem full_clone_relative_gap_can_approach_zero (ε : ℝ) (hε : 0 < ε) :
    ∃ n : ℕ, ∃ t : ℝ, ∃ μ : ℂ,
      1 < t ∧ t ^ (2 * n + 5) = t + 1 ∧
      Module.End.HasEigenvalue (complexFullAdjacencyMatrix n).mulVecLin μ ∧
      μ ≠ (t : ℂ) ∧ 0 < 1 - ‖μ‖ / t ∧ 1 - ‖μ‖ / t < ε := by
  obtain ⟨n, t, μ, ht, hroot, heigen, hne, hpos, hgap⟩ :=
    full_clone_absolute_gap_can_approach_zero ε hε
  have ht0 : 0 < t := by linarith
  have hformula : 1 - ‖μ‖ / t = (t - ‖μ‖) / t := by
    field_simp [ne_of_gt ht0]
  refine ⟨n, t, μ, ht, hroot, heigen, hne, ?_, ?_⟩
  · rw [hformula]
    exact div_pos hpos ht0
  · rw [hformula]
    apply (div_lt_iff₀ ht0).mpr
    have hgain : 0 < ε * (t - 1) := mul_pos hε (by linarith)
    nlinarith

#print axioms clone_exists_nonleading_root_modulus_ge_inv
#print axioms full_clone_nonleading_eigenvalue_close
#print axioms full_clone_absolute_gap_can_approach_zero
#print axioms full_clone_relative_gap_can_approach_zero

end

end LoopsSpectral

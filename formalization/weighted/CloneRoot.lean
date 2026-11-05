import CloneBounds

/-!
# Existence and uniqueness of each finite delayed-clone scalar root

For every natural n, the polynomial t^(2*n+5)=t+1 has exactly one
real root in (1,2). This makes the weighted-return eigenproblem and
the literal positive-weight inconsistency theorem non-vacuous.

The proof uses the intermediate value theorem plus monotonicity of
positive powers. No numerical root finder is invoked.
-/

namespace LoopsSpectral

noncomputable section

def clonePolynomial (n : ℕ) (t : ℝ) : ℝ :=
  t ^ (2 * n + 5) - t - 1

theorem finite_clone_root_exists (n : ℕ) :
    ∃ t : ℝ, 1 < t ∧ t < 2 ∧ t ^ (2 * n + 5) = t + 1 := by
  let g : ℝ → ℝ := clonePolynomial n
  have hcont : ContinuousOn g (Set.Icc (1 : ℝ) 2) := by
    dsimp [g, clonePolynomial]
    fun_prop
  have h1 : g 1 < 0 := by
    dsimp [g, clonePolynomial]
    norm_num
  have hh : (1 : ℝ) ≤ (2 : ℝ) ^ (2 * n) :=
    one_le_pow₀ (by norm_num)
  have hpow : (2 : ℝ) ^ (2 * n + 5) =
      (2 : ℝ) ^ (2 * n) * 32 := by
    rw [show 2 * n + 5 = (2 * n) + 5 by omega, pow_add]
    norm_num
  have h2 : 0 < g 2 := by
    dsimp [g, clonePolynomial]
    rw [hpow]
    nlinarith
  have hsegment : (0 : ℝ) ∈ Set.Icc (g 1) (g 2) :=
    ⟨h1.le, h2.le⟩
  have himage : (0 : ℝ) ∈ g '' Set.Icc (1 : ℝ) 2 :=
    (intermediate_value_Icc (by norm_num : (1 : ℝ) ≤ 2) hcont)
      hsegment
  obtain ⟨t, ht, heq⟩ := himage
  refine ⟨t, ?_, ?_, ?_⟩
  · by_contra hn
    have hval : t = (1 : ℝ) :=
      le_antisymm (le_of_not_gt hn) ht.1
    rw [hval] at heq
    exact (ne_of_lt h1) heq
  · by_contra hn
    have hval : t = (2 : ℝ) :=
      le_antisymm ht.2 (le_of_not_gt hn)
    rw [hval] at heq
    exact (ne_of_gt h2) heq
  · change clonePolynomial n t = 0 at heq
    dsimp [clonePolynomial] at heq
    linarith

/-- If two positive roots were ordered, increasing positive powers
and the two root equations would force the same positive quantity
to be both smaller and larger. -/
private theorem cannot_order_clone_roots (n : ℕ)
    {x y : ℝ} (hx : 1 < x) (hy : 1 < y) (hxy : x < y)
    (hpx : x ^ (2 * n + 5) = x + 1)
    (hpy : y ^ (2 * n + 5) = y + 1) : False := by
  let k : ℕ := 2 * n + 4
  have hk : k ≠ 0 := by dsimp [k]; omega
  have hpowlt : x ^ k < y ^ k :=
    pow_lt_pow_left₀ hxy (by linarith) hk
  have hxp : 1 < x ^ k := one_lt_pow₀ hx hk
  have hxs : (x ^ k - 1) * x = 1 := by
    have hstep : x ^ k * x = x + 1 := by
      calc
        x ^ k * x = x ^ (k + 1) := (pow_succ x k).symm
        _ = x ^ (2 * n + 5) := by congr 1; dsimp [k]; omega
        _ = x + 1 := hpx
    nlinarith
  have hys : (y ^ k - 1) * y = 1 := by
    have hstep : y ^ k * y = y + 1 := by
      calc
        y ^ k * y = y ^ (k + 1) := (pow_succ y k).symm
        _ = y ^ (2 * n + 5) := by congr 1; dsimp [k]; omega
        _ = y + 1 := hpy
    nlinarith
  have ha : 0 < (x ^ k - 1) * (y - x) :=
    mul_pos (by linarith) (by linarith)
  have hb : 0 < (y ^ k - x ^ k) * y :=
    mul_pos (by linarith) (by linarith)
  nlinarith

/-- Every delayed clone has a unique real root greater than one. -/
theorem finite_clone_root_unique (n : ℕ)
    {x y : ℝ} (hx : 1 < x) (hy : 1 < y)
    (hpx : x ^ (2 * n + 5) = x + 1)
    (hpy : y ^ (2 * n + 5) = y + 1) : x = y := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hxy | hyx
  · exact cannot_order_clone_roots n hx hy hxy hpx hpy
  · exact cannot_order_clone_roots n hy hx hyx hpy hpx

/-- A unique positive clone root exists, constructively within (1,2)
in the sense of Prop-valued existence/uniqueness. -/
theorem finite_clone_root_existsUnique (n : ℕ) :
    ∃! t : ℝ, 1 < t ∧ t ^ (2 * n + 5) = t + 1 := by
  obtain ⟨t, ht, _, hpoly⟩ := finite_clone_root_exists n
  refine ⟨t, ⟨ht, hpoly⟩, ?_⟩
  intro s hs
  exact finite_clone_root_unique n hs.1 ht hs.2 hpoly

end

end LoopsSpectral

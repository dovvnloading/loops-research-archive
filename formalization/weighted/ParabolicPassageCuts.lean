import ParabolicTipRate
import Mathlib.Tactic

/-!
# Actual entry and exit of the shrinking parabolic bottleneck

The indices below are constructed from the true polynomial orbit.  The
entry estimate prevents a discrete step from jumping across the bottleneck.
-/

namespace LoopsParabolic

open Set Function

theorem passage_orbit_monotone {t : ℝ} {k : ℕ}
    (ht : t ∈ Icc 0 (1 / 100 : ℝ))
    (stay : ∀ j ≤ k, (H t)^[j] 0 ∈ Icc 0 cap) :
    ∀ j ≤ k, ∀ i ≤ j, (H t)^[i] 0 ≤ (H t)^[j] 0 := by
  intro j
  induction j with
  | zero =>
    intro _ i hi
    have hi0 : i = 0 := by omega
    subst i
    exact le_rfl
  | succ j ih =>
    intro hj i hi
    by_cases hij : i ≤ j
    · have hd := channel_drift ht (stay j (by omega))
      rw [Function.iterate_succ_apply']
      linarith [ih (by omega) i hij, ht.1]
    · have he : i = j + 1 := by omega
      subst i
      exact le_rfl

/-- The true flight has a central interval of indices.  Its first point
is still on the negative side and its last point is already on the positive
side; every central step has both endpoints in a twice enlarged window. -/
theorem passage_cut_indices {t a δ : ℝ} {k : ℕ}
    (ht : 0 < t) (htmax : t ≤ 1 / 100)
    (ha : a ∈ Icc (1 / 20 : ℝ) (3 / 50)) (root : cubic a = 0)
    (hδ : 0 < δ) (hδmax : δ ≤ 1 / 1000) (htδ : t ≤ δ ^ 2)
    (stay : ∀ j ≤ k, (H t)^[j] 0 ∈ Icc 0 cap)
    (reached : 7 / 20 ≤ (H t)^[k] 0) :
    ∃ l m : ℕ, l < m ∧ m ≤ k ∧
      (H t)^[l] 0 - a ∈ Icc (-δ) (-δ / 2) ∧
      (H t)^[m] 0 - a ∈ Icc δ (2 * δ) ∧
      (∀ j, l ≤ j → j < m →
        |(H t)^[j] 0 - a| ≤ δ ∧ |(H t)^[j + 1] 0 - a| ≤ 2 * δ) ∧
      (∀ j < l, δ ≤ |(H t)^[j] 0 - a|) ∧
      (∀ j, m ≤ j → j < k → δ ≤ |(H t)^[j] 0 - a|) := by
  let w : ℕ → ℝ := fun j => (H t)^[j] 0
  have htw : t ∈ Icc 0 (1 / 100 : ℝ) := ⟨ht.le, htmax⟩
  have hmono := passage_orbit_monotone htw stay
  have hsuc (j : ℕ) : w (j + 1) = H t (w j) :=
    Function.iterate_succ_apply' (H t) j 0
  have hδsq : δ ^ 2 ≤ δ / 1000 := by
    nlinarith [mul_le_mul_of_nonneg_left hδmax hδ.le]
  have hleft : a - δ ∈ Icc 0 cap := by
    constructor
    · linarith [ha.1]
    · change a - δ ≤ 2 / 5
      linarith [ha.2]
  have hright : a + δ ∈ Icc 0 cap := by
    constructor
    · linarith [ha.1]
    · change a + δ ≤ 2 / 5
      linarith [ha.2]
  have hleftStep : H t (a - δ) ≤ a - δ / 2 := by
    have hh := (channel_quadratic_step htw hleft ha root).2
    have he : (a - δ - a) ^ 2 = δ ^ 2 := by ring
    rw [he] at hh
    linarith
  have hrightStep : H t (a + δ) ≤ a + 2 * δ := by
    have hh := (channel_quadratic_step htw hright ha root).2
    have he : (a + δ - a) ^ 2 = δ ^ 2 := by ring
    rw [he] at hh
    linarith
  have exl : ∃ j : ℕ, j ≤ k ∧ a - δ ≤ w j :=
    ⟨k, le_rfl, by dsimp [w]; linarith [ha.2]⟩
  have exm : ∃ j : ℕ, j ≤ k ∧ a + δ ≤ w j :=
    ⟨k, le_rfl, by dsimp [w]; linarith [ha.2]⟩
  let l := Nat.find exl
  let m := Nat.find exm
  have hl : l ≤ k ∧ a - δ ≤ w l := Nat.find_spec exl
  have hm : m ≤ k ∧ a + δ ≤ w m := Nat.find_spec exm
  have hbeforeL (j : ℕ) (hj : j < l) : w j < a - δ := by
    apply lt_of_not_ge
    intro hh
    have hh' : l ≤ j := Nat.find_min' exl ⟨by omega, hh⟩
    omega
  have hbeforeM (j : ℕ) (hj : j < m) : w j < a + δ := by
    apply lt_of_not_ge
    intro hh
    have hh' : m ≤ j := Nat.find_min' exm ⟨by omega, hh⟩
    omega
  have hlpos : 0 < l := by
    by_contra! hh
    have he : l = 0 := by omega
    have hz := hl.2
    rw [he] at hz
    change a - δ ≤ 0 at hz
    linarith [ha.1]
  have hmpos : 0 < m := by
    by_contra! hh
    have he : m = 0 := by omega
    have hz := hm.2
    rw [he] at hz
    change a + δ ≤ 0 at hz
    linarith [ha.1]
  have hentry : w l ≤ a - δ / 2 := by
    have hj : l - 1 < l := by omega
    have hb := hbeforeL (l - 1) hj
    have hh := channel_mono htw (stay (l - 1) (by omega)) hleft hb.le
    have he : l - 1 + 1 = l := by omega
    rw [← hsuc, he] at hh
    exact hh.trans hleftStep
  have hexit : w m ≤ a + 2 * δ := by
    have hj : m - 1 < m := by omega
    have hb := hbeforeM (m - 1) hj
    have hh := channel_mono htw (stay (m - 1) (by omega)) hright hb.le
    have he : m - 1 + 1 = m := by omega
    rw [← hsuc, he] at hh
    exact hh.trans hrightStep
  have hlm : l < m := by
    by_contra! hh
    have hh' := hmono l hl.1 m hh
    change w m ≤ w l at hh'
    linarith [hm.2]
  refine ⟨l, m, hlm, hm.1, ⟨by linarith [hl.2], by linarith⟩,
    ⟨by linarith [hm.2], by linarith⟩, ?_, ?_, ?_⟩
  · intro j hlj hjm
    have hjk : j ≤ k := by omega
    have hlo := hmono j hjk l hlj
    change w l ≤ w j at hlo
    have hhi := hbeforeM j hjm
    have hnextlo := hmono (j + 1) (by omega) l (by omega)
    change w l ≤ w (j + 1) at hnextlo
    have hnextHi : w (j + 1) ≤ a + 2 * δ := by
      rw [hsuc]
      exact (channel_mono htw (stay j hjk) hright hhi.le).trans hrightStep
    exact ⟨abs_le.mpr ⟨by change -δ ≤ w j - a; linarith [hl.2],
      by change w j - a ≤ δ; linarith⟩,
      abs_le.mpr ⟨by change -(2 * δ) ≤ w (j + 1) - a; linarith [hl.2],
        by change w (j + 1) - a ≤ 2 * δ; linarith⟩⟩
  · intro j hj
    have hh := hbeforeL j hj
    have hneg : w j - a ≤ 0 := by linarith
    change δ ≤ |w j - a|
    rw [abs_of_nonpos hneg]
    linarith
  · intro j hmj hjk
    have hh := hmono j hjk.le m hmj
    change w m ≤ w j at hh
    change δ ≤ |w j - a|
    exact le_trans (by linarith [hm.2]) (le_abs_self _)

end LoopsParabolic

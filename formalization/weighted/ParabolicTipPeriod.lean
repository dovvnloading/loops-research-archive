import ParabolicChannel
import Mathlib.Dynamics.PeriodicPts.Defs

/-! Recover the exact period for the original quadratic map from a shot in the
reflected third-iterate coordinate. The two intermediate iterates in each
block are separated from the positive target by explicit interval bounds. -/

namespace LoopsParabolic
open Set Function
noncomputable section

theorem reflected_blocks (t e : ℝ) (j : ℕ) :
    (quad (-7/4+t))^[3*j] (-e) = - ((H t)^[j] e) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [show 3 * (j + 1) = 3 + 3*j by omega, Function.iterate_add_apply, ih,
      Function.iterate_succ_apply' (H t) j, reflected, neg_neg]

theorem positive_iterates_even (c e : ℝ) {n : ℕ} (hn : 0 < n) :
    (quad c)^[n] e = (quad c)^[n] (-e) := by
  cases n with
  | zero => omega
  | succ n => simp only [Function.iterate_succ_apply, quad, neg_sq]

theorem small_block_separation {t z : ℝ} (ht : t ∈ Icc 0 (1/100 : ℝ))
    (hz : z ∈ Icc 0 cap) :
    quad (-7/4+t) (-z) < -(1/10 : ℝ) ∧ (1/10 : ℝ) < (quad (-7/4+t))^[2] (-z) := by
  let w := quad (-7/4+t) (-z)
  have hzsq := sq_le_sq' (show -cap ≤ z by unfold cap; linarith [hz.1]) hz.2
  have hw : w ≤ -(3/2 : ℝ) := by
    dsimp [w, quad]; unfold cap at hzsq; nlinarith [ht.2]
  constructor
  · change w < _; linarith
  · change (w^2 + (-7/4+t)) > _
    have hsq := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 3/2)
      (show (3/2:ℝ) ≤ -w by linarith) 2
    nlinarith [ht.1]

theorem exit_block_separation {t z : ℝ} (ht : t ∈ Icc 0 (1/100 : ℝ))
    (hz : z ∈ Icc (9/10 : ℝ) (6/5)) :
    quad (-7/4+t) (-z) < -(1/10 : ℝ) ∧ (quad (-7/4+t))^[2] (-z) < -(1/10 : ℝ) := by
  let w := quad (-7/4+t) (-z)
  have hlo := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 9/10) hz.1 2
  have hhi := sq_le_sq' (show -(6/5 : ℝ) ≤ z by linarith [hz.1]) hz.2
  have hw₁ : -1 ≤ w := by dsimp [w, quad]; nlinarith [ht.1]
  have hw₂ : w < -(1/10 : ℝ) := by dsimp [w, quad]; nlinarith [ht.2]
  refine ⟨hw₂, ?_⟩
  change (w^2 + (-7/4+t)) < _
  have hsq := sq_le_sq' hw₁ (show w ≤ 1 by linarith)
  nlinarith [ht.2]

/-- The entrance corridor and the exit band determine the least period of a
positive reflected return, including at times outside the sampled subsequence. -/
theorem exact_period_of_shot {t e : ℝ} {k : ℕ} (ht : t ∈ Icc 0 (1/100 : ℝ))
    (he : 0 < e) (he' : e ≤ 1/10)
    (hchannel : ∀ j ≤ k, (H t)^[j] e ∈ Icc e cap)
    (hexit : (H t)^[k+1] e ∈ Icc (9/10 : ℝ) (6/5))
    (hreturn : (H t)^[k+2] e = -e) :
    (quad (-7/4+t))^[3*(k+2)] e = e ∧
      ∀ n, 0 < n → n < 3*(k+2) → (quad (-7/4+t))^[n] e ≠ e := by
  constructor
  · rw [positive_iterates_even _ _ (by omega : 0 < 3*(k+2)), reflected_blocks, hreturn, neg_neg]
  intro n hn hbound
  let j := n/3
  let r := n%3
  have hnr : n = r + 3*j := (Nat.mod_add_div n 3).symm
  have hr : r < 3 := Nat.mod_lt _ (by decide)
  have hj : j ≤ k+1 := by omega
  rw [positive_iterates_even _ _ hn, hnr, Function.iterate_add_apply, reflected_blocks]
  let z := (H t)^[j] e
  change (quad (-7/4+t))^[r] (-z) ≠ e
  rcases lt_or_eq_of_le hj with hj | hj
  · have hz := hchannel j (by omega)
    have hsep := small_block_separation ht (z := z) ⟨he.le.trans hz.1, hz.2⟩
    have hpos : 0 < z := he.trans_le hz.1
    rcases (show r = 0 ∨ r = 1 ∨ r = 2 by omega) with h | h | h
    · rw [h]; change -z ≠ e; linarith
    · rw [h]; change quad _ (-z) ≠ e; linarith [hsep.1]
    · rw [h]; linarith [hsep.2]
  · have hz : z ∈ Icc (9/10 : ℝ) (6/5) := by simpa only [z, hj] using hexit
    have hsep := exit_block_separation ht hz
    rcases (show r = 0 ∨ r = 1 ∨ r = 2 by omega) with h | h | h
    · rw [h]; change -z ≠ e; linarith [hz.1]
    · rw [h]; change quad _ (-z) ≠ e; linarith [hsep.1]
    · rw [h]; linarith [hsep.2]

/-- The last critical iterate before entry is the nonperiodic partner `-e` of
`e` under the two-to-one quadratic map. One more step enters the exact cycle. -/
theorem critical_preperiod_of_shot {t e : ℝ} {k : ℕ} (he : 0 < e)
    (hcritical : (H t)^[k+2] 0 = e)
    (hcycle : (quad (-7/4+t))^[3*(k+2)] e = e ∧
      ∀ n, 0 < n → n < 3*(k+2) → (quad (-7/4+t))^[n] e ≠ e) :
    minimalPeriod (quad (-7/4+t)) ((quad (-7/4+t))^[3*(k+2)+1] 0) = 3*(k+2) ∧
      ∀ m ≤ 3*(k+2), (quad (-7/4+t))^[m] 0 ∉ periodicPts (quad (-7/4+t)) := by
  let f := quad (-7/4+t)
  let N := 3*(k+2)
  have hN : 0 < N := by dsimp [N]; omega
  have hper : IsPeriodicPt f N e := hcycle.1
  have hmin : minimalPeriod f e = N := by
    apply le_antisymm (hper.minimalPeriod_le hN)
    by_contra! h
    exact hcycle.2 _ (hper.minimalPeriod_pos hN) h (isPeriodicPt_minimalPeriod f e)
  have hlast : f^[N] 0 = -e := by
    simpa [f, N, hcritical] using reflected_blocks t 0 (k+2)
  have heven : f (-e) = f e := by simp [f, quad]
  constructor
  · change minimalPeriod f (f^[N+1] 0) = N
    rw [Function.iterate_succ_apply', hlast, heven,
      minimalPeriod_apply (mk_mem_periodicPts hN hper), hmin]
  · intro m hm hmem
    obtain ⟨n, hn, hperiodic⟩ := mem_periodicPts.mp hmem
    have htwin : IsPeriodicPt f n (-e) := by
      have h := hperiodic.apply_iterate (N-m)
      change IsPeriodicPt f n (f^[N-m] (f^[m] 0)) at h
      rwa [← Function.iterate_add_apply, Nat.sub_add_cancel hm, hlast] at h
    have heq := htwin.eq_of_apply_eq hper hn hN heven
    linarith

end
end LoopsParabolic

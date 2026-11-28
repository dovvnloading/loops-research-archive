import Mathlib.Analysis.Complex.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Explicit finite-composition stability for the limiting crest gate

The error is measured on a fixed complex disk.  Membership of the
perturbed orbit in that disk is a conclusion of the induction, not an
input.  This is the quantitative composition step needed when the moving
fourth critical cut is compared with the separately certified terminal
crest point.
-/

namespace LimitingCrestPerturbation

open Function

/-- Amplification of a uniform map error under a Lipschitz constant five. -/
def errorCoefficient : ℕ → ℝ
  | 0 => 0
  | n + 1 => 1 + 5 * errorCoefficient n

private theorem errorCoefficient_bounds (n : ℕ) (hn : n ≤ 4) :
    0 ≤ errorCoefficient n ∧ errorCoefficient n ≤ 156 := by
  interval_cases n <;> norm_num [errorCoefficient]

private theorem quadratic_real_unit_invariant (κ t : ℝ)
    (hκ : 0 ≤ κ) (hκ2 : κ ≤ 2) (ht : |t| ≤ 1) :
    |1-κ*t^2| ≤ 1 := by
  have ht' := abs_le.mp ht
  have hinterval : 0 ≤ (1-t)*(1+t) :=
    mul_nonneg (by linarith [ht'.2]) (by linarith [ht'.1])
  have ht2 : t^2 ≤ 1 := by nlinarith
  have hprod0 : 0 ≤ κ*t^2 := mul_nonneg hκ (sq_nonneg t)
  have hprod2 : κ*t^2 ≤ 2 := by
    calc
      κ*t^2 ≤ κ*1 := mul_le_mul_of_nonneg_left ht2 hκ
      _ ≤ 2 := by linarith
  rw [abs_le]
  constructor <;> linarith

/-- Every critical iterate of the real normalized quadratic lies in the
unit disk for coefficients between zero and two. -/
theorem quadratic_critical_orbit_unit (κ : ℝ) (hκ : 0 ≤ κ) (hκ2 : κ ≤ 2)
    (n : ℕ) :
    ‖((fun w : ℂ => 1-(κ : ℂ)*w^2)^[n]) 0‖ ≤ 1 := by
  have hreal : ∀ m : ℕ, ∃ t : ℝ, |t| ≤ 1 ∧
      ((fun w : ℂ => 1-(κ : ℂ)*w^2)^[m]) 0 = (t : ℂ) := by
    intro m
    induction m with
    | zero => exact ⟨0, by norm_num, by simp⟩
    | succ m ih =>
      obtain ⟨t, ht, he⟩ := ih
      refine ⟨1-κ*t^2, quadratic_real_unit_invariant κ t hκ hκ2 ht, ?_⟩
      rw [iterate_succ_apply', he]
      push_cast
      rfl
  obtain ⟨t, ht, he⟩ := hreal n
  rw [he, Complex.norm_real, Real.norm_eq_abs]
  exact ht

/-- The normalized quadratic has Lipschitz constant five on the closed
disk of radius 23/20, uniformly for coefficients between zero and two. -/
theorem quadratic_disk_lipschitz (κ : ℝ) (hκ : 0 ≤ κ) (hκ2 : κ ≤ 2)
    (z w : ℂ) (hz : ‖z‖ ≤ 23/20) (hw : ‖w‖ ≤ 23/20) :
    ‖(1 - (κ : ℂ) * z^2) - (1 - (κ : ℂ) * w^2)‖ ≤ 5 * ‖z-w‖ := by
  have hid : (1 - (κ : ℂ) * z^2) - (1 - (κ : ℂ) * w^2) =
      -(κ : ℂ) * (z-w) * (z+w) := by ring
  have hsum : κ * (‖z‖ + ‖w‖) ≤ 5 := by
    calc
      κ * (‖z‖ + ‖w‖) ≤ 2 * (‖z‖ + ‖w‖) :=
        mul_le_mul_of_nonneg_right hκ2 (by positivity)
      _ ≤ 5 := by linarith
  calc
    ‖(1 - (κ : ℂ) * z^2) - (1 - (κ : ℂ) * w^2)‖ =
        κ * ‖z-w‖ * ‖z+w‖ := by
      rw [hid, norm_mul, norm_mul, norm_neg, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg hκ]
    _ ≤ κ * ‖z-w‖ * (‖z‖ + ‖w‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le z w) (by positivity)
    _ = (κ * (‖z‖ + ‖w‖)) * ‖z-w‖ := by ring
    _ ≤ 5 * ‖z-w‖ := mul_le_mul_of_nonneg_right hsum (norm_nonneg _)

/-- Four complete compositions remain in the approximation disk and
have explicit error bounds.  Only the reference orbit is assumed to lie
in the unit disk; no bound on the perturbed orbit is postulated. -/
theorem iterate_perturbation_up_to_four
    (H Q : ℂ → ℂ) (z : ℂ) (ε : ℝ)
    (hε : 0 ≤ ε) (hεmax : ε ≤ 1/500000)
    (hclose : ∀ w : ℂ, ‖w‖ ≤ 23/20 → ‖H w - Q w‖ ≤ ε)
    (hlip : ∀ v w : ℂ, ‖v‖ ≤ 23/20 → ‖w‖ ≤ 23/20 →
      ‖Q v-Q w‖ ≤ 5 * ‖v-w‖)
    (hmodel : ∀ n : ℕ, n ≤ 4 → ‖(Q^[n]) z‖ ≤ 1) :
    ∀ n : ℕ, n ≤ 4 →
      ‖(H^[n]) z-(Q^[n]) z‖ ≤ errorCoefficient n * ε ∧
      ‖(H^[n]) z‖ ≤ 23/20 := by
  intro n
  induction n with
  | zero =>
    intro hn
    constructor
    · simp [errorCoefficient]
    · simpa using (show ‖z‖ ≤ (23/20 : ℝ) by
        have hz := hmodel 0 (by omega)
        simpa using hz.trans (by norm_num : (1 : ℝ) ≤ 23/20))
  | succ n ih =>
    intro hn
    have hn4 : n ≤ 4 := by omega
    obtain ⟨herr, hHdisk⟩ := ih hn4
    have hQdisk : ‖(Q^[n]) z‖ ≤ 23/20 :=
      (hmodel n hn4).trans (by norm_num)
    have hnext : ‖(H^[n+1]) z-(Q^[n+1]) z‖ ≤
        errorCoefficient (n+1) * ε := by
      rw [iterate_succ_apply', iterate_succ_apply']
      calc
        ‖H ((H^[n]) z)-Q ((Q^[n]) z)‖ ≤
            ‖H ((H^[n]) z)-Q ((H^[n]) z)‖ +
              ‖Q ((H^[n]) z)-Q ((Q^[n]) z)‖ := by
                simpa only [dist_eq_norm] using
                  dist_triangle (H ((H^[n]) z)) (Q ((H^[n]) z)) (Q ((Q^[n]) z))
        _ ≤ ε + 5 * (errorCoefficient n * ε) :=
          add_le_add (hclose _ hHdisk)
            ((hlip _ _ hHdisk hQdisk).trans
              (mul_le_mul_of_nonneg_left herr (by norm_num)))
        _ = errorCoefficient (n+1) * ε := by
          simp only [errorCoefficient]
          ring
    refine ⟨hnext, ?_⟩
    have hb := errorCoefficient_bounds (n+1) hn
    have hemax : errorCoefficient (n+1) * ε ≤ 156/500000 := by
      calc
        errorCoefficient (n+1) * ε ≤ 156 * ε :=
          mul_le_mul_of_nonneg_right hb.2 hε
        _ ≤ 156/500000 := by linarith
    have htri : ‖(H^[n+1]) z‖ ≤
        ‖(H^[n+1]) z-(Q^[n+1]) z‖ + ‖(Q^[n+1]) z‖ := by
      simpa only [dist_eq_norm, sub_zero] using
        dist_triangle ((H^[n+1]) z) ((Q^[n+1]) z) (0 : ℂ)
    have hq := hmodel (n+1) hn
    linarith

/-- In particular the moving fourth critical cut has error at most
156 times the disk error, with every intermediate domain check proved. -/
theorem quadratic_fourth_cut_error
    (κ : ℝ) (hκ : 0 ≤ κ) (hκ2 : κ ≤ 2)
    (H : ℂ → ℂ) (ε : ℝ) (hε : 0 ≤ ε) (hεmax : ε ≤ 1/500000)
    (hclose : ∀ w : ℂ, ‖w‖ ≤ 23/20 →
      ‖H w - (1 - (κ : ℂ) * w^2)‖ ≤ ε) :
    ‖(H^[4]) 0-((fun w : ℂ => 1 - (κ : ℂ) * w^2)^[4]) 0‖ ≤ 156 * ε ∧
      ∀ n : ℕ, n ≤ 4 → ‖(H^[n]) 0‖ ≤ 23/20 := by
  have hs := iterate_perturbation_up_to_four H
    (fun w : ℂ => 1 - (κ : ℂ) * w^2) 0 ε hε hεmax hclose
    (quadratic_disk_lipschitz κ hκ hκ2)
    (fun n _ => quadratic_critical_orbit_unit κ hκ hκ2 n)
  refine ⟨?_, fun n hn => (hs n hn).2⟩
  have hec : errorCoefficient 4 = (156 : ℝ) := by norm_num [errorCoefficient]
  simpa only [hec] using (hs 4 le_rfl).1

/-- A reference fourth critical cut below 0.976 remains below 0.9764
under the stated disk error.  This is strict enough for the independently
certified terminal point below -0.977. -/
theorem fourth_cut_real_upper
    (H Q : ℂ → ℂ) (ε : ℝ) (hεmax : ε ≤ 1/500000)
    (herror : ‖(H^[4]) 0-(Q^[4]) 0‖ ≤ 156 * ε)
    (hcut : ((Q^[4]) 0).re ≤ 122/125) :
    ((H^[4]) 0).re < 2441/2500 := by
  have hreal := (abs_le.mp (Complex.abs_re_le_norm
    ((H^[4]) 0-(Q^[4]) 0))).2
  simp only [Complex.sub_re] at hreal
  linarith

end LimitingCrestPerturbation

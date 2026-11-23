import ParabolicChannel
import Mathlib.Tactic.FinCases

/-! Disjoint real ranges for the three phases of an ordinary return block
and the three phases of its exit block. -/
namespace LoopsParabolic
open Set Function
noncomputable section

def band : Fin 6 → Set ℝ
  | 0 => Icc (-cap) cap
  | 1 => Iic (-(3/2))
  | 2 => Ici (1/2)
  | 3 => Icc (-(6/5)) (-(9/10))
  | 4 => Icc (-(4/5)) (-(1/2))
  | 5 => Icc (-(7/5)) (-(5/4))

theorem band_disjoint {i j : Fin 6} (h : i ≠ j) : Disjoint (band i) (band j) := by
  refine Set.disjoint_left.mpr fun {z} hi hj ↦ ?_
  fin_cases i <;> fin_cases j <;>
    norm_num [band, cap, mem_Iic, mem_Icc, mem_Ici] at * <;>
    (try obtain ⟨hl,hu⟩ := hi) <;> (try obtain ⟨jl,ju⟩ := hj) <;> linarith

theorem small_phase_bands {t z : ℝ} (ht : t ∈ Icc 0 (1/100 : ℝ)) (hz : |z| ≤ cap) :
    z ∈ band 0 ∧ quad (-7/4+t) z ∈ band 1 ∧ (quad (-7/4+t))^[2] z ∈ band 2 := by
  obtain ⟨zl,zh⟩ := abs_le.mp hz
  have hs := sq_le_sq' zl zh
  have hf : quad (-7/4+t) z ≤ -(3/2 : ℝ) := by
    unfold quad; unfold cap at hs; linarith [ht.2]
  refine ⟨⟨zl,zh⟩, by simpa [band] using hf, ?_⟩
  change (1/2:ℝ) ≤ (quad (-7/4+t) z)^2+(-7/4+t)
  have sqf := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤3/2)
    (show (3/2:ℝ)≤ -quad (-7/4+t) z by linarith) 2
  nlinarith [ht.1]

private theorem neg_of_square_bounds {x l u : ℝ} (hx : x ≤ 0) (hl : 0 ≤ l) (hu : 0 ≤ u)
    (hls : l^2 ≤ x^2) (hus : x^2 ≤ u^2) : x ∈ Icc (-u) (-l) := by
  have a := (sq_le_sq₀ hl (neg_nonneg.mpr hx)).mp (by simpa [neg_sq] using hls)
  have b := (sq_le_sq₀ (neg_nonneg.mpr hx) hu).mp (by simpa [neg_sq] using hus)
  exact ⟨by linarith,by linarith⟩

theorem exit_phase_bands {t z : ℝ} (ht : t ∈ Icc 0 (1/100 : ℝ)) (hz : z ∈ band 3)
    (hret : |(quad (-7/4+t))^[3] z| ≤ 1/10) :
    z ∈ band 3 ∧ quad (-7/4+t) z ∈ band 4 ∧ (quad (-7/4+t))^[2] z ∈ band 5 := by
  let x := quad (-7/4+t) z
  let y := quad (-7/4+t) x
  change z ∈ Icc (-(6/5):ℝ) (-(9/10)) at hz
  have zl := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 9/10)
    (show (9/10:ℝ) ≤ -z by linarith [hz.2]) 2
  have zu := sq_le_sq' hz.1 (show z ≤ 6/5 by linarith [hz.2])
  have xl : -1 ≤ x := by dsimp [x,quad]; nlinarith [ht.1]
  have xu : x ≤ 0 := by dsimp [x,quad]; nlinarith [ht.2]
  have yn : y ≤ 0 := by
    dsimp [y,quad]; nlinarith [sq_le_sq' xl (show x≤1 by linarith), ht.2]
  obtain ⟨rl,ru⟩ := abs_le.mp hret
  change -(1/10:ℝ) ≤ y^2+(-7/4+t) at rl
  change y^2+(-7/4+t) ≤ 1/10 at ru
  have hy : y ∈ Icc (-(7/5) : ℝ) (-(5/4)) :=
    neg_of_square_bounds yn (by norm_num) (by norm_num)
      (by linarith [ht.2]) (by linarith [ht.1])
  have hx : x ∈ Icc (-(4/5) : ℝ) (-(1/2)) := by
    apply neg_of_square_bounds xu (by norm_num) (by norm_num)
    · have h := hy.1; dsimp [y,quad] at h; linarith [ht.2]
    · have h := hy.2; dsimp [y,quad] at h; linarith [ht.1]
  exact ⟨hz, hx, hy⟩

private theorem abs_eq_of_quad_eq {c x y : ℝ} (h : quad c x = quad c y) : |x| = |y| :=
  (sq_eq_sq_iff_abs_eq_abs x y).mp (add_right_cancel h)

/-- Before phase three, a collision in the small band can only identify
opposite points of equal absolute value. -/
theorem small_phase_abs_injective {t x y : ℝ} {r : ℕ} (ht : t ∈ Icc 0 (1/100 : ℝ))
    (hx : |x| ≤ cap) (hy : |y| ≤ cap) (hr : r ≤ 2)
    (heq : (quad (-7/4+t))^[r] x = (quad (-7/4+t))^[r] y) : |x| = |y| := by
  rcases (show r = 0 ∨ r = 1 ∨ r = 2 by omega) with h | h | h
  · subst r; exact congrArg abs heq
  · subst r; exact abs_eq_of_quad_eq heq
  · subst r
    have xx : quad (-7/4+t) x ≤ -(3/2:ℝ) := (small_phase_bands ht hx).2.1
    have yy : quad (-7/4+t) y ≤ -(3/2:ℝ) := (small_phase_bands ht hy).2.1
    have h := abs_eq_of_quad_eq heq
    change |quad (-7/4+t) x| = |quad (-7/4+t) y| at h
    rw [abs_of_nonpos (by linarith),abs_of_nonpos (by linarith)] at h
    exact abs_eq_of_quad_eq (neg_inj.mp h)

end
end LoopsParabolic

import ParabolicChannel

/-! Explicit uniform wall inequalities for the parameter shooting construction. -/

namespace LoopsParabolic
open Set
noncomputable section

/-- These seven inequalities orient the two parameter crossings at the exit. -/
def WindowWalls (t : ℝ) : Prop :=
  0 < H t 0 ∧ H t 0 < 1/10 ∧
  1/10 < H t (H t (7/20)) ∧ H t (H t (19/50)) < 0 ∧
  H t (H t (39/100)) < -(1/10) ∧
  9/10 < H t (7/20) ∧ H t (39/100) < 6/5

private abbrev Box := ℝ × ℝ
private def Holds (A : Box) (x : ℝ) : Prop := x ∈ Icc A.1 A.2
private def point (x : ℝ) : Box := (x, x)
private def subBox (A B : Box) : Box := (A.1 - B.2, A.2 - B.1)
private def sqBox (A : Box) : Box :=
  ((max 0 (max A.1 (-A.2)))^2, (max (-A.1) A.2)^2)

private theorem sub_mem {A B : Box} {x y : ℝ} (hx : Holds A x) (hy : Holds B y) :
    Holds (subBox A B) (x-y) := ⟨sub_le_sub hx.1 hy.2, sub_le_sub hx.2 hy.1⟩

private theorem sq_mem {A : Box} {x : ℝ} (hx : Holds A x) : Holds (sqBox A) (x^2) := by
  have hl : max 0 (max A.1 (-A.2)) ≤ |x| := max_le (abs_nonneg _) <|
    max_le (hx.1.trans (le_abs_self x)) ((neg_le_neg hx.2).trans (neg_le_abs x))
  have hu : |x| ≤ max (-A.1) A.2 := abs_le.mpr
    ⟨by linarith [le_max_left (-A.1) A.2, hx.1], hx.2.trans (le_max_right _ _)⟩
  exact ⟨by simpa only [sq_abs, sqBox] using pow_le_pow_left₀ (le_max_left _ _) hl 2,
    by simpa only [sq_abs, sqBox] using pow_le_pow_left₀ (abs_nonneg x) hu 2⟩

private def hbox (A Z : Box) : Box := subBox A (sqBox (subBox (sqBox (subBox A (sqBox Z))) A))

private theorem h_mem {A Z : Box} {t z : ℝ} (ha : Holds A (7/4-t)) (hz : Holds Z z) :
    Holds (hbox A Z) (H t z) := sub_mem ha (sq_mem (sub_mem (sq_mem (sub_mem ha (sq_mem hz))) ha))

private def wallCertificate (A : Box) : Prop :=
  let z := hbox A (point 0)
  let a := hbox A (point (7/20))
  let b := hbox A (point (19/50))
  let c := hbox A (point (39/100))
  0 < z.1 ∧ z.2 < 1/10 ∧ 1/10 < (hbox A a).1 ∧ (hbox A b).2 < 0 ∧
    (hbox A c).2 < -(1/10) ∧ 9/10 < a.1 ∧ c.2 < 6/5

private theorem walls_of_certificate {A : Box} {t : ℝ} (ha : Holds A (7/4-t))
    (hc : wallCertificate A) : WindowWalls t := by
  have h (z : ℝ) := h_mem ha (⟨le_rfl, le_rfl⟩ : Holds (point z) z)
  obtain ⟨h₀,h₁,h₂,h₃,h₄,h₅,h₆⟩ := hc
  exact ⟨h₀.trans_le (h 0).1, (h 0).2.trans_lt h₁,
    h₂.trans_le (h_mem ha (h _)).1, (h_mem ha (h _)).2.trans_lt h₃,
    (h_mem ha (h _)).2.trans_lt h₄, h₅.trans_le (h _).1, (h _).2.trans_lt h₆⟩

/-- Two rational boxes certify the whole parameter window, including both endpoints. -/
theorem window_walls {t : ℝ} (ht : t ∈ Icc 0 (1/100 : ℝ)) : WindowWalls t := by
  by_cases h : t ≤ 1/200
  · apply walls_of_certificate (A := (349/200, 7/4))
    · constructor <;> dsimp <;> linarith [ht.1]
    · norm_num [wallCertificate, hbox, sqBox, subBox, point, max_def]
  · apply walls_of_certificate (A := (87/50, 349/200))
    · constructor <;> dsimp <;> linarith [ht.2]
    · norm_num [wallCertificate, hbox, sqBox, subBox, point, max_def]

/-- At the rightmost parameter the clipped flight reaches the cap on step four. -/
theorem track_four_at_endpoint : cap ≤ track (1/100) 4 := by
  have ht : (1/100:ℝ) ∈ Icc 0 (1/100) := by constructor <;> norm_num
  have step {j : ℕ} {x y : ℝ} (hx : x ∈ Icc 0 cap) (hxt : x ≤ track (1/100) j)
      (hy : y ≤ cap) (hxy : y ≤ H (1/100) x) : y ≤ track (1/100) (j+1) :=
    le_min hy (hxy.trans (channel_mono ht hx (track_mem ht j) hxt))
  have h₁ : (8/100:ℝ) ≤ track (1/100) 1 := by
    apply step (j := 0) (x := 0) <;> norm_num [track, flight, cap, H, Set.mem_Icc]
  have h₂ : (13/100:ℝ) ≤ track (1/100) 2 := by
    apply step (j := 1) (x := 8/100) _ h₁ <;> norm_num [cap, H, Set.mem_Icc]
  have h₃ : (21/100:ℝ) ≤ track (1/100) 3 := by
    apply step (j := 2) (x := 13/100) _ h₂ <;> norm_num [cap, H, Set.mem_Icc]
  apply step (j := 3) (x := 21/100) _ h₃ <;> norm_num [cap, H, Set.mem_Icc]

end
end LoopsParabolic

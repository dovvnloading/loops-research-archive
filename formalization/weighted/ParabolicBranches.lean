import ParabolicTipShooting
import ParabolicTipPeriod

/-! The signed orbit relation yields two full real branches on the central
interval. The two endpoints of each channel image interleave strictly with
the endpoints of the next image. -/
namespace LoopsParabolic
open Set Function
noncomputable section

private theorem spatial_diff (t x y : ℝ) :
    H t y-H t x =
      (y^2-x^2)*((7/4-t-y^2)+(7/4-t-x^2))*
      (((7/4-t-y^2)^2-(7/4-t))+((7/4-t-x^2)^2-(7/4-t))) := by
  unfold H; ring

theorem channel_strictMono {t : ℝ} (ht : t ∈ Icc 0 (1/100 : ℝ)) :
    StrictMonoOn (H t) (Icc 0 cap) := by
  intro x hx y hy hxy
  have bound {w : ℝ} (hw : w ∈ Icc 0 cap) :
      3/2 ≤ 7/4-t-w^2 ∧ 0 < (7/4-t-w^2)^2-(7/4-t) := by
    have hsq := sq_le_sq' (by unfold cap; linarith [hw.1] : -cap ≤ w) hw.2
    unfold cap at hsq
    have h : 3/2 ≤ 7/4-t-w^2 := by nlinarith [ht.2]
    exact ⟨h, by nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 3/2) h 2,ht.1]⟩
  obtain ⟨h₁,h₂⟩ := bound hx
  obtain ⟨h₃,h₄⟩ := bound hy
  apply sub_pos.mp
  rw [spatial_diff]
  exact mul_pos (mul_pos (by nlinarith [sq_lt_sq' (by linarith [hx.1] : -y < x) hxy])
    (by linarith)) (by linarith)

private theorem exit_strictAnti {t : ℝ} (ht : t ∈ Icc 0 (1/100 : ℝ)) :
    StrictAntiOn (H t) (Icc (9/10 : ℝ) (6/5)) := by
  intro x hx y hy hxy
  have bound {w : ℝ} (hw : w ∈ Icc (9/10 : ℝ) (6/5)) :
      0 < 7/4-t-w^2 ∧ (7/4-t-w^2)^2-(7/4-t) < 0 := by
    have hwlo := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 9/10) hw.1 2
    have hwhi := sq_le_sq' (by linarith [hw.1] : -(6/5 : ℝ) ≤ w) hw.2
    have h₁ : 0 < 7/4-t-w^2 := by nlinarith [ht.2]
    have h₂ : 7/4-t-w^2 ≤ 1 := by nlinarith [ht.1]
    exact ⟨h₁,by nlinarith [sq_le_sq' (by linarith : -1 ≤ 7/4-t-w^2) h₂,ht.2]⟩
  obtain ⟨h₁,h₂⟩ := bound hx
  obtain ⟨h₃,h₄⟩ := bound hy
  apply sub_neg.mp
  rw [spatial_diff]
  exact mul_neg_of_pos_of_neg (mul_pos (by nlinarith [sq_lt_sq' (by linarith [hx.1] : -y < x) hxy])
    (by linarith)) (by linarith)

private theorem abs_mem {x e : ℝ} (hx : x ∈ Icc (-e) e) : |x| ∈ Icc 0 e :=
  ⟨abs_nonneg _, abs_le.mpr hx⟩

private theorem block_control {t e : ℝ} {k : ℕ} (hs : Shot k t e) (j : ℕ) (hj : j ≤ k+1) :
    StrictMonoOn ((H t)^[j]) (Icc 0 e) := by
  induction j with
  | zero => intro x hx y hy h; exact h
  | succ j ih =>
    have hjk : j ≤ k := by omega
    have prev := ih (by omega)
    have mem {v : ℝ} (hv : v ∈ Icc 0 e) : (H t)^[j] v ∈ Icc 0 cap := by
      have h₀ : (0:ℝ) ∈ Icc 0 e := ⟨le_rfl,hs.e_pos.le⟩
      have he : e ∈ Icc 0 e := ⟨hs.e_pos.le,le_rfl⟩
      exact ⟨(hs.first_corridor j hjk).1.trans (prev.monotoneOn h₀ hv hv.1),
        (prev.monotoneOn hv he hv.2).trans (hs.corridor j hjk).2⟩
    intro x hx y hy hxy
    simp only [Function.iterate_succ_apply']
    exact channel_strictMono ⟨hs.t_pos.le,hs.t_small⟩ (mem hx) (mem hy) (prev hx hy hxy)

private theorem block_sandwich {t e : ℝ} {k j : ℕ} (hs : Shot k t e) (hj : j ≤ k+1)
    {v : ℝ} (hv : v ∈ Icc 0 e) :
    (H t)^[j] 0 ≤ (H t)^[j] v ∧ (H t)^[j] v ≤ (H t)^[j] e := by
  have mon := (block_control hs j hj).monotoneOn
  exact ⟨mon ⟨le_rfl,hs.e_pos.le⟩ hv hv.1, mon hv ⟨hs.e_pos.le,le_rfl⟩ hv.2⟩

private theorem exit_range {t e v : ℝ} {k : ℕ} (hs : Shot k t e) (hv : v ∈ Icc 0 e) :
    (H t)^[k+1] v ∈ Icc (9/10 : ℝ) (6/5) := by
  have htt : t ∈ Icc 0 (1/100 : ℝ) := ⟨hs.t_pos.le,hs.t_small⟩
  have h₀ := channel_mono htt (show (7/20:ℝ) ∈ Icc 0 cap by norm_num [cap])
    (hs.first_corridor k le_rfl) hs.first_exit.1
  have h₁ := block_sandwich hs (j := k+1) le_rfl hv
  refine ⟨?_,h₁.2.trans hs.penultimate.2⟩
  have hbase : 9/10 ≤ (H t)^[k+1] 0 := by
    rw [Function.iterate_succ_apply']
    exact (window_walls htt).2.2.2.2.2.1.le.trans h₀
  exact hbase.trans h₁.1

private theorem last_branch {t e : ℝ} {k : ℕ} (hs : Shot k t e) :
    StrictAntiOn ((H t)^[k+2]) (Icc 0 e) := by
  intro x hx y hy hxy
  simp only [Function.iterate_succ_apply' (H t) (k+1)]
  exact exit_strictAnti ⟨hs.t_pos.le,hs.t_small⟩ (exit_range hs hx) (exit_range hs hy)
    (block_control hs _ le_rfl hx hy hxy)

private theorem reflected_abs (t x : ℝ) {j : ℕ} (hj : 0 < j) :
    (quad (-7/4+t))^[3*j] x = - (H t)^[j] |x| := by
  rcases le_or_gt 0 x with h | h
  · rw [abs_of_nonneg h, positive_iterates_even _ _ (by omega : 0 < 3*j), reflected_blocks]
  · rw [abs_of_neg h, ← reflected_blocks, neg_neg]

theorem block_abs {t e x : ℝ} {k j : ℕ} (hs : Shot k t e) (hx : x ∈ Icc (-e) e)
    (hj : j ≤ k+1) : |(quad (-7/4+t))^[3*j] x| = (H t)^[j] |x| := by
  rcases Nat.eq_zero_or_pos j with rfl | hp
  · simp
  rw [reflected_abs _ _ hp,abs_neg,abs_of_nonneg]
  rcases lt_or_eq_of_le hj with h | rfl
  · exact (hs.first_corridor j (by omega)).1.trans (block_sandwich hs hj (abs_mem hx)).1
  · linarith [(exit_range hs (abs_mem hx)).1]

theorem block_small {t e x : ℝ} {k j : ℕ} (hs : Shot k t e) (hx : x ∈ Icc (-e) e)
    (hj : j ≤ k) : |(quad (-7/4+t))^[3*j] x| ≤ cap := by
  rw [block_abs hs hx (by omega)]
  exact (block_sandwich hs (by omega) (abs_mem hx)).2.trans (hs.corridor j hj).2

theorem block_exit {t e x : ℝ} {k : ℕ} (hs : Shot k t e) (hx : x ∈ Icc (-e) e) :
    (quad (-7/4+t))^[3*(k+1)] x ∈ Icc (-(6/5):ℝ) (-(9/10)) := by
  rw [reflected_abs _ _ (by omega)]
  exact ⟨neg_le_neg (exit_range hs (abs_mem hx)).2, neg_le_neg (exit_range hs (abs_mem hx)).1⟩

private theorem consecutive {t e : ℝ} {k j : ℕ} (hs : Shot k t e) (hj : j ≤ k) :
    (H t)^[j] e < (H t)^[j+1] 0 := by
  induction j with
  | zero => simpa using hs.gap
  | succ j ih =>
    rw [Function.iterate_succ_apply' (H t) j, Function.iterate_succ_apply' (H t) (j+1)]
    exact channel_strictMono ⟨hs.t_pos.le,hs.t_small⟩
      ⟨hs.e_pos.le.trans (hs.corridor j (by omega)).1,(hs.corridor j (by omega)).2⟩
      (hs.first_corridor (j+1) hj) (ih (by omega))

theorem block_interleave {t e x y : ℝ} {k j l : ℕ} (hs : Shot k t e)
    (hx : x ∈ Icc (-e) e) (hy : y ∈ Icc (-e) e) (hjl : j < l) (hl : l ≤ k+1) :
    (H t)^[j] |x| < (H t)^[l] |y| := by
  have levels {a b : ℕ} (hab : a ≤ b) (hb : b ≤ k+1) : (H t)^[a] 0 ≤ (H t)^[b] 0 := by
    induction b with
    | zero =>
      have ha : a = 0 := by omega
      rw [ha]
    | succ b ih =>
      rcases Nat.eq_or_lt_of_le hab with h | h
      · rw [h]
      · have hd := channel_drift ⟨hs.t_pos.le,hs.t_small⟩ (hs.first_corridor b (by omega))
        rw [Function.iterate_succ_apply']
        exact (ih (by omega) (by omega)).trans (by linarith [hs.t_pos])
  exact ((block_sandwich hs (by omega) (abs_mem hx)).2.trans_lt
    (consecutive hs (by omega))).trans_le
    ((levels hjl hl).trans (block_sandwich hs hl (abs_mem hy)).1)

theorem return_mem {t e x : ℝ} {k : ℕ} (hs : Shot k t e) (hx : x ∈ Icc (-e) e) :
    (quad (-7/4+t))^[3*(k+2)] x ∈ Icc (-e) e := by
  rw [reflected_abs _ _ (by omega)]
  have low := (last_branch hs).antitoneOn (abs_mem hx) (right_mem_Icc.mpr hs.e_pos.le) (abs_mem hx).2
  have high := (last_branch hs).antitoneOn (left_mem_Icc.mpr hs.e_pos.le) (abs_mem hx) (abs_mem hx).1
  rw [hs.collision] at low
  rw [hs.critical] at high
  constructor <;> linarith

/-- The physical return is strictly monotone and onto the entire central
interval on each of its closed halves. -/
theorem full_branches {t e : ℝ} {k : ℕ} (hs : Shot k t e) :
    let G := (quad (-7/4+t))^[3*(k+2)]
    StrictAntiOn G (Icc (-e) 0) ∧ StrictMonoOn G (Icc 0 e) ∧
      G '' Icc (-e) 0 = Icc (-e) e ∧ G '' Icc 0 e = Icc (-e) e := by
  intro G
  have hn : 0 < k+2 := by omega
  have h₀ : G 0 = -e := by simp [G,reflected_abs _ _ hn,hs.critical]
  have he : G e = e := by dsimp only [G]; rw [reflected_abs _ _ hn,abs_of_pos hs.e_pos,hs.collision,neg_neg]
  have he' : G (-e) = e := by dsimp only [G]; rw [reflected_abs _ _ hn,abs_neg,abs_of_pos hs.e_pos,hs.collision,neg_neg]
  have hc : Continuous G := Continuous.iterate (show Continuous (quad (-7/4+t)) by unfold quad; fun_prop) _
  have left : StrictAntiOn G (Icc (-e) 0) := by
    intro a ha b hb hab
    change (quad _)^[3*(k+2)] _ < (quad _)^[3*(k+2)] _
    rw [reflected_abs _ _ hn,reflected_abs _ _ hn,abs_of_nonpos ha.2,abs_of_nonpos hb.2,neg_lt_neg_iff]
    exact last_branch hs ⟨by linarith [hb.2],by linarith [hb.1]⟩
      ⟨by linarith [ha.2],by linarith [ha.1]⟩ (neg_lt_neg hab)
  have right : StrictMonoOn G (Icc 0 e) := by
    intro a ha b hb hab
    change (quad _)^[3*(k+2)] _ < (quad _)^[3*(k+2)] _
    rw [reflected_abs _ _ hn,reflected_abs _ _ hn,abs_of_nonneg ha.1,abs_of_nonneg hb.1,neg_lt_neg_iff]
    exact last_branch hs ha hb hab
  refine ⟨left,right,?_,?_⟩
  · rw [hc.continuousOn.image_Icc_of_antitoneOn (by linarith [hs.e_pos]) left.antitoneOn,h₀,he']
  · rw [hc.continuousOn.image_Icc_of_monotoneOn hs.e_pos.le right.monotoneOn,h₀,he]

end
end LoopsParabolic

import ParabolicTipWindow
import ParabolicShooting
import ParabolicTipPeriod

/-! Uniqueness of the superattracting center on each critical exit slab. -/

namespace LoopsParabolic

open Set Function
noncomputable section

private def A (t y : ℝ) := 7/4-t-y^2
private def B (t y : ℝ) := (A t y)^2-(7/4-t)

private theorem param_diff (s t y : ℝ) :
    H t y-H s y = (t-s)*((A s y+A t y-1)*(B s y+B t y)-1) := by
  unfold H B A
  ring

private theorem low_inner {t y : ℝ} (ht : t ∈ Icc 0 (1/100:ℝ))
    (hy : y ∈ Icc 0 cap) : 3/2 ≤ A t y ∧ 1/2 ≤ B t y := by
  have hy' : y ≤ 2/5 := hy.2
  have hsq := pow_le_pow_left₀ hy.1 hy' 2
  have hA : 3/2 ≤ A t y := by unfold A; nlinarith [ht.2]
  refine ⟨hA, ?_⟩
  unfold B
  nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 3/2) hA 2, ht.1]

theorem channel_parameter_strictMono {y : ℝ} (hy : y ∈ Icc 0 cap) :
    StrictMonoOn (fun t => H t y) (Icc 0 (1/100:ℝ)) := by
  intro s hs t ht hst
  obtain ⟨hsA,hsB⟩ := low_inner hs hy
  obtain ⟨htA,htB⟩ := low_inner ht hy
  have hprod := mul_le_mul (show 2 ≤ A s y+A t y-1 by linarith)
    (show 1 ≤ B s y+B t y by linarith) (by norm_num) (by linarith)
  have hf : 0 < (A s y+A t y-1)*(B s y+B t y)-1 := by linarith
  have := mul_pos (sub_pos.mpr hst) hf
  linarith [param_diff s t y]

theorem track_monotone_parameter (k : ℕ) :
    MonotoneOn (fun t => track t k) (Icc 0 (1/100:ℝ)) := by
  intro s hs t ht hst
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
    apply min_le_min_left
    exact ((channel_parameter_strictMono (track_mem hs k)).monotoneOn hs ht hst).trans
      (channel_mono ht (track_mem hs k) (track_mem ht k) ih)

private theorem high_inner {t y : ℝ} (ht : t ∈ Icc 0 (1/100:ℝ))
    (hy : y ∈ Icc (47/50:ℝ) (11/10)) : 1/2 ≤ A t y ∧ B t y ≤ 0 := by
  have lo := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 47/50) hy.1 2
  have hi := pow_le_pow_left₀ (by linarith [hy.1] : 0 ≤ y) hy.2 2
  have ha : 1/2 ≤ A t y := by unfold A; nlinarith [ht.2]
  have hb : A t y ≤ 1 := by unfold A; nlinarith [ht.1]
  refine ⟨ha, ?_⟩
  unfold B
  nlinarith [pow_le_pow_left₀ (show 0 ≤ A t y by linarith) hb 2, ht.2]

private theorem high_param {y : ℝ} (hy : y ∈ Icc (47/50:ℝ) (11/10)) :
    StrictAntiOn (fun t => H t y) (Icc 0 (1/100:ℝ)) := by
  intro s hs t ht hst
  obtain ⟨hsA,hsB⟩ := high_inner hs hy
  obtain ⟨htA,htB⟩ := high_inner ht hy
  have h := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ A s y+A t y-1 by linarith)
    (show B s y+B t y ≤ 0 by linarith)
  have hf : (A s y+A t y-1)*(B s y+B t y)-1 < 0 := by linarith
  have := mul_neg_of_pos_of_neg (sub_pos.mpr hst) hf
  linarith [param_diff s t y]

private theorem high_arg {t : ℝ} (ht : t ∈ Icc 0 (1/100:ℝ)) :
    AntitoneOn (H t) (Icc (47/50:ℝ) (11/10)) := by
  intro x hx y hy hxy
  obtain ⟨hxA,hxB⟩ := high_inner ht hx
  obtain ⟨hyA,hyB⟩ := high_inner ht hy
  have hA : A t y ≤ A t x := by
    unfold A
    linarith [pow_le_pow_left₀ (by linarith [hx.1] : 0 ≤ x) hxy 2]
  have hB : B t y ≤ B t x := by
    unfold B
    linarith [pow_le_pow_left₀ (by linarith : 0 ≤ A t y) hA 2]
  have hh := pow_le_pow_left₀ (neg_nonneg.mpr hxB) (neg_le_neg hB) 2
  change (7/4-t)-(B t y)^2 ≤ (7/4-t)-(B t x)^2
  nlinarith

private theorem exit_image {t y : ℝ} (ht : t ∈ Icc 0 (1/100:ℝ))
    (hy : y ∈ Icc (7/20:ℝ) (19/50)) : H t y ∈ Icc (47/50:ℝ) (11/10) := by
  have h0 : (0:ℝ) ∈ Icc 0 (1/100:ℝ) := ⟨le_rfl, by norm_num⟩
  have h1 : (1/100:ℝ) ∈ Icc 0 (1/100:ℝ) := ⟨by norm_num, le_rfl⟩
  have hx : (7/20:ℝ) ∈ Icc 0 cap := by norm_num [cap,mem_Icc]
  have hz : (19/50:ℝ) ∈ Icc 0 cap := by norm_num [cap,mem_Icc]
  have hy' : y ∈ Icc 0 cap := ⟨hx.1.trans hy.1,hy.2.trans hz.2⟩
  constructor
  · exact (show 47/50 ≤ H 0 (7/20) by norm_num [H]).trans
      (((channel_parameter_strictMono hx).monotoneOn h0 ht ht.1).trans (channel_mono ht hx hy' hy.1))
  · exact (channel_mono ht hy' hz hy.2).trans
      (((channel_parameter_strictMono hz).monotoneOn ht h1 ht.2).trans
        (show H (1/100) (19/50) ≤ 11/10 by norm_num [H]))

def exitSlab (k : ℕ) : Set ℝ :=
  {t | t ∈ Icc 0 (1/100:ℝ) ∧ track t k ∈ Icc (7/20:ℝ) (19/50)}

private theorem return_on_slab {t : ℝ} {k : ℕ} (hs : t ∈ exitSlab k) :
    (H t)^[k+2] 0 = H t (H t (track t k)) := by
  have h := track_true hs.1 (show track t k < cap by unfold cap; linarith [hs.2.2])
  simp only [Function.iterate_succ_apply', h]

/-- Across the full exit slab, increasing the parameter strictly decreases
the final critical return. -/
theorem exit_return_strictAnti (k : ℕ) :
    StrictAntiOn (fun t => (H t)^[k+2] 0) (exitSlab k) := by
  intro s hs t ht hst
  simp only [return_on_slab hs,return_on_slab ht]
  have hi := track_monotone_parameter k hs.1 ht.1 hst.le
  have hu : H s (track s k) ≤ H t (track t k) :=
    ((channel_parameter_strictMono (track_mem hs.1 k)).monotoneOn hs.1 ht.1 hst.le).trans
    (channel_mono ht.1 (track_mem hs.1 k) (track_mem ht.1 k) hi)
  have hx := exit_image hs.1 hs.2
  have hy := exit_image ht.1 ht.2
  exact (high_arg ht.1 hx hy hu).trans_lt (high_param hx hs.1 ht.1 hst)

/-- Existence and uniqueness on the same exit slab as the near-parabolic
shooting construction; p=3(k+2) corresponds to k≥4. -/
theorem unique_center_on_exit_slab (k : ℕ) (hk : 4 ≤ k) :
    ∃! t : ℝ, t ∈ exitSlab k ∧ (H t)^[k+2] 0 = 0 := by
  have ht1 : (1/100:ℝ) ∈ Icc 0 (1/100:ℝ) := ⟨by norm_num, le_rfl⟩
  have hreach : 19/50 ≤ track (1/100) k :=
    (show (19/50:ℝ) ≤ cap by norm_num [cap]).trans
      (track_four_at_endpoint.trans (flight_steps ht1 (by norm_num [mem_Icc,cap]) hk))
  obtain ⟨a,b,ha,hab,hb,hA,hB,hslab⟩ := exists_crossing_Icc ht1.1
    (continuous_track k).continuousOn (show track 0 k ≤ 7/20 by linarith [parabolic_trap k])
    (by norm_num : (7/20:ℝ) < 19/50) hreach
  have sub {t : ℝ} (h : t ∈ Icc a b) : t ∈ exitSlab k :=
    ⟨⟨ha.trans h.1,h.2.trans hb⟩,hslab h⟩
  have hsA := sub (left_mem_Icc.mpr hab.le)
  have hsB := sub (right_mem_Icc.mpr hab.le)
  have hleft : 0 ≤ (H a)^[k+2] 0 := by
    rw [return_on_slab hsA, hA]
    linarith [(window_walls hsA.1).2.2.1]
  have hright : (H b)^[k+2] 0 ≤ 0 := by
    rw [return_on_slab hsB, hB]
    exact (window_walls hsB.1).2.2.2.1.le
  have hc : Continuous (fun t : ℝ => (H t)^[k+2] 0) :=
    continuous_H_iter _ continuous_id continuous_const
  obtain ⟨t, ht, hzero⟩ := intermediate_value_Icc' hab.le hc.continuousOn ⟨hright,hleft⟩
  refine ⟨t, ⟨sub ht,hzero⟩, ?_⟩
  intro s hs
  exact (exit_return_strictAnti k).injOn hs.1 (sub ht) (hs.2.trans hzero.symm)

/-- The continuous clipped coordinate describes the original critical orbit
on precisely this exit itinerary. -/
theorem exitSlab_iff_orbit {t : ℝ} {k : ℕ} : t ∈ exitSlab k ↔
    t ∈ Icc 0 (1/100:ℝ) ∧ (∀ j ≤ k, (H t)^[j] 0 ∈ Icc 0 cap) ∧
    (H t)^[k] 0 ∈ Icc (7/20:ℝ) (19/50) := by
  constructor
  · intro hs
    have hlast : track t k < cap := by unfold cap; linarith [hs.2.2]
    have h j (hj : j ≤ k) : (H t)^[j] 0 = track t j :=
      track_true hs.1 (lt_of_le_of_lt
        (flight_steps hs.1 (show (0:ℝ) ∈ Icc 0 cap by norm_num [mem_Icc,cap]) hj) hlast)
    refine ⟨hs.1, fun j hj => ?_, ?_⟩
    · rw [h j hj]; exact track_mem hs.1 j
    · rw [h k le_rfl]; exact hs.2
  · rintro ⟨ht,horbit,hexit⟩
    have h : ∀ j ≤ k, track t j = (H t)^[j] 0 := by
      intro j
      induction j with
      | zero => intro _; rfl
      | succ j ih =>
        intro hj
        change min cap (H t (track t j)) = _
        rw [ih (by omega), ← Function.iterate_succ_apply' (H t) j 0]
        exact min_eq_right (horbit (j+1) hj).2
    exact ⟨ht, h k le_rfl ▸ hexit⟩

/-- A center characterized exclusively by the itinerary of the actual
polynomial third return, without clipping. -/
theorem unique_center_on_exit_itinerary (k : ℕ) (hk : 4 ≤ k) :
    ∃! t : ℝ, (t ∈ Icc 0 (1/100:ℝ) ∧ (∀ j ≤ k, (H t)^[j] 0 ∈ Icc 0 cap) ∧
    (H t)^[k] 0 ∈ Icc (7/20:ℝ) (19/50)) ∧ (H t)^[k+2] 0 = 0 := by
  simpa only [← exitSlab_iff_orbit] using unique_center_on_exit_slab k hk

/-- All parameters on a later exit slab lie strictly to the left of every
parameter on an earlier slab. This orders both tips and centers by itinerary. -/
theorem exit_slabs_ordered {k l : ℕ} (hkl : k < l) {s t : ℝ}
    (hs : s ∈ exitSlab k) (ht : t ∈ exitSlab l) : t < s := by
  by_contra! hst
  have he := (exit_image hs.1 hs.2).1
  have hnext : track s (k+1) = cap := by
    change min cap (H s (track s k)) = cap
    apply min_eq_left
    unfold cap
    linarith
  have hz : (0:ℝ) ∈ Icc 0 cap := by norm_num [mem_Icc,cap]
  have h := (flight_steps hs.1 hz (show k+1 ≤ l by omega)).trans
    (track_monotone_parameter l hs.1 ht.1 hst)
  change track s (k+1) ≤ track t l at h
  rw [hnext] at h
  unfold cap at h
  linarith [ht.2.2]

/-- The center closes for the first time at precisely 3(k+2) iterates of
the original quadratic polynomial, including the two intermediate phases. -/
theorem exit_center_minimalPeriod {t : ℝ} {k : ℕ} (hs : t ∈ exitSlab k)
    (hc : (H t)^[k+2] 0 = 0) :
    minimalPeriod (quad (-7/4+t)) 0 = 3*(k+2) := by
  have ht := hs.1
  have htpos : 0 < t := by
    have h : t ≠ 0 := by
      rintro rfl
      linarith [parabolic_trap k, hs.2.1]
    exact lt_of_le_of_ne ht.1 h.symm
  obtain ⟨_,hchannel,hexit⟩ := exitSlab_iff_orbit.mp hs
  have hlast : (H t)^[k+1] 0 ∈ Icc (47/50:ℝ) (11/10) := by
    rw [Function.iterate_succ_apply']
    exact exit_image ht hexit
  let f := quad (-7/4+t)
  let N := 3*(k+2)
  have hN : 0 < N := by dsimp [N]; omega
  have hp : IsPeriodicPt f N 0 := by
    change (quad (-7/4+t))^[3*(k+2)] 0 = 0
    simpa only [neg_zero, hc] using reflected_blocks t 0 (k+2)
  have hmin : ∀ n, 0 < n → n < N → f^[n] 0 ≠ 0 := by
    intro n hn hn'
    let j := n/3
    let r := n%3
    have hr : r < 3 := Nat.mod_lt _ (by decide)
    have hnr : n = r+3*j := (Nat.mod_add_div n 3).symm
    have hj : j ≤ k+1 := by dsimp [N] at hn'; omega
    have hblock : f^[3*j] 0 = -((H t)^[j] 0) := by
      simpa only [neg_zero,f] using reflected_blocks t 0 j
    rw [hnr,Function.iterate_add_apply,hblock]
    let z := (H t)^[j] 0
    change f^[r] (-z) ≠ 0
    rcases lt_or_eq_of_le hj with hj | hj
    · have hzk := hchannel j (by omega)
      have hsep := small_block_separation ht hzk
      rcases (show r = 0 ∨ r = 1 ∨ r = 2 by omega) with h | h | h
      · have hjpos : 0 < j := by omega
        obtain ⟨i,hi⟩ := Nat.exists_eq_succ_of_ne_zero hjpos.ne'
        have hpre := hchannel i (by omega)
        have hstep := channel_drift ht hpre
        have hz : 0 < z := by
          dsimp [z]
          rw [hi,Function.iterate_succ_apply']
          linarith [hpre.1]
        rw [h]; change -z ≠ 0; linarith
      · rw [h]; change quad _ (-z) ≠ 0; exact ne_of_lt (hsep.1.trans (by norm_num))
      · rw [h]; exact ne_of_gt ((by norm_num : (0:ℝ)<1/10).trans hsep.2)
    · have hband : z ∈ Icc (9/10:ℝ) (6/5) := by
        dsimp [z]; rw [hj]
        exact ⟨by linarith [hlast.1],by linarith [hlast.2]⟩
      have hsep := exit_block_separation ht hband
      rcases (show r = 0 ∨ r = 1 ∨ r = 2 by omega) with h | h | h
      · rw [h]; change -z ≠ 0; linarith [hband.1]
      · rw [h]; exact ne_of_lt (hsep.1.trans (by norm_num))
      · rw [h]; exact ne_of_lt (hsep.2.trans (by norm_num))
  change minimalPeriod f 0 = N
  apply le_antisymm (hp.minimalPeriod_le hN)
  by_contra! h
  exact hmin _ (hp.minimalPeriod_pos hN) h (isPeriodicPt_minimalPeriod f 0)

#print axioms exit_center_minimalPeriod
#print axioms exit_slabs_ordered
#print axioms unique_center_on_exit_slab
#print axioms unique_center_on_exit_itinerary

end
end LoopsParabolic

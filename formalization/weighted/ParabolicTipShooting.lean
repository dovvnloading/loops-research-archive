import ParabolicTipWindow
import ParabolicShooting

/-!
# Noncentral critical orbit collisions at the period-three parabolic channel

Shoot the critical orbit through a fixed exit window. Shoot a second orbit
from the first return, retaining its positive distance from the center by
dividing the collision equation by its central factor.
-/
namespace LoopsParabolic
open Set Function Filter Topology
noncomputable section

private def sec (t x y : ℝ) : ℝ :=
  let u := 7/4-t
  (u-x^2+(u-y^2))*((u-x^2)^2-u+((u-y^2)^2-u))

private theorem diff (t x y : ℝ) :
    H t x-H t y = (x^2-y^2)*sec t x y := by unfold H sec; ring

private def iterSec (t x y : ℝ) : ℕ → ℝ
  | 0 => 1
  | n+1 =>
    let a := (H t)^[n] x
    let b := (H t)^[n] y
    iterSec t x y n * (a+b) * sec t a b

private theorem iter_diff (t x y : ℝ) (n : ℕ) :
    (H t)^[n] x - (H t)^[n] y = (x-y)*iterSec t x y n := by
  induction n with
  | zero => simp [iterSec]
  | succ n ih =>
    simp only [Function.iterate_succ_apply', iterSec, diff]
    rw [sq_sub_sq, ih]
    ring

@[fun_prop] private theorem continuous_sec {f g h : ℝ → ℝ}
    (hf : Continuous f) (hg : Continuous g) (hh : Continuous h) :
    Continuous (fun t => sec (f t) (g t) (h t)) := by unfold sec; fun_prop

@[fun_prop] private theorem continuous_iterSec (n : ℕ) {f g h : ℝ → ℝ}
    (hf : Continuous f) (hg : Continuous g) (hh : Continuous h) :
    Continuous (fun t => iterSec (f t) (g t) (h t) n) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih => simp only [iterSec]; fun_prop

private def reduced (k : ℕ) (t z : ℝ) : ℝ :=
  2 + z * sec t z 0 * iterSec t (H t z) (H t 0) (k+1)

/-- The continuous quotient takes value two at a superattracting center. -/
private theorem reduced_eq (k : ℕ) (t z : ℝ) (hz : (H t)^[k+2] 0 = z) :
    z * reduced k t z = (H t)^[k+2] z + z := by
  have h := iter_diff t (H t z) (H t 0) (k+1)
  rw [← Function.iterate_succ_apply, ← Function.iterate_succ_apply, hz, diff] at h
  simp only [zero_pow (by decide : 2 ≠ 0), sub_zero] at h
  unfold reduced
  linarith only [h, show z*(2+z*sec t z 0*iterSec t (H t z) (H t 0) (k+1))
    = 2*z + (z^2*sec t z 0)*iterSec t (H t z) (H t 0) (k+1) by ring]

/-- Records both flights through the channel. In reflected coordinates, the
first return e is positive and the second sends e to -e. -/
structure Shot (k : ℕ) (t e : ℝ) : Prop where
  t_pos : 0 < t
  t_small : t ≤ 1/100
  e_pos : 0 < e
  e_small : e ≤ 1/10
  critical : (H t)^[k+2] 0 = e
  collision : (H t)^[k+2] e = -e
  corridor : ∀ j ≤ k, (H t)^[j] e ∈ Icc e cap
  gap : e < H t 0
  first_corridor : ∀ j ≤ k, (H t)^[j] 0 ∈ Icc 0 cap
  first_exit : (H t)^[k] 0 ∈ Icc (7/20) (19/50)
  center_right : ∃ s ∈ Ioc t (1/100 : ℝ), (H s)^[k+2] 0 = 0 ∧
    (∀ j ≤ k, (H s)^[j] 0 ∈ Icc 0 cap) ∧ (H s)^[k] 0 ∈ Icc (7/20) (19/50)
  penultimate : (H t)^[k+1] e ∈ Icc (9/10) (6/5)

/-- The shooting interval has a critical center at its right endpoint. -/
private theorem shoot {d : ℝ} {k : ℕ} (hd : d ∈ Ioc 0 (1/100 : ℝ))
    (hreach : 19/50 ≤ track d k) :
    ∃ t ∈ Ioc 0 d, ∃ e, Shot k t e := by
  have ht' {t : ℝ} (h : t ∈ Icc 0 d) : t ∈ Icc 0 (1/100 : ℝ) :=
    ⟨h.1,h.2.trans hd.2⟩
  have hw (t : ℝ) (h : t ∈ Icc 0 d) := window_walls (ht' h)
  obtain ⟨a,b,ha,hab,hb,hA,hB,htrack⟩ := exists_crossing_Icc hd.1.le
    (continuous_track k).continuousOn
    (show track 0 k ≤ 7/20 by linarith [parabolic_trap k])
    (by norm_num : (7/20:ℝ) < 19/50)
    hreach
  have sub {t : ℝ} (h : t ∈ Icc a b) : t ∈ Icc 0 d := ⟨ha.trans h.1, h.2.trans hb⟩
  let E := fun t => (H t)^[k+2] 0
  have hE : Continuous E := continuous_H_iter _ continuous_id continuous_const
  have hEval {t : ℝ} (h : t ∈ Icc a b) :
      E t = H t (H t (track t k)) := by
    have hv := track_true (ht' (sub h))
      (show track t k < cap by unfold cap; linarith [(htrack h).2])
    simp only [E, Function.iterate_succ_apply', hv]
  have ha' : a ∈ Icc a b := left_mem_Icc.mpr hab.le
  have hb' : b ∈ Icc a b := right_mem_Icc.mpr hab.le
  have hea : 1/10 < E a := by rw [hEval ha',hA]; exact (hw a (sub ha')).2.2.1
  have heb : E b < 0 := by rw [hEval hb',hB]; exact (hw b (sub hb')).2.2.2.1
  obtain ⟨l,r,hal,hlr,hrb,hL,hR,hEslab⟩ := exists_descending_crossing_Icc
    hab.le hE.continuousOn hea.le (by norm_num : (0:ℝ) < 1/10) heb.le
  have lsub {t : ℝ} (h : t ∈ Icc l r) : t ∈ Icc a b :=
    ⟨hal.trans h.1,h.2.trans hrb⟩
  have rzero : E r = 0 := hR
  have bounds {t : ℝ} (h : t ∈ Icc l r) : E t ∈ Icc 0 (1/10) := hEslab h
  have hl' : l ∈ Icc l r := left_mem_Icc.mpr hlr.le
  have hr' : r ∈ Icc l r := right_mem_Icc.mpr hlr.le
  have hwall {t : ℝ} (h : t ∈ Icc l r) := hw t (sub (lsub h))
  have hzcap {t : ℝ} (h : t ∈ Icc l r) : E t ∈ Icc 0 cap :=
    ⟨(bounds h).1, by unfold cap; linarith [(bounds h).2]⟩
  have hdiff : Continuous (fun t => E t-H t 0) := by fun_prop
  obtain ⟨m,hm,hem⟩ := intermediate_value_Icc' hlr.le hdiff.continuousOn
    (show (0:ℝ) ∈ Icc (E r-H r 0) (E l-H l 0) by
      constructor
      · linarith [(hwall hr').1]
      · linarith [(hwall hl').2.1])
  let W := fun t => flight t (E t) k
  have hW : Continuous W := continuous_flight _ continuous_id hE
  have hwm : W m = cap := by
    have he : E m = H m 0 := by linarith
    have hse : E m = min cap (H m 0) := by rw [← he, min_eq_right (hzcap hm).2]
    dsimp [W]
    rw [hse, flight_shift]
    change min cap (H m (track m k)) = cap
    apply min_eq_left
    have hmon := channel_mono (ht' (sub (lsub hm)))
      (show (7/20:ℝ) ∈ Icc 0 cap by norm_num [cap])
      (track_mem (ht' (sub (lsub hm))) k) (htrack (lsub hm)).1
    unfold cap
    linarith [(hwall hm).2.2.2.2.2.1]
  have hwr : W r < 39/100 := by
    dsimp [W]; rw [rzero]
    change track r k < _
    linarith [(htrack (lsub hr')).2]
  obtain ⟨s,hs,hWs,hstop⟩ := exists_last_upper_hit (f := W) hm.2
    hW.continuousOn (show 39/100 ≤ W m by rw [hwm]; norm_num [cap]) hwr
  have srsub {t : ℝ} (h : t ∈ Icc s r) : t ∈ Icc l r :=
    ⟨hm.1.trans (hs.1.trans h.1),h.2⟩
  have Wtrue {t : ℝ} (h : t ∈ Icc s r) : (H t)^[k] (E t) = W t := by
    apply flight_true (ht' (sub (lsub (srsub h)))) (hzcap (srsub h))
    change W t < cap
    unfold cap
    linarith [hstop t h]
  let Q := fun t => reduced k t (E t)
  have hQ : Continuous Q := by dsimp [Q,reduced]; fun_prop
  have hs' : s ∈ Icc s r := left_mem_Icc.mpr hs.2
  have neg : Q s < 0 := by
    have eqn := reduced_eq k s (E s) rfl
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', Wtrue hs', hWs] at eqn
    have negprod : E s*Q s < 0 := by
      dsimp [Q]; linarith [(hwall (srsub hs')).2.2.2.2.1, (bounds (srsub hs')).2]
    by_contra! h
    exact (not_lt_of_ge (mul_nonneg (bounds (srsub hs')).1 h)) negprod
  have pos : Q r = 2 := by simp [Q,reduced,rzero]
  obtain ⟨t,ht,hQt⟩ := intermediate_value_Icc hs.2 hQ.continuousOn
    (show (0:ℝ) ∈ Icc (Q s) (Q r) by constructor <;> linarith)
  have htr := srsub ht
  have htab := lsub htr
  have htd := sub htab
  have htt := ht' htd
  have htpos : 0 < t := by
    rcases htd.1.eq_or_lt with h | h
    · subst t; linarith [(htrack htab).1, parabolic_trap k]
    · exact h
  have hepos : 0 < E t := by
    refine lt_of_le_of_ne (bounds htr).1 ?_
    intro hz
    simp [Q,reduced,hz.symm] at hQt
  have hcollision : (H t)^[k+2] (E t) = -E t := by
    have heq := reduced_eq k t (E t) rfl
    change reduced k t (E t) = 0 at hQt
    rw [hQt,mul_zero] at heq
    linarith
  have endbound : W t ≤ 39/100 := hstop t ht
  have initial := hzcap htr
  have inc := flight_steps htt initial
  have interior {j : ℕ} (hj : j ≤ k) : (H t)^[j] (E t) = flight t (E t) j := by
    apply flight_true htt initial
    have hj' := inc hj
    change _ ≤ W t at hj'
    unfold cap; linarith
  have first {v : ℝ} (hv : v ∈ Icc a b) :
      (∀ j ≤ k, (H v)^[j] 0 ∈ Icc 0 cap) ∧ (H v)^[k] 0 ∈ Icc (7/20) (19/50) := by
    have hvt := ht' (sub hv)
    have hlast : track v k < cap := by unfold cap; linarith [(htrack hv).2]
    refine ⟨?_, by rw [track_true hvt hlast]; exact htrack hv⟩
    intro j hj
    rw [track_true hvt (lt_of_le_of_lt
      (flight_steps hvt (show (0:ℝ) ∈ Icc 0 cap by norm_num [cap]) hj) hlast)]
    exact track_mem hvt j
  have hcenter : t < r := lt_of_le_of_ne ht.2 (by
    intro he; rw [he,rzero] at hepos; exact lt_irrefl _ hepos)
  refine ⟨t,⟨htpos,htd.2⟩, E t, htpos, htt.2, hepos,(bounds htr).2, rfl,
    hcollision, ?_, ?_, (first htab).1, (first htab).2,
    ⟨r, ⟨hcenter,(ht' (sub (lsub hr'))).2⟩,rzero,first (lsub hr')⟩, ?_⟩
  · intro j hj
    rw [interior hj]
    exact ⟨inc (Nat.zero_le j),(flight_mem htt initial j).2⟩
  · by_contra! h
    have hzero : H t 0 ∈ Icc 0 cap := ⟨(hwall htr).1.le,h.trans initial.2⟩
    have hc := flight_compare htt hzero initial h k
    have hsft := flight_shift t 0 k
    rw [min_eq_right hzero.2] at hsft
    rw [hsft] at hc
    change min cap (H t (track t k)) ≤ W t at hc
    have lower := channel_mono htt (show (7/20:ℝ) ∈ Icc 0 cap by norm_num [cap])
      (track_mem htt k) (htrack htab).1
    rw [min_eq_left (by unfold cap; linarith [(hwall htr).2.2.2.2.2.1])] at hc
    unfold cap at hc; linarith
  · rw [Function.iterate_succ_apply', Wtrue ht]
    have comp := flight_compare htt
      (show (0:ℝ) ∈ Icc 0 cap by norm_num [cap]) initial initial.1 k
    have hlo : 7/20 ≤ W t := (htrack htab).1.trans comp
    have hwm' := flight_mem htt initial k
    have mlo := channel_mono htt (show (7/20:ℝ) ∈ Icc 0 cap by norm_num [cap]) hwm' hlo
    have mhi := channel_mono htt hwm' (show (39/100:ℝ) ∈ Icc 0 cap by norm_num [cap]) endbound
    exact ⟨(hwall htr).2.2.2.2.2.1.le.trans mlo, mhi.trans (hwall htr).2.2.2.2.2.2.le⟩

/-- The first exit occurs for every k ≥ 4, corresponding to physical
return lengths 18, 21, 24, ... . -/
theorem shot_exists (k : ℕ) (hk : 4 ≤ k) : ∃ t e, Shot k t e := by
  have ht : (1/100:ℝ) ∈ Icc 0 (1/100) := by constructor <;> norm_num
  have h := track_four_at_endpoint.trans (flight_steps ht
    (show (0:ℝ) ∈ Icc 0 cap by norm_num [cap]) hk)
  obtain ⟨t,_,e,hs⟩ := shoot (k := k) (d := 1/100) (by constructor <;> norm_num)
    ((by norm_num [cap] : (19/50:ℝ) ≤ cap).trans h)
  exact ⟨t,e,hs⟩

theorem Shot.first_rate_bound {k : ℕ} {t e : ℝ} (hs : Shot k t e) :
    (k:ℝ)*t ≤ 19/25 := by
  have drift := fun j (hj : j < k) => channel_drift
    ⟨hs.t_pos.le,hs.t_small⟩ (hs.first_corridor j hj.le)
  have hl : ∀ j ≤ k, (j:ℝ)*t/2 ≤ (H t)^[j] 0 := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      intro hj
      rw [Function.iterate_succ_apply']
      push_cast
      linarith [ih (by omega), drift j (by omega)]
  linarith [hl k le_rfl,hs.first_exit.2]

end
end LoopsParabolic

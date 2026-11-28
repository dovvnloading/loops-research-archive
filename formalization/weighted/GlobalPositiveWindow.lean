import NearTwoShooting

/-!
# Global localization of the positive critical itinerary

The positive inverse branch is controlled on the entire real parameter
interval [-2,-1].  Its parameter Lipschitz constant is at most one, which
still makes the actual critical shooting function strictly decreasing.
Consequently a nonnegative critical itinerary of length p forces its
parameter into the exponentially small interval already constructed near
-2.  The small parameter interval is a conclusion, not an assumption.
-/

namespace GlobalPositiveWindow

open Set Function
open NearTwoInverse NearTwoShooting LimitingCrestQuadraticReturn

noncomputable section

theorem B_bounds {c x : ℝ} (hc : c ∈ Icc (-2 : ℝ) (-1))
    (hx : x ∈ Icc (0 : ℝ) 2) : B c x ∈ Icc (1 : ℝ) 2 := by
  have hs := B_sq (show c ≤ 0 by linarith [hc.2]) hx.1
  have hn := B_nonneg c x
  constructor <;> nlinarith [hc.1, hc.2, hx.1, hx.2]

theorem back_bounds {c d : ℝ} (hc : c ∈ Icc (-2 : ℝ) (-1))
    (hd : d ∈ Icc (0 : ℝ) 2) (n : ℕ) :
    back c n d ∈ Icc (0 : ℝ) 2 := by
  induction n with
  | zero => exact hd
  | succ n ih =>
    rw [back_succ]
    have h := B_bounds hc ih
    exact ⟨by linarith [h.1], h.2⟩

private theorem branch_difference_bound {c c' x y : ℝ}
    (hc : c ∈ Icc (-2 : ℝ) (-1)) (hc' : c' ∈ Icc (-2 : ℝ) (-1))
    (hx : x ∈ Icc (0 : ℝ) 2) (hy : y ∈ Icc (0 : ℝ) 2) :
    (2 : ℝ) * |B c x - B c' y| ≤ |x-y| + |c-c'| := by
  have hA := B_bounds hc hx
  have hB := B_bounds hc' hy
  have hsA := B_sq (show c ≤ 0 by linarith [hc.2]) hx.1
  have hsB := B_sq (show c' ≤ 0 by linarith [hc'.2]) hy.1
  have hid : (B c x-B c' y)*(B c x+B c' y) = (x-y)-(c-c') := by
    nlinarith [hsA, hsB]
  have habs : |B c x-B c' y| * (B c x+B c' y) = |(x-y)-(c-c')| := by
    rw [← abs_of_nonneg (show 0 ≤ B c x+B c' y by linarith [hA.1, hB.1]),
      ← abs_mul, hid]
  have htri := abs_sub (x-y) (c-c')
  have hmul := mul_le_mul_of_nonneg_left
    (show (2 : ℝ) ≤ B c x+B c' y by linarith [hA.1, hB.1])
    (abs_nonneg (B c x-B c' y))
  nlinarith

theorem back_parameter_lipschitz {c c' d : ℝ}
    (hc : c ∈ Icc (-2 : ℝ) (-1)) (hc' : c' ∈ Icc (-2 : ℝ) (-1))
    (hd : d ∈ Icc (0 : ℝ) 2) (n : ℕ) :
    |back c n d-back c' n d| ≤ |c-c'| := by
  induction n with
  | zero => simp only [back_zero, sub_self, abs_zero]; exact abs_nonneg _
  | succ n ih =>
    have h := branch_difference_bound hc hc' (back_bounds hc hd n) (back_bounds hc' hd n)
    rw [back_succ, back_succ]
    linarith

theorem shooting_strictAnti (n : ℕ) {d : ℝ}
    (hd : d ∈ Icc (0 : ℝ) 2) :
    StrictAntiOn (shooting n d) (Icc (-2 : ℝ) (-1)) := by
  intro a ha b hb hab
  have h := back_parameter_lipschitz ha hb hd n
  have he : |a-b| = b-a := by rw [abs_of_neg (sub_neg.mpr hab)]; ring
  rw [he] at h
  have hdiff := (le_abs_self (back a n d-back b n d)).trans h
  have hs : a+b+2 < 0 := by linarith [hb.2]
  have hm := mul_neg_of_neg_of_pos hs (sub_pos.mpr hab)
  dsimp [shooting]
  nlinarith only [hdiff, hm]

/-- A nonnegative zero-terminal shooting value anywhere on [-2,-1]
forces the same small parameter window as the local shooting chart. -/
theorem shooting_nonneg_parameter_upper {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : c ∈ Icc (-2 : ℝ) (-1))
    (hs : 0 ≤ shooting (p-2) 0 c) :
    c < -2 + 20*scale p := by
  have hq0 := scale_pos p
  have hq := scale_small hp
  have hright : -2 + 20*scale p ∈ Icc (-2 : ℝ) (-1) := by
    constructor <;> linarith
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) (12*scale p) :=
    ⟨le_rfl, by positivity⟩
  have hneg := NearTwoShooting.shooting_right_neg hp h0
  by_contra! h
  have horder := (shooting_strictAnti (p-2)
    (show (0 : ℝ) ∈ Icc (0 : ℝ) 2 by norm_num)).antitoneOn hright hc h
  linarith

/-- The only orbit hypothesis is that the literal critical iterates from
time 2 through time p are nonnegative.  No terminal-size or near-endpoint
parameter estimate is assumed. -/
theorem nonnegative_itinerary_parameter_upper {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : c ∈ Icc (-2 : ℝ) (-1))
    (hit : ∀ j, 2 ≤ j → j ≤ p → 0 ≤ criticalValue c j) :
    c < -2 + 20*scale p := by
  have hp2 : p-2+2 = p := by omega
  have hs := NearTwoShooting.forward_orbit_shooting (c := c) (n := p-2) (by
    intro j hj
    exact hit (j+2) (by omega) (by omega))
  rw [hp2] at hs
  have hd : 0 ≤ criticalValue c p := hit p (by omega) le_rfl
  have hback := back_mono_initial c (p-2) hd
  apply shooting_nonneg_parameter_upper hp hc
  dsimp [shooting] at hs ⊢
  linarith only [hs, hback]

end

end GlobalPositiveWindow

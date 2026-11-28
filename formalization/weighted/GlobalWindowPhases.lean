import GlobalWindowChart
import GlobalWindowLocalization

/-!
# Disjoint physical phases of globally localized restrictive returns

The full source interval has one negative image and then strictly ordered
positive images.  Their separation is derived from the quantitative
localization and the literal quadratic itinerary; disjointness of the
intermediate images is not an additional assumption.
-/

namespace GlobalRestrictiveWindow

open Set Function
open NearTwoInverse NearTwoShooting LimitingCrestQuadraticReturn

noncomputable section

private theorem source_square_le {c x : ℝ} {p : ℕ}
    (hx : x ∈ returnInterval c p) : x^2 ≤ (criticalValue c p)^2 := by
  have hm := mul_nonneg (sub_nonneg.mpr hx.2)
    (show 0 ≤ criticalValue c p+x by linarith [hx.1])
  nlinarith only [hm]

/-- The second critical value lies strictly below the absolute value
of the first endpoint image.  This is the initial gap that orders all
positive phases. -/
theorem PositiveRestrictiveReturn.initial_phase_gap {c : ℝ} {p : ℕ}
    (hp : 17 ≤ p) (h : PositiveRestrictiveReturn c p) :
    criticalValue c 2 < -c-(criticalValue c p)^2 := by
  have hpar := h.sharp_parameter_bounds hp
  have hd := h.return_scale hp
  have hq := scale_small hp
  have hq0 := scale_pos p
  have hpar0 : 0 ≤ c+2 := by linarith [h.parameter_band.1]
  have hsqc := mul_le_mul hpar.2.le hpar.2.le hpar0
    (show 0 ≤ 16*scale p by positivity)
  have hsqd := mul_le_mul hd.le hd.le h.return_pos.le
    (show 0 ≤ 14*scale p by positivity)
  have hqsq := mul_le_mul_of_nonneg_left hq hq0.le
  rw [criticalValue_two]
  nlinarith only [hpar.1, hsqc, hsqd, hqsq, hq0]

/-- The entire first image lies below the original source interval. -/
theorem PositiveRestrictiveReturn.first_phase_below {c x : ℝ} {p : ℕ}
    (hp : 17 ≤ p) (h : PositiveRestrictiveReturn c p)
    (hx : x ∈ returnInterval c p) : realMap c x < -criticalValue c p := by
  have hd := h.return_scale hp
  have hq := scale_small hp
  have hsmall : criticalValue c p < 1/10 := by linarith
  have hsq := mul_le_mul hsmall.le hsmall.le h.return_pos.le
    (show (0 : ℝ) ≤ 1/10 by norm_num)
  have hx2 := source_square_le hx
  dsimp [realMap]
  nlinarith only [hsq, hx2, hsmall, h.parameter_band.2]

/-- On every positive phase the endpoint gives the minimum and the
critical point gives the maximum, uniformly over the full source interval. -/
theorem PositiveRestrictiveReturn.phase_endpoint_bounds {c x : ℝ} {p j : ℕ}
    (h : PositiveRestrictiveReturn c p) (hj : 2 ≤ j) (hjp : j < p)
    (hx : x ∈ returnInterval c p) :
    (realMap c)^[j] (criticalValue c p) ≤ (realMap c)^[j] x ∧
      (realMap c)^[j] x ≤ (realMap c)^[j] 0 := by
  have bounds : ∀ k : ℕ, k+2 < p →
      (realMap c)^[k+2] (criticalValue c p) ≤ (realMap c)^[k+2] x ∧
        (realMap c)^[k+2] x ≤ (realMap c)^[k+2] 0 := by
    intro k
    induction k with
    | zero =>
      intro _
      have hnx := h.negative_first x hx
      have hnd := h.negative_first (criticalValue c p) h.right_mem
      have hcx : c ≤ realMap c x := by dsimp [realMap]; nlinarith only [sq_nonneg x]
      have hxd : realMap c x ≤ realMap c (criticalValue c p) := by
        dsimp [realMap]
        linarith only [source_square_le hx]
      have hlo := pow_le_pow_left₀ (show 0 ≤ -realMap c (criticalValue c p) by linarith)
        (show -realMap c (criticalValue c p) ≤ -realMap c x by linarith) 2
      have hup := pow_le_pow_left₀ (show 0 ≤ -realMap c x by linarith)
        (show -realMap c x ≤ -c by linarith) 2
      change realMap c (realMap c (criticalValue c p)) ≤ realMap c (realMap c x) ∧
        realMap c (realMap c x) ≤ realMap c (realMap c 0)
      have hzero : realMap c 0 = c := by simp [realMap]
      rw [hzero]
      dsimp [realMap] at hlo hup ⊢
      constructor <;> nlinarith only [hlo, hup]
    | succ k ih =>
      intro hkp
      have hs := ih (by omega)
      have hdp := h.positive_phases (k+2) (by omega) (by omega)
        (criticalValue c p) h.right_mem
      have hxp := h.positive_phases (k+2) (by omega) (by omega) x hx
      have hlo := pow_le_pow_left₀ hdp.le hs.1 2
      have hup := pow_le_pow_left₀ hxp.le hs.2 2
      rw [show k+1+2=(k+2)+1 by omega,
        Function.iterate_succ_apply' (realMap c) (k+2) (criticalValue c p),
        Function.iterate_succ_apply' (realMap c) (k+2) x,
        Function.iterate_succ_apply' (realMap c) (k+2) 0]
      change ((realMap c)^[k+2] (criticalValue c p))^2+c ≤
          ((realMap c)^[k+2] x)^2+c ∧
        ((realMap c)^[k+2] x)^2+c ≤ ((realMap c)^[k+2] 0)^2+c
      constructor <;> linarith only [hlo, hup]
  simpa only [Nat.sub_add_cancel hj] using bounds (j-2) (by omega)

private theorem endpoint_gap {c : ℝ} {p j : ℕ}
    (hp : 17 ≤ p) (h : PositiveRestrictiveReturn c p)
    (hj : 2 ≤ j) (hjp : j+1 < p) :
    (realMap c)^[j+1] 0 < (realMap c)^[j] (criticalValue c p) := by
  have gaps : ∀ k : ℕ, k+3 < p →
      (realMap c)^[k+3] 0 < (realMap c)^[k+2] (criticalValue c p) := by
    intro k
    induction k with
    | zero =>
      intro _
      have hg := h.initial_phase_gap hp
      have hc2 := h.critical_prefix 2 (by omega) (by omega)
      have hm := mul_pos
        (show 0 < (-c-(criticalValue c p)^2)-criticalValue c 2 by linarith)
        (show 0 < (-c-(criticalValue c p)^2)+criticalValue c 2 by linarith)
      change realMap c (criticalValue c 2) < realMap c (realMap c (criticalValue c p))
      change (criticalValue c 2)^2+c < ((criticalValue c p)^2+c)^2+c
      nlinarith only [hm]
    | succ k ih =>
      intro hkp
      have hg := ih (by omega)
      have hpos := h.positive_phases (k+3) (by omega) (by omega) 0 h.zero_mem
      have hm := mul_pos (sub_pos.mpr hg)
        (show 0 < (realMap c)^[k+2] (criticalValue c p)+(realMap c)^[k+3] 0 by linarith)
      rw [show k+1+3=(k+3)+1 by omega, show k+1+2=(k+2)+1 by omega,
        Function.iterate_succ_apply' (realMap c) (k+3) 0,
        Function.iterate_succ_apply' (realMap c) (k+2) (criticalValue c p)]
      change ((realMap c)^[k+3] 0)^2+c <
        ((realMap c)^[k+2] (criticalValue c p))^2+c
      nlinarith only [hm]
  simpa only [show j-2+3=j+1 by omega, Nat.sub_add_cancel hj] using
    gaps (j-2) (by omega)

/-- Every point of a later adjacent positive phase lies strictly below
every point of the preceding phase. -/
theorem PositiveRestrictiveReturn.adjacent_phases_separated {c z w : ℝ} {p j : ℕ}
    (hp : 17 ≤ p) (h : PositiveRestrictiveReturn c p)
    (hj : 2 ≤ j) (hjp : j+1 < p)
    (hz : z ∈ returnInterval c p) (hw : w ∈ returnInterval c p) :
    (realMap c)^[j+1] z < (realMap c)^[j] w := by
  have hu := (h.phase_endpoint_bounds (by omega : 2 ≤ j+1) hjp hz).2
  have hl := (h.phase_endpoint_bounds hj (by omega) hw).1
  exact hu.trans_lt ((endpoint_gap hp h hj hjp).trans_le hl)

/-- Every positive phase is strictly above the source interval, including
the last phase whose next iterate may have either sign. -/
theorem PositiveRestrictiveReturn.positive_phase_above {c x : ℝ} {p j : ℕ}
    (hp : 17 ≤ p) (h : PositiveRestrictiveReturn c p)
    (hj : 2 ≤ j) (hjp : j < p) (hx : x ∈ returnInterval c p) :
    criticalValue c p < (realMap c)^[j] x := by
  have hpos := h.positive_phases j hj hjp x hx
  by_contra! hle
  have hy : (realMap c)^[j] x ∈ returnInterval c p :=
    ⟨by linarith [h.return_pos], hle⟩
  have hnegative := h.first_phase_below hp hy
  by_cases hlast : j+1=p
  · have he : (realMap c)^[j+1] x ∈ returnInterval c p := by
      rw [hlast]
      exact h.invariant hx
    rw [Function.iterate_succ_apply'] at he
    linarith only [he.1, hnegative]
  · have hnext := h.positive_phases (j+1) (by omega) (by omega) x hx
    rw [Function.iterate_succ_apply'] at hnext
    linarith only [hnext, hnegative, h.return_pos]

/-- The order of arbitrary positive phases follows the reverse of time. -/
theorem PositiveRestrictiveReturn.positive_phases_separated {c z w : ℝ} {p i j : ℕ}
    (hp : 17 ≤ p) (h : PositiveRestrictiveReturn c p)
    (hi : 2 ≤ i) (hij : i < j) (hjp : j < p)
    (hz : z ∈ returnInterval c p) (hw : w ∈ returnInterval c p) :
    (realMap c)^[j] z < (realMap c)^[i] w := by
  have separated : ∀ k : ℕ, i+1 ≤ k → k < p →
      ∀ v ∈ returnInterval c p, (realMap c)^[k] v < (realMap c)^[i] w := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base =>
      intro hkp v hv
      exact h.adjacent_phases_separated hp hi hkp hv hw
    | succ k hk ih =>
      intro hkp v hv
      exact (h.adjacent_phases_separated hp (by omega) hkp hv h.zero_mem).trans
        (ih (by omega) 0 h.zero_mem)
  exact separated j (by omega) hjp z hz

private theorem ordered_images_disjoint {c : ℝ} {p i j : ℕ}
    (hp : 17 ≤ p) (h : PositiveRestrictiveReturn c p)
    (hij : i < j) (hjp : j < p) :
    Disjoint (((realMap c)^[i]) '' returnInterval c p)
      (((realMap c)^[j]) '' returnInterval c p) := by
  apply Set.disjoint_left.mpr
  intro a ha hb
  rcases ha with ⟨x, hx, hxa⟩
  rcases hb with ⟨y, hy, hya⟩
  have he : (realMap c)^[i] x = (realMap c)^[j] y := hxa.trans hya.symm
  by_cases hi0 : i=0
  · subst i
    simp only [Function.iterate_zero, id_eq] at he
    by_cases hj1 : j=1
    · subst j
      simp only [Function.iterate_one] at he
      have hn := h.first_phase_below hp hy
      linarith only [he, hx.1, hn]
    · have hpositive := h.positive_phase_above hp (by omega : 2 ≤ j) hjp hy
      linarith only [he, hx.2, hpositive]
  · by_cases hi1 : i=1
    · subst i
      simp only [Function.iterate_one] at he
      have hn := h.first_phase_below hp hx
      have hpositive := h.positive_phase_above hp (by omega : 2 ≤ j) hjp hy
      linarith only [he, hn, hpositive, h.return_pos]
    · have hs := h.positive_phases_separated hp (by omega : 2 ≤ i) hij hjp hy hx
      linarith only [he, hs]

/-- Distinct pre-return images of the entire physical source interval
are disjoint.  This property is deduced from the restrictive-return
conditions and quantitative localization. -/
theorem PositiveRestrictiveReturn.phase_images_disjoint {c : ℝ} {p i j : ℕ}
    (hp : 17 ≤ p) (h : PositiveRestrictiveReturn c p)
    (hip : i < p) (hjp : j < p) (hij : i ≠ j) :
    Disjoint (((realMap c)^[i]) '' returnInterval c p)
      (((realMap c)^[j]) '' returnInterval c p) := by
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact ordered_images_disjoint hp h hlt hjp
  · exact (ordered_images_disjoint hp h hgt hip).symm

end

end GlobalRestrictiveWindow

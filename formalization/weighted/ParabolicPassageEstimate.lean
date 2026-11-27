import ParabolicPassageCoefficients
import ParabolicPassageAngle
import ParabolicPassageFlight
import ParabolicPassageCuts

/-!
# A quantitative angular error bound for the actual polynomial flight

Only the central part of the true orbit is approximated by its quadratic
drift.  Every omitted step is counted by its actual telescoping drift.
-/

namespace LoopsParabolic

open Set Function
open scoped BigOperators

noncomputable section

theorem passage_scaled_time_bound {t : ℝ} {k : ℕ}
    (ht : 0 < t) (htmax : t ≤ 1 / 100)
    (stay : ∀ j ≤ k, (H t)^[j] 0 ∈ Icc 0 cap)
    (reached : 7 / 20 ≤ (H t)^[k] 0) :
    (k : ℝ) * Real.sqrt t ≤ 10 := by
  have hc := (channel_inverse_square ht htmax stay reached).2
  have he : ((k : ℝ) * Real.sqrt t) ^ 2 = (k : ℝ) ^ 2 * t := by
    rw [mul_pow, Real.sq_sqrt ht.le]
  have hp : 0 ≤ (k : ℝ) * Real.sqrt t := by positivity
  nlinarith

/-- The finite error separates the central quadratic approximation, the
outer elapsed time, and the two angular tails.  All orbit quantities are
the actual polynomial iterates. -/
theorem passage_quantitative_estimate {a ε η δ t : ℝ} {k : ℕ}
    (ha : a ∈ Icc (1 / 20 : ℝ) (3 / 50)) (root : cubic a = 0)
    (hε : 0 ≤ ε) (hεhalf : ε ≤ 1 / 2)
    (hη : 0 ≤ η) (hηε : η ≤ ε)
    (hδ : 0 < δ) (hδmax : δ ≤ 1 / 1000)
    (ht : 0 < t) (htmax : t ≤ 1 / 100) (htδ : t ≤ δ ^ 2)
    (hrelative : ∀ x : ℝ, |x| ≤ δ →
      (1 - η) * (passageA a * t + passageB a * x ^ 2) ≤
        H t (a + x) - (a + x) ∧
      H t (a + x) - (a + x) ≤
        (1 + η) * (passageA a * t + passageB a * x ^ 2))
    (hscale : 4 * δ * (passageB a * (1 + η)) ≤ ε)
    (stay : ∀ j ≤ k, (H t)^[j] 0 ∈ Icc 0 cap)
    (reached : 7 / 20 ≤ (H t)^[k] 0) :
    |7 * (k : ℝ) * Real.sqrt t - Real.pi| ≤
      280 * ε + (7 * cap / δ ^ 2) * Real.sqrt t +
        (Real.pi - 2 * Real.arctan (δ / (2 * passageScale a t))) := by
  let w : ℕ → ℝ := fun j => (H t)^[j] 0
  let s := passageScale a t
  let B := passageB a
  let u := B * s
  let θ : ℕ → ℝ := fun j => Real.arctan ((w j - a) / s)
  have hs : 0 < s := passage_scale_pos ha ht
  have hB : 0 < B := lt_of_lt_of_le (by norm_num) (passageB_ge_one ha)
  have hu : 0 ≤ u := mul_nonneg hB.le hs.le
  have hueq : u = 7 * Real.sqrt t := passage_scale_mul ha root ht.le
  have htw : t ∈ Icc 0 (1 / 100 : ℝ) := ⟨ht.le, htmax⟩
  obtain ⟨l, m, hlm, hmk, hl, hm, hcentral, hleft, hright⟩ :=
    passage_cut_indices ht htmax ha root hδ hδmax htδ stay reached
  have hlen : m - l ≤ k := by omega
  have hstep : ∀ j < k, (w j - a) ^ 2 ≤ w (j + 1) - w j := by
    intro j hj
    have hh := (channel_quadratic_step htw (stay j hj.le) ha root).1
    dsimp [w]
    rw [Function.iterate_succ_apply']
    linarith
  have hrem : ((k - (m - l) : ℕ) : ℝ) ≤ cap / δ ^ 2 := by
    apply (le_div_iff₀ (by positivity : 0 < δ ^ 2)).mpr
    have hh := passage_complement_time_budget w a δ k l m hδ.le hstep (by
      intro j hj hnot
      by_cases hjl : j < l
      · exact hleft j hjl
      · have hmj : m ≤ j := by
          simp only [Finset.mem_Ico] at hnot
          omega
        exact hright j hmj hj)
    have hend : w k - w 0 ≤ cap := by simpa [w] using (stay k le_rfl).2
    exact hh.trans hend
  have hangle : ∀ j ∈ Finset.Ico l m,
      |(θ (j + 1) - θ j) - u| ≤ (4 * ε) * u := by
    intro j hj
    have hjm := Finset.mem_Ico.mp hj
    obtain ⟨hx, hy⟩ := hcentral j hjm.1 hjm.2
    have hxy : w j - a < w (j + 1) - a := by
      have hd := channel_drift htw (stay j (by omega))
      dsimp [w]
      rw [Function.iterate_succ_apply']
      linarith
    have hr := hrelative (w j - a) hx
    have haadd : a + (w j - a) = w j := by ring
    rw [haadd] at hr
    have hquad := passage_scale_quadratic ha ht.le (w j - a)
    change B * (s ^ 2 + (w j - a) ^ 2) = _ at hquad
    have hsuc : w (j + 1) = H t (w j) :=
      Function.iterate_succ_apply' (H t) j 0
    have hlo : (B * (1 - η)) * (s ^ 2 + (w j - a) ^ 2) ≤
        (w (j + 1) - a) - (w j - a) := by
      calc
        (B * (1 - η)) * (s ^ 2 + (w j - a) ^ 2) =
            (1 - η) * (B * (s ^ 2 + (w j - a) ^ 2)) := by ring
        _ ≤ (w (j + 1) - a) - (w j - a) := by rw [hquad, hsuc]; linarith [hr.1]
    have hhi : (w (j + 1) - a) - (w j - a) ≤
        (B * (1 + η)) * (s ^ 2 + (w j - a) ^ 2) := by
      calc
        (w (j + 1) - a) - (w j - a) ≤
            (1 + η) * (B * (s ^ 2 + (w j - a) ^ 2)) := by
          rw [hquad, hsuc]
          linarith [hr.2]
        _ = (B * (1 + η)) * (s ^ 2 + (w j - a) ^ 2) := by ring
    have hscale' : 2 * (2 * δ) * (B * (1 + η)) ≤ ε := by
      dsimp [B]
      nlinarith only [hscale]
    exact ParabolicPassageAngle.angle_step_error hs (by positivity) hB
      hε hεhalf hη hηε hxy (hx.trans (by linarith)) hy hlo hhi hscale'
  have hsum := passage_angle_error θ l m hlm.le u (4 * ε) hangle
  have hcoarse : (k : ℝ) * u ≤ 70 := by
    rw [hueq]
    nlinarith [passage_scaled_time_bound ht htmax stay reached]
  have hcentralTime : ((m - l : ℕ) : ℝ) * u ≤ 70 :=
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hlen) hu).trans hcoarse
  have herr : |((m - l : ℕ) : ℝ) * u - (θ m - θ l)| ≤ 280 * ε := by
    exact hsum.trans (by nlinarith [mul_le_mul_of_nonneg_left hcentralTime hε])
  have htotal : (k : ℝ) * u =
      ((m - l : ℕ) : ℝ) * u + ((k - (m - l) : ℕ) : ℝ) * u := by
    have hn : k = (m - l) + (k - (m - l)) := by omega
    have hc : (k : ℝ) = ((m - l : ℕ) : ℝ) + ((k - (m - l) : ℕ) : ℝ) := by
      exact_mod_cast hn
    rw [hc]
    ring
  have hremTime : ((k - (m - l) : ℕ) : ℝ) * u ≤
      (7 * cap / δ ^ 2) * Real.sqrt t := by
    calc
      ((k - (m - l) : ℕ) : ℝ) * u ≤ (cap / δ ^ 2) * u :=
        mul_le_mul_of_nonneg_right hrem hu
      _ = (7 * cap / δ ^ 2) * Real.sqrt t := by rw [hueq]; ring
  have hremNonneg : 0 ≤ ((k - (m - l) : ℕ) : ℝ) * u := by positivity
  have hangleUpper : θ m - θ l ≤ Real.pi := by
    dsimp [θ]
    linarith [Real.arctan_lt_pi_div_two ((w m - a) / s),
      Real.neg_pi_div_two_lt_arctan ((w l - a) / s)]
  have hangleLower : 2 * Real.arctan (δ / (2 * s)) ≤ θ m - θ l := by
    have hmlo : δ / (2 * s) ≤ (w m - a) / s := by
      apply (div_le_div_iff₀ (by positivity : 0 < 2 * s) hs).mpr
      have hh := hm.1
      change δ ≤ w m - a at hh
      nlinarith
    have hlhi : (w l - a) / s ≤ -(δ / (2 * s)) := by
      rw [← neg_div]
      apply (div_le_div_iff₀ hs (by positivity : 0 < 2 * s)).mpr
      have hh := hl.2
      change w l - a ≤ -δ / 2 at hh
      nlinarith
    have hmangle := Real.arctan_mono hmlo
    have hlangle := Real.arctan_mono hlhi
    rw [Real.arctan_neg] at hlangle
    dsimp [θ]
    linarith
  have htail : 0 ≤ Real.pi - 2 * Real.arctan (δ / (2 * s)) := by
    linarith [Real.arctan_lt_pi_div_two (δ / (2 * s))]
  have houter : 0 ≤ (7 * cap / δ ^ 2) * Real.sqrt t := by
    dsimp [cap]
    positivity
  have hf := abs_le.mp herr
  have htarget : 7 * (k : ℝ) * Real.sqrt t = (k : ℝ) * u := by rw [hueq]; ring
  rw [htarget]
  change |(k : ℝ) * u - Real.pi| ≤
    280 * ε + (7 * cap / δ ^ 2) * Real.sqrt t +
      (Real.pi - 2 * Real.arctan (δ / (2 * s)))
  apply abs_le.mpr
  constructor <;> linarith

end
end LoopsParabolic

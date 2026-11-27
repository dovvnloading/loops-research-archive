import ParabolicPassageUniform
import ParabolicPassageLimit
import ParabolicTipFamily

/-!
# Sharp accumulation of the actual period-three primitive tips

For every choice of the archive's noncentral shooting roots, the physical
parameter coefficient is nine pi squared divided by forty-nine.  No
uniqueness of those roots or limiting normal-form model is assumed.
-/

namespace LoopsParabolic

open Set Function Filter
open scoped Topology

noncomputable section

/-- The sharp passage time for any sequence of actual polynomial flights
through the fixed entrance corridor. -/
theorem channel_sharp_passage_limit {k : ℕ → ℕ} {t : ℕ → ℝ}
    (htpos : ∀ n, 0 < t n) (htmax : ∀ n, t n ≤ 1 / 100)
    (htzero : Tendsto t atTop (𝓝 0))
    (stay : ∀ n j, j ≤ k n → (H (t n))^[j] 0 ∈ Icc 0 cap)
    (reached : ∀ n, 7 / 20 ≤ (H (t n))^[k n] 0) :
    Tendsto (fun n => (k n : ℝ) * Real.sqrt (t n))
      atTop (𝓝 (Real.pi / 7)) := by
  obtain ⟨a, ha, root⟩ := passage_root
  have hA : 0 < passageA a := lt_of_lt_of_le (by norm_num) (passageA_ge_one ha)
  have hB : 0 < passageB a := lt_of_lt_of_le (by norm_num) (passageB_ge_one ha)
  apply ParabolicPassageLimit.tendsto_rate_of_scaled_rate
  apply ParabolicPassageLimit.tendsto_of_angle_error
    (R := passageA a / passageB a) (div_pos hA hB) htpos htzero
  intro ε hε hεhalf
  obtain ⟨δ, hδ, _, hb⟩ := passage_uniform_quantitative_estimate ha root hε hεhalf
  refine ⟨7 * cap / δ ^ 2, δ / 2, by positivity, ?_⟩
  have hsmall : ∀ᶠ n in atTop, t n < δ ^ 2 :=
    htzero.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < δ ^ 2))
  filter_upwards [hsmall] with n hn
  have he := hb (t n) (k n) (htpos n) (htmax n) hn.le (stay n) (reached n)
  have harg : (δ / 2) / Real.sqrt ((passageA a / passageB a) * t n) =
      δ / (2 * passageScale a (t n)) := by
    dsimp [passageScale]
    ring
  simpa only [harg] using he

private theorem shot_parameters_tendsto_zero {k : ℕ → ℕ} {t e : ℕ → ℝ}
    (hk : Tendsto k atTop atTop)
    (hshot : ∀ n, Shot (k n) (t n) (e n)) :
    Tendsto t atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨L, hL⟩ := exists_nat_gt (1 / ε)
  filter_upwards [(tendsto_atTop.1 hk) L] with n hn
  have hLn : (L : ℝ) ≤ (k n : ℝ) := by exact_mod_cast hn
  have hlarge : 1 < ε * (k n : ℝ) := by
    have hh := (div_lt_iff₀ hε).mp (hL.trans_le hLn)
    nlinarith
  have hbound := (hshot n).first_rate_bound
  have hsmall : t n < ε := by
    by_contra! hh
    have hm := mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg (k n) : (0 : ℝ) ≤ k n)
    nlinarith
  rw [Real.dist_eq, sub_zero, abs_of_pos (hshot n).t_pos]
  exact hsmall

/-- Every permitted choice of actual shooting roots has the same passage
limit for any sequence of flight lengths tending to infinity. -/
theorem shot_sharp_passage_limit {k : ℕ → ℕ} {t e : ℕ → ℝ}
    (hk : Tendsto k atTop atTop)
    (hshot : ∀ n, Shot (k n) (t n) (e n)) :
    Tendsto (fun n => (k n : ℝ) * Real.sqrt (t n))
      atTop (𝓝 (Real.pi / 7)) := by
  exact channel_sharp_passage_limit (fun n => (hshot n).t_pos)
    (fun n => (hshot n).t_small) (shot_parameters_tendsto_zero hk hshot)
    (fun n => (hshot n).first_corridor) (fun n => (hshot n).first_exit.1)

/-- In the original period and parameter coordinates, the exact sharp
coefficient is `9*pi^2/49`.  This quantifies the actual family and does not
require a preferred noncentral root in each shooting window. -/
theorem shot_sharp_parameter_accumulation {k : ℕ → ℕ} {t e : ℕ → ℝ}
    (hk : Tendsto k atTop atTop)
    (hshot : ∀ n, Shot (k n) (t n) (e n)) :
    Tendsto (fun n => (((3 * (k n + 2) : ℕ) : ℝ) - 6) ^ 2 *
      ((-7 / 4 + t n) + 7 / 4)) atTop (𝓝 (9 * Real.pi ^ 2 / 49)) := by
  have hh := ParabolicPassageLimit.tendsto_quadratic_rate_of_rate
    (fun n => (hshot n).t_pos.le) (shot_sharp_passage_limit hk hshot)
  convert hh using 1
  funext n
  push_cast
  ring

/-- The ordinary physical period has the same sharp coefficient; the
finite six-iterate shift disappears in the proven parameter limit. -/
theorem shot_sharp_physical_period_accumulation {k : ℕ → ℕ} {t e : ℕ → ℝ}
    (hk : Tendsto k atTop atTop)
    (hshot : ∀ n, Shot (k n) (t n) (e n)) :
    Tendsto (fun n => ((3 * (k n + 2) : ℕ) : ℝ) ^ 2 * t n)
      atTop (𝓝 (9 * Real.pi ^ 2 / 49)) := by
  exact ParabolicPassageLimit.tendsto_physical_period_rate
    (fun n => (hshot n).t_pos.le) (shot_parameters_tendsto_zero hk hshot)
    (shot_sharp_passage_limit hk hshot)

/-- The theorem is inhabited at every physical period 18,21,24,... by
the archive's already constructed primitive shooting tips. -/
theorem exists_sharp_primitive_tip_sequence :
    ∃ t e : ℕ → ℝ, (∀ n, Shot (n + 4) (t n) (e n)) ∧
      Tendsto (fun n => (((18 + 3 * n : ℕ) : ℝ) - 6) ^ 2 *
        ((-7 / 4 + t n) + 7 / 4)) atTop (𝓝 (9 * Real.pi ^ 2 / 49)) := by
  have hex : ∀ n : ℕ, ∃ t e : ℝ, Shot (n + 4) t e :=
    fun n => shot_exists (n + 4) (by omega)
  choose t e h using hex
  have hk : Tendsto (fun n : ℕ => n + 4) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    exact eventually_atTop.2 ⟨b, fun n hn => by omega⟩
  refine ⟨t, e, h, ?_⟩
  have hh := shot_sharp_parameter_accumulation hk h
  convert hh using 1
  funext n
  rw [show 18 + 3 * n = 3 * (n + 4 + 2) by omega]

end
end LoopsParabolic

import ActualParentMarks
import GlobalCrestSourceGates

/-!
# Literal source marks for the two independent child Wave problems

The upper source base has ending intervals `(-x₄ₚ,x₂ₚ)` and
`(x₅ₚ,-eₚ)` on the upper bank of the actual slit `[-xₚ,xₚ]`.
Here `eₚ` is a constructed positive fixed point of the complete actual
return.  The six normalized cuts below retain those physical meanings.
All six converge to one ordered limiting configuration, with a uniform
quantitative error and with no fixed-point convergence hypothesis.
-/

namespace ActualChildMarks

open Set Function Filter
open NearTwoTip NearTwoShooting LimitingCrest LimitingCrestQuadraticReturn
open LoopsLimitingCrestParameter ActualParentMarks ActualCrestLimit
open GlobalCrestSourceGates
open scoped Topology

noncomputable section

/-- The positive actual fixed cut; the choice is unique on the positive
part of the complete-return control disk under `ActualTip`. -/
def actualAlpha (c : ℝ) (p : ℕ) : ℝ :=
  Classical.epsilon fun a : ℝ =>
    a ∈ Ioo (518/1000 : ℝ) (519/1000) ∧
      normalizedReturn c p (a : ℂ) = (a : ℂ)

theorem actualAlpha_spec {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) :
    actualAlpha c p ∈ Ioo (518/1000 : ℝ) (519/1000) ∧
      normalizedReturn c p (actualAlpha c p : ℂ) = (actualAlpha c p : ℂ) := by
  obtain ⟨a, ha, hfix, _⟩ := actual_positive_fixed_cut hp hc
  unfold actualAlpha
  exact Classical.epsilon_spec
    (show ∃ a : ℝ, a ∈ Ioo (518/1000 : ℝ) (519/1000) ∧
      normalizedReturn c p (a : ℂ) = (a : ℂ) from ⟨a, ha, hfix⟩)

theorem actualAlpha_unique {p : ℕ} (hp : 17 ≤ p) {c b : ℝ}
    (hc : ActualTip p c) (hb : b ∈ Icc (0 : ℝ) (23/20))
    (hfix : normalizedReturn c p (b : ℂ) = (b : ℂ)) : b = actualAlpha c p := by
  obtain ⟨a, _, _, huniq⟩ := actual_positive_fixed_cut hp hc
  have hs := actualAlpha_spec hp hc
  have hmem : actualAlpha c p ∈ Icc (0 : ℝ) (23/20) := by
    constructor <;> linarith [hs.1.1, hs.1.2]
  exact (huniq b hb hfix).trans (huniq _ hmem hs.2).symm

/-- The normalized fixed cut is a literal fixed point of `f_c^p`
after multiplication by the same positive critical return scale. -/
theorem actualAlpha_physical_fixed {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) :
    ((quadraticMap c)^[p])
        ((criticalValue c p : ℂ) * (actualAlpha c p : ℂ)) =
      (criticalValue c p : ℂ) * (actualAlpha c p : ℂ) := by
  have hs := normalized_iterate_scale c p hc.2.1.ne' 1 (actualAlpha c p : ℂ)
  simpa only [Nat.one_mul, Function.iterate_one, (actualAlpha_spec hp hc).2] using hs.symm

def limitAlpha (k : ℝ) : ℝ :=
  Classical.epsilon fun a : ℝ => 0 < a ∧ realMap k a = a

theorem limitAlpha_spec {k : ℝ} (hk : k ∈ parameterInterval) :
    0 < limitAlpha k ∧ realMap k (limitAlpha k) = limitAlpha k := by
  exact Classical.epsilon_spec (positive_fixed_point hk).exists

theorem limitAlpha_bracket {k : ℝ} (hk : k ∈ parameterInterval) :
    limitAlpha k ∈ Ioo (518/1000 : ℝ) (519/1000) :=
  positive_fixed_point_bracket hk (limitAlpha_spec hk).1 (limitAlpha_spec hk).2

/-- The positive fixed-point equation has a scalar expansion factor at
least one.  Uniform complete-map approximation therefore controls the
actual source cut without assuming fixed-point stability. -/
theorem actualAlpha_error {p : ℕ} (hp : 17 ≤ p) {c k : ℝ}
    (hc : ActualTip p c) (hk : k ∈ parameterInterval) (hroot : relation k = 0) :
    |actualAlpha c p-limitAlpha k| ≤ 23646*scale p := by
  let a := actualAlpha c p
  let b := limitAlpha k
  have ha := actualAlpha_spec hp hc
  have hb := limitAlpha_spec hk
  have ha0 : 0 < a := by dsimp only [a]; linarith [ha.1.1]
  have hb0 : 0 < b := hb.1
  have hk0 : 0 ≤ k := by linarith [hk.1]
  have hz : ‖(a : ℂ)‖ ≤ 23/20 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha0]
    dsimp only [a]
    linarith [ha.1.2]
  have he := actual_tip_limit_map_error hp hc hk hroot hz
  change ‖normalizedReturn c p (a : ℂ)-complexMap k (a : ℂ)‖ ≤ _ at he
  have hafix : normalizedReturn c p (a : ℂ) = (a : ℂ) := ha.2
  rw [hafix] at he
  have hre := (Complex.abs_re_le_norm ((a : ℂ)-complexMap k (a : ℂ))).trans he
  have herror : |a-realMap k a| ≤ 23646*scale p := by
    simpa only [complexMap_real, Complex.sub_re, Complex.ofReal_re] using hre
  have hfactor : (a-b)*(k*(a+b)+1) = a-realMap k a := by
    have hfix : realMap k b = b := hb.2
    dsimp only [realMap] at hfix ⊢
    nlinarith only [hfix]
  have hge : 1 ≤ k*(a+b)+1 := by
    have hm := mul_nonneg hk0 (add_nonneg ha0.le hb0.le)
    linarith only [hm]
  change |a-b| ≤ _
  calc
    |a-b| = |a-b| * 1 := (mul_one _).symm
    _ ≤ |a-b| * (k*(a+b)+1) := mul_le_mul_of_nonneg_left hge (abs_nonneg _)
    _ = |a-realMap k a| := by
      rw [← abs_of_nonneg (show 0 ≤ k*(a+b)+1 by linarith), ← abs_mul, hfactor]
    _ ≤ 23646*scale p := herror

/-- The actual slit tips and all four endpoint cuts of the upper child.
The two open ending intervals are coordinates `(1,2)` and `(3,4)`. -/
def actualChildCuts (c : ℝ) (p : ℕ) : Fin 6 → ℝ :=
  ![-1, -normalizedCut c p 4, normalizedCut c p 2,
    normalizedCut c p 5, -actualAlpha c p, 1]

def limitChildCuts (k : ℝ) : Fin 6 → ℝ :=
  ![-1, -criticalOrbit k 4, criticalOrbit k 2,
    criticalOrbit k 5, -limitAlpha k, 1]

theorem actualChildCuts_error {p : ℕ} (hp : 17 ≤ p) {c k : ℝ}
    (hc : ActualTip p c) (hk : k ∈ parameterInterval) (hroot : relation k = 0)
    (i : Fin 6) :
    |actualChildCuts c p i-limitChildCuts k i| ≤ 3906*23646*scale p := by
  have hq := (scale_pos p).le
  fin_cases i
  · change |(-1 : ℝ)-(-1)| ≤ _
    rw [sub_self, abs_zero]
    positivity
  · change |-normalizedCut c p 4 - -criticalOrbit k 4| ≤ _
    rw [neg_sub_neg, abs_sub_comm]
    exact normalizedCut_error_uniform hp (by norm_num : 4 ≤ 6) hc hk hroot
  · change |normalizedCut c p 2-criticalOrbit k 2| ≤ _
    exact normalizedCut_error_uniform hp (by norm_num : 2 ≤ 6) hc hk hroot
  · change |normalizedCut c p 5-criticalOrbit k 5| ≤ _
    exact normalizedCut_error_uniform hp (by norm_num : 5 ≤ 6) hc hk hroot
  · have ha := actualAlpha_error hp hc hk hroot
    change |-actualAlpha c p - -limitAlpha k| ≤ _
    rw [neg_sub_neg, abs_sub_comm]
    nlinarith only [ha, hq]
  · change |(1 : ℝ)-1| ≤ _
    rw [sub_self, abs_zero]
    positivity

theorem limitChildCuts_gap {k : ℝ} (hk : k ∈ parameterInterval)
    {i j : Fin 6} (hij : i < j) :
    (1/50 : ℝ) < limitChildCuts k j-limitChildCuts k i := by
  obtain ⟨h2l,h2u,h5l,h5u,_,_⟩ := limit_cut_boxes hk
  have h4 := parameter_orbit_bounds hk
  have ha := limitAlpha_bracket hk
  fin_cases i <;> fin_cases j
  all_goals norm_num at hij
  all_goals norm_num [limitChildCuts]
  all_goals linarith [h4.2.2.1, h4.2.2.2, ha.1, ha.2]

theorem limitChildCuts_strictMono {k : ℝ} (hk : k ∈ parameterInterval) :
    StrictMono (limitChildCuts k) := by
  intro i j hij
  have h := limitChildCuts_gap hk hij
  linarith

theorem limitChildCuts_separated {k : ℝ} (hk : k ∈ parameterInterval)
    {i j : Fin 6} (hij : i ≠ j) :
    (1/50 : ℝ) < |limitChildCuts k i-limitChildCuts k j| := by
  rcases lt_or_gt_of_ne hij with hij | hij
  · simpa only [abs_sub_comm] using
      (limitChildCuts_gap hk hij).trans_le (le_abs_self (limitChildCuts k j-limitChildCuts k i))
  · exact (limitChildCuts_gap hk hij).trans_le (le_abs_self _)

theorem actualChildCuts_error_lt {p : ℕ} (hp : 17 ≤ p) {c k : ℝ}
    (hc : ActualTip p c) (hk : k ∈ parameterInterval) (hroot : relation k = 0)
    (i : Fin 6) : |actualChildCuts c p i-limitChildCuts k i| < 1/150 := by
  have he := actualChildCuts_error hp hc hk hroot i
  nlinarith [scale_small hp]

theorem actualChildCuts_gap {p : ℕ} (hp : 17 ≤ p) {c k : ℝ}
    (hc : ActualTip p c) (hk : k ∈ parameterInterval) (hroot : relation k = 0)
    {i j : Fin 6} (hij : i < j) :
    (1/200 : ℝ) < actualChildCuts c p j-actualChildCuts c p i := by
  have hi := abs_lt.mp (actualChildCuts_error_lt hp hc hk hroot i)
  have hj := abs_lt.mp (actualChildCuts_error_lt hp hc hk hroot j)
  have hg := limitChildCuts_gap hk hij
  linarith

theorem actualChildCuts_strictMono {p : ℕ} (hp : 17 ≤ p) {c k : ℝ}
    (hc : ActualTip p c) (hk : k ∈ parameterInterval) (hroot : relation k = 0) :
    StrictMono (actualChildCuts c p) := by
  intro i j hij
  have h := actualChildCuts_gap hp hc hk hroot hij
  linarith

private theorem error_tendsto_zero (C : ℝ) :
    Tendsto (fun n : ℕ => C*scale (n+17)) atTop (𝓝 0) := by
  have hbase : Tendsto (fun n : ℕ => (1/4 : ℝ)^n) atTop (𝓝 (0 : ℝ)) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  simpa only [scale, pow_add, mul_zero, zero_mul] using
    (hbase.mul_const ((1/4 : ℝ)^17)).const_mul C

theorem actualChildCuts_tendsto {k : ℝ} (hk : k ∈ parameterInterval)
    (hroot : relation k = 0) (c : ℕ → ℝ)
    (hc : ∀ n, ActualTip (n+17) (c n)) (i : Fin 6) :
    Tendsto (fun n => actualChildCuts (c n) (n+17) i)
      atTop (𝓝 (limitChildCuts k i)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have he := (tendsto_order.mp (error_tendsto_zero (3906*23646))).2 ε hε
  filter_upwards [he] with n hn
  rw [Real.dist_eq]
  exact (actualChildCuts_error (by omega) (hc n) hk hroot i).trans_lt hn

/-- Every unscaled coordinate is a critical iterate or the proved
positive physical fixed cut of the same actual polynomial return. -/
def physicalChildCuts (c : ℝ) (p : ℕ) : Fin 6 → ℝ :=
  ![-criticalValue c p, -criticalValue c (4*p), criticalValue c (2*p),
    criticalValue c (5*p), -(criticalValue c p*actualAlpha c p), criticalValue c p]

theorem physicalChildCuts_scale {p : ℕ} {c : ℝ}
    (hd : criticalValue c p ≠ 0) (i : Fin 6) :
    criticalValue c p*actualChildCuts c p i = physicalChildCuts c p i := by
  fin_cases i <;> dsimp [actualChildCuts, physicalChildCuts, normalizedCut] <;>
    field_simp [hd] <;> ring

theorem physicalChildCuts_strictMono {p : ℕ} (hp : 17 ≤ p) {c k : ℝ}
    (hc : ActualTip p c) (hk : k ∈ parameterInterval) (hroot : relation k = 0) :
    StrictMono (physicalChildCuts c p) := by
  intro i j hij
  rw [← physicalChildCuts_scale hc.2.1.ne' i, ← physicalChildCuts_scale hc.2.1.ne' j]
  exact mul_lt_mul_of_pos_left (actualChildCuts_strictMono hp hc hk hroot hij) hc.2.1

end
end ActualChildMarks

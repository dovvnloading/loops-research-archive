import ActualPairablePortLimit
import ActualParentSupremum
import SlitFourPointPairable

/-!
# The attained limiting-domain pairable optimization problem

The full-plane source retains the literal limiting slit [-1,1] and the
four limiting physical source ports. Its Borel pairable supremum is
identified with an actual attaining reflected rectangle Wave.
-/

namespace ActualPairableLimitModel

open Set MarkedSlitTransport SlitWaveModulus
open LoopsLimitingCrestParameter ActualPairablePortLimit
open SlitFourPointPairable
open scoped ENNReal
noncomputable section

def sourceSlit : Set ℂ := {z | z.im = 0 ∧ z.re ∈ Icc (-1) 1}

def leftPort (k : ℝ) : Set ℂ := port (-criticalOrbit k 4) (criticalOrbit k 2)

def rightPort (k : ℝ) (hk : k ∈ parameterInterval) : Set ℂ :=
  port (criticalOrbit k 5) (-limitingAlpha k hk)

def limitingPairableWidth (k : ℝ) (hk : k ∈ parameterInterval) : ℝ≥0∞ :=
  SlitPairableWaves.width (ActualParentSupremum.limitMarking k hk) univ univ sourceSlit
    (leftPort k) (rightPort k hk)

def limitingFamily (k : ℝ) (hk : k ∈ parameterInterval) : Set Curve :=
  SlitFourPointPairable.family (limiting_source_order hk).2.1
    (limiting_source_order hk).2.2.1 (limiting_source_order hk).2.2.2.1

def limitingRatio (k : ℝ) (hk : k ∈ parameterInterval) : ℝ :=
  SlitFourPointChart.height (-criticalOrbit k 4) (criticalOrbit k 2)
    (criticalOrbit k 5) (-limitingAlpha k hk) /
  (2*SlitFourPointChart.width (-criticalOrbit k 4) (criticalOrbit k 2)
    (criticalOrbit k 5) (-limitingAlpha k hk))

theorem negative_limitingAlpha_lt_third_cut {k : ℝ} (hk : k ∈ parameterInterval) :
    -limitingAlpha k hk < criticalOrbit k 3 := by
  have ha := limitingAlpha_bounds hk
  obtain ⟨_,_,_,_,h3l,h3u⟩ := ActualParentMarks.limit_cut_boxes hk
  linarith [ha.1]

theorem ports_subset_sourceSlit {k : ℝ} (hk : k ∈ parameterInterval) :
    leftPort k ⊆ sourceSlit ∧ rightPort k hk ⊆ sourceSlit := by
  obtain ⟨h0,h1,h2,h3,h4⟩ := limiting_source_order hk
  constructor
  · intro z hz
    refine ⟨hz.1,?_,?_⟩
    · exact (h0.trans hz.2.1).le
    · have hh := hz.2.2.trans (h2.trans (h3.trans h4))
      linarith
  · intro z hz
    refine ⟨hz.1,?_,?_⟩
    · exact ((h0.trans (h1.trans h2)).trans hz.2.1).le
    · have hh := hz.2.2.trans h4
      linarith

theorem endpoints_mem_sourceSlit {k : ℝ} (hk : k ∈ parameterInterval) :
    ((-criticalOrbit k 4 : ℝ):ℂ) ∈ sourceSlit ∧ (criticalOrbit k 2 : ℂ) ∈ sourceSlit ∧
      (criticalOrbit k 5 : ℂ) ∈ sourceSlit ∧ ((-limitingAlpha k hk : ℝ):ℂ) ∈ sourceSlit := by
  obtain ⟨h0,h1,h2,h3,h4⟩ := limiting_source_order hk
  refine ⟨⟨rfl,?_,?_⟩,⟨rfl,?_,?_⟩,⟨rfl,?_,?_⟩,⟨rfl,?_,?_⟩⟩ <;>
    simp only [Complex.ofReal_re] <;> linarith

/-- The full limiting physical two-port optimum is attained by the actual
reflected four-electrode foliation, with the exact period value. -/
theorem limitingFamily_attains {k : ℝ} (hk : k ∈ parameterInterval) :
    SlitPairableWaves.PairableWave (ActualParentSupremum.limitMarking k hk)
      univ univ sourceSlit (leftPort k) (rightPort k hk) (limitingFamily k hk) ∧
      modulus (traces (limitingFamily k hk)) = limitingPairableWidth k hk ∧
      limitingPairableWidth k hk = ENNReal.ofReal (limitingRatio k hk) := by
  obtain ⟨h0,h1,h2,h3,h4⟩ := limiting_source_order hk
  obtain ⟨he0,he1,he2,he3⟩ := endpoints_mem_sourceSlit hk
  apply SlitFourPointPairable.family_attains_width h1 h2 h3
    (ActualParentSupremum.limitMarking k hk) sourceSlit
  · exact le_rfl
  · exact le_rfl
  · exact (negative_limitingAlpha_lt_third_cut hk).le
  · exact fun _ hz => hz.1
  · exact (ports_subset_sourceSlit hk).1
  · exact (ports_subset_sourceSlit hk).2
  · exact he0
  · exact he1
  · exact he2
  · exact he3

theorem limitingPairableWidth_eq_period_ratio {k : ℝ} (hk : k ∈ parameterInterval) :
    limitingPairableWidth k hk = ENNReal.ofReal (limitingRatio k hk) :=
  (limitingFamily_attains hk).2.2

theorem limitingPairableWidth_pos {k : ℝ} (hk : k ∈ parameterInterval) :
    0 < limitingPairableWidth k hk := by
  rw [limitingPairableWidth_eq_period_ratio hk]
  apply ENNReal.ofReal_pos.mpr
  have ho := limiting_source_order hk
  exact div_pos (SlitFourPointChart.height_pos ho.2.1 ho.2.2.1 ho.2.2.2.1)
    (mul_pos (by norm_num) (SlitFourPointChart.width_pos ho.2.1 ho.2.2.1 ho.2.2.2.1))

theorem limitingPairableWidth_ne_top {k : ℝ} (hk : k ∈ parameterInterval) :
    limitingPairableWidth k hk ≠ ⊤ := by
  rw [limitingPairableWidth_eq_period_ratio hk]
  exact ENNReal.ofReal_ne_top

end
end ActualPairableLimitModel

import SlitWaveLimit
import ActualParentMarks
import SlitWaveFinite
import SlitWaveScaling

/-!
# Convergence of the actual unrestricted marked parent optimum

Every mark and every outer radius below is a literal expression in the
critical orbit of an actual quadratic parameter.  The generic marked
exhaustion theorem is instantiated with proved convergence of all four
marks and the actual target disk.  No modulus transport, escaping-family
estimate, or optimizer is an input to the final theorem.
-/

namespace ActualParentSupremum

open Set Filter Metric
open MarkedSlitTransport SlitWaveLimit ActualParentMarks
open NearTwoTip NearTwoShooting LoopsLimitingCrestParameter
open SlitWaveModulus SlitWaveFinite
open SlitWaveScaling LimitingCrestQuadraticReturn
open scoped Topology ENNReal

noncomputable section

def markingOfCuts (a : Fin 4 → ℝ) (ha : StrictMono a) : Marking where
  left := a 0
  first := a 1
  second := a 2
  right := a 3
  left_lt_first := ha (by decide : (0 : Fin 4) < 1)
  first_lt_second := ha (by decide : (1 : Fin 4) < 2)
  second_lt_right := ha (by decide : (2 : Fin 4) < 3)

theorem markCoords_markingOfCuts (a : Fin 4 → ℝ) (ha : StrictMono a) (i : Fin 4) :
    markCoords (markingOfCuts a ha) i = a i := by
  fin_cases i <;> rfl

def limitMarking (k : ℝ) (hk : k ∈ parameterInterval) : Marking :=
  markingOfCuts (limitCuts k) (limitCuts_strictMono hk)

def actualMarking {p : ℕ} (hp : 17 ≤ p) {c k : ℝ}
    (hc : ActualTip p c) (hk : k ∈ parameterInterval) (hroot : relation k = 0) : Marking :=
  markingOfCuts (actualCuts c p) (actualCuts_strictMono hp hc hk hroot)

/-- The actual normalized parent width is the unrestricted supremum of
the actual geometric Borel laminations, not a selected witness or a
full-path envelope substituted for that supremum. -/
def actualParentWidth {p : ℕ} (hp : 17 ≤ p) {c k : ℝ}
    (hc : ActualTip p c) (hk : k ∈ parameterInterval) (hroot : relation k = 0) : ℝ≥0∞ :=
  width (actualMarking hp hc hk hroot) (ball (0 : ℂ) (targetRadius c p))

def limitingParentWidth (k : ℝ) (hk : k ∈ parameterInterval) : ℝ≥0∞ :=
  width (limitMarking k hk) univ

/-- All actual signed tips satisfying the proved near-minus-two
shooting conditions have the same limiting marked parent optimum.
The sequence of actual parameters is arbitrary subject to those actual
conditions; no continuity or geometric estimates for it are assumed. -/
theorem actual_parent_optimum_converges {k : ℝ} (hk : k ∈ parameterInterval)
    (hroot : relation k = 0) (c : ℕ → ℝ)
    (hc : ∀ n, ActualTip (n+17) (c n)) :
    Tendsto (fun n => actualParentWidth (by omega : 17 ≤ n+17) (hc n) hk hroot)
      atTop (𝓝 (limitingParentWidth k hk)) := by
  apply width_tendsto_of_mark_convergence (limitMarking k hk)
    (fun n => actualMarking (by omega : 17 ≤ n+17) (hc n) hk hroot)
    (fun n => targetRadius (c n) (n+17)) (r := 1/100) (by norm_num)
  · intro i j hij
    simp only [limitMarking, markCoords_markingOfCuts]
    exact (by norm_num : (1/100 : ℝ) ≤ 1/25).trans (limitCuts_separated hk hij).le
  · intro i
    simpa only [actualMarking, limitMarking, markCoords_markingOfCuts] using
      actualCuts_tendsto hk hroot c hc i
  · exact targetRadius_tendsto c hc

/-- Actual parameters and the common model root are constructed within
Lean.  In particular the convergence theorem has no assumed existence
of the quadratic family or of the limiting coefficient. -/
theorem exists_actual_parent_optima_converging :
    ∃ (k : ℝ) (hk : k ∈ parameterInterval) (hroot : relation k = 0),
      ∃ (c : ℕ → ℝ) (hc : ∀ n, ActualTip (n+17) (c n)),
        Tendsto (fun n => actualParentWidth (by omega : 17 ≤ n+17) (hc n) hk hroot)
          atTop (𝓝 (limitingParentWidth k hk)) := by
  classical
  obtain ⟨k, ⟨hk, hroot⟩, _⟩ := exists_unique_limiting_parameter
  choose c hc using fun n : ℕ => exists_actual_tip (n+17) (by omega)
  exact ⟨k, hk, hroot, c, hc, actual_parent_optimum_converges hk hroot c hc⟩

/-- The unrestricted marked supremum is finite on every outer domain.
A single explicitly constructed bounded-disk metric controls all of its
laminations at once. -/
theorem marked_width_ne_top (M : Marking) (D : Set ℂ) : width M D ≠ ⊤ := by
  have hbound : width M D ≤ area (parentDensity M) := by
    apply iSup₂_le
    intro Γ hΓ
    exact parentWave_modulus_le hΓ
  exact ne_top_of_le_ne_top (parentDensity_area_ne_top M) hbound

theorem actualParentWidth_ne_top {p : ℕ} (hp : 17 ≤ p) {c k : ℝ}
    (hc : ActualTip p c) (hk : k ∈ parameterInterval) (hroot : relation k = 0) :
    actualParentWidth hp hc hk hroot ≠ ⊤ :=
  marked_width_ne_top _ _

theorem limitingParentWidth_ne_top (k : ℝ) (hk : k ∈ parameterInterval) :
    limitingParentWidth k hk ≠ ⊤ := marked_width_ne_top _ _

/-- The same convergence is convergence of finite real optimal widths,
not merely convergence to a possibly infinite extended value. -/
theorem actual_parent_optimum_real_converges {k : ℝ} (hk : k ∈ parameterInterval)
    (hroot : relation k = 0) (c : ℕ → ℝ)
    (hc : ∀ n, ActualTip (n+17) (c n)) :
    Tendsto (fun n => (actualParentWidth (by omega : 17 ≤ n+17) (hc n) hk hroot).toReal)
      atTop (𝓝 (limitingParentWidth k hk).toReal) :=
  (ENNReal.tendsto_toReal (limitingParentWidth_ne_top k hk)).comp
    (actual_parent_optimum_converges hk hroot c hc)

theorem exists_finite_actual_parent_optima_converging :
    ∃ (k : ℝ) (hk : k ∈ parameterInterval) (hroot : relation k = 0),
      ∃ (c : ℕ → ℝ) (hc : ∀ n, ActualTip (n+17) (c n)),
        (∀ n, actualParentWidth (by omega : 17 ≤ n+17) (hc n) hk hroot ≠ ⊤) ∧
        limitingParentWidth k hk ≠ ⊤ ∧
        Tendsto (fun n => (actualParentWidth (by omega : 17 ≤ n+17) (hc n) hk hroot).toReal)
          atTop (𝓝 (limitingParentWidth k hk).toReal) := by
  classical
  obtain ⟨k, ⟨hk, hroot⟩, _⟩ := exists_unique_limiting_parameter
  choose c hc using fun n : ℕ => exists_actual_tip (n+17) (by omega)
  exact ⟨k,hk,hroot,c,hc,
    (fun n => actualParentWidth_ne_top (by omega) (hc n) hk hroot),
    limitingParentWidth_ne_top k hk, actual_parent_optimum_real_converges hk hroot c hc⟩

/-- The four unscaled marks are literal values in the original
quadratic dynamical plane. -/
def physicalCuts (c : ℝ) (p : ℕ) : Fin 4 → ℝ :=
  ![criticalValue c (2*p), criticalValue c (5*p),
    criticalValue c (3*p), criticalValue c p]

theorem physicalCuts_scale {p : ℕ} {c : ℝ} (hd : criticalValue c p ≠ 0)
    (i : Fin 4) : criticalValue c p * actualCuts c p i = physicalCuts c p i := by
  fin_cases i <;> dsimp [actualCuts,physicalCuts,normalizedCut] <;> field_simp [hd]

theorem physicalCuts_strictMono {p : ℕ} (hp : 17 ≤ p) {c k : ℝ}
    (hc : ActualTip p c) (hk : k ∈ parameterInterval) (hroot : relation k = 0) :
    StrictMono (physicalCuts c p) := by
  intro i j hij
  rw [← physicalCuts_scale hc.2.1.ne' i,← physicalCuts_scale hc.2.1.ne' j]
  exact mul_lt_mul_of_pos_left (actualCuts_strictMono hp hc hk hroot hij) hc.2.1

def physicalMarking {p : ℕ} (hp : 17 ≤ p) {c k : ℝ}
    (hc : ActualTip p c) (hk : k ∈ parameterInterval) (hroot : relation k = 0) : Marking :=
  markingOfCuts (physicalCuts c p) (physicalCuts_strictMono hp hc hk hroot)

/-- The original target is exactly the disk of radius `2⁻ᵖ` with the
literal physical slit and electrode cuts specified by `physicalMarking`. -/
def physicalParentWidth {p : ℕ} (hp : 17 ≤ p) {c k : ℝ}
    (hc : ActualTip p c) (hk : k ∈ parameterInterval) (hroot : relation k = 0) : ℝ≥0∞ :=
  width (physicalMarking hp hc hk hroot) (ball (0 : ℂ) ((1/2 : ℝ)^p))

private theorem marking_eq {M A : Marking}
    (hl : M.left = A.left) (ha : M.first = A.first)
    (hb : M.second = A.second) (hr : M.right = A.right) : M = A := by
  cases M
  cases A
  simp_all

theorem actualMarking_scale {p : ℕ} (hp : 17 ≤ p) {c k : ℝ}
    (hc : ActualTip p c) (hk : k ∈ parameterInterval) (hroot : relation k = 0) :
    (actualMarking hp hc hk hroot).map
      (OrderIso.mulLeft₀ (criticalValue c p) hc.2.1) = physicalMarking hp hc hk hroot := by
  apply marking_eq
  · exact physicalCuts_scale hc.2.1.ne' 0
  · exact physicalCuts_scale hc.2.1.ne' 1
  · exact physicalCuts_scale hc.2.1.ne' 2
  · exact physicalCuts_scale hc.2.1.ne' 3

/-- The exact full physical optimum equals the normalized full optimum.
The equality is proved by conformal dilation of all leaves and densities,
not inferred from the normalization of the four numerical cuts. -/
theorem physicalParentWidth_eq_actual {p : ℕ} (hp : 17 ≤ p) {c k : ℝ}
    (hc : ActualTip p c) (hk : k ∈ parameterInterval) (hroot : relation k = 0) :
    physicalParentWidth hp hc hk hroot = actualParentWidth hp hc hk hroot := by
  have hscale := width_dilation_ball (actualMarking hp hc hk hroot)
    (targetRadius c p) (criticalValue c p) hc.2.1
  have hR : criticalValue c p * targetRadius c p = (1/2 : ℝ)^p := by
    unfold targetRadius
    field_simp [hc.2.1.ne']
  rw [actualMarking_scale,hR] at hscale
  exact hscale

theorem physicalParentWidth_ne_top {p : ℕ} (hp : 17 ≤ p) {c k : ℝ}
    (hc : ActualTip p c) (hk : k ∈ parameterInterval) (hroot : relation k = 0) :
    physicalParentWidth hp hc hk hroot ≠ ⊤ := by
  rw [physicalParentWidth_eq_actual]
  exact actualParentWidth_ne_top hp hc hk hroot

/-- Finite real convergence for the unrestricted optimal widths on the
literal, unscaled quadratic slit domains. -/
theorem physical_parent_optimum_real_converges {k : ℝ} (hk : k ∈ parameterInterval)
    (hroot : relation k = 0) (c : ℕ → ℝ)
    (hc : ∀ n, ActualTip (n+17) (c n)) :
    Tendsto (fun n => (physicalParentWidth (by omega : 17 ≤ n+17) (hc n) hk hroot).toReal)
      atTop (𝓝 (limitingParentWidth k hk).toReal) := by
  simpa only [physicalParentWidth_eq_actual] using
    actual_parent_optimum_real_converges hk hroot c hc

/-- The physical quadratic family, the finite limiting optimum, and
convergence of all complete parent suprema are constructed together. -/
theorem exists_physical_parent_optima_converging :
    ∃ (k : ℝ) (hk : k ∈ parameterInterval) (hroot : relation k = 0),
      ∃ (c : ℕ → ℝ) (hc : ∀ n, ActualTip (n+17) (c n)),
        (∀ n, physicalParentWidth (by omega : 17 ≤ n+17) (hc n) hk hroot ≠ ⊤) ∧
        limitingParentWidth k hk ≠ ⊤ ∧
        Tendsto (fun n => (physicalParentWidth (by omega : 17 ≤ n+17) (hc n) hk hroot).toReal)
          atTop (𝓝 (limitingParentWidth k hk).toReal) := by
  classical
  obtain ⟨k, ⟨hk, hroot⟩, _⟩ := exists_unique_limiting_parameter
  choose c hc using fun n : ℕ => exists_actual_tip (n+17) (by omega)
  exact ⟨k,hk,hroot,c,hc,
    (fun n => physicalParentWidth_ne_top (by omega) (hc n) hk hroot),
    limitingParentWidth_ne_top k hk, physical_parent_optimum_real_converges hk hroot c hc⟩

end
end ActualParentSupremum

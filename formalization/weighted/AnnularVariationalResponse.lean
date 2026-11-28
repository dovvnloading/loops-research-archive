import AnnularModeContraction
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

/-!
# Nonlinear full-trace response through an annular collar

The trace has arbitrarily many real Fourier coordinates. Energy is the
extended nonnegative sum of the exact mode energies, so no finite-mode
truncation, summability exchange, or minimizer is assumed. A terminal load
may be nonlinear, nonconvex, discontinuous, or infinite off its admissible
cone. Its only algebraic requirement is quadratic homogeneity.

The contraction proof rescales the entire trial trace by one scalar.
Consequently it commutes with arbitrary linear changes of trace coordinates,
including changes mixing all Fourier modes.
-/

namespace AnnularVariationalResponse

open Set Function
open scoped ENNReal
open AnnularModeContraction

noncomputable section

abbrev Trace (ι : Type*) := ι → ℝ

/-- The complete normalized Fourier energy, including infinite-energy traces. -/
def collar {ι : Type*} (e : ι → ℝ) (u v : Trace ι) : ℝ≥0∞ :=
  ∑' i, ENNReal.ofReal (mode (e i) (u i) (v i))

/-- Positive homogeneous terminal energy. Convexity and quadratic-form
representability are deliberately absent. -/
structure Load (ι : Type*) where
  energy : Trace ι → ℝ≥0∞
  zero : energy 0 = 0
  homogeneous : ∀ (s : ℝ) (v : Trace ι),
    energy (s • v) = ENNReal.ofReal (s^2) * energy v

instance {ι : Type*} : CoeFun (Load ι) (fun _ => Trace ι → ℝ≥0∞) :=
  ⟨Load.energy⟩

/-- Elimination of the whole distal trace, rather than of a selected mode. -/
def response {ι : Type*} (e : ι → ℝ) (B : Load ι) (u : Trace ι) : ℝ≥0∞ :=
  ⨅ v : Trace ι, collar e u v + B v

/-- Symmetric multiplicative comparison; its square-root radius is `a`. -/
def Comparable {ι : Type*} (a : ℝ) (B D : Trace ι → ℝ≥0∞) : Prop :=
  (∀ u, D u ≤ ENNReal.ofReal (a^2) * B u) ∧
    (∀ u, B u ≤ ENNReal.ofReal (a^2) * D u)

theorem collar_smul {ι : Type*} (e : ι → ℝ) (s : ℝ) (u v : Trace ι) :
    collar e (s • u) (s • v) = ENNReal.ofReal (s^2) * collar e u v := by
  unfold collar
  simp_rw [Pi.smul_apply, smul_eq_mul, mode_smul,
    ENNReal.ofReal_mul (sq_nonneg s)]
  exact ENNReal.tsum_mul_left

theorem collar_zero {ι : Type*} (e : ι → ℝ) : collar e 0 0 = 0 := by
  simp [collar, mode]

theorem response_zero {ι : Type*} (e : ι → ℝ) (B : Load ι) :
    response e B 0 = 0 := by
  apply le_antisymm _ bot_le
  exact iInf_le_of_le (0 : Trace ι) (by simp [collar_zero, B.zero])

theorem response_smul {ι : Type*} (e : ι → ℝ) (B : Load ι)
    (s : ℝ) (u : Trace ι) :
    response e B (s • u) = ENNReal.ofReal (s^2) * response e B u := by
  by_cases hs : s = 0
  · subst s
    simp [response_zero]
  have hs0 : ENNReal.ofReal (s^2) ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero]
    exact not_le.mpr (sq_pos_of_ne_zero hs)
  have hst : ENNReal.ofReal (s^2) ≠ ∞ := ENNReal.ofReal_ne_top
  apply le_antisymm
  · change response e B (s • u) ≤ ENNReal.ofReal (s^2) * ⨅ v, collar e u v + B v
    rw [ENNReal.mul_iInf_of_ne hs0 hst]
    apply le_iInf
    intro v
    calc
      response e B (s • u) ≤ collar e (s • u) (s • v) + B (s • v) :=
        iInf_le _ _
      _ = ENNReal.ofReal (s^2) * (collar e u v + B v) := by
        rw [collar_smul, B.homogeneous, mul_add]
  · apply le_iInf
    intro v
    have hv : s • (s⁻¹ • v) = v := by simp [smul_smul, hs]
    calc
      ENNReal.ofReal (s^2) * response e B u ≤
          ENNReal.ofReal (s^2) * (collar e u (s⁻¹ • v) + B (s⁻¹ • v)) :=
        mul_le_mul_left' (iInf_le _ _) _
      _ = collar e (s • u) v + B v := by
        rw [mul_add, ← collar_smul, ← B.homogeneous, hv]

/-- Annular elimination stays in the same nonlinear load class. -/
def responseLoad {ι : Type*} (e : ι → ℝ) (B : Load ι) : Load ι where
  energy := response e B
  zero := response_zero e B
  homogeneous := response_smul e B

/-- Every linear welding acts on the complete trace space. No norm bound,
mode-preservation hypothesis, or finite-dimensional state is used. -/
def weld {ι κ : Type*} (W : Trace ι →ₗ[ℝ] Trace κ) (B : Load κ) : Load ι where
  energy := fun u => B (W u)
  zero := by simpa using B.zero
  homogeneous := by
    intro s u
    rw [map_smul, B.homogeneous]

theorem comparable_weld {ι κ : Type*} (W : Trace ι →ₗ[ℝ] Trace κ)
    {a : ℝ} {B D : Load κ} (h : Comparable a B D) :
    Comparable a (weld W B) (weld W D) :=
  ⟨fun u => h.1 (W u), fun u => h.2 (W u)⟩

theorem collar_rescale {ι : Type*} {e : ι → ℝ} {r a : ℝ}
    (he : ∀ i, 0 ≤ e i) (her : ∀ i, e i ≤ r) (hr : r < 1) (ha : 1 ≤ a)
    (u v : Trace ι) :
    collar e u ((radiusStep r a / a) • v) ≤
      ENNReal.ofReal ((radiusStep r a)^2) * collar e u v := by
  unfold collar
  rw [← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro i
  rw [← ENNReal.ofReal_mul (sq_nonneg (radiusStep r a))]
  apply ENNReal.ofReal_le_ofReal
  exact mode_rescale (he i) (her i) hr ha (u i) (v i)

private theorem response_comparison_one_way {ι : Type*} {e : ι → ℝ} {r a : ℝ}
    (he : ∀ i, 0 ≤ e i) (her : ∀ i, e i ≤ r) (hr0 : 0 ≤ r) (hr : r < 1)
    (ha : 1 ≤ a) (B D : Load ι)
    (h : ∀ v, D v ≤ ENNReal.ofReal (a^2) * B v) (u : Trace ι) :
    response e D u ≤ ENNReal.ofReal ((radiusStep r a)^2) * response e B u := by
  let b := radiusStep r a
  let k := b / a
  have ha0 : a ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num) ha)
  have hb1 : 1 ≤ b := radiusStep_one_le hr0 hr ha
  have hb0 : ENNReal.ofReal (b^2) ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero]
    exact not_le.mpr (sq_pos_of_ne_zero (ne_of_gt (lt_of_lt_of_le (by norm_num) hb1)))
  have hbt : ENNReal.ofReal (b^2) ≠ ∞ := ENNReal.ofReal_ne_top
  have hka : k^2 * a^2 = b^2 := by dsimp [k]; field_simp
  change response e D u ≤ ENNReal.ofReal (b^2) * ⨅ v, collar e u v + B v
  rw [ENNReal.mul_iInf_of_ne hb0 hbt]
  apply le_iInf
  intro v
  have hload : D (k • v) ≤ ENNReal.ofReal (b^2) * B v := by
    rw [D.homogeneous]
    calc
      ENNReal.ofReal (k^2) * D v ≤
          ENNReal.ofReal (k^2) * (ENNReal.ofReal (a^2) * B v) :=
        mul_le_mul_left' (h v) _
      _ = ENNReal.ofReal (b^2) * B v := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (sq_nonneg k), hka]
  calc
    response e D u ≤ collar e u (k • v) + D (k • v) := iInf_le _ _
    _ ≤ ENNReal.ofReal (b^2) * collar e u v + ENNReal.ofReal (b^2) * B v :=
      add_le_add (collar_rescale he her hr ha u v) hload
    _ = ENNReal.ofReal (b^2) * (collar e u v + B v) := (mul_add _ _ _).symm

/-- Sharp nonlinear comparison for the complete Fourier response. The proof
uses neither convexity of the loads nor existence of their minimizing traces. -/
theorem response_contraction {ι : Type*} {e : ι → ℝ} {r a : ℝ}
    (he : ∀ i, 0 ≤ e i) (her : ∀ i, e i ≤ r) (hr0 : 0 ≤ r) (hr : r < 1)
    (ha : 1 ≤ a) {B D : Load ι} (h : Comparable a B D) :
    Comparable (radiusStep r a) (response e B) (response e D) := by
  exact ⟨response_comparison_one_way he her hr0 hr ha B D h.1,
    response_comparison_one_way he her hr0 hr ha D B h.2⟩

/-- The same comparison across a welding that can mix every trace mode. -/
theorem welded_response_contraction {ι κ : Type*} {e : ι → ℝ} {r a : ℝ}
    (he : ∀ i, 0 ≤ e i) (her : ∀ i, e i ≤ r) (hr0 : 0 ≤ r) (hr : r < 1)
    (ha : 1 ≤ a) (W : Trace ι →ₗ[ℝ] Trace κ) {B D : Load κ}
    (h : Comparable a B D) :
    Comparable (radiusStep r a) (response e (weld W B)) (response e (weld W D)) :=
  response_contraction he her hr0 hr ha (comparable_weld W h)

/-- Squared norm of the normalized nonconstant Fourier trace. -/
def traceMass {ι : Type*} (u : Trace ι) : ℝ≥0∞ :=
  ∑' i, ENNReal.ofReal ((u i)^2)

def upperFactor (r : ℝ) : ℝ := (1+r^2)/(1-r^2)

def lowerFactor (r : ℝ) : ℝ := (1-r^2)/(1+r^2)

theorem upperFactor_pos {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    0 < upperFactor r :=
  div_pos (by positivity) (one_sub_sq_pos hr0 hr1)

theorem lowerFactor_pos {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    0 < lowerFactor r :=
  div_pos (one_sub_sq_pos hr0 hr1) (by positivity)

theorem upperFactor_one_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    1 ≤ upperFactor r := by
  apply (le_div_iff₀ (one_sub_sq_pos hr0 hr1)).mpr
  nlinarith [sq_nonneg r]

/-- A complete collar controls the entire incoming trace, independently
of its outgoing trace and of any attached load. -/
theorem collar_coercive {ι : Type*} {e : ι → ℝ} {r : ℝ}
    (he : ∀ i, 0 ≤ e i) (her : ∀ i, e i ≤ r) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (u v : Trace ι) :
    ENNReal.ofReal (lowerFactor r) * traceMass u ≤ collar e u v := by
  unfold traceMass collar
  rw [← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro i
  rw [← ENNReal.ofReal_mul (lowerFactor_pos hr0 hr1).le]
  exact ENNReal.ofReal_le_ofReal (mode_coercive (he i) (her i) hr1 (u i) (v i))

theorem response_coercive {ι : Type*} {e : ι → ℝ} {r : ℝ}
    (he : ∀ i, 0 ≤ e i) (her : ∀ i, e i ≤ r) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (B : Load ι) (u : Trace ι) :
    ENNReal.ofReal (lowerFactor r) * traceMass u ≤ response e B u := by
  apply le_iInf
  intro v
  exact (collar_coercive he her hr0 hr1 u v).trans (le_add_right le_rfl)

/-- The zero exit trace supplies a finite-energy competitor for every
finite-energy incoming trace, even when the terminal load is infinite elsewhere. -/
theorem response_upper {ι : Type*} {e : ι → ℝ} {r : ℝ}
    (he : ∀ i, 0 ≤ e i) (her : ∀ i, e i ≤ r) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (B : Load ι) (u : Trace ι) :
    response e B u ≤ ENNReal.ofReal (upperFactor r) * traceMass u := by
  calc
    response e B u ≤ collar e u 0 + B 0 := iInf_le _ _
    _ = collar e u 0 := by rw [B.zero, add_zero]
    _ ≤ ENNReal.ofReal (upperFactor r) * traceMass u := by
      unfold collar traceMass
      rw [← ENNReal.tsum_mul_left]
      apply ENNReal.tsum_le_tsum
      intro i
      rw [← ENNReal.ofReal_mul (upperFactor_pos hr0 hr1).le]
      exact ENNReal.ofReal_le_ofReal (mode_at_zero_le (he i) (her i) hr1 (u i))

theorem response_ne_top {ι : Type*} {e : ι → ℝ} {r : ℝ}
    (he : ∀ i, 0 ≤ e i) (her : ∀ i, e i ≤ r) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (B : Load ι) {u : Trace ι} (hu : traceMass u ≠ ∞) : response e B u ≠ ∞ :=
  ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hu)
    (response_upper he her hr0 hr1 B u)

/-- One collar makes even initially incomparable loads comparable, with
a factor independent of the loads and of the number of Fourier coordinates. -/
theorem universal_response_comparison {ι : Type*} {e : ι → ℝ} {r : ℝ}
    (he : ∀ i, 0 ≤ e i) (her : ∀ i, e i ≤ r) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (B D : Load ι) :
    Comparable (upperFactor r) (response e B) (response e D) := by
  have hcancel : (upperFactor r)^2 * lowerFactor r = upperFactor r := by
    have hm : 1-r^2 ≠ 0 := (one_sub_sq_pos hr0 hr1).ne'
    have hp : 1+r^2 ≠ 0 := by positivity
    unfold upperFactor lowerFactor
    field_simp
    <;> ring
  have hbound (B D : Load ι) (u : Trace ι) :
      response e D u ≤ ENNReal.ofReal ((upperFactor r)^2) * response e B u := by
    calc
      response e D u ≤ ENNReal.ofReal (upperFactor r) * traceMass u :=
        response_upper he her hr0 hr1 D u
      _ = ENNReal.ofReal ((upperFactor r)^2) *
          (ENNReal.ofReal (lowerFactor r) * traceMass u) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (sq_nonneg (upperFactor r)), hcancel]
      _ ≤ ENNReal.ofReal ((upperFactor r)^2) * response e B u :=
        mul_le_mul_left' (response_coercive he her hr0 hr1 B u) _
  exact ⟨hbound B D, hbound D B⟩

theorem comparable_mono {ι : Type*} {a b : ℝ} {B D : Trace ι → ℝ≥0∞}
    (ha : 0 ≤ a) (hab : a ≤ b) (h : Comparable a B D) : Comparable b B D := by
  have hs : ENNReal.ofReal (a^2) ≤ ENNReal.ofReal (b^2) :=
    ENNReal.ofReal_le_ofReal (AnnularModeContraction.sq_le_sq_of_nonneg ha hab)
  exact ⟨fun u => (h.1 u).trans (mul_le_mul_right' hs _),
    fun u => (h.2 u).trans (mul_le_mul_right' hs _)⟩

end
end AnnularVariationalResponse

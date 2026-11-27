import ParabolicTipRate
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.FieldSimp

/-!
# Exact coefficients of the physical period-three passage

The two coefficients of the actual polynomial return have product 49.
An exact polynomial remainder gives a uniform relative approximation on
shrinking neighborhoods of the parabolic point.
-/

namespace LoopsParabolic
open Set
noncomputable section

def passageA (a : ℝ) : ℝ := 11/2 - 2*a^2
def passageB (a : ℝ) : ℝ := 21/2 - 28*a - 14*a^2

theorem passage_root : ∃ a ∈ Icc (1/20:ℝ) (3/50), cubic a = 0 := by
  have hc : Continuous cubic := by unfold cubic; fun_prop
  exact intermediate_value_Icc (by norm_num) hc.continuousOn
    (show (0:ℝ) ∈ Icc (cubic (1/20)) (cubic (3/50)) by
      constructor <;> norm_num [cubic])

theorem passageA_ge_one {a : ℝ} (ha : a ∈ Icc (1/20:ℝ) (3/50)) :
    1 ≤ passageA a := by
  have hs := pow_le_pow_left₀ (show (0:ℝ) ≤ a by linarith [ha.1]) ha.2 2
  dsimp [passageA]
  nlinarith

theorem passageB_ge_one {a : ℝ} (ha : a ∈ Icc (1/20:ℝ) (3/50)) :
    1 ≤ passageB a := by
  have hs := pow_le_pow_left₀ (show (0:ℝ) ≤ a by linarith [ha.1]) ha.2 2
  dsimp [passageB]
  nlinarith [ha.2]

theorem passage_coefficients_mul {a : ℝ} (root : cubic a = 0) :
    passageA a * passageB a = 49 := by
  have h : passageA a * passageB a - 49 = cubic a * (-7*a/2-35/4) := by
    unfold passageA passageB cubic
    ring
  rw [root, zero_mul] at h
  linarith

theorem passageB_le_49 {a : ℝ} (ha : a ∈ Icc (1/20:ℝ) (3/50))
    (root : cubic a = 0) : passageB a ≤ 49 := by
  have hA := passageA_ge_one ha
  have hB := passageB_ge_one ha
  have hm := passage_coefficients_mul root
  have hb := mul_le_mul_of_nonneg_right hA (show 0 ≤ passageB a by linarith)
  nlinarith

private def pInner (y : ℝ) : ℝ := 7/4-y^2
private def pOuter (y : ℝ) : ℝ := (pInner y)^2-7/4
private def pL (y : ℝ) : ℝ := 2*pInner y-1
private def pW (y : ℝ) : ℝ := 7-4*y^2-4*y
private def pM (a x : ℝ) : ℝ := 18+8*a+4*x-24*a^2-24*a*x-8*x^2
private def pSpatial (a x : ℝ) : ℝ := pW (a+x)*(pM a x)^2/256
private def pParameter (y : ℝ) : ℝ := 2*pL y*pOuter y-1

private def remSpatial (a x : ℝ) : ℝ :=
  (-4*(2*a+x+1)*(pM a x)^2 +
    pW a*(4-24*a-8*x)*(pM a x+pM a 0))/256

private def remMixed (a x : ℝ) : ℝ :=
  -2*(2*a+x)*(2*pOuter (a+x)+pL a*(pInner (a+x)+pInner a))

private def remParameter (a t x : ℝ) : ℝ :=
  -(pL (a+x))^2-2*pOuter (a+x)+2*pL (a+x)*t-t^2

private theorem parameter_coefficient {a : ℝ} (root : cubic a = 0) :
    pParameter a = passageA a := by
  calc
    pParameter a = passageA a + cubic a *
        (a^3/2+a^2/4-9*a/8-1/16) := by
      unfold pParameter pL pOuter pInner passageA cubic
      ring
    _ = passageA a := by rw [root]; ring

private theorem spatial_coefficient {a : ℝ} (root : cubic a = 0) :
    pSpatial a 0 = passageB a := by
  calc
    pSpatial a 0 = passageB a + cubic a *
        (9*a^3/8+15*a^2/16-41*a/32+105/64) := by
      unfold pSpatial pW pM passageB cubic
      ring
    _ = passageB a := by rw [root]; ring

private theorem passage_expansion {a : ℝ} (root : cubic a = 0) (t x : ℝ) :
    H t (a+x)-(a+x)-(passageA a*t+passageB a*x^2) =
      x^3*remSpatial a x+t*x*remMixed a x+t^2*remParameter a t x := by
  have hshift : cubic (a+x) = x*pM a x := by
    calc
      cubic (a+x) = cubic a+x*pM a x := by unfold cubic pM; ring
      _ = x*pM a x := by rw [root]; ring
  have hs : H 0 (a+x)-(a+x) = x^2*pSpatial a x := by
    rw [parabolic_identity, hshift]
    unfold pSpatial pW
    ring
  have ht : H t (a+x)-H 0 (a+x) =
      t*pParameter (a+x)+t^2*remParameter a t x := by
    unfold H pParameter remParameter pL pOuter pInner
    ring
  have hsp : pSpatial a x = passageB a+x*remSpatial a x := by
    calc
      pSpatial a x = pSpatial a 0+x*remSpatial a x := by
        unfold pSpatial remSpatial pW pM
        ring
      _ = passageB a+x*remSpatial a x := by rw [spatial_coefficient root]
  have hpa : pParameter (a+x) = passageA a+x*remMixed a x := by
    calc
      pParameter (a+x) = pParameter a+x*remMixed a x := by
        unfold pParameter remMixed pL pOuter pInner
        ring
      _ = passageA a+x*remMixed a x := by rw [parameter_coefficient root]
  calc
    H t (a+x)-(a+x)-(passageA a*t+passageB a*x^2) =
        (H t (a+x)-H 0 (a+x))+(H 0 (a+x)-(a+x))-
          (passageA a*t+passageB a*x^2) := by ring
    _ = x^3*remSpatial a x+t*x*remMixed a x+t^2*remParameter a t x := by
      rw [ht, hs, hsp, hpa]
      ring

/-- One constant bounds the remainder for every allowed parabolic root,
parameter, and spatial displacement. No limiting normal form is assumed. -/
theorem passage_uniform_remainder :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ a, a ∈ Icc (1/20:ℝ) (3/50) → cubic a = 0 →
      ∀ t x : ℝ, t ∈ Icc 0 1 → |x| ≤ 1 →
      |H t (a+x)-(a+x)-(passageA a*t+passageB a*x^2)| ≤
        C*(t^2+t*|x|+|x|^3) := by
  let K : Set (ℝ × ℝ × ℝ) :=
    Icc (1/20:ℝ) (3/50) ×ˢ (Icc (0:ℝ) 1 ×ˢ Icc (-1:ℝ) 1)
  let f : (ℝ × ℝ × ℝ) → ℝ := fun z =>
    |remSpatial z.1 z.2.2|+|remMixed z.1 z.2.2|+
      |remParameter z.1 z.2.1 z.2.2|
  have hK : IsCompact K := isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hf : Continuous f := by
    dsimp [f, remSpatial, remMixed, remParameter, pW, pM, pL, pOuter, pInner]
    fun_prop
  obtain ⟨M, hM⟩ := (hK.image hf).bddAbove
  let C := max 1 M
  refine ⟨C, le_max_left _ _, ?_⟩
  intro a ha root t x ht hx
  have hx' : x ∈ Icc (-1:ℝ) 1 := abs_le.mp hx
  have hsum : |remSpatial a x|+|remMixed a x|+|remParameter a t x| ≤ C := by
    exact (hM (mem_image_of_mem f (show (a,t,x) ∈ K from ⟨ha, ht, hx'⟩))).trans
      (le_max_right 1 M)
  have hU : |remSpatial a x| ≤ C := by
    linarith [abs_nonneg (remMixed a x), abs_nonneg (remParameter a t x)]
  have hR : |remMixed a x| ≤ C := by
    linarith [abs_nonneg (remSpatial a x), abs_nonneg (remParameter a t x)]
  have hS : |remParameter a t x| ≤ C := by
    linarith [abs_nonneg (remSpatial a x), abs_nonneg (remMixed a x)]
  rw [passage_expansion root t x]
  calc
    |x^3*remSpatial a x+t*x*remMixed a x+t^2*remParameter a t x| ≤
        (|x^3*remSpatial a x|+|t*x*remMixed a x|)+|t^2*remParameter a t x| :=
      (abs_add_le _ _).trans (add_le_add_right (abs_add_le _ _) _)
    _ = |x| ^ 3 * |remSpatial a x| + t * |x| * |remMixed a x| +
        t^2 * |remParameter a t x| := by
      simp only [abs_mul, abs_pow, abs_of_nonneg ht.1]
    _ ≤ |x| ^ 3 * C + t * |x| * C + t^2*C :=
      add_le_add
        (add_le_add (mul_le_mul_of_nonneg_left hU (by positivity))
          (mul_le_mul_of_nonneg_left hR (mul_nonneg ht.1 (abs_nonneg x))))
        (mul_le_mul_of_nonneg_left hS (sq_nonneg t))
    _ = C*(t^2+t*|x|+|x|^3) := by ring

/-- The true return drift has a relative quadratic approximation uniform
over all roots in the specified parabolic bracket. -/
theorem passage_uniform_relative :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ a, a ∈ Icc (1/20:ℝ) (3/50) → cubic a = 0 →
      ∀ δ t x : ℝ, 0 ≤ δ → δ ≤ 1 → 0 ≤ t → t ≤ δ^2 → |x| ≤ δ →
      (1-C*δ)*(passageA a*t+passageB a*x^2) ≤ H t (a+x)-(a+x) ∧
        H t (a+x)-(a+x) ≤ (1+C*δ)*(passageA a*t+passageB a*x^2) := by
  obtain ⟨C, hC, herr⟩ := passage_uniform_remainder
  have hC0 : 0 ≤ C := by linarith
  refine ⟨2*C, by linarith, ?_⟩
  intro a ha root δ t x hδ hδ1 ht htδ hx
  have htδ' : t ≤ δ := htδ.trans (by nlinarith)
  have ht1 : t ≤ 1 := htδ'.trans hδ1
  have he := herr a ha root t x ⟨ht, ht1⟩ (hx.trans hδ1)
  have ht2 : t^2 ≤ δ*t := by nlinarith [mul_le_mul_of_nonneg_left htδ' ht]
  have htx : t*|x| ≤ δ*t := by nlinarith [mul_le_mul_of_nonneg_left hx ht]
  have hx3 : |x|^3 ≤ δ*x^2 := by
    calc
      |x|^3 = |x| * x^2 := by rw [pow_succ, sq_abs]; ring
      _ ≤ δ*x^2 := mul_le_mul_of_nonneg_right hx (sq_nonneg x)
  have hlead : t+x^2 ≤ passageA a*t+passageB a*x^2 := by
    have hA := mul_le_mul_of_nonneg_right (passageA_ge_one ha) ht
    have hB := mul_le_mul_of_nonneg_right (passageB_ge_one ha) (sq_nonneg x)
    nlinarith
  have hbound : C*(t^2+t*|x|+|x|^3) ≤
      2*C*δ*(passageA a*t+passageB a*x^2) := by
    calc
      C*(t^2+t*|x|+|x|^3) ≤ C*(2*δ*(t+x^2)) :=
        mul_le_mul_of_nonneg_left (by nlinarith [mul_nonneg hδ (sq_nonneg x)]) hC0
      _ = (2*C*δ)*(t+x^2) := by ring
      _ ≤ 2*C*δ*(passageA a*t+passageB a*x^2) :=
        mul_le_mul_of_nonneg_left hlead (by positivity)
  have habs := abs_le.mp (he.trans hbound)
  constructor <;> nlinarith only [habs.1, habs.2]

def passageScale (a t : ℝ) : ℝ := Real.sqrt ((passageA a / passageB a)*t)

theorem passage_scale_sq {a t : ℝ} (ha : a ∈ Icc (1/20:ℝ) (3/50))
    (ht : 0 ≤ t) : (passageScale a t)^2 = (passageA a / passageB a)*t := by
  have hA : 0 ≤ passageA a := le_trans (by norm_num) (passageA_ge_one ha)
  have hB : 0 ≤ passageB a := le_trans (by norm_num) (passageB_ge_one ha)
  exact Real.sq_sqrt (mul_nonneg (div_nonneg hA hB) ht)

theorem passage_scale_pos {a t : ℝ} (ha : a ∈ Icc (1/20:ℝ) (3/50))
    (ht : 0 < t) : 0 < passageScale a t := by
  have hA : 0 < passageA a := lt_of_lt_of_le (by norm_num) (passageA_ge_one ha)
  have hB : 0 < passageB a := lt_of_lt_of_le (by norm_num) (passageB_ge_one ha)
  exact Real.sqrt_pos.mpr (mul_pos (div_pos hA hB) ht)

theorem passage_scale_quadratic {a t : ℝ} (ha : a ∈ Icc (1/20:ℝ) (3/50))
    (ht : 0 ≤ t) (x : ℝ) :
    passageB a*((passageScale a t)^2+x^2) = passageA a*t+passageB a*x^2 := by
  have hB : passageB a ≠ 0 := ne_of_gt
    (lt_of_lt_of_le (by norm_num) (passageB_ge_one ha))
  rw [passage_scale_sq ha ht]
  field_simp [hB] <;> ring

theorem passage_scale_mul {a t : ℝ} (ha : a ∈ Icc (1/20:ℝ) (3/50))
    (root : cubic a = 0) (ht : 0 ≤ t) :
    passageB a * passageScale a t = 7*Real.sqrt t := by
  have hBpos : 0 < passageB a :=
    lt_of_lt_of_le (by norm_num) (passageB_ge_one ha)
  have hs : 0 ≤ passageScale a t := Real.sqrt_nonneg _
  have hmul := passage_coefficients_mul root
  have hquad : passageB a * (passageScale a t)^2 = passageA a*t := by
    simpa using passage_scale_quadratic ha ht (0:ℝ)
  have hsq : (passageB a * passageScale a t)^2 = 49*t := by
    calc
      (passageB a * passageScale a t)^2 =
          passageB a * (passageB a * (passageScale a t)^2) := by ring
      _ = passageB a*(passageA a*t) := by rw [hquad]
      _ = (passageA a*passageB a)*t := by ring
      _ = 49*t := by rw [hmul]
  have htsq := Real.sq_sqrt ht
  have hleft := mul_nonneg hBpos.le hs
  have hright := Real.sqrt_nonneg t
  nlinarith

end
end LoopsParabolic

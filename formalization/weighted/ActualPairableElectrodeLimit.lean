import ActualPairableElectrodes
import ActualParentMarks

/-!
# Normal form and limit of the actual pairable electrodes

All four physical electrodes share one positive scale.  Removing it
leaves a continuous two-variable expression in the return-to-target
radius ratio and the normalized return value.  The radius ratio tends to
zero for every sequence of actual tips, so no compactness of a family of
source domains or extremizing laminations is needed for this step.
-/

namespace ActualPairableElectrodeLimit

open Set Filter
open NearTwoTip NearTwoShooting LimitingCrestQuadraticReturn
open ActualPairableSource ActualPairableElectrodes
open scoped Topology

noncomputable section

def delta (c : ℝ) (p : ℕ) : ℝ := criticalValue c p / radius p

def normalizingScale (c : ℝ) (p : ℕ) : ℝ := (2 * Real.sqrt (delta c p))⁻¹

def normalizedElectrode (δ u : ℝ) : ℝ :=
  -Real.sqrt ((1-u)*(1-δ^2*u)) / ((1-δ)*(1-δ*u))

theorem delta_pos {p : ℕ} {c : ℝ} (hc : ActualTip p c) : 0 < delta c p :=
  div_pos hc.2.1 (radius_pos p)

theorem delta_lt_one {p : ℕ} (hp : 17 ≤ p) {c : ℝ} (hc : ActualTip p c) :
    delta c p < 1 := (div_lt_one (radius_pos p)).mpr (criticalValue_lt_radius hp hc)

theorem normalizingScale_pos {p : ℕ} {c : ℝ} (hc : ActualTip p c) :
    0 < normalizingScale c p := inv_pos.mpr
  (mul_pos (by norm_num) (Real.sqrt_pos.mpr (delta_pos hc)))

private theorem normal_denominator_pos {δ u : ℝ} (hδ : δ ∈ Ioo (0 : ℝ) 1)
    (hu : u < 1) : 0 < (1-δ)*(1-δ*u) := by
  have hmul := mul_lt_mul_of_pos_left hu hδ.1
  exact mul_pos (by linarith [hδ.2]) (by nlinarith [hδ.2])

private theorem normal_radicand_pos {δ u : ℝ} (hδ : δ ∈ Ioo (0 : ℝ) 1)
    (hu : u < 1) : 0 < (1-u)*(1-δ^2*u) := by
  have hsq : δ^2 < 1 := by nlinarith [mul_pos hδ.1 (sub_pos.mpr hδ.2)]
  have hm := mul_lt_mul_of_pos_left hu (sq_pos_of_pos hδ.1)
  exact mul_pos (by linarith) (by nlinarith)

theorem normalizedElectrode_neg {δ u : ℝ} (hδ : δ ∈ Ioo (0 : ℝ) 1) (hu : u < 1) :
    normalizedElectrode δ u < 0 :=
  div_neg_of_neg_of_pos (neg_neg_of_pos (Real.sqrt_pos.mpr (normal_radicand_pos hδ hu)))
    (normal_denominator_pos hδ hu)

private theorem cayley_difference_factor {R d y : ℝ} (hd : R-d ≠ 0) (hy : R-y ≠ 0) :
    SlitDiskCayley.realMap R (-y) - SlitDiskCayley.realMap R (-d) =
      4*R*(d-y)*(R^2-d*y) / (((R-d)*(R-y))^2) := by
  unfold SlitDiskCayley.realMap
  simp only [sub_neg_eq_add,← sub_eq_add_neg]
  field_simp [hd,hy]
  ring

private theorem sqrt_cayley_difference {R d y : ℝ} (hR : 0 < R) (hd : 0 < d)
    (hdR : d < R) (hyd : y < d) :
    Real.sqrt (SlitDiskCayley.realMap R (-y) - SlitDiskCayley.realMap R (-d)) =
      2 * Real.sqrt (d/R) * Real.sqrt ((1-y/d)*(1-(d/R)^2*(y/d))) /
        ((1-d/R)*(1-(d/R)*(y/d))) := by
  have hδ : d/R ∈ Ioo (0 : ℝ) 1 := ⟨div_pos hd hR,(div_lt_one hR).mpr hdR⟩
  have hu : y/d < 1 := (div_lt_one hd).mpr hyd
  have hden := normal_denominator_pos hδ hu
  have hrad := normal_radicand_pos hδ hu
  have hRd : R-d ≠ 0 := (sub_pos.mpr hdR).ne'
  have hRy : R-y ≠ 0 := (sub_pos.mpr (hyd.trans hdR)).ne'
  have hsq : SlitDiskCayley.realMap R (-y) - SlitDiskCayley.realMap R (-d) =
      (2 * Real.sqrt (d/R) * Real.sqrt ((1-y/d)*(1-(d/R)^2*(y/d))) /
        ((1-d/R)*(1-(d/R)*(y/d))))^2 := by
    conv_rhs => rw [div_pow,mul_pow,mul_pow,Real.sq_sqrt hδ.1.le,Real.sq_sqrt hrad.le]
    rw [cayley_difference_factor hRd hRy]
    field_simp [hR.ne',hd.ne',hRd,hRy]
    ring
  rw [hsq,Real.sqrt_sq_eq_abs,abs_of_pos]
  exact div_pos (mul_pos (mul_pos (by norm_num) (Real.sqrt_pos.mpr hδ.1))
    (Real.sqrt_pos.mpr hrad)) hden

/-- Exact common-scale normalization of a squared-Cayley electrode. -/
theorem normalized_cayley_electrode {R d y : ℝ} (hR : 0 < R) (hd : 0 < d)
    (hdR : d < R) (hyd : y < d) :
    (2 * Real.sqrt (d/R))⁻¹ *
      (-Real.sqrt (SlitDiskCayley.realMap R (-y) - SlitDiskCayley.realMap R (-d))) =
      normalizedElectrode (d/R) (y/d) := by
  rw [sqrt_cayley_difference hR hd hdR hyd]
  unfold normalizedElectrode
  have hs : Real.sqrt (d/R) ≠ 0 := (Real.sqrt_pos.mpr (div_pos hd hR)).ne'
  have hcancel : (2 * Real.sqrt (d/R))⁻¹ * (2 * Real.sqrt (d/R)) = 1 :=
    inv_mul_cancel₀ (mul_ne_zero (by norm_num) hs)
  calc
    _ = -(((2 * Real.sqrt (d/R))⁻¹ * (2 * Real.sqrt (d/R))) *
      Real.sqrt ((1-y/d)*(1-(d/R)^2*(y/d))) / ((1-d/R)*(1-(d/R)*(y/d)))) := by ring
    _ = _ := by rw [hcancel,one_mul,neg_div]

theorem scaled_electrodeAt_eq {p : ℕ} (hp : 17 ≤ p) {c y : ℝ}
    (hc : ActualTip p c) (hy : y < criticalValue c p) :
    normalizingScale c p * electrodeAt c p y =
      normalizedElectrode (delta c p) (y / criticalValue c p) :=
  normalized_cayley_electrode (radius_pos p) hc.2.1 (criticalValue_lt_radius hp hc) hy

@[simp] theorem normalizedElectrode_zero (u : ℝ) :
    normalizedElectrode 0 u = -Real.sqrt (1-u) := by simp [normalizedElectrode]

/-- Joint continuity at zero radius ratio includes the complete limiting
electrode, with no ordering premise needed for the continuity itself. -/
theorem normalizedElectrode_continuousAt_zero (u : ℝ) :
    ContinuousAt (fun q : ℝ × ℝ => normalizedElectrode q.1 q.2) (0,u) := by
  have hn : Continuous (fun q : ℝ × ℝ => -Real.sqrt ((1-q.2)*(1-q.1^2*q.2))) := by
    fun_prop
  have hd : Continuous (fun q : ℝ × ℝ => (1-q.1)*(1-q.1*q.2)) := by fun_prop
  exact hn.continuousAt.div hd.continuousAt (by norm_num)

theorem tendsto_normalizedElectrode {ι : Type*} {l : Filter ι} {δ u : ι → ℝ} {v : ℝ}
    (hδ : Tendsto δ l (𝓝 0)) (hu : Tendsto u l (𝓝 v)) :
    Tendsto (fun n => normalizedElectrode (δ n) (u n)) l (𝓝 (-Real.sqrt (1-v))) := by
  simpa only [normalizedElectrode_zero,Function.comp_def] using
    (normalizedElectrode_continuousAt_zero v).tendsto.comp (hδ.prodMk_nhds hu)

theorem delta_eq_inv_targetRadius (c : ℝ) (p : ℕ) :
    delta c p = (ActualParentMarks.targetRadius c p)⁻¹ := by
  simp only [delta,radius,ActualParentMarks.targetRadius,inv_div]

theorem delta_tendsto (c : ℕ → ℝ) (hc : ∀ n, ActualTip (n+17) (c n)) :
    Tendsto (fun n => delta (c n) (n+17)) atTop (𝓝 0) := by
  simp only [delta_eq_inv_targetRadius]
  exact tendsto_inv_atTop_zero.comp (ActualParentMarks.targetRadius_tendsto c hc)

/-- Every convergent normalized actual return value gives a convergent
normalized physical electrode. -/
theorem normalized_electrode_tendsto (c y : ℕ → ℝ)
    (hc : ∀ n, ActualTip (n+17) (c n)) {v : ℝ}
    (hy : ∀ n, y n < criticalValue (c n) (n+17))
    (hlim : Tendsto (fun n => y n / criticalValue (c n) (n+17)) atTop (𝓝 v)) :
    Tendsto (fun n => normalizingScale (c n) (n+17) * electrodeAt (c n) (n+17) (y n))
      atTop (𝓝 (-Real.sqrt (1-v))) := by
  convert tendsto_normalizedElectrode (delta_tendsto c hc) hlim using 1
  funext n
  exact scaled_electrodeAt_eq (by omega) (hc n) (hy n)

end
end ActualPairableElectrodeLimit

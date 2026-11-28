import ActualPairableClosedChart

/-!
# Explicit actual orbit formulas for the four pairable electrodes

The regular source coordinate at each negative physical electrode is the
negative square root of its squared-Cayley return value. Thus the final
quadrilateral periods depend explicitly on the actual critical iterates,
the actual positive fixed point, and the physical target radius.
-/

namespace ActualPairableElectrodes

open Set NearTwoTip NearTwoShooting LimitingCrestQuadraticReturn
open ActualPairableSource ActualPairablePorts ActualPairableCoordinate
open ActualPairableClosedChart
noncomputable section

def electrodeAt (c : ℝ) (p : ℕ) (y : ℝ) : ℝ :=
  -Real.sqrt (SlitDiskCayley.realMap (radius p) (-y) -
    SlitDiskCayley.realMap (radius p) (-criticalValue c p))

theorem realCoordinate_eq_electrodeAt {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {x y : ℝ} (hx : (x:ℂ) ∈ source c p) (hx0 : x < 0)
    (hF : returnMap c p (x:ℂ) = (y:ℂ)) :
    realCoordinate c p x = electrodeAt c p y := by
  have him := coordinate_real_im hp hc hx (by simp)
  have hneg := coordinate_real_neg hp hc hx hx0
  change realCoordinate c p x < 0 at hneg
  have hs := congrArg Complex.re (coordinate_sq hp hc hx)
  rw [hF] at hs
  simp only [SlitDiskCutChart.shift,← Complex.ofReal_neg,SlitDiskCayley.map_ofReal,
    Complex.sub_re,Complex.ofReal_re,pow_two,Complex.mul_re,him,mul_zero,sub_zero] at hs
  have hs' : SlitDiskCayley.realMap (radius p) (-y) -
      SlitDiskCayley.realMap (radius p) (-criticalValue c p) =
      (realCoordinate c p x)^2 := by
    change _ = (coordinate c p (x:ℂ)).re^2
    nlinarith [hs]
  unfold electrodeAt
  rw [hs',Real.sqrt_sq_eq_abs,abs_of_neg hneg,neg_neg]

theorem electrode0_eq {p : ℕ} (hp : 17 ≤ p) {c : ℝ} (hc : ActualTip p c) :
    electrode0 c p = electrodeAt c p (cut c p 5) := by
  have hx := (physical_endpoints_mem_interval hp hc).1
  have ho := source_ports_ordered hp hc
  apply realCoordinate_eq_electrodeAt hp hc (negativeInterval_mem_source hp hc hx)
    (ho.2.1.trans (ho.2.2.1.trans (ho.2.2.2.1.trans ho.2.2.2.2)))
  simpa only [Complex.ofReal_neg] using returnMap_neg_cut c (by omega : 1 ≤ p) 4

theorem electrode1_eq {p : ℕ} (hp : 17 ≤ p) {c : ℝ} (hc : ActualTip p c) :
    electrode1 c p = electrodeAt c p (cut c p 3) := by
  have hx := (physical_endpoints_mem_interval hp hc).2.1
  have ho := source_ports_ordered hp hc
  exact realCoordinate_eq_electrodeAt hp hc (negativeInterval_mem_source hp hc hx)
    (ho.2.2.1.trans (ho.2.2.2.1.trans ho.2.2.2.2)) (returnMap_cut c p 2)

theorem electrode2_eq {p : ℕ} (hp : 17 ≤ p) {c : ℝ} (hc : ActualTip p c) :
    electrode2 c p = electrodeAt c p (cut c p 6) := by
  have hx := (physical_endpoints_mem_interval hp hc).2.2.1
  have ho := source_ports_ordered hp hc
  exact realCoordinate_eq_electrodeAt hp hc (negativeInterval_mem_source hp hc hx)
    (ho.2.2.2.1.trans ho.2.2.2.2) (returnMap_cut c p 5)

theorem electrode3_eq {p : ℕ} (hp : 17 ≤ p) {c : ℝ} (hc : ActualTip p c) :
    electrode3 hp hc = electrodeAt c p (alpha hp hc) := by
  have hx := (physical_endpoints_mem_interval hp hc).2.2.2
  apply realCoordinate_eq_electrodeAt hp hc (negativeInterval_mem_source hp hc hx)
    (source_ports_ordered hp hc).2.2.2.2
  simpa only [Complex.ofReal_neg] using returnMap_neg_alpha hp hc

/-- The exact candidate value, expressed entirely through actual return
values and real square roots, followed by the specified cubic integrals. -/
def periodRatio {p : ℕ} (hp : 17 ≤ p) {c : ℝ} (hc : ActualTip p c) : ℝ :=
  SlitFourPointChart.height (electrodeAt c p (cut c p 5))
    (electrodeAt c p (cut c p 3)) (electrodeAt c p (cut c p 6))
      (electrodeAt c p (alpha hp hc)) /
  (2*SlitFourPointChart.width (electrodeAt c p (cut c p 5))
    (electrodeAt c p (cut c p 3)) (electrodeAt c p (cut c p 6))
      (electrodeAt c p (alpha hp hc)))

theorem height_div_width_eq {p : ℕ} (hp : 17 ≤ p) {c : ℝ} (hc : ActualTip p c) :
    ActualPairableClosedChart.height hp hc/(2*ActualPairableClosedChart.width hp hc) =
      periodRatio hp hc := by
  unfold ActualPairableClosedChart.height ActualPairableClosedChart.width periodRatio
  rw [electrode0_eq hp hc,electrode1_eq hp hc,electrode2_eq hp hc,electrode3_eq hp hc]

theorem periodRatio_pos {p : ℕ} (hp : 17 ≤ p) {c : ℝ} (hc : ActualTip p c) :
    0 < periodRatio hp hc := by
  rw [← height_div_width_eq hp hc]
  exact div_pos (height_pos hp hc) (mul_pos (by norm_num) (width_pos hp hc))

end
end ActualPairableElectrodes

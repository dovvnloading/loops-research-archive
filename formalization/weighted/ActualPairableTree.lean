import ActualPairableMarking

/-!
# The literal source slit is the complete pullback of the parent slit

The equality concerns the whole archived component.  No additional
nonreal branch or component is removed when the source slit is used in
the pairable proper-restriction definition.
-/

namespace ActualPairableTree

open Set Function Metric MarkedSlitTransport
open NearTwoTip LimitingCrestQuadraticReturn
open ActualPairableSource ActualPairablePorts ActualPairableMarking

noncomputable section

theorem realReturn_neg_abs (c : ℝ) {p : ℕ} (hp : 1 ≤ p) (x : ℝ) :
    realReturn c p (-|x|) = realReturn c p x := by
  by_cases hx : 0 ≤ x
  · simp only [abs_of_nonneg hx,realReturn,Complex.ofReal_neg,returnMap_neg c hp]
  · simp only [abs_of_nonpos (le_of_not_ge hx),neg_neg]

theorem realReturn_negative_criticalValue {p : ℕ} (hp : 17 ≤ p) {c : ℝ} :
    realReturn c p (-criticalValue c p) = cut c p 2 := by
  have h := congrArg Complex.re (returnMap_neg_cut c (p := p) (by omega) 1)
  simpa only [realReturn,cut,one_mul,Complex.ofReal_re,Complex.ofReal_neg] using h

/-- Inside the actual source, a real output at or to the left of the
critical value can only come from the real axis. -/
theorem real_of_real_image_le_criticalValue {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {z : ℂ} (hz : z ∈ source c p)
    (him : (returnMap c p z).im = 0) (hre : (returnMap c p z).re ≤ criticalValue c p) : z.im = 0 := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · have hu : -z ∈ upperSource c p := ⟨source_neg hp hc hz,by simpa using neg_pos.mpr hneg⟩
    have hreal : (returnMap c p (-z)).im = 0 := by rwa [returnMap_neg c (by omega)]
    have h := criticalValue_lt_returnMap_re_of_upper_real hp hc hu hreal
    rw [returnMap_neg c (by omega)] at h
    exact (not_lt_of_ge hre) h
  · exact (not_lt_of_ge hre) (criticalValue_lt_returnMap_re_of_upper_real hp hc ⟨hz,hpos⟩ him)

theorem real_source_parentSlit_iff {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {z : ℂ} (hz : z ∈ source c p) (him : z.im = 0) :
    returnMap c p z ∈ (parentMarking hp hc).slit ↔ z ∈ sourceSlit c p := by
  have he : z = (z.re : ℂ) := by apply Complex.ext <;> simp [him]
  have hn : |z.re| < radius p := by
    have h := norm_lt_radius_of_mem_source hp hc hz
    rw [he] at h
    simpa only [Complex.norm_real,Real.norm_eq_abs] using h
  have hdmem : -criticalValue c p ∈ Icc (-radius p) 0 :=
    ⟨by linarith [criticalValue_lt_radius hp hc],by linarith [hc.2.1]⟩
  have hnmem : -|z.re| ∈ Icc (-radius p) 0 :=
    ⟨by linarith,neg_nonpos.mpr (abs_nonneg _)⟩
  have hv : realReturn c p (-|z.re|) = (returnMap c p z).re := by
    rw [realReturn_neg_abs c (by omega)]
    change (returnMap c p (z.re : ℂ)).re = _
    rw [← he]
  have hiff := (realReturn_strictMonoOn hp hc).le_iff_le hdmem hnmem
  rw [realReturn_negative_criticalValue hp,hv] at hiff
  have hupper := returnMap_re_le_of_real hp hc hz him
  have hreal := returnMap_real_of_real c p him
  constructor
  · intro hf
    have habs : |z.re| ≤ criticalValue c p := by
      have h := hiff.mp hf.2.1
      linarith
    exact ⟨him,abs_le.mp habs⟩
  · intro hs
    refine ⟨hreal,?_,hupper⟩
    apply hiff.mpr
    have ha := abs_le.mpr hs.2
    linarith

/-- The removed source slit is exactly the complete parent-slit pullback
inside the actual archived polynomial restriction. -/
theorem source_inter_preimage_parentSlit {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) :
    source c p ∩ returnMap c p ⁻¹' (parentMarking hp hc).slit = sourceSlit c p := by
  ext z
  constructor
  · intro hz
    have hi := real_of_real_image_le_criticalValue hp hc hz.1 hz.2.1 hz.2.2.2
    exact (real_source_parentSlit_iff hp hc hz.1 hi).mp hz.2
  · intro hz
    have hs := sourceSlit_subset_source hp hc hz
    exact ⟨hs,(real_source_parentSlit_iff hp hc hs hz.1).mpr hz⟩

theorem parentSlit_subset_disk {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) : (parentMarking hp hc).slit ⊆ ball 0 (radius p) :=
  (parentSlit_subset_sourceSlit hp hc).trans
    ((sourceSlit_subset_source hp hc).trans (source_subset_disk hp hc))

/-- The complete source slit covers exactly the literal parent slit interval. -/
theorem sourceSlit_image {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) : returnMap c p '' sourceSlit c p = (parentMarking hp hc).slit := by
  apply Subset.antisymm
  · rintro _ ⟨z,hz,rfl⟩
    exact ((source_inter_preimage_parentSlit hp hc).symm ▸ hz).2
  · intro w hw
    obtain ⟨z,hz,he⟩ := (returnMap_image_source hp hc).symm ▸ (parentSlit_subset_disk hp hc hw)
    refine ⟨z,?_,he⟩
    rw [← source_inter_preimage_parentSlit hp hc]
    refine ⟨hz,?_⟩
    change returnMap c p z ∈ (parentMarking hp hc).slit
    rwa [he]

/-- The actual slit source covers the actual slit target, with the
removed sets identified rather than assigned. -/
theorem slit_source_image {p : ℕ} (hp : 17 ≤ p) {c : ℝ} (hc : ActualTip p c) :
    returnMap c p '' (source c p \ sourceSlit c p) = ball 0 (radius p) \ (parentMarking hp hc).slit := by
  apply Subset.antisymm
  · rintro _ ⟨z,⟨hz,hnot⟩,rfl⟩
    refine ⟨returnMap_mem_ball hp hz,?_⟩
    intro hf
    exact hnot ((source_inter_preimage_parentSlit hp hc) ▸ (show z ∈ source c p ∩ returnMap c p ⁻¹'
      (parentMarking hp hc).slit from ⟨hz,hf⟩))
  · intro w hw
    obtain ⟨z,hz,he⟩ := (returnMap_image_source hp hc).symm ▸ hw.1
    refine ⟨z,⟨hz,?_⟩,he⟩
    intro hs
    have hf := mem_image_of_mem (returnMap c p) hs
    rw [sourceSlit_image hp hc,he] at hf
    exact hw.2 hf

end
end ActualPairableTree

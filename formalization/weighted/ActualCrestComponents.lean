import ActualCrestPaths

/-!
# Maximal surviving components of the fourth actual restriction

The selected q arc is an entire connected component of the fourth
restriction of the full semicircle.  It is not chosen as a smaller
proper subarc.  The missing parameter is the unique actual crossing,
whose third image lies on the source slit.
-/

namespace ActualCrestComponents

open Set Function Filter
open NearTwoTip LimitingCrestQuadraticReturn LimitingCrest
open GlobalCrestCrossing GlobalCrestClassification ActualCrestPaths

noncomputable section

def fourthSurvivingParameters (c : ℝ) (p : ℕ) (s : ℝ) : Set ℝ :=
  {u | u ∈ Ioo (-1 : ℝ) 1 ∧
    ((normalizedReturn c p)^[3]) (circlePoint s u) ∈ slitSource c p}

theorem fourth_survivors_eq_punctured {p : ℕ} (hp : 17 ≤ p) {c s : ℝ}
    (hc : ActualTip p c) (hS : StrictSupport c p) (F : Family p c)
    (hs : s ∈ Icc (1/16 : ℝ) (133/2000)) (hg : terminalGate F s) :
    fourthSurvivingParameters c p s = Ioo (-1 : ℝ) 1 \ {realAngle F s} := by
  ext u
  constructor
  · rintro ⟨hu,hmem⟩
    exact ⟨hu,(full_arc_source_membership hp hc hS F hs hg hu).2.mp hmem⟩
  · rintro ⟨hu,hne⟩
    exact ⟨hu,(full_arc_source_membership hp hc hS F hs hg hu).2.mpr hne⟩

theorem fourth_survivors_eq_two_intervals {p : ℕ} (hp : 17 ≤ p) {c s : ℝ}
    (hc : ActualTip p c) (hS : StrictSupport c p) (F : Family p c)
    (hs : s ∈ Icc (1/16 : ℝ) (133/2000)) (hg : terminalGate F s) :
    fourthSurvivingParameters c p s =
      Ioo (-1 : ℝ) (realAngle F s) ∪ Ioo (realAngle F s) 1 := by
  rw [fourth_survivors_eq_punctured hp hc hS F hs hg]
  ext u
  constructor
  · rintro ⟨hu,hne⟩
    rcases lt_or_gt_of_ne (show u ≠ realAngle F s from hne) with h | h
    · exact Or.inl ⟨hu.1,h⟩
    · exact Or.inr ⟨h,hu.2⟩
  · rintro (hu | hu)
    · have ha := (realAngle_mem F s).2
      exact ⟨⟨hu.1,by linarith [hu.2]⟩,ne_of_lt hu.2⟩
    · have ha := (realAngle_mem F s).1
      exact ⟨⟨by linarith [hu.1],hu.2⟩,ne_of_gt hu.1⟩

/-- Every basepoint on the q side selects the same maximal component.
Any connected surviving set crossing to the other side would contain
the excluded actual crossing by the real intermediate-value property. -/
theorem fourth_q_component {p : ℕ} (hp : 17 ≤ p) {c s b : ℝ}
    (hc : ActualTip p c) (hS : StrictSupport c p) (F : Family p c)
    (hs : s ∈ Icc (1/16 : ℝ) (133/2000)) (hg : terminalGate F s)
    (hb : b ∈ Ioo (realAngle F s) 1) :
    connectedComponentIn (fourthSurvivingParameters c p s) b =
      Ioo (realAngle F s) 1 := by
  have he := fourth_survivors_eq_punctured hp hc hS F hs hg
  have ha := realAngle_mem F s
  have hbS : b ∈ fourthSurvivingParameters c p s := by
    rw [he]
    exact ⟨⟨by linarith [ha.1,hb.1],hb.2⟩,ne_of_gt hb.1⟩
  apply Subset.antisymm
  · intro u hu
    have huS := connectedComponentIn_subset (fourthSurvivingParameters c p s) b hu
    rw [he] at huS
    refine ⟨?_,huS.1.2⟩
    by_contra h
    have hcross : realAngle F s ∈
        connectedComponentIn (fourthSurvivingParameters c p s) b :=
      isPreconnected_connectedComponentIn.Icc_subset hu (mem_connectedComponentIn hbS)
        ⟨le_of_not_gt h,hb.1.le⟩
    have hbad := connectedComponentIn_subset (fourthSurvivingParameters c p s) b hcross
    rw [he] at hbad
    exact hbad.2 rfl
  · apply isPreconnected_Ioo.subset_connectedComponentIn hb
    intro u hu
    rw [he]
    exact ⟨⟨by linarith [ha.1,hu.1],hu.2⟩,ne_of_gt hu.1⟩

theorem fourth_q_midpoint_component {p : ℕ} (hp : 17 ≤ p) {c s : ℝ}
    (hc : ActualTip p c) (hS : StrictSupport c p) (F : Family p c)
    (hs : s ∈ Icc (1/16 : ℝ) (133/2000)) (hg : terminalGate F s) :
    connectedComponentIn (fourthSurvivingParameters c p s) ((realAngle F s+1)/2) =
      Ioo (realAngle F s) 1 := by
  apply fourth_q_component hp hc hS F hs hg
  have ha := (realAngle_mem F s).2
  constructor <;> linarith

/-- The entire third-image q arc is the image of the maximal surviving
parameter component. Full-ancestor injectivity gives a one-to-one
parametrization of this image. -/
theorem third_q_component_image {p : ℕ} (hp : 17 ≤ p) {c s : ℝ}
    (hc : ActualTip p c) (hS : StrictSupport c p) (F : Family p c)
    (hs : s ∈ Icc (1/16 : ℝ) (133/2000)) (hg : terminalGate F s) :
    (fun u : ℝ => ((normalizedReturn c p)^[3]) (circlePoint s u)) ''
        connectedComponentIn (fourthSurvivingParameters c p s) ((realAngle F s+1)/2) =
      (fun u : ℝ => ((normalizedReturn c p)^[3]) (circlePoint s u)) ''
        Ioo (realAngle F s) 1 ∧
    InjOn (fun u : ℝ => ((normalizedReturn c p)^[3]) (circlePoint s u))
      (Ioo (realAngle F s) 1) := by
  refine ⟨by rw [fourth_q_midpoint_component hp hc hS F hs hg],?_⟩
  apply (full_arc_iterate_injective hp hc hS F hs (by norm_num : 3 ≤ 4)).mono
  intro u hu
  have ha := (realAngle_mem F s).1
  exact ⟨by linarith [hu.1],hu.2.le⟩

/-- The maximal-component conclusion is simultaneous for every actual
parameter at all sufficiently large return indices. -/
theorem eventually_all_fourth_q_components :
    ∀ᶠ n : ℕ in atTop, ∀ c : ℝ, ActualTip (n+17) c →
      ∀ F : Family (n+17) c, ∀ s ∈ Icc (1/16 : ℝ) (133/2000),
        terminalGate F s →
        fourthSurvivingParameters c (n+17) s =
          Ioo (-1 : ℝ) (realAngle F s) ∪ Ioo (realAngle F s) 1 ∧
        connectedComponentIn (fourthSurvivingParameters c (n+17) s)
            ((realAngle F s+1)/2) = Ioo (realAngle F s) 1 := by
  filter_upwards [eventually_all_strict_support] with n hn
  intro c hc F s hs hg
  exact ⟨fourth_survivors_eq_two_intervals (by omega) hc (hn c hc) F hs hg,
    fourth_q_midpoint_component (by omega) hc (hn c hc) F hs hg⟩

end
end ActualCrestComponents

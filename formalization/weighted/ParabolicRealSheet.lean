import ParabolicDisjoint

/-! The intermediate images of the closed restrictive interval occupy one
strict real sign sheet at each phase. The complete return covers the interval. -/

namespace LoopsParabolic
open Set Function
noncomputable section

theorem phase_sign_agrees {t e x : ℝ} {k j : ℕ} (hs : Shot k t e)
    (hx : x ∈ Icc (-e) e) (hj : 0 < j) (hp : j < 3*(k+2)) :
    0 < (quad (-7/4+t))^[j] x * (quad (-7/4+t))^[j] 0 := by
  let F := (quad (-7/4+t))^[j]
  have hc : Continuous F := Continuous.iterate
    (show Continuous (quad (-7/4+t)) by unfold quad; fun_prop) _
  have hz : (0:ℝ) ∈ Icc (-e) e := ⟨by linarith [hs.e_pos],hs.e_pos.le⟩
  have hmiss : (0:ℝ) ∉ F '' Icc (-e) e := by
    rintro ⟨z,hz',hz0⟩
    apply (first_return_on_interval hs hz').2 j hj hp
    change F z ∈ Icc (-e) e
    rwa [hz0]
  have exclude {a b : ℝ} (ha : a ∈ Icc (-e) e) (hb : b ∈ Icc (-e) e)
      (haa : F a ≤ 0) (hbb : 0 ≤ F b) : False :=
    hmiss (isPreconnected_Icc.intermediate_value ha hb hc.continuousOn ⟨haa,hbb⟩)
  change 0 < F x * F 0
  by_cases h : F 0 ≤ 0
  · have h0 : F 0 < 0 := lt_of_le_of_ne h (fun heq => hmiss ⟨0,hz,heq⟩)
    exact mul_pos_of_neg_of_neg (lt_of_not_ge (fun h' => exclude hz hx h h')) h0
  · have h0 : 0 < F 0 := lt_of_not_ge h
    exact mul_pos (lt_of_not_ge (fun h' => exclude hx hz h' h0.le)) h0

theorem return_image_eq {t e : ℝ} {k : ℕ} (hs : Shot k t e) :
    (quad (-7/4+t))^[3*(k+2)] '' Icc (-e) e = Icc (-e) e := by
  apply subset_antisymm
  · rintro _ ⟨x,hx,rfl⟩
    exact return_mem hs hx
  · have h := (full_branches hs).2.2.2
    calc
      Icc (-e) e = (quad (-7/4+t))^[3*(k+2)] '' Icc 0 e := h.symm
      _ ⊆ _ := image_mono (Icc_subset_Icc (by linarith [hs.e_pos]) le_rfl)

#print axioms phase_sign_agrees
#print axioms return_image_eq

end
end LoopsParabolic

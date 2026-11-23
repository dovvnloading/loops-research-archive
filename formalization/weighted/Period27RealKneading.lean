import Period27RealExactPeriod

/-!
# The physical real orbit underlying the period-27 kneading table

Every parameter in the isolated bracket has the indicated first 26 signs
and the displayed strict order through time 26. At its unique center the
critical orbit closes at time 27. Ray landing requires a separate theorem.
-/

namespace LoopsRealPeriod27

open LoopsFormal.Period27 LoopsFormal.Paper2

noncomputable section

private theorem sign_bounds (j : Fin 26) :
    if negatives.getD j.val false then (orbitCertificate (j.val + 1)).hi < 0
    else 0 < (orbitCertificate (j.val + 1)).lo := by
  revert j
  decide +kernel

private theorem adjacent_bounds (j : Fin 26) :
    (orbitCertificate (realIncreasingIndices.getD j.val 0)).hi <
      (orbitCertificate (realIncreasingIndices.getD (j.val + 1) 0)).lo := by
  revert j
  decide +kernel

private theorem scale_pos : (0 : ℝ) < (unit : ℝ) := by
  exact_mod_cast (show (0 : Int) < unit by decide +kernel)

/-- Both signs are strict and concern the physical iterates of the quadratic. -/
theorem physical_sign_at (c : ℝ) (hc : c ∈ Set.Icc left right) (j : Fin 26) :
    if negatives.getD j.val false then iterate (quadratic c) (j.val + 1) 0 < 0
    else 0 < iterate (quadratic c) (j.val + 1) 0 := by
  rw [← polynomial_eq_quadratic_iterate]
  have hs := sign_bounds j
  obtain ⟨hl, hu⟩ := real_orbit_bounds (j.val + 1) c hc
  cases h : negatives.getD j.val false <;> simp only [h, Bool.false_eq_true,
    if_false, if_true] at hs ⊢
  · exact lt_of_lt_of_le (div_pos (by exact_mod_cast hs) scale_pos) hl
  · exact lt_of_le_of_lt hu (div_neg_of_neg_of_pos (by exact_mod_cast hs) scale_pos)

/-- Each adjacent pair in the complete 27-index permutation is ordered
in the real dynamical plane, uniformly on the closed parameter bracket. -/
theorem physical_adjacent_order (c : ℝ) (hc : c ∈ Set.Icc left right) (j : Fin 26) :
    iterate (quadratic c) (realIncreasingIndices.getD j.val 0) 0 <
      iterate (quadratic c) (realIncreasingIndices.getD (j.val + 1) 0) 0 := by
  rw [← polynomial_eq_quadratic_iterate, ← polynomial_eq_quadratic_iterate]
  apply lt_of_le_of_lt (real_orbit_upper _ c hc)
  apply lt_of_lt_of_le _ (real_orbit_lower _ c hc)
  apply (div_lt_div_iff_of_pos_right scale_pos).mpr
  exact_mod_cast adjacent_bounds j

/-- Construct the kneading word from the physical orbit by testing its sign
at each time 1 through 26. The terminal digit uses the archive's convention. -/
theorem physical_kneading_numerator (c : ℝ) (hc : c ∈ Set.Icc left right) :
    binaryValue (kneading false (List.ofFn fun j : Fin 26 =>
      decide (iterate (quadratic c) (j.val + 1) 0 < 0))) = 59914011 := by
  have heq : (fun j : Fin 26 => decide (iterate (quadratic c) (j.val + 1) 0 < 0)) =
      (fun j : Fin 26 => negatives.getD j.val false) := by
    funext j
    have hs := physical_sign_at c hc j
    cases h : negatives.getD j.val false <;> simp only [h, Bool.false_eq_true,
      if_false, if_true] at hs
    · simp [not_lt_of_gt hs]
    · simp [hs]
  rw [heq]
  decide +kernel

#print axioms physical_sign_at
#print axioms physical_adjacent_order
#print axioms physical_kneading_numerator

end
end LoopsRealPeriod27

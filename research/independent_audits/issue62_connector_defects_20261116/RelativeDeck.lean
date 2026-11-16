import TipNativeDeckWords

/-!
Issue #62: genuine *finite* nonabelian based-word controls.

This is NOT an original KL path object or a construction of a missing
physical connector. It imports the archive's exact signed nine-generator
word model and checks only the explicitly stated example words. In
particular the synthetic inverse/commutator controls are not geometric
certificates for any xi/eta prime end.
-/

namespace LoopsFormal.Issue62RelativeDeck

open LoopsFormal.TipNativeDeckWords

def b10 : Letter := pos 3

/-- The coarse three-hole peripheral beta0 is not the fine root meridian. -/
theorem coarse_peripheral_is_not_in_fine_root_cyclic_subgroup :
    rootCyclicWord beta0 = false := by
  decide +kernel

/-- Nonabelian based prefix multiplication must not be replaced by
a commutative winding-vector operation. -/
theorem coarse_left_prefix_is_not_right_suffix :
    reduce (beta0 ++ [b10]) ≠ reduce ([b10] ++ beta0) := by
  decide +kernel

/-- An inverse coarse prefix followed by a fine root power does lie in H
after cancellation. This is a CONTROL word, not a path defect. -/
theorem one_based_prefix_inverse_control :
    rootCyclicWord (beta0 ++ beta0Inverse ++ [b00, b00]) = true := by
  decide +kernel

/-- A zero-winding nonroot commutator remains nonroot after the synthetic
inverse-prefix cancellation. No physical connector is assigned this word. -/
theorem commutator_survives_based_prefix_cancellation :
    rootCyclicWord (beta0 ++ beta0Inverse ++ commutator) = false := by
  decide +kernel

/-- The nine-generator free-word test sees an unremoved obstacle b10. -/
theorem other_fine_obstacle_not_in_H :
    rootCyclicWord [b10] = false := by
  decide +kernel

#print axioms coarse_peripheral_is_not_in_fine_root_cyclic_subgroup
#print axioms coarse_left_prefix_is_not_right_suffix
#print axioms one_based_prefix_inverse_control
#print axioms commutator_survives_based_prefix_cancellation
#print axioms other_fine_obstacle_not_in_H

end LoopsFormal.Issue62RelativeDeck

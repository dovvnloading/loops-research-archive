import TipNativeDeckWords

/-!
# Issue 62: literal word reference gauge, finite controls only

No source KL path, segment/cut intersection, analytic lift or root-end
convergence is postulated here. These are purely syntactic examples
using the archive's actual nine-generator signed letter normalizer.
-/

namespace LoopsFormal.Issue62ConnectorWordGauge

open LoopsFormal.TipNativeDeckWords

def inverseWord (w : Word) : Word := w.reverse.map flip

def sameLeftRootCoset (u v : Word) : Bool :=
  rootCyclicWord (u ++ inverseWord v)

/-- A W-compatible root reference can be prefixed by b00 without
    changing its H-sheet, but the literal word changes. -/
theorem root_word_reference_gauge :
    rootCyclicWord [b00, b00] = true ∧
    rootCyclicWord [b00, b00, flip b00] = true ∧
    reduce [b00, b00] ≠ reduce [b00, b00, flip b00] := by
  decide +kernel

/-- A synthetic nonroot word and its changed-root-reference expression
    have the same root-membership answer but distinct H-left cosets. -/
theorem nonroot_reference_changes_coset_coordinate :
    rootCyclicWord [b01] = false ∧
    rootCyclicWord [b01, flip b00] = false ∧
    sameLeftRootCoset [b01] [b01, flip b00] = false := by
  decide +kernel

/-- Based peripheral left prefix is not a fine b00 twist or right suffix. -/
theorem correct_nonabelian_prefix_order :
    rootCyclicWord beta0 = false ∧
    reduce (beta0 ++ [pos 3]) ≠ reduce ([pos 3] ++ beta0) := by
  decide +kernel

/-- A conjugated root generator ceases to use the OLD literal H basis.
    A basepoint change must transport H by the SAME conjugation. -/
theorem old_root_basis_not_invariant_under_conjugation :
    rootCyclicWord ([pos 3, b00, flip (pos 3)]) = false := by
  decide +kernel

#print axioms root_word_reference_gauge
#print axioms nonroot_reference_changes_coset_coordinate
#print axioms correct_nonabelian_prefix_order
#print axioms old_root_basis_not_invariant_under_conjugation

end LoopsFormal.Issue62ConnectorWordGauge

import FiberEnergyCollapse
import QuadraticEscape

/-!
# A sampling criterion on the actual quadratic parameter locus

The set below is defined by boundedness of the genuine critical orbit of
z ↦ z^2 + c.  The archive's proved escape theorem identifies it with the
zero set of its actual parameter escape potential.

The final theorem is conditional: no finite neighborhood certificate for
an infinitely renormalizable parameter is supplied by this module.
-/

namespace Loops.FiberSampling

open Set
open scoped Topology

/-- The quadratic Mandelbrot set, defined directly by its critical orbit. -/
def quadraticMandelbrot : Set ℂ :=
  {c : ℂ | ∃ B : ℝ, ∀ n : ℕ, ‖QuadraticEscape.orbit c n 0‖ ≤ B}

/-- Parameters in the actual locus, with the inherited metric and relative topology. -/
abbrev MandelbrotParameter := {c : ℂ // c ∈ quadraticMandelbrot}

/-- The bounded-orbit definition agrees with the existing actual escape potential. -/
theorem quadraticMandelbrot_eq_zero_escape :
    quadraticMandelbrot = {c : ℂ | QuadraticEscape.parameterEscape c = 0} := by
  ext c
  exact (QuadraticEscape.parameterEscape_zero_iff c).symm

/-- The parameter locus used in the reduction is a closed subset of the complex plane. -/
theorem quadraticMandelbrot_isClosed : IsClosed quadraticMandelbrot := by
  rw [quadraticMandelbrot_eq_zero_escape]
  exact isClosed_eq QuadraticEscape.parameterEscape_continuous continuous_const

/-- An explicit sufficient hypothesis for MLC on the actual parameter subtype.
The hypotheses require relative neighborhoods, finite covering of every point
in those neighborhoods, and the cubic energy budget at every target scale.
They are not asserted to hold for quadratic parameters. -/
theorem quadratic_mlc_of_local_energy_certificates
    (hcert : ∀ c : MandelbrotParameter, ∀ ε : ℝ, 0 < ε →
      ∃ (K : Set MandelbrotParameter) (n : ℕ)
        (s : Fin n → MandelbrotParameter) (a : MandelbrotParameter) (r : ℝ),
        K ∈ 𝓝 c ∧ IsPreconnected K ∧ 0 < r ∧ r ≤ ε / 8 ∧
          1024 * r * energy s a < ε ^ 3 ∧
            ∀ z ∈ K, ∃ i, dist z (s i) ≤ r) :
    LocallyConnectedSpace MandelbrotParameter :=
  locallyConnectedSpace_of_local_energy_certificates hcert

end Loops.FiberSampling

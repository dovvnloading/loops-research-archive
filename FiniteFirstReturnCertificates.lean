import FiniteThreeReturnCertificates

/-!
# Exact finite certificates for the enclosing p-return restriction

These checks use the same actual parameter boxes as the fixed
three-return collar.  They control the entire normalized disk of
radius 23/20 under the p-return, including its complete even
secant factors.  The outer circle escapes with margin 1/10.
-/

namespace FiniteFirstReturnCertificates

open LoopsFormal.Period27 LoopsFormal.DepthThree
open FiniteThreeReturnCertificates

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

def parentRadius (S : Int) (p : Nat) (C : Bounds) : Ratio :=
  ⟨23*(collarD S p C).hi, 20*S⟩

def parentErrors (S : Int) (p : Nat) (C : Bounds) : List Int :=
  errors S (collarRows S p C) (parentRadius S p C) p

def parentDeviation (S : Int) (p : Nat) (C : Bounds) (j : Nat) : Int :=
  upperProduct S (absHi (rowAt (collarRows S p C) j).quadratic)
    (radiusSquaredUpper S (parentRadius S p C)) +
    errorAt (parentErrors S p C) j

/-- The exact integer sphere margin and every intermediate nonzero
factor for the full enclosing p-return disk. -/
def FirstReturnCertificate (S : Int) (p : Nat) (C : Bounds) : Prop :=
  let rows := collarRows S p C
  let d := collarD S p C
  let a := (rowAt rows p).quadratic
  let t := errorAt (parentErrors S p C) p
  0 < S ∧ 0 < p ∧ 0 < d.lo ∧ 0 ≤ absLo a ∧ 0 ≤ t ∧
    900*S^2*d.lo + 400*S^2*t < 529*absLo a*d.lo^2 ∧
    ((List.range p).all fun j =>
      if j = 0 then true else decide
        (parentDeviation S p C j < absLo (rowAt rows j).orbit)) = true

instance (S : Int) (p : Nat) (C : Bounds) :
    Decidable (FirstReturnCertificate S p C) := by
  unfold FirstReturnCertificate
  infer_instance

/-- Every finite parameter box passes the full p-return disk test
in the kernel, with the same radius and strict margin. -/
theorem finite_first_return_certificates_valid :
    ((List.range 14).all fun i => decide
      (FirstReturnCertificate finiteScale (i+3) (parameterBox (i+3)))) = true := by
  decide +kernel

/-- The original ambient source radius is 1/4 at period three and
2^(-p) for the remaining finite periods. -/
def archiveRadiusDen (p : Nat) : Int := if p = 3 then 4 else 2^p

/-- The normalized control disk, in original coordinates, lies
strictly inside the archived ambient source disk. -/
theorem finite_parent_scale_certificates_valid :
    ((List.range 14).all fun i => decide
      (0 < archiveRadiusDen (i+3) ∧
       23*(collarD finiteScale (i+3) (parameterBox (i+3))).hi * archiveRadiusDen (i+3) <
         20*finiteScale)) = true := by
  decide +kernel

end FiniteFirstReturnCertificates

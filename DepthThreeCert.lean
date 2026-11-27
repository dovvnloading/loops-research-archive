import Period27RationalDerivative

/-!
# Exact arithmetic interface for the remaining depth-three tuning charts

Every operation in this module is integer arithmetic. The grid scale is an
explicit argument, so a certificate can increase precision without changing
the verification rules. `RootCertificate` contains strict endpoint and whole
parameter-interval derivative tests for the actual collision polynomial.
The real interpretation is proved in `DepthThreeReal`.

The disk predicates record the complete finite arithmetic hypotheses of the
archived depth-three packet. They make no claim about an unconstructed
straightening, prime-end identification, or marked extremal-width family.
-/

namespace LoopsFormal.DepthThree

open LoopsFormal.Period27

def oneAt (S : Int) : Bounds := ⟨S, S⟩

def jointNext (S : Int) (C : Bounds) (st : Bounds × Bounds) : Bounds × Bounds :=
  ⟨addBounds (squareBoundsAt S st.1) C,
   addBounds (mulBoundsAt S (doubleBounds st.1) st.2) (oneAt S)⟩

def jointIter (S : Int) (C : Bounds) : Nat → (Bounds × Bounds) → Bounds × Bounds
  | 0, st => st
  | n + 1, st => jointIter S C n (jointNext S C st)

def orbitAt (S : Int) (C : Bounds) (n : Nat) : Bounds :=
  (jointIter S C n (zeroBound, zeroBound)).1

def derivAt (S : Int) (C : Bounds) (n : Nat) : Bounds :=
  (jointIter S C n (zeroBound, zeroBound)).2

def collision (S : Int) (C : Bounds) (n : Nat) : Bounds :=
  addBounds (orbitAt S C (3 * n)) (orbitAt S C (6 * n))

def collisionDeriv (S : Int) (C : Bounds) (n : Nat) : Bounds :=
  addBounds (derivAt S C (3 * n)) (derivAt S C (6 * n))

/-- Strict endpoint signs and one signed derivative interval. No floating
point evaluation or equality with a rounded seed enters this proposition. -/
def RootCertificate (S : Int) (n : Nat) (C : Bounds) : Prop :=
  0 < S ∧ C.lo < C.hi ∧
    (((collision S ⟨C.lo, C.lo⟩ n).hi < 0 ∧
       0 < (collision S ⟨C.hi, C.hi⟩ n).lo) ∨
     ((collision S ⟨C.hi, C.hi⟩ n).hi < 0 ∧
       0 < (collision S ⟨C.lo, C.lo⟩ n).lo)) ∧
    (0 < (collisionDeriv S C n).lo ∨ (collisionDeriv S C n).hi < 0)

instance (S : Int) (n : Nat) (C : Bounds) : Decidable (RootCertificate S n C) :=
  by unfold RootCertificate; infer_instance

/-- A root certificate always specifies a nonempty parameter interval. -/
theorem rootCertificate_ordered {S : Int} {n : Nat} {C : Bounds}
    (h : RootCertificate S n C) : 0 < S ∧ C.lo < C.hi :=
  ⟨h.1, h.2.1⟩

end LoopsFormal.DepthThree

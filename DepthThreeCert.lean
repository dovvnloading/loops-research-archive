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

/-! ## Fixed-point disk and marked-cut arithmetic -/

structure Ratio where
  num : Int
  den : Int
  deriving Repr, DecidableEq

structure Packet where
  p : Nat
  q : Nat
  r : Nat
  parameter : Bounds
  radius1 : Ratio
  radius2 : Ratio
  radius3 : Ratio
  alpha : Bounds
  reference2 : Bounds
  reference1 : Bounds
  deriving Repr, DecidableEq

def floorDiv (a b : Int) : Int := if b < 0 then (-a) / (-b) else a / b

def ceilDiv (a b : Int) : Int := -floorDiv (-a) b

def ratioBounds (S : Int) (r : Ratio) : Bounds :=
  ⟨floorDiv (r.num * S) r.den, ceilDiv (r.num * S) r.den⟩

def negate (b : Bounds) : Bounds := ⟨-b.hi, -b.lo⟩

def subtract (a b : Bounds) : Bounds := addBounds a (negate b)

def absHi (b : Bounds) : Int := max (-b.lo) b.hi

def absLo (b : Bounds) : Int :=
  if 0 < b.lo then b.lo else if b.hi < 0 then -b.hi else 0

def inverseBounds (S : Int) (b : Bounds) : Bounds :=
  ⟨floorDiv (S * S) b.hi, ceilDiv (S * S) b.lo⟩

def upperProduct (S a b : Int) : Int := ceilDiv (a * b) S

def sameSign (a b : Bounds) : Bool :=
  decide ((0 < a.lo ∧ 0 < b.lo) ∨ (a.hi < 0 ∧ b.hi < 0))

def strictLT (a b : Bounds) : Bool := decide (a.hi < b.lo)

def strictChain : List Bounds → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => strictLT a b && strictChain (b :: rest)

structure TraceRow where
  orbit : Bounds
  deriv : Bounds
  quadratic : Bounds
  deriving Repr, DecidableEq

def zeroRow : TraceRow := ⟨zeroBound, zeroBound, zeroBound⟩

def rowNext (S : Int) (C : Bounds) (j : Nat) (st : TraceRow) : TraceRow :=
  let next := jointNext S C (st.orbit, st.deriv)
  ⟨next.1, next.2,
    if j = 0 then oneAt S
    else mulBoundsAt S (doubleBounds st.orbit) st.quadratic⟩

def rowTrace (S : Int) (C : Bounds) : Nat → Nat → TraceRow → List TraceRow
  | 0, _, st => [st]
  | n + 1, j, st => st :: rowTrace S C n (j + 1) (rowNext S C j st)

def trace (S : Int) (C : Bounds) (n : Nat) : List TraceRow :=
  rowTrace S C n 0 zeroRow

def rowAt (rows : List TraceRow) (n : Nat) : TraceRow := rows.getD n zeroRow

def radiusSquaredUpper (S : Int) (r : Ratio) : Int :=
  ceilDiv (r.num * r.num * S) (r.den * r.den)

def errorStep (S rr : Int) (row : TraceRow) (t : Int) : Int :=
  let v := upperProduct S (absHi row.quadratic) rr + t
  upperProduct S (2 * absHi row.orbit) t + upperProduct S v v

def errorTail (S rr : Int) : List TraceRow → Int → List Int
  | [], _ => []
  | row :: rest, t =>
    let next := errorStep S rr row t
    next :: errorTail S rr rest next

/-- Remainders are computed only through the requested time. Computing a
large-radius error beyond its return would needlessly magnify the bound. -/
def errors (S : Int) (rows : List TraceRow) (r : Ratio) (n : Nat) : List Int :=
  if n = 0 then [0]
  else 0 :: 0 :: errorTail S (radiusSquaredUpper S r) ((rows.drop 1).take (n - 1)) 0

def errorAt (ts : List Int) (j : Nat) : Int := ts.getD j 0

/-- Numerator of the full disk margin with positive denominator S*den². -/
def gapNumerator (S : Int) (row : TraceRow) (t : Int) (r : Ratio) : Int :=
  absLo row.quadratic * r.num * r.num -
    (absHi row.orbit + t) * r.den * r.den - S * r.num * r.den

def insideRadius (S : Int) (b : Bounds) (r : Ratio) : Bool :=
  decide (absHi b * r.den < S * r.num)

def deviation (S : Int) (rows : List TraceRow) (ts : List Int)
    (r : Ratio) (j : Nat) : Int :=
  if j = 0 then (ratioBounds S r).hi
  else upperProduct S (absHi (rowAt rows j).quadratic) (radiusSquaredUpper S r) +
    errorAt ts j

def phaseCheck (S : Int) (rows : List TraceRow) (ts : List Int)
    (r : Ratio) (stride count : Nat) : Bool :=
  (List.range count).all fun i => (List.range count).all fun j =>
    !(decide (i < j)) || decide
      (deviation S rows ts r (i * stride) + deviation S rows ts r (j * stride) <
       absLo (subtract (rowAt rows (i * stride)).orbit (rowAt rows (j * stride)).orbit))

def upperDiskImage (S : Int) (rows : List TraceRow)
    (start len : Nat) (delta : Int) : Int :=
  ((rows.drop start).take len).foldl (fun d row =>
    upperProduct S (2 * absHi row.orbit) d + upperProduct S d d) delta

def layerContainment (S : Int) (rows : List TraceRow) (ts : List Int)
    (parent child : Ratio) (period repeats : Nat) : Bool :=
  (List.range repeats).all fun j =>
    let i := j * period
    let after := upperDiskImage S rows i period (deviation S rows ts child i)
    decide ((absHi (rowAt rows (i + period)).orbit + after) * parent.den < S * parent.num)

def orbitBox (S : Int) (C : Bounds) : Nat → Bounds → Bounds
  | 0, z => z
  | n + 1, z => orbitBox S C n (addBounds (squareBoundsAt S z) C)

def connectorSteps (S : Int) (C : Bounds) : List TraceRow → Bounds → Bounds × Bool
  | [], z => (z, true)
  | row :: rest, z =>
    let next := addBounds (squareBoundsAt S z) C
    let result := connectorSteps S C rest next
    (result.1, sameSign row.orbit next && result.2)

def connectorCheck (S : Int) (C : Bounds) (rows : List TraceRow)
    (period count : Nat) (r : Ratio) : Bool :=
  let M := ((List.range count).map fun j => absHi (rowAt rows ((j + 1) * period)).orbit).foldl max 0
  let result := connectorSteps S C ((rows.drop 1).take (period - 1)) ⟨-M, M⟩
  decide (M * r.den < S * r.num) && result.2 &&
    insideRadius S (addBounds (squareBoundsAt S result.1) C) r

def signedKneading (S : Int) (rows refs : List TraceRow)
    (period count : Nat) : Bool :=
  (List.range count).all fun k =>
    sameSign (mulBoundsAt S (rowAt rows period).quadratic
      (rowAt rows ((k + 1) * period)).orbit) (rowAt refs (k + 1)).orbit

def fixedResidual (S : Int) (C : Bounds) (A : Bounds) (n : Nat) (u : Int) : Bounds :=
  let point : Bounds := ⟨u, u⟩
  let z := negate (mulBoundsAt S point (inverseBounds S A))
  subtract (negate (mulBoundsAt S A (orbitBox S C n z))) point

def normalizedCuts (S : Int) (rows : List TraceRow) (n : Nat) : List Bounds :=
  zeroBound :: (List.range 6).map (fun j =>
    negate (mulBoundsAt S (rowAt rows n).quadratic (rowAt rows ((j + 1) * n)).orbit))

def cutAt (cuts : List Bounds) (j : Nat) : Bounds := cuts.getD j zeroBound

def cutOrderCheck (cuts : List Bounds) (alpha : Bounds) : Bool :=
  let y := cutAt cuts
  strictChain [y 2, y 5, y 3, zeroBound, y 6, alpha, y 4, y 1] &&
  strictChain [negate (y 1), negate (y 4), y 2, y 5, negate alpha, y 3,
    y 6, alpha, negate (y 5), negate (y 2), y 4, y 1]

def roundedCoefficient (S : Int) (A : Bounds) : Int :=
  floorDiv (absLo A + absHi A + S) (2 * S)

def terminalRadius (S : Int) (A : Bounds) : Ratio := ⟨3, 10 * roundedCoefficient S A⟩

def terminalCheck (S : Int) (C : Bounds) (rows : List TraceRow)
    (n : Nat) (r : Ratio) : Bool :=
  let A := (rowAt rows n).quadratic
  let nearest := roundedCoefficient S A
  let r4 := terminalRadius S A
  let ts := errors S rows r4 (3 * n)
  decide (0 < nearest ∧ S * (2 * nearest - 1) < 2 * absLo A ∧
    2 * absHi A < S * (2 * nearest + 1)) &&
  decide (S * S * r4.den * r4.den <
    8 * absLo A * gapNumerator S (rowAt rows (3 * n)) (errorAt ts (3 * n)) r4) &&
  decide (r4.num * r.den < r.num * r4.den) &&
  insideRadius S (rowAt rows (3 * n)).orbit r4 &&
  phaseCheck S rows ts r4 n 3 &&
  ([1, 2, 3] : List Nat).all (fun j =>
    decide ((absHi (rowAt rows (j * n)).orbit + deviation S rows ts r4 (j * n)) *
      r.den < S * r.num)) &&
  connectorCheck S C rows n 6 r

structure GateData where
  center : Bounds
  inner : Bounds
  plus : Bounds
  minus : Bounds
  deriving Repr, DecidableEq

def gateData (S : Int) (cuts : List Bounds) (alpha : Bounds) : GateData :=
  let half := ratioBounds S ⟨1, 2⟩
  let center := mulBoundsAt S (addBounds (cutAt cuts 2) (cutAt cuts 5)) half
  ⟨center, mulBoundsAt S (subtract (cutAt cuts 5) (cutAt cuts 2)) half,
    subtract (negate alpha) center, addBounds (cutAt cuts 4) center⟩

def diskImage (S : Int) (C : Bounds) : Nat → Bounds → Int → Bounds × Int
  | 0, z, d => (z, d)
  | n + 1, z, d => diskImage S C n
      (addBounds (squareBoundsAt S z) C)
      (upperProduct S (2 * absHi z) d + upperProduct S d d)

def gateCheck (S : Int) (C : Bounds) (rows : List TraceRow)
    (n : Nat) (r : Ratio) (g : GateData) : Bool :=
  let A := (rowAt rows n).quadratic
  let zcenter := negate (mulBoundsAt S g.center (inverseBounds S A))
  let dr := ceilDiv (absHi g.plus * S) (absLo A)
  let output := diskImage S C n zcenter dr
  decide (0 < g.inner.lo ∧ 0 < absLo A) &&
  strictLT g.plus g.minus && strictLT g.inner g.plus &&
  decide ((absHi output.1 + output.2) * r.den < S * r.num) &&
  decide (absHi zcenter < absLo (rowAt rows n).orbit)

def positiveRatio (r : Ratio) : Bool := decide (0 < r.num ∧ 0 < r.den)

/-- The complete finite disk, itinerary, cut, and whole-gate checks. The
separate width certificate uses exactly the `GateData` and cuts computed here. -/
def geometryCheck (S : Int) (P : Packet) : Bool :=
  let n1 := P.p
  let n2 := P.p * P.q
  let n3 := P.p * P.q * P.r
  let rows := trace S P.parameter (6 * n3)
  let ts1 := errors S rows P.radius1 n1
  let ts2 := errors S rows P.radius2 n2
  let ts3 := errors S rows P.radius3 n3
  let refs2 := trace S P.reference2 (6 * P.q * P.r)
  let refs1 := trace S P.reference1 (6 * P.r)
  let A := (rowAt rows n3).quadratic
  let cuts := normalizedCuts S rows n3
  decide (0 < S ∧ P.parameter.lo < P.parameter.hi ∧
    P.reference2.lo ≤ P.reference2.hi ∧ P.reference1.lo ≤ P.reference1.hi ∧
    3 ≤ P.p ∧ P.p ≤ 5 ∧ 3 ≤ P.q ∧ P.q ≤ 5 ∧ 3 ≤ P.r ∧ P.r ≤ 5) &&
  positiveRatio P.radius1 && positiveRatio P.radius2 && positiveRatio P.radius3 &&
  decide ((rowAt rows 1).orbit.hi < 0) &&
  ((List.range (P.p - 1)).all fun j => decide (0 < (rowAt rows (j + 2)).orbit.lo)) &&
  decide ((rowAt rows n1).quadratic.hi < 0 ∧
    0 < (rowAt rows n2).quadratic.lo ∧ A.hi < 0) &&
  decide (0 < (mulBoundsAt S A (rowAt rows (3 * n3)).orbit).lo ∧
    (mulBoundsAt S A (rowAt rows (6 * n3)).orbit).hi < 0) &&
  signedKneading S rows refs2 n1 (6 * P.q * P.r) &&
  signedKneading S rows refs1 n2 (6 * P.r) &&
  insideRadius S (rowAt rows n1).orbit P.radius1 &&
  insideRadius S (rowAt rows n2).orbit P.radius2 &&
  insideRadius S (rowAt rows n3).orbit P.radius3 &&
  decide (0 < gapNumerator S (rowAt rows n1) (errorAt ts1 n1) P.radius1 ∧
    0 < gapNumerator S (rowAt rows n2) (errorAt ts2 n2) P.radius2 ∧
    0 < gapNumerator S (rowAt rows n3) (errorAt ts3 n3) P.radius3) &&
  phaseCheck S rows ts1 P.radius1 1 P.p &&
  phaseCheck S rows ts2 P.radius2 n1 P.q &&
  phaseCheck S rows ts3 P.radius3 n2 P.r &&
  layerContainment S rows ts2 P.radius1 P.radius2 n1 P.q &&
  layerContainment S rows ts3 P.radius2 P.radius3 n2 P.r &&
  connectorCheck S P.parameter rows n1 (6 * P.q * P.r) P.radius1 &&
  connectorCheck S P.parameter rows n2 (6 * P.r) P.radius2 &&
  decide (P.alpha.lo < P.alpha.hi ∧
    0 < (fixedResidual S P.parameter A n3 P.alpha.lo).lo ∧
    (fixedResidual S P.parameter A n3 P.alpha.hi).hi < 0) &&
  cutOrderCheck cuts P.alpha && terminalCheck S P.parameter rows n3 P.radius3 &&
  gateCheck S P.parameter rows n3 P.radius3 (gateData S cuts P.alpha)

def GeometryCertificate (S : Int) (P : Packet) : Prop := geometryCheck S P = true

instance (S : Int) (P : Packet) : Decidable (GeometryCertificate S P) :=
  by unfold GeometryCertificate; infer_instance

end LoopsFormal.DepthThree

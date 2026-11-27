import DepthThreeCert

/-!
# Exact finite certificates for a fixed three-return collar

The parameter boxes are the archived adjacent dyadic boxes for periods
three through sixteen.  All conclusions here are rechecked from the
literal quadratic orbit.  The new checks concern the fixed normalized
radii 3/20 and 1/6, and exclude a zero at every intermediate phase on
the complete closed source disk.  Their analytic meaning is proved in
`FiniteThreeReturnCollars`.
-/

namespace FiniteThreeReturnCertificates

open LoopsFormal.Period27 LoopsFormal.DepthThree

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

def finiteScale : Int := 2 ^ 512

/-- The archived rational boxes, rescaled exactly to the certificate grid. -/
def parameterBox (p : Nat) : Bounds :=
  match p with
  | 3 => ⟨-206863788397282802267408702538793977315584867630598294361534944901352850303604 * 2^256, -206863788397282802267408702538793977315584867630598294361534944901352850303603 * 2^256⟩
  | 4 => ⟨-224932405974042298957915524477148973464551640119884252130376804385108645516290 * 2^256, -224932405974042298957915524477148973464551640119884252130376804385108645516289 * 2^256⟩
  | 5 => ⟨-229908455009726844371636647325851011168021710766793344328591203466498463304892 * 2^256, -229908455009726844371636647325851011168021710766793344328591203466498463304891 * 2^256⟩
  | 6 => ⟨-231165301948715810770228801979889868997710711484378648858382566481886798601362 * 2^256, -231165301948715810770228801979889868997710711484378648858382566481886798601361 * 2^256⟩
  | 7 => ⟨-231479511493544950186069647316998533527551584431058987623697926625334430730271 * 2^256, -231479511493544950186069647316998533527551584431058987623697926625334430730270 * 2^256⟩
  | 8 => ⟨-231558017961263534024166083767791669928606608564833463355994069705641667440255 * 2^256, -231558017961263534024166083767791669928606608564833463355994069705641667440254 * 2^256⟩
  | 9 => ⟨-231577638920564092579136255421939630884836906131569849829313081641534396423027 * 2^256, -231577638920564092579136255421939630884836906131569849829313081641534396423026 * 2^256⟩
  | 10 => ⟨-231582543633546533526283756991348241519646229656381644300932701776334013313375 * 2^256, -231582543633546533526283756991348241519646229656381644300932701776334013313374 * 2^256⟩
  | 11 => ⟨-231583769768046569854648970766680764658829534892687229250012680253511623627757 * 2^256, -231583769768046569854648970766680764658829534892687229250012680253511623627756 * 2^256⟩
  | 12 => ⟨-231584076298261366026035660140568367251093068401698564453360469439884152023717 * 2^256, -231584076298261366026035660140568367251093068401698564453360469439884152023716 * 2^256⟩
  | 13 => ⟨-231584152930559666515303967650834348256481862329075540046349754537259200892081 * 2^256, -231584152930559666515303967650834348256481862329075540046349754537259200892080 * 2^256⟩
  | 14 => ⟨-231584172088615637851266831576303849748697550697125275380614674797195062691559 * 2^256, -231584172088615637851266831576303849748697550697125275380614674797195062691558 * 2^256⟩
  | 15 => ⟨-231584176878128302859622673046256263221575212163151167105653190928991956027351 * 2^256, -231584176878128302859622673046256263221575212163151167105653190928991956027350 * 2^256⟩
  | 16 => ⟨-231584178075506375804479650715242823625679539211828532799419525784242925600673 * 2^256, -231584178075506375804479650715242823625679539211828532799419525784242925600672 * 2^256⟩
  | _ => zeroBound

def collarRows (S : Int) (p : Nat) (C : Bounds) : List TraceRow :=
  trace S C (3*p)

def collarD (S : Int) (p : Nat) (C : Bounds) : Bounds :=
  (rowAt (collarRows S p C) p).orbit

def collarRadius (S : Int) (p : Nat) (C : Bounds) : Ratio :=
  ⟨(collarD S p C).hi, 6*S⟩

def collarErrors (S : Int) (p : Nat) (C : Bounds) : List Int :=
  errors S (collarRows S p C) (collarRadius S p C) (3*p)

def collarDeviation (S : Int) (p : Nat) (C : Bounds) (j : Nat) : Int :=
  upperProduct S (absHi (rowAt (collarRows S p C) j).quadratic)
    (radiusSquaredUpper S (collarRadius S p C)) +
    errorAt (collarErrors S p C) j

/-- Integer conditions for the actual normalized collar, including every
factor in the complete even divided difference of the three-return map. -/
def GeometryCertificate (S : Int) (p : Nat) (C : Bounds) : Prop :=
  let rows := collarRows S p C
  let d := collarD S p C
  let x2 := (rowAt rows (2*p)).orbit
  let x3 := (rowAt rows (3*p)).orbit
  let a3 := (rowAt rows (3*p)).quadratic
  let t3 := errorAt (collarErrors S p C) (3*p)
  0 < S ∧ 0 < p ∧ 0 < d.lo ∧ x3.hi < 0 ∧
    8 * absHi x3 < d.lo ∧
    50 * collarDeviation S p C p < 3*d.lo ∧
    100 * collarDeviation S p C (2*p) < 19*d.lo ∧
    -4*d.lo ≤ 5*x2.lo ∧ 4*x2.hi ≤ -3*d.hi ∧
    0 ≤ t3 ∧ 0 ≤ absLo a3 ∧
    6000*S^2*(absHi x3+t3) + 1012*S^2*d.lo <
      135*absLo a3*d.lo^2 ∧
    ((List.range (3*p)).all fun j =>
      if j = 0 then true else decide
        (collarDeviation S p C j < absLo (rowAt rows j).orbit)) = true

instance (S : Int) (p : Nat) (C : Bounds) :
    Decidable (GeometryCertificate S p C) := by
  unfold GeometryCertificate
  infer_instance

/-- All fourteen root and fixed-collar certificates are checked in the
kernel from integer arithmetic, including the complete intermediate list. -/
theorem finite_certificates_valid :
    ((List.range 14).all fun i => decide
      (RootCertificate finiteScale (i+3) (parameterBox (i+3)) ∧
       GeometryCertificate finiteScale (i+3) (parameterBox (i+3)))) = true := by
  decide +kernel

end FiniteThreeReturnCertificates

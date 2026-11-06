import Period27IntervalSound

/-!
# Recomputed signed-dyadic margins for the nonattracting period-9 tip

These finite integer theorems use the already-audited generic signed
outward interval implementation at precision 2^-224. No numerical
floating-point arithmetic or proof placeholders are used. Theorems about complex
holomorphic topology (Rouché, Riemann-Hurwitz, Julia connectivity) are
NOT Lean formalized here; see the separate mathematical audit.
-/

namespace LoopsFormal.TipComplexMargins

open LoopsFormal.Period27

def unitTip : Int := 2 ^ 224
def tipParameterK : Int := -607918036626757496169199575185708826140
def tipStep : Int := 2 ^ 96
def tipBracket : Bounds :=
  ⟨tipParameterK * tipStep, (tipParameterK + 1) * tipStep⟩

/-- True orbit on the entire exact isolating parameter interval is
    enclosed by these outward 2^-224 grid intervals. -/
def tipOrbit (j : Nat) : Bounds :=
  pointAfterAt unitTip j tipBracket zeroBound

/-- Coefficient a_j of z^2 in f^j(z) = x_j + a_j z^2 + O(z^4). -/
def tipCoefficient : Nat → Bounds
  | 0 => zeroBound
  | 1 => ⟨unitTip, unitTip⟩
  | n + 2 =>
      mulBoundsAt unitTip
        (doubleBounds (tipOrbit (n + 1))) (tipCoefficient (n + 1))

def absUpper (b : Bounds) : Int :=
  max (max b.lo (-b.lo)) (max b.hi (-b.hi))

def absLower (b : Bounds) : Int :=
  if 0 < b.lo then b.lo
  else if b.hi < 0 then -b.hi
  else 0

def ceilGrid (n : Int) : Int :=
  - ((-n) / unitTip)

def radiusSquare (r : Int) : Int := r * r / unitTip

/-- Guaranteed bound on the O(z^4) remainder on the circle of
    physical radius r/unitTip. Uses outward integer products. -/
def errorTail (r : Int) : Nat → Int
  | 0 => 0
  | 1 => 0
  | n + 2 =>
      let j := n + 1
      let prev := errorTail r j
      let leading := ceilGrid (absUpper (tipCoefficient j) * radiusSquare r)
      ceilGrid (2 * absUpper (tipOrbit j) * prev) +
        ceilGrid ((leading + prev) * (leading + prev))

def deviation (r : Int) (j : Nat) : Int :=
  if j = 0 then r
  else ceilGrid (absUpper (tipCoefficient j) * radiusSquare r) +
       errorTail r j

def leadingLower (r : Int) (j : Nat) : Int :=
  absLower (tipCoefficient j) * radiusSquare r / unitTip

def roucheMargin (r : Int) (p : Nat) (target : Int) : Int :=
  leadingLower r p - absUpper (tipOrbit p) -
    errorTail r p - target

def outerRadius : Int := unitTip / 4
def innerRadius : Int := unitTip / 32
def innerShrinkRadius : Int := 27 * unitTip / 1024
def badOldShrinkRadius : Int := 13 * unitTip / 512

/-- Three positive, recomputed Rouché inequalities: true period-3
    and period-9 centers plus the stricter inner disk restriction. -/
theorem positive_rouche_margins :
    0 < roucheMargin outerRadius 3 outerRadius ∧
    0 < roucheMargin innerRadius 9 innerRadius ∧
    0 < roucheMargin innerShrinkRadius 9 innerRadius := by
  decide +kernel

/-- Adversarial negative control. The center's old 13/512 bound
    fails to certify this new Misiurewicz parameter. This does not
    refute the actual existence of any polynomial-like domain. -/
theorem old_shrink_bound_is_inconclusive :
    roucheMargin badOldShrinkRadius 9 innerRadius ≤ 0 := by
  decide +kernel

def intervalGap (a b : Bounds) : Int :=
  max 0 (max (a.lo - b.hi) (b.lo - a.hi))

def pairwiseSeparated (p : Nat) (r : Int) : Bool :=
  (List.range p).all (fun i =>
    (List.range p).all (fun j =>
      decide (i ≥ j ∨
        deviation r i + deviation r j <
        intervalGap (tipOrbit i) (tipOrbit j))))

/-- The actual complex phases have strictly disjoint enclosing disks:
    3 phases using U3 and 9 using the shrunken inner source disk. -/
theorem phase_disks_pairwise_separated :
    pairwiseSeparated 3 outerRadius = true ∧
    pairwiseSeparated 9 innerShrinkRadius = true := by
  decide +kernel

def noOtherCriticalPreimage (p : Nat) (r : Int) : Bool :=
  (List.range p).all (fun j =>
    decide (j = 0 ∨
      deviation r j < absLower (tipOrbit j)))

theorem unique_critical_point_on_source_disks :
    noOtherCriticalPreimage 3 outerRadius = true ∧
    noOtherCriticalPreimage 9 innerRadius = true ∧
    noOtherCriticalPreimage 9 innerShrinkRadius = true := by
  decide +kernel

def nestedOuterReturns : Bool :=
  ([0, 3, 6, 9] : List Nat).all (fun j =>
    decide (absUpper (tipOrbit j) + deviation innerRadius j < outerRadius))

/-- f^(3k)(U9) is strictly inside U3 at k=0,1,2,3. -/
theorem nested_outer_return_disk_margins :
    nestedOuterReturns = true := by
  decide +kernel

#print axioms positive_rouche_margins
#print axioms old_shrink_bound_is_inconclusive
#print axioms phase_disks_pairwise_separated
#print axioms unique_critical_point_on_source_disks
#print axioms nested_outer_return_disk_margins

end LoopsFormal.TipComplexMargins

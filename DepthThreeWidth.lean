import DepthThreeCert
import Lean

/-!
# Exact rational width-envelope witnesses for the depth-three grid

This module checks the finite rational arithmetic in the archived logarithm,
cosine Taylor, and arithmetic-geometric-mean envelopes. Square roots and
inverse cosines are represented by witnesses whose defining inequalities are
rechecked by the kernel. No floating-point search is part of the checker.

The conclusions are rational certificate inequalities. Their interpretation
as extremal widths requires the same analytic and marked-family inputs as
the original depth-three packet; this file does not add those as premises
to a claimed unconditional physical-width theorem.
-/

namespace LoopsFormal.DepthThree

open LoopsFormal.Period27

structure RationalBounds where
  lo : Rat
  hi : Rat
  deriving Repr, DecidableEq

structure WidthWitness where
  logV : Rat
  angleA : RationalBounds
  angleB : RationalBounds
  complement : RationalBounds
  agmKLo : List RationalBounds
  agmKHi : List RationalBounds
  agmSLo : List RationalBounds
  agmSHi : List RationalBounds
  deriving Repr, DecidableEq

def rationalValue (S x : Int) : Rat := Rat.ofInt x / Rat.ofInt S

def certificateFactorial : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * certificateFactorial n

def cosineTaylor (t : Rat) : Rat :=
  (List.range 18).foldl (fun s j =>
    s + (-1 : Rat) ^ j * t ^ (2 * j) / (certificateFactorial (2 * j) : Rat)) 0

def cosineBounds (t : Rat) : RationalBounds :=
  let remainder := t ^ 36 / (certificateFactorial 36 : Rat)
  ⟨cosineTaylor t - remainder, cosineTaylor t + remainder⟩

def cosineBracketCheck (S : Int) (input : Bounds) (angle : RationalBounds) : Bool :=
  decide (0 < input.lo ∧ input.lo ≤ input.hi ∧ input.hi < S ∧
    0 < angle.lo ∧ angle.lo < angle.hi ∧ angle.hi < 2 ∧
    rationalValue S input.hi < (cosineBounds angle.lo).lo ∧
    (cosineBounds angle.hi).hi < rationalValue S input.lo)

structure AgmBox where
  aLo : Rat
  aHi : Rat
  bLo : Rat
  bHi : Rat
  deriving Repr, DecidableEq

def agmInitial (t : Rat) : AgmBox := ⟨1, 1, t, t⟩

def agmNext (state : AgmBox) (sqrt : RationalBounds) : AgmBox :=
  ⟨(state.aLo + state.bLo) / 2, (state.aHi + state.bHi) / 2, sqrt.lo, sqrt.hi⟩

def agmStepCheck (state : AgmBox) (sqrt : RationalBounds) : Bool :=
  decide (0 < state.aLo ∧ state.aLo ≤ state.aHi ∧
    0 < state.bLo ∧ state.bLo ≤ state.bHi ∧
    0 < sqrt.lo ∧ sqrt.lo ≤ sqrt.hi ∧
    sqrt.lo * sqrt.lo ≤ state.aLo * state.bLo ∧
    state.aHi * state.bHi ≤ sqrt.hi * sqrt.hi)

def agmChainCheck : AgmBox → List RationalBounds → Bool
  | state, [] => decide (0 < state.bLo ∧ state.bLo ≤ state.aHi)
  | state, w :: ws => agmStepCheck state w && agmChainCheck (agmNext state w) ws

def agmCheck (t : Rat) (ws : List RationalBounds) : Bool :=
  decide (0 < t ∧ t ≤ 1 ∧ ws.length = 10) && agmChainCheck (agmInitial t) ws

def agmBounds (t : Rat) (ws : List RationalBounds) : RationalBounds :=
  let state := ws.foldl agmNext (agmInitial t)
  ⟨state.bLo, state.aHi⟩

def ellipticRatio (w : WidthWitness) : RationalBounds :=
  ⟨(w.angleB.lo - w.angleA.hi) / (w.angleB.lo + w.angleA.hi),
   (w.angleB.hi - w.angleA.lo) / (w.angleB.hi + w.angleA.lo)⟩

def planeBounds (w : WidthWitness) : RationalBounds :=
  let k := ellipticRatio w
  let topLo := (agmBounds k.lo w.agmKLo).lo
  let topHi := (agmBounds k.hi w.agmKHi).hi
  let bottomLo := (agmBounds w.complement.lo w.agmSLo).lo
  let bottomHi := (agmBounds w.complement.hi w.agmSHi).hi
  ⟨topLo / bottomHi, topHi / bottomLo⟩

def logarithmPartialSum (v : Rat) : Rat :=
  2 * (List.range 16).foldl (fun s j => s + v ^ (2 * j + 1) / (2 * j + 1 : Nat)) 0

def radialLower (w : WidthWitness) : Rat := logarithmPartialSum w.logV / (2 * (22 / 7))

def widthArithmeticCheck (S : Int) (P : Packet) (w : WidthWitness) : Bool :=
  let n := P.p * P.q * P.r
  let rows := trace S P.parameter (6 * n)
  let cuts := normalizedCuts S rows n
  let g := gateData S cuts P.alpha
  let half := ratioBounds S ⟨1, 2⟩
  let mid := mulBoundsAt S (addBounds (cutAt cuts 2) (cutAt cuts 1)) half
  let rad := mulBoundsAt S (subtract (cutAt cuts 1) (cutAt cuts 2)) half
  let inputA := mulBoundsAt S (subtract mid (cutAt cuts 5)) (inverseBounds S rad)
  let inputB := mulBoundsAt S (subtract mid (cutAt cuts 3)) (inverseBounds S rad)
  let k := ellipticRatio w
  let v := Rat.ofInt (g.plus.lo - g.inner.hi) / Rat.ofInt (g.plus.lo + g.inner.hi)
  decide (0 < S ∧ 0 < rad.lo ∧ 0 < g.inner.hi ∧ g.inner.hi < g.plus.lo ∧
    0 < w.logV ∧ w.logV ≤ v ∧ w.logV < 1) &&
  cosineBracketCheck S inputA w.angleA && cosineBracketCheck S inputB w.angleB &&
  decide (w.angleA.hi < w.angleB.lo ∧ 0 < k.lo ∧ k.lo < k.hi ∧ k.hi < 1 ∧
    0 < w.complement.lo ∧ w.complement.lo ≤ w.complement.hi ∧ w.complement.hi ≤ 1 ∧
    w.complement.lo * w.complement.lo ≤ 1 - k.hi * k.hi ∧
    1 - k.lo * k.lo ≤ w.complement.hi * w.complement.hi) &&
  agmCheck k.lo w.agmKLo && agmCheck k.hi w.agmKHi &&
  agmCheck w.complement.lo w.agmSLo && agmCheck w.complement.hi w.agmSHi

/-- Every arithmetic witness is checked, and the rational envelopes have
the strict constants claimed for the complete finite grid. -/
def WidthCertificate (S : Int) (P : Packet) (w : WidthWitness) : Prop :=
  widthArithmeticCheck S P w = true ∧
    (1 / 4 : Rat) < radialLower w ∧ (planeBounds w).hi < (31 / 40 : Rat) ∧
    radialLower w < (planeBounds w).lo

instance (S : Int) (P : Packet) (w : WidthWitness) :
    Decidable (WidthCertificate S P w) := by
  unfold WidthCertificate
  infer_instance

theorem certified_rational_width_bounds {S : Int} {P : Packet} {w : WidthWitness}
    (h : WidthCertificate S P w) :
    (1 / 4 : Rat) < radialLower w ∧ (planeBounds w).hi < (31 / 40 : Rat) :=
  ⟨h.2.1, h.2.2.1⟩

end LoopsFormal.DepthThree

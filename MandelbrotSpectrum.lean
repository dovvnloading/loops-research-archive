import Lean

/-!
# Finite identities for the Mandelbrot boundary-spectrum estimates

The Abel identity holds in any commutative ring. Its square-weight
specialization is the finite step of Lemma 2 in the area-tail note.
The analytic estimates, the ray landings and the infinite limit are
separate inputs to the written theorem.
-/

namespace LoopsFormal.MandelbrotSpectrum

open Lean.Grind

/-- Sum f(start), ..., f(start + count - 1), including the empty interval. -/
def intervalSum {R : Type} [CommRing R] (f : Nat → R) (start : Nat) : Nat → R
  | 0 => 0
  | n + 1 => intervalSum f start n + f (start + n)

/-- Summation by parts with both endpoint terms retained. -/
theorem abel_identity {R : Type} [CommRing R] (w t : Nat → R) (start count : Nat) :
    intervalSum (fun j => w j * (t j - t (j + 1))) start count +
        w (start + count) * t (start + count) =
      w start * t start +
        intervalSum (fun j => (w (j + 1) - w j) * t (j + 1)) start count := by
  induction count with
  | zero => simp [intervalSum]
  | succ n ih =>
    simp only [intervalSum, Nat.add_succ] at *
    grind

/-- The weight increment (j+1)^2 - j^2 is 2j+1, at every scale. -/
theorem square_weight_abel (t : Nat → Rat) (start count : Nat) :
    intervalSum (fun j => (j : Rat)^2 * (t j - t (j + 1))) start count +
        ((start + count : Nat) : Rat)^2 * t (start + count) =
      (start : Rat)^2 * t start +
        intervalSum (fun j => (2 * (j : Rat) + 1) * t (j + 1)) start count := by
  have step (j : Nat) : ((j + 1 : Nat) : Rat)^2 - (j : Rat)^2 = 2 * (j : Rat) + 1 := by
    grind
  simpa only [step] using abel_identity (fun j => (j : Rat)^2) t start count

/-- Positive-index coefficients b1,...,b5 from the published Laurent expansion. -/
def firstFive : List Rat := [1/8, -1/4, 15/128, 0, -47/1024]

def partialEnergy (coefficients : List Rat) : Rat :=
  (List.zipWith (fun (i : Nat) (b : Rat) => ((i + 1 : Nat) : Rat) * b^2)
    (List.range coefficients.length) coefficients).sum

theorem five_coefficient_energy :
    partialEnergy firstFive = 201701/1048576 := by decide +kernel

/-- The inner parameter disk of radius 1/4 supplies the 15/16 budget. -/
def residual : Rat := 15/16 - partialEnergy firstFive

theorem five_coefficient_residual :
    residual = 781339/1048576 := by decide +kernel

/-- Substitute R=2 and N=5 into the exterior squared-error bound. -/
theorem radius_two_budget :
    residual * (1/4)^6 / (6 * (1 - 1/4)) = 781339/19327352832 := by decide +kernel

def fejerTerm (n k : Nat) (b : Rat) : Rat :=
  (1 - (k : Rat) / ((n + 1 : Nat) : Rat)) * b

/-- The difference has coefficients 1/48 and -1/12. Their absolute
    values sum to 5/48, attained in the circle problem at angle pi. -/
theorem first_fejer_difference :
    let a := fejerTerm 2 1 (1/8) - fejerTerm 1 1 (1/8)
    let b := fejerTerm 2 2 (-1/4)
    a = 1/48 ∧ b = -1/12 ∧ a - b = 5/48 := by decide +kernel

end LoopsFormal.MandelbrotSpectrum

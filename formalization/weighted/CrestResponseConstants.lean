import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum

/-!
# Rational centers for the endpoint response certificate

These numbers are centers of proved enclosures, rather than definitions of
the limiting parameter or its endpoint.  The canonical model is identified
with their small neighborhoods in `CrestModelCoordinateBounds`.
-/

namespace CrestResponseConstants

def kRef : ℝ := 1790327491999345703396901 / 10^24
def tRef : ℝ := 1056936162954836358332328 / 10^24
def yRef : ℝ := 178331415818680342642268 / 10^24
def xRef : ℝ := 750308663601865568754437 / 10^24
def vRef : ℝ := 66378192165584559465645 / 10^24
def rRef : ℝ := 66378909816223917964875 / 10^24

/-- All rational centers used by the endpoint certificate are positive. -/
theorem reference_coordinates_positive :
    0 < kRef ∧ 0 < tRef ∧ 0 < yRef ∧ 0 < xRef ∧ 0 < vRef ∧ 0 < rRef := by
  norm_num [kRef,tRef,yRef,xRef,vRef,rRef]

end CrestResponseConstants

import TipComplexMargins

/-!
# Exact finite arithmetic for the first KL decoration at the Misiurewicz tip

ONLY finite orbit interval inequalities and ray-angle modular arithmetic are
kernel checked. All statements identifying the *geometric* Yoccoz puzzle,
landings, domain components, the KL Lemma 2.1, and Kahn's localization
covers are imported classical facts, proved separately in the written audit.
-/

namespace LoopsFormal.TipKLPuzzle

open LoopsFormal.Period27
open LoopsFormal.TipComplexMargins

def imageAt (j : Nat) (x : Int) : Bounds :=
  pointAfterAt unitTip j tipBracket ⟨x, x⟩

/-- Coarse strict bounds show alpha' (the positive preimage of the
    negative dividing fixed point) lies in (7/8,1); f²(0)>1
    lies in the right-hand off-critical Yoccoz depth-one piece.
    Here h_c(y)=y²+y+c has h_c(7/8)<0<h_c(1). -/
theorem top_escape_positive_margins :
    -2 * unitTip < tipBracket.lo ∧
    tipBracket.hi < -(105 * unitTip / 64) ∧
    unitTip < (tipOrbit 2).lo ∧
    0 < (tipOrbit 3).lo ∧
    (tipOrbit 3).hi < unitTip / 4 := by
  decide +kernel

/-- The positive equation f²(t)=alpha' has a root t in (5/16,7/16).
    Its geometric use relies on real monotonicity and on alpha'∈(7/8,1).
    The small period-3 filled Julia set is already inside D(0,1/4). -/
theorem root_vertex_bracket_margins :
    unitTip < (imageAt 2 (5 * unitTip / 16)).lo ∧
    (imageAt 2 (7 * unitTip / 16)).hi < 7 * unitTip / 8 := by
  decide +kernel

/-- A real g=f³ fixed point occurs in (1/16,1/8) by IVT, is in
    the interior of the real restrictive interval I3, and is not an
    f³-periodic phase of the disjoint three-cycle of little K9 sets. -/
theorem outer_return_fixed_point_bracket :
    unitTip / 16 < (imageAt 3 (unitTip / 16)).lo ∧
    (imageAt 3 (unitTip / 8)).hi < unitTip / 8 ∧
    (tipOrbit 6).hi < unitTip / 16 ∧
    unitTip / 8 < (tipOrbit 3).lo := by
  decide +kernel

/-- A real point in (1,9/8) maps to 0 under f³ by IVT.
    The two complex phase-disk enclosures for K3 show it cannot belong
    to K3 ∪ f(K3) ∪ f²(K3). Thus it witnesses an *extra*
    component of (f³)^-1(K3), used for a genuine one-scale
    based-localization coset collision. -/
theorem explicit_extra_inverse_component_margins :
    (imageAt 3 unitTip).hi < 0 ∧
    0 < (imageAt 3 (9 * unitTip / 8)).lo ∧
    (9 * unitTip / 8) <
      (tipOrbit 2).lo - deviation outerRadius 2 ∧
    (tipOrbit 1).hi + deviation outerRadius 1 < -unitTip := by
  decide +kernel

/-- Source-printed p. 6 has q=2,n=1, with P depth 1,
    V^0 and Q_L,Q_R depth 3, and deep qn=q.
    This is NOT a period-3/period-9 return-time comparison. -/
theorem shallow_deep_clock_at_first_escape :
    (1 - 1) * 2 + 1 = 1 ∧
    1 * 2 + 1 = 3 ∧
    (2 * 1 - 1) * 2 + 1 = 3 ∧
    1 * 2 = 2 := by
  decide

/-- Angles here are numerators on the 24-grid:
    alpha (8,16), alpha' (4,20), b_- (10,14),
    v_- (7,17), v_+ (5,19).
    The assertion checks forward ×2/×4 dynamics, NOT ray landing. -/
theorem kl_boundary_ray_modular_dynamics :
    (2 * 8) % 24 = 16 ∧ (2 * 16) % 24 = 8 ∧
    (2 * 4) % 24 = 8 ∧ (2 * 20) % 24 = 16 ∧
    (2 * 7) % 24 = 14 ∧ (2 * 17) % 24 = 10 ∧
    (2 * 5) % 24 = 10 ∧ (2 * 19) % 24 = 14 ∧
    (4 * 7) % 24 = 4 ∧ (4 * 17) % 24 = 20 ∧
    (4 * 5) % 24 = 20 ∧ (4 * 19) % 24 = 4 ∧
    (8 * 7) % 24 = 8 ∧ (8 * 17) % 24 = 16 ∧
    (8 * 5) % 24 = 16 ∧ (8 * 19) % 24 = 8 := by
  decide

#print axioms top_escape_positive_margins
#print axioms root_vertex_bracket_margins
#print axioms outer_return_fixed_point_bracket
#print axioms explicit_extra_inverse_component_margins
#print axioms kl_boundary_ray_modular_dynamics

end LoopsFormal.TipKLPuzzle

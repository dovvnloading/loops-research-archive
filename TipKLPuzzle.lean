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

/--
Three consecutive real inverse returns under g=f³.
The first s₁∈(1,17/16) satisfies g(s₁)=0, the next
s₂∈(6/5,49/40) satisfies g(s₂)=s₁, and the third
s₃∈(31/25,5/4) satisfies g(s₃)=s₂.
These *exist* by the IVT and the strict bounds below.
Consequently f⁹(s₃)=0∈K9, while s₃ is outside the nine
little-Julia phase disks. This realizes an off-cycle component
of (f⁹)^-1(K9), independently of any drawn ray picture.

Lean checks *only* the six exact rational sign inequalities, not IVT.
-/
theorem three_nested_preimage_brackets :
    (imageAt 3 unitTip).hi < 0 ∧
    0 < (imageAt 3 (17 * unitTip / 16)).lo ∧
    (imageAt 3 (6 * unitTip / 5)).hi < unitTip ∧
    17 * unitTip / 16 <
      (imageAt 3 (49 * unitTip / 40)).lo ∧
    (imageAt 3 (31 * unitTip / 25)).hi <
      6 * unitTip / 5 ∧
    49 * unitTip / 40 <
      (imageAt 3 (5 * unitTip / 4)).lo := by
  decide +kernel

def outsidePhaseDisk (j : Nat) (sourceRadius left right : Int) : Bool :=
  (tipOrbit j).hi + deviation sourceRadius j < left ||
  right < (tipOrbit j).lo - deviation sourceRadius j

/-- Every period-nine complex phase enclosure misses the explicit
    noncentral real preimage interval (31/25,5/4). -/
theorem period_nine_extra_preimage_outside_all_phases :
    (List.range 9).all
      (fun j => outsidePhaseDisk j innerShrinkRadius
        (31 * unitTip / 25) (5 * unitTip / 4)) = true := by
  decide +kernel

/-- Same for the outer first inverse preimage (1,17/16). -/
theorem period_three_extra_preimage_outside_all_phases :
    (List.range 3).all
      (fun j => outsidePhaseDisk j outerRadius
        unitTip (17 * unitTip / 16)) = true := by
  decide +kernel

#print axioms three_nested_preimage_brackets
#print axioms period_nine_extra_preimage_outside_all_phases
#print axioms period_three_extra_preimage_outside_all_phases

/--
SECOND LEVEL, for the actual polynomial-like return G=f³ (not the
ambient quadratic f): exact real bracket for its dividing fixed point
a∈(3/32,1/10), hence alpha'_G=-a.

Let b_G be the positive real preimage G(b_G)=-a. The strict
inequalities below force b_G∈(17/100,7/40).
Its central preimages ±t_G solve G(t_G)=b_G, with
t_G∈(1/32,1/16). The exact K9 is in D(0,1/32), so this shows
strict separation from the second-level critical puzzle vertices.

Ray *landing*, internal external angles, and the topological statement
that this is the two-level KL top puzzle are classical/imported.
-/
theorem inner_return_kl_fixed_and_vertex_brackets :
    3 * unitTip / 32 <
      (imageAt 3 (3 * unitTip / 32)).lo ∧
    (imageAt 3 (unitTip / 10)).hi <
      unitTip / 10 ∧
    -(3 * unitTip / 32) <
      (imageAt 3 (17 * unitTip / 100)).lo ∧
    (imageAt 3 (7 * unitTip / 40)).hi <
      -(unitTip / 10) ∧
    7 * unitTip / 40 <
      (imageAt 3 (unitTip / 32)).lo ∧
    (imageAt 3 (unitTip / 16)).hi <
      17 * unitTip / 100 ∧
    (tipOrbit 6).hi < -(unitTip / 10) ∧
    unitTip / 16 < (tipOrbit 3).lo ∧
    -(unitTip / 32) < (tipOrbit 9).lo ∧
    (tipOrbit 9).hi < unitTip / 32 := by
  decide +kernel

/--
Every point of G(U9)=f³(D(0,1/32)) has real part
strictly greater than 7/40, by its complex-disk majorant.
All four *central* G²-preimages of alpha_G=a are contained
in the real interval (-7/40,7/40): ±a and ±b_G.
Therefore no central G³-preimage of a lies in U9;
the genuine second-level Y³_G puzzle Julia vertices
are strictly outside the entire inner polynomial-like U9.
The geometric identification of the four preimages uses
degree-two properness, evenness, and the IVT signs above.
-/
theorem inner_puzzle_all_vertices_outside_inner_disk :
    7 * unitTip / 40 <
      (tipOrbit 3).lo - deviation innerRadius 3 := by
  decide +kernel

#print axioms inner_puzzle_all_vertices_outside_inner_disk

/-- Both top-puzzle escape clocks have q=2,n=1.
    At the second level, a single internal symbol means G²=f⁶,
    while the terminal little return is G³=f⁹. -/
theorem two_distinct_kl_escape_clocks :
    (1 * 2 + 1 = 3) ∧ (1 * 2 = 2) ∧
    (3 * 3 = 9) ∧ (2 * 3 = 6) := by decide

#print axioms inner_return_kl_fixed_and_vertex_brackets
#print axioms two_distinct_kl_escape_clocks

/-- The *actual* dyadic obstruction point: 31/1024 lies in U9
    but outside the certified V9 ⊂ D(0,27/1024). -/
def obstructionPoint : Int := 31 * unitTip / 1024

/-- This point belongs to the real outer restrictive interval I3,
    hence to K3, but not to the central nine-scale K9. -/
theorem obstruction_point_in_outer_real_interval_not_V9 :
    innerShrinkRadius < obstructionPoint ∧
    obstructionPoint < innerRadius ∧
    (tipOrbit 6).hi < obstructionPoint ∧
    obstructionPoint < (tipOrbit 3).lo := by
  decide +kernel

/-- All noncentral physical nine-scale images f^j(V9), 1≤j<9,
    are excluded by their existing strict complex disk enclosures. -/
def obstructionAvoidsNinePhase (j : Nat) : Bool :=
  j = 0 ||
    (tipOrbit j).hi + deviation innerShrinkRadius j < obstructionPoint ||
    obstructionPoint + deviation innerShrinkRadius j < (tipOrbit j).lo

theorem obstruction_point_outside_all_noncentral_nine_phases :
    (List.range 9).all obstructionAvoidsNinePhase = true := by
  decide +kernel

/-- Consequently, at the geometric-analysis level, z=31/1024 is
    in Ω_t9 = U9 \ B9 but is absent from Ω_t3 = U3 \ B3:
    K3 contains I3, while B9 is confined to the nine complex phase
    disks. In particular *identity inclusion* Ω_t9→Ω_t3 is undefined.
    This is a theorem about the actual target complements, **not** a
    source-defined KL 9-to-3 localization sheet functor. -/

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

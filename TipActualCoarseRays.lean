import TipRayPortrait

/-!
# Certified rational ray-sector sieve at the real period-3/9 tip

This module proves FINITE integer arithmetic only. In particular, it does not
formalize the classical complex-analytic ray landing theorem, the alpha puzzle,
Levin's correspondence, or that the geometric domains contain the indicated
preimages. These are explicit written hypotheses in the companion audit.

The physical angular denominator is 2^10*(2^9-1)=523264. Every physical
10-step inverse ray is represented by (228+511*k) or (283+511*k),
0<=k<1024. The critical Y^6 face consists of the four source-authenticated
angular seams (41,43), (53,55), (137,139), (149,151), all divided by 192.
-/

namespace LoopsFormal.TipActualCoarseRays

def den : Nat := 523264

/-- Exact strict rational comparison: `lo/192 < n/den < hi/192` modulo 1. -/
def insideSeam (lo hi n : Nat) : Bool :=
  let x := n % den
  decide (lo * den < 192 * x ∧ 192 * x < hi * den)

/-- Actual physical F=f alpha depth-six central-face seams. -/
def sourceFace (n : Nat) : Bool :=
  insideSeam 41 43 n || insideSeam 53 55 n ||
  insideSeam 137 139 n || insideSeam 149 151 n

/-- Two successive G=f^3 checkpoints in the genuine F-Y^6 face. -/
def survives (n : Nat) : Bool :=
  sourceFace n && sourceFace (8*n)

/-- Every physical depth-ten predecessor of the two period-nine rays. -/
def preimageNumerator (target k : Nat) : Nat := target + 511 * k

def firstFaceCount (target : Nat) : Nat :=
  ((List.range 1024).filter (fun k => sourceFace (preimageNumerator target k))).length

def survivorCount (target : Nat) : Nat :=
  ((List.range 1024).filter (fun k => survives (preimageNumerator target k))).length

/-- Exhaustive check over all 2048 rational ambient inverse-ray angles. -/
theorem actual_physical_face_counts :
    firstFaceCount 228 = 40 ∧ firstFaceCount 283 = 40 ∧
    survivorCount 228 = 16 ∧ survivorCount 283 = 16 := by
  decide +kernel

/-- The 32 source-geometric survivors, in increasing ambient angle order;
    their denominator is 523264. No tuning assumption enters this list. -/
def ambient32 : List Nat :=
  [112137,112192,112648,112703,116225,116280,116736,116791,
   144841,144896,145352,145407,148929,148984,149440,149495,
   373769,373824,374280,374335,377857,377912,378368,378423,
   406473,406528,406984,407039,410561,410616,411072,411127]

/-- Finite list, with every survivor strictly in its two source sectors. -/
theorem ambient32_exactly_thirty_two_distinct_survivors :
    ambient32.length = 32 ∧ ambient32.Nodup ∧
    (∀ n ∈ ambient32, survives n = true ∧
      (n % 511 = 228 ∨ n % 511 = 283)) := by
  decide +kernel

/-- Internal Pi3 angle numerators /112 sorted by physical AMBIENT rank.
    The shift was uniquely fixed by 114/511 -> 5/7. -/
def internalByAmbientRank : List Nat :=
  [59,60,66,67,73,74,80,81,87,88,94,95,101,102,108,109,
   3,4,10,11,17,18,24,25,31,32,38,39,45,46,52,53]

def insideGTopY3 (n : Nat) : Bool :=
  decide (5 * 112 < 24*n ∧ 24*n < 7 * 112) ||
  decide (17 * 112 < 24*n ∧ 24*n < 19 * 112)

def insideGChildY6 (n : Nat) : Bool :=
  decide (41 * 112 < 192*n ∧ 192*n < 43 * 112) ||
  decide (53 * 112 < 192*n ∧ 192*n < 55 * 112) ||
  decide (137 * 112 < 192*n ∧ 192*n < 139 * 112) ||
  decide (149 * 112 < 192*n ∧ 192*n < 151 * 112)

/-- The K9 subfiber occupies exactly the eight central G-sector rays.
    Every other one of the 24 outer K3 rays is outside even G's top Y^3. -/
theorem genuine_G_top_and_child_face_counts :
    (internalByAmbientRank.filter insideGTopY3).length = 8 ∧
    (internalByAmbientRank.filter insideGChildY6).length = 8 := by
  decide +kernel

/-- Explicit 15 landing classes: 14 simple pairs and one critical quartet.
    These are denominators 523264 and come from actual inverse G ray lifting
    through the 25/56 critical-value slit, under the cited analytic assumptions. -/
def landingGroups : List (List Nat) :=
  [[116280,406984],[145352,377912],[112648,410616],[148984,374280],
   [116736,406528],[144896,378368],[112192,411072],[149440,373824],
   [116225,407039],[145407,377857],[112703,410561],[148929,374335],
   [116791,144841,378423,406473],[112137,411127],[149495,373769]]

/-- 12 genuine coarse-only 2-ray classes; the last remaining 3 groups
    are the 2+2+4 fine-stage classes from the previously audited source. -/
def isFineGroup (g : List Nat) : Bool :=
  g == [116736,406528] || g == [144896,378368] ||
  g == [116791,144841,378423,406473]

theorem complete_precritical_landing_partition :
    landingGroups.length = 15 ∧
    landingGroups.flatten.length = 32 ∧
    landingGroups.flatten.Nodup ∧
    (∀ n ∈ landingGroups.flatten, n ∈ ambient32) ∧
    (landingGroups.filter isFineGroup).length = 3 ∧
    (landingGroups.filter (fun g => !isFineGroup g)).length = 12 ∧
    (landingGroups.filter (fun g => !isFineGroup g)).all (fun g => g.length == 2) = true := by
  decide +kernel

/-! The original G depth-three alpha puzzle has five faces occupied by
    these 15 inverse points, with cardinalities 2,4,3,4,2. Computing the
    signature requires only the eight source-landed alpha-ray chords.
    The accompanying independent Python verifier checks every signature. -/

#print axioms actual_physical_face_counts
#print axioms ambient32_exactly_thirty_two_distinct_survivors
#print axioms genuine_G_top_and_child_face_counts
#print axioms complete_precritical_landing_partition

end LoopsFormal.TipActualCoarseRays

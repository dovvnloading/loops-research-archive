import TipLevinComposition

/-!
# Finite formal layer: two sheet-winding characters

The source-specific free-group and local-cover theorems are proved in the
companion mathematical note, not in Lean. This module checks the integer
identities which distinguish the exhibited Z x Z family of actual fine
sheets, plus the previously kernel-proved 8/24 ray cohort.
At the exhibited word b01^k (b00 b01 b02)^n, the winding triplet is
(w00,w01,w02)=(n,k+n,n). Non-normal cosets are never treated as a group.
-/

namespace LoopsFormal.TipSheetGrid

structure Winding where
  w00 : Int
  w01 : Int
  w02 : Int
  deriving DecidableEq, Repr

/-- Coarse peripheral beta0^n has winding (n,n,n). -/
def coarsePeripheral (n : Int) : Winding := ⟨n,n,n⟩

/-- Every conjugate of H=<b00> has abelianized winding (h,0,0). -/
def Hwind (h : Int) : Winding := ⟨h,0,0⟩

/-- The specific actual coset representative b01^k beta0^n. -/
def gridWinding (k n : Int) : Winding := ⟨n,k+n,n⟩

/-- Transverse component character. -/
def delta (w : Winding) : Int := w.w01-w.w02

/-- Within-component peripheral winding character. -/
def nu (w : Winding) : Int := w.w02

theorem two_coordinates (k n : Int) :
    delta (gridWinding k n)=k ∧ nu (gridWinding k n)=n := by
  constructor <;> dsimp [delta,nu,gridWinding] <;> omega

theorem grid_injective_from_charges (k n k' n' : Int)
    (hdelta : delta (gridWinding k n)=delta (gridWinding k' n'))
    (hnu : nu (gridWinding k n)=nu (gridWinding k' n')) :
    k=k' ∧ n=n' := by
  dsimp [delta,nu,gridWinding] at hdelta hnu
  omega

theorem core_loop_shift (k n m : Int) :
    delta (gridWinding k (n+m))=delta (gridWinding k n) ∧
    nu (gridWinding k (n+m))=nu (gridWinding k n)+m := by
  constructor <;> dsimp [delta,nu,gridWinding] <;> omega

theorem nonzero_core_cannot_be_H_winding (m h : Int)
    (a : coarsePeripheral m=Hwind h) : m=0 := by
  have v := congrArg Winding.w02 a
  simpa [coarsePeripheral,Hwind] using v

theorem delta_unchanged_by_coarse_winding (k n m : Int) :
    delta (gridWinding k (n+m))=k := by
  dsimp [delta,gridWinding]
  omega

/-- Actual 8/24 rational cohort was proved in the imported module. -/
theorem source_selected_8_24 :
    (LoopsFormal.TipActualCoarseRays.ambient32.filter
      (fun x => LoopsFormal.TipLevinComposition.fineNumerators.contains x)).length=8 ∧
    (LoopsFormal.TipActualCoarseRays.ambient32.filter
      (fun x => !(LoopsFormal.TipLevinComposition.fineNumerators.contains x))).length=24 := by
  constructor
  · exact LoopsFormal.TipLevinComposition.eight_fine_twenty_four_coarse.1
  · exact LoopsFormal.TipLevinComposition.eight_fine_twenty_four_coarse.2.1

#print axioms two_coordinates
#print axioms grid_injective_from_charges
#print axioms core_loop_shift
#print axioms nonzero_core_cannot_be_H_winding
#print axioms delta_unchanged_by_coarse_winding
#print axioms source_selected_8_24

end LoopsFormal.TipSheetGrid

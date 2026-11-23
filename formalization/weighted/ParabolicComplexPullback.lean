import ParabolicChannel
import Mathlib.Analysis.Complex.Basic

/-! Backward uniqueness for complex quadratic iterates with a prescribed
finite itinerary in the left and right half-planes. -/
namespace LoopsParabolic
open Set Function
noncomputable section

def cquad (c : ℝ) (z : ℂ) : ℂ := z^2+c

@[simp] theorem cquad_ofReal (c x : ℝ) : cquad c (x : ℂ) = (quad c x : ℝ) := by
  simp [cquad,quad]

@[simp] theorem cquad_iterate_ofReal (c x : ℝ) (n : ℕ) :
    (cquad c)^[n] (x : ℂ) = ((quad c)^[n] x : ℝ) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [iterate_succ_apply', iterate_succ_apply', ih, cquad_ofReal]

theorem continuous_cquad (c : ℝ) : Continuous (cquad c) := by unfold cquad; fun_prop

/-- The intermediate iterates lie in matching open half-planes at every
time from 1 through p−1. The initial point is free to switch signs. -/
def sameSheet (c : ℝ) (p : ℕ) (z x : ℂ) : Prop :=
  ∀ j : ℕ, 1 ≤ j → j < p →
    0 < ((cquad c)^[j] z).re * ((cquad c)^[j] x).re

/-- On a common itinerary, the terminal value determines the unordered
initial pair {x,−x}. -/
theorem sameSheet_pullback {c : ℝ} {p : ℕ} {z x : ℂ} (hp : 0<p)
    (hs : sameSheet c p z x) (heq : (cquad c)^[p] z = (cquad c)^[p] x) :
    z=x ∨ z= -x := by
  induction p with
  | zero => omega
  | succ n ih =>
    rw [iterate_succ_apply',iterate_succ_apply'] at heq
    have sqs : ((cquad c)^[n] z)^2 = ((cquad c)^[n] x)^2 := add_right_cancel heq
    have branches := sq_eq_sq_iff_eq_or_eq_neg.mp sqs
    by_cases hn : n=0
    · subst n
      exact branches
    · have ne : (cquad c)^[n] z ≠ -(cquad c)^[n] x := by
        intro neg
        have h := hs n (by omega) (by omega)
        rw [neg,Complex.neg_re] at h
        nlinarith only [h,sq_nonneg (((cquad c)^[n] x).re)]
      exact ih (by omega) (fun j lo hi => hs j lo (by omega)) (branches.resolve_right ne)

/-- Each finite half-plane itinerary is an open set in the physical
complex plane. The reference point may itself be complex. -/
theorem isOpen_sameSheet (c : ℝ) (p : ℕ) (x : ℂ) : IsOpen {z | sameSheet c p z x} := by
  let test (j : Fin p) := {z : ℂ | 1≤j.val →
    0 < ((cquad c)^[j.val] z).re * ((cquad c)^[j.val] x).re}
  have eqs : {z | sameSheet c p z x} = ⋂ j : Fin p, test j := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    exact ⟨fun h j lo => h j lo j.isLt,
      fun h j lo hi => h ⟨j,hi⟩ lo⟩
  rw [eqs]
  apply isOpen_iInter_of_finite
  intro j
  by_cases h : 1≤j.val
  · have hc := (Complex.continuous_re.comp ((continuous_cquad c).iterate j.val)).mul
      (continuous_const (y:=((cquad c)^[j.val] x).re))
    simpa [test,h] using isOpen_lt (continuous_const (y:=(0:ℝ))) hc
  · simp [test,h]

#print axioms sameSheet_pullback
#print axioms isOpen_sameSheet
end
end LoopsParabolic

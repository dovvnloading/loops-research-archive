import Mathlib

/-!
# Independent phase words in closed lifts

Concatenation retains every temporal occurrence. Two different closed lifts
of the same target loop generate an injective family indexed by arbitrary
finite Boolean words, all with the same source basepoint and target path.
-/

namespace LoopsCriticalPhaseWords

open Set Function

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- With the standard timed concatenation, equality remembers both
halves. No quotient by path homotopy or by reparameterization is used. -/
theorem path_trans_eq_iff {x y z : X}
    (p p' : Path x y) (q q' : Path y z) :
    p.trans q = p'.trans q' ↔ p = p' ∧ q = q' := by
  constructor
  · intro h
    constructor
    · ext t
      have ht : (t : ℝ)/2 ≤ 1/2 := by linarith [t.property.2]
      have he := congrArg (fun r : Path x z => r.extend ((t : ℝ)/2)) h
      rw [Path.extend_trans_of_le_half _ _ ht,
        Path.extend_trans_of_le_half _ _ ht,
        show (2 : ℝ)*((t : ℝ)/2) = (t : ℝ) by ring,
        Path.extend_apply _ t.property, Path.extend_apply _ t.property] at he
      exact he
    · ext t
      have ht : (1/2 : ℝ) ≤ ((t : ℝ)+1)/2 := by linarith [t.property.1]
      have he := congrArg (fun r : Path x z => r.extend (((t : ℝ)+1)/2)) h
      rw [Path.extend_trans_of_half_le _ _ ht,
        Path.extend_trans_of_half_le _ _ ht,
        show (2 : ℝ)*(((t : ℝ)+1)/2)-1 = (t : ℝ) by ring,
        Path.extend_apply _ t.property, Path.extend_apply _ t.property] at he
      exact he
  · rintro ⟨rfl, rfl⟩
    rfl

/-- A finite word of based source loops, with its exact recursive clock. -/
def loopWord {x : X} (L : Bool → Path x x) :
    (n : ℕ) → (Fin n → Bool) → Path x x
  | 0, _ => Path.refl x
  | n+1, s => (L (s 0)).trans (loopWord L n (fun i => s i.succ))

/-- Every phase word is retained, even though all projected letters may
be identical. The final constant interval is fixed for all words. -/
theorem loopWord_injective {x : X} (L : Bool → Path x x)
    (hL : Injective L) (n : ℕ) : Injective (loopWord L n) := by
  induction n with
  | zero =>
    intro s t _
    funext i
    exact Fin.elim0 i
  | succ n ih =>
    intro s t h
    change (L (s 0)).trans (loopWord L n (fun i => s i.succ)) =
      (L (t 0)).trans (loopWord L n (fun i => t i.succ)) at h
    obtain ⟨hhead, htail⟩ := (path_trans_eq_iff _ _ _ _).mp h
    have hzero := hL hhead
    have hsucc := ih htail
    funext i
    refine Fin.cases ?_ ?_ i
    · exact hzero
    · intro j
      exact congrFun hsucc j

/-- The whole word remains in the physical source when both letters do. -/
theorem loopWord_range {x : X} (L : Bool → Path x x) (A : Set X)
    (hx : x ∈ A) (hL : ∀ b, range (L b) ⊆ A)
    (n : ℕ) (s : Fin n → Bool) : range (loopWord L n s) ⊆ A := by
  induction n generalizing s with
  | zero =>
    rintro z ⟨t, rfl⟩
    exact hx
  | succ n ih =>
    rw [loopWord, Path.trans_range]
    exact union_subset (hL _) (ih _)

/-- Common projected letters give a common complete projected word. -/
theorem loopWord_common_projection {x : X} (L : Bool → Path x x)
    (f : X → Y) (hf : Continuous f) (Q : Path (f x) (f x))
    (hL : ∀ b, (L b).map hf = Q) (n : ℕ) (s : Fin n → Bool) :
    (loopWord L n s).map hf =
      loopWord (fun _ => Q) n (fun _ => false) := by
  induction n generalizing s with
  | zero =>
    ext t
    rfl
  | succ n ih =>
    change ((L (s 0)).trans (loopWord L n (fun i => s i.succ))).map hf =
      Q.trans (loopWord (fun _ => Q) n (fun _ => false))
    rw [Path.map_trans, hL, ih]

/-- Two distinct based loops with one projection produce 2^N distinct
closed source routes over one common target loop, for every N. -/
theorem two_loops_independent_words {x : X}
    (p q : Path x x) (hne : p ≠ q)
    (f : X → Y) (hf : Continuous f) (hproj : p.map hf = q.map hf)
    (A : Set X) (hx : x ∈ A) (hp : range p ⊆ A) (hq : range q ⊆ A)
    (n : ℕ) :
    ∃ γ : Path (f x) (f x), ∃ Γ : (Fin n → Bool) → Path x x,
      Injective Γ ∧ (∀ s, range (Γ s) ⊆ A) ∧
        ∀ s, (Γ s).map hf = γ := by
  let L : Bool → Path x x := fun b => if b then q else p
  have hL : Injective L := by
    intro s t h
    cases s <;> cases t
    · rfl
    · exact (hne (by simpa [L] using h)).elim
    · exact (hne (by simpa [L] using h.symm)).elim
    · rfl
  have hrange (b : Bool) : range (L b) ⊆ A := by
    cases b
    · exact hp
    · exact hq
  have hcommon (b : Bool) : (L b).map hf = p.map hf := by
    cases b
    · rfl
    · exact hproj.symm
  refine ⟨loopWord (fun _ => p.map hf) n (fun _ => false),
    loopWord L n, loopWord_injective L hL n, ?_, ?_⟩
  · intro s
    exact loopWord_range L A hx hrange n s
  · intro s
    exact loopWord_common_projection L f hf (p.map hf) hcommon n s

end LoopsCriticalPhaseWords

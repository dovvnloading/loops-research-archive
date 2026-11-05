import CloneGraph

/-!
# Gate-avoiding first-return paths in the delayed five-vertex graph

Gate e is vertex 0 and gate f is vertex n+3. A FirstReturn path
ends at its declared target gate and avoids BOTH gates at every
intermediate vertex. We prove its possible lengths and rule out
self-first-returns. These are support results; multiplicities of
edge-occurrence paths are still a separate formal obligation.
-/

namespace LoopsFormal.CloneGraph

def IsGate (n : Nat) (v : Vertex n) : Prop :=
  v = hub n ∨ v = secondGate n

inductive FirstReturn (n : Nat) (target : Vertex n) :
    Nat → Vertex n → Prop where
  | finish {u : Vertex n} (h : Edge n u target) :
      FirstReturn n target 1 u
  | advance {k : Nat} {u v : Vertex n}
      (h : Edge n u v) (hnot : ¬ IsGate n v)
      (tail : FirstReturn n target k v) :
      FirstReturn n target (k + 1) u

private theorem below_second_step (n : Nat) {u v : Vertex n}
    (h : Edge n u v) (hu : u.val < n + 3)
    (hnot : ¬ IsGate n v) : v.val < n + 3 := by
  have hneq : v.val ≠ n + 3 := by
    intro hv
    apply hnot
    right
    apply Fin.ext
    simpa [secondGate] using hv
  dsimp [Edge] at h
  cases h with
  | inl hs => omega
  | inr rest =>
      cases rest with
      | inl hw =>
          have hsize : n + 3 < size n := by
            dsimp [size]
            omega
          omega
      | inr hc => omega

private theorem above_second_step (n : Nat) {u v : Vertex n}
    (h : Edge n u v) (hu : n + 3 ≤ u.val)
    (hnot : ¬ IsGate n v) : n + 3 ≤ v.val := by
  have hnonzero : v.val ≠ 0 := by
    intro hv
    apply hnot
    left
    apply Fin.ext
    simpa [hub] using hv
  dsimp [Edge] at h
  cases h with
  | inl hs => omega
  | inr rest =>
      cases rest with
      | inl hw => exact False.elim (hnonzero hw.2)
      | inr hc => omega

theorem first_to_f_length_support (n : Nat) :
    ∀ {u : Vertex n} {k : Nat},
      FirstReturn n (secondGate n) k u →
      u.val < n + 3 →
      (u.val + k = n + 3 ∨
        (u.val ≤ n ∧ u.val + k + 1 = n + 3)) := by
  intro u k path
  induction path with
  | finish hedge =>
      intro hu
      dsimp [Edge] at hedge
      cases hedge with
      | inl hs =>
          left
          dsimp [secondGate] at hs
          omega
      | inr rest =>
          cases rest with
          | inl hw =>
              dsimp [secondGate] at hw
              omega
          | inr hc =>
              dsimp [secondGate] at hc
              omega
  | @advance k u v hedge hnot tail ih =>
      intro hu
      have hvlt := below_second_step n hedge hu hnot
      have htail := ih hvlt
      dsimp [Edge] at hedge
      cases hedge with
      | inl hs =>
          cases htail with
          | inl hl => exact Or.inl (by omega)
          | inr hr => exact Or.inr ⟨by omega, by omega⟩
      | inr rest =>
          cases rest with
          | inl hw =>
              have hsize : n + 3 < size n := by
                dsimp [size]
                omega
              omega
          | inr hc =>
              cases htail with
              | inl hl => exact Or.inr ⟨by omega, by omega⟩
              | inr hr => omega

theorem first_to_e_length_support (n : Nat) :
    ∀ {u : Vertex n} {k : Nat},
      FirstReturn n (hub n) k u →
      n + 3 ≤ u.val → u.val + k = size n := by
  intro u k path
  induction path with
  | finish hedge =>
      intro hu
      dsimp [Edge] at hedge
      cases hedge with
      | inl hs =>
          dsimp [hub] at hs
          omega
      | inr rest =>
          cases rest with
          | inl hw => omega
          | inr hc =>
              dsimp [hub] at hc
              omega
  | @advance k u v hedge hnot tail ih =>
      intro hu
      have hv := above_second_step n hedge hu hnot
      have ht := ih hv
      dsimp [Edge] at hedge
      cases hedge with
      | inl hs => omega
      | inr rest =>
          cases rest with
          | inl hw => omega
          | inr hc => omega

theorem cannot_return_to_e_before_f (n : Nat) :
    ∀ {u : Vertex n} {k : Nat},
      FirstReturn n (hub n) k u →
      u.val < n + 3 → False := by
  intro u k path
  induction path with
  | finish hedge =>
      intro hu
      dsimp [Edge] at hedge
      cases hedge with
      | inl hs =>
          dsimp [hub] at hs
          omega
      | inr rest =>
          cases rest with
          | inl hw =>
              have hs : n + 3 < size n := by
                dsimp [size]
                omega
              omega
          | inr hc =>
              dsimp [hub] at hc
              omega
  | @advance k u v hedge hnot tail ih =>
      intro hu
      have hv := below_second_step n hedge hu hnot
      exact ih hv

theorem cannot_return_to_f_after_f (n : Nat) :
    ∀ {u : Vertex n} {k : Nat},
      FirstReturn n (secondGate n) k u →
      n + 3 ≤ u.val → False := by
  intro u k path
  induction path with
  | finish hedge =>
      intro hu
      dsimp [Edge] at hedge
      cases hedge with
      | inl hs =>
          dsimp [secondGate] at hs
          omega
      | inr rest =>
          cases rest with
          | inl hw =>
              dsimp [secondGate] at hw
              omega
          | inr hc =>
              dsimp [secondGate] at hc
              omega
  | @advance k u v hedge hnot tail ih =>
      intro hu
      have hv := above_second_step n hedge hu hnot
      exact ih hv

theorem no_e_to_e_first_return (n k : Nat) :
    ¬ FirstReturn n (hub n) k (hub n) := by
  intro h
  apply cannot_return_to_e_before_f n h
  dsimp [hub]
  omega

theorem no_f_to_f_first_return (n k : Nat) :
    ¬ FirstReturn n (secondGate n) k (secondGate n) := by
  intro h
  apply cannot_return_to_f_after_f n h
  dsimp [secondGate]
  omega

theorem e_to_f_first_return_lengths (n : Nat) {k : Nat}
    (h : FirstReturn n (secondGate n) k (hub n)) :
    k = n + 2 ∨ k = n + 3 := by
  have ht := first_to_f_length_support n h (by dsimp [hub]; omega)
  cases ht with
  | inl hp =>
      right
      dsimp [hub] at hp
      omega
  | inr hp =>
      left
      dsimp [hub] at hp
      omega

theorem f_to_e_first_return_length (n : Nat) {k : Nat}
    (h : FirstReturn n (hub n) k (secondGate n)) :
    k = n + 2 := by
  have ht := first_to_e_length_support n h (by dsimp [secondGate]; omega)
  dsimp [size, secondGate] at ht
  omega

end LoopsFormal.CloneGraph

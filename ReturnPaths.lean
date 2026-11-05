import ReturnBlocks

/-!
# Type-valued first-return paths: exact multiplicities

The existing FirstReturn predicate is Prop-valued, proving only which
routes can exist. This module retains the actual intermediate vertices
in a Type-valued path, and proves that each permitted gate-to-gate path
of fixed length is unique, for every clone length n.
-/

namespace LoopsFormal.CloneGraph

inductive ReturnPath (n : Nat) (target : Vertex n) :
    Nat → Vertex n → Type where
  | finish {u : Vertex n} (h : Edge n u target) :
      ReturnPath n target 1 u
  | advance {k : Nat} {u v : Vertex n}
      (h : Edge n u v) (hnot : ¬ IsGate n v)
      (tail : ReturnPath n target k v) :
      ReturnPath n target (k + 1) u

/-- Forget the data while retaining the same first-return assertion. -/
def ReturnPath.toProp {n : Nat} {target : Vertex n}
    {k : Nat} {u : Vertex n} :
    ReturnPath n target k u → FirstReturn n target k u
  | .finish h => .finish h
  | .advance h hnot tail => .advance h hnot tail.toProp

/-- Recover a concrete witness in Prop (Nonempty) from an existing
    first-return proof. There is no illicit Prop-to-Type elimination. -/
theorem returnPath_nonempty_of_prop {n : Nat} {target : Vertex n}
    {k : Nat} {u : Vertex n}
    (p : FirstReturn n target k u) :
    Nonempty (ReturnPath n target k u) := by
  induction p with
  | finish h =>
      exact ⟨ReturnPath.finish h⟩
  | advance h hnot tail ih =>
      cases ih with
      | intro route =>
          exact ⟨ReturnPath.advance h hnot route⟩

private theorem same_next_to_f (n : Nat) {u v w : Vertex n} {k : Nat}
    (h : Edge n u v) (h' : Edge n u w)
    (pv : FirstReturn n (secondGate n) k v)
    (pw : FirstReturn n (secondGate n) k w) : v = w := by
  have hv : v.val < n + 3 := by
    by_contra hn
    have hge : n + 3 ≤ v.val := by omega
    exact cannot_return_to_f_after_f n pv hge
  have hw : w.val < n + 3 := by
    by_contra hn
    have hge : n + 3 ≤ w.val := by omega
    exact cannot_return_to_f_after_f n pw hge
  have phv := first_to_f_length_support n pv hv
  have phw := first_to_f_length_support n pw hw
  apply Fin.ext
  dsimp [Edge, size] at h h'
  omega

private theorem same_next_to_e (n : Nat) {u v w : Vertex n} {k : Nat}
    (h : Edge n u v) (h' : Edge n u w)
    (pv : FirstReturn n (hub n) k v)
    (pw : FirstReturn n (hub n) k w) : v = w := by
  have hv : n + 3 ≤ v.val := by
    by_contra hn
    have hlt : v.val < n + 3 := by omega
    exact cannot_return_to_e_before_f n pv hlt
  have hw : n + 3 ≤ w.val := by
    by_contra hn
    have hlt : w.val < n + 3 := by omega
    exact cannot_return_to_e_before_f n pw hlt
  apply Fin.ext
  dsimp [Edge, size] at h h'
  omega

/-- All concrete paths to a specified gate with the same source and
    number of edges are equal. -/
theorem returnPaths_subsingleton (n : Nat) (target : Vertex n)
    (htarget : IsGate n target) :
    ∀ {k : Nat} {u : Vertex n},
      (p q : ReturnPath n target k u) → p = q := by
  intro k u p
  induction p with
  | finish hedge =>
      intro q
      cases q with
      | finish h' =>
          rfl
      | advance h hnot tail =>
          cases tail
  | @advance k u v hedge hnot tail ih =>
      intro q
      cases q with
      | finish h' =>
          cases tail
      | @advance k' u' w hedge' hnot' tail' =>
          have hv : v = w := by
            cases htarget with
            | inl he =>
                subst target
                exact same_next_to_e n hedge hedge' tail.toProp tail'.toProp
            | inr hf =>
                subst target
                exact same_next_to_f n hedge hedge' tail.toProp tail'.toProp
          subst w
          have htail : tail = tail' := ih tail'
          cases htail
          rfl

/-- Exactly one short e-to-f first return for every n. -/
theorem unique_e_to_f_short (n : Nat) :
    ∃! p : ReturnPath n (secondGate n) (n + 2) (hub n), True := by
  obtain ⟨p⟩ := returnPath_nonempty_of_prop
    (e_to_f_short_first_return_exists n)
  refine ⟨p, trivial, ?_⟩
  intro q _
  exact returnPaths_subsingleton n (secondGate n) (Or.inr rfl) q p

/-- Exactly one long e-to-f first return for every n. -/
theorem unique_e_to_f_long (n : Nat) :
    ∃! p : ReturnPath n (secondGate n) (n + 3) (hub n), True := by
  obtain ⟨p⟩ := returnPath_nonempty_of_prop
    (e_to_f_long_first_return_exists n)
  refine ⟨p, trivial, ?_⟩
  intro q _
  exact returnPaths_subsingleton n (secondGate n) (Or.inr rfl) q p

/-- Exactly one f-to-e first return for every n. -/
theorem unique_f_to_e (n : Nat) :
    ∃! p : ReturnPath n (hub n) (n + 2) (secondGate n), True := by
  obtain ⟨p⟩ := returnPath_nonempty_of_prop
    (f_to_e_first_return_exists n)
  refine ⟨p, trivial, ?_⟩
  intro q _
  exact returnPaths_subsingleton n (hub n) (Or.inl rfl) q p

/-- Every other e-to-f length has no actual first-return route. -/
theorem no_other_e_to_f_lengths (n k : Nat)
    (hshort : k ≠ n + 2) (hlong : k ≠ n + 3) :
    ¬ Nonempty (ReturnPath n (secondGate n) k (hub n)) := by
  intro h
  cases h with
  | intro p =>
      have lengths := e_to_f_first_return_lengths n p.toProp
      cases lengths with
      | inl hs => exact hshort hs
      | inr hl => exact hlong hl

/-- Every other f-to-e length has no actual first-return route. -/
theorem no_other_f_to_e_lengths (n k : Nat)
    (hlen : k ≠ n + 2) :
    ¬ Nonempty (ReturnPath n (hub n) k (secondGate n)) := by
  intro h
  cases h with
  | intro p =>
      exact hlen (f_to_e_first_return_length n p.toProp)

theorem no_e_to_e_concrete (n k : Nat) :
    ¬ Nonempty (ReturnPath n (hub n) k (hub n)) := by
  intro h
  cases h with
  | intro p => exact no_e_to_e_first_return n k p.toProp

theorem no_f_to_f_concrete (n k : Nat) :
    ¬ Nonempty (ReturnPath n (secondGate n) k (secondGate n)) := by
  intro h
  cases h with
  | intro p => exact no_f_to_f_first_return n k p.toProp

end LoopsFormal.CloneGraph

import Paper2Phase

/-!
# Two-scale phase projection for an actual nested return

This reusable, conditional theorem is the logical bridge between a
physical return time 3, an inner return time 9, and the quotient from
nine phase windows to the three outer phase windows.

The particular real quadratic's interval existence, inclusion and
real-image disjointness are proved separately by an exact signed-integer
interval certificate: research/independent_audits/verify_real_nested_3_9.py

No analytic assertion about complex puzzle pieces, Julia sets, or MLC
is imported or assumed by this module.
-/

namespace LoopsFormal.RealTwoScale

open LoopsFormal.Paper2

variable {α : Type}

/-- A nested period-9 restrictive set I9 within a forward-invariant
    period-3 outer set I3 admits a canonical 9-to-3 phase projection.

    For every point x in I9 and time j, its actual iterate f^j(x)
    has the form f^(j mod 3)(y) for some y inside I3. Crucially the
    conclusion follows from *physical* f^3 invariance, not a relabeling
    axiom or an assumed two-scale marking correspondence. -/
theorem nested_three_nine_phase_transport
    (f : α → α) (I3 I9 : α → Prop)
    (hcontain : ∀ x, I9 x → I3 x)
    (hinvariant : ∀ y, I3 y → I3 (iterate f 3 y)) :
    ∀ x, I9 x → ∀ j : Nat,
      ∃ y, I3 y ∧ iterate f j x = iterate f (j % 3) y := by
  intro x hx j
  exact terminal_root_phase_route f I3 3 j hinvariant x
    (hcontain x hx)

/-- The underlying nine-phase ring maps to the three-phase ring. -/
theorem reduction_of_nine_phase (j : Nat) :
    (j % 9) % 3 = j % 3 := by
  omega

/-- The phase quotient commutes with one physical forward step. -/
theorem phase_projection_respects_successor (j : Nat) :
    ((j + 1) % 9) % 3 = ((j % 3) + 1) % 3 := by
  omega

/-- Three steps preserve the outer phase of the nine-level itinerary. -/
theorem inner_clock_preserves_outer_phase (j : Nat) :
    ((j + 3) % 9) % 3 = (j % 9) % 3 := by
  omega

end LoopsFormal.RealTwoScale

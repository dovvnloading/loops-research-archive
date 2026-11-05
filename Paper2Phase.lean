import Lean

/-!
# Direct-decoration phase and critical-orbit safeguards

These are independently kernel-checked *conditional* deductions from
Paper 2's primitive polynomial-like cycle hypotheses. No holomorphic
puzzle-boundary statement is being smuggled in as a theorem of Lean.

A primitive disjoint terminal cycle excludes the critical orbit from
the dividing fixed point; also, if every nonzero cycle phase is outside
the chosen return base, a return under f^(n*q) is possible only when
n*q is zero modulo the primitive period.

The phase result is useful precisely because the deep-block fallback
changes the branch clock from q to n*q.
-/

namespace LoopsFormal.Paper2

variable {α : Type}

/-- The forward orbit of a self-map, with no analytic hypotheses. -/
def iterate (f : α → α) : Nat → α → α
  | 0, x => x
  | k + 1, x => f (iterate f k x)

/-- Exact time-addition law. -/
theorem iterate_add (f : α → α) (m k : Nat) (x : α) :
    iterate f (m + k) x = iterate f k (iterate f m x) := by
  induction k with
  | zero =>
      simp [iterate]
  | succ k ih =>
      simpa [Nat.add_succ, iterate, ih]

/-- An orbit at a fixed point is stationary for every later iterate. -/
theorem iterate_fixed (f : α → α) (a : α) (ha : f a = a) (k : Nat) :
    iterate f k a = a := by
  induction k with
  | zero => rfl
  | succ k ih => simpa [iterate, ih, ha]

/-- A periodically forward-invariant root contains the critical
    orbit at all multiples of its primitive return period. -/
theorem all_return_times_in_root (f : α → α) (K : α → Prop)
    (p : Nat) (critical : α)
    (h0 : K critical)
    (hblock : ∀ x, K x → K (iterate f p x)) :
    ∀ k : Nat, K (iterate f (k * p) critical) := by
  intro k
  induction k with
  | zero => simpa [iterate] using h0
  | succ k ih =>
      have h := hblock (iterate f (k * p) critical) ih
      simpa [Nat.succ_mul, iterate_add] using h

/-- A fixed point cannot be hit by the critical orbit of a
    period-p primitive disjoint terminal cycle.

    K is the terminal filled Julia root. Periodic forward invariance
    f^p(K)⊆K and K∩f(K)=∅ are *hypotheses*, not conclusions inferred
    from generic holomorphic dynamics.
-/
theorem primitive_cycle_excludes_fixed_landing
    (f : α → α) (K : α → Prop)
    (p : Nat) (critical a : α)
    (hp : 1 ≤ p)
    (h0 : K critical)
    (hblock : ∀ x, K x → K (iterate f p x))
    (hdisj : ∀ x, K x → ¬ K (f x))
    (hfixed : f a = a) :
    ∀ m : Nat, iterate f m critical ≠ a := by
  intro m hm
  have hmul : m ≤ m * p := by
    calc
      m = m * 1 := by simp
      _ ≤ m * p := Nat.mul_le_mul_left m hp
  let d := m * p - m
  have hd : m + d = m * p := by
    dsimp [d]
    omega
  have hhit :
      iterate f (m * p) critical = a := by
    calc
      iterate f (m * p) critical =
          iterate f (m + d) critical := by rw [hd]
      _ = iterate f d (iterate f m critical) :=
          iterate_add f m d critical
      _ = a := by rw [hm, iterate_fixed f a hfixed d]
  have hmember : K (iterate f (m * p) critical) :=
    all_return_times_in_root f K p critical h0 hblock m
  have ha : K a := by
    rw [hhit] at hmember
    exact hmember
  exact (hdisj a ha) (by simpa [hfixed] using ha)

/-- A general clock/phase obstruction: if every nonzero primitive
    phase lies outside B, then an actual return to B under f^tau
    can occur only at phase zero modulo p. The phase routing is
    an explicitly required *dynamical input*.
-/
theorem return_to_base_requires_aligned_phase
    (f : α → α) (p tau : Nat) (hp : 0 < p)
    (root B : α → Prop) (phase : Nat → α → Prop)
    (hseparate : ∀ r : Nat, 0 < r → r < p →
      ∀ y : α, phase r y → ¬ B y)
    (hroute : ∀ x : α, root x →
      phase (tau % p) (iterate f tau x))
    (hreturn : ∃ x : α, root x ∧ B (iterate f tau x)) :
    tau % p = 0 := by
  by_cases hzero : tau % p = 0
  · exact hzero
  · have hpos : 0 < tau % p := by omega
    have hlt : tau % p < p := Nat.mod_lt tau hp
    obtain ⟨x, hx, hB⟩ := hreturn
    exact False.elim ((hseparate (tau % p) hpos hlt
      (iterate f tau x) (hroute x hx)) hB)


/-- Recover the actual terminal root phase from periodic forward invariance.
    After tau steps the orbit lies in the phase (tau mod p) image
    of the original root. This uses no independent phase-routing axiom. -/
theorem terminal_root_phase_route
    (f : α → α) (K : α → Prop) (p tau : Nat)
    (hstart : ∀ x, K x → K (iterate f p x))
    (x : α) (hx : K x) :
    ∃ y : α, K y ∧
      iterate f tau x = iterate f (tau % p) y := by
  let k := tau / p
  let y := iterate f (k * p) x
  have hy : K y := by
    exact all_return_times_in_root f K p x hx hstart k
  refine ⟨y, hy, ?_⟩
  have hdecomp : tau = k * p + tau % p := by
    have h : tau % p + p * (tau / p) = tau :=
      Nat.mod_add_div tau p
    dsimp [k]
    omega
  rw [hdecomp, iterate_add]
  rfl

/-- Source-facing phase obstruction without a separately postulated
    route table. If each nonzero primitive root-cycle phase lies
    outside the chosen first-return base B, a deep block can meet
    B only when its clock is a multiple of the primitive period. -/
theorem no_deep_root_return_without_phase_alignment
    (f : α → α) (K B : α → Prop)
    (p tau : Nat) (hp : 0 < p)
    (hcycle : ∀ x : α, K x → K (iterate f p x))
    (houtside : ∀ r : Nat, 0 < r → r < p →
      ∀ y : α, K y → ¬ B (iterate f r y))
    (hreturn : ∃ x : α, K x ∧ B (iterate f tau x)) :
    tau % p = 0 := by
  by_cases hz : tau % p = 0
  · exact hz
  · have hpos : 0 < tau % p := by omega
    have hlt : tau % p < p := Nat.mod_lt tau hp
    obtain ⟨x, hx, hB⟩ := hreturn
    obtain ⟨y, hy, hroute⟩ :=
      terminal_root_phase_route f K p tau hcycle x hx
    have hn : ¬ B (iterate f (tau % p) y) :=
      houtside (tau % p) hpos hlt y hy
    rw [hroute] at hB
    exact False.elim (hn hB)

/-- In particular, changing to the deep block time n*q requires
    p-period phase alignment for any proposed return to B. -/
theorem deep_block_return_requires_phase_alignment
    (f : α → α) (K B : α → Prop)
    (p n q : Nat) (hp : 0 < p)
    (hcycle : ∀ x : α, K x → K (iterate f p x))
    (houtside : ∀ r : Nat, 0 < r → r < p →
      ∀ y : α, K y → ¬ B (iterate f r y))
    (hreturn : ∃ x : α, K x ∧ B (iterate f (n * q) x)) :
    (n * q) % p = 0 := by
  exact no_deep_root_return_without_phase_alignment
    f K B p (n * q) hp hcycle houtside hreturn

/-- Algebraic regression: the deep time n*q need not have the same
    root-cycle phase as the shallow time q. -/
theorem deep_clock_can_change_root_phase :
    (2 % 3 : Nat) ≠ (2 * 2) % 3 := by
  decide

end LoopsFormal.Paper2

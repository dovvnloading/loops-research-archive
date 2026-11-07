import Mathlib

/-!
# KKL parabolic-tail insertion: source-typed orbit clocks and gate acyclicity certificates

The source's k-limb insertion satisfies physical equations
  g^[1] (φ x) = φ (f x) on ordinary limbs,
  g^[2] (φ x) = φ (f x) on the inserted limb.
The time-change theorem below is valid for ANY such step relation,
including the actual Julia continua, with no local connectivity assumption.

The gate-cycle theorems are purely finite:
  * an actual return-graph arrow can be simulated by a decreasing
    old rank, or a strictly decreasing local stutter budget;
  * then the new graph cannot contain a directed cycle.
THE ANALYTIC PRIME-END ACCESS EXTENSION AND THE HYPOTHESIS THAT
REAL KKL GATE ARROWS OBEY THAT SIMULATION ARE NOT PROVED HERE.
-/

namespace LoopsKKLLimbInsertion

/-- Exact number of steps in the new system after n old steps,
where each old iterate consumes the source-defined clock increment. -/
def clock {X : Type*} (f : X → X) (phase : X → ℕ) (x : X) :
    ℕ → ℕ
  | 0 => 0
  | n + 1 =>
      clock f phase x n + phase (Nat.iterate f n x)

/-- Physical orbit time-change under source-defined one-step/two-step
insertion. This is a true theorem about actual points if the published
limb-by-limb equation is supplied as hlocal. -/
theorem clocked_orbit_semiconjugacy
    {X Y : Type*}
    (f : X → X) (g : Y → Y) (φ : X → Y)
    (phase : X → ℕ)
    (hlocal : ∀ x, Nat.iterate g (phase x) (φ x) = φ (f x))
    (x : X) (n : ℕ) :
    Nat.iterate g (clock f phase x n) (φ x) =
      φ (Nat.iterate f n x) := by
  induction n with
  | zero =>
      simp [clock]
  | succ n ih =>
      have ht :
          clock f phase x (n + 1) =
            phase (Nat.iterate f n x) + clock f phase x n := by
        simp [clock, Nat.add_comm]
      calc
        Nat.iterate g (clock f phase x (n + 1)) (φ x)
            = Nat.iterate g
                (phase (Nat.iterate f n x) + clock f phase x n)
                (φ x) := by rw [ht]
        _ = Nat.iterate g (phase (Nat.iterate f n x))
              (Nat.iterate g (clock f phase x n) (φ x)) := by
                rw [Function.iterate_add_apply]
        _ = Nat.iterate g (phase (Nat.iterate f n x))
              (φ (Nat.iterate f n x)) := by rw [ih]
        _ = φ (f (Nat.iterate f n x)) := hlocal _
        _ = φ (Nat.iterate f (n + 1) x) := by
              rw [Function.iterate_succ_apply']

/-- A source limb insertion with one or two new physical steps
gives a clock between n and 2n on every old orbit. -/
theorem clock_one_or_two_bounds
    {X : Type*} (f : X → X) (phase : X → ℕ)
    (hphase : ∀ x, phase x = 1 ∨ phase x = 2)
    (x : X) (n : ℕ) :
    n ≤ clock f phase x n ∧ clock f phase x n ≤ 2 * n := by
  induction n with
  | zero =>
      simp [clock]
  | succ n ih =>
      rcases hphase (Nat.iterate f n x) with h | h
      · simp only [clock, h]
        constructor <;> omega
      · simp only [clock, h]
        constructor <;> omega

/-- A finite or infinite source-defined FIRST-RETURN gate map is partial:
none means saturation, strict marked-length growth, or no qualifying
critical return. Its iterate only follows truly defined return arrows. -/
def partialIter {X : Type*} (step : X → Option X) :
    ℕ → X → Option X
  | 0, x => some x
  | n + 1, x => (step x).bind (partialIter step n)

/-- A nat-valued strict rank drop bounds every actual partial-return
path and forbids a nonempty periodic path. -/
theorem partialIter_rank_le
    {X : Type*} (step : X → Option X) (rank : X → ℕ)
    (hstep : ∀ x y, step x = some y → rank y < rank x) :
    ∀ n x y, partialIter step n x = some y → rank y ≤ rank x := by
  intro n
  induction n with
  | zero =>
      intro x y h
      simp [partialIter] at h
      subst y
      exact le_rfl
  | succ n ih =>
      intro x y h
      cases hx : step x with
      | none =>
          simp [partialIter, hx] at h
      | some z =>
          have htail : partialIter step n z = some y := by
            simpa [partialIter, hx] using h
          exact le_trans (ih z y htail) (Nat.le_of_lt (hstep x z hx))

theorem no_periodic_partial_gate_of_rank
    {X : Type*} (step : X → Option X) (rank : X → ℕ)
    (hstep : ∀ x y, step x = some y → rank y < rank x)
    (x : X) (n : ℕ) (hn : 0 < n) :
    partialIter step n x ≠ some x := by
  intro hcycle
  cases n with
  | zero => omega
  | succ n =>
      cases hx : step x with
      | none =>
          simp [partialIter, hx] at hcycle
      | some z =>
          have htail : partialIter step n z = some x := by
            simpa [partialIter, hx] using hcycle
          have hle : rank x ≤ rank z :=
            partialIter_rank_le step rank hstep n z x htail
          have hlt : rank z < rank x := hstep x z hx
          omega

/-- The old graph has a strictly decreasing rank, and a noncritical
inserted-limb phase is allowed to STUTTER only when a separately
bounded nonnegative phase budget decreases strictly. Under these
conditions the composite potential decreases at every actual new arrow. -/
theorem stuttering_insertion_potential_drop
    {Old New : Type*}
    (proj : New → Old)
    (oldRank : Old → ℕ)
    (stutter : New → ℕ) (budget : ℕ)
    (hbudget : ∀ z, stutter z ≤ budget)
    (edge : New → New → Prop)
    (hstep : ∀ x y, edge x y →
       oldRank (proj y) < oldRank (proj x) ∨
       (oldRank (proj y) = oldRank (proj x) ∧
        stutter y < stutter x))
    (x y : New) (hxy : edge x y) :
    (budget + 1) * oldRank (proj y) + stutter y <
      (budget + 1) * oldRank (proj x) + stutter x := by
  rcases hstep x y hxy with hstrict | ⟨heq, hlocal⟩
  · have hstepNat :
        oldRank (proj y) + 1 ≤ oldRank (proj x) := by omega
    have hmul :
        (budget + 1) * (oldRank (proj y) + 1) ≤
          (budget + 1) * oldRank (proj x) :=
        Nat.mul_le_mul_left (budget + 1) hstepNat
    have hlocalbound :
        (budget + 1) * oldRank (proj y) + stutter y <
          (budget + 1) * (oldRank (proj y) + 1) := by
      calc
        (budget + 1) * oldRank (proj y) + stutter y
            ≤ (budget + 1) * oldRank (proj y) + budget :=
              Nat.add_le_add_left (hbudget y) _
        _ < (budget + 1) * oldRank (proj y) + (budget + 1) := by
              omega
        _ = (budget + 1) * (oldRank (proj y) + 1) := by
              ring
    calc
      (budget + 1) * oldRank (proj y) + stutter y
          < (budget + 1) * (oldRank (proj y) + 1) := hlocalbound
      _ ≤ (budget + 1) * oldRank (proj x) := hmul
      _ ≤ (budget + 1) * oldRank (proj x) + stutter x :=
          Nat.le_add_right _ _
  · rw [heq]
    omega

/-- The exact finite NO-NEW-CYCLE certificate after one inserted
limb: if every source-defined new first-return arrow either makes
old-graph progress or consumes a bounded stutter phase, then
NO new actual periodic critical-cut return orbit exists. -/
theorem no_gate_cycle_under_stuttering_insertion
    {Old New : Type*}
    (proj : New → Old)
    (oldRank : Old → ℕ)
    (stutter : New → ℕ) (budget : ℕ)
    (hbudget : ∀ z, stutter z ≤ budget)
    (step : New → Option New)
    (hstep : ∀ x y, step x = some y →
       oldRank (proj y) < oldRank (proj x) ∨
       (oldRank (proj y) = oldRank (proj x) ∧
        stutter y < stutter x))
    (x : New) (n : ℕ) (hn : 0 < n) :
    partialIter step n x ≠ some x := by
  let rank : New → ℕ :=
    fun z => (budget + 1) * oldRank (proj z) + stutter z
  have hd : ∀ u v, step u = some v → rank v < rank u := by
    intro u v huv
    exact stuttering_insertion_potential_drop
      proj oldRank stutter budget hbudget
      (fun a b => step a = some b) hstep u v huv
  exact no_periodic_partial_gate_of_rank step rank hd x n hn

end LoopsKKLLimbInsertion

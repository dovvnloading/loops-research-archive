import PhaseTower27

/-!
# Future-observable quotients of deterministic marked dynamics

A quotient must preserve an observable after **every** future iterate,
not merely at time zero. We prove a precise abstract theorem:

  for a surjective forward-compatible quotient, observable
  factorization at time zero is equivalent to equality of all
  future observation streams on every quotient fiber.

We also prove a sharp obstruction for cyclic clocks: recording the
single Boolean "am I at phase zero?" across a full period distinguishes
every starting phase. Thus a coarse clock without additional memory
cannot retain this observable's complete future.

These are formal theorems about deterministic maps and finite clocks.
No claim about holomorphic dynamics, KL sheet transport, or MLC follows.
-/

namespace LoopsFormal.PhaseFuture

open LoopsFormal.Paper2
open LoopsFormal.PhaseTower

/-- Two states are indistinguishable by *all future values* of an
    observable along the actual iterates of a deterministic transition. -/
def FutureEqual {S O : Type} (step : S → S) (obs : S → O)
    (x y : S) : Prop :=
  ∀ t : Nat, obs (iterate step t x) = obs (iterate step t y)

theorem futureEqual_refl {S O : Type} (step : S → S)
    (obs : S → O) (x : S) : FutureEqual step obs x x := by
  intro t
  rfl

theorem futureEqual_symm {S O : Type} (step : S → S)
    (obs : S → O) {x y : S}
    (h : FutureEqual step obs x y) : FutureEqual step obs y x := by
  intro t
  exact (h t).symm

theorem futureEqual_trans {S O : Type} (step : S → S)
    (obs : S → O) {x y z : S}
    (hxy : FutureEqual step obs x y)
    (hyz : FutureEqual step obs y z) : FutureEqual step obs x z := by
  intro t
  exact (hxy t).trans (hyz t)

/-- Future indistinguishability survives applying the physical
    transition to both states; unlike a static label relation it is
    automatically forward invariant. -/
theorem futureEqual_next {S O : Type} (step : S → S)
    (obs : S → O) {x y : S}
    (h : FutureEqual step obs x y) :
    FutureEqual step obs (step x) (step y) := by
  intro t
  change obs (iterate step t (step x)) =
    obs (iterate step t (step y))
  rw [← iterate_add step 1 t x, ← iterate_add step 1 t y]
  exact h (1 + t)

/-- A quotient map commutes with one physical transition. -/
def Semiconjugate {S T : Type} (π : S → T)
    (step : S → S) (coarseStep : T → T) : Prop :=
  ∀ x, π (step x) = coarseStep (π x)

/-- Compatibility of one step implies compatibility at *every* time.
    This is a genuine induction in time, not finite-state sampling. -/
theorem semiconjugate_iterate {S T : Type} (π : S → T)
    (step : S → S) (coarseStep : T → T)
    (h : Semiconjugate π step coarseStep) (t : Nat) (x : S) :
    π (iterate step t x) = iterate coarseStep t (π x) := by
  induction t with
  | zero => rfl
  | succ t ih =>
      change π (step (iterate step t x)) =
        coarseStep (iterate coarseStep t (π x))
      rw [h (iterate step t x), ih]

/-- A quotient is future-sound for an observable if states that it
    identifies have indistinguishable complete future observation streams. -/
def PreservesFuture {S T O : Type} (π : S → T)
    (step : S → S) (obs : S → O) : Prop :=
  ∀ x y, π x = π y → FutureEqual step obs x y

/-- The current observable can be computed solely from quotient data. -/
def FactorsObservation {S T O : Type} (π : S → T)
    (obs : S → O) : Prop :=
  ∃ read : T → O, ∀ x, obs x = read (π x)

/-- The complete future stream can be computed by iterating the
    *coarse* transition and reading a *coarse* observable. -/
def FactorsFutureStream {S T O : Type} (π : S → T)
    (step : S → S) (coarseStep : T → T) (obs : S → O) : Prop :=
  ∃ read : T → O, ∀ x t,
    obs (iterate step t x) =
      read (iterate coarseStep t (π x))

/-- A forward-compatible quotient upgrades an instantaneous readout
    to a readout at every time. -/
theorem factorsFutureStream_iff_factorsObservation
    {S T O : Type} (π : S → T) (step : S → S)
    (coarseStep : T → T) (obs : S → O)
    (h : Semiconjugate π step coarseStep) :
    FactorsFutureStream π step coarseStep obs ↔
      FactorsObservation π obs := by
  constructor
  · rintro ⟨read, hr⟩
    refine ⟨read, ?_⟩
    intro x
    simpa [iterate] using hr x 0
  · rintro ⟨read, hr⟩
    refine ⟨read, ?_⟩
    intro x t
    calc
      obs (iterate step t x) =
          read (π (iterate step t x)) := hr _
      _ = read (iterate coarseStep t (π x)) := by
          rw [semiconjugate_iterate π step coarseStep h t x]

/-- Any complete-stream model is necessarily future-sound on fibers. -/
theorem preservesFuture_of_streamFactor
    {S T O : Type} (π : S → T) (step : S → S)
    (coarseStep : T → T) (obs : S → O)
    (h : FactorsFutureStream π step coarseStep obs) :
    PreservesFuture π step obs := by
  obtain ⟨read, hr⟩ := h
  intro x y hxy t
  calc
    obs (iterate step t x) =
      read (iterate coarseStep t (π x)) := hr x t
    _ = read (iterate coarseStep t (π y)) := by rw [hxy]
    _ = obs (iterate step t y) := (hr y t).symm

/-- A future-sound quotient must at least have a constant instantaneous
    observation on each fiber. No transition compatibility is needed. -/
theorem fiber_constant_of_preservesFuture
    {S T O : Type} (π : S → T) (step : S → S)
    (obs : S → O) (h : PreservesFuture π step obs) :
    ∀ x y, π x = π y → obs x = obs y := by
  intro x y hxy
  simpa [iterate] using h x y hxy 0

/-- Surjectivity allows a coarse readout to be constructed from a
    fiber-constant observable by selecting one representative per fiber.
    The conclusion does not require a decidable or finite state type. -/
theorem factorsObservation_of_fiber_constant
    {S T O : Type} (π : S → T) (obs : S → O)
    (hsurj : Function.Surjective π)
    (h : ∀ x y, π x = π y → obs x = obs y) :
    FactorsObservation π obs := by
  classical
  let pick : T → S := fun y => Classical.choose (hsurj y)
  have hpick : ∀ y, π (pick y) = y :=
    fun y => Classical.choose_spec (hsurj y)
  refine ⟨fun y => obs (pick y), ?_⟩
  intro x
  exact h x (pick (π x)) (hpick (π x)).symm

/-- Fundamental abstract quotient theorem: for surjective
    forward-compatible quotients, future soundness, instantaneous
    factorization, and factorization of the full future stream are
    *equivalent*. It does not say the quotient retains the original
    state, only the named observable. -/
theorem futureSound_iff_observationFactor
    {S T O : Type} (π : S → T) (step : S → S)
    (coarseStep : T → T) (obs : S → O)
    (hsurj : Function.Surjective π)
    (hstep : Semiconjugate π step coarseStep) :
    PreservesFuture π step obs ↔ FactorsObservation π obs := by
  constructor
  · intro h
    exact factorsObservation_of_fiber_constant π obs hsurj
      (fiber_constant_of_preservesFuture π step obs h)
  · intro h
    exact preservesFuture_of_streamFactor π step coarseStep obs
      ((factorsFutureStream_iff_factorsObservation
        π step coarseStep obs hstep).mpr h)

/-- A quotient that preserves an observable whose full future stream
    separates all states cannot identify *any* two distinct states. -/
theorem injective_of_future_separating
    {S T O : Type} (π : S → T)
    (step : S → S) (obs : S → O)
    (hsep : ∀ x y, FutureEqual step obs x y → x = y)
    (hpres : PreservesFuture π step obs) :
    Function.Injective π := by
  intro x y hxy
  exact hsep x y (hpres x y hxy)

/-- The canonical successor on any positive finite clock. -/
def clockNext (p : Nat) (hp : 0 < p) (i : Phase p) : Phase p :=
  ⟨(i.val + 1) % p, Nat.mod_lt _ hp⟩

/-- Successor is a permutation even when the period is one. -/
theorem clockNext_injective (p : Nat) (hp : 0 < p) :
    Function.Injective (clockNext p hp) := by
  intro i j heq
  apply Fin.ext
  have hv := congrArg Fin.val heq
  dsimp [clockNext] at hv
  have hi := i.isLt
  have hj := j.isLt
  omega

/-- Every future iterate adds its time to the phase, modulo the period. -/
theorem clock_iterate_formula (p : Nat) (hp : 0 < p)
    (t : Nat) (i : Phase p) :
    (iterate (clockNext p hp) t i).val = (i.val + t) % p := by
  induction t with
  | zero =>
      change i.val = (i.val + 0) % p
      simp [Nat.mod_eq_of_lt i.isLt]
  | succ t ih =>
      change ((iterate (clockNext p hp) t i).val + 1) % p =
        (i.val + (t + 1)) % p
      rw [ih, Nat.mod_add_mod]
      simp only [Nat.add_assoc]

/-- Division of periods makes phase projection genuinely compatible
    with the deterministic successor, not just a set-theoretic map. -/
theorem clock_project_semiconjugate
    (p q : Nat) (hp : 0 < p) (hq : 0 < q)
    (hdiv : p ∣ q) :
    Semiconjugate (project p q hp)
      (clockNext q hq) (clockNext p hp) := by
  intro i
  apply Fin.ext
  change ((i.val + 1) % q) % p = ((i.val % p + 1) % p)
  rw [mod_mod_of_divisor (i.val + 1) p q hdiv]
  rw [Nat.mod_add_mod]

/-- Exact phase-clock theorem: a static fiber-constant mark is already
    sufficient for the entire future *because* the quotient commutes
    with successor. This fails for arbitrary noncompatible quotients. -/
theorem clock_future_iff_static_factor
    {O : Type} (p q : Nat) (hp : 0 < p) (hq : 0 < q)
    (hdiv : p ∣ q) (obs : Phase q → O) :
    PreservesFuture (project p q hp) (clockNext q hq) obs ↔
      FactorsThrough p q hp obs := by
  exact futureSound_iff_observationFactor
    (project p q hp) (clockNext q hq) (clockNext p hp) obs
    (project_surjective p q hp (Nat.le_of_dvd hq hdiv))
    (clock_project_semiconjugate p q hp hq hdiv)

/-- The stronger stream formulation has the same exact criterion. -/
theorem clock_future_stream_iff_static_factor
    {O : Type} (p q : Nat) (hp : 0 < p) (hq : 0 < q)
    (hdiv : p ∣ q) (obs : Phase q → O) :
    FactorsFutureStream (project p q hp)
      (clockNext q hq) (clockNext p hp) obs ↔
      FactorsThrough p q hp obs := by
  exact factorsFutureStream_iff_factorsObservation
    (project p q hp) (clockNext q hq) (clockNext p hp) obs
    (clock_project_semiconjugate p q hp hq hdiv)

/-- Iterating an injective transition remains injective for every
    number of steps. -/
theorem iterate_injective {S : Type}
    (step : S → S) (h : Function.Injective step)
    (t : Nat) : Function.Injective (iterate step t) := by
  induction t with
  | zero =>
      intro x y heq
      exact heq
  | succ t ih =>
      intro x y heq
      exact ih (h heq)

/-- A single bit reporting whether the clock is currently in phase zero. -/
def zeroSensor (p : Nat) (i : Phase p) : Bool :=
  decide (i.val = 0)

theorem zeroSensor_true_iff (p : Nat) (i : Phase p) :
    zeroSensor p i = true ↔ i.val = 0 := by
  simp [zeroSensor]

/-- From any starting phase, phase zero is reached at some time
    strictly before the end of the cycle. -/
theorem clock_reaches_zero (p : Nat) (hp : 0 < p)
    (i : Phase p) :
    ∃ t : Nat, t < p ∧
      zeroSensor p (iterate (clockNext p hp) t i) = true := by
  let t := (p - i.val) % p
  refine ⟨t, Nat.mod_lt _ hp, ?_⟩
  have hsum : (i.val + t) % p = 0 := by
    by_cases hz : i.val = 0
    · dsimp [t]
      simp [hz]
    · have hlt : p - i.val < p := by
        have hi := i.isLt
        omega
      have hadd : i.val + (p - i.val) = p := by
        have hi := i.isLt
        omega
      dsimp [t]
      rw [Nat.mod_eq_of_lt hlt, hadd]
      simp
  apply (zeroSensor_true_iff p _).mpr
  rw [clock_iterate_formula]
  exact hsum

/-- MAIN OBSERVABILITY RESULT. A Boolean sensor plus its first p
    readings separates all p clock phases, for *every* positive p.
    The proof picks a time when the first orbit reaches phase zero,
    then uses injectivity of the time-t transition. -/
theorem zeroSensor_bounded_future_separates (p : Nat) (hp : 0 < p)
    (i j : Phase p)
    (hobs : ∀ t : Nat, t < p →
      zeroSensor p (iterate (clockNext p hp) t i) =
        zeroSensor p (iterate (clockNext p hp) t j)) :
    i = j := by
  obtain ⟨t, ht, hzero⟩ := clock_reaches_zero p hp i
  have hzero' :
      zeroSensor p (iterate (clockNext p hp) t j) = true := by
    rw [← hobs t ht]
    exact hzero
  have heq : iterate (clockNext p hp) t i =
      iterate (clockNext p hp) t j := by
    apply Fin.ext
    have hi := (zeroSensor_true_iff p _).mp hzero
    have hj := (zeroSensor_true_iff p _).mp hzero'
    omega
  exact iterate_injective (clockNext p hp)
    (clockNext_injective p hp) t heq

/-- Arbitrarily long observation streams distinguish states as well;
    the stronger bounded theorem above already needs fewer readings. -/
theorem zeroSensor_future_separates (p : Nat) (hp : 0 < p)
    (i j : Phase p)
    (hobs : FutureEqual (clockNext p hp) (zeroSensor p) i j) :
    i = j := by
  exact zeroSensor_bounded_future_separates p hp i j
    (fun t _ => hobs t)

/-- All p time samples packaged into a single finite observation trace. -/
def zeroTrace (p : Nat) (hp : 0 < p) (i : Phase p) :
    Phase p → Bool :=
  fun t => zeroSensor p (iterate (clockNext p hp) t.val i)

/-- A one-bit observation trace of length p injectively encodes all
    p states. This is an exact theorem, not an information estimate. -/
theorem zeroTrace_injective (p : Nat) (hp : 0 < p) :
    Function.Injective (zeroTrace p hp) := by
  intro i j h
  apply zeroSensor_bounded_future_separates p hp i j
  intro t ht
  have hv := congrArg (fun f : Phase p → Bool =>
    f ⟨t, ht⟩) h
  exact hv

/-- Any quotient preserving every future reading of the Boolean
    zero-phase sensor must be injective. In particular, no strictly
    coarser phase clock can be future-sound for this sensor. -/
theorem zeroSensor_future_sound_implies_injective
    {T : Type} (p : Nat) (hp : 0 < p) (π : Phase p → T)
    (h : PreservesFuture π (clockNext p hp) (zeroSensor p)) :
    Function.Injective π := by
  exact injective_of_future_separating π (clockNext p hp)
    (zeroSensor p) (zeroSensor_future_separates p hp) h

theorem strict_phase_quotient_loses_zero_future
    (p q : Nat) (hp : 0 < p) (hq : 0 < q)
    (hlt : p < q) :
    ¬ PreservesFuture (project p q hp)
        (clockNext q hq) (zeroSensor q) := by
  intro h
  obtain ⟨i, j, hne, heq⟩ :=
    project_has_collision p q hp hlt
  exact hne ((zeroSensor_future_sound_implies_injective
    q hq (project p q hp) h) heq)

#print axioms futureSound_iff_observationFactor
#print axioms clock_future_iff_static_factor
#print axioms zeroSensor_bounded_future_separates
#print axioms zeroTrace_injective
#print axioms strict_phase_quotient_loses_zero_future

end LoopsFormal.PhaseFuture

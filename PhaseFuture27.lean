import PhaseFuture

/-!
# Sharp finite memory costs of future-faithful 27/9/3 phase descriptions

We keep the coarse physical clock and add exactly the missing digits:
  Fin 27 ≃ Fin 9 × Fin 3  (one ternary memory state),
  Fin 27 ≃ Fin 3 × Fin 9  (two ternary memory digits).

For an arbitrary memory alphabet M, if a code
  i ↦ (coarsePhase(i), memory(i))
retains the future of the single Boolean zero-phase sensor, then
memory must distinguish *all* points in each coarse-phase fiber:
at least three distinct memories over one 9-phase fiber and at
least nine distinct memories over one 3-phase fiber.

Both lower bounds are realized by the explicit reversible addresses.
This is a finite symbolic-clock result, not a claim about the infinite
sheet/coset fiber or analytic returns in complex dynamics.
-/

namespace LoopsFormal.PhaseFuture

open LoopsFormal.PhaseTower
open LoopsFormal.Paper2

/-- Memory of the phase's position within the three outer phases. -/
def outerMemory9 (i : Phase 27) : Phase 9 :=
  ⟨i.val / 3, by have h := i.isLt; omega⟩

/-- Lossless address using the 3-phase clock and nine auxiliary states. -/
def outerAddress (i : Phase 27) : Phase 3 × Phase 9 :=
  (project 3 27 (by decide) i, outerMemory9 i)

/-- Recover the complete 27-phase clock from outer phase and memory. -/
def outerDecode (a : Phase 3 × Phase 9) : Phase 27 :=
  ⟨a.1.val + 3 * a.2.val, by
    have h0 := a.1.isLt
    have h1 := a.2.isLt
    omega⟩

theorem outerDecode_encode : ∀ i : Phase 27,
    outerDecode (outerAddress i) = i := by
  decide +kernel

theorem outerEncode_decode : ∀ a : Phase 3 × Phase 9,
    outerAddress (outerDecode a) = a := by
  intro a
  cases a with
  | mk x y =>
      revert x y
      decide +kernel

theorem outerAddress_injective : Function.Injective outerAddress := by
  intro i j hij
  calc
    i = outerDecode (outerAddress i) := (outerDecode_encode i).symm
    _ = outerDecode (outerAddress j) := congrArg outerDecode hij
    _ = j := outerDecode_encode j

/-- Memory inside each 9-phase residue has three possible positions. -/
def middleMemory3 (i : Phase 27) : Phase 3 :=
  ⟨i.val / 9, by have h := i.isLt; omega⟩

/-- Lossless address using the 9-phase clock and three auxiliary states. -/
def middleAddress (i : Phase 27) : Phase 9 × Phase 3 :=
  (project 9 27 (by decide) i, middleMemory3 i)

def middleDecode (a : Phase 9 × Phase 3) : Phase 27 :=
  ⟨a.1.val + 9 * a.2.val, by
    have h0 := a.1.isLt
    have h1 := a.2.isLt
    omega⟩

theorem middleDecode_encode : ∀ i : Phase 27,
    middleDecode (middleAddress i) = i := by
  decide +kernel

theorem middleEncode_decode : ∀ a : Phase 9 × Phase 3,
    middleAddress (middleDecode a) = a := by
  intro a
  cases a with
  | mk x y =>
      revert x y
      decide +kernel

theorem middleAddress_injective : Function.Injective middleAddress := by
  intro i j hij
  calc
    i = middleDecode (middleAddress i) := (middleDecode_encode i).symm
    _ = middleDecode (middleAddress j) := congrArg middleDecode hij
    _ = j := middleDecode_encode j

/-- Compatibility with the previously verified three-digit carry code:
    outer memory is exactly the pair of higher ternary digits b+3c. -/
def remainingDigits9 (a : Address27) : Phase 9 :=
  ⟨a.2.1.val + 3 * a.2.2.val, by
    have hb := a.2.1.isLt
    have hc := a.2.2.isLt
    omega⟩

theorem outerMemory_matches_digits : ∀ i : Phase 27,
    outerMemory9 i = remainingDigits9 (encode27 i) := by
  decide +kernel

theorem middleMemory_matches_digits : ∀ i : Phase 27,
    middleMemory3 i = (encode27 i).2.2 := by
  decide +kernel

/-- Every nine-phase position appears over fixed outer phase zero. -/
def outerZeroFiber (a : Phase 9) : Phase 27 :=
  ⟨3 * a.val, by have h := a.isLt; omega⟩

theorem outerZeroFiber_projects_zero (a : Phase 9) :
    project 3 27 (by decide) (outerZeroFiber a) = (0 : Phase 3) := by
  apply Fin.ext
  simp [project, outerZeroFiber]

theorem outerZeroFiber_injective : Function.Injective outerZeroFiber := by
  intro a b hab
  apply Fin.ext
  have h := congrArg Fin.val hab
  dsimp [outerZeroFiber] at h
  omega

/-- Every three-phase position appears over fixed middle phase zero. -/
def middleZeroFiber (a : Phase 3) : Phase 27 :=
  ⟨9 * a.val, by have h := a.isLt; omega⟩

theorem middleZeroFiber_projects_zero (a : Phase 3) :
    project 9 27 (by decide) (middleZeroFiber a) = (0 : Phase 9) := by
  apply Fin.ext
  simp [project, middleZeroFiber]

theorem middleZeroFiber_injective : Function.Injective middleZeroFiber := by
  intro a b hab
  apply Fin.ext
  have h := congrArg Fin.val hab
  dsimp [middleZeroFiber] at h
  omega

/-- If the outer phase and a memory code jointly separate the 27
    states, the memory alone must separate all NINE elements over one
    fixed outer phase. This lower bound is valid for *any* type M. -/
theorem outer_memory_requires_nine_distinct
    {M : Type} (memory : Phase 27 → M)
    (hcode : Function.Injective (fun i : Phase 27 =>
      (project 3 27 (by decide) i, memory i))) :
    Function.Injective (fun a : Phase 9 => memory (outerZeroFiber a)) := by
  intro a b hmem
  apply outerZeroFiber_injective
  apply hcode
  apply Prod.ext
  · rw [outerZeroFiber_projects_zero a, outerZeroFiber_projects_zero b]
  · exact hmem

/-- The analogous lower bound over one middle-phase fiber is THREE
    distinct memory values, regardless of how they are represented. -/
theorem middle_memory_requires_three_distinct
    {M : Type} (memory : Phase 27 → M)
    (hcode : Function.Injective (fun i : Phase 27 =>
      (project 9 27 (by decide) i, memory i))) :
    Function.Injective (fun a : Phase 3 => memory (middleZeroFiber a)) := by
  intro a b hmem
  apply middleZeroFiber_injective
  apply hcode
  apply Prod.ext
  · rw [middleZeroFiber_projects_zero a, middleZeroFiber_projects_zero b]
  · exact hmem

/-- An arbitrary augmented 3-phase state that preserves the complete
    future of the single zero-phase Boolean sensor already needs nine
    distinct memory states in a single coarse fiber. -/
theorem outer_future_memory_lower_bound
    {M : Type} (memory : Phase 27 → M)
    (hfuture : PreservesFuture
      (fun i : Phase 27 => (project 3 27 (by decide) i, memory i))
      next27 (zeroSensor 27)) :
    Function.Injective (fun a : Phase 9 => memory (outerZeroFiber a)) := by
  apply outer_memory_requires_nine_distinct memory
  apply zeroSensor_future_sound_implies_injective 27 (by decide)
  exact hfuture

/-- The same future-faithfulness requirement for a 9-phase state
    forces three distinct memory values in each three-element fiber. -/
theorem middle_future_memory_lower_bound
    {M : Type} (memory : Phase 27 → M)
    (hfuture : PreservesFuture
      (fun i : Phase 27 => (project 9 27 (by decide) i, memory i))
      next27 (zeroSensor 27)) :
    Function.Injective (fun a : Phase 3 => memory (middleZeroFiber a)) := by
  apply middle_memory_requires_three_distinct memory
  apply zeroSensor_future_sound_implies_injective 27 (by decide)
  exact hfuture

/-- The explicit three-phase address with nine states meets the lower
    bound and is future-sound for *every* possible observable. -/
theorem outerAddress_future_sound {O : Type} (obs : Phase 27 → O) :
    PreservesFuture outerAddress next27 obs := by
  intro i j hij
  have h : i = j := outerAddress_injective hij
  subst j
  exact futureEqual_refl next27 obs i

theorem middleAddress_future_sound {O : Type} (obs : Phase 27 → O) :
    PreservesFuture middleAddress next27 obs := by
  intro i j hij
  have h : i = j := middleAddress_injective hij
  subst j
  exact futureEqual_refl next27 obs i

/-- Transport the 27-phase successor as a *genuine* deterministic
    transition on the augmented 3-phase address. -/
def outerAddressStep (a : Phase 3 × Phase 9) : Phase 3 × Phase 9 :=
  outerAddress (next27 (outerDecode a))

theorem outerAddress_step_commutes :
    Semiconjugate outerAddress next27 outerAddressStep := by
  intro i
  simp [outerAddressStep, outerDecode_encode]

/-- The code also admits a coarse readout, so not only the underlying
    states but the entire observation stream can be reconstructed. -/
theorem outerAddress_future_stream {O : Type} (obs : Phase 27 → O) :
    FactorsFutureStream outerAddress next27 outerAddressStep obs := by
  apply (factorsFutureStream_iff_factorsObservation
    outerAddress next27 outerAddressStep obs outerAddress_step_commutes).mpr
  refine ⟨fun a => obs (outerDecode a), ?_⟩
  intro i
  rw [outerDecode_encode]

def middleAddressStep (a : Phase 9 × Phase 3) : Phase 9 × Phase 3 :=
  middleAddress (next27 (middleDecode a))

theorem middleAddress_step_commutes :
    Semiconjugate middleAddress next27 middleAddressStep := by
  intro i
  simp [middleAddressStep, middleDecode_encode]

theorem middleAddress_future_stream {O : Type} (obs : Phase 27 → O) :
    FactorsFutureStream middleAddress next27 middleAddressStep obs := by
  apply (factorsFutureStream_iff_factorsObservation
    middleAddress next27 middleAddressStep obs middleAddress_step_commutes).mpr
  refine ⟨fun a => obs (middleDecode a), ?_⟩
  intro i
  rw [middleDecode_encode]

/-- A single snapshot fails to expose one kind of future aliasing:
    phases 1 and 10 have the same modulo-3 phase and the same current
    zero sensor output, yet their readings differ 26 steps later. -/
theorem same_snapshot_but_different_future :
    project 3 27 (by decide) (1 : Phase 27) =
      project 3 27 (by decide) (10 : Phase 27) ∧
    zeroSensor 27 (1 : Phase 27) = zeroSensor 27 (10 : Phase 27) ∧
    zeroSensor 27 (iterate next27 26 (1 : Phase 27)) ≠
      zeroSensor 27 (iterate next27 26 (10 : Phase 27)) := by
  decide +kernel

/-- Without any memory, the strict 27-to-3 phase quotient cannot
    preserve the future of the zero sensor; adding the full nine-state
    memory is sufficient and (as an injection bound) necessary. -/
theorem no_memory_3_phase_is_not_future_sound :
    ¬ PreservesFuture (project 3 27 (by decide)) next27 (zeroSensor 27) := by
  exact strict_phase_quotient_loses_zero_future 3 27
    (by decide) (by decide) (by decide)

theorem no_memory_9_phase_is_not_future_sound :
    ¬ PreservesFuture (project 9 27 (by decide)) next27 (zeroSensor 27) := by
  exact strict_phase_quotient_loses_zero_future 9 27
    (by decide) (by decide) (by decide)

#print axioms outer_memory_requires_nine_distinct
#print axioms middle_memory_requires_three_distinct
#print axioms outer_future_memory_lower_bound
#print axioms outerAddress_future_stream
#print axioms middleAddress_future_stream
#print axioms same_snapshot_but_different_future

end LoopsFormal.PhaseFuture

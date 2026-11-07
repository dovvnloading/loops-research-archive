import PhaseFuture

/-!
# Arbitrary finite-clock refinements: lossless addresses and minimal memory

For all positive integers p and k, the physical (p*k)-phase clock is
reversibly encoded as a coarse p-phase and exactly k memory states.

A future-faithful augmentation (coarse phase, arbitrary memory M) must be
injective on the k distinct points over coarse phase zero, even if the
only demanded observation is the future of the Boolean zero-phase sensor.
The explicit mixed-radix address attains this bound for *every* observable,
with a deterministic update whose first component is the true coarse clock.

These theorems concern symbolic clocks, not holomorphic renormalization,
physical access/sheet atlases, KL width estimates, or Mandelbrot local
connectivity.
-/

namespace LoopsFormal.PhaseMemory

open LoopsFormal.PhaseTower
open LoopsFormal.PhaseFuture

/-- Cancellation without importing mathlib: multiplication by a strictly
positive natural number is injective. -/
private theorem mul_left_cancel_pos (p : Nat) (hp : 0 < p) {a b : Nat}
    (h : p * a = p * b) : a = b := by
  by_cases hlt : a < b
  · have hstrict := Nat.mul_lt_mul_of_pos_left hlt hp
    omega
  · by_cases hgt : b < a
    · have hstrict := Nat.mul_lt_mul_of_pos_left hgt hp
      omega
    · omega

/-- The quotient digit, specifying which of k copies of the coarse
p-phase clock the physical phase occupies. -/
def memoryDigit (p k : Nat) (hp : 0 < p)
    (i : Phase (p * k)) : Phase k :=
  ⟨i.val / p, by
    have hi := i.isLt
    have hdiv := Nat.mod_add_div i.val p
    have hbound : p * (i.val / p) ≤ i.val := by omega
    by_contra hnot
    have hk : k ≤ i.val / p := by omega
    have hprod : p * k ≤ p * (i.val / p) :=
      Nat.mul_le_mul_left p hk
    omega⟩

/-- The reversible address of a physical phase. The first coordinate
is exactly the pre-existing modulo-p projection. -/
def address (p k : Nat) (hp : 0 < p)
    (i : Phase (p * k)) : Phase p × Phase k :=
  (project p (p * k) hp i, memoryDigit p k hp i)

/-- Recover the physical phase from the coarse phase and memory digit. -/
def decode (p k : Nat) (hp : 0 < p)
    (a : Phase p × Phase k) : Phase (p * k) :=
  ⟨a.1.val + p * a.2.val, by
    have ha := a.1.isLt
    have hb : a.2.val + 1 ≤ k := by have h := a.2.isLt; omega
    have hprod : p * (a.2.val + 1) ≤ p * k :=
      Nat.mul_le_mul_left p hb
    have hlinear : p * a.2.val + p ≤ p * k := by
      simpa [Nat.mul_add] using hprod
    omega⟩

/-- Encoding and decoding are inverse on every physical phase, with
no finite enumeration and no restriction to 3/9/27. -/
theorem decode_address (p k : Nat) (hp : 0 < p)
    (i : Phase (p * k)) :
    decode p k hp (address p k hp i) = i := by
  apply Fin.ext
  change i.val % p + p * (i.val / p) = i.val
  exact Nat.mod_add_div i.val p

/-- Every possible coarse phase / memory pair also round-trips. -/
theorem address_decode (p k : Nat) (hp : 0 < p)
    (a : Phase p × Phase k) :
    address p k hp (decode p k hp a) = a := by
  cases a with
  | mk a b =>
    have hmod : (a.val + p * b.val) % p = a.val := by
      simp [Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt a.isLt]
    apply Prod.ext
    · apply Fin.ext
      exact hmod
    · apply Fin.ext
      change (a.val + p * b.val) / p = b.val
      have hdiv := Nat.mod_add_div (a.val + p * b.val) p
      rw [hmod] at hdiv
      apply mul_left_cancel_pos p hp
      omega

theorem address_injective (p k : Nat) (hp : 0 < p) :
    Function.Injective (address p k hp) := by
  intro i j hij
  calc
    i = decode p k hp (address p k hp i) :=
      (decode_address p k hp i).symm
    _ = decode p k hp (address p k hp j) := congrArg _ hij
    _ = j := decode_address p k hp j

theorem address_surjective (p k : Nat) (hp : 0 < p) :
    Function.Surjective (address p k hp) := by
  intro a
  exact ⟨decode p k hp a, address_decode p k hp a⟩

/-- The k fine phases over coarse phase zero, represented by multiples
of p. This explicitly exhibits the information the quotient discards. -/
def zeroFiber (p k : Nat) (hp : 0 < p)
    (a : Phase k) : Phase (p * k) :=
  ⟨p * a.val, Nat.mul_lt_mul_of_pos_left a.isLt hp⟩

theorem zeroFiber_projects_zero (p k : Nat) (hp : 0 < p)
    (a : Phase k) :
    project p (p * k) hp (zeroFiber p k hp a) = (0 : Phase p) := by
  apply Fin.ext
  simp [project, zeroFiber, Nat.mul_mod]

theorem zeroFiber_injective (p k : Nat) (hp : 0 < p) :
    Function.Injective (zeroFiber p k hp) := by
  intro a b hab
  apply Fin.ext
  apply mul_left_cancel_pos p hp
  exact congrArg Fin.val hab

/-- Regardless of the memory alphabet, any *injective* augmented
coarse code needs k distinct memory values within one projection fiber. -/
theorem memory_injective_on_zeroFiber
    {M : Type} (p k : Nat) (hp : 0 < p)
    (mem : Phase (p * k) → M)
    (hcode : Function.Injective (fun i : Phase (p * k) =>
      (project p (p * k) hp i, mem i))) :
    Function.Injective (fun a : Phase k => mem (zeroFiber p k hp a)) := by
  intro a b hmem
  apply zeroFiber_injective p k hp
  apply hcode
  apply Prod.ext
  · rw [zeroFiber_projects_zero p k hp a,
        zeroFiber_projects_zero p k hp b]
  · exact hmem

/-- Bounded future readings of just ONE Boolean zero-phase sensor
already force k pairwise distinct memory values in each zero fiber.
The transition on the augmentation is not assumed in this obstruction. -/
theorem zeroSensor_future_requires_memory
    {M : Type} (p k : Nat) (hp : 0 < p) (hk : 0 < k)
    (mem : Phase (p * k) → M)
    (hfuture : PreservesFuture
      (fun i : Phase (p * k) => (project p (p * k) hp i, mem i))
      (clockNext (p * k) (Nat.mul_pos hp hk))
      (zeroSensor (p * k))) :
    Function.Injective (fun a : Phase k => mem (zeroFiber p k hp a)) := by
  apply memory_injective_on_zeroFiber p k hp mem
  exact zeroSensor_future_sound_implies_injective
    (p * k) (Nat.mul_pos hp hk) _ hfuture

/-- The deterministic transition on the mixed-radix address is
induced by the actual physical clock, not an independently chosen
memory automaton. -/
def addressNext (p k : Nat) (hp : 0 < p) (hk : 0 < k)
    (a : Phase p × Phase k) : Phase p × Phase k :=
  address p k hp
    (clockNext (p * k) (Nat.mul_pos hp hk) (decode p k hp a))

theorem address_step_semiconjugate
    (p k : Nat) (hp : 0 < p) (hk : 0 < k) :
    Semiconjugate (address p k hp)
      (clockNext (p * k) (Nat.mul_pos hp hk))
      (addressNext p k hp hk) := by
  intro i
  simp [addressNext, decode_address]

/-- The first coordinate really advances by one on the coarse clock,
including carries and wraparound. -/
theorem addressNext_coarse
    (p k : Nat) (hp : 0 < p) (hk : 0 < k)
    (a : Phase p × Phase k) :
    (addressNext p k hp hk a).1 = clockNext p hp a.1 := by
  have hsem := clock_project_semiconjugate
    p (p * k) hp (Nat.mul_pos hp hk) (show p ∣ p * k from ⟨k, rfl⟩)
  have hstep := hsem (decode p k hp a)
  have hfirst := congrArg Prod.fst (address_decode p k hp a)
  change project p (p * k) hp (decode p k hp a) = a.1 at hfirst
  change project p (p * k) hp
    (clockNext (p * k) (Nat.mul_pos hp hk) (decode p k hp a)) =
      clockNext p hp a.1
  rw [hstep, hfirst]

/-- The sharp witness: k memory states suffice, for the COMPLETE
future stream of every observable and every time, at every p and k. -/
theorem address_factors_all_future_streams
    (p k : Nat) (hp : 0 < p) (hk : 0 < k)
    {O : Type} (obs : Phase (p * k) → O) :
    FactorsFutureStream (address p k hp)
      (clockNext (p * k) (Nat.mul_pos hp hk))
      (addressNext p k hp hk) obs := by
  apply (factorsFutureStream_iff_factorsObservation
    (address p k hp) (clockNext (p * k) (Nat.mul_pos hp hk))
    (addressNext p k hp hk) obs
    (address_step_semiconjugate p k hp hk)).mpr
  refine ⟨fun a => obs (decode p k hp a), ?_⟩
  intro i
  change obs i = obs (decode p k hp (address p k hp i))
  rw [decode_address]

#print axioms decode_address
#print axioms address_decode
#print axioms zeroSensor_future_requires_memory
#print axioms addressNext_coarse
#print axioms address_factors_all_future_streams

end LoopsFormal.PhaseMemory

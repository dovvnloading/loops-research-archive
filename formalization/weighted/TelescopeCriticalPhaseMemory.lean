import TelescopeCriticalPhaseWitness
import CriticalPhaseWords

/-!
# Unbounded critical-crossing phase memory at fixed return degree

Every actual one-critical quadratic return admits, for every N, a common
closed target path with 2^N explicitly distinct complete closed lifts based
at the same regular physical point. Degree two, a closed target itinerary,
and both endpoint phase marks therefore give no uniform finite bound on
the number of complete source routes when critical encounters are allowed.
-/

namespace LoopsTelescopeCriticalPhaseMemory

open Set Function
open QuadraticEscape LoopsSaturatedTelescope
open LoopsCriticalPhaseWords LoopsTelescopeCriticalPhaseWitness

noncomputable section

/-- Arbitrary finite Boolean phase words are realized by genuine closed
source paths in each actual one-critical return. All words of a given
length have one common complete target path and the same regular source
basepoint. The distinctness is of complete timed physical paths. -/
theorem quadratic_return_unbounded_closed_phase_memory
    (c : ℂ) (a b : ℕ) (A B D : Set ℂ) (hc : c ∈ D) (hA : IsOpen A)
    (hB : B = connectedComponentIn ((fun w : ℂ => w^2+c) ⁻¹' D) 0)
    (hponto : orbit c a '' A = B)
    (hpinj : InjOn (orbit c a) A) (hrinj : InjOn (orbit c b) D) :
    ∃ z ∈ A, orbit c (a+1+b) z ≠ orbit c b c ∧
      ∀ n : ℕ, ∃ γ : Path (orbit c (a+1+b) z) (orbit c (a+1+b) z),
        ∃ Γ : (Fin n → Bool) → Path z z,
          Injective Γ ∧ (∀ s, range (Γ s) ⊆ A) ∧
            ∀ s, (Γ s).map (quadratic_orbit_continuous c (a+1+b)) = γ := by
  obtain ⟨γ₀, Γ₀, Γ₁, hmem, hproj, _, hstart, hend, hne,
      _, hclosed, _, hregular⟩ :=
    quadratic_return_two_crossing_same_endpoints c a b A B D
      hc hA hB hponto hpinj hrinj
  let z := Γ₀ 0
  let p : Path z z :=
    { toContinuousMap := Γ₀
      source' := rfl
      target' := hclosed.symm }
  let q : Path z z :=
    { toContinuousMap := Γ₁
      source' := hstart
      target' := hend.trans hclosed.symm }
  have hpq : p ≠ q := by
    intro h
    apply hne
    ext t
    exact (congrArg (fun r : Path z z => r t) h).symm
  have hmap : p.map (quadratic_orbit_continuous c (a+1+b)) =
      q.map (quadratic_orbit_continuous c (a+1+b)) := by
    ext t
    exact (hproj t).1.trans (hproj t).2.symm
  have hp : range p ⊆ A := by
    rintro w ⟨t, rfl⟩
    exact (hmem t).1
  have hq : range q ⊆ A := by
    rintro w ⟨t, rfl⟩
    exact (hmem t).2
  have hz : z ∈ A := (hmem 0).1
  have hzregular : orbit c (a+1+b) z ≠ orbit c b c := by
    intro h
    exact hregular ((hproj 0).1.symm.trans h)
  refine ⟨z, hz, hzregular, ?_⟩
  intro n
  exact two_loops_independent_words p q hpq (orbit c (a+1+b))
    (quadratic_orbit_continuous c (a+1+b)) hmap A hz hp hq n

end

end LoopsTelescopeCriticalPhaseMemory

import QuadraticComponentFiberDegree

/-!
# Reflection data preserved by stable actual pullback components

Exact component preservation at every residual depth preserves each
reflection flag and hence the entire intrinsic reflection rank. The
argument uses the actual even quadratic iterate and allows critical
target values. It requires no regular anchor or target openness.
-/

namespace LoopsQuadraticStableReflection

open Set Function Classical
open LoopsQuadraticCylinderRamification
open LoopsQuadraticComponentFiberDegree
open LoopsStationarySeparatorTransport

noncomputable section

/-- For a positive quadratic iterate, invariance of its actual component
under reflection is equivalent to containing the reflected anchor. -/
theorem quadratic_component_reflection_iff_neg_mem
    (c : ℂ) (n : ℕ) (V : Set ℂ) (x : ℂ)
    (hn : 0 < n) (hx : (quad c)^[n] x ∈ V) :
    (∀ z ∈ connectedComponentIn ((quad c)^[n] ⁻¹' V) x,
      -z ∈ connectedComponentIn ((quad c)^[n] ⁻¹' V) x) ↔
    -x ∈ connectedComponentIn ((quad c)^[n] ⁻¹' V) x := by
  constructor
  · intro hs
    exact hs x (mem_connectedComponentIn hx)
  · intro hnx
    exact even_component_reflection_of_pair ((quad c)^[n]) V
      (quadratic_positive_iterate_even c n hn) x x
      (mem_connectedComponentIn hx) hnx

/-- Exact preservation of an old component inside an enlargement
preserves its reflection flag. The reflected anchor remains over the
old target because every positive quadratic iterate is even. -/
theorem quadratic_enlargement_reflection_iff_of_no_merger
    (c : ℂ) (n : ℕ) (U V : Set ℂ) (hUV : U ⊆ V)
    (x : ℂ) (hn : 0 < n) (hx : (quad c)^[n] x ∈ U)
    (hno : connectedComponentIn ((quad c)^[n] ⁻¹' V) x ∩
        ((quad c)^[n] ⁻¹' U) =
      connectedComponentIn ((quad c)^[n] ⁻¹' U) x) :
    (∀ z ∈ connectedComponentIn ((quad c)^[n] ⁻¹' U) x,
      -z ∈ connectedComponentIn ((quad c)^[n] ⁻¹' U) x) ↔
    (∀ z ∈ connectedComponentIn ((quad c)^[n] ⁻¹' V) x,
      -z ∈ connectedComponentIn ((quad c)^[n] ⁻¹' V) x) := by
  rw [quadratic_component_reflection_iff_neg_mem c n U x hn hx,
    quadratic_component_reflection_iff_neg_mem c n V x hn (hUV hx)]
  constructor
  · exact connectedComponentIn_mono x (preimage_mono hUV)
  · intro hnx
    have hnegU : -x ∈ (quad c)^[n] ⁻¹' U := by
      change (quad c)^[n] (-x) ∈ U
      rw [quadratic_positive_iterate_even c n hn]
      exact hx
    have hm : -x ∈ connectedComponentIn ((quad c)^[n] ⁻¹' V) x ∩
        ((quad c)^[n] ⁻¹' U) := ⟨hnx, hnegU⟩
    rw [hno] at hm
    exact hm

/-- Simultaneous preservation of actual pullback components through
a finite horizon preserves every corresponding reflection rank.
No regular-target hypothesis is needed: each summand is preserved
at its own residual depth before the ranks are assembled. -/
theorem quadratic_stable_reflection_rank
    (c : ℂ) (U V : Set ℂ) (hUV : U ⊆ V) (H : ℕ)
    (hno : ∀ k ≤ H, ∀ x : ℂ, (quad c)^[k] x ∈ U →
      connectedComponentIn ((quad c)^[k] ⁻¹' V) x ∩
          ((quad c)^[k] ⁻¹' U) =
        connectedComponentIn ((quad c)^[k] ⁻¹' U) x) :
    ∀ k ≤ H, ∀ x : ℂ, (quad c)^[k] x ∈ U →
      componentReflectionRank c U k x = componentReflectionRank c V k x := by
  intro k
  induction k with
  | zero =>
      intro hk x hx
      rfl
  | succ k ih =>
      intro hk x hx
      have hxTail : (quad c)^[k] (quad c x) ∈ U := by
        simpa only [Function.iterate_succ_apply] using hx
      have ht := ih (by omega) (quad c x) hxTail
      have he := quadratic_enlargement_reflection_iff_of_no_merger
        c (k+1) U V hUV x (by omega) hx (hno (k+1) hk x hx)
      simp only [componentReflectionRank, ht, he]

end
end LoopsQuadraticStableReflection

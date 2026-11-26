import QuadraticCriticalWindow
import QuadraticEnlargementDegree

/-!
# Local ramification conservation on actual quadratic components

The weights are the exact local orders already certified by the translated
quadratic-iterate factorization.  Their sum over an actual inverse fiber is
the intrinsic component degree, including at postcritical target points.
The proof counts the two signed inverse branches and retains the double
weight at their unique collision, rather than discarding that collision.
-/

namespace LoopsQuadraticLocalRamification

open Set Function Classical Polynomial
open LoopsQuadraticTransversality QuadraticCriticalWindow
open LoopsQuadraticCylinderCensus LoopsQuadraticCriticalFiberCensus
open LoopsQuadraticCylinderRamification LoopsQuadraticComponentFiberDegree
open LoopsStationarySeparatorTransport
open scoped BigOperators

noncomputable section

/-- The exact local order of the n-th actual quadratic iterate at z. -/
def localMultiplicity (c z : ℂ) (n : ℕ) : ℕ := 2 ^ criticalCount c z n

theorem localMultiplicity_pos (c z : ℂ) (n : ℕ) :
    0 < localMultiplicity c z n := by
  unfold localMultiplicity
  positivity

theorem returnOrbit_shift (c z : ℂ) (n : ℕ) :
    returnOrbit c z (n+1) = returnOrbit c (quad c z) n := by
  rw [returnOrbit_eq_iterate, returnOrbit_eq_iterate, Function.iterate_succ_apply]

/-- Split off the first orbit position from the exact critical count. -/
theorem criticalCount_shift (c z : ℂ) (n : ℕ) :
    criticalCount c z (n+1) =
      criticalCount c (quad c z) n + (if z = 0 then 1 else 0) := by
  induction n with
  | zero => simp [criticalCount, returnOrbit]
  | succ n ih =>
    change (if returnOrbit c z (n+1) = 0 then criticalCount c z (n+1) + 1
        else criticalCount c z (n+1)) =
      (if returnOrbit c (quad c z) n = 0 then criticalCount c (quad c z) n + 1
        else criticalCount c (quad c z) n) + (if z = 0 then 1 else 0)
    rw [returnOrbit_shift, ih]
    split_ifs <;> omega

/-- A critical first step doubles the local order; every other step
preserves the local order of the remaining iterate. -/
theorem localMultiplicity_step (c z : ℂ) (n : ℕ) :
    localMultiplicity c z (n+1) =
      (if z = 0 then 2 else 1) * localMultiplicity c (quad c z) n := by
  unfold localMultiplicity
  rw [criticalCount_shift, pow_add]
  by_cases hz : z = 0 <;> simp [hz, Nat.mul_comm]

/-- These weights are certified exact polynomial orders, not merely
positive numerical labels on inverse points. -/
theorem localMultiplicity_exact_order (c z : ℂ) (n : ℕ) :
    (X : ℂ[X]) ^ localMultiplicity c z n ∣
        shiftedOrbit c z n - C (returnOrbit c z n) ∧
      ¬ (X : ℂ[X]) ^ (localMultiplicity c z n + 1) ∣
        shiftedOrbit c z n - C (returnOrbit c z n) :=
  shiftedOrbit_exact_order c z n

theorem localMultiplicity_eq_one_iff (c z : ℂ) (n : ℕ) :
    localMultiplicity c z n = 1 ↔ ∀ k < n, (quad c)^[k] z ≠ 0 := by
  constructor
  · intro he
    have hc : criticalCount c z n = 0 := by
      by_contra hn
      obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hn
      change (2 : ℕ) ^ criticalCount c z n = 1 at he
      rw [hk, pow_succ] at he
      have hp : 0 < (2 : ℕ)^k := by positivity
      omega
    simpa only [returnOrbit_eq_iterate] using
      (criticalCount_eq_zero_iff c z n).mp hc
  · intro h
    have hc : criticalCount c z n = 0 :=
      (criticalCount_eq_zero_iff c z n).mpr
        (by simpa only [returnOrbit_eq_iterate] using h)
    simp [localMultiplicity, hc]

theorem fiberRoot_eq_zero_iff (c w : ℂ) : fiberRoot c w = 0 ↔ w = c := by
  constructor
  · intro h
    simpa [h] using (fiberRoot_spec c w).symm
  · intro h
    subst w
    have he : fiberRoot c c * fiberRoot c c = 0 := by
      linear_combination fiberRoot_spec c c
    exact (mul_eq_zero.mp he).elim id id

/-- The nonsymmetric component contains no critical point. -/
theorem quadratic_nonsymmetric_component_omits_zero (c : ℂ) (n : ℕ)
    (V : Set ℂ) (x : ℂ)
    (hn : ¬ (∀ z ∈ connectedComponentIn ((quad c)^[n+1] ⁻¹' V) x,
      -z ∈ connectedComponentIn ((quad c)^[n+1] ⁻¹' V) x)) :
    (0 : ℂ) ∉ connectedComponentIn ((quad c)^[n+1] ⁻¹' V) x := by
  intro hz
  apply hn
  exact even_component_reflection_of_pair ((quad c)^[n+1]) V
    (quadratic_positive_iterate_even c (n+1) (by omega)) x 0 hz (by simpa using hz)

/-- On a single signed sheet the whole weighted fiber transports
unchanged to the next actual component. -/
theorem quadratic_component_nonsymmetric_weighted (c : ℂ) (n : ℕ)
    (V : Set ℂ) (hVo : IsOpen V) (x y : ℂ)
    (hx : (quad c)^[n+1] x ∈ V)
    (hn : ¬ (∀ z ∈ connectedComponentIn ((quad c)^[n+1] ⁻¹' V) x,
      -z ∈ connectedComponentIn ((quad c)^[n+1] ⁻¹' V) x)) :
    (∑ z ∈ localFiber c (n+1) (connectedComponentIn ((quad c)^[n+1] ⁻¹' V) x) y,
        localMultiplicity c z (n+1)) =
      ∑ w ∈ localFiber c n (connectedComponentIn ((quad c)^[n] ⁻¹' V) (quad c x)) y,
        localMultiplicity c w n := by
  let C := connectedComponentIn ((quad c)^[n+1] ⁻¹' V) x
  let A := localFiber c (n+1) C y
  have hi := quadratic_component_nonsymmetric_inj c n V x hn
  have hAi : InjOn (quad c) (↑A : Set ℂ) := by
    intro a ha b hb hab
    exact hi ((mem_localFiber c (n+1) C y a).mp ha).1
      ((mem_localFiber c (n+1) C y b).mp hb).1 hab
  have hz0 := quadratic_nonsymmetric_component_omits_zero c n V x hn
  calc
    (∑ z ∈ A, localMultiplicity c z (n+1)) =
        ∑ z ∈ A, localMultiplicity c (quad c z) n := by
      apply Finset.sum_congr rfl
      intro z hz
      have hne : z ≠ 0 := by
        intro he
        apply hz0
        rw [← he]
        exact ((mem_localFiber c (n+1) C y z).mp hz).1
      rw [localMultiplicity_step, if_neg hne, one_mul]
    _ = ∑ w ∈ A.image (quad c), localMultiplicity c w n :=
      (Finset.sum_image hAi).symm
    _ = ∑ w ∈ localFiber c n
        (connectedComponentIn ((quad c)^[n] ⁻¹' V) (quad c x)) y,
        localMultiplicity c w n := by
      rw [show A.image (quad c) = localFiber c n
          (connectedComponentIn ((quad c)^[n] ⁻¹' V) (quad c x)) y from
        quadratic_component_fiber_image c n V hVo x y hx]

/-- In the symmetric case the two signed inverse branches describe
the entire component fiber, with their sole duplicate removed. -/
theorem quadratic_component_symmetric_fiber (c : ℂ) (n : ℕ)
    (V : Set ℂ) (hVo : IsOpen V) (x y : ℂ)
    (hx : (quad c)^[n+1] x ∈ V)
    (hs : ∀ z ∈ connectedComponentIn ((quad c)^[n+1] ⁻¹' V) x,
      -z ∈ connectedComponentIn ((quad c)^[n+1] ⁻¹' V) x) :
    localFiber c (n+1) (connectedComponentIn ((quad c)^[n+1] ⁻¹' V) x) y =
      (localFiber c n (connectedComponentIn ((quad c)^[n] ⁻¹' V) (quad c x)) y).image
          (fiberRoot c) ∪
      ((localFiber c n (connectedComponentIn ((quad c)^[n] ⁻¹' V) (quad c x)) y).erase c).image
          (fun w => -fiberRoot c w) := by
  let f := quad c
  let C := connectedComponentIn (f^[n+1] ⁻¹' V) x
  let D := connectedComponentIn (f^[n] ⁻¹' V) (f x)
  let B := localFiber c n D y
  have hfirst : f '' C = D := by
    simpa only [Function.iterate_one] using
      quadratic_prefix_component_image c n 1 V hVo x hx
  have hposmem (w : ℂ) : fiberRoot c w ∈ C ↔ w ∈ D := by
    constructor
    · intro hw
      rw [← hfirst]
      exact ⟨fiberRoot c w, hw, fiberRoot_spec c w⟩
    · intro hw
      have hw' : w ∈ f '' C := hfirst.symm ▸ hw
      obtain ⟨a, ha, haw⟩ := hw'
      have he : f a = f (fiberRoot c w) :=
        haw.trans (fiberRoot_spec c w).symm
      rcases quadratic_eq_or_neg c a (fiberRoot c w) he with h | h
      · exact h ▸ ha
      · have h' : -a ∈ C := hs a ha
        rw [h, neg_neg] at h'
        exact h'
  have hnegmem (w : ℂ) : -fiberRoot c w ∈ C ↔ w ∈ D := by
    constructor
    · intro hw
      have h : -(-fiberRoot c w) ∈ C := hs _ hw
      rw [neg_neg] at h
      exact (hposmem w).mp h
    · intro hw
      exact hs _ ((hposmem w).mpr hw)
  have hpos : (globalFiber c n y).filter (fun w => fiberRoot c w ∈ C) = B := by
    ext w
    simp only [B, Finset.mem_filter, mem_globalFiber, mem_localFiber, hposmem]
    exact and_comm
  have hneg : ((globalFiber c n y).erase c).filter (fun w => -fiberRoot c w ∈ C) =
      B.erase c := by
    ext w
    simp only [B, Finset.mem_filter, Finset.mem_erase, mem_globalFiber,
      mem_localFiber, hnegmem]
    tauto
  change localFiber c (n+1) C y =
    B.image (fiberRoot c) ∪ (B.erase c).image (fun w => -fiberRoot c w)
  rw [localFiber_signed_recursion, hpos, hneg]

/-- The inverse-branch collision at zero retains twice the tail
weight. Consequently every symmetric step doubles the weighted fiber,
even when the chosen target is postcritical. -/
theorem quadratic_component_symmetric_weighted (c : ℂ) (n : ℕ)
    (V : Set ℂ) (hVo : IsOpen V) (x y : ℂ)
    (hx : (quad c)^[n+1] x ∈ V)
    (hs : ∀ z ∈ connectedComponentIn ((quad c)^[n+1] ⁻¹' V) x,
      -z ∈ connectedComponentIn ((quad c)^[n+1] ⁻¹' V) x) :
    (∑ z ∈ localFiber c (n+1) (connectedComponentIn ((quad c)^[n+1] ⁻¹' V) x) y,
        localMultiplicity c z (n+1)) =
      2 * ∑ w ∈ localFiber c n
        (connectedComponentIn ((quad c)^[n] ⁻¹' V) (quad c x)) y,
        localMultiplicity c w n := by
  let B := localFiber c n (connectedComponentIn ((quad c)^[n] ⁻¹' V) (quad c x)) y
  have hneg : Injective (fun w => -fiberRoot c w) := by
    intro a b h
    apply fiberRoot_injective c
    linear_combination -h
  have hposweight (w : ℂ) : localMultiplicity c (fiberRoot c w) (n+1) =
      localMultiplicity c w n + (if w = c then localMultiplicity c w n else 0) := by
    have he : quad c (fiberRoot c w) = w := fiberRoot_spec c w
    rw [localMultiplicity_step, he]
    by_cases hw : w = c
    · rw [if_pos ((fiberRoot_eq_zero_iff c w).mpr hw), if_pos hw]
      omega
    · rw [if_neg (fun h => hw ((fiberRoot_eq_zero_iff c w).mp h)), if_neg hw]
      omega
  have hnegweight (w : ℂ) (hw : w ≠ c) :
      localMultiplicity c (-fiberRoot c w) (n+1) = localMultiplicity c w n := by
    have hne : -fiberRoot c w ≠ 0 :=
      neg_ne_zero.mpr (fun h => hw ((fiberRoot_eq_zero_iff c w).mp h))
    have he : quad c (-fiberRoot c w) = w := by
      change (-fiberRoot c w)^2+c = w
      calc
        (-fiberRoot c w)^2+c = (fiberRoot c w)^2+c := by ring
        _ = w := fiberRoot_spec c w
    rw [localMultiplicity_step, if_neg hne, one_mul, he]
  have hpossum :
      (∑ w ∈ B, localMultiplicity c (fiberRoot c w) (n+1)) =
        (∑ w ∈ B, localMultiplicity c w n) +
          (if c ∈ B then localMultiplicity c c n else 0) := by
    calc
      _ = ∑ w ∈ B, (localMultiplicity c w n +
          (if w = c then localMultiplicity c w n else 0)) :=
        Finset.sum_congr rfl (fun w _ => hposweight w)
      _ = _ := by rw [Finset.sum_add_distrib]; simp
  have hnegsum :
      (∑ w ∈ B.erase c, localMultiplicity c (-fiberRoot c w) (n+1)) =
        ∑ w ∈ B.erase c, localMultiplicity c w n := by
    apply Finset.sum_congr rfl
    intro w hw
    exact hnegweight w (Finset.mem_erase.mp hw).1
  rw [quadratic_component_symmetric_fiber c n V hVo x y hx hs]
  change (∑ z ∈ B.image (fiberRoot c) ∪ (B.erase c).image (fun w => -fiberRoot c w),
      localMultiplicity c z (n+1)) = 2 * ∑ w ∈ B, localMultiplicity c w n
  rw [Finset.sum_union (inverse_branches_disjoint c B),
    Finset.sum_image (fiberRoot_injective c).injOn, Finset.sum_image hneg.injOn,
    hpossum, hnegsum]
  by_cases hc : c ∈ B
  · have he := Finset.sum_erase_add B (fun w => localMultiplicity c w n) hc
    rw [if_pos hc]
    omega
  · rw [if_neg hc, Finset.erase_eq_of_notMem hc]
    omega

/-- Conservation of exact local orders in every fiber of an actual
connected quadratic pullback component. No regularity of the target
point or simple connectivity of the target domain is assumed. -/
theorem quadratic_component_weighted_fiber_degree (c : ℂ) (V : Set ℂ)
    (hVo : IsOpen V) (hVc : IsPreconnected V) (y : ℂ) (hy : y ∈ V)
    (n : ℕ) (x : ℂ) (hx : (quad c)^[n] x ∈ V) :
    (∑ z ∈ localFiber c n (connectedComponentIn ((quad c)^[n] ⁻¹' V) x) y,
      localMultiplicity c z n) = 2 ^ componentReflectionRank c V n x := by
  induction n generalizing x with
  | zero =>
    have hxV : x ∈ V := by simpa using hx
    have hsub : V ⊆ connectedComponentIn V x :=
      hVc.subset_connectedComponentIn hxV Subset.rfl
    have hmem : y ∈ connectedComponentIn ((quad c)^[0] ⁻¹' V) x := by
      simpa using hsub hy
    have hf : localFiber c 0 (connectedComponentIn ((quad c)^[0] ⁻¹' V) x) y = {y} := by
      ext z
      simp only [mem_localFiber, Function.iterate_zero, id_eq, Finset.mem_singleton]
      constructor
      · exact fun h => h.2
      · intro h
        subst z
        exact ⟨hmem, rfl⟩
    rw [hf]
    simp [localMultiplicity, criticalCount, componentReflectionRank]
  | succ n ih =>
    have hxD : (quad c)^[n] (quad c x) ∈ V := by
      simpa only [Function.iterate_succ_apply] using hx
    have ht := ih (quad c x) hxD
    by_cases hs : ∀ z ∈ connectedComponentIn ((quad c)^[n+1] ⁻¹' V) x,
        -z ∈ connectedComponentIn ((quad c)^[n+1] ⁻¹' V) x
    · rw [quadratic_component_symmetric_weighted c n V hVo x y hx hs, ht]
      simp only [componentReflectionRank, if_pos hs, pow_succ]
      omega
    · rw [quadratic_component_nonsymmetric_weighted c n V hVo x y hx hs, ht]
      simp only [componentReflectionRank, if_neg hs, Nat.add_zero]

/-- The previously recursive target-fiber defect is exactly the sum
of the actual local ramification excesses at its distinct inverse points. -/
theorem quadratic_component_defect_eq_ramification_sum (c : ℂ) (V : Set ℂ)
    (hVo : IsOpen V) (hVc : IsPreconnected V) (y : ℂ) (hy : y ∈ V)
    (n : ℕ) (x : ℂ) (hx : (quad c)^[n] x ∈ V) :
    componentFiberDefect c V y n x =
      ∑ z ∈ localFiber c n (connectedComponentIn ((quad c)^[n] ⁻¹' V) x) y,
        (localMultiplicity c z n - 1) := by
  let F := localFiber c n (connectedComponentIn ((quad c)^[n] ⁻¹' V) x) y
  have hs := quadratic_component_weighted_fiber_degree c V hVo hVc y hy n x hx
  have hd := quadratic_component_fiber_card_exact c V hVo hVc y hy n x hx
  have hadd : (∑ z ∈ F, (localMultiplicity c z n - 1)) + F.card =
      ∑ z ∈ F, localMultiplicity c z n := by
    have hcard : (∑ _z ∈ F, (1 : ℕ)) = F.card := by simp
    rw [← hcard, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro z _
    exact Nat.sub_add_cancel (localMultiplicity_pos c z n)
  change (∑ z ∈ F, localMultiplicity c z n) = _ at hs
  change F.card + componentFiberDefect c V y n x = _ at hd
  change componentFiberDefect c V y n x = ∑ z ∈ F, (localMultiplicity c z n - 1)
  omega

end
end LoopsQuadraticLocalRamification

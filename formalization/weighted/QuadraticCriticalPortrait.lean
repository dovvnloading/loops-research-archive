import QuadraticRamificationCensus

/-!
# Exact distinct critical-point portraits of quadratic iterates

The critical locus is the union of the actual inverse fibers of zero.
Its cardinality depends only on whether, and when, the critical point
first returns to itself. Repeated points are counted only once.
-/

namespace LoopsQuadraticCriticalPortrait

open Set Function Classical
open LoopsQuadraticCylinderRamification LoopsQuadraticCriticalFiberCensus
open LoopsQuadraticRamificationCensus

noncomputable section

/-- The complete inverse of a finite target set under the actual quadratic.
The negative branch omits the duplicate inverse of the critical value. -/
def signedPreimage (c : ℂ) (A : Finset ℂ) : Finset ℂ :=
  A.image (fiberRoot c) ∪ (A.erase c).image (fun w => -fiberRoot c w)

theorem mem_signedPreimage (c : ℂ) (A : Finset ℂ) (z : ℂ) :
    z ∈ signedPreimage c A ↔ quad c z ∈ A := by
  classical
  simp only [signedPreimage, Finset.mem_union, Finset.mem_image, Finset.mem_erase]
  constructor
  · rintro (⟨w, hw, rfl⟩ | ⟨w, ⟨_, hw⟩, rfl⟩)
    · simpa only [quad, fiberRoot_spec] using hw
    · have he : quad c (-fiberRoot c w) = w := by
        calc
          quad c (-fiberRoot c w) = (fiberRoot c w)^2+c := by simp [quad]
          _ = w := fiberRoot_spec c w
      rwa [he]
  · intro hz
    let w := quad c z
    have hw : w ∈ A := hz
    have hprod : (z-fiberRoot c w)*(z+fiberRoot c w) = 0 := by
      have h := fiberRoot_spec c w
      dsimp [w, quad] at h
      linear_combination -h
    by_cases hpos : z = fiberRoot c w
    · exact Or.inl ⟨w, hw, hpos.symm⟩
    · have hneg := (mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hpos)
      have hwc : w ≠ c := by
        intro h
        have hzsq : z*z = 0 := by
          dsimp [w, quad] at h
          linear_combination h
        have hr := fiberRoot_spec c w
        have hrsq : fiberRoot c w * fiberRoot c w = 0 := by
          linear_combination hr + h
        have hz0 : z = 0 := (mul_eq_zero.mp hzsq).elim id id
        have hr0 : fiberRoot c w = 0 := (mul_eq_zero.mp hrsq).elim id id
        exact hpos (hz0.trans hr0.symm)
      exact Or.inr ⟨w, ⟨hwc, hw⟩, by linear_combination -hneg⟩

/-- Every target contributes two inverse points except the critical value,
which contributes exactly one. This counts distinct complex points. -/
theorem signedPreimage_card (c : ℂ) (A : Finset ℂ) :
    (signedPreimage c A).card + (if c ∈ A then 1 else 0) = 2*A.card := by
  classical
  have hneg : Injective (fun w => -fiberRoot c w) := by
    intro a b h
    exact fiberRoot_injective c (neg_injective h)
  rw [signedPreimage, Finset.card_union_of_disjoint (inverse_branches_disjoint c A),
    Finset.card_image_of_injective _ (fiberRoot_injective c),
    Finset.card_image_of_injective _ hneg]
  by_cases hc : c ∈ A
  · rw [if_pos hc, Finset.card_erase_of_mem hc]
    have hp : 0 < A.card := Finset.card_pos.mpr ⟨c, hc⟩
    omega
  · rw [if_neg hc, Finset.erase_eq_of_notMem hc]
    omega

/-- The next critical locus is zero together with the complete inverse
of the previous critical locus, including every critical coincidence. -/
theorem criticalPoints_succ (c : ℂ) (n : ℕ) :
    criticalPoints c (n+1) univ =
      insert 0 (signedPreimage c (criticalPoints c n univ)) := by
  classical
  ext z
  rw [mem_criticalPoints, Finset.mem_insert, mem_signedPreimage, mem_criticalPoints]
  simp only [mem_univ, true_and]
  constructor
  · rintro ⟨k, hk, hz⟩
    cases k with
    | zero => exact Or.inl (by simpa using hz)
    | succ k =>
      exact Or.inr ⟨k, by omega, by simpa only [iterate_succ_apply] using hz⟩
  · rintro (hz | ⟨k, hk, hz⟩)
    · exact ⟨0, by omega, by simpa using hz⟩
    · exact ⟨k+1, by omega, by simpa only [iterate_succ_apply] using hz⟩

/-- The critical value belongs to the n-th critical locus precisely when
the critical point has a positive return of length at most n. -/
theorem critical_value_mem_criticalPoints_iff (c : ℂ) (n : ℕ) :
    c ∈ criticalPoints c n univ ↔
      ∃ p : ℕ, 0 < p ∧ p ≤ n ∧ (quad c)^[p] 0 = 0 := by
  rw [mem_criticalPoints]
  simp only [mem_univ, true_and]
  have hf0 : quad c 0 = c := by simp [quad]
  constructor
  · rintro ⟨k, hk, he⟩
    exact ⟨k+1, by omega, by omega,
      by simpa only [iterate_succ_apply, hf0] using he⟩
  · rintro ⟨p, hp, hpn, he⟩
    cases p with
    | zero => omega
    | succ k =>
      exact ⟨k, by omega, by simpa only [iterate_succ_apply, hf0] using he⟩

/-- Before the first critical return, the distinct critical count doubles
and gains one. Once a positive critical return has occurred, it doubles
and loses one. The displayed equality uses only natural-number addition. -/
theorem criticalPoints_card_succ (c : ℂ) (n : ℕ) :
    (criticalPoints c (n+1) univ).card +
      (if c ∈ criticalPoints c n univ then 1 else 0) =
      2*(criticalPoints c n univ).card +
        (if c ∈ criticalPoints c n univ then 0 else 1) := by
  classical
  have h := signedPreimage_card c (criticalPoints c n univ)
  have hz : 0 ∈ signedPreimage c (criticalPoints c n univ) ↔
      c ∈ criticalPoints c n univ := by
    rw [mem_signedPreimage]
    simp [quad]
  rw [criticalPoints_succ]
  by_cases hc : c ∈ criticalPoints c n univ
  · rw [Finset.insert_eq_of_mem (hz.mpr hc), if_pos hc, if_pos hc, Nat.add_zero]
    simpa only [if_pos hc] using h
  · rw [Finset.card_insert_of_notMem (fun h0 => hc (hz.mp h0)),
      if_neg hc, if_neg hc]
    simp only [if_neg hc] at h
    omega

/-- With no positive critical return before the horizon, all 2^n-1
critical points of the iterate are distinct. -/
theorem criticalPoints_card_of_no_return (c : ℂ) (n : ℕ) :
    (∀ p : ℕ, 0 < p → p < n → (quad c)^[p] 0 ≠ 0) →
      (criticalPoints c n univ).card + 1 = 2^n := by
  induction n with
  | zero =>
    intro _
    have he : criticalPoints c 0 univ = ∅ := by
      ext z
      simp [mem_criticalPoints]
    simp [he]
  | succ n ih =>
    intro hfirst
    have hprev := ih (fun p hp hpn => hfirst p hp (by omega))
    have hc : c ∉ criticalPoints c n univ := by
      intro hc
      obtain ⟨p, hp, hpn, he⟩ := (critical_value_mem_criticalPoints_iff c n).mp hc
      exact hfirst p hp (by omega) he
    have hs := criticalPoints_card_succ c n
    simp only [if_neg hc, Nat.add_zero] at hs
    rw [pow_succ]
    omega

/-- Exact critical-locus cardinality after the first positive return of
the critical point. The horizon is p+k, and p is the exact return time. -/
theorem criticalPoints_card_after_first_return (c : ℂ) (p : ℕ)
    (hp : 0 < p) (hreturn : (quad c)^[p] 0 = 0)
    (hfirst : ∀ j : ℕ, 0 < j → j < p → (quad c)^[j] 0 ≠ 0) (k : ℕ) :
    (criticalPoints c (p+k) univ).card = (2^p-2)*2^k+1 := by
  induction k with
  | zero =>
    have h := criticalPoints_card_of_no_return c p hfirst
    have hpow : 2 ≤ (2 : ℕ)^p := by
      cases p with
      | zero => omega
      | succ p =>
        have : 0 < (2 : ℕ)^p := pow_pos (by decide) p
        rw [pow_succ]
        omega
    simp only [Nat.add_zero, pow_zero, Nat.mul_one]
    omega
  | succ k ih =>
    have hc : c ∈ criticalPoints c (p+k) univ :=
      (critical_value_mem_criticalPoints_iff c (p+k)).mpr
        ⟨p, hp, by omega, hreturn⟩
    have hs := criticalPoints_card_succ c (p+k)
    simp only [if_pos hc, Nat.add_zero] at hs
    rw [ih] at hs
    have he : p+(k+1) = p+k+1 := by omega
    rw [he, pow_succ]
    rw [← Nat.mul_assoc]
    omega

/-- The same exact portrait formula at an arbitrary horizon beyond the
first critical return, without choosing an auxiliary time difference. -/
theorem criticalPoints_card_at_horizon (c : ℂ) (p n : ℕ)
    (hp : 0 < p) (hpn : p ≤ n) (hreturn : (quad c)^[p] 0 = 0)
    (hfirst : ∀ j : ℕ, 0 < j → j < p → (quad c)^[j] 0 ≠ 0) :
    (criticalPoints c n univ).card = (2^p-2)*2^(n-p)+1 := by
  have h := criticalPoints_card_after_first_return c p hp hreturn hfirst (n-p)
  have hn : p+(n-p) = n := by omega
  simpa only [hn] using h

/-- For z ↦ z² every positive iterate has exactly one distinct critical
point, although its local order grows with the horizon. -/
theorem criticalPoints_zero_parameter_card (n : ℕ) (hn : 0 < n) :
    (criticalPoints 0 n univ).card = 1 := by
  have h := criticalPoints_card_at_horizon 0 1 n (by omega) (by omega)
    (by norm_num [quad]) (by intro j hj hj1; omega)
  simpa using h

/-- The actual critical orbit 0 ↦ -1 ↦ 0 has exact period two.
Consequently z ↦ z²-1 has precisely 2^(n+1)+1 distinct critical points
in its (n+2)-nd iterate. -/
theorem criticalPoints_neg_one_card (n : ℕ) :
    (criticalPoints (-1) (n+2) univ).card = 2^(n+1)+1 := by
  have h := criticalPoints_card_after_first_return (-1) 2 (by omega)
    (by norm_num [iterate_succ_apply, quad])
    (by
      intro j hj hj2
      have he : j = 1 := by omega
      subst j
      norm_num [quad]) n
  rw [show 2+n = n+2 by omega] at h
  calc
    (criticalPoints (-1) (n+2) univ).card = (2^2-2)*2^n+1 := h
    _ = 2^(n+1)+1 := by simp [pow_succ, Nat.mul_comm]

private theorem neg_two_critical_orbit_after_two (n : ℕ) :
    (quad (-2))^[n+2] 0 = 2 := by
  induction n with
  | zero => norm_num [iterate_succ_apply, quad]
  | succ n ih =>
    rw [show n+1+2 = (n+2)+1 by omega, iterate_succ_apply', ih]
    norm_num [quad]

/-- The actual critical orbit 0 ↦ -2 ↦ 2 ↦ 2 never returns to zero.
Thus the maximal distinct count 2^n-1 is attained at every horizon. -/
theorem criticalPoints_neg_two_card (n : ℕ) :
    (criticalPoints (-2) n univ).card + 1 = 2^n := by
  apply criticalPoints_card_of_no_return
  intro p hp _
  by_cases hp1 : p = 1
  · subst p
    norm_num [quad]
  · have he : p = (p-2)+2 := by omega
    rw [he, neg_two_critical_orbit_after_two]
    norm_num

end
end LoopsQuadraticCriticalPortrait

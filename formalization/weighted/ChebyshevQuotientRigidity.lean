import Mathlib
import ChebyshevFibers

/-!
# Nonconstant monotone factors of the actual Chebyshev carrier

Every nondegenerate connected subset of the bounded-orbit interval
covers the whole interval under some iterate of any positive return.
Consequently a globally equivariant connected-fiber quotient of this
carrier is either injective or constant. No continuity of the quotient
map is needed for this dichotomy.
-/

namespace LoopsChebyshevQuotient
open Set Function LoopsParabolic LoopsChebyshev

noncomputable section

private def anglePoint (t : ℝ) : ℂ := ((2 * Real.cos t : ℝ) : ℂ)

private theorem angle_mem (t : ℝ) : anglePoint t ∈ realSegment 2 := by
  refine ⟨2 * Real.cos t, ?_, rfl⟩
  have h := Real.cos_mem_Icc t
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

private theorem angle_surj : SurjOn anglePoint (Icc 0 Real.pi) (realSegment 2) := by
  rintro z ⟨x, hx, rfl⟩
  have hx' : x / 2 ∈ Icc (-1 : ℝ) 1 :=
    ⟨by linarith [hx.1], by linarith [hx.2]⟩
  obtain ⟨t, ht, he⟩ := Real.surjOn_cos hx'
  refine ⟨t, ht, ?_⟩
  unfold anglePoint
  rw [he]
  congr 1 <;> ring

private theorem angle_step (t : ℝ) :
    cquad (-2) (anglePoint t) = anglePoint (2 * t) := by
  simp only [anglePoint, cquad_ofReal, Real.cos_two_mul, quad]
  congr 1 <;> ring

private theorem angle_iterate (n : ℕ) (t : ℝ) :
    (cquad (-2))^[n] (anglePoint t) = anglePoint ((2 : ℝ)^n * t) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iterate_succ_apply', ih, angle_step, pow_succ]
    congr 1 <;> ring

private theorem angle_retimed (p n : ℕ) (t : ℝ) :
    ((cquad (-2))^[p])^[n] (anglePoint t) =
      anglePoint (((2 : ℝ)^p)^n * t) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iterate_succ_apply', ih, angle_iterate, pow_succ]
    congr 1 <;> ring

private theorem iterate_mem (n : ℕ) {z : ℂ} (hz : z ∈ realSegment 2) :
    (cquad (-2))^[n] z ∈ realSegment 2 := by
  induction n with
  | zero => exact hz
  | succ n ih =>
    rw [iterate_succ_apply']
    exact realSegment_invariant ih

private theorem retimed_mem (p n : ℕ) {z : ℂ} (hz : z ∈ realSegment 2) :
    ((cquad (-2))^[p])^[n] z ∈ realSegment 2 := by
  induction n with
  | zero => exact hz
  | succ n ih =>
    rw [iterate_succ_apply']
    exact iterate_mem p ih

private theorem angle_interval_subset {S : Set ℂ}
    (hS : IsPreconnected S) (hsub : S ⊆ realSegment 2)
    {a b : ℝ} (ha : a ∈ Icc 0 Real.pi) (hb : b ∈ Icc 0 Real.pi)
    (haS : anglePoint a ∈ S) (hbS : anglePoint b ∈ S) :
    anglePoint '' Icc a b ⊆ S := by
  rintro _ ⟨t, ht, rfl⟩
  have hR : IsPreconnected (Complex.re '' S) :=
    hS.image _ Complex.continuous_re.continuousOn
  have haR : (anglePoint a).re ∈ Complex.re '' S := ⟨_, haS, rfl⟩
  have hbR : (anglePoint b).re ∈ Complex.re '' S := ⟨_, hbS, rfl⟩
  have h₁ := Real.cos_le_cos_of_nonneg_of_le_pi (ha.1.trans ht.1) hb.2 ht.2
  have h₂ := Real.cos_le_cos_of_nonneg_of_le_pi ha.1 (ht.2.trans hb.2) ht.1
  have htR : (anglePoint t).re ∈ Complex.re '' S := by
    apply hR.ordConnected.out hbR haR
    change 2 * Real.cos b ≤ 2 * Real.cos t ∧ 2 * Real.cos t ≤ 2 * Real.cos a
    exact ⟨by linarith, by linarith⟩
  obtain ⟨z, hz, he⟩ := htR
  have hi := (mem_realSegment_iff.mp (hsub hz)).1
  have heq : z = anglePoint t :=
    Complex.ext he (by simpa [anglePoint] using hi)
  exact heq ▸ hz

/-- A quantitative full-cover criterion in the actual angular coordinate.
The constant 3π is sufficient, not claimed optimal. -/
theorem retimed_angular_interval_covers (p n : ℕ) (a b : ℝ)
    (hgap : 3 * Real.pi ≤ ((2 : ℝ)^p)^n * (b - a)) :
    ((cquad (-2))^[p])^[n] '' (anglePoint '' Icc a b) = realSegment 2 := by
  apply Subset.antisymm
  · rintro _ ⟨z, ⟨t, _, rfl⟩, rfl⟩
    exact retimed_mem p n (angle_mem t)
  · intro z hz
    obtain ⟨θ, hθ, rfl⟩ := angle_surj hz
    let B : ℝ := ((2 : ℝ)^p)^n
    have hB : 0 < B := by dsimp [B]; positivity
    have hP : 0 < 2 * Real.pi := by linarith [Real.pi_pos]
    let k : ℤ := ⌈(B * a) / (2 * Real.pi)⌉
    have hklo : B * a ≤ (k : ℝ) * (2 * Real.pi) :=
      (div_le_iff₀ hP).mp (Int.le_ceil _)
    have hkhi : (k : ℝ) * (2 * Real.pi) < B * a + 2 * Real.pi := by
      calc
        (k : ℝ) * (2 * Real.pi) <
            ((B * a) / (2 * Real.pi) + 1) * (2 * Real.pi) :=
          mul_lt_mul_of_pos_right (Int.ceil_lt_add_one _) hP
        _ = B * a + 2 * Real.pi := by
          rw [add_mul, div_mul_cancel₀ _ (ne_of_gt hP), one_mul]
    change 3 * Real.pi ≤ B * (b - a) at hgap
    let t := (θ + (k : ℝ) * (2 * Real.pi)) / B
    have ht : t ∈ Icc a b := by
      constructor
      · exact (le_div_iff₀ hB).mpr (by linarith [hθ.1])
      · exact (div_le_iff₀ hB).mpr (by nlinarith [hθ.2])
    refine ⟨anglePoint t, ⟨t, ht, rfl⟩, ?_⟩
    rw [angle_retimed]
    change anglePoint (B * t) = anglePoint θ
    have he : B * t = θ + (k : ℝ) * (2 * Real.pi) := by
      dsimp [t]
      rw [mul_comm B, div_mul_cancel₀ _ (ne_of_gt hB)]
    rw [he]
    simp only [anglePoint, Real.cos_add_int_mul_two_pi]

/-- Every nondegenerate connected subset of the physical Chebyshev
carrier covers the entire carrier after finitely many applications of
any positive retimed return. This is stronger than mere open-set exactness. -/
theorem retimed_connected_subset_covers (p : ℕ) (hp : 0 < p)
    (S : Set ℂ) (hS : IsPreconnected S) (hsub : S ⊆ realSegment 2)
    (x y : ℂ) (hx : x ∈ S) (hy : y ∈ S) (hne : x ≠ y) :
    ∃ n : ℕ, ((cquad (-2))^[p])^[n] '' S = realSegment 2 := by
  obtain ⟨a, ha, hea⟩ := angle_surj (hsub hx)
  obtain ⟨b, hb, heb⟩ := angle_surj (hsub hy)
  have hab : a ≠ b := by
    intro h
    apply hne
    rw [← hea, ← heb, h]
  have haS : anglePoint a ∈ S := by rwa [hea]
  have hbS : anglePoint b ∈ S := by rwa [heb]
  obtain ⟨u, v, huv, hI⟩ :
      ∃ u v : ℝ, u < v ∧ anglePoint '' Icc u v ⊆ S := by
    rcases lt_or_gt_of_ne hab with h | h
    · exact ⟨a, b, h, angle_interval_subset hS hsub ha hb haS hbS⟩
    · exact ⟨b, a, h, angle_interval_subset hS hsub hb ha hbS haS⟩
  have hpow : ∀ k : ℕ, 1 ≤ (2 : ℝ)^k := by
    intro k
    induction k with
    | zero => norm_num
    | succ k ih => rw [pow_succ]; linarith
  have hbase : 1 < (2 : ℝ)^p := by
    cases p with
    | zero => omega
    | succ k => rw [pow_succ]; linarith [hpow k]
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (3 * Real.pi / (v-u)) hbase
  have hgap : 3 * Real.pi ≤ ((2 : ℝ)^p)^n * (v-u) :=
    ((div_lt_iff₀ (sub_pos.mpr huv)).mp hn).le
  refine ⟨n, Subset.antisymm ?_ ?_⟩
  · rintro _ ⟨w, hw, rfl⟩
    exact retimed_mem p n (hsub hw)
  · rw [← retimed_angular_interval_covers p n u v hgap]
    exact image_mono hI

/-- A single collapsed pair in a connected fiber forces a globally
equivariant retimed factor to collapse the entire physical carrier.
The statement needs neither continuity nor topology on the codomain. -/
theorem retimed_collapsed_fiber_forces_constant {Y : Type*}
    (p : ℕ) (hp : 0 < p) (q : ℂ → Y) (G : Y → Y)
    (hf : ∀ a : Y, IsPreconnected (realSegment 2 ∩ q ⁻¹' {a}))
    (hsemi : ∀ z ∈ realSegment 2, q ((cquad (-2))^[p] z) = G (q z))
    (x y : ℂ) (hx : x ∈ realSegment 2) (hy : y ∈ realSegment 2)
    (hne : x ≠ y) (heq : q x = q y) :
    ∀ u ∈ realSegment 2, ∀ v ∈ realSegment 2, q u = q v := by
  let S : Set ℂ := realSegment 2 ∩ q ⁻¹' {q x}
  have hxS : x ∈ S := ⟨hx, rfl⟩
  have hyS : y ∈ S := ⟨hy, heq.symm⟩
  obtain ⟨n, hn⟩ := retimed_connected_subset_covers p hp S (hf (q x))
    inter_subset_left x y hxS hyS hne
  have hcomm : ∀ (m : ℕ) (z : ℂ), z ∈ realSegment 2 →
      q (((cquad (-2))^[p])^[m] z) = G^[m] (q z) := by
    intro m
    induction m with
    | zero => intro z hz; rfl
    | succ m ih =>
      intro z hz
      rw [iterate_succ_apply', iterate_succ_apply',
        hsemi _ (retimed_mem p m hz), ih z hz]
  have hconst : ∀ z ∈ realSegment 2, q z = G^[n] (q x) := by
    intro z hz
    rw [← hn] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    rw [hcomm n w hw.1]
    exact congrArg (G^[n]) hw.2
  intro u hu v hv
  exact (hconst u hu).trans (hconst v hv).symm

/-- On the actual bounded-orbit set, every nonconstant globally
semiconjugating quotient with connected fibers is injective,
uniformly for every positive retiming. -/
theorem bounded_orbit_monotone_factor_injective {Y : Type*}
    (p : ℕ) (hp : 0 < p) (q : ℂ → Y) (G : Y → Y)
    (hf : ∀ a : Y, IsPreconnected ({z | BoundedOrbit z} ∩ q ⁻¹' {a}))
    (hsemi : ∀ z, BoundedOrbit z → q ((cquad (-2))^[p] z) = G (q z))
    (hnonconstant : ∃ u v : ℂ, BoundedOrbit u ∧ BoundedOrbit v ∧ q u ≠ q v) :
    InjOn q {z | BoundedOrbit z} := by
  have hK : {z | BoundedOrbit z} = realSegment 2 := by
    ext z
    exact bounded_iff_realSegment z
  rw [hK] at hf ⊢
  intro x hx y hy heq
  by_contra hne
  obtain ⟨u, v, hu, hv, huv⟩ := hnonconstant
  apply huv
  exact retimed_collapsed_fiber_forces_constant p hp q G hf
    (fun z hz => hsemi z ((bounded_iff_realSegment z).mpr hz))
    x y hx hy hne heq u ((bounded_iff_realSegment u).mp hu)
    v ((bounded_iff_realSegment v).mp hv)

#print axioms retimed_angular_interval_covers
#print axioms retimed_connected_subset_covers
#print axioms retimed_collapsed_fiber_forces_constant
#print axioms bounded_orbit_monotone_factor_injective

end
end LoopsChebyshevQuotient

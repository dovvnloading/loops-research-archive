import ParabolicComplexPullback
import ParabolicSegment
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Dynamics.PeriodicPts.Defs
import Mathlib.Tactic

/-!
# Exact physical fibers at the quadratic Chebyshev parameter

The map is the archive's actual complex quadratic at c = -2.
The Joukowski map is not a freely chosen finite symbolic projection.
Classical identities are used to expose a genuine obstruction to a
single-valued future-compatible boundary address.
-/
namespace LoopsChebyshev
open Function Set
open scoped ComplexConjugate
open LoopsParabolic

noncomputable section

def J (w : ℂ) : ℂ := w + w⁻¹

def BoundedOrbit (z : ℂ) : Prop :=
  ∃ B : ℝ, ∀ n : ℕ, ‖(cquad (-2))^[n] z‖ ≤ B

def UnitAddress (w : ℂ) : Prop := ‖w‖ = 1

theorem pair_step {w v : ℂ} (h : w * v = 1) :
    cquad (-2) (w + v) = w^2 + v^2 := by
  norm_num [cquad]
  linear_combination 2 * h

theorem pair_iterate {w v : ℂ} (h : w * v = 1) (n : ℕ) :
    (cquad (-2))^[n] (w + v) = w^(2^n) + v^(2^n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iterate_succ_apply', ih]
    have hp : w^(2^n) * v^(2^n) = 1 := by rw [← mul_pow, h, one_pow]
    rw [pair_step hp]
    simp only [pow_succ (2 : ℕ) n, pow_mul]

theorem joukowski_step {w : ℂ} (hw : w ≠ 0) :
    cquad (-2) (J w) = J (w^2) := by
  unfold J
  rw [pair_step (mul_inv_cancel₀ hw), inv_pow]

theorem joukowski_iterate {w : ℂ} (hw : w ≠ 0) (n : ℕ) :
    (cquad (-2))^[n] (J w) = J (w^(2^n)) := by
  unfold J
  rw [pair_iterate (mul_inv_cancel₀ hw), inv_pow]

/-- All complex points, not just points in a selected symbolic carrier. -/
theorem reciprocal_pair_exists (z : ℂ) :
    ∃ w v : ℂ, w*v = 1 ∧ w+v = z := by
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (z^2-4) (n := 2) (by decide)
  refine ⟨(z+s)/2, (z-s)/2, ?_, by ring⟩
  linear_combination -(1/4 : ℂ) * hs

theorem reciprocal_eq_inv {w v : ℂ} (h : w*v = 1) : v = w⁻¹ := by
  have hw : w ≠ 0 := by intro hz; simp [hz] at h
  apply mul_left_cancel₀ hw
  rw [h, mul_inv_cancel₀ hw]

theorem joukowski_surjective : Surjective J := by
  intro z
  obtain ⟨w,v,h,hz⟩ := reciprocal_pair_exists z
  have hw : w ≠ 0 := by intro he; simp [he] at h
  exact ⟨w, by simpa only [J, ← reciprocal_eq_inv h] using hz⟩

/-- The only ambiguity for nonzero addresses is inversion. -/
theorem joukowski_fiber {w v : ℂ} (hw : w ≠ 0) (hv : v ≠ 0) :
    J w = J v ↔ w = v ∨ w = v⁻¹ := by
  constructor
  · intro he
    have hf : (w-v)*(w*v-1) = 0 := by
      calc
        (w-v)*(w*v-1) = w*v*(J w-J v) := by
          unfold J
          field_simp [hw,hv] <;> ring
        _ = 0 := by rw [he, sub_self, mul_zero]
    rcases mul_eq_zero.mp hf with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (reciprocal_eq_inv (by simpa [mul_comm] using sub_eq_zero.mp h))
  · rintro (rfl | rfl)
    · rfl
    · simp [J, add_comm]

theorem unit_nonzero {w : ℂ} (h : UnitAddress w) : w ≠ 0 := by
  intro he
  simp [UnitAddress, he] at h

theorem unit_inv {w : ℂ} (h : UnitAddress w) : UnitAddress w⁻¹ := by
  change ‖w‖ = 1 at h
  simp [UnitAddress, norm_inv, h]

theorem unit_square {w : ℂ} (h : UnitAddress w) : UnitAddress (w^2) := by
  change ‖w‖ = 1 at h
  simp [UnitAddress, norm_pow, h]

private theorem pair_norm_product {w v : ℂ} (h : w*v = 1) :
    ‖w‖ * ‖v‖ = 1 := by
  simpa only [norm_mul, norm_one] using congrArg (fun z : ℂ => ‖z‖) h

private theorem growth (r : ℝ) (hr : 1 < r) (n : ℕ) :
    r ≤ r^(2^n) ∧ 1+(n:ℝ)*(r-1) ≤ r^(2^n) := by
  induction n with
  | zero => simp; linarith
  | succ n ih =>
    rw [pow_succ (2 : ℕ) n, pow_mul]
    push_cast
    constructor <;> nlinarith [sq_nonneg (r^(2^n)-1)]

/-- Every non-unit reciprocal lift on the exterior side escapes, with
a lower bound valid at every iterate (not just a sampled orbit). -/
theorem exterior_lower_bound {w v : ℂ} (h : w*v=1) (hw : 1 < ‖w‖) (n : ℕ) :
    ‖w‖^(2^n) - 1 ≤ ‖(cquad (-2))^[n] (w+v)‖ := by
  have hp := pair_norm_product h
  have hv : ‖v‖ ≤ 1 := by
    nlinarith [mul_nonneg (show 0 ≤ ‖w‖-1 by linarith) (norm_nonneg v)]
  have hpow : ‖v‖^(2^n) ≤ 1 := by
    simpa using pow_le_pow_left₀ (norm_nonneg v) hv (2^n)
  have ht := norm_sub_le (w^(2^n)+v^(2^n)) (v^(2^n))
  rw [add_sub_cancel_right, norm_pow, norm_pow] at ht
  rw [pair_iterate h]
  linarith

theorem exterior_unbounded {w v : ℂ} (h : w*v=1) (hw : 1 < ‖w‖) :
    ¬ BoundedOrbit (w+v) := by
  rintro ⟨B,hB⟩
  obtain ⟨n,hn⟩ := exists_nat_gt (B / (‖w‖-1))
  have hmul := (div_lt_iff₀ (sub_pos.mpr hw)).mp hn
  have hg := (growth ‖w‖ hw n).2
  have hl := exterior_lower_bound h hw n
  linarith [hB n]

theorem unit_bounded {w : ℂ} (hw : UnitAddress w) :
    ∀ n : ℕ, ‖(cquad (-2))^[n] (J w)‖ ≤ 2 := by
  intro n
  rw [joukowski_iterate (unit_nonzero hw)]
  change ‖w‖ = 1 at hw
  have hp : ‖w^(2^n)‖ = 1 := by simp [norm_pow, hw]
  calc
    ‖J (w^(2^n))‖ ≤ ‖w^(2^n)‖ + ‖(w^(2^n))⁻¹‖ := norm_add_le _ _
    _ = 2 := by rw [norm_inv, hp]; norm_num

/-- An exact equivalence, with neither connectedness nor a priori bounds assumed. -/
theorem bounded_iff_unit_image (z : ℂ) :
    BoundedOrbit z ↔ ∃ w : ℂ, UnitAddress w ∧ J w = z := by
  constructor
  · intro hb
    obtain ⟨w,v,h,hz⟩ := reciprocal_pair_exists z
    have hp := pair_norm_product h
    have hw : ‖w‖ ≤ 1 := by
      by_contra! hgt
      exact exterior_unbounded h hgt (hz.symm ▸ hb)
    have hv : ‖v‖ ≤ 1 := by
      by_contra! hgt
      have h' : v*w=1 := by simpa [mul_comm] using h
      exact exterior_unbounded h' hgt ((add_comm v w ▸ hz).symm ▸ hb)
    have he : ‖w‖ = 1 := by
      have hm := mul_le_mul_of_nonneg_left hv (norm_nonneg w)
      linarith
    exact ⟨w,he,by simpa only [J, ← reciprocal_eq_inv h] using hz⟩
  · rintro ⟨w,hw,rfl⟩
    exact ⟨2, unit_bounded hw⟩

theorem unit_inv_eq_conj {w : ℂ} (hw : UnitAddress w) : w⁻¹ = conj w := by
  have h : w * conj w = 1 := by
    rw [Complex.mul_conj', hw]
    norm_num
  exact (reciprocal_eq_inv h).symm

theorem unit_image_realSegment {w : ℂ} (hw : UnitAddress w) :
    J w ∈ realSegment 2 := by
  rw [J, unit_inv_eq_conj hw, Complex.add_conj]
  refine ⟨2*w.re, ?_, rfl⟩
  have h := Complex.abs_re_le_norm w
  rw [hw, abs_le] at h
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

theorem realSegment_invariant {z : ℂ} (hz : z ∈ realSegment 2) :
    cquad (-2) z ∈ realSegment 2 := by
  obtain ⟨x,hx,rfl⟩ := hz
  refine ⟨x^2-2, ?_, ?_⟩
  · exact ⟨by nlinarith [sq_nonneg x], by nlinarith [sq_le_sq' hx.1 hx.2]⟩
  · norm_num [cquad, sub_eq_add_neg]

/-- The filled bounded-orbit set of the actual polynomial is exactly [-2,2]. -/
theorem bounded_iff_realSegment (z : ℂ) :
    BoundedOrbit z ↔ z ∈ realSegment 2 := by
  constructor
  · intro hb
    obtain ⟨w,hw,rfl⟩ := (bounded_iff_unit_image z).mp hb
    exact unit_image_realSegment hw
  · intro hz
    have hm : ∀ n : ℕ, (cquad (-2))^[n] z ∈ realSegment 2 := by
      intro n
      induction n with
      | zero => exact hz
      | succ n ih => rw [iterate_succ_apply']; exact realSegment_invariant ih
    refine ⟨2, fun n => ?_⟩
    obtain ⟨x,hx,he⟩ := hm n
    rw [← he, Complex.norm_real, Real.norm_eq_abs, abs_le]
    exact hx

/-- A fixed planar point may have no fixed boundary address.
Consequently no single-valued equivariant section exists, even without
continuity or any regularity assumption. -/
theorem no_equivariant_unit_section :
    ¬ ∃ s : ℂ → ℂ,
      (∀ z ∈ realSegment 2, UnitAddress (s z) ∧ J (s z) = z) ∧
      (∀ z ∈ realSegment 2, s (cquad (-2) z) = (s z)^2) := by
  rintro ⟨s,hsec,heq⟩
  have hm : (-1 : ℂ) ∈ realSegment 2 := by
    exact ⟨-1, ⟨by norm_num, by norm_num⟩, by norm_num⟩
  have hf : cquad (-2) (-1) = -1 := by norm_num [cquad]
  have h := heq (-1) hm
  rw [hf] at h
  obtain ⟨hu,hj⟩ := hsec (-1) hm
  have hfactor : s (-1) * (s (-1)-1) = 0 := by linear_combination -h
  have hone : s (-1) = 1 :=
    sub_eq_zero.mp ((mul_eq_zero.mp hfactor).resolve_left (unit_nonzero hu))
  rw [hone] at hj
  norm_num [J] at hj

/-- The algebraic address dynamics on the nonzero complex plane. -/
def D (w : ℂ) : ℂ := w^2

theorem doubling_iterate (w : ℂ) (n : ℕ) :
    D^[n] w = w^(2^n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iterate_succ_apply', ih]
    unfold D
    rw [pow_succ (2 : ℕ) n, pow_mul]

/-- A return of the actual planar point is precisely either an address
return or an address inversion. -/
theorem planar_return_iff {w : ℂ} (hw : w ≠ 0) (n : ℕ) :
    (cquad (-2))^[n] (J w) = J w ↔ w^(2^n) = w ∨ w^(2^n) = w⁻¹ := by
  rw [joukowski_iterate hw]
  exact joukowski_fiber (pow_ne_zero _ hw) hw

/-- Every primitive root of order 2^p+1 is a genuine planar point of
exact period p, and the first return exchanges its two distinct addresses.
The strict lower-period exclusion is by divisibility, not a finite sample. -/
theorem primitive_swap {p : ℕ} (hp : 0 < p) {w : ℂ}
    (hroot : IsPrimitiveRoot w (2^p+1)) :
    UnitAddress w ∧ w ≠ w⁻¹ ∧ w^(2^p) = w⁻¹ ∧
      (cquad (-2))^[p] (J w) = J w ∧
      (∀ k : ℕ, 0 < k → k < p → (cquad (-2))^[k] (J w) ≠ J w) := by
  have hu : UnitAddress w := hroot.norm'_eq_one (by omega)
  have hw := unit_nonzero hu
  have hswap : w^(2^p) = w⁻¹ := by
    apply mul_left_cancel₀ hw
    rw [mul_inv_cancel₀ hw, ← pow_succ' w (2^p)]
    exact hroot.pow_eq_one
  have hpowp : 1 < (2:ℕ)^p := by
    simpa only [pow_zero] using (pow_lt_pow_right₀ (by decide : 1 < (2:ℕ)) hp)
  have hne : w ≠ w⁻¹ := by
    intro he
    have htwo : w^2 = 1 := calc
      w^2 = w*w := pow_two w
      _ = w*w⁻¹ := congrArg (fun x : ℂ => w*x) he
      _ = 1 := mul_inv_cancel₀ hw
    have hle := Nat.le_of_dvd (by decide : 0 < 2)
      ((hroot.pow_eq_one_iff_dvd 2).mp htwo)
    omega
  refine ⟨hu,hne,hswap,(planar_return_iff hw p).mpr (Or.inr hswap),?_⟩
  intro k hk hkp hret
  have hpowlt : (2:ℕ)^k < 2^p := pow_lt_pow_right₀ (by decide) hkp
  have hpow1 : 1 < (2:ℕ)^k := by
    simpa only [pow_zero] using (pow_lt_pow_right₀ (by decide : 1 < (2:ℕ)) hk)
  rcases (planar_return_iff hw k).mp hret with hsame | hflip
  · have hsuc : 2^k-1+1 = 2^k := by omega
    have hone : w^(2^k-1) = 1 := by
      apply mul_left_cancel₀ hw
      rw [← pow_succ' w, hsuc, hsame, mul_one]
    have hle := Nat.le_of_dvd (by omega : 0 < 2^k-1)
      ((hroot.pow_eq_one_iff_dvd _).mp hone)
    omega
  · have hone : w^(2^k+1) = 1 := by
      rw [pow_succ', hflip, mul_inv_cancel₀ hw]
    have hle := Nat.le_of_dvd (by omega : 0 < 2^k+1)
      ((hroot.pow_eq_one_iff_dvd _).mp hone)
    omega

/-- Exact planar period and nontrivial two-sheet monodromy for every p>0. -/
theorem every_period_swap (p : ℕ) (hp : 0 < p) :
    ∃ w : ℂ, UnitAddress w ∧ w ≠ w⁻¹ ∧ w^(2^p) = w⁻¹ ∧
      minimalPeriod (cquad (-2)) (J w) = p := by
  let w : ℂ := Complex.exp (2 * Real.pi * Complex.I / ((2^p+1 : ℕ) : ℂ))
  have hroot : IsPrimitiveRoot w (2^p+1) :=
    Complex.isPrimitiveRoot_exp _ (by omega)
  obtain ⟨hu,hne,hswap,hret,hmin⟩ := primitive_swap hp hroot
  have hper : IsPeriodicPt (cquad (-2)) p (J w) := hret
  have hle := hper.minimalPeriod_le hp
  have hpos := hper.minimalPeriod_pos hp
  have he : minimalPeriod (cquad (-2)) (J w) = p := by
    by_contra hne'
    exact hmin _ hpos (lt_of_le_of_ne hle hne') (iterate_minimalPeriod _ _)
  exact ⟨w,hu,hne,hswap,he⟩

private theorem projected_period_dvd {w : ℂ} (hw : w ≠ 0) :
    minimalPeriod (cquad (-2)) (J w) ∣ minimalPeriod D w := by
  apply IsPeriodicPt.minimalPeriod_dvd
  change (cquad (-2))^[minimalPeriod D w] (J w) = J w
  rw [joukowski_iterate hw, ← doubling_iterate]
  exact congrArg J (iterate_minimalPeriod _ _)

/-- If the return swaps distinct addresses, the least address period is
exactly twice the least physical period; no shorter hidden clock exists. -/
theorem swapping_doubles_period {w : ℂ} (hw : w ≠ 0) (p : ℕ) (hp : 0 < p)
    (hbase : minimalPeriod (cquad (-2)) (J w) = p)
    (hswap : w^(2^p) = w⁻¹) (hne : w ≠ w⁻¹) :
    minimalPeriod D w = 2*p := by
  let q := minimalPeriod D w
  have hd : p ∣ q := by simpa only [hbase] using projected_period_dvd hw
  have h2 : IsPeriodicPt D (p+p) w := by
    change D^[p+p] w = w
    rw [doubling_iterate, pow_add (2 : ℕ), pow_mul, hswap]
    calc
      (w⁻¹)^(2^p) = (w^(2^p))⁻¹ := by rw [inv_pow]
      _ = w := by rw [hswap, inv_inv]
  have hqpos : 0 < q := h2.minimalPeriod_pos (by omega)
  have hqle : q ≤ p+p := h2.minimalPeriod_le (by omega)
  have hqne : q ≠ p := by
    intro he
    have hret : D^[p] w = w := by
      rw [← he]
      exact iterate_minimalPeriod _ _
    rw [doubling_iterate, hswap] at hret
    exact hne hret.symm
  obtain ⟨k,hk⟩ := hd
  have hkpos : 0 < k := by
    by_contra! hn
    have hz : k=0 := by omega
    simp [hz] at hk
    omega
  have hkne : k ≠ 1 := by
    intro he
    apply hqne
    simpa [he] using hk
  have hkle : k ≤ 2 := by
    by_contra! hn
    have hm := Nat.mul_le_mul_left p (show 3 ≤ k by omega)
    omega
  have hk2 : k=2 := by omega
  rw [hk2] at hk
  omega

/-- In general the address clock is either the physical clock or exactly
twice it. The assumption is actual periodicity, not an abstract clock. -/
theorem lift_period_dichotomy {w : ℂ} (hw : w ≠ 0)
    (hp : 0 < minimalPeriod (cquad (-2)) (J w)) :
    minimalPeriod D w = minimalPeriod (cquad (-2)) (J w) ∨
      minimalPeriod D w = 2 * minimalPeriod (cquad (-2)) (J w) := by
  let p := minimalPeriod (cquad (-2)) (J w)
  have hret : (cquad (-2))^[p] (J w) = J w := iterate_minimalPeriod _ _
  have hsame (h : w^(2^p) = w) : minimalPeriod D w = p := by
    have hper : IsPeriodicPt D p w := by
      change D^[p] w = w
      rw [doubling_iterate, h]
    exact Nat.dvd_antisymm hper.minimalPeriod_dvd (projected_period_dvd hw)
  rcases (planar_return_iff hw p).mp hret with h | h
  · exact Or.inl (hsame h)
  · by_cases he : w = w⁻¹
    · exact Or.inl (hsame (h.trans he.symm))
    · exact Or.inr (swapping_doubles_period hw p hp rfl h he)

/-- Sharpness of the factor two, at every positive physical period. -/
theorem every_period_doubling (p : ℕ) (hp : 0 < p) :
    ∃ w : ℂ, UnitAddress w ∧ minimalPeriod (cquad (-2)) (J w) = p ∧
      minimalPeriod D w = 2*p := by
  obtain ⟨w,hu,hne,hswap,hbase⟩ := every_period_swap p hp
  exact ⟨w,hu,hbase,swapping_doubles_period (unit_nonzero hu) p hp hbase hswap hne⟩

/-- No finite retiming can repair a global single-valued equivariant
selection on this actual filled set. For each p choose its own p-cycle. -/
theorem no_retimed_equivariant_unit_section (p : ℕ) (hp : 0 < p) :
    ¬ ∃ s : ℂ → ℂ,
      (∀ z ∈ realSegment 2, UnitAddress (s z) ∧ J (s z) = z) ∧
      (∀ z ∈ realSegment 2, s ((cquad (-2))^[p] z) = (s z)^(2^p)) := by
  rintro ⟨s,hsec,heq⟩
  obtain ⟨w,hu,hne,hswap,hbase⟩ := every_period_swap p hp
  have hm := unit_image_realSegment hu
  have hret : (cquad (-2))^[p] (J w) = J w := by
    rw [← hbase]
    exact iterate_minimalPeriod _ _
  obtain ⟨hsu,hsj⟩ := hsec (J w) hm
  have h := heq (J w) hm
  rw [hret] at h
  rcases (joukowski_fiber (unit_nonzero hsu) (unit_nonzero hu)).mp hsj with he | he
  · rw [he, hswap] at h
    exact hne h
  · rw [he] at h
    have hflip : (w⁻¹)^(2^p) = w := by
      calc
        (w⁻¹)^(2^p) = (w^(2^p))⁻¹ := by rw [inv_pow]
        _ = w := by rw [hswap, inv_inv]
    rw [hflip] at h
    exact hne h.symm

end
end LoopsChebyshev

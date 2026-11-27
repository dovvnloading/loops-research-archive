import GlobalTipCertificates
import GlobalTipWindow

/-!
# Global uniqueness of the ten actual finite primitive tips

The interval trees exhaust all possible real parameters: a negative third
return forces the parameter into (-2,0), and the kernel-checked trees cover
that entire range. The selected root is then constructed by the existing
real intermediate-value theorem and its derivative certificate.

The geometric statement uses the actual forward-invariant critical interval
and the phase signs of the real quadratic map. No seed or collision equation
occurs in the definition of that restrictive-window hypothesis.
-/

namespace LoopsGlobalTip

open Set
open LoopsFormal.Period27 LoopsFormal.DepthThree
open LoopsDepthThreeReal LoopsRealPeriod27

/-- Exact retained intervals, in units of `1 / tipScale`. -/
def selectedSeed : Nat → Bounds
  | 3 => seed3
  | 4 => seed4
  | 5 => seed5
  | 6 => seed6
  | 7 => seed7
  | 8 => seed8
  | 9 => seed9
  | 10 => seed10
  | 11 => seed11
  | 12 => seed12
  | _ => seed3

/-- Complete closed parameter covers for the ten finite periods. -/
def selectedCover : Nat → CoverTree
  | 3 => cover3
  | 4 => cover4
  | 5 => cover5
  | 6 => cover6
  | 7 => cover7
  | 8 => cover8
  | 9 => cover9
  | 10 => cover10
  | 11 => cover11
  | 12 => cover12
  | _ => cover3

/-- The actual finite certificates include global exclusion, real-root
existence/uniqueness, the complete itinerary, and interval invariance. -/
theorem finite_tip_certificates (p : Nat) (hp : 3 ≤ p) (hp' : p ≤ 12) :
    coverCheck tipScale p ⟨-2 * tipScale, 0⟩ (selectedSeed p) (selectedCover p) = true ∧
    RootCertificate tipScale p (selectedSeed p) ∧
    signBoxCheck tipScale p (selectedSeed p) = true ∧
    0 < (addBounds (orbitBound tipScale p (selectedSeed p) p)
      (orbitBound tipScale p (selectedSeed p) (2*p))).lo := by
  have hcases : p = 3 ∨ p = 4 ∨ p = 5 ∨ p = 6 ∨ p = 7 ∨ p = 8 ∨ p = 9 ∨ p = 10 ∨ p = 11 ∨ p = 12 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨cover3_checked, seed3_root, seed3_signs, seed3_invariant⟩
  · exact ⟨cover4_checked, seed4_root, seed4_signs, seed4_invariant⟩
  · exact ⟨cover5_checked, seed5_root, seed5_signs, seed5_invariant⟩
  · exact ⟨cover6_checked, seed6_root, seed6_signs, seed6_invariant⟩
  · exact ⟨cover7_checked, seed7_root, seed7_signs, seed7_invariant⟩
  · exact ⟨cover8_checked, seed8_root, seed8_signs, seed8_invariant⟩
  · exact ⟨cover9_checked, seed9_root, seed9_signs, seed9_invariant⟩
  · exact ⟨cover10_checked, seed10_root, seed10_signs, seed10_invariant⟩
  · exact ⟨cover11_checked, seed11_root, seed11_signs, seed11_invariant⟩
  · exact ⟨cover12_checked, seed12_root, seed12_signs, seed12_invariant⟩

noncomputable section

private theorem parameter_box_enclosed {c : ℝ} (hc : c ∈ Icc (-2) 0) :
    RealEnclosed tipScale ⟨-2 * tipScale, 0⟩ c := by
  have hS : (0 : ℝ) < (tipScale : ℝ) := by exact_mod_cast tipScale_pos
  constructor
  · push_cast
    nlinarith [hc.1]
  · change c * (tipScale : ℝ) ≤ 0
    exact mul_nonpos_of_nonpos_of_nonneg hc.2 hS.le

/-- Every actual real parameter with the selected complete critical
itinerary and collision relation lies in the retained interval. This
has no a priori bound or local chart assumption on the parameter. -/
theorem global_tip_enclosed (p : Nat) (hp : 3 ≤ p) (hp' : p ≤ 12)
    (c : ℝ) (hroot : collisionPolynomial p c = 0) (hs : HasSigns p c) :
    RealEnclosed tipScale (selectedSeed p) c := by
  have hcert := finite_tip_certificates p hp hp'
  have hbounds := hasSigns_parameter_bounds (by omega : 0 < p) hs
  exact coverCheck_sound tipScale_pos (by omega) hcert.1
    (parameter_box_enclosed hbounds) hroot hs

/-- Exactly one real parameter has the selected critical itinerary and
the actual collision x_(6p)+x_(3p)=0, for each p=3,...,12. Uniqueness
holds on the whole real line, not only on the original seed interval. -/
theorem exists_unique_global_signed_tip (p : Nat) (hp : 3 ≤ p) (hp' : p ≤ 12) :
    ∃! c : ℝ, collisionPolynomial p c = 0 ∧ HasSigns p c := by
  have hcert := finite_tip_certificates p hp hp'
  obtain ⟨c, hc, _⟩ := certified_unique_real_root hcert.2.1
  have hcI : c ∈ Icc (((selectedSeed p).lo : ℝ) / (tipScale : ℝ))
      (((selectedSeed p).hi : ℝ) / (tipScale : ℝ)) := ⟨hc.1.le, hc.2.1.le⟩
  have henc := (realEnclosed_iff tipScale_pos (selectedSeed p) c).mpr hcI
  have hs := signBoxCheck_sound tipScale_pos hcert.2.2.1 henc
  refine ⟨c, ⟨hc.2.2, hs⟩, ?_⟩
  intro y hy
  have hyenc := global_tip_enclosed p hp hp' y hy.1 hy.2
  exact (certified_collision_injective hcert.2.1)
    ((realEnclosed_iff tipScale_pos (selectedSeed p) y).mp hyenc)
    hcI (hy.1.trans hc.2.2.symm)

/-- Every globally selected tip is a simple zero of the genuine real
critical-relation polynomial. -/
theorem global_tip_simple (p : Nat) (hp : 3 ≤ p) (hp' : p ≤ 12)
    (c : ℝ) (hroot : collisionPolynomial p c = 0) (hs : HasSigns p c) :
    deriv (collisionPolynomial p) c ≠ 0 := by
  rw [(collision_hasDerivAt p c).deriv]
  exact certified_collision_derivative_ne_zero
    (finite_tip_certificates p hp hp').2.1 (global_tip_enclosed p hp hp' c hroot hs)

private theorem seed_return_sum_positive (p : Nat) (hp : 3 ≤ p) (hp' : p ≤ 12)
    {c : ℝ} (hc : RealEnclosed tipScale (selectedSeed p) c) :
    0 < polynomial p c + polynomial (2*p) c := by
  have hcert := (finite_tip_certificates p hp hp').2.2.2
  have hx := (trace_enclosed tipScale_pos hc p p le_rfl).1
  have hy := (trace_enclosed tipScale_pos hc (2*p) (2*p) le_rfl).1
  have hb := real_add_enclosed hx hy
  have hlo : (0 : ℝ) < ((addBounds
      (orbitBound tipScale p (selectedSeed p) p)
      (orbitBound tipScale p (selectedSeed p) (2*p))).lo : ℝ) := by
    exact_mod_cast hcert
  have hS : (0 : ℝ) < (tipScale : ℝ) := by exact_mod_cast tipScale_pos
  exact (mul_pos_iff_of_pos_right hS).mp (hlo.trans_le hb.1)

/-- The selected global root really supplies an invariant critical
interval with strict intermediate phases. This geometric premise is
derived from the certificates and is not assumed of the constructed root. -/
theorem global_tip_restrictive (p : Nat) (hp : 3 ≤ p) (hp' : p ≤ 12)
    (c : ℝ) (hroot : collisionPolynomial p c = 0) (hs : HasSigns p c) :
    RestrictiveWindow p c := by
  apply hasSigns_restrictiveWindow (by omega : 2 ≤ p) hs
  exact (seed_return_sum_positive p hp hp'
    (global_tip_enclosed p hp hp' c hroot hs)).le

/-- Global uniqueness on the entire real restrictive-window domain,
selected by its six return signs. The domain is defined by actual
interval dynamics and contains no equation or parameter locator. -/
theorem exists_unique_restrictive_tip (p : Nat) (hp : 3 ≤ p) (hp' : p ≤ 12) :
    ∃! c : ℝ, RestrictiveWindow p c ∧ ReturnSigns p c ∧
      collisionPolynomial p c = 0 := by
  obtain ⟨c, hc, hu⟩ := exists_unique_global_signed_tip p hp hp'
  refine ⟨c, ⟨global_tip_restrictive p hp hp' c hc.1 hc.2,
    hasSigns_returnSigns (by omega : 0 < p) hc.2, hc.1⟩, ?_⟩
  intro y hy
  exact hu y ⟨hy.2.2, restrictiveWindow_hasSigns (by omega : 2 ≤ p) hy.1 hy.2.1⟩

end
end LoopsGlobalTip

import GlobalSignedRelationStability
import GlobalWindowParameterSecant
import GlobalActualWindow

/-!
# Uniqueness of the actual signed tip in the complete restrictive family

The finite-difference estimate applies to the literal normalized return
maps.  Thus the narrow coefficient isolator contains one physical
six-versus-three signed collision, rather than merely one model root.
-/

namespace GlobalActualSignedUniqueness

open Set Function NearTwoShooting LimitingCrestQuadraticReturn
open LoopsLimitingCrestParameter GlobalRestrictiveWindow
open GlobalWindowSignedChart GlobalWindowInverseShape GlobalWindowParameterSecant
open GlobalSignedRelationStability NearTwoTip GlobalActualWindow

noncomputable section

/-- The actual normalized signed relation has a uniform oriented secant
margin throughout the narrow coefficient interval. -/
theorem actual_signed_secant {p : ℕ} (hp : 17≤p) {c a : ℝ}
    (hc : PositiveRestrictiveReturn c p) (ha : PositiveRestrictiveReturn a p)
    (hkc : kappa p c∈parameterInterval) (hka : kappa p a∈parameterInterval)
    (horder : kappa p c<kappa p a) :
    5*(kappa p a-kappa p c)<
      signedRelation (realReturn a p)-signedRelation (realReturn c p) := by
  have hpone : (1 : ℝ)≤p := by exact_mod_cast (show 1≤p by omega)
  have hq : scale p≤(p : ℝ)*scale p := by
    have hm := mul_le_mul_of_nonneg_right hpone (scale_pos p).le
    simpa only [one_mul] using hm
  apply signed_relation_secant_gt_five hkc hka horder
    (t := (p : ℝ)*scale p)
    (mul_nonneg (Nat.cast_nonneg p) (scale_pos p).le) ?_
    (realReturn_mapsTo hc) (realReturn_mapsTo ha)
  · have h := horizon_scale_small hp
    nlinarith only [h]
  · intro z hz
    have he := realReturn_error hp ha hz
    change |realReturn a p z-(1-kappa p a*z^2)|≤22*((p : ℝ)*scale p)
    exact he.trans (mul_le_mul_of_nonneg_left hq (by norm_num))
  · intro z hz
    simpa only [Q,mul_assoc] using parameter_error_lipschitz hp hc ha hz
  · intro z hz w hw
    simpa only [Q,mul_assoc] using spatial_error_lipschitz hp hc hz hw

/-- The normalized functional is exactly the literal polynomial
collision divided by its positive return scale. -/
theorem signed_relation_identity {c : ℝ} {p : ℕ}
    (hd : criticalValue c p≠0) :
    signedRelation (realReturn c p)=
      (criticalValue c (6*p)+criticalValue c (3*p))/criticalValue c p := by
  unfold signedRelation
  rw [realReturn_iterate_zero hd 6,realReturn_iterate_zero hd 3]
  ring

/-- Among all physical restrictive parameters in the coefficient
isolator, the literal signed collision has at most one solution. -/
theorem physical_signed_collision_unique {p : ℕ} (hp : 17≤p) {c a : ℝ}
    (hc : PositiveRestrictiveReturn c p) (ha : PositiveRestrictiveReturn a p)
    (hkc : kappa p c∈parameterInterval) (hka : kappa p a∈parameterInterval)
    (hczero : criticalValue c (6*p)+criticalValue c (3*p)=0)
    (hazero : criticalValue a (6*p)+criticalValue a (3*p)=0) : c=a := by
  have hcsigned : signedRelation (realReturn c p)=0 := by
    rw [signed_relation_identity hc.return_pos.ne',hczero,zero_div]
  have hasigned : signedRelation (realReturn a p)=0 := by
    rw [signed_relation_identity ha.return_pos.ne',hazero,zero_div]
  have hk : kappa p c=kappa p a := by
    rcases lt_trichotomy (kappa p c) (kappa p a) with hlt | heq | hgt
    · have hs := actual_signed_secant hp hc ha hkc hka hlt
      rw [hcsigned,hasigned] at hs
      linarith only [hs,hlt]
    · exact heq
    · have hs := actual_signed_secant hp ha hc hka hkc hgt
      rw [hcsigned,hasigned] at hs
      linarith only [hs,hgt]
  have hreturn := return_scale_kappa_lipschitz hp hc ha
  rw [hk,sub_self,abs_zero,mul_zero] at hreturn
  have hd : criticalValue c p=criticalValue a p := by
    exact sub_eq_zero.mp (abs_eq_zero.mp
      (le_antisymm hreturn (abs_nonneg (criticalValue c p-criticalValue a p))))
  have hparameter := parameter_lipschitz hp hc ha
  rw [hd,sub_self,abs_zero,mul_zero] at hparameter
  exact sub_eq_zero.mp (abs_eq_zero.mp
    (le_antisymm hparameter (abs_nonneg (c-a))))

/-- The archived actual-tip existence theorem now has uniqueness in the
same literal quadratic family. -/
theorem actual_tip_unique {p : ℕ} (hp : 17≤p) {c a : ℝ}
    (hc : ActualTip p c) (ha : ActualTip p a) : c=a := by
  exact physical_signed_collision_unique hp
    (actual_tip_restrictive_return hp hc) (actual_tip_restrictive_return hp ha)
    hc.2.2.2.1 ha.2.2.2.1 hc.2.2.2.2.1 ha.2.2.2.2.1

theorem exists_unique_actual_tip (p : ℕ) (hp : 17≤p) : ∃! c : ℝ, ActualTip p c := by
  obtain ⟨c,hc⟩ := exists_actual_tip p hp
  exact ⟨c,hc,fun a ha => actual_tip_unique hp ha hc⟩

/-- Existence and uniqueness hold among the complete physical
restrictive class, without assuming the archived tip's orbit bounds or
its smaller return-scale bound. -/
theorem exists_unique_physical_signed_collision (p : ℕ) (hp : 17≤p) :
    ∃! c : ℝ, PositiveRestrictiveReturn c p ∧
      kappa p c∈parameterInterval ∧
      criticalValue c (6*p)+criticalValue c (3*p)=0 := by
  obtain ⟨c,hc⟩ := exists_actual_tip p hp
  have hphysical := actual_tip_restrictive_return hp hc
  refine ⟨c,⟨hphysical,hc.2.2.2.1,hc.2.2.2.2.1⟩,?_⟩
  intro a ha
  exact physical_signed_collision_unique hp ha.1 hphysical ha.2.1 hc.2.2.2.1
    ha.2.2 hc.2.2.2.2.1

end
end GlobalActualSignedUniqueness

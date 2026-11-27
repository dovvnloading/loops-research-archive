import ActualCrestEndpoint
import ActualCrestSupport

/-!
# Strict radial order for the actual terminal coordinate

The actual third return is injective along the selected crossing curve.
This follows from complete-support injectivity and exclusion of the even
polynomial's antipodal collision at the positive imaginary first images.
Continuity then forces radial order. The first-exit construction orients
that order without assuming a radial derivative estimate.
-/

namespace ActualCrestRadialOrder

open Set Function Filter
open scoped Topology
open NearTwoTip NearTwoShooting LimitingCrestQuadraticReturn LimitingCrest
open LoopsLimitingCrestParameter ActualCrestCrossingWindow ActualCrestEndpoint
open QuadraticCrestDividedDifference

noncomputable section

private theorem family_point_mem {p : ℕ} {c : ℝ} (F : Family p c) (s : Radius) :
    F.point s ∈ initialDisk := by
  change ‖F.point s+(3/4 : ℂ)‖ ≤ 133/2000
  rw [F.point_radius]
  exact s.property.2

/-- No two distinct radii have the same actual third-return coordinate.
This uses exact collisions of the full polynomial, not an approximation
to its derivative or an assumed radial order. -/
theorem actual_terminal_injective (c : ℕ → ℝ)
    (hc : ∀ n, ActualTip (n+17) (c n))
    (F : ∀ n, Family (n+17) (c n)) :
    ∀ᶠ n in atTop,
      InjOn (terminal (F n)) (Icc (1/16 : ℝ) (133/2000)) := by
  filter_upwards [ActualCrestSupport.actual_support_bounds c hc,
    ActualCrestSupport.actual_complete_support_injective c hc] with n hbound hinj
  intro s hs t ht he
  let ss : Radius := ⟨s,hs⟩
  let tt : Radius := ⟨t,ht⟩
  let H := normalizedReturn (c n) (n+17)
  have hsD := family_point_mem (F n) ss
  have htD := family_point_mem (F n) tt
  have hthree : (H^[3]) ((F n).point ss) = (H^[3]) ((F n).point tt) := by
    apply Complex.ext
    · simpa only [terminal,point,radiusProjection_eq hs,radiusProjection_eq ht] using he
    · change (((normalizedReturn (c n) (n+17))^[3]) ((F n).point ss)).im =
        (((normalizedReturn (c n) (n+17))^[3]) ((F n).point tt)).im
      rw [(F n).third_real (by omega) ss,(F n).third_real (by omega) tt]
  have htwo : (H^[2]) ((F n).point ss) = (H^[2]) ((F n).point tt) :=
    hinj.2.1 ⟨(F n).point ss,hsD,rfl⟩ ⟨(F n).point tt,htD,rfl⟩ hthree
  have hband := parameter_band (by omega : 17 ≤ n+17) (hc n).1
  have hsmall : criticalValue (c n) (n+17) ≤ 12/(4 : ℝ)^(n+17) := by
    simpa only [scale,one_div_pow,mul_one_div] using (hc n).2.2.1
  have hsNorm : ‖H ((F n).point ss)‖ ≤ 23/20 := by
    simpa only [iterate_one] using (hbound _ hsD).1 1 (by norm_num)
  have htNorm : ‖H ((F n).point tt)‖ ≤ 23/20 := by
    simpa only [iterate_one] using (hbound _ htD).1 1 (by norm_num)
  have hcollision := (normalized_return_collision_iff (c n) (n+17) (by omega)
    ⟨hband.1,by linarith [hband.2]⟩ (hc n).2.1 hsmall (hc n).2.2.2.1
    hsNorm htNorm).mp htwo
  have hone : H ((F n).point ss) = H ((F n).point tt) := by
    rcases hcollision with h | h
    · exact h
    · have him := congrArg Complex.im h
      simp only [Complex.neg_im] at him
      have hps := (F n).positive ss
      have hpt := (F n).positive tt
      change 0 < (H ((F n).point ss)).im at hps
      change 0 < (H ((F n).point tt)).im at hpt
      exact (by linarith : False).elim
  have hpoints := hinj.1 hsD htD hone
  exact congrArg Subtype.val ((F n).point_injective hpoints)

/-- At all sufficiently large periods, the literal terminal coordinate
is strictly decreasing on the entire extended crossing window. -/
theorem actual_terminal_strictAnti (c : ℕ → ℝ)
    (hc : ∀ n, ActualTip (n+17) (c n))
    (F : ∀ n, Family (n+17) (c n)) :
    ∀ᶠ n in atTop,
      StrictAntiOn (terminal (F n)) (Icc (1/16 : ℝ) (133/2000)) := by
  obtain ⟨k₀,⟨hk₀,hroot⟩,_⟩ := exists_unique_limiting_parameter
  obtain ⟨r,hr,hterm,radii,hmem,hlimit,hcollars⟩ :=
    actual_initial_collars_converge hk₀ hroot c hc F
  filter_upwards [actual_terminal_injective c hc F,hcollars] with n hinj hcollar
  rcases ContinuousOn.strictMonoOn_of_injOn_Icc'
    (by norm_num : (1/16 : ℝ) ≤ 133/2000)
    (terminal_continuous (F n)).continuousOn hinj with hmono | hanti
  · have hm := hmono
      (show (1/16 : ℝ) ∈ Icc (1/16 : ℝ) (133/2000) by constructor <;> norm_num)
      ⟨hcollar.1.1.le,hcollar.1.2.le⟩ hcollar.1.1
    have ha := hcollar.2.2.1 (1/16) ⟨le_rfl,hcollar.1.1⟩
    rw [hcollar.2.1] at hm
    exact (by linarith : False).elim
  · exact hanti

/-- The first exit is the only terminal crossing anywhere in the window;
the retained side is exactly the interval below that radius. -/
theorem actual_unique_terminal_collars (c : ℕ → ℝ)
    (hc : ∀ n, ActualTip (n+17) (c n))
    (F : ∀ n, Family (n+17) (c n)) :
    ∀ᶠ n in atTop, ∃ r : ℝ, InitialCollar (F n) r ∧
      (∀ s ∈ Icc (1/16 : ℝ) (133/2000), terminal (F n) s = -1 ↔ s = r) ∧
      (∀ s ∈ Icc (1/16 : ℝ) (133/2000), -1 < terminal (F n) s ↔ s < r) := by
  obtain ⟨k₀,⟨hk₀,hroot⟩,_⟩ := exists_unique_limiting_parameter
  obtain ⟨r,hr,hterm,radii,hmem,hlimit,hcollars⟩ :=
    actual_initial_collars_converge hk₀ hroot c hc F
  filter_upwards [actual_terminal_strictAnti c hc F,hcollars] with n hanti hcollar
  have hrad : radii n ∈ Icc (1/16 : ℝ) (133/2000) :=
    ⟨hcollar.1.1.le,hcollar.1.2.le⟩
  refine ⟨radii n,hcollar,?_,?_⟩
  · intro s hs
    constructor
    · intro he
      exact hanti.injOn hs hrad (he.trans hcollar.2.1.symm)
    · rintro rfl
      exact hcollar.2.1
  · intro s hs
    constructor
    · intro hpos
      by_contra h
      have hle : radii n ≤ s := le_of_not_gt h
      have hm := hanti.antitoneOn hrad hs hle
      rw [hcollar.2.1] at hm
      linarith
    · intro hlt
      have hm := hanti hs hrad hlt
      rwa [hcollar.2.1] at hm

end
end ActualCrestRadialOrder

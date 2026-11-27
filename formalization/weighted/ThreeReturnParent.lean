import ThreeReturnPhysical

/-!
# A proper ambient p-return domain for the selected three-return

The three phases are put inside an actual proper degree-two p-return
component.  Inclusion follows by exhausting its exact signed fibers; no
unquantified shrinking of the three-return collar is used.  The ambient
component is selected canonically from the same complete polynomial.
-/

namespace ThreeReturnParent

open Set Function Metric Topology
open LimitingCrestQuadraticReturn LoopsQuadraticCylinderCensus
open ThreeReturnDomain ThreeReturnDegree ThreeReturnCollar ThreeReturnPhysical
open ThreeReturnEstimates NearTwoTip NearTwoShooting LimitingCrest
open QuadraticCrestDividedDifference

noncomputable section

def parentSource (c : ℝ) (p : ℕ) : Set ℂ :=
  connectedComponentIn (normalizedReturn c p ⁻¹' ball 0 (23/20)) 0

def parentMap (c : ℝ) (p : ℕ) : parentSource c p → ball (0 : ℂ) (23/20) :=
  fun z => ⟨normalizedReturn c p z,
    connectedComponentIn_subset (normalizedReturn c p ⁻¹' ball 0 (23/20)) 0 z.property⟩

def physicalParentSource (c : ℝ) (p : ℕ) : Set ℂ :=
  (fun z : ℂ => (criticalValue c p : ℂ) * z) '' parentSource c p

theorem quadratic_iterate_zero (c : ℝ) (n : ℕ) :
    ((quadraticMap c)^[n]) 0 = (criticalValue c n : ℂ) := by
  induction n with
  | zero => simp [criticalValue]
  | succ n ih =>
    rw [iterate_succ_apply', ih]
    simp only [quadraticMap, criticalValue, iterate_succ_apply',
      Complex.ofReal_add, Complex.ofReal_pow]

theorem normalized_return_zero (c : ℝ) (p : ℕ) (hd : criticalValue c p ≠ 0) :
    normalizedReturn c p 0 = 1 := by
  have hdC : (criticalValue c p : ℂ) ≠ 0 := by exact_mod_cast hd
  simp only [normalizedReturn, mul_zero, quadratic_iterate_zero, div_self hdC]

theorem parent_source_symmetric (c : ℝ) (p : ℕ) (hp : 0 < p)
    (hd : criticalValue c p ≠ 0) :
    ∀ z ∈ parentSource c p, -z ∈ parentSource c p := by
  have h0 : (0 : ℂ) ∈ parentSource c p := mem_connectedComponentIn (by
    norm_num [normalized_return_zero c p hd])
  have hconn : IsPreconnected ((fun z : ℂ => -z) '' parentSource c p) :=
    isPreconnected_connectedComponentIn.image _ continuous_neg.continuousOn
  have hhit : (0 : ℂ) ∈ (fun z : ℂ => -z) '' parentSource c p := ⟨0, h0, neg_zero⟩
  have hsub : (fun z : ℂ => -z) '' parentSource c p ⊆
      normalizedReturn c p ⁻¹' ball 0 (23/20) := by
    rintro _ ⟨z, hz, rfl⟩
    change normalizedReturn c p (-z) ∈ ball 0 (23/20)
    rw [normalized_return_even c p hp]
    exact connectedComponentIn_subset (normalizedReturn c p ⁻¹' ball 0 (23/20)) 0 hz
  have h := hconn.subset_connectedComponentIn hhit hsub
  intro z hz
  exact h ⟨z, hz, rfl⟩

structure ParentRestriction (c : ℝ) (p : ℕ) : Prop where
  zero_mem : (0 : ℂ) ∈ parentSource c p
  isOpen_source : IsOpen (parentSource c p)
  isConnected_source : IsConnected (parentSource c p)
  compact_closure : IsCompact (closure (parentSource c p))
  closure_inside : closure (parentSource c p) ⊆ ball 0 (23/20)
  image_eq : normalizedReturn c p '' parentSource c p = ball 0 (23/20)
  proper : IsProperMap (parentMap c p)
  fiber_card : ∀ y ∈ ball (0 : ℂ) (23/20),
    {z : ℂ | z ∈ parentSource c p ∧ normalizedReturn c p z = y}.ncard =
      if y = 1 then 1 else 2
  target_closure_subset : closedBall (0 : ℂ) (1/6) ⊆ parentSource c p
  phase_subset : ∀ n : ℕ, n ≤ 2 →
    (normalizedReturn c p)^[n] '' source c p ⊆ parentSource c p
  physical_phase_subset : ∀ n : ℕ, n ≤ 2 →
    ((quadraticMap c)^[n*p]) '' physicalSource c p ⊆ physicalParentSource c p

/-- The ambient domain and all phase inclusions are constructed from
complete-polynomial estimates at the fixed control radius. -/
theorem parent_restriction_of_bounds (c : ℝ) (p : ℕ) (hp : 0 < p)
    (hc : CanonicalCollar c p)
    (hbarrier : ∀ z : ℂ, ‖z‖ = 23/20 → 23/20 < ‖normalizedReturn c p z‖)
    (hcollision : ∀ {z w : ℂ}, ‖z‖ ≤ 23/20 → ‖w‖ ≤ 23/20 →
      (normalizedReturn c p z = normalizedReturn c p w ↔ z = w ∨ z = -w))
    (hphase : ∀ z : ℂ, ‖z‖ ≤ 1/6 →
      ‖normalizedReturn c p z‖ < 23/20 ∧
        ‖normalizedReturn c p (normalizedReturn c p z)‖ < 23/20) :
    ParentRestriction c p := by
  let F := normalizedReturn c p
  have hd := hc.scale_pos.ne'
  have hproper := normalized_return_proper c p hd
  have hopen := normalized_return_open c p hd
  have hzero : ‖F 0‖ < 23/20 := by
    norm_num [F, normalized_return_zero c p hd]
  have h0 : (0 : ℂ) ∈ parentSource c p := mem_connectedComponentIn (by simpa using hzero)
  obtain ⟨hinside, hcompact⟩ := component_closure_inside_barrier
    F hproper.continuous (23/20) (23/20) (by norm_num) hzero hbarrier
  change closure (parentSource c p) ⊆ ball 0 (23/20) at hinside
  have hnorm {z : ℂ} (hz : z ∈ parentSource c p) : ‖z‖ < 23/20 := by
    simpa using hinside (subset_closure hz)
  have honto : F '' parentSource c p = ball 0 (23/20) :=
    localized_component_image F (F ⁻¹' ball 0 (23/20)) (ball 0 (23/20))
      hopen hproper.isClosedMap (isOpen_ball.preimage hproper.continuous)
      (convex_ball (0 : ℂ) (23/20)).isPreconnected
      (fun _ hz => hz) (fun _ hz => hz.2) 0 (by simpa using hzero)
  have hsurj : SurjOn F (parentSource c p) (ball 0 (23/20)) := by
    simp only [SurjOn, honto, Subset.refl]
  have hsym := parent_source_symmetric c p hp hd
  have hexhaust {z : ℂ} (hz : ‖z‖ ≤ 23/20) (hfz : ‖F z‖ < 23/20) :
      z ∈ parentSource c p := by
    obtain ⟨w, hw, hwe⟩ := hsurj (show F z ∈ ball (0 : ℂ) (23/20) by simpa using hfz)
    rcases (hcollision (hnorm hw).le hz).mp hwe with he | he
    · exact he ▸ hw
    · have hzw : z = -w := by rw [he, neg_neg]
      rw [hzw]
      exact hsym w hw
  have hphases : ∀ n : ℕ, n ≤ 2 → F^[n] '' source c p ⊆ parentSource c p := by
    intro n hn
    rintro _ ⟨z, hz, rfl⟩
    have hz0 : ‖z‖ < 3/20 := by simpa using hc.closure_inside (subset_closure hz)
    have hzd : ‖z‖ ≤ 1/6 := by linarith
    have hz1 := (hphase z hzd).1
    have hz2 := (hphase z hzd).2
    have hz3 : ‖F (F (F z))‖ < 1/6 := by
      simpa [threeReturn, F, iterate_succ_apply'] using
        connectedComponentIn_subset (threeReturn c p ⁻¹' ball 0 (1/6)) 0 hz
    interval_cases n
    · exact hexhaust (by simpa using (show ‖z‖ ≤ 23/20 by linarith)) hz1
    · exact hexhaust hz1.le hz2
    · apply hexhaust hz2.le
      change ‖F (F (F z))‖ < 23/20
      linarith
  refine ⟨h0, (isOpen_ball.preimage hproper.continuous).connectedComponentIn,
    ⟨⟨0, h0⟩, isPreconnected_connectedComponentIn⟩,
    hcompact, hinside, honto,
    component_proper F hproper (ball 0 (23/20)) 0 isOpen_ball, ?_, ?_, hphases, ?_⟩
  · intro y hy
    have hcard := fiber_ncard F (parentSource c p) (ball 0 (23/20)) h0
      (fun hz hw => hcollision (hnorm hz).le (hnorm hw).le) hsym hsurj hy
    simpa only [F, normalized_return_zero c p hd] using hcard
  · intro z hz
    have hzn : ‖z‖ ≤ 1/6 := by simpa using hz
    exact hexhaust (by linarith) (hphase z hzn).1
  · intro n hn
    rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    refine ⟨F^[n] z, hphases n hn ⟨z, hz, rfl⟩, ?_⟩
    exact normalized_iterate_scale c p hd n z

/-- The analytic tail also has a strict ambient p-return barrier. -/
theorem actual_parent_barrier {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {z : ℂ} (hz : ‖z‖ = 23/20) :
    23/20 < ‖normalizedReturn c p z‖ := by
  have hsmall : criticalValue c p ≤ 12/(4 : ℝ)^p := by
    simpa only [scale, one_div_pow, mul_one_div] using hc.2.2.1
  have herror := normalized_return_error c p (by omega) hc.2.2.2.2.2.2
    hc.2.1 hsmall z hz.le
  change ‖normalizedReturn c p z - complexMap (kappa p c) z‖ ≤ 24/(4 : ℝ)^p at herror
  have hpow := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4)
    (show 13 ≤ p by omega)
  norm_num at hpow
  have heps : 24/(4 : ℝ)^p ≤ 1/100000 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 4^p)).mpr
    linarith
  have hk := hc.2.2.2.1.1
  change 17903/10000 ≤ kappa p c at hk
  have hlead := norm_sub_le (1 : ℂ) (complexMap (kappa p c) z)
  have he : 1 - complexMap (kappa p c) z = (kappa p c : ℂ) * z^2 := by
    simp [complexMap]
  rw [he, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by linarith), hz, norm_one] at hlead
  have ht := norm_le_norm_sub_add (complexMap (kappa p c) z) (normalizedReturn c p z)
  rw [norm_sub_rev] at ht
  linarith

theorem actual_parent_restriction {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) : ParentRestriction c p := by
  have hcanonical := actual_canonical_collar hp hc
  have hband := parameter_band hp hc.1
  have hsmall : criticalValue c p ≤ 12/(4 : ℝ)^p := by
    simpa only [scale, one_div_pow, mul_one_div] using hc.2.2.1
  apply parent_restriction_of_bounds c p (by omega) hcanonical
    (fun _ hz => actual_parent_barrier hp hc hz)
  · exact normalized_return_collision_iff c p (by omega)
      ⟨hband.1, by linarith [hband.2]⟩ hc.2.1 hsmall hc.2.2.2.1
  · intro z hz
    have hb := (actual_phase_bounds hp hc hz).2.2.2
    exact ⟨hb 1 (by omega), hb 2 (by omega)⟩

/-- The physical radius fixed by the archived p-return convention. -/
def archivedTargetRadius (p : ℕ) : ℝ := if p = 3 then 1/4 else 1/(2 : ℝ)^p

def archivedParentSource (c : ℝ) (p : ℕ) : Set ℂ :=
  connectedComponentIn (((quadraticMap c)^[p]) ⁻¹'
    ball 0 (archivedTargetRadius p)) 0

/-- The new ambient restriction lies inside the archived p-return
component whenever its explicitly chosen target disk lies inside the
archived target.  This proves inclusion, without asserting equality. -/
theorem physical_parent_subset_archived (c : ℝ) (p : ℕ)
    (hd : 0 < criticalValue c p) (hparent : ParentRestriction c p)
    (hscale : criticalValue c p * (23/20) < archivedTargetRadius p) :
    physicalParentSource c p ⊆ archivedParentSource c p := by
  have hconn : IsPreconnected (physicalParentSource c p) :=
    hparent.isConnected_source.isPreconnected.image _
      (continuous_const.mul continuous_id).continuousOn
  have h0 : (0 : ℂ) ∈ physicalParentSource c p := ⟨0, hparent.zero_mem, mul_zero _⟩
  apply hconn.subset_connectedComponentIn h0
  rintro _ ⟨z, hz, rfl⟩
  have hzF : ‖normalizedReturn c p z‖ < 23/20 := by
    simpa using connectedComponentIn_subset
      (normalizedReturn c p ⁻¹' ball 0 (23/20)) 0 hz
  change ((quadraticMap c)^[p]) ((criticalValue c p : ℂ) * z) ∈
    ball 0 (archivedTargetRadius p)
  rw [mem_ball_zero_iff]
  have he := normalized_iterate_scale c p hd.ne' 1 z
  simp only [iterate_one, one_mul] at he
  rw [← he, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd]
  nlinarith

theorem actual_parent_scale_bound {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) :
    criticalValue c p * (23/20) < archivedTargetRadius p := by
  have hsmall : criticalValue c p ≤ 12/(4 : ℝ)^p := by
    simpa only [scale, one_div_pow, mul_one_div] using hc.2.2.1
  have ht : 16 ≤ (2 : ℝ)^p := by
    have h := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (show 4 ≤ p by omega)
    norm_num at h
    exact h
  have he : (4 : ℝ)^p = ((2 : ℝ)^p)^2 := by
    rw [← pow_mul, Nat.mul_comm p 2, pow_mul]
    norm_num
  have htpos : 0 < (2 : ℝ)^p := by positivity
  have hmul := (le_div_iff₀ (by positivity : (0 : ℝ) < 4^p)).mp hsmall
  rw [he] at hmul
  rw [archivedTargetRadius, if_neg (by omega)]
  apply (lt_div_iff₀ htpos).mpr
  nlinarith [hc.2.1]

theorem actual_phases_subset_archived {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) (n : ℕ) (hn : n ≤ 2) :
    ((quadraticMap c)^[n*p]) '' physicalSource c p ⊆ archivedParentSource c p :=
  ((actual_parent_restriction hp hc).physical_phase_subset n hn).trans
    (physical_parent_subset_archived c p hc.2.1 (actual_parent_restriction hp hc)
      (actual_parent_scale_bound hp hc))

end
end ThreeReturnParent

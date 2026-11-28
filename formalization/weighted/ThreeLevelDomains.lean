import ThreeReturnDomain
import ThreeReturnDegree

/-!
# Actual polynomial return components at an arbitrary signed scale

The middle return of a three-level construction is not in the terminal
tip chart.  Its source is therefore selected directly from the complete
polynomial pullback of its own target disk.  A circle barrier and complete
signed collision control give its proper restriction and exact fibers.
The estimates can be supplied in any nonzero signed affine coordinate.
-/

namespace ThreeLevelDomains

open Set Function Metric Topology
open LimitingCrestQuadraticReturn LoopsQuadraticCylinderCensus

noncomputable section

def source (c : ℝ) (n : ℕ) (R : ℝ) : Set ℂ :=
  connectedComponentIn (((quadraticMap c)^[n]) ⁻¹' ball 0 R) 0

def sourceMap (c : ℝ) (n : ℕ) (R : ℝ) :
    source c n R → ball (0 : ℂ) R :=
  fun z => ⟨((quadraticMap c)^[n]) z,
    connectedComponentIn_subset (((quadraticMap c)^[n]) ⁻¹' ball 0 R)
      0 z.property⟩

/-- All geometric fields concern the complete literal polynomial iterate. -/
structure Restriction (c : ℝ) (n : ℕ) (R r : ℝ) : Prop where
  inner_pos : 0 < r
  radius_lt : r < R
  zero_mem : (0 : ℂ) ∈ source c n R
  source_open : IsOpen (source c n R)
  source_connected : IsConnected (source c n R)
  compact_closure : IsCompact (closure (source c n R))
  closure_inside : closure (source c n R) ⊆ ball 0 r
  image_eq : ((quadraticMap c)^[n]) '' source c n R = ball 0 R
  proper : IsProperMap (sourceMap c n R)
  symmetric : ∀ z ∈ source c n R, -z ∈ source c n R
  fiber_card : ∀ y ∈ ball (0 : ℂ) R,
    {z : ℂ | z ∈ source c n R ∧ ((quadraticMap c)^[n]) z = y}.ncard =
      if y = ((quadraticMap c)^[n]) 0 then 1 else 2
  exhaustion : ∀ z : ℂ, ‖z‖ ≤ r → ‖((quadraticMap c)^[n]) z‖ < R →
    z ∈ source c n R

/-- Exact signed fibers and a whole-circle barrier select the entire
central component, without prescribing a smaller source neighborhood. -/
theorem restriction_of_estimates (c : ℝ) (n : ℕ) (R r : ℝ)
    (hn : 0 < n) (hr : 0 < r) (hrR : r < R)
    (hzero : ‖((quadraticMap c)^[n]) 0‖ < R)
    (hbarrier : ∀ z : ℂ, ‖z‖ = r → R < ‖((quadraticMap c)^[n]) z‖)
    (hcollision : ∀ {z w : ℂ}, ‖z‖ ≤ r → ‖w‖ ≤ r →
      (((quadraticMap c)^[n]) z = ((quadraticMap c)^[n]) w ↔
        z = w ∨ z = -w)) :
    Restriction c n R r := by
  let F := (quadraticMap c)^[n]
  have hp : IsProperMap F := quadratic_iterate_proper (c : ℂ) n
  have ho : IsOpenMap F := quadratic_iterate_open (c : ℂ) n
  have h0 : (0 : ℂ) ∈ source c n R :=
    mem_connectedComponentIn (by simpa using hzero)
  obtain ⟨hcl, hcompact⟩ := ThreeReturnDomain.component_closure_inside_barrier
    F hp.continuous r R hr hzero hbarrier
  change closure (source c n R) ⊆ ball 0 r at hcl
  change IsCompact (closure (source c n R)) at hcompact
  have hnorm {z : ℂ} (hz : z ∈ source c n R) : ‖z‖ ≤ r := by
    exact (show ‖z‖ < r by simpa using hcl (subset_closure hz)).le
  have himage : F '' source c n R = ball 0 R :=
    localized_component_image F (F ⁻¹' ball 0 R) (ball 0 R)
      ho hp.isClosedMap (isOpen_ball.preimage hp.continuous)
      (convex_ball (0 : ℂ) R).isPreconnected
      (fun _ hz => hz) (fun _ hz => hz.2) 0 (by simpa using hzero)
  have hsurj : SurjOn F (source c n R) (ball 0 R) := by
    simp only [SurjOn, himage, Subset.refl]
  have heven (z : ℂ) : F (-z) = F z := by
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
    dsimp [F]
    rw [hm]
    simp only [iterate_succ_apply, quadraticMap, neg_sq]
  have hsym : ∀ z ∈ source c n R, -z ∈ source c n R := by
    have hconn : IsPreconnected ((fun z : ℂ => -z) '' source c n R) :=
      isPreconnected_connectedComponentIn.image _ continuous_neg.continuousOn
    have hhit : (0 : ℂ) ∈ (fun z : ℂ => -z) '' source c n R :=
      ⟨0, h0, neg_zero⟩
    have hsub : (fun z : ℂ => -z) '' source c n R ⊆ F ⁻¹' ball 0 R := by
      rintro _ ⟨z, hz, rfl⟩
      change F (-z) ∈ ball 0 R
      rw [heven]
      exact connectedComponentIn_subset (F ⁻¹' ball 0 R) 0 hz
    have h := hconn.subset_connectedComponentIn hhit hsub
    exact fun z hz => h ⟨z, hz, rfl⟩
  refine ⟨hr, hrR, h0,
    (isOpen_ball.preimage hp.continuous).connectedComponentIn,
    ⟨⟨0, h0⟩, isPreconnected_connectedComponentIn⟩,
    hcompact, hcl, himage,
    ThreeReturnDomain.component_proper F hp (ball 0 R) 0 isOpen_ball,
    hsym, ?_, ?_⟩
  · intro y hy
    exact ThreeReturnDegree.fiber_ncard F (source c n R) (ball 0 R) h0
      (fun hz hw => hcollision (hnorm hz) (hnorm hw)) hsym hsurj hy
  · intro z hz hfz
    obtain ⟨w, hw, hwe⟩ := hsurj (show F z ∈ ball 0 R by simpa using hfz)
    rcases (hcollision (hnorm hw) hz).mp hwe with heq | heq
    · exact heq ▸ hw
    · have hzw : z = -w := by rw [heq, neg_neg]
      rw [hzw]
      exact hsym w hw

/-- A complete return viewed in a signed monic coordinate. -/
def scaledReturn (c : ℝ) (n : ℕ) (a : ℝ) (z : ℂ) : ℂ :=
  (a : ℂ) * ((quadraticMap c)^[n]) (z/(a : ℂ))

theorem scaledReturn_physical (c : ℝ) (n : ℕ) (a : ℝ) (ha : a ≠ 0)
    (z : ℂ) :
    scaledReturn c n a ((a : ℂ)*z) = (a : ℂ)*((quadraticMap c)^[n]) z := by
  have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha
  unfold scaledReturn
  congr 1
  field_simp [haC]

/-- Circle and collision estimates in a signed affine coordinate produce
the actual physical restriction, with radii divided by the absolute scale. -/
theorem restriction_of_scaled_estimates (c : ℝ) (n : ℕ) (a R r : ℝ)
    (hn : 0 < n) (ha : a ≠ 0) (hr : 0 < r) (hrR : r < R)
    (hzero : ‖scaledReturn c n a 0‖ < R)
    (hbarrier : ∀ z : ℂ, ‖z‖ = r → R < ‖scaledReturn c n a z‖)
    (hcollision : ∀ {z w : ℂ}, ‖z‖ ≤ r → ‖w‖ ≤ r →
      (scaledReturn c n a z = scaledReturn c n a w ↔ z = w ∨ z = -w)) :
    Restriction c n (R/|a|) (r/|a|) := by
  have habs : 0 < |a| := abs_pos.mpr ha
  have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha
  have hnorm (z : ℂ) : ‖(a : ℂ)*z‖ = |a| * ‖z‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  apply restriction_of_estimates c n (R/|a|) (r/|a|) hn
    (div_pos hr habs) ((div_lt_div_iff_of_pos_right habs).mpr hrR)
  · have hz := scaledReturn_physical c n a ha 0
    simp only [mul_zero] at hz
    rw [hz, hnorm] at hzero
    apply (lt_div_iff₀ habs).mpr
    nlinarith only [hzero]
  · intro z hz
    have hs : ‖(a : ℂ)*z‖ = r := by
      rw [hnorm, hz]
      field_simp [habs.ne']
    have hb := hbarrier ((a : ℂ)*z) hs
    rw [scaledReturn_physical c n a ha z, hnorm] at hb
    apply (div_lt_iff₀ habs).mpr
    nlinarith only [hb]
  · intro z w hz hw
    have hz' : ‖(a : ℂ)*z‖ ≤ r := by
      rw [hnorm]
      have hh := (le_div_iff₀ habs).mp hz
      nlinarith only [hh]
    have hw' : ‖(a : ℂ)*w‖ ≤ r := by
      rw [hnorm]
      have hh := (le_div_iff₀ habs).mp hw
      nlinarith only [hh]
    have h := hcollision hz' hw'
    rw [scaledReturn_physical c n a ha z,
      scaledReturn_physical c n a ha w] at h
    constructor
    · intro he
      rcases h.mp (congrArg (fun v : ℂ => (a : ℂ)*v) he) with heq | heq
      · exact Or.inl (mul_left_cancel₀ haC heq)
      · exact Or.inr (mul_left_cancel₀ haC (by simpa only [mul_neg] using heq))
    · rintro (he | he)
      · rw [he]
      · apply mul_left_cancel₀ haC
        apply h.mpr
        right
        rw [he, mul_neg]

/-- Uniform image control on a complete disk places that disk in the
already selected central component. -/
theorem disk_in_source (c : ℝ) (n : ℕ) (R δ : ℝ) (hδ : 0 ≤ δ)
    (himage : ∀ z : ℂ, ‖z‖ ≤ δ → ‖((quadraticMap c)^[n]) z‖ < R) :
    closedBall (0 : ℂ) δ ⊆ source c n R := by
  have h0 : (0 : ℂ) ∈ closedBall (0 : ℂ) δ := by
    simpa only [mem_closedBall, dist_self] using hδ
  apply (convex_closedBall (0 : ℂ) δ).isPreconnected.subset_connectedComponentIn h0
  intro z hz
  simpa only [mem_preimage, mem_ball_zero_iff] using
    himage z (by simpa only [mem_closedBall_zero_iff] using hz)

/-- A scaled comparison disk is retained as a whole physical disk. -/
theorem scaled_disk_in_source (c : ℝ) (n : ℕ) (a R δ : ℝ)
    (ha : a ≠ 0) (hδ : 0 ≤ δ)
    (himage : ∀ z : ℂ, ‖z‖ ≤ δ → ‖scaledReturn c n a z‖ < R) :
    ∀ z : ℂ, ‖z‖ ≤ δ → z/(a : ℂ) ∈ source c n (R/|a|) := by
  have habs : 0 < |a| := abs_pos.mpr ha
  have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha
  have hsub : closedBall (0 : ℂ) (δ/|a|) ⊆ source c n (R/|a|) := by
    apply disk_in_source c n (R/|a|) (δ/|a|) (div_nonneg hδ habs.le)
    intro z hz
    have hz' : ‖(a : ℂ)*z‖ ≤ δ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have hh := (le_div_iff₀ habs).mp hz
      nlinarith only [hh]
    have hh := himage ((a : ℂ)*z) hz'
    rw [scaledReturn_physical c n a ha z, norm_mul,
      Complex.norm_real, Real.norm_eq_abs] at hh
    apply (lt_div_iff₀ habs).mpr
    nlinarith only [hh]
  intro z hz
  apply hsub
  rw [mem_closedBall_zero_iff, norm_div, Complex.norm_real, Real.norm_eq_abs]
  exact div_le_div_of_nonneg_right hz habs.le

/-- Complete phase bounds, on all source points, imply phase nesting. -/
theorem phases_in_source {c : ℝ} {n m : ℕ} {R δ : ℝ} {S : Set ℂ}
    (hδ : 0 ≤ δ)
    (himage : ∀ z : ℂ, ‖z‖ ≤ δ → ‖((quadraticMap c)^[n]) z‖ < R)
    (hphase : ∀ z ∈ S, ‖((quadraticMap c)^[m]) z‖ ≤ δ) :
    ((quadraticMap c)^[m]) '' S ⊆ source c n R := by
  rintro _ ⟨z, hz, rfl⟩
  apply disk_in_source c n R δ hδ himage
  simpa only [mem_closedBall_zero_iff] using hphase z hz

end
end ThreeLevelDomains

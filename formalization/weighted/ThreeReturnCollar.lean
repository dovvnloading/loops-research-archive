import ThreeReturnDomain
import ThreeReturnDegree
import ThreeReturnAnnulus
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Uniform canonical physical three-return collars

The inner domain is the component containing zero of the complete actual
three-return pullback.  The numerical barrier chooses that component before
any shrinking.  The statements below connect its proper map and exact fibers
to a scale-independent Dirichlet-energy certificate in the original plane.
-/

namespace ThreeReturnCollar

open Set Function Metric Topology
open LimitingCrestQuadraticReturn ThreeReturnDomain ThreeReturnDegree
open ThreeReturnEstimates ThreeReturnAnnulus NearTwoTip
open scoped ENNReal

noncomputable section

/-- The literal restriction between the selected plane domains. -/
def sourceMap (c : ℝ) (p : ℕ) : source c p → ball (0 : ℂ) (1/6) :=
  fun z => ⟨threeReturn c p z,
    connectedComponentIn_subset (threeReturn c p ⁻¹' ball 0 (1/6)) 0 z.property⟩

/-- The selected source in the original dynamical coordinate. -/
def physicalSource (c : ℝ) (p : ℕ) : Set ℂ :=
  (fun z : ℂ => (criticalValue c p : ℂ) * z) '' source c p

def physicalTarget (c : ℝ) (p : ℕ) : Set ℂ :=
  ball 0 (criticalValue c p / 6)

theorem source_zero (c : ℝ) (p : ℕ)
    (hzero : ‖threeReturn c p 0‖ < 1/6) : (0 : ℂ) ∈ source c p :=
  mem_connectedComponentIn (by simpa using hzero)

theorem source_open (c : ℝ) (p : ℕ) (hd : criticalValue c p ≠ 0) :
    IsOpen (source c p) :=
  (isOpen_ball.preimage (threeReturn_proper c p hd).continuous).connectedComponentIn

theorem source_connected (c : ℝ) (p : ℕ)
    (hzero : ‖threeReturn c p 0‖ < 1/6) : IsConnected (source c p) :=
  ⟨⟨0, source_zero c p hzero⟩, isPreconnected_connectedComponentIn⟩

theorem sourceMap_proper (c : ℝ) (p : ℕ) (hd : criticalValue c p ≠ 0) :
    IsProperMap (sourceMap c p) :=
  component_proper (threeReturn c p) (threeReturn_proper c p hd)
    (ball 0 (1/6)) 0 isOpen_ball

/-- Scaling identifies the complete pullback sets, not only their orbits. -/
theorem physical_pullback_image (c : ℝ) (p : ℕ) (hd : 0 < criticalValue c p) :
    (fun z : ℂ => (criticalValue c p : ℂ) * z) ''
        (threeReturn c p ⁻¹' ball 0 (1/6)) =
      ((quadraticMap c)^[3*p]) ⁻¹' physicalTarget c p := by
  let d := criticalValue c p
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have hscale (z : ℂ) := normalized_iterate_scale c p hd.ne' 3 z
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    have hwn : ‖threeReturn c p w‖ < 1/6 := by simpa using hw
    change ((quadraticMap c)^[3*p]) ((d : ℂ) * w) ∈ ball 0 (d/6)
    rw [← hscale w, mem_ball_zero_iff, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hd]
    change d * ‖threeReturn c p w‖ < d/6
    nlinarith
  · intro hz
    refine ⟨z / (d : ℂ), ?_, ?_⟩
    · change threeReturn c p (z / (d : ℂ)) ∈ ball 0 (1/6)
      rw [mem_ball_zero_iff]
      have he : (d : ℂ) * (z / (d : ℂ)) = z := by field_simp
      have hn : ‖((quadraticMap c)^[3*p]) z‖ < d/6 := by simpa [physicalTarget] using hz
      rw [← he, ← hscale (z / (d : ℂ)), norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hd] at hn
      change d * ‖threeReturn c p (z / (d : ℂ))‖ < d/6 at hn
      nlinarith
    · change (d : ℂ) * (z / (d : ℂ)) = z
      field_simp [hdC]

/-- The physical domain is exactly the central component of the full
physical `3*p`-iterate pullback of the fixed physical disk. -/
theorem physicalSource_eq_component (c : ℝ) (p : ℕ)
    (hd : 0 < criticalValue c p) (hzero : ‖threeReturn c p 0‖ < 1/6) :
    physicalSource c p = connectedComponentIn
      (((quadraticMap c)^[3*p]) ⁻¹' physicalTarget c p) 0 := by
  have hdC : (criticalValue c p : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  let e := Homeomorph.mulLeft₀ (criticalValue c p : ℂ) hdC
  have he := e.image_connectedComponentIn
    (show (0 : ℂ) ∈ threeReturn c p ⁻¹' ball 0 (1/6) by simpa using hzero)
  change physicalSource c p = connectedComponentIn
    ((fun z : ℂ => (criticalValue c p : ℂ) * z) ''
      (threeReturn c p ⁻¹' ball 0 (1/6))) ((criticalValue c p : ℂ) * 0) at he
  simpa only [physical_pullback_image c p hd, mul_zero] using he

theorem physicalSource_closure (c : ℝ) (p : ℕ)
    (hd : 0 < criticalValue c p)
    (hinside : closure (source c p) ⊆ ball 0 (3/20)) :
    closure (physicalSource c p) ⊆ ball 0 (3 * criticalValue c p / 20) := by
  have hdC : (criticalValue c p : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  let e := Homeomorph.mulLeft₀ (criticalValue c p : ℂ) hdC
  have he : closure (physicalSource c p) = e '' closure (source c p) :=
    (e.image_closure (source c p)).symm
  rw [he]
  rintro _ ⟨z, hz, rfl⟩
  have hn : ‖z‖ < 3/20 := by simpa using hinside hz
  change (criticalValue c p : ℂ) * z ∈ ball 0 (3 * criticalValue c p / 20)
  rw [mem_ball_zero_iff, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd]
  nlinarith

/-- Quantitative geometry of the canonical domains.  All fields refer to
the selected actual polynomial component or a literal plane integral. -/
structure CanonicalCollar (c : ℝ) (p : ℕ) : Prop where
  scale_pos : 0 < criticalValue c p
  zero_mem : (0 : ℂ) ∈ source c p
  isOpen_source : IsOpen (source c p)
  isConnected_source : IsConnected (source c p)
  compact_closure : IsCompact (closure (source c p))
  closure_inside : closure (source c p) ⊆ ball 0 (3/20)
  image_eq : threeReturn c p '' source c p = ball 0 (1/6)
  proper : IsProperMap (sourceMap c p)
  fiber_card : ∀ y ∈ ball (0 : ℂ) (1/6),
    {z : ℂ | z ∈ source c p ∧ threeReturn c p z = y}.ncard =
      if y = threeReturn c p 0 then 1 else 2
  physical_closure_inside : closure (physicalSource c p) ⊆
    ball 0 (3 * criticalValue c p / 20)
  capacity_lt : capacity (closure (physicalSource c p)) (physicalTarget c p) < 60
  modulus_gt : (60 : ℝ≥0∞)⁻¹ <
    variationalModulus (closure (physicalSource c p)) (physicalTarget c p)

/-- The generic assembly separates finite exact certificates from the
all-period analytic tail.  No domain, degree, or capacity conclusion is an
input: the only geometric inputs are a boundary inequality and collisions. -/
theorem canonical_collar_of_bounds (c : ℝ) (p : ℕ) (hp : 0 < p)
    (hd : 0 < criticalValue c p)
    (hzero : ‖threeReturn c p 0‖ < 1/6)
    (hbarrier : ∀ z : ℂ, ‖z‖ = 3/20 → 1/6 < ‖threeReturn c p z‖)
    (hcollision : ∀ {z w : ℂ}, ‖z‖ ≤ 1/6 → ‖w‖ ≤ 1/6 →
      (threeReturn c p z = threeReturn c p w ↔ z = w ∨ z = -w)) :
    CanonicalCollar c p := by
  obtain ⟨hinside, hcompact⟩ := component_closure_inside_barrier
    (threeReturn c p) (threeReturn_proper c p hd.ne').continuous
    (3/20) (1/6) (by norm_num) hzero hbarrier
  change closure (source c p) ⊆ ball 0 (3/20) at hinside
  have h0 := source_zero c p hzero
  have hnorm {z : ℂ} (hz : z ∈ source c p) : ‖z‖ ≤ 1/6 := by
    have hn : ‖z‖ < 3/20 := by simpa using hinside (subset_closure hz)
    linarith
  have honto := source_image c p hd.ne' hzero
  have hphys := physicalSource_closure c p hd hinside
  have hphysclosed := hphys.trans ball_subset_closedBall
  exact ⟨hd, h0, source_open c p hd.ne', source_connected c p hzero,
    hcompact, hinside, honto, sourceMap_proper c p hd.ne',
    fun y hy => fiber_ncard (threeReturn c p) (source c p) (ball 0 (1/6)) h0
      (fun hz hw => hcollision (hnorm hz) (hnorm hw))
      (source_symmetric c p hp hzero) (by simp only [SurjOn, honto, Subset.refl]) hy,
    hphys, physical_capacity_lt_sixty hd hphysclosed,
    physical_variationalModulus_gt hd hphysclosed⟩

theorem actual_canonical_collar {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) : CanonicalCollar c p := by
  apply canonical_collar_of_bounds c p (by omega) hc.2.1
    (actual_critical_value_bound hp hc)
  · intro z hz
    have hb := actual_annular_barrier hp hc (le_of_eq hz.symm)
      (by rw [hz]; norm_num [outerRadius])
    change 1/6 + 1/500 < ‖threeReturn c p z‖ at hb
    linarith
  · exact fun hz hw => actual_three_return_collision_iff hp hc hz hw

/-- Every period in the analytic tail has an actual signed tip with the
canonical, fixed-radius physical capacity certificate. -/
theorem exists_actual_canonical_collar (p : ℕ) (hp : 17 ≤ p) :
    ∃ c : ℝ, ActualTip p c ∧ CanonicalCollar c p := by
  obtain ⟨c, hc⟩ := exists_actual_tip p hp
  exact ⟨c, hc, actual_canonical_collar hp hc⟩

end
end ThreeReturnCollar

import ThreeReturnParent
import ThreeReturnContraction

/-!
# Physical realization and the trapped critical orbit

The actual physical restriction is proper and holomorphic.  Scaling
transports the source contraction and all three disjoint phase domains.
The signed critical relation supplies the exact orbit after the critical
value, and the complete fiber census keeps that whole orbit in the
canonically selected source.
-/

namespace ThreeReturnRealization

open Set Function Metric
open scoped Topology
open LimitingCrestQuadraticReturn LoopsQuadraticCylinderCensus
open ThreeReturnDomain ThreeReturnDegree ThreeReturnCollar ThreeReturnPhysical
open ThreeReturnParent ThreeReturnContraction

noncomputable section

/-- The literal physical return map, with its actual source and target. -/
def physicalMap (c : ℝ) (p : ℕ) (hc : CanonicalCollar c p) :
    physicalSource c p → physicalTarget c p :=
  fun z => ⟨((quadraticMap c)^[3*p]) z,
    (physical_return_image hc) ▸ mem_image_of_mem _ z.property⟩

private theorem restriction_proper_of_component (f : ℂ → ℂ) (hf : IsProperMap f)
    (W V : Set ℂ) (x : ℂ) (hV : IsOpen V)
    (hW : W = connectedComponentIn (f ⁻¹' V) x) (hm : MapsTo f W V) :
    IsProperMap (MapsTo.restrict f W V hm) := by
  subst W
  exact component_proper f hf V x hV

/-- Properness is proved directly for the complete physical iterate
between the physical source and target subspaces. -/
theorem physicalMap_proper {c : ℝ} {p : ℕ} (hc : CanonicalCollar c p) :
    IsProperMap (physicalMap c p hc) := by
  exact restriction_proper_of_component ((quadraticMap c)^[3*p])
    (quadratic_iterate_proper (c : ℂ) (3*p))
    (physicalSource c p) (physicalTarget c p) 0 isOpen_ball
    (physicalSource_eq_component c p hc.scale_pos (collar_critical_value hc))
    (fun z hz => (physical_return_image hc) ▸ mem_image_of_mem _ hz)

/-- Global complex differentiability of the actual physical polynomial. -/
theorem physical_return_differentiable (c : ℝ) (p : ℕ) :
    Differentiable ℂ ((quadraticMap c)^[3*p]) := by
  have hquad : Differentiable ℂ (quadraticMap c) := by
    change Differentiable ℂ (fun z : ℂ => z^2 + (c : ℂ))
    exact (differentiable_id.pow 2).add_const (c : ℂ)
  exact hquad.iterate (3*p)

/-- The source contraction is transported by the actual nonzero physical
scale, preserving the literal domain rather than replacing its topology. -/
theorem physical_source_contractible {c : ℝ} {p : ℕ}
    (hc : CanonicalCollar c p) (hW : ContractibleSpace (source c p)) :
    ContractibleSpace (physicalSource c p) := by
  letI := hW
  have hdC : (criticalValue c p : ℂ) ≠ 0 := by exact_mod_cast hc.scale_pos.ne'
  let e := Homeomorph.mulLeft₀ (criticalValue c p : ℂ) hdC
  have he : source c p ≃ₜ physicalSource c p := e.isEmbedding.homeomorphImage (source c p)
  exact he.symm.contractibleSpace

/-- Every physical phase is the scaled corresponding normalized phase. -/
theorem physical_phase_image (c : ℝ) (p : ℕ) (hd : criticalValue c p ≠ 0) (n : ℕ) :
    (fun z : ℂ => (criticalValue c p : ℂ) * z) ''
        ((normalizedReturn c p)^[n] '' source c p) =
      ((quadraticMap c)^[n*p]) '' physicalSource c p := by
  ext z
  constructor
  · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    exact ⟨(criticalValue c p : ℂ) * u, ⟨u, hu, rfl⟩,
      (normalized_iterate_scale c p hd n u).symm⟩
  · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    exact ⟨((normalizedReturn c p)^[n]) u, ⟨u, hu, rfl⟩,
      normalized_iterate_scale c p hd n u⟩

/-- Pairwise phase disjointness is transported into the original
dynamical plane with the literal p-th and 2p-th quadratic iterates. -/
theorem physical_phases_disjoint (c : ℝ) (p : ℕ) (hd : criticalValue c p ≠ 0)
    (hphase : Disjoint (source c p) (normalizedReturn c p '' source c p) ∧
      Disjoint (source c p) ((normalizedReturn c p)^[2] '' source c p) ∧
      Disjoint (normalizedReturn c p '' source c p)
        ((normalizedReturn c p)^[2] '' source c p)) :
    Disjoint (physicalSource c p) (((quadraticMap c)^[p]) '' physicalSource c p) ∧
      Disjoint (physicalSource c p) (((quadraticMap c)^[2*p]) '' physicalSource c p) ∧
      Disjoint (((quadraticMap c)^[p]) '' physicalSource c p)
        (((quadraticMap c)^[2*p]) '' physicalSource c p) := by
  let M := fun z : ℂ => (criticalValue c p : ℂ) * z
  have hdC : (criticalValue c p : ℂ) ≠ 0 := by exact_mod_cast hd
  have hi : Injective M := fun _ _ h => mul_left_cancel₀ hdC h
  have h0 : M '' source c p = physicalSource c p := rfl
  have h1 : M '' (normalizedReturn c p '' source c p) =
      ((quadraticMap c)^[p]) '' physicalSource c p := by
    simpa only [iterate_one, one_mul] using physical_phase_image c p hd 1
  have h2 : M '' ((normalizedReturn c p)^[2] '' source c p) =
      ((quadraticMap c)^[2*p]) '' physicalSource c p := physical_phase_image c p hd 2
  refine ⟨?_, ?_, ?_⟩
  · simpa only [h0, h1] using disjoint_image_of_injective hi hphase.1
  · simpa only [h0, h2] using disjoint_image_of_injective hi hphase.2.1
  · simpa only [h1, h2] using disjoint_image_of_injective hi hphase.2.2

/-- The signed critical relation gives the exact two subsequent values
of the normalized three-return critical orbit. -/
theorem critical_signed_orbit (c : ℝ) (p : ℕ) (hp : 0 < p)
    (hd : criticalValue c p ≠ 0)
    (hrelation : criticalValue c (6*p) + criticalValue c (3*p) = 0) :
    threeReturn c p (threeReturn c p 0) = -threeReturn c p 0 ∧
      threeReturn c p (-threeReturn c p 0) = -threeReturn c p 0 := by
  have hdC : (criticalValue c p : ℂ) ≠ 0 := by exact_mod_cast hd
  have h3 := normalized_iterate_scale c p hd 3 (0 : ℂ)
  have h6 := normalized_iterate_scale c p hd 6 (0 : ℂ)
  simp only [mul_zero, quadratic_iterate_zero] at h3 h6
  change (criticalValue c p : ℂ) * threeReturn c p 0 =
    (criticalValue c (3*p) : ℂ) at h3
  change (criticalValue c p : ℂ) * threeReturn c p (threeReturn c p 0) =
    (criticalValue c (6*p) : ℂ) at h6
  have hrelC : (criticalValue c (6*p) : ℂ) + (criticalValue c (3*p) : ℂ) = 0 := by
    exact_mod_cast hrelation
  have hnext : threeReturn c p (threeReturn c p 0) = -threeReturn c p 0 := by
    apply mul_left_cancel₀ hdC
    rw [h6, mul_neg, h3]
    exact eq_neg_of_add_eq_zero_left hrelC
  exact ⟨hnext, (threeReturn_even c p hp (threeReturn c p 0)).trans hnext⟩

/-- Exact fibers exhaust all inverse points in the closed control disk.
The conclusion identifies membership in the actual canonical component. -/
theorem canonical_source_exhaustion (c : ℝ) (p : ℕ) (hp : 0 < p)
    (hc : CanonicalCollar c p)
    (hcollision : ∀ {z w : ℂ}, ‖z‖ ≤ 1/6 → ‖w‖ ≤ 1/6 →
      (threeReturn c p z = threeReturn c p w ↔ z = w ∨ z = -w))
    {z : ℂ} (hz : ‖z‖ ≤ 1/6) (hfz : ‖threeReturn c p z‖ < 1/6) :
    z ∈ source c p := by
  have hzimage : threeReturn c p z ∈ threeReturn c p '' source c p := by
    rw [hc.image_eq]
    simpa using hfz
  obtain ⟨w, hw, hwe⟩ := hzimage
  have hwn : ‖w‖ ≤ 1/6 := by
    have h : ‖w‖ < 3/20 := by simpa using hc.closure_inside (subset_closure hw)
    linarith
  rcases (hcollision hwn hz).mp hwe with he | he
  · exact he ▸ hw
  · have hzw : z = -w := by rw [he, neg_neg]
    rw [hzw]
    exact source_symmetric c p hp (collar_critical_value hc) w hw

/-- The complete normalized critical orbit remains in the canonical
source and lands on its signed fixed point after two returns. -/
theorem critical_orbit_trapped (c : ℝ) (p : ℕ) (hp : 0 < p)
    (hc : CanonicalCollar c p)
    (hrelation : criticalValue c (6*p) + criticalValue c (3*p) = 0)
    (hcollision : ∀ {z w : ℂ}, ‖z‖ ≤ 1/6 → ‖w‖ ≤ 1/6 →
      (threeReturn c p z = threeReturn c p w ↔ z = w ∨ z = -w)) :
    threeReturn c p 0 ∈ source c p ∧ -threeReturn c p 0 ∈ source c p ∧
      (∀ n : ℕ, ((threeReturn c p)^[n]) 0 ∈ source c p) ∧
      (∀ n : ℕ, ((threeReturn c p)^[n+2]) 0 = -threeReturn c p 0) := by
  let H := threeReturn c p
  have htrace := critical_signed_orbit c p hp hc.scale_pos.ne' hrelation
  have hvalue := collar_critical_value hc
  have ha : H 0 ∈ source c p := canonical_source_exhaustion c p hp hc hcollision
    hvalue.le (by rw [htrace.1, norm_neg]; exact hvalue)
  have hna : -H 0 ∈ source c p := source_symmetric c p hp hvalue (H 0) ha
  have htail : ∀ n : ℕ, (H^[n+2]) 0 = -H 0 := by
    intro n
    induction n with
    | zero => exact htrace.1
    | succ n ih =>
      rw [show n+1+2 = (n+2)+1 by omega, iterate_succ_apply', ih]
      exact htrace.2
  refine ⟨ha, hna, ?_, htail⟩
  intro n
  cases n with
  | zero => exact hc.zero_mem
  | succ n =>
    cases n with
    | zero => exact ha
    | succ n =>
      change (H^[n+2]) 0 ∈ source c p
      rw [htail]
      exact hna

/-- Scaling transports every critical iterate into the literal physical
source, for the complete physical return polynomial. -/
theorem physical_critical_orbit_trapped (c : ℝ) (p : ℕ) (hp : 0 < p)
    (hc : CanonicalCollar c p)
    (hrelation : criticalValue c (6*p) + criticalValue c (3*p) = 0)
    (hcollision : ∀ {z w : ℂ}, ‖z‖ ≤ 1/6 → ‖w‖ ≤ 1/6 →
      (threeReturn c p z = threeReturn c p w ↔ z = w ∨ z = -w)) (n : ℕ) :
    ((quadraticMap c)^[(3*p)*n]) 0 ∈ physicalSource c p := by
  have htrap := (critical_orbit_trapped c p hp hc hrelation hcollision).2.2.1 n
  have hsemi : Semiconj (fun z : ℂ => (criticalValue c p : ℂ) * z)
      (threeReturn c p) ((quadraticMap c)^[3*p]) :=
    fun z => normalized_iterate_scale c p hc.scale_pos.ne' 3 z
  have he := (hsemi.iterate_right n) (0 : ℂ)
  simp only [mul_zero] at he
  rw [iterate_mul]
  exact ⟨((threeReturn c p)^[n]) 0, htrap, he⟩

end

end ThreeReturnRealization

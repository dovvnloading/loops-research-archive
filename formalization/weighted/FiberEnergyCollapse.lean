import ConnectedFiberEnergy
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.MetricSpace.Defs
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Collapsing connected fibers by finite sampling energy

The energy is an unnormalized sum over all samples.  The smallness condition
controls the product of the covering radius with that sum, as well as the
covering radius itself.  Samples and the center may vary between certificates.

This module does not assert that any Mandelbrot fiber has these certificates.
-/

namespace Loops.FiberSampling

open Set Topology
open scoped Topology

variable {X : Type*} [MetricSpace X]

/-- Arbitrarily fine finite covers whose unnormalized radial energy has
vanishing radius-energy product.  No bound on the sample count is imposed. -/
def FineEnergyCertificates (K : Set X) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ (n : ℕ) (s : Fin n → X) (a : X) (r : ℝ),
      0 < r ∧ r < ε ∧ r * energy s a < ε ∧
        ∀ z ∈ K, ∃ i, dist z (s i) ≤ r

/-- Every sufficiently fine cover of a connected set pays a definite
unnormalized energy cost for each separated pair in that set. -/
theorem connected_sampling_cost_lower_bound
    {I : Type*} [Fintype I] (K : Set X) (hK : IsPreconnected K)
    (s : I → X) (a : X) (r : ℝ) (hr : 0 < r)
    (hcover : ∀ z ∈ K, ∃ i, dist z (s i) ≤ r)
    (x y : X) (hx : x ∈ K) (hy : y ∈ K)
    (hscale : r ≤ dist x y / 8) :
    dist x y ^ 3 / 1024 ≤ r * energy s a := by
  have h := connected_cubic_energy_bound K hK s a r hr hcover x y hx hy hscale
  nlinarith

/-- A single cover with cost below the separated-pair threshold is impossible.
This is the finite obstruction behind the all-scale criterion. -/
theorem no_low_cost_cover_of_separated_pair
    {I : Type*} [Fintype I] (K : Set X) (hK : IsPreconnected K)
    (s : I → X) (a : X) (r : ℝ) (hr : 0 < r)
    (hcover : ∀ z ∈ K, ∃ i, dist z (s i) ≤ r)
    (x y : X) (hx : x ∈ K) (hy : y ∈ K)
    (hscale : r ≤ dist x y / 8) :
    ¬ r * energy s a < dist x y ^ 3 / 1024 := by
  exact not_lt_of_ge
    (connected_sampling_cost_lower_bound K hK s a r hr hcover x y hx hy hscale)

/-- Connected sets with arbitrarily fine, sufficiently low-energy finite
covers are singletons or empty.  Both the samples and their center may vary. -/
theorem subsingleton_of_fineEnergyCertificates
    (K : Set X) (hK : IsPreconnected K) (hcert : FineEnergyCertificates K) :
    K.Subsingleton := by
  intro x hx y hy
  by_contra hxy
  have hd : 0 < dist x y := dist_pos.mpr hxy
  have hc : 0 < dist x y ^ 3 := pow_pos hd 3
  have he : 0 < min (dist x y / 8) (dist x y ^ 3 / 2048) := by
    apply lt_min
    · positivity
    · positivity
  obtain ⟨n, s, a, r, hr, hre, hcost, hcover⟩ := hcert _ he
  have hscale : r ≤ dist x y / 8 :=
    le_trans hre.le (min_le_left _ _)
  have hsmall : r * energy s a < dist x y ^ 3 / 2048 :=
    lt_of_lt_of_le hcost (min_le_right _ _)
  have hbound :=
    connected_cubic_energy_bound K hK s a r hr hcover x y hx hy hscale
  nlinarith

/-- Trivial sets have one-point certificates of zero energy. -/
theorem fineEnergyCertificates_of_subsingleton [Nonempty X]
    (K : Set X) (hK : K.Subsingleton) : FineEnergyCertificates K := by
  classical
  obtain ⟨a, ha⟩ : ∃ a : X, ∀ z ∈ K, z = a := by
    by_cases hn : K.Nonempty
    · obtain ⟨a, ha⟩ := hn
      exact ⟨a, fun z hz => hK hz ha⟩
    · exact ⟨Classical.choice (inferInstance : Nonempty X),
        fun z hz => False.elim (hn ⟨z, hz⟩)⟩
  intro ε hε
  refine ⟨1, (fun _ => a), a, ε / 2, ?_, ?_, ?_, ?_⟩
  · positivity
  · linarith
  · simpa [energy] using hε
  · intro z hz
    refine ⟨0, ?_⟩
    rw [ha z hz, dist_self]
    positivity

/-- For a connected set the finite sampling condition is exactly equivalent
to triviality.  The difficult direction is the cubic packing estimate. -/
theorem fineEnergyCertificates_iff_subsingleton [Nonempty X]
    (K : Set X) (hK : IsPreconnected K) :
    FineEnergyCertificates K ↔ K.Subsingleton :=
  ⟨subsingleton_of_fineEnergyCertificates K hK,
    fineEnergyCertificates_of_subsingleton K⟩

/-- A map with connected fibers satisfying the finite energy criterion
is injective.  No continuity assumption is needed for this implication. -/
theorem injective_of_fiber_energy_certificates {Y : Type*}
    (q : X → Y)
    (hconnected : ∀ b, IsPreconnected {x : X | q x = b})
    (hcert : ∀ b, FineEnergyCertificates {x : X | q x = b}) :
    Function.Injective q := by
  intro x y hxy
  have hs := subsingleton_of_fineEnergyCertificates
    {z : X | q z = q x} (hconnected (q x)) (hcert (q x))
  exact hs (show x ∈ {z : X | q z = q x} from rfl)
    (show y ∈ {z : X | q z = q x} from hxy.symm)

/-- The criterion also applies directly to reflexive fiber relations,
without first constructing a quotient space. -/
theorem relation_trivial_of_fiber_energy_certificates
    (R : X → X → Prop) (hrefl : ∀ x, R x x)
    (hconnected : ∀ x, IsPreconnected {y : X | R x y})
    (hcert : ∀ x, FineEnergyCertificates {y : X | R x y}) :
    ∀ x y, R x y ↔ x = y := by
  intro x y
  constructor
  · intro hxy
    have hs := subsingleton_of_fineEnergyCertificates
      {z : X | R x z} (hconnected x) (hcert x)
    exact hs (hrefl x) hxy
  · rintro rfl
    exact hrefl x

/-- A precise complex-plane interface: any assignment of connected sets
containing their base parameters becomes the singleton assignment if every
set admits the certificates.  Establishing that premise for Mandelbrot
fibers remains a separate mathematical task. -/
theorem complex_fiber_assignment_trivial
    (F : ℂ → Set ℂ) (hself : ∀ c, c ∈ F c)
    (hconnected : ∀ c, IsPreconnected (F c))
    (hcert : ∀ c, FineEnergyCertificates (F c)) :
    ∀ c, F c = {c} := by
  intro c
  have hs := subsingleton_of_fineEnergyCertificates (F c) (hconnected c) (hcert c)
  apply Set.Subset.antisymm
  · intro z hz
    exact Set.mem_singleton_iff.mpr (hs hz (hself c))
  · exact Set.singleton_subset_iff.mpr (hself c)

/-- A quotient with connected fibers satisfying the energy criterion is a
homeomorphism.  This is the decomposition-theoretic form of the reduction. -/
theorem isHomeomorph_of_quotient_fiber_energy_certificates
    {Y : Type*} [TopologicalSpace Y] (q : X → Y)
    (hq : IsQuotientMap q)
    (hconnected : ∀ b, IsPreconnected {x : X | q x = b})
    (hcert : ∀ b, FineEnergyCertificates {x : X | q x = b}) :
    IsHomeomorph q := by
  exact isHomeomorph_iff_isQuotientMap_injective.mpr
    ⟨hq, injective_of_fiber_energy_certificates q hconnected hcert⟩

/-- Compact-to-Hausdorff version: continuity and surjectivity supply the
topological quotient interface, while the finite certificates give injectivity. -/
theorem isHomeomorph_of_compact_fiber_energy_certificates
    {Y : Type*} [TopologicalSpace Y] [T2Space Y] [CompactSpace X]
    (q : X → Y) (hq : Continuous q) (hsurj : Function.Surjective q)
    (hconnected : ∀ b, IsPreconnected {x : X | q x = b})
    (hcert : ∀ b, FineEnergyCertificates {x : X | q x = b}) :
    IsHomeomorph q := by
  exact isHomeomorph_iff_continuous_bijective.mpr
    ⟨hq, injective_of_fiber_energy_certificates q hconnected hcert, hsurj⟩

/-- Local connectivity lifts from a locally connected quotient when every
connected fiber has arbitrarily fine low-energy finite certificates. -/
theorem locallyConnectedSpace_of_quotient_fiber_energy_certificates
    {Y : Type*} [TopologicalSpace Y] [LocallyConnectedSpace Y]
    (q : X → Y) (hq : IsQuotientMap q)
    (hconnected : ∀ b, IsPreconnected {x : X | q x = b})
    (hcert : ∀ b, FineEnergyCertificates {x : X | q x = b}) :
    LocallyConnectedSpace X := by
  exact (isHomeomorph_of_quotient_fiber_energy_certificates
    q hq hconnected hcert).isOpenEmbedding.locallyConnectedSpace

/-- The complete compact decomposition criterion, with all analytic work
isolated in the explicitly quantified finite fiber certificates. -/
theorem locallyConnectedSpace_of_compact_fiber_energy_certificates
    {Y : Type*} [TopologicalSpace Y] [T2Space Y] [LocallyConnectedSpace Y]
    [CompactSpace X] (q : X → Y) (hq : Continuous q)
    (hsurj : Function.Surjective q)
    (hconnected : ∀ b, IsPreconnected {x : X | q x = b})
    (hcert : ∀ b, FineEnergyCertificates {x : X | q x = b}) :
    LocallyConnectedSpace X := by
  exact (isHomeomorph_of_compact_fiber_energy_certificates
    q hq hsurj hconnected hcert).isOpenEmbedding.locallyConnectedSpace

/-- A direct local-connectivity criterion requiring no quotient construction.
At every point and target scale, it suffices to certify one connected
neighborhood by a finite cover whose radius-energy product lies below the
cubic target threshold.  The neighborhood need not be known in advance to
have small diameter. -/
theorem locallyConnectedSpace_of_local_energy_certificates
    (hcert : ∀ x : X, ∀ ε : ℝ, 0 < ε →
      ∃ (K : Set X) (n : ℕ) (s : Fin n → X) (a : X) (r : ℝ),
        K ∈ 𝓝 x ∧ IsPreconnected K ∧ 0 < r ∧ r ≤ ε / 8 ∧
          1024 * r * energy s a < ε ^ 3 ∧
            ∀ z ∈ K, ∃ i, dist z (s i) ≤ r) :
    LocallyConnectedSpace X := by
  apply locallyConnectedSpace_iff_connected_subsets.mpr
  intro x U hU
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hU
  obtain ⟨K, n, s, a, r, hKn, hK, hr, hscale, hcost, hcover⟩ :=
    hcert x ε hε
  refine ⟨K, hKn, hK, ?_⟩
  intro z hz
  apply hball
  change dist z x < ε
  by_contra hnot
  have hdist : ε ≤ dist z x := le_of_not_gt hnot
  have hx : x ∈ K := mem_of_mem_nhds hKn
  have hrD : r ≤ dist z x / 8 := by linarith
  have hbound :=
    connected_cubic_energy_bound K hK s a r hr hcover z x hz hx hrD
  have hfactor :
      0 ≤ (dist z x - ε) *
        (dist z x ^ 2 + dist z x * ε + ε ^ 2) := by
    apply mul_nonneg
    · exact sub_nonneg.mpr hdist
    · positivity
  nlinarith

end Loops.FiberSampling

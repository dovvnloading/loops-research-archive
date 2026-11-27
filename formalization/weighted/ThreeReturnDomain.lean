import LimitingCrestQuadraticReturn
import QuadraticCylinderCensus

/-!
# The canonical actual three-return source component

The source is the component containing zero of the complete polynomial
pullback of a fixed disk.  A whole-circle barrier traps its closure, and
properness and openness of the actual polynomial give the whole target
as its image.  No source component or neighborhood is supplied as data.
-/

namespace ThreeReturnDomain

open Set Function Metric Topology
open LimitingCrestQuadraticReturn LoopsQuadraticCylinderCensus

noncomputable section

def threeReturn (c : ℝ) (p : ℕ) : ℂ → ℂ :=
  (normalizedReturn c p)^[3]

def source (c : ℝ) (p : ℕ) : Set ℂ :=
  connectedComponentIn (threeReturn c p ⁻¹' ball 0 (1/6)) 0

private theorem component_inside_barrier (f : ℂ → ℂ) (r R : ℝ)
    (hr : 0 < r) (hzero : ‖f 0‖ < R)
    (hbarrier : ∀ z : ℂ, ‖z‖ = r → R < ‖f z‖) :
    connectedComponentIn (f ⁻¹' ball 0 R) 0 ⊆ ball 0 r := by
  let C := connectedComponentIn (f ⁻¹' ball 0 R) 0
  have h0 : (0 : ℂ) ∈ C := mem_connectedComponentIn (by simpa using hzero)
  intro z hz
  rw [mem_ball_zero_iff]
  by_contra! hzbig
  have hpre : IsPreconnected C := isPreconnected_connectedComponentIn
  have hin : r ∈ Icc (‖(0 : ℂ)‖) ‖z‖ := by simpa using And.intro hr.le hzbig
  obtain ⟨w, hw, hwr⟩ := hpre.intermediate_value h0 hz continuous_norm.continuousOn hin
  have hsmall : ‖f w‖ < R := by
    have h := connectedComponentIn_subset (f ⁻¹' ball 0 R) 0 hw
    simpa using h
  exact (not_lt_of_ge (hbarrier w hwr).le) hsmall

/-- The actual closure is strictly inside the inner barrier, with a
compactness certificate.  The conclusion concerns the whole selected
component of the complete pullback. -/
theorem component_closure_inside_barrier (f : ℂ → ℂ) (hf : Continuous f)
    (r R : ℝ) (hr : 0 < r) (hzero : ‖f 0‖ < R)
    (hbarrier : ∀ z : ℂ, ‖z‖ = r → R < ‖f z‖) :
    closure (connectedComponentIn (f ⁻¹' ball 0 R) 0) ⊆ ball 0 r ∧
    IsCompact (closure (connectedComponentIn (f ⁻¹' ball 0 R) 0)) := by
  let C := connectedComponentIn (f ⁻¹' ball 0 R) 0
  have hsub : C ⊆ ball 0 r := component_inside_barrier f r R hr hzero hbarrier
  have hcl : closure C ⊆ closedBall 0 r :=
    isClosed_closedBall.closure_subset_iff.mpr (hsub.trans ball_subset_closedBall)
  have hvalues : closure C ⊆ f ⁻¹' closedBall 0 R :=
    (isClosed_closedBall.preimage hf).closure_subset_iff.mpr (by
      intro z hz
      change f z ∈ closedBall 0 R
      exact ball_subset_closedBall (connectedComponentIn_subset (f ⁻¹' ball 0 R) 0 hz))
  refine ⟨?_, (isCompact_closedBall (0 : ℂ) r).of_isClosed_subset isClosed_closure hcl⟩
  intro z hz
  have hzn : ‖z‖ ≤ r := by simpa using hcl hz
  have hfz : ‖f z‖ ≤ R := by simpa using hvalues hz
  have hne : ‖z‖ ≠ r := by
    intro heq
    exact (not_lt_of_ge hfz) (hbarrier z heq)
  simpa using lt_of_le_of_ne hzn hne

private theorem component_compact_preimage (f : ℂ → ℂ) (hf : IsProperMap f)
    (V K : Set ℂ) (x : ℂ) (hVo : IsOpen V) (hK : IsCompact K) (hKV : K ⊆ V) :
    IsCompact (connectedComponentIn (f ⁻¹' V) x ∩ f ⁻¹' K) := by
  let C := connectedComponentIn (f ⁻¹' V) x
  have hrel := open_component_relative_closed (f ⁻¹' V) (hVo.preimage hf.continuous) x
  have he : C ∩ f ⁻¹' K = closure C ∩ f ⁻¹' K := by
    apply Subset.antisymm
    · intro z hz
      exact ⟨subset_closure hz.1, hz.2⟩
    · intro z hz
      exact ⟨hrel ⟨hz.1, hKV hz.2⟩, hz.2⟩
  rw [show connectedComponentIn (f ⁻¹' V) x = C from rfl, he]
  exact (hf.isCompact_preimage hK).of_isClosed_subset
    (isClosed_closure.inter (hK.isClosed.preimage hf.continuous)) (fun _ hz => hz.2)

/-- Properness is proved in the literal source and target subspaces. -/
theorem component_proper (f : ℂ → ℂ) (hf : IsProperMap f)
    (V : Set ℂ) (x : ℂ) (hVo : IsOpen V) :
    IsProperMap (fun z : connectedComponentIn (f ⁻¹' V) x =>
      (⟨f z, connectedComponentIn_subset (f ⁻¹' V) x z.property⟩ : V)) := by
  let C := connectedComponentIn (f ⁻¹' V) x
  let g : C → V := fun z => ⟨f z, connectedComponentIn_subset (f ⁻¹' V) x z.property⟩
  change IsProperMap g
  apply isProperMap_iff_isCompact_preimage.mpr
  refine ⟨(hf.continuous.comp continuous_subtype_val).subtype_mk _, ?_⟩
  intro K hK
  let L : Set ℂ := ((↑) : V → ℂ) '' K
  have hLc : IsCompact L := hK.image continuous_subtype_val
  have hLV : L ⊆ V := by
    rintro _ ⟨w, _, rfl⟩
    exact w.property
  have hp := component_compact_preimage f hf V L x hVo hLc hLV
  have hsub : C ∩ f ⁻¹' L ⊆ range ((↑) : C → ℂ) := by
    rw [Subtype.range_coe]
    exact inter_subset_left
  have he : g ⁻¹' K = ((↑) : C → ℂ) ⁻¹' (C ∩ f ⁻¹' L) := by
    ext z
    constructor
    · intro hz
      exact ⟨z.property, ⟨g z, hz, rfl⟩⟩
    · rintro ⟨_, ⟨w, hw, heq⟩⟩
      have hwg : w = g z := Subtype.ext heq
      change g z ∈ K
      exact hwg ▸ hw
  rw [he]
  exact IsInducing.subtypeVal.isCompact_preimage' hp hsub

theorem normalized_return_proper (c : ℝ) (p : ℕ)
    (hd : criticalValue c p ≠ 0) : IsProperMap (normalizedReturn c p) := by
  have hdC : (criticalValue c p : ℂ) ≠ 0 := by exact_mod_cast hd
  have hpoly : IsProperMap ((quadraticMap c)^[p]) :=
    quadratic_iterate_proper (c : ℂ) p
  have h := (Homeomorph.mulLeft₀ ((criticalValue c p : ℂ)⁻¹)
      (inv_ne_zero hdC)).isProperMap.comp
    (hpoly.comp (Homeomorph.mulLeft₀ (criticalValue c p : ℂ) hdC).isProperMap)
  change IsProperMap (fun z : ℂ => (criticalValue c p : ℂ)⁻¹ *
    ((quadraticMap c)^[p]) ((criticalValue c p : ℂ) * z)) at h
  convert h using 1
  funext z
  simp only [normalizedReturn, div_eq_mul_inv]
  ring

theorem normalized_return_open (c : ℝ) (p : ℕ)
    (hd : criticalValue c p ≠ 0) : IsOpenMap (normalizedReturn c p) := by
  have hdC : (criticalValue c p : ℂ) ≠ 0 := by exact_mod_cast hd
  have hpoly : IsOpenMap ((quadraticMap c)^[p]) :=
    quadratic_iterate_open (c : ℂ) p
  have h := (Homeomorph.mulLeft₀ ((criticalValue c p : ℂ)⁻¹)
      (inv_ne_zero hdC)).isOpenMap.comp
    (hpoly.comp (Homeomorph.mulLeft₀ (criticalValue c p : ℂ) hdC).isOpenMap)
  change IsOpenMap (fun z : ℂ => (criticalValue c p : ℂ)⁻¹ *
    ((quadraticMap c)^[p]) ((criticalValue c p : ℂ) * z)) at h
  convert h using 1
  funext z
  simp only [normalizedReturn, div_eq_mul_inv]
  ring

theorem threeReturn_proper (c : ℝ) (p : ℕ)
    (hd : criticalValue c p ≠ 0) : IsProperMap (threeReturn c p) := by
  have h := normalized_return_proper c p hd
  simpa [threeReturn, iterate_succ_apply', Function.comp_def] using h.comp (h.comp h)

theorem threeReturn_open (c : ℝ) (p : ℕ)
    (hd : criticalValue c p ≠ 0) : IsOpenMap (threeReturn c p) := by
  have h := normalized_return_open c p hd
  simpa [threeReturn, iterate_succ_apply', Function.comp_def] using h.comp (h.comp h)

/-- The canonical component covers every point of the fixed target disk. -/
theorem source_image (c : ℝ) (p : ℕ) (hd : criticalValue c p ≠ 0)
    (hzero : ‖threeReturn c p 0‖ < 1/6) :
    threeReturn c p '' source c p = ball 0 (1/6) := by
  let f := threeReturn c p
  have hp := threeReturn_proper c p hd
  exact localized_component_image f (f ⁻¹' ball 0 (1/6)) (ball 0 (1/6))
    (threeReturn_open c p hd) hp.isClosedMap (isOpen_ball.preimage hp.continuous)
    (convex_ball (0 : ℂ) (1/6)).isPreconnected
    (fun _ hz => hz) (fun _ hz => hz.2) 0 (by simpa [f] using hzero)

theorem normalized_return_even (c : ℝ) (p : ℕ) (hp : 0 < p) (z : ℂ) :
    normalizedReturn c p (-z) = normalizedReturn c p z := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hp)
  simp only [normalizedReturn, iterate_succ_apply, quadraticMap, mul_neg, neg_sq]

theorem threeReturn_even (c : ℝ) (p : ℕ) (hp : 0 < p) (z : ℂ) :
    threeReturn c p (-z) = threeReturn c p z := by
  change normalizedReturn c p (normalizedReturn c p (normalizedReturn c p (-z))) = _
  rw [normalized_return_even c p hp]
  rfl

/-- The canonical central component retains both signed sheets. -/
theorem source_symmetric (c : ℝ) (p : ℕ) (hp : 0 < p)
    (hzero : ‖threeReturn c p 0‖ < 1/6) :
    ∀ z ∈ source c p, -z ∈ source c p := by
  have h0 : (0 : ℂ) ∈ source c p := mem_connectedComponentIn (by simpa using hzero)
  have hconn : IsPreconnected ((fun z : ℂ => -z) '' source c p) :=
    isPreconnected_connectedComponentIn.image _ continuous_neg.continuousOn
  have hhit : (0 : ℂ) ∈ (fun z : ℂ => -z) '' source c p := ⟨0, h0, neg_zero⟩
  have hsub : (fun z : ℂ => -z) '' source c p ⊆
      threeReturn c p ⁻¹' ball 0 (1/6) := by
    rintro _ ⟨z, hz, rfl⟩
    change threeReturn c p (-z) ∈ ball 0 (1/6)
    rw [threeReturn_even c p hp]
    exact connectedComponentIn_subset (threeReturn c p ⁻¹' ball 0 (1/6)) 0 hz
  have h := hconn.subset_connectedComponentIn hhit hsub
  intro z hz
  exact h ⟨z, hz, rfl⟩

end
end ThreeReturnDomain

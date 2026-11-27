import QuadraticLocalDeckAction
import PowerMapRigidity

/-!
# Complete local sheet symmetry classification for quadratic iterates

Continuity away from the branch anchor already forces a fiber-preserving
self-map to have one constant root-of-unity phase. Such maps are therefore
analytic and bijective, and there are exactly as many distinct restrictions
as the actual critical-visit multiplicity. No analyticity or injectivity of
the candidate self-map is assumed.
-/

namespace LoopsQuadraticLocalDeckRigidity

open Set Function Filter Polynomial
open scoped Topology
open QuadraticEscape LoopsTelescopeRamification
open LoopsQuadraticLocalDeckAction LoopsPowerMapRigidity

namespace PowerChart

variable {f : ℂ → ℂ} {x : ℂ} {m : ℕ} (C : PowerChart f x m)

/-- A continuous choice of sheet on the punctured physical neighborhood
cannot switch its root-of-unity phase. The anchor value is forced by the
fiber equation, so continuity there is not an assumption. -/
theorem continuous_fiber_preserver_eq_deck (T : ℂ → ℂ)
    (hT : ContinuousOn T (C.source \ {x}))
    (hmap : MapsTo T C.source C.source)
    (hf : ∀ z ∈ C.source, f (T z) = f z) :
    ∃! ζ : ℂ, ζ^m = 1 ∧ EqOn T (C.deck ζ) C.source := by
  let g : ℂ → ℂ := fun w => C.coord (T (C.inv w))
  have hinv : MapsTo C.inv (Metric.ball (0 : ℂ) C.r \ {0}) (C.source \ {x}) := by
    intro w hw
    refine ⟨C.inv_mapsTo hw.1, ?_⟩
    intro he
    have he' : C.inv w = x := Set.mem_singleton_iff.mp he
    have hw0 : w = 0 := by
      calc
        w = C.coord (C.inv w) := (C.right_inv hw.1).symm
        _ = 0 := by rw [he', C.coord_center]
    exact hw.2 (Set.mem_singleton_iff.mpr hw0)
  have hg : ContinuousOn g (Metric.ball (0 : ℂ) C.r \ {0}) := by
    exact C.coord_analytic.continuousOn.comp
      (hT.comp (C.inv_analytic.continuousOn.mono diff_subset) hinv)
      (fun w hw => hmap (C.inv_mapsTo hw.1))
  have hpow (w : ℂ) (hw : w ∈ Metric.ball (0 : ℂ) C.r) : (g w)^m = w^m := by
    apply mul_left_cancel₀ C.a_ne_zero
    calc
      C.a * (g w)^m = f (T (C.inv w)) - f x :=
        (C.normal_form _ (hmap (C.inv_mapsTo hw))).symm
      _ = f (C.inv w) - f x := by rw [hf _ (C.inv_mapsTo hw)]
      _ = C.a * w^m := by
        rw [C.normal_form _ (C.inv_mapsTo hw), C.right_inv hw]
  obtain ⟨ζ, hζ, hgζ⟩ :=
    power_preserving_rigidity m C.degree_pos C.r C.radius_pos g hg hpow
  have heq : EqOn T (C.deck ζ) C.source := by
    intro z hz
    have hc := hgζ (C.coord z) (C.coord_mapsTo hz)
    change C.coord (T (C.inv (C.coord z))) = ζ*C.coord z at hc
    rw [C.left_inv hz] at hc
    calc
      T z = C.inv (C.coord (T z)) := (C.left_inv (hmap hz)).symm
      _ = C.deck ζ z := congrArg C.inv hc
  refine ⟨ζ, ⟨hζ, heq⟩, ?_⟩
  intro η hη
  have he : C.deck η =ᶠ[𝓝 x] C.deck ζ := by
    filter_upwards [C.isOpen_source.mem_nhds C.mem_source] with z hz
    exact (hη.2 z hz).symm.trans (heq z hz)
  exact (C.deck_deriv_center η).unique
    ((C.deck_deriv_center ζ).congr_of_eventuallyEq he)

/-- The complete fiber equation and continuity away from the anchor
automatically upgrade a candidate map to an analytic automorphism. -/
theorem continuous_fiber_preserver_analytic_bijective (T : ℂ → ℂ)
    (hT : ContinuousOn T (C.source \ {x}))
    (hmap : MapsTo T C.source C.source)
    (hf : ∀ z ∈ C.source, f (T z) = f z) :
    AnalyticOnNhd ℂ T C.source ∧ BijOn T C.source C.source := by
  obtain ⟨ζ, ⟨hζ, heq⟩, _⟩ := C.continuous_fiber_preserver_eq_deck T hT hmap hf
  have hζ0 : ζ ≠ 0 := by
    intro h
    rw [h, zero_pow (Nat.ne_of_gt C.degree_pos)] at hζ
    exact zero_ne_one hζ
  have hinv : (ζ⁻¹)^m = 1 := by rw [inv_pow, hζ, inv_one]
  refine ⟨(C.deck_analytic ζ hζ).congr C.isOpen_source heq.symm, hmap, ?_, ?_⟩
  · intro z hz w hw he
    apply C.coord_injOn hz hw
    rw [heq z hz, heq w hw] at he
    have hc := congrArg C.coord he
    rw [C.deck_coord ζ z hζ hz, C.deck_coord ζ w hζ hw] at hc
    exact mul_left_cancel₀ hζ0 hc
  · intro w hw
    refine ⟨C.deck ζ⁻¹ w, C.deck_mem ζ⁻¹ w hinv hw, ?_⟩
    rw [heq _ (C.deck_mem ζ⁻¹ w hinv hw), ← C.deck_mul ζ ζ⁻¹ w hinv hw,
      mul_inv_cancel₀ hζ0, C.deck_one w hw]

/-- Distinct analytic sheet symmetries are distinguished by their
derivatives at the branch anchor. This removes coordinate-label ambiguity. -/
theorem continuous_fiber_preserver_deriv (T : ℂ → ℂ)
    (hT : ContinuousOn T (C.source \ {x}))
    (hmap : MapsTo T C.source C.source)
    (hf : ∀ z ∈ C.source, f (T z) = f z) :
    (deriv T x)^m = 1 ∧ EqOn T (C.deck (deriv T x)) C.source := by
  obtain ⟨ζ, ⟨hζ, heq⟩, _⟩ := C.continuous_fiber_preserver_eq_deck T hT hmap hf
  have he : T =ᶠ[𝓝 x] C.deck ζ := by
    filter_upwards [C.isOpen_source.mem_nhds C.mem_source] with z hz
    exact heq z hz
  have hd : deriv T x = ζ :=
    ((C.deck_deriv_center ζ).congr_of_eventuallyEq he).deriv
  simpa only [hd] using And.intro hζ heq

/-- The finite set of actual source restrictions of all local sheet
symmetries. Arbitrary extensions outside the source are not counted. -/
noncomputable def deckMaps : Finset (C.source → ℂ) := by
  classical
  exact (nthRootsFinset m (1 : ℂ)).image (fun ζ z => C.deck ζ z)

/-- There are exactly m distinct local sheet symmetries, including
the degree-one case. Each is an actual function on the physical source. -/
theorem deckMaps_card : C.deckMaps.card = m := by
  classical
  rw [deckMaps, Finset.card_image_of_injOn]
  · exact LoopsQuadraticLocalFiberCensus.complex_nthRootsFinset_card
      m C.degree_pos 1 one_ne_zero
  · intro ζ _ η _ heq
    have he : C.deck ζ =ᶠ[𝓝 x] C.deck η := by
      filter_upwards [C.isOpen_source.mem_nhds C.mem_source] with z hz
      exact congrFun heq ⟨z, hz⟩
    exact (C.deck_deriv_center ζ).unique
      ((C.deck_deriv_center η).congr_of_eventuallyEq he)

/-- The finite list exhausts all continuous fiber-preserving self-maps;
no assumed bijectivity, analyticity, or prior deck marking is needed. -/
theorem mem_deckMaps_iff (T : ℂ → ℂ) :
    (fun z : C.source => T z) ∈ C.deckMaps ↔
      ContinuousOn T C.source ∧ MapsTo T C.source C.source ∧
        ∀ z ∈ C.source, f (T z) = f z := by
  classical
  rw [deckMaps, Finset.mem_image]
  constructor
  · rintro ⟨ζ, hζ, he⟩
    have hroot := (mem_nthRootsFinset C.degree_pos (1 : ℂ)).mp hζ
    have heq : EqOn T (C.deck ζ) C.source := by
      intro z hz
      exact (congrFun he ⟨z, hz⟩).symm
    refine ⟨(C.deck_analytic ζ hroot).continuousOn.congr heq, ?_, ?_⟩
    · intro z hz
      rw [heq z hz]
      exact C.deck_mem ζ z hroot hz
    · intro z hz
      rw [heq z hz]
      exact C.deck_preserves ζ z hroot hz
  · rintro ⟨hT, hmap, hf⟩
    obtain ⟨ζ, ⟨hζ, heq⟩, _⟩ :=
      C.continuous_fiber_preserver_eq_deck T (hT.mono diff_subset) hmap hf
    refine ⟨ζ, (mem_nthRootsFinset C.degree_pos (1 : ℂ)).mpr hζ, ?_⟩
    funext z
    exact (heq z z.property).symm

end PowerChart

/-- Unconditional local classification for every actual quadratic
parameter, anchor, and finite iterate. The only map-specific hypotheses
are preservation of this constructed source and of the actual fibers,
and continuity off the anchor. -/
theorem quadratic_local_deck_classification (c x : ℂ) (n : ℕ) :
    ∃ C : PowerChart (orbit c n) x (2^criticalVisits c x n),
      C.deckMaps.card = 2^criticalVisits c x n ∧
      ∀ T : ℂ → ℂ, ContinuousOn T (C.source \ {x}) →
        MapsTo T C.source C.source →
        (∀ z ∈ C.source, orbit c n (T z) = orbit c n z) →
        ∃! ζ : ℂ, ζ^(2^criticalVisits c x n) = 1 ∧ EqOn T (C.deck ζ) C.source := by
  obtain ⟨C⟩ := exists_quadratic_powerChart c x n
  exact ⟨C, C.deckMaps_card, fun T hT hmap hf =>
    C.continuous_fiber_preserver_eq_deck T hT hmap hf⟩

end LoopsQuadraticLocalDeckRigidity

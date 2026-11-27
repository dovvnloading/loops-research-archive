import ThreeReturnRealization
import StationaryGeometricFibers
import LeastSaturatedCarrier

/-!
# The connected filled core of the constructed actual return

The retained core consists of exactly those points whose complete orbit
under the actual three-return remains in its canonical source. Compact
connected finite pullbacks converge to this core. The critical orbit,
the two signed sheets, and source properness are proved inputs of the
actual parameter construction; no filled continuum is supplied as data.
-/

namespace ActualFilledReturn

open Set Function Metric Topology
open LimitingCrestQuadraticReturn NearTwoTip
open ThreeReturnDomain ThreeReturnDegree ThreeReturnCollar ThreeReturnRealization
open ThreeReturnPhysical
open LoopsQuadraticCylinderCensus LoopsStationaryGeometricFibers

noncomputable section

/-- The full nonescaping set of the literal normalized three-return
in its canonically selected source. -/
def normalizedCore (c : ℝ) (p : ℕ) : Set ℂ :=
  {z | ∀ n : ℕ, ((threeReturn c p)^[n]) z ∈ source c p}

/-- The same retained core in the original quadratic plane. -/
def physicalCore (c : ℝ) (p : ℕ) : Set ℂ :=
  (fun z : ℂ => (criticalValue c p : ℂ)*z) '' normalizedCore c p

private def finiteStage (c : ℝ) (p : ℕ) : ℕ → Set ℂ
  | 0 => closure (source c p)
  | n+1 => closure (source c p) ∩ threeReturn c p ⁻¹' finiteStage c p n

/-- Every retained point already belongs to the actual source component. -/
theorem normalizedCore_subset_source (c : ℝ) (p : ℕ) :
    normalizedCore c p ⊆ source c p := by
  intro z hz
  exact hz 0

private theorem closure_source_subset_target {c : ℝ} {p : ℕ}
    (hc : CanonicalCollar c p) :
    closure (source c p) ⊆ ball (0 : ℂ) (1/6) := by
  intro z hz
  have hn : ‖z‖ < 3/20 := by simpa using hc.closure_inside hz
  rw [mem_ball_zero_iff]
  linarith

private theorem finiteStage_subset_closure (c : ℝ) (p n : ℕ) :
    finiteStage c p n ⊆ closure (source c p) := by
  cases n with
  | zero => exact Subset.refl _
  | succ n => exact inter_subset_left

private theorem finiteStage_antitone (c : ℝ) (p : ℕ) :
    Antitone (finiteStage c p) := by
  apply antitone_nat_of_succ_le
  intro n
  induction n with
  | zero => exact inter_subset_left
  | succ n ih =>
    intro z hz
    exact ⟨hz.1, ih hz.2⟩

private theorem finiteStage_compact {c : ℝ} {p : ℕ}
    (hc : CanonicalCollar c p) (n : ℕ) : IsCompact (finiteStage c p n) := by
  induction n with
  | zero => exact hc.compact_closure
  | succ n ih =>
    exact hc.compact_closure.inter_right
      (ih.isClosed.preimage (threeReturn_proper c p hc.scale_pos.ne').continuous)

private theorem critical_orbit_mem_stage {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) (n m : ℕ) :
    ((threeReturn c p)^[m]) 0 ∈ finiteStage c p n := by
  have hcan := actual_canonical_collar hp hc
  have htrap := (critical_orbit_trapped c p (by omega) hcan hc.2.2.2.2.1
    (actual_three_return_collision_iff hp hc)).2.2.1
  induction n generalizing m with
  | zero => exact subset_closure (htrap m)
  | succ n ih =>
    refine ⟨subset_closure (htrap m), ?_⟩
    change threeReturn c p (((threeReturn c p)^[m]) 0) ∈ finiteStage c p n
    simpa only [iterate_succ_apply'] using ih (m+1)

private theorem source_pullback_preconnected {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) (K : Set ℂ) (hK : IsPreconnected K)
    (hKV : K ⊆ ball (0 : ℂ) (1/6)) (hcrit : threeReturn c p 0 ∈ K) :
    IsPreconnected (source c p ∩ threeReturn c p ⁻¹' K) := by
  let W := source c p
  let V := ball (0 : ℂ) (1/6)
  let f : W → V := sourceMap c p
  have hcan := actual_canonical_collar hp hc
  have hzero := collar_critical_value hcan
  let σ : W → W := fun z =>
    ⟨-(z : ℂ), source_symmetric c p (by omega) hzero z z.property⟩
  have hσc : Continuous σ :=
    (continuous_subtype_val.neg : Continuous (fun z : W => -(z : ℂ))).subtype_mk _
  have hsurj : Surjective f := by
    intro y
    have hy : (y : ℂ) ∈ threeReturn c p '' source c p := by
      rw [hcan.image_eq]
      exact y.property
    obtain ⟨z, hz, he⟩ := hy
    exact ⟨⟨z, hz⟩, Subtype.ext he⟩
  have hσ : ∀ z, f (σ z) = f z := by
    intro z
    exact Subtype.ext (threeReturn_even c p (by omega) z)
  have hnorm (z : W) : ‖(z : ℂ)‖ ≤ 1/6 := by
    have hn : ‖(z : ℂ)‖ < 3/20 := by
      simpa using hcan.closure_inside (subset_closure z.property)
    linarith
  have hfib : ∀ x z, f x = f z → z = x ∨ z = σ x := by
    intro x z he
    have he' : threeReturn c p z = threeReturn c p x :=
      (congrArg (fun y : V => (y : ℂ)) he).symm
    rcases (actual_three_return_collision_iff hp hc (hnorm z) (hnorm x)).mp he'
      with hz | hz
    · exact Or.inl (Subtype.ext hz)
    · exact Or.inr (Subtype.ext hz)
  let S : Set V := ((↑) : V → ℂ) ⁻¹' K
  have hSimage : ((↑) : V → ℂ) '' S = K := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact hw
    · intro hz
      exact ⟨⟨z, hKV hz⟩, hz, rfl⟩
  have hS : IsPreconnected S :=
    IsInducing.subtypeVal.isPreconnected_image.mp (hSimage.symm ▸ hK)
  let a : W := ⟨0, hcan.zero_mem⟩
  have hfix : σ a = a := by apply Subtype.ext; exact neg_zero
  have haS : f a ∈ S := hcrit
  have hpre := critical_preimage_preconnected f σ hcan.proper.isClosedMap
    hσc hsurj hσ hfib S hS a hfix haS
  have himage : ((↑) : W → ℂ) '' (f ⁻¹' S) =
      source c p ∩ threeReturn c p ⁻¹' K := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w.property, hw⟩
    · rintro ⟨hz, hHz⟩
      exact ⟨⟨z, hz⟩, hHz, rfl⟩
  rw [← himage]
  exact hpre.image _ continuous_subtype_val.continuousOn

private theorem finiteStage_succ_eq {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) (n : ℕ) :
    finiteStage c p (n+1) = source c p ∩ threeReturn c p ⁻¹' finiteStage c p n := by
  have hcan := actual_canonical_collar hp hc
  have hrel := open_component_relative_closed
    (threeReturn c p ⁻¹' ball 0 (1/6))
    (isOpen_ball.preimage (threeReturn_proper c p hc.2.1.ne').continuous) 0
  apply Subset.antisymm
  · intro z hz
    exact ⟨hrel ⟨hz.1, closure_source_subset_target hcan
      (finiteStage_subset_closure c p n hz.2)⟩, hz.2⟩
  · intro z hz
    exact ⟨subset_closure hz.1, hz.2⟩

private theorem finiteStage_preconnected {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) (n : ℕ) : IsPreconnected (finiteStage c p n) := by
  have hcan := actual_canonical_collar hp hc
  induction n with
  | zero => exact hcan.isConnected_source.closure.isPreconnected
  | succ n ih =>
    rw [finiteStage_succ_eq hp hc]
    exact source_pullback_preconnected hp hc _ ih
      ((finiteStage_subset_closure c p n).trans (closure_source_subset_target hcan))
      (by simpa only [iterate_one] using critical_orbit_mem_stage hp hc n 1)

private theorem normalizedCore_eq_iInter {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) : normalizedCore c p = ⋂ n, finiteStage c p n := by
  have hcan := actual_canonical_collar hp hc
  have hforward (n : ℕ) : ∀ z ∈ normalizedCore c p, z ∈ finiteStage c p n := by
    induction n with
    | zero => intro z hz; exact subset_closure (hz 0)
    | succ n ih =>
      intro z hz
      refine ⟨subset_closure (hz 0), ih _ ?_⟩
      intro m
      simpa only [iterate_succ_apply] using hz (m+1)
  have hiter (n : ℕ) : ∀ z : ℂ, (∀ m, z ∈ finiteStage c p m) →
      ((threeReturn c p)^[n]) z ∈ closure (source c p) := by
    induction n with
    | zero => intro z hz; exact hz 0
    | succ n ih =>
      intro z hz
      have h := ih (threeReturn c p z) (fun m => (hz (m+1)).2)
      simpa only [iterate_succ_apply] using h
  apply Subset.antisymm
  · intro z hz
    exact mem_iInter.mpr (fun n => hforward n z hz)
  · intro z hz n
    have hrel := open_component_relative_closed
      (threeReturn c p ⁻¹' ball 0 (1/6))
      (isOpen_ball.preimage (threeReturn_proper c p hc.2.1.ne').continuous) 0
    refine hrel ⟨hiter n z (mem_iInter.mp hz), ?_⟩
    have hn := closure_source_subset_target hcan (hiter (n+1) z (mem_iInter.mp hz))
    change threeReturn c p (((threeReturn c p)^[n]) z) ∈ ball 0 (1/6)
    simpa only [iterate_succ_apply'] using hn

/-- The actual critical orbit never leaves the constructed normalized core. -/
theorem actual_normalizedCore_zero {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) : (0 : ℂ) ∈ normalizedCore c p := by
  exact (critical_orbit_trapped c p (by omega) (actual_canonical_collar hp hc)
    hc.2.2.2.2.1 (actual_three_return_collision_iff hp hc)).2.2.1

/-- Compactness includes boundary exclusion: the closed finite-pullback
limit is exactly the set staying in the open source forever. -/
theorem actual_normalizedCore_compact {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) : IsCompact (normalizedCore c p) := by
  rw [normalizedCore_eq_iInter hp hc]
  have hcan := actual_canonical_collar hp hc
  exact hcan.compact_closure.of_isClosed_subset
    (isClosed_iInter (fun n => (finiteStage_compact hcan n).isClosed))
    (iInter_subset (finiteStage c p) 0)

/-- Connectedness is constructed by pulling back the complete critical
orbit through the actual signed two-sheet map at every finite depth. -/
theorem actual_normalizedCore_connected {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) : IsConnected (normalizedCore c p) := by
  refine ⟨⟨0, actual_normalizedCore_zero hp hc⟩, ?_⟩
  rw [normalizedCore_eq_iInter hp hc]
  have hcan := actual_canonical_collar hp hc
  exact LoopsLeastCarrier.directed_carrier_preconnected
    (closure (source c p)) hcan.compact_closure (finiteStage c p)
    (finiteStage_compact hcan) (finiteStage_preconnected hp hc)
    (finiteStage_subset_closure c p) (by
      intro n m
      refine ⟨max n m, ?_, ?_⟩
      · exact finiteStage_antitone c p (le_max_left n m)
      · exact finiteStage_antitone c p (le_max_right n m))

/-- Every retained point has an actual retained inverse, and the return
maps the full constructed core exactly onto itself. -/
theorem actual_normalizedCore_image {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) :
    threeReturn c p '' normalizedCore c p = normalizedCore c p := by
  apply Subset.antisymm
  · rintro _ ⟨z, hz, rfl⟩ n
    simpa only [iterate_succ_apply] using hz (n+1)
  · intro y hy
    have hcan := actual_canonical_collar hp hc
    have hyV := closure_source_subset_target hcan
      (subset_closure (normalizedCore_subset_source c p hy))
    have hyim : y ∈ threeReturn c p '' source c p := by
      rwa [hcan.image_eq]
    obtain ⟨z, hz, hzy⟩ := hyim
    refine ⟨z, ?_, hzy⟩
    intro n
    cases n with
    | zero => exact hz
    | succ n => simpa only [iterate_succ_apply, hzy] using hy n

/-- Scaling retains membership in the actual physical source. -/
theorem physicalCore_subset_source (c : ℝ) (p : ℕ) :
    physicalCore c p ⊆ physicalSource c p :=
  image_mono (normalizedCore_subset_source c p)

/-- The physical core contains the literal critical point. -/
theorem actual_physicalCore_zero {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) : (0 : ℂ) ∈ physicalCore c p :=
  ⟨0, actual_normalizedCore_zero hp hc, mul_zero _⟩

/-- The constructed actual physical core is compact. -/
theorem actual_physicalCore_compact {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) : IsCompact (physicalCore c p) :=
  (actual_normalizedCore_compact hp hc).image (continuous_const.mul continuous_id)

/-- The constructed actual physical core is connected. -/
theorem actual_physicalCore_connected {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) : IsConnected (physicalCore c p) :=
  (actual_normalizedCore_connected hp hc).image _
    (continuous_const.mul continuous_id).continuousOn

/-- The original quadratic 3p-iterate maps the physical core exactly
onto itself, with the same parameter and physical scale. -/
theorem actual_physicalCore_image {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) :
    ((quadraticMap c)^[3*p]) '' physicalCore c p = physicalCore c p := by
  have hscale := normalized_iterate_scale c p hc.2.1.ne' 3
  have hcore := actual_normalizedCore_image hp hc
  apply Subset.antisymm
  · rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    refine ⟨threeReturn c p z, ?_, hscale z⟩
    rw [← hcore]
    exact mem_image_of_mem _ hz
  · rintro _ ⟨z, hz, rfl⟩
    rw [← hcore] at hz
    obtain ⟨w, hw, hwz⟩ := hz
    refine ⟨(criticalValue c p : ℂ)*w, ⟨w, hw, rfl⟩, ?_⟩
    rw [← hscale w]
    exact congrArg (fun u : ℂ => (criticalValue c p : ℂ)*u) hwz

/-- The physical construction is exactly the literal nonescaping set
of the original 3p-return inside its actual physical source. -/
theorem physicalCore_eq_nonescaping (c : ℝ) (p : ℕ)
    (hd : criticalValue c p ≠ 0) :
    physicalCore c p =
      {z : ℂ | ∀ n : ℕ,
        ((((quadraticMap c)^[3*p])^[n]) z) ∈ physicalSource c p} := by
  let M : ℂ → ℂ := fun z => (criticalValue c p : ℂ)*z
  have hdC : (criticalValue c p : ℂ) ≠ 0 := by exact_mod_cast hd
  have hsemi : Semiconj M (threeReturn c p) ((quadraticMap c)^[3*p]) :=
    normalized_iterate_scale c p hd 3
  have hiter (n : ℕ) (z : ℂ) :
      M (((threeReturn c p)^[n]) z) =
        (((quadraticMap c)^[3*p])^[n]) (M z) :=
    (hsemi.iterate_right n) z
  apply Subset.antisymm
  · rintro _ ⟨z, hz, rfl⟩ n
    change (((quadraticMap c)^[3*p])^[n]) (M z) ∈ physicalSource c p
    rw [← hiter n z]
    exact ⟨((threeReturn c p)^[n]) z, hz n, rfl⟩
  · intro z hz
    let e := Homeomorph.mulLeft₀ (criticalValue c p : ℂ) hdC
    obtain ⟨w, hw⟩ := e.surjective z
    change M w = z at hw
    refine ⟨w, ?_, hw⟩
    intro n
    obtain ⟨u, hu, huz⟩ := hz n
    have hmw := hiter n w
    rw [hw] at hmw
    have he : u = ((threeReturn c p)^[n]) w :=
      mul_left_cancel₀ hdC (huz.trans hmw.symm)
    exact he ▸ hu

/-- The constructed physical continuum is nondegenerate: it contains
both zero and its strictly negative 3p-th critical value. -/
theorem actual_physicalCore_nontrivial {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) : (physicalCore c p).Nontrivial := by
  have hzero := actual_physicalCore_zero hp hc
  have himage := actual_physicalCore_image hp hc
  have hcrit : ((quadraticMap c)^[3*p]) 0 ∈ physicalCore c p := by
    rw [← himage]
    exact mem_image_of_mem _ hzero
  rw [ThreeReturnParent.quadratic_iterate_zero] at hcrit
  refine ⟨0, hzero, (criticalValue c (3*p) : ℂ), hcrit, ?_⟩
  intro he
  have hr := congrArg Complex.re he
  simp only [Complex.zero_re, Complex.ofReal_re] at hr
  linarith [hc.2.2.2.2.2.1]

end
end ActualFilledReturn

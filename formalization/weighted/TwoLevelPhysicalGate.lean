import TwoLevelGateDomain

/-!
# The central gate in the original polynomial coordinate

The affine scale is signed. Its absolute value controls radii, while the
original sign is retained in every map and component identity. In particular,
the complete gate disk is transported when a second return has negative scale.
-/

namespace TwoLevelPhysicalGate

open Set Function Metric Topology
open LimitingCrestQuadraticReturn ThreeReturnDomain ThreeReturnParent
open LoopsQuadraticCylinderCensus TwoLevelGateDomain

noncomputable section

def physicalTarget (c : ℝ) (n : ℕ) : Set ℂ :=
  ball 0 (|criticalValue c n|*(23/20))

def physicalGateDisk (c : ℝ) (n : ℕ) : Set ℂ :=
  {z | ‖z+((3*criticalValue c n/4 : ℝ) : ℂ)‖ ≤
    |criticalValue c n|*(133/2000)}

/-- The literal polynomial on the component of its complete physical
pullback. The component is identified with `physicalParentSource` below. -/
def physicalMap (c : ℝ) (n : ℕ) :
    connectedComponentIn (((quadraticMap c)^[n]) ⁻¹' physicalTarget c n) 0 →
      physicalTarget c n :=
  fun z => ⟨((quadraticMap c)^[n]) z,
    connectedComponentIn_subset (((quadraticMap c)^[n]) ⁻¹' physicalTarget c n)
      0 z.property⟩

theorem physical_scale_identity (c : ℝ) (n : ℕ)
    (hd : criticalValue c n ≠ 0) (z : ℂ) :
    ((quadraticMap c)^[n]) ((criticalValue c n : ℂ)*z) =
      (criticalValue c n : ℂ)*normalizedReturn c n z := by
  simpa only [one_mul, iterate_one] using
    (normalized_iterate_scale c n hd 1 z).symm

/-- Scaling identifies the entire inverse images of the prescribed disks. -/
theorem physical_pullback_image (c : ℝ) (n : ℕ)
    (hd : criticalValue c n ≠ 0) :
    (fun z : ℂ => (criticalValue c n : ℂ)*z) ''
      (normalizedReturn c n ⁻¹' ball 0 (23/20)) =
        ((quadraticMap c)^[n]) ⁻¹' physicalTarget c n := by
  have hdC : (criticalValue c n : ℂ) ≠ 0 := by exact_mod_cast hd
  have habs : 0 < |criticalValue c n| := abs_pos.mpr hd
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    have hwn : ‖normalizedReturn c n w‖ < 23/20 := by simpa using hw
    change ((quadraticMap c)^[n]) ((criticalValue c n : ℂ)*w) ∈
      ball 0 (|criticalValue c n|*(23/20))
    rw [physical_scale_identity c n hd, mem_ball_zero_iff,
      norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_lt_mul_of_pos_left hwn habs
  · intro hz
    refine ⟨z/(criticalValue c n : ℂ), ?_, ?_⟩
    · change normalizedReturn c n (z/(criticalValue c n : ℂ)) ∈ ball 0 (23/20)
      rw [mem_ball_zero_iff]
      have he : (criticalValue c n : ℂ)*(z/(criticalValue c n : ℂ)) = z := by
        field_simp [hdC]
      have hn : ‖((quadraticMap c)^[n]) z‖ < |criticalValue c n|*(23/20) := by
        simpa [physicalTarget] using hz
      rw [← he, physical_scale_identity c n hd, norm_mul,
        Complex.norm_real, Real.norm_eq_abs] at hn
      exact (mul_lt_mul_iff_right₀ habs).mp hn
    · field_simp [hdC]

/-- The actual source is exactly the central component of the complete
literal polynomial pullback, including for a negative affine scale. -/
theorem physical_source_eq_component (c : ℝ) (n : ℕ)
    (hd : criticalValue c n ≠ 0) :
    physicalParentSource c n = connectedComponentIn
      (((quadraticMap c)^[n]) ⁻¹' physicalTarget c n) 0 := by
  have hdC : (criticalValue c n : ℂ) ≠ 0 := by exact_mod_cast hd
  let e := Homeomorph.mulLeft₀ (criticalValue c n : ℂ) hdC
  have he := e.image_connectedComponentIn
    (show (0 : ℂ) ∈ normalizedReturn c n ⁻¹' ball 0 (23/20) by
      norm_num [normalized_return_zero c n hd])
  change physicalParentSource c n = connectedComponentIn
    ((fun z : ℂ => (criticalValue c n : ℂ)*z) ''
      (normalizedReturn c n ⁻¹' ball 0 (23/20)))
        ((criticalValue c n : ℂ)*0) at he
  simpa only [physical_pullback_image c n hd, mul_zero] using he

theorem physical_zero {c : ℝ} {n : ℕ} (h : CentralGate c n) :
    (0 : ℂ) ∈ physicalParentSource c n :=
  ⟨0, h.zero_mem, mul_zero _⟩

theorem physical_return_image {c : ℝ} {n : ℕ} (h : CentralGate c n) :
    ((quadraticMap c)^[n]) '' physicalParentSource c n = physicalTarget c n := by
  rw [physical_source_eq_component c n h.scale_ne]
  let F := (quadraticMap c)^[n]
  have hproper : IsProperMap F := quadratic_iterate_proper (c : ℂ) n
  have hopen : IsOpenMap F := quadratic_iterate_open (c : ℂ) n
  have h0 : (0 : ℂ) ∈ F ⁻¹' physicalTarget c n := by
    have hz := physical_zero h
    rw [physical_source_eq_component c n h.scale_ne] at hz
    exact connectedComponentIn_subset _ _ hz
  exact localized_component_image F (F ⁻¹' physicalTarget c n) (physicalTarget c n)
    hopen hproper.isClosedMap (isOpen_ball.preimage hproper.continuous)
    (convex_ball (0 : ℂ) (|criticalValue c n|*(23/20))).isPreconnected
    (fun _ hz => hz) (fun _ hz => hz.2) 0 h0

theorem physical_source_open {c : ℝ} {n : ℕ} (h : CentralGate c n) :
    IsOpen (physicalParentSource c n) := by
  have hdC : (criticalValue c n : ℂ) ≠ 0 := by exact_mod_cast h.scale_ne
  exact (Homeomorph.mulLeft₀ (criticalValue c n : ℂ) hdC).isOpenMap _ h.source_open

theorem physical_source_connected {c : ℝ} {n : ℕ} (h : CentralGate c n) :
    IsConnected (physicalParentSource c n) :=
  h.source_connected.image _ (continuous_const.mul continuous_id).continuousOn

theorem physical_closure_inside {c : ℝ} {n : ℕ} (h : CentralGate c n) :
    closure (physicalParentSource c n) ⊆ physicalTarget c n := by
  have hdC : (criticalValue c n : ℂ) ≠ 0 := by exact_mod_cast h.scale_ne
  let e := Homeomorph.mulLeft₀ (criticalValue c n : ℂ) hdC
  have he : closure (physicalParentSource c n) = e '' closure (parentSource c n) :=
    (e.image_closure (parentSource c n)).symm
  rw [he]
  rintro _ ⟨z, hz, rfl⟩
  have hn : ‖z‖ < 23/20 := by simpa using h.closure_inside hz
  change (criticalValue c n : ℂ)*z ∈ ball 0 (|criticalValue c n|*(23/20))
  rw [mem_ball_zero_iff, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_lt_mul_of_pos_left hn (abs_pos.mpr h.scale_ne)

theorem physical_quantitative_closure {c : ℝ} {n : ℕ} (h : CentralGate c n) :
    closure (physicalParentSource c n) ⊆
      ball 0 (|criticalValue c n|*(11/10)) := by
  have hdC : (criticalValue c n : ℂ) ≠ 0 := by exact_mod_cast h.scale_ne
  let e := Homeomorph.mulLeft₀ (criticalValue c n : ℂ) hdC
  have he : closure (physicalParentSource c n) = e '' closure (parentSource c n) :=
    (e.image_closure (parentSource c n)).symm
  rw [he]
  rintro _ ⟨z, hz, rfl⟩
  have hn : ‖z‖ < 11/10 := by simpa using h.quantitative_closure hz
  change (criticalValue c n : ℂ)*z ∈ ball 0 (|criticalValue c n|*(11/10))
  rw [mem_ball_zero_iff, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_lt_mul_of_pos_left hn (abs_pos.mpr h.scale_ne)

/-- The collar gap is a fixed fraction of the actual signed return's
absolute scale, including when that return lies on the opposite side. -/
theorem physical_gap {c : ℝ} {n : ℕ} (h : CentralGate c n)
    {u v : ℂ} (hu : u ∈ closure (physicalParentSource c n))
    (hv : v ∉ physicalTarget c n) :
    |criticalValue c n|/20 < dist u v := by
  have hu' : ‖u‖ < |criticalValue c n|*(11/10) := by
    simpa using physical_quantitative_closure h hu
  have hv' : |criticalValue c n|*(23/20) ≤ ‖v‖ := by
    simpa [physicalTarget] using hv
  have hnorm := norm_sub_norm_le v u
  rw [dist_eq_norm, norm_sub_rev]
  linarith only [hu', hv', hnorm]

theorem physical_compact_closure {c : ℝ} {n : ℕ} (h : CentralGate c n) :
    IsCompact (closure (physicalParentSource c n)) :=
  (isCompact_closedBall (0 : ℂ) (|criticalValue c n|*(23/20))).of_isClosed_subset
    isClosed_closure ((physical_closure_inside h).trans ball_subset_closedBall)

theorem physicalMap_proper (c : ℝ) (n : ℕ) : IsProperMap (physicalMap c n) :=
  component_proper ((quadraticMap c)^[n]) (quadratic_iterate_proper (c : ℂ) n)
    (physicalTarget c n) 0 isOpen_ball

/-- The physical disk uses the signed center and the unsigned radius. -/
theorem physical_gate_image (c : ℝ) (n : ℕ) (hd : criticalValue c n ≠ 0) :
    (fun z : ℂ => (criticalValue c n : ℂ)*z) '' gateDisk = physicalGateDisk c n := by
  have hdC : (criticalValue c n : ℂ) ≠ 0 := by exact_mod_cast hd
  have habs : 0 < |criticalValue c n| := abs_pos.mpr hd
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    have hwn : ‖w+(3/4 : ℂ)‖ ≤ (133/2000 : ℝ) := hw
    change ‖(criticalValue c n : ℂ)*w+((3*criticalValue c n/4 : ℝ) : ℂ)‖ ≤ _
    have he : (criticalValue c n : ℂ)*w+((3*criticalValue c n/4 : ℝ) : ℂ) =
        (criticalValue c n : ℂ)*(w+(3/4 : ℂ)) := by
      push_cast
      ring
    rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left hwn habs.le
  · intro hz
    refine ⟨z/(criticalValue c n : ℂ), ?_, ?_⟩
    · have he : (criticalValue c n : ℂ)*(z/(criticalValue c n : ℂ)+(3/4 : ℂ)) =
          z+((3*criticalValue c n/4 : ℝ) : ℂ) := by
        push_cast
        field_simp [hdC]
        <;> ring
      have hn : ‖(criticalValue c n : ℂ)*
          (z/(criticalValue c n : ℂ)+(3/4 : ℂ))‖ ≤
            |criticalValue c n|*(133/2000) := by
        rw [he]
        exact hz
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs] at hn
      exact (mul_le_mul_iff_right₀ habs).mp hn
    · field_simp [hdC]

theorem complete_physical_gate {c : ℝ} {n : ℕ} (h : CentralGate c n) :
    physicalGateDisk c n ⊆ physicalParentSource c n := by
  rw [← physical_gate_image c n h.scale_ne]
  exact image_mono h.full_gate_disk

/-- Exact fibers are transported as complete sets, not assigned a degree
by convention. The exceptional target is the literal critical value. -/
theorem physical_fiber_card {c : ℝ} {n : ℕ} (h : CentralGate c n)
    {y : ℂ} (hy : y ∈ physicalTarget c n) :
    {z : ℂ | z ∈ physicalParentSource c n ∧ ((quadraticMap c)^[n]) z = y}.ncard =
      if y = ((quadraticMap c)^[n]) 0 then 1 else 2 := by
  have hdC : (criticalValue c n : ℂ) ≠ 0 := by exact_mod_cast h.scale_ne
  have habs : 0 < |criticalValue c n| := abs_pos.mpr h.scale_ne
  have hy' : y/(criticalValue c n : ℂ) ∈ ball (0 : ℂ) (23/20) := by
    rw [mem_ball_zero_iff, norm_div, Complex.norm_real, Real.norm_eq_abs]
    apply (div_lt_iff₀ habs).mpr
    have hn : ‖y‖ < |criticalValue c n|*(23/20) := by simpa [physicalTarget] using hy
    nlinarith only [hn]
  have hfiber : {z : ℂ | z ∈ physicalParentSource c n ∧ ((quadraticMap c)^[n]) z = y} =
      (fun z : ℂ => (criticalValue c n : ℂ)*z) ''
        {z : ℂ | z ∈ parentSource c n ∧ normalizedReturn c n z =
          y/(criticalValue c n : ℂ)} := by
    ext z
    constructor
    · rintro ⟨⟨w, hw, rfl⟩, he⟩
      refine ⟨w, ⟨hw, ?_⟩, rfl⟩
      rw [physical_scale_identity c n h.scale_ne] at he
      apply (eq_div_iff hdC).mpr
      simpa only [mul_comm] using he
    · rintro ⟨w, ⟨hw, he⟩, rfl⟩
      refine ⟨⟨w, hw, rfl⟩, ?_⟩
      rw [physical_scale_identity c n h.scale_ne, he]
      field_simp [hdC]
  rw [hfiber, Set.ncard_image_of_injective _ (fun _ _ he => mul_left_cancel₀ hdC he)]
  rw [h.fiber_card _ hy', quadratic_iterate_zero]
  have he : y/(criticalValue c n : ℂ) = (1 : ℂ) ↔ y = (criticalValue c n : ℂ) := by
    rw [div_eq_iff hdC]
    simp
  simp only [he]

/-- A whole physical central gate, with the actual component, actual map,
and literal plane radii all retained in the statement. -/
structure PhysicalGate (c : ℝ) (n : ℕ) : Prop where
  scale_ne : criticalValue c n ≠ 0
  source_eq_component : physicalParentSource c n = connectedComponentIn
    (((quadraticMap c)^[n]) ⁻¹' physicalTarget c n) 0
  zero_mem : (0 : ℂ) ∈ physicalParentSource c n
  source_open : IsOpen (physicalParentSource c n)
  source_connected : IsConnected (physicalParentSource c n)
  compact_closure : IsCompact (closure (physicalParentSource c n))
  closure_inside : closure (physicalParentSource c n) ⊆ physicalTarget c n
  quantitative_closure : closure (physicalParentSource c n) ⊆
    ball 0 (|criticalValue c n|*(11/10))
  gap : ∀ {u v : ℂ}, u ∈ closure (physicalParentSource c n) →
    v ∉ physicalTarget c n → |criticalValue c n|/20 < dist u v
  image_eq : ((quadraticMap c)^[n]) '' physicalParentSource c n = physicalTarget c n
  proper : IsProperMap (physicalMap c n)
  fiber_card : ∀ y ∈ physicalTarget c n,
    {z : ℂ | z ∈ physicalParentSource c n ∧ ((quadraticMap c)^[n]) z = y}.ncard =
      if y = ((quadraticMap c)^[n]) 0 then 1 else 2
  full_gate_disk : physicalGateDisk c n ⊆ physicalParentSource c n

theorem physical_gate_of_central {c : ℝ} {n : ℕ} (h : CentralGate c n) :
    PhysicalGate c n :=
  ⟨h.scale_ne, physical_source_eq_component c n h.scale_ne, physical_zero h,
    physical_source_open h, physical_source_connected h, physical_compact_closure h,
    physical_closure_inside h, physical_quantitative_closure h, physical_gap h,
    physical_return_image h, physicalMap_proper c n,
    fun _ hy => physical_fiber_card h hy, complete_physical_gate h⟩

end
end TwoLevelPhysicalGate

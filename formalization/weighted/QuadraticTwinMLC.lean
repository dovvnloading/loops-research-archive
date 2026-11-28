import QuadraticEscape
import QuadraticMonotoneFiberTopology
import QuadraticTwinSemiconjugacy

/-!
# Simultaneous quadratic semiconjugacies and actual Mandelbrot fibers

The parameter locus in this module is the bounded critical-orbit locus for
the actual maps `z ↦ z^2 + c`.  No canonical quotient is postulated: the
continuous monotone map in the endpoint is an explicit input.

The ordinary compactness proof is reproduced, with attribution, from
`QuadraticMixedSusceptibilityMLC.lean`.  It uses only `QuadraticEscape`;
no susceptibility definition or theorem is imported.  The escape function
is used solely for closedness and a coarse orbit bound.

The new analytic input is the companion theorem classifying the parameter
pair of a simultaneous semiconjugacy continuous only on the real axis for `f_c` and `f_c + 1`.
Connectedness eliminates its two-point ambiguity.  The final implication to
an actual connected neighborhood basis uses the archive's separately proved
classical monotone-map topology.
-/

namespace QuadraticTwinMLC

open Set Filter Topology

noncomputable section

/-- The actual bounded critical-orbit parameter locus. -/
def mandelbrot : Set ℂ :=
  {c | ∃ B : ℝ, ∀ n : ℕ, ‖QuadraticEscape.orbit c n 0‖ ≤ B}

/-- This identification is ordinary supporting compactness, not a density
hypothesis on the quadratic escape function. -/
theorem mandelbrot_eq_zero_escape :
    mandelbrot = {c : ℂ | QuadraticEscape.parameterEscape c = 0} := by
  ext c
  exact (QuadraticEscape.parameterEscape_zero_iff c).symm

/-- The actual quadratic parameter locus is closed. -/
theorem mandelbrot_isClosed : IsClosed mandelbrot := by
  rw [mandelbrot_eq_zero_escape]
  exact isClosed_eq QuadraticEscape.parameterEscape_continuous continuous_const

/-- A coarse bound suffices for the compactness argument. -/
theorem mandelbrot_norm_le_three {c : ℂ} (hc : c ∈ mandelbrot) : ‖c‖ ≤ 3 := by
  have hz : QuadraticEscape.escape c 0 = 0 :=
    (QuadraticEscape.escape_zero_iff_bounded c 0).mpr hc
  have hbound := QuadraticEscape.escape_zero_orbit_bound c 0 hz 2
  have hsecond : ‖c ^ 2 + c‖ ≤ 1 + ‖c‖ := by
    simpa [QuadraticEscape.orbit] using hbound
  have hnorm : ‖c‖ ^ 2 ≤ ‖c ^ 2 + c‖ + ‖c‖ := by
    calc
      ‖c‖ ^ 2 = ‖(c ^ 2 + c) - c‖ := by
        rw [add_sub_cancel_right, norm_pow]
      _ ≤ ‖c ^ 2 + c‖ + ‖c‖ := norm_sub_le _ _
  nlinarith [norm_nonneg c]

/-- Compactness is proved for the actual complex quadratic parameter set. -/
theorem mandelbrot_isCompact : IsCompact mandelbrot := by
  apply (isCompact_closedBall (0 : ℂ) 3).of_isClosed_subset mandelbrot_isClosed
  intro c hc
  simpa only [Metric.mem_closedBall, dist_zero_right] using mandelbrot_norm_le_three hc

instance : CompactSpace mandelbrot :=
  isCompact_iff_compactSpace.mp mandelbrot_isCompact

/-- A map intertwines both actual quadratic generators and is continuous
on the real axis.  No continuity off that axis, injectivity, surjectivity,
or normalization is assumed. -/
def TwinParameters (c d : ℂ) : Prop :=
  ∃ h : ℂ → ℂ, Continuous (fun x : ℝ => h (x : ℂ)) ∧
    (∀ z : ℂ, h (z ^ 2 + c) = h z ^ 2 + d) ∧
    (∀ z : ℂ, h (z ^ 2 + c + 1) = h z ^ 2 + d + 1)

/-- The companion actual-family theorem leaves only conjugate parameters. -/
theorem parameter_eq_or_conj_of_twin {c d : ℂ} (ht : TwinParameters c d) :
    d = c ∨ d = star c := by
  obtain ⟨h, hcont, hquad, htwin⟩ := ht
  exact QuadraticTwinSemiconjugacy.parameter_eq_or_conj
    (c := c) (d := d) h hcont hquad htwin

/-- The identity supplies the simultaneous map for equal parameters. -/
theorem twinParameters_self (c : ℂ) : TwinParameters c c := by
  refine ⟨fun z => z, ?_, ?_, ?_⟩
  · exact Complex.continuous_ofReal
  · intro z
    rfl
  · intro z
    rfl

/-- Complex conjugation supplies the simultaneous map for conjugate
parameters; its restriction to the real axis is the identity. -/
theorem twinParameters_conj (c : ℂ) : TwinParameters c (star c) := by
  refine ⟨fun z => star z, ?_, ?_, ?_⟩
  · simpa only [Complex.star_def, Complex.conj_ofReal] using
      Complex.continuous_ofReal
  · intro z
    simp only [star_add, star_pow]
  · intro z
    simp only [star_add, star_pow, star_one]

/-- Exact strength of the simultaneous quadratic parameter relation. -/
theorem twinParameters_iff (c d : ℂ) :
    TwinParameters c d ↔ d = c ∨ d = star c := by
  constructor
  · intro ht
    exact parameter_eq_or_conj_of_twin ht
  · rintro (rfl | rfl)
    · exact twinParameters_self c
    · exact twinParameters_conj c

/-- Every parameter in this specified fiber admits the simultaneous
semiconjugacy continuous on the real axis.  No parameter equality is part
of this premise. -/
def TwinFiber {Y : Type*} (q : mandelbrot → Y) (c : mandelbrot) : Prop :=
  ∀ d : mandelbrot, q d = q c → TwinParameters (c : ℂ) (d : ℂ)

/-- The complex-plane image of a fiber of the explicitly supplied map. -/
def planeFiber {Y : Type*} (q : mandelbrot → Y) (c : mandelbrot) : Set ℂ :=
  Subtype.val '' (q ⁻¹' ({q c} : Set Y))

/-- The actual-family identities force each point of the fiber into an
explicit two-point set; no canonical-fiber identification is used. -/
theorem planeFiber_subset_pair_of_twin
    {Y : Type*} (q : mandelbrot → Y) (c : mandelbrot)
    (ht : TwinFiber q c) :
    planeFiber q c ⊆ {(c : ℂ), star (c : ℂ)} := by
  rintro _ ⟨d, hd, rfl⟩
  have hqd : q d = q c := hd
  have hpair : (d : ℂ) = (c : ℂ) ∨ (d : ℂ) = star (c : ℂ) :=
    parameter_eq_or_conj_of_twin (ht d hqd)
  simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hpair

/-- A preconnected fiber satisfying the two actual quadratic identities is
a singleton.  Connectedness removes the complex-conjugation ambiguity. -/
theorem monotone_fiber_eq_singleton_of_twin
    {Y : Type*} (q : mandelbrot → Y)
    (hf : ∀ y : Y, IsPreconnected (q ⁻¹' {y}))
    (c : mandelbrot) (ht : TwinFiber q c) :
    q ⁻¹' ({q c} : Set Y) = {c} := by
  have hF : IsPreconnected (planeFiber q c) :=
    (hf (q c)).image Subtype.val continuous_subtype_val.continuousOn
  have hfin : (planeFiber q c).Finite :=
    ((Set.finite_singleton (star (c : ℂ))).insert (c : ℂ)).subset
      (planeFiber_subset_pair_of_twin q c ht)
  have hcF : (c : ℂ) ∈ planeFiber q c := ⟨c, rfl, rfl⟩
  ext d
  constructor
  · intro hd
    change d = c
    apply Subtype.ext
    have hdF : (d : ℂ) ∈ planeFiber q c := ⟨d, hd, rfl⟩
    by_contra hdc
    have hnon : (planeFiber q c).Nontrivial :=
      ⟨(d : ℂ), hdF, (c : ℂ), hcF, hdc⟩
    exact (hF.infinite_of_nontrivial hnon) hfin
  · intro hd
    change d = c at hd
    subst d
    rfl

/-- A nontrivial actual parameter fiber obstructs the simultaneous
semiconjugacy condition with continuity only on the real axis. -/
theorem not_twin_of_nontrivial_fiber
    {Y : Type*} (q : mandelbrot → Y)
    (hf : ∀ y : Y, IsPreconnected (q ⁻¹' {y}))
    (c : mandelbrot)
    (hnon : (q ⁻¹' ({q c} : Set Y)).Nontrivial) :
    ¬ TwinFiber q c := by
  intro ht
  have hs := monotone_fiber_eq_singleton_of_twin q hf c ht
  obtain ⟨d, hd, e, he, hde⟩ := hnon
  have hd' : d = c := by
    rw [hs] at hd
    exact hd
  have he' : e = c := by
    rw [hs] at he
    exact he
  exact hde (hd'.trans he'.symm)

/-- The obstruction has a concrete parameter witness in the same fiber:
no map continuous on the real axis intertwines both named quadratic generators. -/
theorem exists_parameter_without_twin_of_nontrivial_fiber
    {Y : Type*} (q : mandelbrot → Y)
    (hf : ∀ y : Y, IsPreconnected (q ⁻¹' {y}))
    (c : mandelbrot)
    (hnon : (q ⁻¹' ({q c} : Set Y)).Nontrivial) :
    ∃ d : mandelbrot, q d = q c ∧ ¬ TwinParameters (c : ℂ) (d : ℂ) := by
  classical
  by_contra hn
  apply not_twin_of_nontrivial_fiber q hf c hnon
  intro d hd
  by_contra hdt
  exact hn ⟨d, hd, hdt⟩

/-- The simultaneous semiconjugacy criterion, with continuity required only
on the real axis, implies actual
pointwise local connectivity of the quadratic bounded-orbit locus.
The quotient map and all its topological hypotheses are explicit inputs. -/
theorem locallyConnectedAt_of_twin
    {Y : Type*} [TopologicalSpace Y] [T2Space Y] [LocallyConnectedSpace Y]
    (q : mandelbrot → Y) (hq : Continuous q) (hsurj : Function.Surjective q)
    (hf : ∀ y : Y, IsPreconnected (q ⁻¹' {y}))
    (c : mandelbrot) (ht : TwinFiber q c) :
    ∀ U ∈ 𝓝 c, ∃ V : Set mandelbrot,
      V ⊆ U ∧ IsOpen V ∧ c ∈ V ∧ IsConnected V := by
  exact LoopsQuadraticMonotoneFiberTopology.connected_open_basis_of_singleton_fiber
    q hq hsurj hf c (monotone_fiber_eq_singleton_of_twin q hf c ht)

end

end QuadraticTwinMLC

import TelescopePathPairing
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Nontrivial loop transport in the actual one-critical return

A small circle in the actual central quadratic component supplies a family
of regular target loops.  The selected analytic prefix inverse lifts its
half turns.  Every physical lift of an even number of turns closes; every
physical lift of an odd number of turns ends at its other deck point.
The target loops and their lifts are constructed inside the full selected
return components, with the original prefix, critical step and suffix.
-/

namespace LoopsTelescopeLoopMonodromy

open Set Function
open QuadraticEscape LoopsSaturatedTelescope LoopsTelescopeRamification
open LoopsTelescopeCollar LoopsTelescopeConformalInverse
open LoopsTelescopeDeckInvolution LoopsTelescopeUnbranchedCover

noncomputable section

/-- The central circle traversed through `m` half turns. -/
def centralHalfTurns (r : ℝ) (m : ℕ) : C(unitInterval, ℂ) :=
  ⟨fun t => (r : ℂ) * Complex.exp
    (((m : ℂ) * (Real.pi : ℂ) * Complex.I) * ((t : ℝ) : ℂ)), by fun_prop⟩

/-- The actual suffix image of the central circle after the critical
quadratic step.  Squaring the half-turn path makes `m` whole turns. -/
def criticalValueTurns (c : ℂ) (b : ℕ) (r : ℝ) (m : ℕ) :
    C(unitInterval, ℂ) :=
  ⟨fun t => orbit c b ((centralHalfTurns r m t)^2+c),
    (quadratic_orbit_continuous c b).comp
      (((centralHalfTurns r m).continuous.pow 2).add continuous_const)⟩

/-- A whole path in the physical selected return component. -/
def ActualPathLift (c : ℂ) (n : ℕ) (A : Set ℂ)
    (γ Γ : C(unitInterval, ℂ)) : Prop :=
  (∀ t, Γ t ∈ A) ∧ (∀ t, orbit c n (Γ t) = γ t)

private theorem centralHalfTurns_norm {r : ℝ} (hr : 0 < r)
    (m : ℕ) (t : unitInterval) : ‖centralHalfTurns r m t‖ = r := by
  change ‖(r : ℂ) * Complex.exp
    (((m : ℂ) * (Real.pi : ℂ) * Complex.I) * ((t : ℝ) : ℂ))‖ = r
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr,
    Complex.norm_exp]
  simp

private theorem centralHalfTurns_zero (r : ℝ) (m : ℕ) :
    centralHalfTurns r m 0 = (r : ℂ) := by
  simp [centralHalfTurns]

private theorem centralHalfTurns_one (r : ℝ) (m : ℕ) :
    centralHalfTurns r m 1 = (r : ℂ) * (-1 : ℂ)^m := by
  change (r : ℂ) * Complex.exp
    (((m : ℂ) * (Real.pi : ℂ) * Complex.I) * (1 : ℂ)) = _
  rw [mul_one, mul_assoc, Complex.exp_nat_mul, Complex.exp_pi_mul_I]

private theorem centralHalfTurns_even (r : ℝ) (k : ℕ) :
    centralHalfTurns r (2*k) 1 = (r : ℂ) := by
  simp [centralHalfTurns_one, pow_mul]

private theorem centralHalfTurns_odd (r : ℝ) (k : ℕ) :
    centralHalfTurns r (2*k+1) 1 = -(r : ℂ) := by
  simp [centralHalfTurns_one, pow_add, pow_mul]

/-- Every constructed target path is a loop, before any small-radius or
component hypotheses are imposed. -/
theorem criticalValueTurns_closed (c : ℂ) (b : ℕ) (r : ℝ) (m : ℕ) :
    criticalValueTurns c b r m 1 = criticalValueTurns c b r m 0 := by
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' m
  · simp [criticalValueTurns, centralHalfTurns_even, centralHalfTurns_zero]
  · simp [criticalValueTurns, centralHalfTurns_odd, centralHalfTurns_zero]

/-- The actual one-critical return realizes both deck phases through
explicit regular target loops. One radius and one analytic involution work
for all turn counts. Every lift of an even-turn loop closes, whereas every
lift of an odd-turn loop ends at its distinct deck mate. In particular the
one-turn loop has no closed physical lift, and its two-turn version has only
closed lifts. No covering, inverse branch or loop is supplied as a premise. -/
theorem quadratic_return_loop_monodromy (c : ℂ) (a b : ℕ)
    (A B D V : Set ℂ) (x : ℂ) (hx0 : orbit c a x = 0)
    (hVo : IsOpen V) (hVc : IsPreconnected V) (hv : orbit c b c ∈ V)
    (hD : D = connectedComponentIn (orbit c b ⁻¹' V) c)
    (hB : B = connectedComponentIn ((fun w : ℂ => w^2+c) ⁻¹' D) 0)
    (hA : A = connectedComponentIn (orbit c a ⁻¹' B) x)
    (hpinj : InjOn (orbit c a) A) (hrinj : InjOn (orbit c b) D) :
    ∃ (r : ℝ) (τ : ℂ → ℂ) (z : ℂ),
      0 < r ∧ z ∈ A ∧ orbit c a z = (r : ℂ) ∧
      AnalyticOnNhd ℂ τ A ∧ MapsTo τ A A ∧
      (∀ w ∈ A, τ (τ w) = w) ∧
      (∀ w ∈ A, orbit c a (τ w) = -(orbit c a w)) ∧ τ z ≠ z ∧
      (∀ m : ℕ,
        (∀ t, criticalValueTurns c b r m t ∈ V) ∧
        (∀ t, criticalValueTurns c b r m t ≠ orbit c b c) ∧
        criticalValueTurns c b r m 1 = criticalValueTurns c b r m 0 ∧
        ∃ Γ : C(unitInterval, ℂ),
          ActualPathLift c (a+1+b) A (criticalValueTurns c b r m) Γ ∧ Γ 0 = z) ∧
      (∀ (k : ℕ) (Γ : C(unitInterval, ℂ)),
        (ActualPathLift c (a+1+b) A (criticalValueTurns c b r (2*k)) Γ →
          Γ 1 = Γ 0) ∧
        (ActualPathLift c (a+1+b) A (criticalValueTurns c b r (2*k+1)) Γ →
          Γ 1 = τ (Γ 0) ∧ Γ 1 ≠ Γ 0)) := by
  have hc : c ∈ D := by
    rw [hD]
    exact mem_connectedComponentIn hv
  have h0 : (0 : ℂ) ∈ B := by
    rw [hB]
    exact mem_connectedComponentIn (by simpa using hc)
  have hDo : IsOpen D := by
    rw [hD]
    exact (hVo.preimage (quadratic_orbit_continuous c b)).connectedComponentIn
  have hBo : IsOpen B := by
    rw [hB]
    exact (hDo.preimage ((continuous_id.pow 2).add continuous_const)).connectedComponentIn
  have hAo : IsOpen A := by
    rw [hA]
    exact (hBo.preimage (quadratic_orbit_continuous c a)).connectedComponentIn
  have hBc : IsPreconnected B := by
    rw [hB]
    exact isPreconnected_connectedComponentIn
  have hAp : orbit c a '' A = B := by
    rw [hA]
    exact orbit_component_image c a B hBo hBc x (by simpa [hx0] using h0)
  obtain ⟨g, hgmap, hgleft, hgright, hga, _⟩ :=
    orbit_conformal_inverse c a A B hAo hpinj hAp
  obtain ⟨τ, hτan, hτmap, hτinv, hτprefix, hτfixed, hτfiber, _, _⟩ :=
    quadratic_return_analytic_involution c a b A B D hc hAo hB hAp hpinj hrinj
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hBo 0 h0
  let r : ℝ := ε/2
  have hr : 0 < r := by dsimp [r]; positivity
  have hrε : r < ε := by dsimp [r]; linarith
  have hwB (m : ℕ) (t : unitInterval) : centralHalfTurns r m t ∈ B := by
    apply hball
    rw [Metric.mem_ball, dist_zero_right, centralHalfTurns_norm hr]
    exact hrε
  have hrB : (r : ℂ) ∈ B := by
    simpa only [centralHalfTurns_zero] using hwB 0 0
  let z : ℂ := g (r : ℂ)
  have hz : z ∈ A := hgmap hrB
  have hzr : orbit c a z = (r : ℂ) := hgright hrB
  have hτz : τ z ≠ z := by
    intro he
    have h := (hτfixed z hz).mp he
    rw [hzr] at h
    exact (Complex.ofReal_ne_zero.mpr hr.ne') h
  have hqD (m : ℕ) (t : unitInterval) : (centralHalfTurns r m t)^2+c ∈ D := by
    have h := hwB m t
    rw [hB] at h
    exact connectedComponentIn_subset ((fun w : ℂ => w^2+c) ⁻¹' D) 0 h
  have hγV (m : ℕ) (t : unitInterval) : criticalValueTurns c b r m t ∈ V := by
    have h := hqD m t
    rw [hD] at h
    exact connectedComponentIn_subset (orbit c b ⁻¹' V) c h
  have hγreg (m : ℕ) (t : unitInterval) :
      criticalValueTurns c b r m t ≠ orbit c b c := by
    intro he
    have hzero : (centralHalfTurns r m t)^2 = 0 := by
      have hh := hrinj (hqD m t) hc he
      linear_combination hh
    have hz0 : centralHalfTurns r m t = 0 := eq_zero_of_pow_eq_zero hzero
    have hn := centralHalfTurns_norm hr m t
    rw [hz0, norm_zero] at hn
    exact hr.ne' hn.symm
  have hgcont : ContinuousOn g B := fun w hw => (hga w hw).continuousAt.continuousWithinAt
  let Λ : ℕ → C(unitInterval, ℂ) := fun m =>
    ⟨fun t => g (centralHalfTurns r m t),
      hgcont.comp_continuous (centralHalfTurns r m).continuous (hwB m)⟩
  have hΛA (m : ℕ) (t : unitInterval) : Λ m t ∈ A := hgmap (hwB m t)
  have hΛzero (m : ℕ) : Λ m 0 = z := by
    change g (centralHalfTurns r m 0) = g (r : ℂ)
    rw [centralHalfTurns_zero]
  have hΛlift (m : ℕ) : ActualPathLift c (a+1+b) A (criticalValueTurns c b r m) (Λ m) := by
    refine ⟨hΛA m, ?_⟩
    intro t
    rw [quadratic_orbit_add c (a+1) b]
    change orbit c b ((orbit c a (g (centralHalfTurns r m t)))^2+c) = _
    rw [hgright (hwB m t)]
    rfl
  have hΛeven (k : ℕ) : Λ (2*k) 1 = z := by
    change g (centralHalfTurns r (2*k) 1) = g (r : ℂ)
    rw [centralHalfTurns_even]
  have hΛodd (k : ℕ) : Λ (2*k+1) 1 = τ z := by
    apply hpinj (hΛA _ _) (hτmap hz)
    change orbit c a (g (centralHalfTurns r (2*k+1) 1)) = orbit c a (τ z)
    rw [hgright (hwB _ _), centralHalfTurns_odd, hτprefix z hz, hzr]
  have hτcont : ContinuousOn τ A := fun w hw => (hτan w hw).continuousAt.continuousWithinAt
  let mate : ℕ → C(unitInterval, ℂ) := fun m =>
    ⟨fun t => τ (Λ m t), hτcont.comp_continuous (Λ m).continuous (hΛA m)⟩
  have hMateA (m : ℕ) (t : unitInterval) : mate m t ∈ A := hτmap (hΛA m t)
  have hMatelift (m : ℕ) : ActualPathLift c (a+1+b) A (criticalValueTurns c b r m) (mate m) := by
    refine ⟨hMateA m, ?_⟩
    intro t
    exact ((hτfiber (Λ m t) (hΛA m t) (mate m t) (hMateA m t)).mpr (Or.inr rfl)).trans
      ((hΛlift m).2 t)
  have hMatezero (m : ℕ) : mate m 0 = τ z := by
    change τ (Λ m 0) = τ z
    rw [hΛzero]
  have hclass (m : ℕ) (Γ : C(unitInterval, ℂ))
      (hΓ : ActualPathLift c (a+1+b) A (criticalValueTurns c b r m) Γ) :
      Γ = Λ m ∨ Γ = mate m := by
    have hvalue : orbit c (a+1+b) z = criticalValueTurns c b r m 0 := by
      rw [← hΛzero m]
      exact (hΛlift m).2 0
    have hstart : orbit c (a+1+b) (Γ 0) = orbit c (a+1+b) z :=
      (hΓ.2 0).trans hvalue.symm
    rcases (hτfiber z hz (Γ 0) (hΓ.1 0)).mp hstart with he | he
    · have hu := quadratic_return_unique_path_lift c a b A B D V x hx0 hVo hVc hv
        hD hB hA hpinj hrinj (criticalValueTurns c b r m) (hγV m) (hγreg m) z hz hvalue
      exact Or.inl (hu.unique ⟨hΓ.1,hΓ.2,he⟩ ⟨(hΛlift m).1,(hΛlift m).2,hΛzero m⟩)
    · have hτvalue : orbit c (a+1+b) (τ z) = criticalValueTurns c b r m 0 :=
        ((hτfiber z hz (τ z) (hτmap hz)).mpr (Or.inr rfl)).trans hvalue
      have hu := quadratic_return_unique_path_lift c a b A B D V x hx0 hVo hVc hv
        hD hB hA hpinj hrinj (criticalValueTurns c b r m) (hγV m) (hγreg m)
          (τ z) (hτmap hz) hτvalue
      exact Or.inr (hu.unique ⟨hΓ.1,hΓ.2,he⟩ ⟨(hMatelift m).1,(hMatelift m).2,hMatezero m⟩)
  refine ⟨r, τ, z, hr, hz, hzr, hτan, hτmap, hτinv, hτprefix, hτz, ?_, ?_⟩
  · intro m
    exact ⟨hγV m, hγreg m, criticalValueTurns_closed c b r m, Λ m, hΛlift m, hΛzero m⟩
  · intro k Γ
    constructor
    · intro hΓ
      rcases hclass (2*k) Γ hΓ with rfl | rfl
      · rw [hΛeven, hΛzero]
      · change τ (Λ (2*k) 1) = τ (Λ (2*k) 0)
        rw [hΛeven, hΛzero]
    · intro hΓ
      rcases hclass (2*k+1) Γ hΓ with rfl | rfl
      · rw [hΛodd, hΛzero]
        exact ⟨rfl, hτz⟩
      · change τ (Λ (2*k+1) 1) = τ (τ (Λ (2*k+1) 0)) ∧
          τ (Λ (2*k+1) 1) ≠ τ (Λ (2*k+1) 0)
        rw [hΛodd, hΛzero, hτinv z hz]
        exact ⟨rfl, Ne.symm hτz⟩

/-- Forgetting the deck phase cannot produce a continuous inverse on
the whole regular target of the actual selected return. The obstruction
is the explicit odd-turn loop, with all of its physical lifts retained. -/
theorem quadratic_return_no_regular_section (c : ℂ) (a b : ℕ)
    (A B D V : Set ℂ) (x : ℂ) (hx0 : orbit c a x = 0)
    (hVo : IsOpen V) (hVc : IsPreconnected V) (hv : orbit c b c ∈ V)
    (hD : D = connectedComponentIn (orbit c b ⁻¹' V) c)
    (hB : B = connectedComponentIn ((fun w : ℂ => w^2+c) ⁻¹' D) 0)
    (hA : A = connectedComponentIn (orbit c a ⁻¹' B) x)
    (hpinj : InjOn (orbit c a) A) (hrinj : InjOn (orbit c b) D) :
    ¬ ∃ s : ℂ → ℂ,
      ContinuousOn s (V \ {orbit c b c}) ∧
      MapsTo s (V \ {orbit c b c}) A ∧
      ∀ v ∈ V \ {orbit c b c}, orbit c (a+1+b) (s v) = v := by
  obtain ⟨r, τ, z, _, _, _, _, _, _, _, _, hpaths, hphase⟩ :=
    quadratic_return_loop_monodromy c a b A B D V x hx0 hVo hVc hv
      hD hB hA hpinj hrinj
  rintro ⟨s, hscont, hsmap, hsright⟩
  let γ := criticalValueTurns c b r 1
  have hγ (t : unitInterval) : γ t ∈ V \ {orbit c b c} :=
    ⟨(hpaths 1).1 t, (hpaths 1).2.1 t⟩
  let Γ : C(unitInterval, ℂ) :=
    ⟨fun t => s (γ t), hscont.comp_continuous γ.continuous hγ⟩
  have hΓ : ActualPathLift c (a+1+b) A γ Γ :=
    ⟨fun t => hsmap (hγ t), fun t => hsright (γ t) (hγ t)⟩
  have hne : Γ 1 ≠ Γ 0 := ((hphase 0 Γ).2 hΓ).2
  apply hne
  change s (γ 1) = s (γ 0)
  exact congrArg s (hpaths 1).2.2.1

end

end LoopsTelescopeLoopMonodromy

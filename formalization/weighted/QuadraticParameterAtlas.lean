import QuadraticInverseBranches
import QuadraticInverseOpen

/-!
# One jointly analytic atlas for every branch of a regular quadratic fiber

All inverse points over one regular target value are continued together.
Finite separation of their physical source neighborhoods gives distinct
branches on one common parameter-target product.  The exact polynomial
degree then proves that these branches exhaust every nearby fiber.
Their images are the full actual pullback components, with pairwise
disjoint compact closures.  No moving branch family is assumed.
The joint analyticity and exact census include the closed target disk;
the full open source components lie over its interior.
-/

namespace LoopsQuadraticParameterAtlas

open Set Function Filter
open scoped Topology
open QuadraticEscape LoopsSaturatedTelescope LoopsTelescopeRamification
open LoopsQuadraticCylinderCensus LoopsQuadraticCriticalFiberCensus
open LoopsQuadraticRegularInverse LoopsQuadraticInverseBranches
open LoopsQuadraticParameterInverse LoopsQuadraticInverseOpen

noncomputable section

/-- A regular terminal value excludes every preterminal critical
encounter along each of its actual inverse orbits. -/
theorem inverseFiber_no_critical_visits (c : ℂ) (n : ℕ) (y : ℂ)
    (hregular : ∀ k < n, orbit c k c ≠ y) (a : inverseFiber c n y) :
    ∀ j < n, orbit c j a.val ≠ 0 := by
  intro j hj hz
  let k := n - (j+1)
  have hk : k < n := by dsimp [k]; omega
  have hclock : j+1+k = n := by dsimp [k]; omega
  have hstep : orbit c (j+1) a.val = c := by simp [orbit, hz]
  apply hregular k hk
  calc
    orbit c k c = orbit c k (orbit c (j+1) a.val) := by rw [hstep]
    _ = orbit c (j+1+k) a.val := (quadratic_orbit_add c (j+1) k a.val).symm
    _ = y := by rw [hclock]; exact a.property

/-- An arbitrary regular actual fiber generates one common analytic
atlas for all nearby parameters and targets.  Every nearby solution is
represented exactly once, and every branch fills its entire physical
component with a compact closure disjoint from every other branch.
The inverse derivatives and finite postcritical avoidance persist through
the closed target disk on the same parameter neighborhood. -/
theorem quadratic_parameter_inverse_atlas (c : ℂ) (n : ℕ) (y : ℂ)
    (hregular : ∀ k < n, orbit c k c ≠ y) :
    ∃ ε δ : ℝ, 0 < ε ∧ 0 < δ ∧
      ∃ g : inverseFiber c n y → ℂ → ℂ → ℂ,
        (∀ a, g a c y = a.val) ∧
        (∀ a, AnalyticOnNhd ℂ (fun p : ℂ × ℂ => g a p.1 p.2)
          (Metric.ball c ε ×ˢ Metric.closedBall y δ)) ∧
        (∀ d ∈ Metric.ball c ε, ∀ w ∈ Metric.closedBall y δ, ∀ z : ℂ,
          orbit d n z = w ↔ ∃! a : inverseFiber c n y, g a d w = z) ∧
        (∀ d ∈ Metric.ball c ε, ∀ a,
          g a d '' Metric.ball y δ =
            inverseComponent d n (Metric.ball y δ) (g a d y) ∧
          IsCompact (closure (g a d '' Metric.ball y δ)) ∧
          InjOn (orbit d n) (closure (g a d '' Metric.ball y δ))) ∧
        (∀ d ∈ Metric.ball c ε,
          Pairwise (fun a b : inverseFiber c n y =>
            Disjoint (closure (g a d '' Metric.ball y δ))
              (closure (g b d '' Metric.ball y δ)))) ∧
        (∀ d ∈ Metric.ball c ε, ∀ k < n, orbit d k d ∉ Metric.closedBall y δ) ∧
        (∀ d ∈ Metric.ball c ε, ∀ a, ∀ w ∈ Metric.closedBall y δ,
          HasDerivAt (g a d) (deriv (orbit d n) (g a d w))⁻¹ w ∧
          ConformalAt (g a d) w) := by
  classical
  let I := inverseFiber c n y
  have hcard : Nat.card I = 2^n := inverseFiber_card c n y hregular
  letI : Finite I := Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  letI : Fintype I := Fintype.ofFinite I
  have hcardI : Fintype.card I = 2^n := by
    simpa only [Nat.card_eq_fintype_card] using hcard
  have hfinite : (range (fun a : I => a.val)).Finite := finite_range _
  obtain ⟨W, hW, hWdisj⟩ := hfinite.t2_separation
  have hlocal (a : I) :
      ∃ (P U T : Set ℂ) (g : ℂ → ℂ → ℂ),
        IsOpen P ∧ c ∈ P ∧ IsOpen U ∧ ({a.val} : Set ℂ) ⊆ U ∧
        IsCompact (closure U) ∧ closure U ⊆ W a.val ∧
        IsOpen T ∧ orbit c n '' ({a.val} : Set ℂ) ⊆ T ∧
        AnalyticOnNhd ℂ (fun p : ℂ × ℂ => g p.1 p.2) (P ×ˢ T) ∧
        (∀ d ∈ P, MapsTo (g d) T U ∧ LeftInvOn (g d) (orbit d n) U ∧
          RightInvOn (g d) (orbit d n) T) ∧
        g c '' (orbit c n '' ({a.val} : Set ℂ)) = {a.val} ∧
        ∀ d ∈ P, ∀ w ∈ T,
          HasDerivAt (g d) (deriv (orbit d n) (g d w))⁻¹ w ∧
          ConformalAt (g d) w := by
    apply quadratic_compact_parameter_inverse_family c n {a.val} (W a.val)
      isCompact_singleton (hW a.val).2
    · exact singleton_subset_iff.mpr (hW a.val).1
    · exact Set.injOn_singleton _ _
    · intro z hz j hj
      have hza : z = a.val := mem_singleton_iff.mp hz
      rw [hza]
      exact inverseFiber_no_critical_visits c n y hregular a j hj
  choose P U T g hP hcP hU haU hUc hUW hT hyT hana hbranch hcore hder using hlocal
  have hyT' (a : I) : y ∈ T a :=
    hyT a ⟨a.val, by simp, a.property⟩
  have hanchor (a : I) : g a c y = a.val := by
    simpa only [a.property] using
      (hbranch a c (hcP a)).2.1 (haU a (by simp))
  let P₀ := ⋂ a : I, P a
  let T₀ := ⋂ a : I, T a
  have hP₀ : IsOpen P₀ := isOpen_iInter_of_finite hP
  have hT₀ : IsOpen T₀ := isOpen_iInter_of_finite hT
  have hcP₀ : c ∈ P₀ := mem_iInter.mpr hcP
  have hyT₀ : y ∈ T₀ := mem_iInter.mpr hyT'
  obtain ⟨ε, hε, hεP⟩ := Metric.isOpen_iff.mp hP₀ c hcP₀
  obtain ⟨r, hr, hrT⟩ := Metric.isOpen_iff.mp hT₀ y hyT₀
  let δ := r/2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  let V := Metric.ball y δ
  have hVy : y ∈ V := Metric.mem_ball_self hδ
  have hVcl : IsCompact (closure V) :=
    (isCompact_closedBall y δ).of_isClosed_subset isClosed_closure
      Metric.closure_ball_subset_closedBall
  have hBT₀ : Metric.closedBall y δ ⊆ T₀ :=
    (Metric.closedBall_subset_ball (by dsimp [δ]; linarith)).trans hrT
  have hclT₀ : closure V ⊆ T₀ :=
    Metric.closure_ball_subset_closedBall.trans hBT₀
  have hdP (d : ℂ) (hd : d ∈ Metric.ball c ε) (a : I) : d ∈ P a :=
    mem_iInter.mp (hεP hd) a
  have hwT (w : ℂ) (hw : w ∈ Metric.closedBall y δ) (a : I) : w ∈ T a :=
    mem_iInter.mp (hBT₀ hw) a
  have hdistinct (d : ℂ) (hd : d ∈ Metric.ball c ε)
      (w : ℂ) (hw : w ∈ Metric.closedBall y δ) :
      Injective (fun a : I => g a d w) := by
    intro a b he
    by_contra hab
    have habval : a.val ≠ b.val := fun h => hab (Subtype.ext h)
    have hsep : Disjoint (W a.val) (W b.val) :=
      hWdisj ⟨a, rfl⟩ ⟨b, rfl⟩ habval
    have hga : g a d w ∈ W a.val :=
      hUW a (subset_closure ((hbranch a d (hdP d hd a)).1 (hwT w hw a)))
    have hgb : g b d w ∈ W b.val :=
      hUW b (subset_closure ((hbranch b d (hdP d hd b)).1 (hwT w hw b)))
    exact Set.disjoint_left.mp hsep hga (he.symm ▸ hgb)
  have hcomplete (d : ℂ) (hd : d ∈ Metric.ball c ε)
      (w : ℂ) (hw : w ∈ Metric.closedBall y δ) :
      (∀ z : ℂ, orbit d n z = w ↔ ∃! a : I, g a d w = z) ∧
      ∀ k < n, orbit d k d ≠ w := by
    let A := Finset.univ.image (fun a : I => g a d w)
    have hAc : A.card = 2^n := by
      rw [Finset.card_image_of_injective _ (hdistinct d hd w hw), Finset.card_univ]
      exact hcardI
    have hA (z : ℂ) (hz : z ∈ A) : ((fun z : ℂ => z^2+d)^[n]) z = w := by
      obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hz
      simpa only [← orbit_map_eq_iterate] using
        (hbranch a d (hdP d hd a)).2.2 (hwT w hw a)
    have hfull (z : ℂ) : orbit d n z = w ↔ z ∈ A := by
      simpa only [← orbit_map_eq_iterate] using
        quadratic_full_degree_census d w n A hA hAc.ge z
    have hsub : A ⊆ globalFiber d n w := by
      intro z hz
      exact (mem_globalFiber d n w z).mpr (hA z hz)
    have hglobal : (globalFiber d n w).card = 2^n := by
      have hle := Finset.card_le_card hsub
      have hexact := globalFiber_card_exact d w n
      omega
    refine ⟨?_, ?_⟩
    · intro z
      constructor
      · intro hz
        obtain ⟨a, _, haz⟩ := Finset.mem_image.mp ((hfull z).mp hz)
        exact ⟨a, haz, fun b hb => hdistinct d hd w hw (hb.trans haz.symm)⟩
      · rintro ⟨a, ha, _⟩
        exact (hfull z).mpr (Finset.mem_image.mpr ⟨a, Finset.mem_univ _, ha⟩)
    · simpa only [← orbit_map_eq_iterate] using
        (globalFiber_full_card_iff d w n).mp hglobal
  have hcomponents (d : ℂ) (hd : d ∈ Metric.ball c ε) (a : I) :
      g a d '' V = inverseComponent d n V (g a d y) ∧
      IsOpen (g a d '' V) ∧ IsPreconnected (g a d '' V) ∧
      IsCompact (closure (g a d '' V)) ∧ closure (g a d '' V) ⊆ U a ∧
      orbit d n '' (g a d '' V) = V ∧
      InjOn (orbit d n) (closure (g a d '' V)) := by
    have hcont : ContinuousOn (g a d) (T a) := by
      intro w hw
      have hi : AnalyticAt ℂ (fun z : ℂ => (d,z)) w :=
        analyticAt_const.prod analyticAt_id
      have hag : AnalyticAt ℂ (g a d) w :=
        (hana a (d,w) ⟨hdP d hd a, hw⟩).comp hi
      exact hag.continuousAt.continuousWithinAt
    exact quadratic_inverse_open_component d n (U a) (T a) V (g a d)
      (hU a) Metric.isOpen_ball (convex_ball y δ).isPreconnected hVcl
      (fun z hz => mem_iInter.mp (hclT₀ hz) a) hcont
      (hbranch a d (hdP d hd a)).1
      (hbranch a d (hdP d hd a)).2.1
      (hbranch a d (hdP d hd a)).2.2 y hVy
  refine ⟨ε, δ, hε, hδ, g, hanchor, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a p hp
    exact hana a p ⟨hdP p.1 hp.1 a, hwT p.2 hp.2 a⟩
  · intro d hd w hw
    exact (hcomplete d hd w hw).1
  · intro d hd a
    have h := hcomponents d hd a
    exact ⟨h.1, h.2.2.2.1, h.2.2.2.2.2.2⟩
  · intro d hd a b hab
    have habval : a.val ≠ b.val := fun h => hab (Subtype.ext h)
    apply (hWdisj ⟨a, rfl⟩ ⟨b, rfl⟩ habval).mono
    · exact (hcomponents d hd a).2.2.2.2.1.trans
        ((subset_closure : U a ⊆ closure (U a)).trans (hUW a))
    · exact (hcomponents d hd b).2.2.2.2.1.trans
        ((subset_closure : U b ⊆ closure (U b)).trans (hUW b))
  · intro d hd k hk hw
    exact (hcomplete d hd (orbit d k d) hw).2 k hk rfl
  · intro d hd a w hw
    exact hder a d (hdP d hd a) w (hwT w hw a)

end
end LoopsQuadraticParameterAtlas

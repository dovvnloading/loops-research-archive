import QuadraticEscapeCoding
import ConnectedBinaryCoding

/-!
# Exact component coding for an escaping quadratic

One positive-height inverse splitting supplies coherent inverse sections at
every finite depth. Its connected compact cylinders have exactly the actual
bounded-orbit components as their infinite intersections. The conclusion is
a conjugacy on the component quotient, without a singleton-component premise.
-/

namespace LoopsQuadraticEscapeTree

open Set Function QuadraticEscape LoopsStationaryFiberDynamics
open LoopsQuadraticEscapeFullness
open LoopsCompactBinaryCoding LoopsConnectedBinaryCoding

noncomputable section

set_option maxHeartbeats 1000000

/-- Include the actual bounded-orbit set in the critical escape sublevel. -/
def filledIntoCriticalSublevel (c : ℂ) :
    quadraticFilled c → sublevel c (escape c 0) :=
  fun z => ⟨z, by
    change escape c (z : ℂ) ≤ escape c 0
    rw [show escape c (z : ℂ) = 0 from z.property]
    exact escape_nonneg c 0⟩

theorem filledIntoCriticalSublevel_continuous (c : ℂ) :
    Continuous (filledIntoCriticalSublevel c) :=
  continuous_subtype_val.subtype_mk _

theorem filledIntoCriticalSublevel_injective (c : ℂ) :
    Injective (filledIntoCriticalSublevel c) := by
  intro x y h
  exact Subtype.ext (congrArg Subtype.val h)

/-- The same positive-height splitting gives all finite inverse sections
and the zero-height coding. Their nested cylinder limits lie in the actual
bounded-orbit set, by the exact escape-height functional equation. -/
theorem filled_coherent_branch_system (c : ℂ) (hc : 0 < escape c 0) :
    ∃ (e : quadraticFilled c ≃ₜ (Fin 2 × quadraticFilled c))
      (b : Fin 2 → sublevel c (escape c 0) → sublevel c (escape c 0)),
      (∀ z, (e z).2 = quadraticFilledMap c z) ∧
      (∀ i, Continuous (b i)) ∧
      Injective (fun p : Fin 2 × sublevel c (escape c 0) => b p.1 p.2) ∧
      (∀ i y, filledIntoCriticalSublevel c (e.symm (i,y)) =
        b i (filledIntoCriticalSublevel c y)) ∧
      (∀ a, (⋂ n, cylinder b a n) ⊆ range (filledIntoCriticalSublevel c)) := by
  let a := escape c 0
  have ha : 0 < a := hc
  obtain ⟨E₀, hE₀⟩ := sublevel_split c (a/2) (by positivity) (by dsimp [a]; linarith)
  let top : sublevel c (2*(a/2)) ≃ₜ sublevel c a :=
    Homeomorph.setCongr (congrArg (sublevel c) (by ring : 2*(a/2)=a))
  let E : sublevel c (a/2) ≃ₜ (Fin 2 × sublevel c a) :=
    E₀.trans ((Homeomorph.refl (Fin 2)).prodCongr top)
  have hE (z : sublevel c (a/2)) : ((E z).2 : ℂ) = (z : ℂ)^2+c := hE₀ z
  let inc : sublevel c (a/2) → sublevel c a := fun z =>
    ⟨z, le_trans z.property (by linarith)⟩
  have hinc : Continuous inc := continuous_subtype_val.subtype_mk _
  let b : Fin 2 → sublevel c a → sublevel c a :=
    fun i z => inc (E.symm (i,z))
  have hb (i : Fin 2) : Continuous (b i) :=
    hinc.comp (E.symm.continuous.comp (continuous_const.prodMk continuous_id))
  have hbi : Injective (fun p : Fin 2 × sublevel c a => b p.1 p.2) := by
    intro p q hpq
    apply E.symm.injective
    exact Subtype.ext (congrArg Subtype.val hpq)
  have hbq (i : Fin 2) (z : sublevel c a) :
      (b i z : ℂ)^2+c = (z : ℂ) := by
    have h := hE (E.symm (i,z))
    rw [E.apply_symm_apply] at h
    exact h.symm
  have hheight (i : Fin 2) (z : sublevel c a) :
      2*escape c (b i z) = escape c z := by
    rw [← escape_step, hbq]
  let j := filledIntoCriticalSublevel c
  have hj : Continuous j := filledIntoCriticalSublevel_continuous c
  have hji : Injective j := filledIntoCriticalSublevel_injective c
  let bf : (Fin 2 × quadraticFilled c) → quadraticFilled c := fun p =>
    ⟨b p.1 (j p.2), by
      change escape c (b p.1 (j p.2)) = 0
      have h := hheight p.1 (j p.2)
      have hz : escape c (j p.2) = 0 := p.2.property
      linarith⟩
  have hbf (p : Fin 2 × quadraticFilled c) :
      j (bf p) = b p.1 (j p.2) := by
    apply Subtype.ext
    rfl
  have hbfc : Continuous bf := by
    have hh : Continuous (fun p : Fin 2 × quadraticFilled c => b p.1 (j p.2)) := by
      apply continuous_prod_of_discrete_left.mpr
      intro i
      exact (hb i).comp hj
    exact (continuous_subtype_val.comp hh).subtype_mk _
  have hbfi : Injective bf := by
    intro p q hpq
    have he : b p.1 (j p.2) = b q.1 (j q.2) := by
      rw [← hbf p, ← hbf q, hpq]
    have hpair := hbi he
    exact Prod.ext (congrArg Prod.fst hpair) (hji (congrArg Prod.snd hpair))
  have hbfs : Surjective bf := by
    intro z
    let zs : sublevel c (a/2) := ⟨z, by
      change escape c (z : ℂ) ≤ a/2
      rw [show escape c (z : ℂ) = 0 from z.property]
      positivity⟩
    have hz : escape c ((E zs).2 : ℂ) = 0 := by
      rw [hE, escape_step]
      change 2*escape c (z : ℂ) = 0
      rw [show escape c (z : ℂ) = 0 from z.property, mul_zero]
    let w : quadraticFilled c := ⟨(E zs).2, hz⟩
    have hjw : j w = (E zs).2 := by
      apply Subtype.ext
      rfl
    refine ⟨((E zs).1,w), ?_⟩
    apply Subtype.ext
    change (E.symm ((E zs).1,j w) : ℂ) = (z : ℂ)
    rw [hjw, Prod.eta, E.symm_apply_apply]
  letI : CompactSpace (quadraticFilled c) :=
    isCompact_iff_compactSpace.mp (quadratic_filled_compact c)
  let e : quadraticFilled c ≃ₜ (Fin 2 × quadraticFilled c) :=
    ((Equiv.ofBijective bf ⟨hbfi,hbfs⟩).toHomeomorphOfContinuousClosed
      hbfc hbfc.isClosedMap).symm
  have he (z : quadraticFilled c) : (e z).2 = quadraticFilledMap c z := by
    have hi : bf (e z) = z := e.symm_apply_apply z
    have hq := hbq (e z).1 (j (e z).2)
    have hi' : (b (e z).1 (j (e z).2) : ℂ) = (z : ℂ) :=
      congrArg Subtype.val hi
    rw [hi'] at hq
    exact Subtype.ext hq.symm
  have hjb (i : Fin 2) (y : quadraticFilled c) :
      j (e.symm (i,y)) = b i (j y) := hbf (i,y)
  have hbound : ∀ (n : ℕ) (ω : ℕ → Fin 2) (z : sublevel c a),
      z ∈ cylinder b ω n → (2 : ℝ)^n*escape c z ≤ a := by
    intro n
    induction n with
    | zero =>
      intro ω z hz
      simpa using z.property
    | succ n ih =>
      intro ω z hz
      obtain ⟨w,hw,rfl⟩ := hz
      calc
        (2 : ℝ)^(n+1)*escape c (b (ω 0) w) =
            (2 : ℝ)^n * escape c w := by
          rw [pow_succ, mul_assoc, hheight]
        _ ≤ a := ih (shift ω) w hw
  have hlim (ω : ℕ → Fin 2) :
      (⋂ n, cylinder b ω n) ⊆ range j := by
    intro z hz
    have hg : escape c z = 0 := by
      by_contra hn
      have hp : 0 < escape c z :=
        lt_of_le_of_ne (escape_nonneg c z) (Ne.symm hn)
      obtain ⟨n,hn⟩ := pow_unbounded_of_one_lt (a / escape c z)
        (by norm_num : (1 : ℝ) < 2)
      have hlt := (div_lt_iff₀ hp).mp hn
      have hle := hbound n ω z (mem_iInter.mp hz n)
      linarith
    refine ⟨⟨z,hg⟩, ?_⟩
    apply Subtype.ext
    rfl
  exact ⟨e,b,he,hb,hbi,hjb,hlim⟩

/-- Continuity of the genuine polynomial restricted to its bounded-orbit set. -/
theorem quadraticFilledMap_continuous (c : ℂ) :
    Continuous (quadraticFilledMap c) :=
  ((continuous_subtype_val.pow 2).add continuous_const).subtype_mk _

/-- The actual quadratic action on connected components, with no choice
of symbolic labeling in its definition. -/
def quadraticComponentMap (c : ℂ) :
    ConnectedComponents (quadraticFilled c) → ConnectedComponents (quadraticFilled c) :=
  (quadraticFilledMap_continuous c).connectedComponentsMap

theorem quadraticComponentMap_mk (c : ℂ) (z : quadraticFilled c) :
    quadraticComponentMap c (ConnectedComponents.mk z) =
      ConnectedComponents.mk (quadraticFilledMap c z) := rfl

/-- A coherent binary coding has exactly the genuine connected components
as fibers, and its quotient is a homeomorphism conjugating the actual
quadratic component action to the full one-sided binary shift. -/
theorem filled_binary_component_model (c : ℂ) (hc : 0 < escape c 0) :
    ∃ (e : quadraticFilled c ≃ₜ (Fin 2 × quadraticFilled c))
      (E : ConnectedComponents (quadraticFilled c) ≃ₜ (ℕ → Fin 2)),
      (∀ z, (e z).2 = quadraticFilledMap c z) ∧
      (∀ z : quadraticFilled c,
        connectedComponent z = {w | address e w = address e z}) ∧
      (∀ z, E (ConnectedComponents.mk z) = address e z) ∧
      Semiconj E (quadraticComponentMap c) shift := by
  letI : CompactSpace (sublevel c (escape c 0)) :=
    isCompact_iff_compactSpace.mp
      (quadratic_escape_sublevel_compact c (escape c 0) (escape_nonneg c 0))
  letI : PreconnectedSpace (sublevel c (escape c 0)) :=
    isPreconnected_iff_preconnectedSpace.mp
      (quadratic_escape_sublevel_connected_of_critical c (escape c 0) le_rfl).isPreconnected
  letI : CompactSpace (quadraticFilled c) :=
    isCompact_iff_compactSpace.mp (quadratic_filled_compact c)
  obtain ⟨z,hz⟩ := sublevel_nonempty c 0 le_rfl
  have hzK : z ∈ quadraticFilled c := by
    rwa [sublevel_zero_eq_filled c] at hz
  letI : Nonempty (quadraticFilled c) := ⟨⟨z,hzK⟩⟩
  obtain ⟨e,b,he,hb,hbi,hjb,hlim⟩ := filled_coherent_branch_system c hc
  let j := filledIntoCriticalSublevel c
  have hj := filledIntoCriticalSublevel_continuous c
  have hji := filledIntoCriticalSublevel_injective c
  obtain ⟨E,hE,hsemi⟩ := component_conjugacy j hj hji e b hb hbi hjb hlim
  have hstep : componentStep e = quadraticComponentMap c := by
    funext q
    obtain ⟨w,rfl⟩ := ConnectedComponents.surjective_coe q
    change ConnectedComponents.mk (step e w) =
      ConnectedComponents.mk (quadraticFilledMap c w)
    exact congrArg ConnectedComponents.mk (he w)
  rw [hstep] at hsemi
  exact ⟨e,E,he,component_eq_address_fiber j hj hji e b hb hbi hjb hlim,hE,hsemi⟩

/-- For every escaping critical parameter, the space of actual filled-set
components is homeomorphic to binary sequence space, and its actual
quadratic dynamics is conjugate to the shift. -/
theorem filled_component_conjugacy (c : ℂ) (hc : 0 < escape c 0) :
    ∃ E : ConnectedComponents (quadraticFilled c) ≃ₜ (ℕ → Fin 2),
      Semiconj E (quadraticComponentMap c) shift := by
  obtain ⟨_,E,_,_,_,hE⟩ := filled_binary_component_model c hc
  exact ⟨E,hE⟩

end
end LoopsQuadraticEscapeTree

import QuadraticEscapeFullness

/-!
# Local injectivity of the nonconstant quadratic geometric model

The archived fixed-reflection theorem identifies the exceptional
predecessor fiber. Connectedness and nontriviality now distinguish that
fiber from a degenerate one-point quotient: its point is exactly where
the actual model map has no injective open neighborhood.
-/

namespace LoopsStationaryModelBranchLocus

open Set Function
open LoopsStationaryFiberDynamics LoopsStationaryLightModel
open LoopsQuadraticEscapeFullness

variable {Y : Type*} [TopologicalSpace Y] [T2Space Y]

/-- On a connected nontrivial space, a continuous involution with one
fixed point and an open two-sheet orbit map gives an exact local
injectivity locus. Connectedness prevents the fixed point from being
isolated; each of its neighborhoods contains a paired collision. -/
theorem involution_local_injectivity_locus [PreconnectedSpace Y] [Nontrivial Y]
    (G S : Y → Y) (b : Y)
    (hSc : Continuous S) (hSi : Involutive S) (ho : IsOpenMap G)
    (hpair : ∀ y : Y, G ⁻¹' {G y} = {y, S y})
    (hfixed : ∀ y : Y, S y = y ↔ y = b) (y : Y) :
    (¬ ∃ U : Set Y, IsOpen U ∧ y ∈ U ∧ InjOn G U) ↔ y = b := by
  classical
  constructor
  · intro h
    by_contra hy
    have hne : S y ≠ y := fun he => hy ((hfixed y).mp he)
    obtain ⟨U, V, W, hU, _, _, hyU, _, _, _, _, _, _, hi, _⟩ :=
      involution_local_two_sheets G S hSc hSi ho hpair y hne
    exact h ⟨U, hU, hyU, hi⟩
  · intro hy
    subst y
    rintro ⟨U, hU, hbU, hi⟩
    let V : Set Y := U ∩ S ⁻¹' U
    have hV : IsOpen V := hU.inter (hU.preimage hSc)
    have hSb : S b = b := (hfixed b).mpr rfl
    have hGS (z : Y) : G (S z) = G z := by
      have hmem : S z ∈ G ⁻¹' {G z} := by
        rw [hpair z]
        exact Or.inr rfl
      exact hmem
    have he : V = {b} := by
      ext z
      constructor
      · intro hz
        have hzz : z = S z := hi hz.1 hz.2 (hGS z).symm
        exact (hfixed z).mp hzz.symm
      · intro hz
        have hz' : z = b := hz
        subst z
        exact ⟨hbU, by simpa only [mem_preimage, hSb] using hbU⟩
    have hsingleton : IsOpen ({b} : Set Y) := he ▸ hV
    have hclopen : IsClopen ({b} : Set Y) := ⟨isClosed_singleton, hsingleton⟩
    have hall : (univ : Set Y) ⊆ {b} :=
      isPreconnected_univ.subset_isClopen hclopen ⟨b, mem_univ b, mem_singleton b⟩
    obtain ⟨z, hz⟩ := exists_ne b
    exact hz (hall (mem_univ z))

/-- For every nontrivial monotone light quotient of the actual
empty-interior filled quadratic with bounded critical orbit, the
image of zero is exactly the failure locus of local injectivity.
The older exceptional-fiber theorem alone allowed a one-point model;
the explicit nontriviality hypothesis removes that degeneracy here.
No dendrite or physical local connectivity hypothesis is assumed. -/
theorem quadratic_filled_model_local_injectivity_locus [Nontrivial Y]
    (c : ℂ) (p : quadraticFilled c → Y) (G : Y → Y)
    (hp : Continuous p) (hsurj : Surjective p)
    (hs : Semiconj p (quadraticFilledMap c) G)
    (hf : ∀ y : Y, IsPreconnected (p ⁻¹' {y}))
    (hlight : ∀ y : Y, IsTotallyDisconnected (G ⁻¹' {y}))
    (hE : interior (quadraticFilled c) = ∅)
    (h0 : (0 : ℂ) ∈ quadraticFilled c) (y : Y) :
    (¬ ∃ U : Set Y, IsOpen U ∧ y ∈ U ∧ InjOn G U) ↔ y = p ⟨0, h0⟩ := by
  letI : ConnectedSpace (quadraticFilled c) :=
    isConnected_iff_connectedSpace.mp (quadratic_filled_connected_of_critical c h0)
  letI : ConnectedSpace Y := hsurj.connectedSpace hp
  obtain ⟨S, hSc, hSi, ho, hpair, hbranch⟩ :=
    quadratic_filled_light_model_exact_critical_branch c p G hp hsurj hs hf hlight hE
  have hfixed (w : Y) : S w = w ↔ w = p ⟨0, h0⟩ := by
    rw [← involution_singleton_fiber_iff G S hpair w, hbranch w]
    constructor
    · rintro ⟨x, hx, hpx⟩
      have he : x = (⟨0, h0⟩ : quadraticFilled c) := Subtype.ext hx
      rw [he] at hpx
      exact hpx.symm
    · intro hw
      exact ⟨⟨0, h0⟩, rfl, hw.symm⟩
  exact involution_local_injectivity_locus G S (p ⟨0, h0⟩)
    hSc hSi ho hpair hfixed y

omit [T2Space Y] in
/-- For a continuous open map, an iterate is injective on some open
neighborhood exactly when each factor is locally injective along the
finite orbit. Openness is essential in the forward implication: the
image of the earlier neighborhood must still be a neighborhood. -/
theorem iterate_local_injectivity_iff
    (G : Y → Y) (hc : Continuous G) (ho : IsOpenMap G) (n : ℕ) (y : Y) :
    (∃ U : Set Y, IsOpen U ∧ y ∈ U ∧ InjOn (G^[n]) U) ↔
      ∀ k < n, ∃ V : Set Y, IsOpen V ∧ (G^[k]) y ∈ V ∧ InjOn G V := by
  induction n generalizing y with
  | zero =>
    constructor
    · intro _ k hk
      omega
    · intro _
      exact ⟨univ, isOpen_univ, mem_univ _, fun _ _ _ _ h => h⟩
  | succ n ih =>
    constructor
    · rintro ⟨U, hU, hy, hi⟩
      have hfirst : InjOn G U := by
        intro a ha b hb hab
        apply hi ha hb
        simp only [Function.iterate_succ_apply, hab]
      have htail : InjOn (G^[n]) (G '' U) := by
        rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hab
        have he : a = b := hi ha hb (by
          simpa only [Function.iterate_succ_apply] using hab)
        exact congrArg G he
      have ht := (ih (G y)).mp ⟨G '' U, ho _ hU, ⟨y, hy, rfl⟩, htail⟩
      intro k hk
      cases k with
      | zero => exact ⟨U, hU, hy, hfirst⟩
      | succ k =>
        simpa only [Function.iterate_succ_apply] using ht k (by omega)
    · intro h
      obtain ⟨U, hU, hy, hfirst⟩ := h 0 (Nat.zero_lt_succ n)
      have htail : ∀ k < n, ∃ V : Set Y,
          IsOpen V ∧ (G^[k]) (G y) ∈ V ∧ InjOn G V := by
        intro k hk
        simpa only [Function.iterate_succ_apply] using h (k+1) (by omega)
      obtain ⟨V, hV, hGy, hi⟩ := (ih (G y)).mpr htail
      refine ⟨U ∩ G ⁻¹' V, hU.inter (hV.preimage hc), ⟨hy, hGy⟩, ?_⟩
      intro a ha b hb hab
      apply hfirst ha.1 hb.1
      apply hi ha.2 hb.2
      simpa only [Function.iterate_succ_apply] using hab

private theorem quadratic_filled_semiconjugate_continuous
    (c : ℂ) (p : quadraticFilled c → Y) (G : Y → Y)
    (hp : Continuous p) (hsurj : Surjective p)
    (hs : Semiconj p (quadraticFilledMap c) G) : Continuous G := by
  letI : CompactSpace (quadraticFilled c) :=
    isCompact_iff_compactSpace.mp (quadratic_filled_compact c)
  have hF : Continuous (quadraticFilledMap c) := by
    apply Continuous.subtype_mk
    exact ((continuous_subtype_val : Continuous
      (Subtype.val : quadraticFilled c → ℂ)).pow 2).add continuous_const
  have hquot : Topology.IsQuotientMap p := hp.isClosedMap.isQuotientMap hp hsurj
  apply hquot.continuous_iff.mpr
  have he : G ∘ p = p ∘ quadraticFilledMap c := funext fun x => (hs x).symm
  rw [he]
  exact hp.comp hF

/-- Exact topological ramification itinerary for every iterate of a
nontrivial geometric quadratic model. Continuity of the model map is
derived from the compact physical quotient, while connectedness of
the model is derived from the bounded critical orbit. The branch
locus is the finite union of the preimages of the image of zero. -/
theorem quadratic_filled_model_iterate_local_injectivity_iff [Nontrivial Y]
    (c : ℂ) (p : quadraticFilled c → Y) (G : Y → Y)
    (hp : Continuous p) (hsurj : Surjective p)
    (hs : Semiconj p (quadraticFilledMap c) G)
    (hf : ∀ y : Y, IsPreconnected (p ⁻¹' {y}))
    (hlight : ∀ y : Y, IsTotallyDisconnected (G ⁻¹' {y}))
    (hE : interior (quadraticFilled c) = ∅)
    (h0 : (0 : ℂ) ∈ quadraticFilled c) (n : ℕ) (y : Y) :
    (∃ U : Set Y, IsOpen U ∧ y ∈ U ∧ InjOn (G^[n]) U) ↔
      ∀ k < n, (G^[k]) y ≠ p ⟨0, h0⟩ := by
  classical
  have hc := quadratic_filled_semiconjugate_continuous c p G hp hsurj hs
  obtain ⟨_, _, _, ho, _, _⟩ :=
    quadratic_filled_light_model_exact_critical_branch c p G hp hsurj hs hf hlight hE
  rw [iterate_local_injectivity_iff G hc ho n y]
  constructor
  · intro h k hk he
    have hbad := (quadratic_filled_model_local_injectivity_locus
      c p G hp hsurj hs hf hlight hE h0 ((G^[k]) y)).mpr he
    exact hbad (h k hk)
  · intro h k hk
    by_contra hbad
    have he := (quadratic_filled_model_local_injectivity_locus
      c p G hp hsurj hs hf hlight hE h0 ((G^[k]) y)).mp hbad
    exact h k hk he

end LoopsStationaryModelBranchLocus

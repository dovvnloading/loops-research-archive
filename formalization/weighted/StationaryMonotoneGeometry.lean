import Mathlib
import PlanarFullification

/-!
# Closed monotone quotients and geometric marked continua

The physical filled Julia set and its canonical rational-cut quotient
must be supplied separately. All the statements here use actual sets
and their topologies, not a finite tree of incidence labels.
-/

namespace LoopsStationaryMonotoneGeometry

open Set
open LoopsFormal.ProtectedCarriers

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- Closed maps with preconnected fibers pull back arbitrary preconnected
sets. Neither local connectivity nor compactness of the target subset
is required. -/
theorem preconnected_preimage_closed_fibers (p : X → Y)
    (hp : IsClosedMap p) (hsurj : Function.Surjective p)
    (hf : ∀ y : Y, IsPreconnected (p ⁻¹' {y}))
    {S : Set Y} (hS : IsPreconnected S) :
    IsPreconnected (p ⁻¹' S) := by
  apply isPreconnected_closed_iff.mpr
  intro U V hU hV hcover hleft hright
  let A : Set Y := p '' U
  let B : Set Y := p '' V
  have hc : S ⊆ A ∪ B := by
    intro y hy
    obtain ⟨x, hxy⟩ := hsurj y
    have hx : x ∈ p ⁻¹' S := by
      change p x ∈ S
      rwa [hxy]
    rcases hcover hx with hxU | hxV
    · exact Or.inl ⟨x, hxU, hxy⟩
    · exact Or.inr ⟨x, hxV, hxy⟩
  have ha : (S ∩ A).Nonempty := by
    obtain ⟨x, hx, hxU⟩ := hleft
    exact ⟨p x, hx, ⟨x, hxU, rfl⟩⟩
  have hb : (S ∩ B).Nonempty := by
    obtain ⟨x, hx, hxV⟩ := hright
    exact ⟨p x, hx, ⟨x, hxV, rfl⟩⟩
  obtain ⟨y, hy, hyA, hyB⟩ :=
    (isPreconnected_closed_iff.mp hS) A B (hp U hU) (hp V hV) hc ha hb
  obtain ⟨a, haU, hay⟩ := hyA
  obtain ⟨b, hbV, hby⟩ := hyB
  have hsub : p ⁻¹' ({y} : Set Y) ⊆ U ∪ V := by
    intro z hz
    apply hcover
    change p z ∈ S
    change p z = y at hz
    rwa [hz]
  obtain ⟨z, hz, hzU, hzV⟩ :=
    (isPreconnected_closed_iff.mp (hf y)) U V hU hV hsub
      ⟨a, hay, haU⟩ ⟨b, hby, hbV⟩
  refine ⟨z, ?_, hzU, hzV⟩
  change p z ∈ S
  change p z = y at hz
  rwa [hz]

/-- Exact connected-component transport on every saturated subset. -/
theorem component_preimage_closed_fibers (p : X → Y)
    (hp : IsClosedMap p) (hc : Continuous p) (hsurj : Function.Surjective p)
    (hf : ∀ y : Y, IsPreconnected (p ⁻¹' {y}))
    (S : Set Y) (x : X) (hx : p x ∈ S) :
    connectedComponentIn (p ⁻¹' S) x =
      p ⁻¹' connectedComponentIn S (p x) := by
  apply Subset.antisymm
  · have hconn : IsPreconnected (p '' connectedComponentIn (p ⁻¹' S) x) :=
      isPreconnected_connectedComponentIn.image p hc.continuousOn
    have hmem : p x ∈ p '' connectedComponentIn (p ⁻¹' S) x :=
      ⟨x, mem_connectedComponentIn hx, rfl⟩
    have hsub : p '' connectedComponentIn (p ⁻¹' S) x ⊆ S := by
      rintro _ ⟨z, hz, rfl⟩
      exact connectedComponentIn_subset (p ⁻¹' S) x hz
    intro z hz
    exact hconn.subset_connectedComponentIn hmem hsub ⟨z, hz, rfl⟩
  · have hconn : IsPreconnected (p ⁻¹' connectedComponentIn S (p x)) :=
      preconnected_preimage_closed_fibers p hp hsurj hf isPreconnected_connectedComponentIn
    exact hconn.subset_connectedComponentIn (mem_connectedComponentIn hx)
      (fun z hz => show p z ∈ S from connectedComponentIn_subset S (p x) hz)

/-- In the compact Hausdorff quotient setting, a singleton fiber at a
root is sufficient for exact transport of the entire punctured
component, not just its image or a marked vertex. -/
theorem punctured_component_full_lift [CompactSpace X] [T2Space Y]
    (p : X → Y) (hc : Continuous p) (hsurj : Function.Surjective p)
    (hf : ∀ y : Y, IsPreconnected (p ⁻¹' {y}))
    (a x : X) (ha : p ⁻¹' ({p a} : Set Y) = {a}) (hx : x ≠ a) :
    connectedComponentIn ({a} : Set X)ᶜ x =
      p ⁻¹' connectedComponentIn ({p a} : Set Y)ᶜ (p x) := by
  have heq : p ⁻¹' ({p a} : Set Y)ᶜ = ({a} : Set X)ᶜ := by
    rw [preimage_compl, ha]
  rw [← heq]
  apply component_preimage_closed_fibers p hc.isClosedMap hc hsurj hf
  change p x ≠ p a
  intro h
  have h' : x ∈ p ⁻¹' ({p a} : Set Y) := h
  rw [ha] at h'
  exact hx h'

/-- Hereditary unicoherence rules out two disjoint connected bridges
joining the same two disjoint nonempty closed connected marks.
No path or local-connectivity hypothesis is used. -/
theorem disjoint_bridges_impossible
    (A B C D : Set X)
    (hu : ∀ U V : Set X, IsClosed U → IsClosed V →
      IsConnected U → IsConnected V → IsPreconnected (U ∩ V))
    (hAc : IsClosed A) (hBc : IsClosed B) (hCc : IsClosed C) (hDc : IsClosed D)
    (hA : IsConnected A) (hB : IsConnected B)
    (hC : IsConnected C) (hD : IsConnected D)
    (hAB : Disjoint A B) (hCD : Disjoint C D)
    (hAC : (A ∩ C).Nonempty) (hBC : (B ∩ C).Nonempty)
    (hAD : (A ∩ D).Nonempty) (hBD : (B ∩ D).Nonempty) : False := by
  have h1 : IsConnected (A ∪ C ∪ B) := by
    apply IsConnected.union _ (IsConnected.union hAC hA hC) hB
    obtain ⟨b, hb, hbC⟩ := hBC
    exact ⟨b, Or.inr hbC, hb⟩
  have h2 : IsConnected (A ∪ D ∪ B) := by
    apply IsConnected.union _ (IsConnected.union hAD hA hD) hB
    obtain ⟨b, hb, hbD⟩ := hBD
    exact ⟨b, Or.inr hbD, hb⟩
  have hi := hu (A ∪ C ∪ B) (A ∪ D ∪ B)
    ((hAc.union hCc).union hBc) ((hAc.union hDc).union hBc) h1 h2
  have heq : (A ∪ C ∪ B) ∩ (A ∪ D ∪ B) = A ∪ B := by
    ext z
    simp only [mem_inter_iff, mem_union]
    have hd : ¬ (z ∈ C ∧ z ∈ D) := fun h => Set.disjoint_left.mp hCD h.1 h.2
    tauto
  rw [heq] at hi
  obtain ⟨a, ha⟩ := hA.nonempty
  obtain ⟨b, hb⟩ := hB.nonempty
  obtain ⟨z, _, hzA, hzB⟩ := (isPreconnected_closed_iff.mp hi) A B hAc hBc
    Subset.rfl ⟨a, Or.inl ha, ha⟩ ⟨b, Or.inr hb, hb⟩
  exact Set.disjoint_left.mp hAB hzA hzB

/-- A semiconjugacy with connected fibers cannot identify two disjoint
invariant geometric continua if all nonsingleton fibers are nonfixed
under the specified return. This is the wandering-fiber argument
applied to the return map, with hereditary unicoherence explicit. -/
theorem invariant_marks_disjoint_image [T1Space Y]
    (p : X → Y) (F : X → X) (G : Y → Y)
    (hp : Continuous p) (hf : ∀ y : Y, IsConnected (p ⁻¹' {y}))
    (hsemi : ∀ x, p (F x) = G (p x))
    (hw : ∀ y : Y, ¬ (p ⁻¹' {y}).Subsingleton → G y ≠ y)
    (hu : ∀ U V : Set X, IsClosed U → IsClosed V →
      IsConnected U → IsConnected V → IsPreconnected (U ∩ V))
    (A B : Set X) (hAc : IsClosed A) (hBc : IsClosed B)
    (hA : IsConnected A) (hB : IsConnected B) (hAB : Disjoint A B)
    (hFA : MapsTo F A A) (hFB : MapsTo F B B) :
    Disjoint (p '' A) (p '' B) := by
  apply Set.disjoint_left.mpr
  intro y hyA hyB
  obtain ⟨a, ha, hay⟩ := hyA
  obtain ⟨b, hb, hby⟩ := hyB
  let C : Set X := p ⁻¹' {y}
  let D : Set X := p ⁻¹' {G y}
  have haC : a ∈ C := hay
  have hbC : b ∈ C := hby
  have hn : ¬ C.Subsingleton := by
    intro hs
    have hab : a = b := hs haC hbC
    exact Set.disjoint_left.mp hAB (hab ▸ ha) hb
  have hneq : G y ≠ y := hw y hn
  have hCD : Disjoint C D := by
    apply Set.disjoint_left.mpr
    intro z hz hz'
    change p z = y at hz
    change p z = G y at hz'
    exact hneq (hz'.symm.trans hz)
  have haD : F a ∈ D := by
    change p (F a) = G y
    rw [hsemi, hay]
  have hbD : F b ∈ D := by
    change p (F b) = G y
    rw [hsemi, hby]
  exact disjoint_bridges_impossible A B C D hu hAc hBc
    (isClosed_singleton.preimage hp) (isClosed_singleton.preimage hp)
    (hA) (hB) (hf y) (hf (G y)) hAB hCD
    ⟨a, ha, haC⟩ ⟨b, hb, hbC⟩ ⟨F a, hFA ha, haD⟩ ⟨F b, hFB hb, hbD⟩


/-- Exact full-preimage selected predecessor identity at arbitrary depth
for a semiconjugacy with closed connected fibers. The selected component
is an actual connected component of the complement of a root. -/
theorem selected_predecessor_full_lift [CompactSpace X] [T2Space Y]
    (p : X → Y) (F : X → X) (G : Y → Y)
    (hp : Continuous p) (hsurj : Function.Surjective p)
    (hf : ∀ y : Y, IsPreconnected (p ⁻¹' {y}))
    (hsemi : Function.Semiconj p F G)
    (B : Set Y) (a x : X) (ha : p ⁻¹' ({p a} : Set Y) = {a})
    (hx : x ≠ a) (n : ℕ) :
    p ⁻¹' ((G^[n]) ⁻¹' B ∩ connectedComponentIn ({p a} : Set Y)ᶜ (p x)) =
      (F^[n]) ⁻¹' (p ⁻¹' B) ∩ connectedComponentIn ({a} : Set X)ᶜ x := by
  rw [preimage_inter, ← punctured_component_full_lift p hp hsurj hf a x ha hx]
  ext z
  have hz : p ((F^[n]) z) = (G^[n]) (p z) := hsemi.iterate_right n z
  simp only [mem_inter_iff, mem_preimage, hz]

/-- A least compact connected carrier cannot enter a terminal open
region that contains no marked point, if its entire frontier is one
point outside the region. The proof constructs the continuous pruning
map, rather than assuming local connectivity or a graph model. -/
theorem least_carrier_terminal_incidence {ι : Type*}
    (K : ι → Set X) (S O : Set X) (a : X)
    (hSc : IsCompact S) (hS : IsConnected S)
    (hK : ∀ i, K i ⊆ S)
    (hleast : ∀ U : Set X, IsCompact U → IsConnected U →
      (∀ i, K i ⊆ U) → S ⊆ U)
    (hfront : frontier O ⊆ {a}) (ha : a ∉ O)
    (hSO : (S ∩ O).Nonempty) :
    ∃ i, (K i ∩ O).Nonempty := by
  classical
  by_contra hnot
  have hmiss : ∀ i, ∀ z ∈ K i, z ∉ O := by
    intro i z hz hO
    exact hnot ⟨i, z, hz, hO⟩
  let r : X → X := O.piecewise (fun _ => a) id
  have hr : Continuous r := by
    dsimp [r]
    apply Continuous.piecewise
    · intro z hz
      exact (show z = a from hfront hz).symm
    · exact continuous_const
    · exact continuous_id
  have hmarks : ∀ i, K i ⊆ r '' S := by
    intro i z hz
    refine ⟨z, hK i hz, ?_⟩
    simp [r, hmiss i z hz]
  have hsub := hleast (r '' S) (hSc.image hr) (hS.image r hr.continuousOn) hmarks
  obtain ⟨w, hwS, hwO⟩ := hSO
  obtain ⟨v, _, hv⟩ := hsub hwS
  by_cases hvO : v ∈ O
  · have he : a = w := by simpa [r, Set.piecewise, hvO] using hv
    exact ha (he.symm ▸ hwO)
  · have he : v = w := by simpa [r, Set.piecewise, hvO] using hv
    exact hvO (he.symm ▸ hwO)

/-- If an intermediate carrier has no extra quotient points, then
occupancy of a saturated terminal sheet is detected already on the
least carrier. A connected mark avoiding the root is contained in the
whole sheet; forward invariance of its carrier puts the entire mark
in the selected predecessor, with no finite-tree incidence premise. -/
omit [TopologicalSpace Y] in
theorem selected_predecessor_contains_mark {ι : Type*}
    (p : X → Y) (F : X → X) (K : ι → Set X)
    (S T : Set X) (a x : X) (V : Set Y) (n : ℕ)
    (hSc : IsCompact S) (hS : IsConnected S)
    (hK : ∀ i, K i ⊆ S)
    (hleast : ∀ U : Set X, IsCompact U → IsConnected U →
      (∀ i, K i ⊆ U) → S ⊆ U)
    (hST : S ⊆ T) (himg : p '' T ⊆ p '' S)
    (hconn : ∀ i, IsPreconnected (K i)) (havoid : ∀ i, a ∉ K i)
    (hF : MapsTo F T T)
    (hsat : connectedComponentIn ({a} : Set X)ᶜ x = p ⁻¹' V)
    (hfront : frontier (connectedComponentIn ({a} : Set X)ᶜ x) ⊆ {a})
    (hhit : (T ∩ connectedComponentIn ({a} : Set X)ᶜ x).Nonempty) :
    ∃ i, K i ⊆ (F^[n]) ⁻¹' T ∩ connectedComponentIn ({a} : Set X)ᶜ x := by
  let O := connectedComponentIn ({a} : Set X)ᶜ x
  have hO : O ⊆ ({a} : Set X)ᶜ := connectedComponentIn_subset _ _
  have ha : a ∉ O := by
    intro haO
    exact hO haO (mem_singleton a)
  have hSO : (S ∩ O).Nonempty := by
    obtain ⟨w, hwT, hwO⟩ := hhit
    obtain ⟨z, hzS, hzw⟩ := himg ⟨w, hwT, rfl⟩
    have hwV : p w ∈ V := by
      change w ∈ O at hwO
      rw [show O = p ⁻¹' V from hsat] at hwO
      exact hwO
    refine ⟨z, hzS, ?_⟩
    rw [show O = p ⁻¹' V from hsat]
    change p z ∈ V
    rwa [hzw]
  obtain ⟨i, w, hwK, hwO⟩ :=
    least_carrier_terminal_incidence K S O a hSc hS hK hleast hfront ha hSO
  have hKW : K i ⊆ ({a} : Set X)ᶜ := by
    intro z hz hz'
    have he : z = a := hz'
    exact havoid i (he ▸ hz)
  have hsub : K i ⊆ O := by
    have h' := (hconn i).subset_connectedComponentIn hwK hKW
    rw [← connectedComponentIn_eq hwO] at h'
    exact h'
  have hFn : MapsTo (F^[n]) T T := hF.iterate n
  exact ⟨i, fun z hz => ⟨hFn (hST (hK i hz)), hsub hz⟩⟩


/-- The actual least continuum exists for every nonempty marked subset
of a compact Hausdorff connected space satisfying hereditary
unicoherence. Compactness and directed intersection are proved here;
leastness is not an additional premise. -/
theorem least_compact_connected_carrier_exists [CompactSpace X] [T2Space X]
    (M : Set X) (hM : M.Nonempty) (hX : IsConnected (univ : Set X))
    (hu : ∀ U V : Set X, IsClosed U → IsClosed V →
      IsConnected U → IsConnected V → IsPreconnected (U ∩ V)) :
    ∃ S : Set X, IsCompact S ∧ IsConnected S ∧ M ⊆ S ∧
      ∀ U : Set X, IsCompact U → IsConnected U → M ⊆ U → S ⊆ U := by
  classical
  let I := {U : Set X // IsClosed U ∧ IsConnected U ∧ M ⊆ U}
  letI : Nonempty I := ⟨⟨univ, isClosed_univ, hX, subset_univ M⟩⟩
  let S : Set X := ⋂ i : I, i.val
  have hSclosed : IsClosed S := isClosed_iInter fun i : I => i.property.1
  have hMS : M ⊆ S := by
    intro z hz
    exact mem_iInter.mpr fun i : I => i.property.2.2 hz
  refine ⟨S, hSclosed.isCompact, ⟨hM.mono hMS, ?_⟩, hMS, ?_⟩
  · apply (isPreconnected_iff_subset_of_fully_disjoint_closed hSclosed).mpr
    intro A B hAc hBc hcov hAB
    obtain ⟨U, V, hU, hV, hAU, hBV, hUV⟩ := normal_separation hAc hBc hAB
    have hcovUV : S ⊆ U ∪ V := hcov.trans (union_subset_union hAU hBV)
    have hd : Directed (· ⊇ ·) (fun i : I => i.val) := by
      intro i j
      have hMij : M ⊆ i.val ∩ j.val := fun _ hz =>
        ⟨i.property.2.2 hz, j.property.2.2 hz⟩
      have hcij : IsConnected (i.val ∩ j.val) :=
        ⟨hM.mono hMij, hu i.val j.val i.property.1 j.property.1
          i.property.2.1 j.property.2.1⟩
      exact ⟨⟨i.val ∩ j.val, i.property.1.inter j.property.1, hcij, hMij⟩,
        inter_subset_left, inter_subset_right⟩
    have hdis : (U ∪ V)ᶜ ∩ (⋂ i : I, i.val) = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro z hz
      exact hz.1 (hcovUV hz.2)
    obtain ⟨i, hi⟩ := (hU.union hV).isClosed_compl.isCompact.elim_directed_family_closed
      (fun i : I => i.val) (fun i => i.property.1) hdis hd
    have hiUV : i.val ⊆ U ∪ V := by
      intro z hz
      by_contra hn
      have hh : z ∈ (U ∪ V)ᶜ ∩ i.val := ⟨hn, hz⟩
      rw [hi] at hh
      exact hh
    have hSi : S ⊆ i.val := iInter_subset (fun i : I => i.val) i
    rcases IsPreconnected.subset_or_subset hU hV hUV hiUV i.property.2.1.isPreconnected with h | h
    · left
      intro z hz
      rcases hcov hz with hzA | hzB
      · exact hzA
      · exact False.elim (Set.disjoint_left.mp hUV (h (hSi hz)) (hBV hzB))
    · right
      intro z hz
      rcases hcov hz with hzA | hzB
      · exact False.elim (Set.disjoint_left.mp hUV (hAU hzA) (h (hSi hz)))
      · exact hzB
  · intro U hUc hUconn hMU
    exact iInter_subset (fun i : I => i.val) ⟨U, hUc.isClosed, hUconn, hMU⟩

/-- A least physical continuum projects onto the least model continuum.
The full inverse of the model hull is connected by the proved
closed-fiber theorem, so no independent saturation assumption on the
least physical continuum is used. -/
theorem least_carrier_image_eq [CompactSpace X] [T2Space Y]
    (p : X → Y) (hp : Continuous p) (hsurj : Function.Surjective p)
    (hf : ∀ y : Y, IsPreconnected (p ⁻¹' {y}))
    (M S : Set X) (B : Set Y)
    (hSc : IsCompact S) (hS : IsConnected S) (hMS : M ⊆ S)
    (hleastS : ∀ U : Set X, IsCompact U → IsConnected U → M ⊆ U → S ⊆ U)
    (hBc : IsCompact B) (hB : IsConnected B) (hMB : p '' M ⊆ B)
    (hleastB : ∀ V : Set Y, IsCompact V → IsConnected V → p '' M ⊆ V → B ⊆ V) :
    p '' S = B := by
  have hpreconn : IsConnected (p ⁻¹' B) := by
    refine ⟨?_, preconnected_preimage_closed_fibers p hp.isClosedMap hsurj hf hB.isPreconnected⟩
    obtain ⟨y, hy⟩ := hB.nonempty
    obtain ⟨z, rfl⟩ := hsurj y
    exact ⟨z, hy⟩
  have hSsub : S ⊆ p ⁻¹' B :=
    hleastS _ (hBc.isClosed.preimage hp).isCompact hpreconn
      (fun z hz => hMB ⟨z, hz, rfl⟩)
  apply Subset.antisymm
  · rintro _ ⟨z, hz, rfl⟩
    exact hSsub hz
  · exact hleastB _ (hSc.image hp) (hS.image p hp.continuousOn) (image_mono hMS)

/-- The intersection of a physical continuum and the full inverse of a
path-connected model region is preconnected. Every pair of physical
points has a compact connected bridge, obtained by lifting the
actual path image and intersecting via hereditary unicoherence. -/
theorem preconnected_inter_preimage_path_connected [CompactSpace X] [T2Space Y]
    (p : X → Y) (hp : Continuous p) (hsurj : Function.Surjective p)
    (hf : ∀ y : Y, IsPreconnected (p ⁻¹' {y}))
    (hu : ∀ U V : Set X, IsClosed U → IsClosed V →
      IsConnected U → IsConnected V → IsPreconnected (U ∩ V))
    (U : Set X) (V : Set Y) (hUc : IsClosed U) (hU : IsConnected U)
    (hV : IsPathConnected V) :
    IsPreconnected (U ∩ p ⁻¹' V) := by
  apply isPreconnected_of_forall_pair
  intro a ha b hb
  obtain ⟨g, hg⟩ := hV.joinedIn (p a) ha.2 (p b) hb.2
  let C : Set Y := range (⇑g)
  have hCc : IsCompact C := isCompact_range g.continuous
  have hCV : C ⊆ V := range_subset_iff.mpr hg
  have hCpre : IsConnected (p ⁻¹' C) :=
    ⟨⟨a, g.source_mem_range⟩,
      preconnected_preimage_closed_fibers p hp.isClosedMap hsurj hf
        (isPreconnected_range g.continuous)⟩
  refine ⟨U ∩ p ⁻¹' C, ?_, ⟨ha.1, g.source_mem_range⟩,
    ⟨hb.1, g.target_mem_range⟩, hu U (p ⁻¹' C) hUc (hCc.isClosed.preimage hp) hU hCpre⟩
  exact fun _ hz => ⟨hz.1, hCV hz.2⟩

/-- Every compact subset of an actual full empty-interior plane set
has connected complement and is itself full. Any bounded complementary
component would be an open subset of the ambient set, impossible.
This is the planar half of the hereditary-unicoherence argument. -/
theorem compact_subset_full_of_full_empty_interior
    (K A : Set ℂ) (hA : IsCompact A) (hAK : A ⊆ K)
    (hKfull : LoopsFormal.ProtectedCarriers.planarFill K = K)
    (hKempty : interior K = ∅) :
    LoopsFormal.ProtectedCarriers.planarFill A = A ∧ IsConnected Aᶜ := by
  have hfull : planarFill A = A := by
    apply Subset.antisymm _ (planarFill_extensive A)
    intro z hz
    by_contra hza
    have hcomp : IsOpen (connectedComponentIn Aᶜ z) :=
      hA.isClosed.isOpen_compl.connectedComponentIn
    have hsub : connectedComponentIn Aᶜ z ⊆ K := by
      intro w hw
      have hwfill : w ∈ planarFill A := by
        change Bornology.IsBounded (connectedComponentIn Aᶜ w)
        rw [← connectedComponentIn_eq hw]
        exact hz
      have hwK := planarFill_mono hAK hwfill
      rwa [hKfull] at hwK
    have hzz : z ∈ connectedComponentIn Aᶜ z :=
      mem_connectedComponentIn (show z ∈ Aᶜ from hza)
    have hzi := interior_maximal hsub hcomp hzz
    rw [hKempty] at hzi
    exact hzi
  refine ⟨hfull, ?_⟩
  obtain ⟨z, hz, _, he, _⟩ := LoopsFormal.ProtectedCarriers.planarFill_exterior hA.isBounded
  rw [hfull] at he
  rw [he]
  exact isConnected_connectedComponentIn_iff.mpr hz

end LoopsStationaryMonotoneGeometry

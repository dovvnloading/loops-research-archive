import QuadraticMergerBalance

/-!
# Exact component naturality from critical charge and reflection debt

The scalar certificate below controls the full geometric inverse trace of
every retained target subset. A failed certificate supplies an actual
omitted inverse point over every retained target value.
-/

namespace LoopsQuadraticMergerBalance

open Set Function Classical
open LoopsQuadraticCylinderCensus LoopsQuadraticCylinderRamification
open LoopsQuadraticComponentFiberDegree LoopsQuadraticEnlargementDegree
open scoped BigOperators

noncomputable section

/-- The selected old component is always an entry of the actual census. -/
theorem selected_mem_mergerCensus (c : ℂ) (n : ℕ) (U V : Set ℂ)
    (hUV : U ⊆ V) (hUo : IsOpen U) (hUc : IsPreconnected U)
    (x y : ℂ) (hx : (quad c)^[n] x ∈ U) (hy : y ∈ U) :
    connectedComponentIn ((quad c)^[n] ⁻¹' U) x ∈ mergerCensus c n U V x y := by
  exact (mem_mergerCensus c n U V hUV hUo hUc x y hy _).mpr
    ⟨x, mem_connectedComponentIn (hUV hx), hx, rfl⟩

/-- One actual old component in the census is exactly the Cartesian
retained-source equality, without regular-value assumptions. -/
theorem mergerCensus_singleton_iff_cartesian (c : ℂ) (n : ℕ) (U V : Set ℂ)
    (hUV : U ⊆ V) (hUo : IsOpen U) (hUc : IsPreconnected U)
    (x y : ℂ) (hx : (quad c)^[n] x ∈ U) (hy : y ∈ U) :
    mergerCensus c n U V x y = {connectedComponentIn ((quad c)^[n] ⁻¹' U) x} ↔
      connectedComponentIn ((quad c)^[n] ⁻¹' V) x ∩ ((quad c)^[n] ⁻¹' U) =
        connectedComponentIn ((quad c)^[n] ⁻¹' U) x := by
  let f := (quad c)^[n]
  let A := connectedComponentIn (f ⁻¹' U) x
  let B := connectedComponentIn (f ⁻¹' V) x
  have hAB : A ⊆ B := connectedComponentIn_mono x (preimage_mono hUV)
  change mergerCensus c n U V x y = {A} ↔ B ∩ f ⁻¹' U = A
  constructor
  · intro hC
    apply Subset.antisymm
    · intro z hz
      have hzC : connectedComponentIn (f ⁻¹' U) z ∈ mergerCensus c n U V x y :=
        (mem_mergerCensus c n U V hUV hUo hUc x y hy _).mpr
          ⟨z, hz.1, hz.2, rfl⟩
      rw [hC, Finset.mem_singleton] at hzC
      exact hzC ▸ mem_connectedComponentIn hz.2
    · intro z hz
      exact ⟨hAB hz, connectedComponentIn_subset (f ⁻¹' U) x hz⟩
  · intro hcart
    ext D
    simp only [Finset.mem_singleton]
    constructor
    · intro hD
      obtain ⟨a, haB, haU, hDa⟩ :=
        (mem_mergerCensus c n U V hUV hUo hUc x y hy D).mp hD
      have haA : a ∈ A := hcart ▸ (show a ∈ B ∩ f ⁻¹' U from ⟨haB, haU⟩)
      exact hDa.trans (connectedComponentIn_eq haA).symm
    · rintro rfl
      exact selected_mem_mergerCensus c n U V hUV hUo hUc x y hx hy

/-- The selected old debt never exceeds the enlarged debt plus the
newly admitted critical charge. Every competing component consumes at
least one additional unit of this exact budget. -/
theorem selected_debt_le_enlargement_charge (c : ℂ) (n : ℕ) (U V : Set ℂ)
    (hUV : U ⊆ V) (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hVo : IsOpen V) (hVc : IsPreconnected V)
    (x y : ℂ) (hx : (quad c)^[n] x ∈ U) (hy : y ∈ U) :
    componentReflectionDebt c U n x ≤
      componentReflectionDebt c V n x + newCriticalCharge c n U V x := by
  let C := mergerCensus c n U V x y
  let A := connectedComponentIn ((quad c)^[n] ⁻¹' U) x
  have hA : A ∈ C := selected_mem_mergerCensus c n U V hUV hUo hUc x y hx hy
  have hpos : 0 < C.card := Finset.card_pos.mpr ⟨A, hA⟩
  have hle : componentDebt c n U A ≤ ∑ D ∈ C, componentDebt c n U D :=
    Finset.single_le_sum (f := fun D : Set ℂ => componentDebt c n U D)
      (fun D _ => Nat.zero_le (componentDebt c n U D)) hA
  have hbal := merger_balance_any_anchor c n U V hUV hUo hUc hVo hVc x y (hUV hx) hy
  have he := componentDebt_eq c n U hUo x hx
  change componentDebt c n U A = _ at he
  change C.card + (∑ D ∈ C, componentDebt c n U D) = _ at hbal
  omega

/-- Exact scalar recognition of a retained Cartesian component.
The certificate uses the selected old debt, the enlarged debt, and the
critical charge of new target values; it does not enumerate other old
components or assume equality of inverse fibers. -/
theorem quadratic_enlargement_cartesian_iff_charge (c : ℂ) (n : ℕ) (U V : Set ℂ)
    (hUV : U ⊆ V) (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hVo : IsOpen V) (hVc : IsPreconnected V)
    (x y : ℂ) (hx : (quad c)^[n] x ∈ U) (hy : y ∈ U) :
    connectedComponentIn ((quad c)^[n] ⁻¹' V) x ∩ ((quad c)^[n] ⁻¹' U) =
        connectedComponentIn ((quad c)^[n] ⁻¹' U) x ↔
      componentReflectionDebt c V n x + newCriticalCharge c n U V x =
        componentReflectionDebt c U n x := by
  let C := mergerCensus c n U V x y
  let A := connectedComponentIn ((quad c)^[n] ⁻¹' U) x
  have hA : A ∈ C := selected_mem_mergerCensus c n U V hUV hUo hUc x y hx hy
  have hbal := merger_balance_any_anchor c n U V hUV hUo hUc hVo hVc x y (hUV hx) hy
  have hdebt := componentDebt_eq c n U hUo x hx
  change componentDebt c n U A = _ at hdebt
  change C.card + (∑ D ∈ C, componentDebt c n U D) = _ at hbal
  rw [← mergerCensus_singleton_iff_cartesian c n U V hUV hUo hUc x y hx hy]
  change C = {A} ↔ _
  constructor
  · intro he
    rw [he] at hbal
    simp only [Finset.card_singleton, Finset.sum_singleton, hdebt] at hbal
    omega
  · intro hcharge
    have hle : componentDebt c n U A ≤ ∑ D ∈ C, componentDebt c n U D :=
      Finset.single_le_sum (f := fun D : Set ℂ => componentDebt c n U D)
        (fun D _ => Nat.zero_le (componentDebt c n U D)) hA
    have hcard : C.card = 1 := by
      have hpos : 0 < C.card := Finset.card_pos.mpr ⟨A, hA⟩
      omega
    obtain ⟨D, hD⟩ := Finset.card_eq_one.mp hcard
    have hAD : A = D := by simpa only [hD, Finset.mem_singleton] using hA
    simpa only [hAD] using hD

/-- The same exact charge test preserves the complete geometric
inverse trace of every retained target subset, including disconnected
traces. It is not a statement about only parametrized path lifts. -/
theorem quadratic_enlargement_all_traces_iff_charge (c : ℂ) (n : ℕ) (U V : Set ℂ)
    (hUV : U ⊆ V) (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hVo : IsOpen V) (hVc : IsPreconnected V)
    (x y : ℂ) (hx : (quad c)^[n] x ∈ U) (hy : y ∈ U) :
    (∀ S : Set ℂ, S ⊆ U →
      connectedComponentIn ((quad c)^[n] ⁻¹' V) x ∩ ((quad c)^[n] ⁻¹' S) =
        connectedComponentIn ((quad c)^[n] ⁻¹' U) x ∩ ((quad c)^[n] ⁻¹' S)) ↔
      componentReflectionDebt c V n x + newCriticalCharge c n U V x =
        componentReflectionDebt c U n x := by
  let f := (quad c)^[n]
  let A := connectedComponentIn (f ⁻¹' U) x
  let B := connectedComponentIn (f ⁻¹' V) x
  have hApre : A ⊆ f ⁻¹' U := connectedComponentIn_subset (f ⁻¹' U) x
  have hAB : A ⊆ B := connectedComponentIn_mono x (preimage_mono hUV)
  rw [← quadratic_enlargement_cartesian_iff_charge c n U V hUV hUo hUc hVo hVc
    x y hx hy]
  change (∀ S : Set ℂ, S ⊆ U → B ∩ f ⁻¹' S = A ∩ f ⁻¹' S) ↔ B ∩ f ⁻¹' U = A
  constructor
  · intro h
    exact (h U Subset.rfl).trans (inter_eq_left.mpr hApre)
  · intro h S hSU
    apply Subset.antisymm
    · intro z hz
      have hzA : z ∈ A := h ▸ (show z ∈ B ∩ f ⁻¹' U from ⟨hz.1, hSU hz.2⟩)
      exact ⟨hzA, hz.2⟩
    · exact fun _ hz => ⟨hAB hz.1, hz.2⟩

/-- A failed scalar certificate yields an actual missing source point
over any specified retained target value, including critical values.
Thus the defect is witnessed on every complete retained fiber. -/
theorem quadratic_enlargement_charge_iff_missing_point (c : ℂ) (n : ℕ) (U V : Set ℂ)
    (hUV : U ⊆ V) (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hVo : IsOpen V) (hVc : IsPreconnected V)
    (x y : ℂ) (hx : (quad c)^[n] x ∈ U) (hy : y ∈ U)
    (t : ℂ) (ht : t ∈ U) :
    componentReflectionDebt c U n x <
        componentReflectionDebt c V n x + newCriticalCharge c n U V x ↔
      ∃ z ∈ connectedComponentIn ((quad c)^[n] ⁻¹' V) x,
        (quad c)^[n] z = t ∧ z ∉ connectedComponentIn ((quad c)^[n] ⁻¹' U) x := by
  let A := connectedComponentIn ((quad c)^[n] ⁻¹' U) x
  let B := connectedComponentIn ((quad c)^[n] ⁻¹' V) x
  have hAB : A ⊆ B := connectedComponentIn_mono x (preimage_mono hUV)
  have hsub : localFiber c n A t ⊆ localFiber c n B t := by
    intro z hz
    obtain ⟨hzA, hzt⟩ := (mem_localFiber c n A t z).mp hz
    exact (mem_localFiber c n B t z).mpr ⟨hAB hzA, hzt⟩
  have hle := selected_debt_le_enlargement_charge c n U V hUV hUo hUc hVo hVc
    x y hx hy
  have heq := quadratic_enlargement_cartesian_iff_charge c n U V hUV hUo hUc hVo hVc
    x y hx hy
  have hfib := quadratic_enlargement_no_merger_iff_fiber_eq c n U V hUV hUo hUc
    x hx t ht
  change localFiber c n A t = localFiber c n B t ↔ _ at hfib
  constructor
  · intro hlt
    have hne : localFiber c n A t ≠ localFiber c n B t := by
      intro he
      have hc := heq.mp (hfib.mp he)
      omega
    have hnot : ¬ localFiber c n B t ⊆ localFiber c n A t := by
      intro h
      exact hne (Finset.Subset.antisymm hsub h)
    obtain ⟨z, hzB, hzA⟩ := Finset.not_subset.mp hnot
    obtain ⟨hz, hzt⟩ := (mem_localFiber c n B t z).mp hzB
    refine ⟨z, hz, hzt, ?_⟩
    intro ha
    exact hzA ((mem_localFiber c n A t z).mpr ⟨ha, hzt⟩)
  · rintro ⟨z, hzB, hzt, hzA⟩
    have hne : componentReflectionDebt c V n x + newCriticalCharge c n U V x ≠
        componentReflectionDebt c U n x := by
      intro he
      have hf := hfib.mpr (heq.mpr he)
      have hz : z ∈ localFiber c n B t := (mem_localFiber c n B t z).mpr ⟨hzB, hzt⟩
      rw [← hf] at hz
      exact hzA ((mem_localFiber c n A t z).mp hz).1
    omega

end
end LoopsQuadraticMergerBalance

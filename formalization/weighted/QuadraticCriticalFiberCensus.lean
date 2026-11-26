import QuadraticCylinderCensus

/-!
# Ramification-aware exact inverse-fiber census

A quadratic inverse step has two distinct points except at the critical
value. Counting these actual branches gives the exact defect from the
global degree at every target, including repeated postcritical hits.
-/
namespace LoopsQuadraticCriticalFiberCensus

open Set Function
open LoopsQuadraticCylinderCensus
open Classical

noncomputable section

/-- Surjectivity of the actual complex quadratic follows from its
proved open and proper map properties on the connected plane. -/
theorem quadratic_surjective (c : ℂ) : Surjective (fun z : ℂ => z^2+c) := by
  intro y
  have he := localized_component_image (fun z : ℂ => z^2+c)
    (Set.univ : Set ℂ) (Set.univ : Set ℂ)
    (quadratic_open c) (quadratic_proper c).isClosedMap
    isOpen_univ isPreconnected_univ (by intro z hz; trivial)
    (by intro z hz; trivial) (0 : ℂ) (by simp)
  have hy : y ∈ (fun z : ℂ => z^2+c) '' connectedComponentIn Set.univ 0 :=
    he.symm ▸ mem_univ y
  obtain ⟨z, _, hz⟩ := hy
  exact ⟨z, hz⟩

/-- Choose one inverse point; no continuity of this choice is needed. -/
def fiberRoot (c y : ℂ) : ℂ := Classical.choose (quadratic_surjective c y)

theorem fiberRoot_spec (c y : ℂ) : (fiberRoot c y)^2+c = y :=
  Classical.choose_spec (quadratic_surjective c y)

theorem fiberRoot_injective (c : ℂ) : Injective (fiberRoot c) := by
  intro a b h
  calc
    a = (fiberRoot c a)^2+c := (fiberRoot_spec c a).symm
    _ = (fiberRoot c b)^2+c := by rw [h]
    _ = b := fiberRoot_spec c b

/-- The finite set of distinct actual global inverse points. -/
def globalFiber (c : ℂ) (n : ℕ) (y : ℂ) : Finset ℂ :=
  localFiber c n Set.univ y

theorem mem_globalFiber (c : ℂ) (n : ℕ) (y z : ℂ) :
    z ∈ globalFiber c n y ↔ ((fun w : ℂ => w^2+c)^[n]) z = y := by
  simp [globalFiber, mem_localFiber]

theorem globalFiber_zero (c y : ℂ) : globalFiber c 0 y = {y} := by
  ext z
  simp [mem_globalFiber]

/-- Exact inverse recursion: the negative branch must omit the unique
critical value, where the two square-root choices coincide. -/
theorem globalFiber_succ (c y : ℂ) (n : ℕ) :
    globalFiber c (n+1) y =
      (globalFiber c n y).image (fiberRoot c) ∪
      ((globalFiber c n y).erase c).image (fun w => -fiberRoot c w) := by
  classical
  ext z
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_erase, mem_globalFiber]
  constructor
  · intro hz
    let w := z^2+c
    have hw : ((fun u : ℂ => u^2+c)^[n]) w = y := by
      simpa only [Function.iterate_succ_apply, w] using hz
    have hprod : (z-fiberRoot c w)*(z+fiberRoot c w) = 0 := by
      have h := fiberRoot_spec c w
      dsimp [w] at h
      linear_combination -h
    by_cases hpos : z = fiberRoot c w
    · exact Or.inl ⟨w, hw, hpos.symm⟩
    · have hneg := (mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hpos)
      have hwc : w ≠ c := by
        intro h
        have hzsq : z*z = 0 := by
          dsimp [w] at h
          linear_combination h
        have hr := fiberRoot_spec c w
        rw [h] at hr
        have hrsq : fiberRoot c w * fiberRoot c w = 0 := by
          linear_combination hr
        have hz0 : z = 0 := (mul_eq_zero.mp hzsq).elim id id
        have hr0 : fiberRoot c w = 0 := (mul_eq_zero.mp hrsq).elim id id
        exact hpos (hz0.trans hr0.symm)
      exact Or.inr ⟨w, ⟨hwc, hw⟩, by linear_combination -hneg⟩
  · rintro (⟨w, hw, rfl⟩ | ⟨w, ⟨_, hw⟩, rfl⟩)
    · rw [Function.iterate_succ_apply]
      change ((fun u : ℂ => u^2+c)^[n]) ((fiberRoot c w)^2+c) = y
      rw [fiberRoot_spec]
      exact hw
    · rw [Function.iterate_succ_apply]
      change ((fun u : ℂ => u^2+c)^[n]) ((-fiberRoot c w)^2+c) = y
      have he : (-fiberRoot c w)^2+c = w := by
        calc
          (-fiberRoot c w)^2+c = (fiberRoot c w)^2+c := by ring
          _ = w := fiberRoot_spec c w
      rw [he]
      exact hw

/-- The two inverse branches are disjoint after omitting the duplicate
critical inverse point. This holds for every finite set of targets. -/
theorem inverse_branches_disjoint (c : ℂ) (A : Finset ℂ) :
    Disjoint (A.image (fiberRoot c))
      ((A.erase c).image (fun w => -fiberRoot c w)) := by
  classical
  apply Finset.disjoint_left.mpr
  intro z hz hz'
  obtain ⟨a, _, hza⟩ := Finset.mem_image.mp hz
  obtain ⟨b, hb, hzb⟩ := Finset.mem_image.mp hz'
  have hbne := (Finset.mem_erase.mp hb).1
  have he : fiberRoot c a = -fiberRoot c b := hza.trans hzb.symm
  have hab : a = b := by
    calc
      a = (fiberRoot c a)^2+c := (fiberRoot_spec c a).symm
      _ = (fiberRoot c b)^2+c := by rw [he]; ring
      _ = b := fiberRoot_spec c b
  subst a
  have hz0 : fiberRoot c b = 0 := by linear_combination (1/2 : ℂ)*he
  apply hbne
  simpa [hz0] using (fiberRoot_spec c b).symm

/-- Each inverse step doubles the distinct-point count except for
one lost point precisely when the target is the corresponding critical
orbit value. -/
theorem globalFiber_card_step (c y : ℂ) (n : ℕ) :
    (globalFiber c (n+1) y).card +
      (if ((fun w : ℂ => w^2+c)^[n]) c = y then 1 else 0) =
      2*(globalFiber c n y).card := by
  classical
  have hneg : Injective (fun w => -fiberRoot c w) := by
    intro a b h
    apply fiberRoot_injective c
    linear_combination -h
  rw [globalFiber_succ, Finset.card_union_of_disjoint (inverse_branches_disjoint c _),
    Finset.card_image_of_injective _ (fiberRoot_injective c),
    Finset.card_image_of_injective _ hneg]
  by_cases hc : c ∈ globalFiber c n y
  · have he := (mem_globalFiber c n y c).mp hc
    rw [if_pos he, Finset.card_erase_of_mem hc]
    have hp : 0 < (globalFiber c n y).card := Finset.card_pos.mpr ⟨c,hc⟩
    omega
  · have he : ((fun w : ℂ => w^2+c)^[n]) c ≠ y :=
      fun h => hc ((mem_globalFiber c n y c).mpr h)
    have herase : (globalFiber c n y).erase c = globalFiber c n y := by
      ext z
      simp only [Finset.mem_erase]
      constructor
      · exact fun h => h.2
      · intro hz
        exact ⟨fun h => hc (h ▸ hz), hz⟩
    rw [if_neg he, herase]
    omega

/-- Accumulated distinct-point deficit from the global degree.
Every earlier loss is doubled at the next inverse step. -/
def criticalFiberDefect (c y : ℂ) : ℕ → ℕ
  | 0 => 0
  | n+1 => 2*criticalFiberDefect c y n +
      (if ((fun w : ℂ => w^2+c)^[n]) c = y then 1 else 0)

/-- Exact all-depth ramification-aware cardinality, including parameters
with recurrent or periodic critical orbit. -/
theorem globalFiber_card_exact (c y : ℂ) (n : ℕ) :
    (globalFiber c n y).card + criticalFiberDefect c y n = 2^n := by
  induction n with
  | zero => simp [globalFiber_zero, criticalFiberDefect]
  | succ n ih =>
    have h := globalFiber_card_step c y n
    simp only [criticalFiberDefect, pow_succ]
    omega

/-- A fiber has maximal cardinality exactly when its target avoids
all critical values of the iterate. -/
theorem criticalFiberDefect_zero_iff (c y : ℂ) (n : ℕ) :
    criticalFiberDefect c y n = 0 ↔
      ∀ k < n, ((fun w : ℂ => w^2+c)^[k]) c ≠ y := by
  induction n with
  | zero => simp [criticalFiberDefect]
  | succ n ih =>
    constructor
    · intro hd k hk
      have hprev : criticalFiberDefect c y n = 0 := by
        simp only [criticalFiberDefect] at hd
        omega
      by_cases hkn : k = n
      · subst k
        intro he
        simp [criticalFiberDefect, he] at hd
      · exact ih.mp hprev k (by omega)
    · intro h
      have hprev := ih.mpr (fun k hk => h k (by omega))
      simp [criticalFiberDefect, hprev, h n (by omega)]

theorem globalFiber_full_card_iff (c y : ℂ) (n : ℕ) :
    (globalFiber c n y).card = 2^n ↔
      ∀ k < n, ((fun w : ℂ => w^2+c)^[k]) c ≠ y := by
  rw [← criticalFiberDefect_zero_iff]
  have h := globalFiber_card_exact c y n
  omega

/-- An exact critical-value-adjusted census certificate for any finite
list of actual inverse points. -/
theorem globalFiber_census (c y : ℂ) (n : ℕ) (A : Finset ℂ)
    (hA : ∀ z ∈ A, ((fun w : ℂ => w^2+c)^[n]) z = y)
    (hcard : 2^n ≤ A.card + criticalFiberDefect c y n) :
    A = globalFiber c n y := by
  apply Finset.eq_of_subset_of_card_le
  · intro z hz
    exact (mem_globalFiber c n y z).mpr (hA z hz)
  · have h := globalFiber_card_exact c y n
    omega

/-- Apply the corrected global bound to actual proper open pullback
components; unlike the uncorrected degree this also accepts a complete
critical fiber. It does not assert that the localization contains every
global inverse point. -/
theorem quadratic_critical_component_census {ι : Type*} [Fintype ι]
    (c : ℂ) (n : ℕ) (S V : Set ℂ)
    (hS : IsOpen S) (hVo : IsOpen V) (hVc : IsPreconnected V)
    (hm : MapsTo ((fun z : ℂ => z^2+c)^[n]) S V)
    (hp : IsProperMap (fun z : S =>
      (⟨((fun w : ℂ => w^2+c)^[n]) z, hm z.property⟩ : V)))
    (y : ℂ) (hy : y ∈ V) (a : ι → ℂ) (ha : ∀ i, a i ∈ S)
    (haf : ∀ i, ((fun w : ℂ => w^2+c)^[n]) (a i) = y)
    (hdist : Injective (fun i => connectedComponentIn S (a i)))
    (hcard : 2^n ≤ Fintype.card ι + criticalFiberDefect c y n)
    (x : ℂ) (hx : x ∈ S) :
    ∃! i, connectedComponentIn S x = connectedComponentIn S (a i) := by
  apply quadratic_localized_count_census c n S V hS hVo hVc hm hp
    y hy a ha haf hdist _ x hx
  have hsub : localFiber c n S y ⊆ globalFiber c n y := by
    intro z hz
    exact (mem_globalFiber c n y z).mpr ((mem_localFiber c n S y z).mp hz).2
  have hle := Finset.card_le_card hsub
  have he := globalFiber_card_exact c y n
  omega

end
end LoopsQuadraticCriticalFiberCensus

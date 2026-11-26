import PrimeEndSectorRank
import StationaryGeometricFibers

/-!
# Angular localization of physical impressions

Compact angular footprints give an exact decomposition of the nested
physical cluster set, even when the whole trace is not a neighborhood
basis at any angle. The exterior chart is an explicit input; its
construction is not part of these theorems.
-/

namespace PrimeEndImpressionDecomposition

open Set Metric PrimeEndSectorFilters

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

/-- The impression seen through all stages of the prescribed exterior traces
and all punctured neighborhoods of one angular coordinate. -/
def restrictedImpression (ψ : X × ℝ → Y) (A : ℕ → Set X)
    (H : ℕ → ℝ) (θ : X) : Set Y :=
  {z | ∀ n ε, 0 < ε → z ∈ closure (ψ '' (trace (A n) (H n) ∩ wedge θ ε))}

/-- The ordinary coordinate impression, without restriction to the puzzle. -/
def fullImpression (ψ : X × ℝ → Y) (θ : X) : Set Y :=
  {z | ∀ ε > 0, z ∈ closure (ψ '' wedge θ ε)}

/-- Exact angular localization of the physical cluster set. Compactness
is required on the angular footprints, not on the physical target.
No continuity or injectivity of the chart and no single-sector or
interiority hypothesis is needed. -/
theorem exterior_impression_decomposition (ψ : X × ℝ → Y)
    (A : ℕ → Set X) (H : ℕ → ℝ)
    (hc : ∀ n, IsCompact (A n)) (ha : Antitone A)
    (hp : ∀ n, 0 < H n) (hh : Antitone H)
    (hsmall : ∀ ε > 0, ∃ n, H n < ε) :
    (⋂ n, closure (ψ '' trace (A n) (H n))) =
      ⋃ θ ∈ (⋂ n, A n), restrictedImpression ψ A H θ := by
  apply Subset.antisymm
  · intro z hz
    let C : ℕ → Set X := fun n =>
      closure (Prod.fst '' {p : X × ℝ |
        p ∈ trace (A n) (H n) ∧ dist z (ψ p) < H n})
    have hsub (n : ℕ) : C n ⊆ A n := by
      apply closure_minimal _ (hc n).isClosed
      rintro x ⟨p, hp', rfl⟩
      exact hp'.1.1
    have hC (n : ℕ) : IsCompact (C n) :=
      (hc n).of_isClosed_subset isClosed_closure (hsub n)
    have hne (n : ℕ) : (C n).Nonempty := by
      obtain ⟨w, ⟨p, hp', rfl⟩, hw⟩ :=
        Metric.mem_closure_iff.mp (mem_iInter.mp hz n) (H n) (hp n)
      exact ⟨p.1, subset_closure ⟨p, ⟨hp', hw⟩, rfl⟩⟩
    have hm : Antitone C := by
      intro i j hij
      apply closure_mono
      rintro x ⟨p, hp', rfl⟩
      exact ⟨p, ⟨⟨ha hij hp'.1.1, hp'.1.2.1,
        hp'.1.2.2.trans (hh hij)⟩, hp'.2.trans_le (hh hij)⟩, rfl⟩
    have hd : Directed (· ⊇ ·) C := by
      intro i j
      exact ⟨max i j, hm (le_max_left i j), hm (le_max_right i j)⟩
    obtain ⟨θ, hθ⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
      C hd hne hC (fun n => (hC n).isClosed)
    have hθA : θ ∈ ⋂ n, A n :=
      mem_iInter.mpr (fun n => hsub n (mem_iInter.mp hθ n))
    apply mem_iUnion.mpr
    refine ⟨θ, mem_iUnion.mpr ⟨hθA, ?_⟩⟩
    intro n ε he
    apply Metric.mem_closure_iff.mpr
    intro δ hδ
    obtain ⟨j, hj⟩ := hsmall (min ε δ) (lt_min he hδ)
    let k := max n j
    have hk : H k < min ε δ := (hh (le_max_right n j)).trans_lt hj
    have hθk : θ ∈ C k := mem_iInter.mp hθ k
    obtain ⟨x, ⟨p, hp', rfl⟩, hx⟩ :=
      Metric.mem_closure_iff.mp hθk ε he
    refine ⟨ψ p, ⟨p, ⟨?_, ?_⟩, rfl⟩, ?_⟩
    · exact ⟨ha (le_max_left n j) hp'.1.1, hp'.1.2.1,
        hp'.1.2.2.trans (hh (le_max_left n j))⟩
    · exact ⟨Metric.mem_ball.mpr (by simpa only [dist_comm] using hx),
        hp'.1.2.1, hp'.1.2.2.trans_lt (hk.trans_le (min_le_left _ _))⟩
    · exact hp'.2.trans (hk.trans_le (min_le_right _ _))
  · intro z hz
    obtain ⟨θ, hθ⟩ := mem_iUnion.mp hz
    obtain ⟨_, hzθ⟩ := mem_iUnion.mp hθ
    apply mem_iInter.mpr
    intro n
    exact closure_mono (image_mono inter_subset_left) (hzθ n 1 (by norm_num))

/-- Each localized impression is contained in the ordinary coordinate
impression. Equality can fail if only one angular side is retained. -/
theorem restricted_impression_subset_full (ψ : X × ℝ → Y)
    (A : ℕ → Set X) (H : ℕ → ℝ) (θ : X) :
    restrictedImpression ψ A H θ ⊆ fullImpression ψ θ := by
  intro z hz ε he
  exact closure_mono (image_mono inter_subset_right) (hz 0 ε he)

/-- Interiority at every finite stage suffices to recover the full
ordinary impression at that angle, irrespective of other surviving angles. -/
theorem restricted_impression_eq_full_of_interior (ψ : X × ℝ → Y)
    (A : ℕ → Set X) (H : ℕ → ℝ) (θ : X)
    (hp : ∀ n, 0 < H n)
    (hint : ∀ n, ∃ δ > 0, ball θ δ ⊆ A n) :
    restrictedImpression ψ A H θ = fullImpression ψ θ := by
  apply Subset.antisymm (restricted_impression_subset_full ψ A H θ)
  intro z hz n ε he
  obtain ⟨δ, hd, hs⟩ := (reverse_stage_iff (A n) (H n) θ (hp n)).2 (hint n)
  have hsub : wedge θ (min ε δ) ⊆ trace (A n) (H n) ∩ wedge θ ε := by
    intro p h
    refine ⟨hs ?_, ?_⟩
    · exact ⟨Metric.mem_ball.mpr ((Metric.mem_ball.mp h.1).trans_le
        (min_le_right _ _)), h.2.1, h.2.2.trans_le (min_le_right _ _)⟩
    · exact ⟨Metric.mem_ball.mpr ((Metric.mem_ball.mp h.1).trans_le
        (min_le_left _ _)), h.2.1, h.2.2.trans_le (min_le_left _ _)⟩
  exact closure_mono (image_mono hsub) (hz (min ε δ) (lt_min he hd))

/-- Every surviving angle contributes a nonempty localized impression
when the initial physical trace has compact closure. No boundary
extension of the exterior chart is assumed. -/
theorem restricted_impression_nonempty (ψ : X × ℝ → Y)
    (A : ℕ → Set X) (H : ℕ → ℝ) (θ : X)
    (ha : Antitone A) (hp : ∀ n, 0 < H n) (hh : Antitone H)
    (hsmall : ∀ ε > 0, ∃ n, H n < ε)
    (hθ : θ ∈ ⋂ n, A n)
    (hc : IsCompact (closure (ψ '' trace (A 0) (H 0)))) :
    (restrictedImpression ψ A H θ).Nonempty := by
  let S : ℕ → Set (X × ℝ) := fun n => trace (A n) (H n) ∩ wedge θ (H n)
  let C : ℕ → Set Y := fun n => closure (ψ '' S n)
  have hm : Antitone S := by
    intro i j hij p h
    exact ⟨⟨ha hij h.1.1, h.1.2.1, h.1.2.2.trans (hh hij)⟩,
      ⟨Metric.mem_ball.mpr ((Metric.mem_ball.mp h.2.1).trans_le (hh hij)),
        h.2.2.1, h.2.2.2.trans_le (hh hij)⟩⟩
  have hC : Antitone C := fun _ _ hij => closure_mono (image_mono (hm hij))
  have hcompact (n : ℕ) : IsCompact (C n) := by
    apply hc.of_isClosed_subset isClosed_closure
    exact (hC (Nat.zero_le n)).trans (closure_mono (image_mono inter_subset_left))
  have hne (n : ℕ) : (C n).Nonempty := by
    have ht : 0 < H n / 2 := by linarith [hp n]
    have ht' : H n / 2 < H n := by linarith [hp n]
    have hmem : (θ, H n / 2) ∈ S n :=
      ⟨⟨mem_iInter.mp hθ n, ht, ht'.le⟩,
        ⟨by simpa only [Metric.mem_ball, dist_self] using hp n, ht, ht'⟩⟩
    exact ⟨ψ (θ, H n / 2), subset_closure ⟨_, hmem, rfl⟩⟩
  have hd : Directed (· ⊇ ·) C := by
    intro i j
    exact ⟨max i j, hC (le_max_left i j), hC (le_max_right i j)⟩
  obtain ⟨z, hz⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
    C hd hne hcompact (fun n => (hcompact n).isClosed)
  refine ⟨z, ?_⟩
  intro n ε he
  obtain ⟨j, hj⟩ := hsmall ε he
  let k := max n j
  have hk : H k < ε := (hh (le_max_right n j)).trans_lt hj
  have hsub : S k ⊆ trace (A n) (H n) ∩ wedge θ ε := by
    intro p h
    exact ⟨⟨ha (le_max_left n j) h.1.1, h.1.2.1,
      h.1.2.2.trans (hh (le_max_left n j))⟩,
      ⟨Metric.mem_ball.mpr ((Metric.mem_ball.mp h.2.1).trans hk),
        h.2.2.1, h.2.2.2.trans hk⟩⟩
  exact closure_mono (image_mono hsub) (mem_iInter.mp hz k)

/-- Finite angular rank and singleton ordinary impressions force a
preconnected physical cluster set to be subsingleton, even when its
exterior trace is not cofinal at any single angle. -/
theorem finite_landing_footprint_subsingleton (ψ : X × ℝ → Y)
    (A : ℕ → Set X) (H : ℕ → ℝ)
    (hc : ∀ n, IsCompact (A n)) (ha : Antitone A)
    (hp : ∀ n, 0 < H n) (hh : Antitone H)
    (hsmall : ∀ ε > 0, ∃ n, H n < ε)
    (hfinite : Finite (↥(⋂ n, A n)))
    (hpoint : ∀ θ ∈ ⋂ n, A n, ∃ z, fullImpression ψ θ = {z})
    (hconn : IsPreconnected (⋂ n, closure (ψ '' trace (A n) (H n)))) :
    (⋂ n, closure (ψ '' trace (A n) (H n))).Subsingleton := by
  classical
  letI : Finite (↥(⋂ n, A n)) := hfinite
  let f : ↥(⋂ n, A n) → Y :=
    fun θ => Classical.choose (hpoint θ.val θ.property)
  have hf (θ : ↥(⋂ n, A n)) : fullImpression ψ θ.val = {f θ} :=
    Classical.choose_spec (hpoint θ.val θ.property)
  have hsub : (⋂ n, closure (ψ '' trace (A n) (H n))) ⊆ Set.range f := by
    intro z hz
    rw [exterior_impression_decomposition ψ A H hc ha hp hh hsmall] at hz
    obtain ⟨θ, hθ⟩ := mem_iUnion.mp hz
    obtain ⟨hθA, hzθ⟩ := mem_iUnion.mp hθ
    let t : ↥(⋂ n, A n) := ⟨θ, hθA⟩
    have hmem : z ∈ fullImpression ψ t.val :=
      restricted_impression_subset_full ψ A H θ hzθ
    rw [hf t] at hmem
    exact ⟨t, (mem_singleton_iff.mp hmem).symm⟩
  exact LoopsStationaryGeometricFibers.preconnected_finite_subsingleton hconn
    ((Set.finite_range f).subset hsub)

/-- Physical cylinder corollary: if the closed cylinders really are the
closures of their exterior traces, the cluster set is exactly the end
fiber. Finite angular rank and point impressions yield a common point
for all surviving prime ends, not a unique prime end. -/
theorem physical_end_common_impression (ψ : X × ℝ → ℂ)
    (Q : ℕ → Set ℂ) (A : ℕ → Set X) (H : ℕ → ℝ)
    (hQ : ∀ n, Q n = closure (ψ '' trace (A n) (H n)))
    (hc : ∀ n, IsCompact (A n)) (ha : Antitone A)
    (hp : ∀ n, 0 < H n) (hh : Antitone H)
    (hsmall : ∀ ε > 0, ∃ n, H n < ε)
    (hcompact : IsCompact (Q 0))
    (hfinite : Finite (↥(⋂ n, A n)))
    (hpoint : ∀ θ ∈ ⋂ n, A n, ∃ z, fullImpression ψ θ = {z})
    (hconn : IsPreconnected (⋂ n, Q n))
    (hne : (⋂ n, Q n).Nonempty) :
    ∃ z, (⋂ n, Q n) = {z} ∧
      ∀ θ ∈ ⋂ n, A n, fullImpression ψ θ = {z} := by
  have heq : (⋂ n, Q n) = ⋂ n, closure (ψ '' trace (A n) (H n)) := by
    simp only [hQ]
  have hs := finite_landing_footprint_subsingleton ψ A H hc ha hp hh hsmall
    hfinite hpoint (heq ▸ hconn)
  obtain ⟨z, hz⟩ := hne
  have hz' : z ∈ ⋂ n, closure (ψ '' trace (A n) (H n)) := heq ▸ hz
  refine ⟨z, ?_, ?_⟩
  · apply Subset.antisymm
    · intro w hw
      exact mem_singleton_iff.mpr (hs (heq ▸ hw) hz')
    · intro w hw
      rw [mem_singleton_iff.mp hw]
      exact hz
  · intro θ hθ
    obtain ⟨w, hw⟩ := restricted_impression_nonempty ψ A H θ ha hp hh hsmall hθ
      (hQ 0 ▸ hcompact)
    have hw' : w ∈ ⋂ n, closure (ψ '' trace (A n) (H n)) := by
      rw [exterior_impression_decomposition ψ A H hc ha hp hh hsmall]
      exact mem_iUnion.mpr ⟨θ, mem_iUnion.mpr ⟨hθ, hw⟩⟩
    obtain ⟨v, hv⟩ := hpoint θ hθ
    have hwv : w = v := by
      have hmem := restricted_impression_subset_full ψ A H θ hw
      rw [hv] at hmem
      exact mem_singleton_iff.mp hmem
    rw [hv, ← hwv, hs hw' hz']


/-- Regular closed puzzle pieces are closures of their actual exterior
parts when the quadratic filled locus has empty interior. This discharges
the closure hypothesis of the abstract impression decomposition without
postulating density of exterior approaches as a separate axiom. -/
theorem quadratic_exterior_closure_of_regular_closed (c : ℂ) (Q : Set ℂ)
    (hQ : IsClosed Q) (hreg : Q ⊆ closure (interior Q))
    (hK : interior (LoopsDecorationCriticalCycle.filledLocus c) = ∅) :
    closure (Q \ LoopsDecorationCriticalCycle.filledLocus c) = Q := by
  apply Subset.antisymm (closure_minimal diff_subset hQ)
  apply hreg.trans
  apply closure_minimal _ isClosed_closure
  intro z hz
  apply Metric.mem_closure_iff.mpr
  intro ε he
  obtain ⟨δ, hd, hb⟩ := Metric.isOpen_iff.mp isOpen_interior z hz
  let r := min ε δ
  have hr : 0 < r := lt_min he hd
  have hex : ∃ w ∈ ball z r, w ∉ LoopsDecorationCriticalCycle.filledLocus c := by
    by_contra hn
    have hs : ball z r ⊆ LoopsDecorationCriticalCycle.filledLocus c := by
      intro w hw
      by_contra hwK
      exact hn ⟨w, hw, hwK⟩
    have hzK : z ∈ interior (LoopsDecorationCriticalCycle.filledLocus c) :=
      interior_maximal hs isOpen_ball (mem_ball_self hr)
    rw [hK] at hzK
    exact hzK
  obtain ⟨w, hw, hwK⟩ := hex
  have hdist : dist w z < r := Metric.mem_ball.mp hw
  have hwQ : w ∈ Q :=
    interior_subset (hb (Metric.mem_ball.mpr (hdist.trans_le (min_le_right _ _))))
  refine ⟨w, ⟨hwQ, hwK⟩, ?_⟩
  rw [dist_comm]
  exact hdist.trans_le (min_le_left _ _)

/-- The whole physical end is exactly the union of localized impressions
for regular closed quadratic puzzle pieces with the actual exterior
trace formula. The Julia empty-interior input and chart representation
remain explicit. -/
theorem quadratic_end_exact_decomposition (c : ℂ) (ψ : X × ℝ → ℂ)
    (Q : ℕ → Set ℂ) (A : ℕ → Set X) (H : ℕ → ℝ)
    (hclosed : ∀ n, IsClosed (Q n))
    (hreg : ∀ n, Q n ⊆ closure (interior (Q n)))
    (hK : interior (LoopsDecorationCriticalCycle.filledLocus c) = ∅)
    (htrace : ∀ n, ψ '' trace (A n) (H n) =
      Q n \ LoopsDecorationCriticalCycle.filledLocus c)
    (hc : ∀ n, IsCompact (A n)) (ha : Antitone A)
    (hp : ∀ n, 0 < H n) (hh : Antitone H)
    (hsmall : ∀ ε > 0, ∃ n, H n < ε) :
    (⋂ n, Q n) = ⋃ θ ∈ (⋂ n, A n), restrictedImpression ψ A H θ := by
  have hQ (n : ℕ) : Q n = closure (ψ '' trace (A n) (H n)) := by
    rw [htrace n, quadratic_exterior_closure_of_regular_closed c (Q n)
      (hclosed n) (hreg n) hK]
  simp only [hQ]
  exact exterior_impression_decomposition ψ A H hc ha hp hh hsmall

/-- A finite sector cover and point impressions at its surviving angles
suffice for pointness of the actual nested physical end, with every
surviving angle having that common full impression. Connectedness and
nonemptiness of the limit are derived from the closed puzzle pieces. -/
theorem quadratic_end_common_impression_of_sector_cover (c : ℂ)
    (ψ : X × ℝ → ℂ) (Q : ℕ → Set ℂ) (A : ℕ → Set X) (H : ℕ → ℝ)
    (hcompact : ∀ n, IsCompact (Q n))
    (hreg : ∀ n, Q n ⊆ closure (interior (Q n)))
    (hK : interior (LoopsDecorationCriticalCycle.filledLocus c) = ∅)
    (htrace : ∀ n, ψ '' trace (A n) (H n) =
      Q n \ LoopsDecorationCriticalCycle.filledLocus c)
    (hc : ∀ n, IsCompact (A n)) (ha : Antitone A)
    (hp : ∀ n, 0 < H n) (hh : Antitone H)
    (hsmall : ∀ ε > 0, ∃ n, H n < ε)
    (hconnected : ∀ n, IsPreconnected (Q n))
    (hnonempty : ∀ n, (Q n).Nonempty)
    (s : ℕ) (B : ℕ → Fin s → Set X)
    (hcover : ∀ n, A n ⊆ ⋃ j, B n j)
    (hsector : ∀ ε > 0, ∃ n, ∀ j x y,
      x ∈ B n j → y ∈ B n j → dist x y < ε)
    (hpoint : ∀ θ ∈ ⋂ n, A n, ∃ z, fullImpression ψ θ = {z}) :
    ∃ z, (⋂ n, Q n) = {z} ∧
      ∀ θ ∈ ⋂ n, A n, fullImpression ψ θ = {z} := by
  have hQ (n : ℕ) : Q n = closure (ψ '' trace (A n) (H n)) := by
    rw [htrace n, quadratic_exterior_closure_of_regular_closed c (Q n)
      (hcompact n).isClosed (hreg n) hK]
  have hm : Antitone Q := by
    intro i j hij
    rw [hQ i, hQ j]
    apply closure_mono
    apply image_mono
    intro p h
    exact ⟨ha hij h.1, h.2.1, h.2.2.trans (hh hij)⟩
  have hd : Directed (· ⊇ ·) Q := by
    intro i j
    exact ⟨max i j, hm (le_max_left i j), hm (le_max_right i j)⟩
  have hconn := LoopsLeastCarrier.directed_carrier_preconnected
    (Q 0) (hcompact 0) Q hcompact hconnected (fun n => hm (Nat.zero_le n)) hd
  have hne := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
    Q hd hnonempty hcompact (fun n => (hcompact n).isClosed)
  exact physical_end_common_impression ψ Q A H hQ hc ha hp hh hsmall
    (hcompact 0) (PrimeEndSectorRank.limiting_footprint_finite A s B hcover hsector)
    hpoint hconn hne

end PrimeEndImpressionDecomposition

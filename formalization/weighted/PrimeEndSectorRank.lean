import DecorationCriticalCycle

/-!
# Exact surviving-sector rank

The live labels of a finite angular-sector cover are those meeting the
limiting footprint. A fixed-depth census is detected by finite lookahead,
and sufficiently fine disjoint covers identify live labels bijectively with
limiting angles. No local connectivity or single-sector hypothesis is used.
-/

namespace PrimeEndSectorRank

open Set

variable {X : Type*} [MetricSpace X]

/-- Labels meeting the limiting angular footprint. -/
def live (A : ℕ → Set X) {s : ℕ} (B : ℕ → Fin s → Set X)
    (n : ℕ) : Set (Fin s) :=
  {j | (B n j ∩ (⋂ k, A k)).Nonempty}

/-- A compact sector survives precisely when it meets every finite
footprint. Nonemptiness of all finite contacts is sufficient even when
the contact points are different at each horizon. -/
theorem live_iff_all_contacts (A : ℕ → Set X) {s : ℕ}
    (B : ℕ → Fin s → Set X) (ha : Antitone A)
    (hc : ∀ k, IsClosed (A k)) (n : ℕ) (j : Fin s)
    (hb : IsCompact (B n j)) :
    j ∈ live A B n ↔ ∀ k, (B n j ∩ A k).Nonempty := by
  constructor
  · rintro ⟨x, hx, hxA⟩ k
    exact ⟨x, hx, mem_iInter.mp hxA k⟩
  · intro h
    let C : ℕ → Set X := fun k => B n j ∩ A k
    have hm : Antitone C := fun _ _ hkl => inter_subset_inter_left _ (ha hkl)
    have hd : Directed (· ⊇ ·) C := by
      intro k l
      exact ⟨max k l, hm (le_max_left k l), hm (le_max_right k l)⟩
    have hcompact (k : ℕ) : IsCompact (C k) := hb.inter_right (hc k)
    obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
      C hd h hcompact (fun k => (hcompact k).isClosed)
    exact ⟨x, (mem_iInter.mp hx 0).1,
      mem_iInter.mpr (fun k => (mem_iInter.mp hx k).2)⟩

/-- At each fixed depth there is a common finite lookahead after which
the contact labels are exactly the surviving labels, permanently. This
is an existence theorem; it gives no uniform bound on the lookahead. -/
theorem live_census_stabilizes (A : ℕ → Set X) {s : ℕ}
    (B : ℕ → Fin s → Set X) (ha : Antitone A)
    (hc : ∀ k, IsClosed (A k)) (n : ℕ)
    (hb : ∀ j, IsCompact (B n j)) :
    ∃ N ≥ n, ∀ k ≥ N, live A B n =
      {j | (B n j ∩ A k).Nonempty} := by
  classical
  have hex : ∀ j : Fin s, ∃ k, (B n j ∩ A k).Nonempty → j ∈ live A B n := by
    intro j
    by_cases hj : j ∈ live A B n
    · exact ⟨0, fun _ => hj⟩
    · have hn : ¬ ∀ k, (B n j ∩ A k).Nonempty :=
        fun h => hj ((live_iff_all_contacts A B ha hc n j (hb j)).2 h)
      push_neg at hn
      obtain ⟨k, hk⟩ := hn
      exact ⟨k, fun h => False.elim (hk h)⟩
  choose k hk using hex
  let N := max n (Finset.univ.sup k)
  refine ⟨N, le_max_left _ _, ?_⟩
  intro m hm
  ext j
  constructor
  · intro hj
    exact (live_iff_all_contacts A B ha hc n j (hb j)).1 hj m
  · intro hj
    have hle : k j ≤ Finset.univ.sup k := Finset.le_sup (Finset.mem_univ j)
    have hkm : k j ≤ m := hle.trans ((le_max_right n _).trans hm)
    apply hk j
    obtain ⟨x, hx, hxm⟩ := hj
    exact ⟨x, hx, ha hkm hxm⟩

/-- The previously checked sector-capacity bound implies actual finiteness
of the entire limiting footprint, not merely a bound on a chosen list. -/
theorem limiting_footprint_finite (A : ℕ → Set X) (s : ℕ)
    (B : ℕ → Fin s → Set X) (hcover : ∀ n, A n ⊆ ⋃ j, B n j)
    (hsmall : ∀ ε > 0, ∃ n, ∀ j x y,
      x ∈ B n j → y ∈ B n j → dist x y < ε) :
    Finite (↥(⋂ n, A n)) := by
  classical
  by_contra h
  letI : Infinite (↥(⋂ n, A n)) := not_finite_iff_infinite.mp h
  let e := Infinite.natEmbedding (↥(⋂ n, A n))
  let f : Fin (s+1) → X := fun i => (e i.val).val
  apply PrimeEndSectorFilters.finite_sector_capacity A s B hcover hsmall
    f (fun i => (e i.val).property)
  intro i j hij
  apply Fin.ext
  apply e.injective
  exact Subtype.ext hij

/-- Any finite set of limiting angles is eventually separated by the
shrinking sectors. The finite separation scale is taken over all pairs
of distinct limiting angles, not over sampled representatives. -/
theorem sectors_eventually_separate (A : ℕ → Set X) (s : ℕ)
    (B : ℕ → Fin s → Set X) (hcover : ∀ n, A n ⊆ ⋃ j, B n j)
    (hsmall : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ j x y,
      x ∈ B n j → y ∈ B n j → dist x y < ε) :
    ∃ N, ∀ n ≥ N, ∀ j, (B n j ∩ (⋂ k, A k)).Subsingleton := by
  classical
  let L : Set X := ⋂ k, A k
  letI : Finite (↥L) := limiting_footprint_finite A s B hcover
    (fun ε hε => by
      obtain ⟨N, hN⟩ := hsmall ε hε
      exact ⟨N, hN N le_rfl⟩)
  letI : Fintype (↥L) := Fintype.ofFinite _
  let P := (Finset.univ : Finset (↥L × ↥L)).filter (fun p => p.1 ≠ p.2)
  by_cases hP : P.Nonempty
  · obtain ⟨p, hp, hmin⟩ := P.exists_min_image
      (fun p => dist p.1.val p.2.val) hP
    have hne : p.1 ≠ p.2 := (Finset.mem_filter.mp hp).2
    have hpos : 0 < dist p.1.val p.2.val := dist_pos.mpr
      (fun he => hne (Subtype.ext he))
    obtain ⟨N, hN⟩ := hsmall _ hpos
    refine ⟨N, ?_⟩
    intro n hn j x hx y hy
    by_contra hxy
    let u : ↥L := ⟨x, hx.2⟩
    let v : ↥L := ⟨y, hy.2⟩
    have huv : u ≠ v := fun he => hxy (congrArg Subtype.val he)
    have huvP : (u,v) ∈ P := Finset.mem_filter.mpr ⟨Finset.mem_univ _, huv⟩
    have hle : dist p.1.val p.2.val ≤ dist x y := hmin (u,v) huvP
    exact (not_lt_of_ge hle) (hN n hn j x y hx.1 hy.1)
  · refine ⟨0, ?_⟩
    intro n hn j x hx y hy
    by_contra hxy
    let u : ↥L := ⟨x, hx.2⟩
    let v : ↥L := ⟨y, hy.2⟩
    apply hP
    exact ⟨(u,v), Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, fun he => hxy (congrArg Subtype.val he)⟩⟩

/-- Disjoint sectors meeting the limit, with no two limiting angles in
one sector, give an exact equivalence rather than a cardinal inequality. -/
theorem live_sector_equiv (A : ℕ → Set X) {s : ℕ}
    (B : ℕ → Fin s → Set X) (n : ℕ)
    (hcover : A n ⊆ ⋃ j, B n j)
    (hdisj : ∀ i j, i ≠ j → Disjoint (B n i) (B n j))
    (hsep : ∀ j, (B n j ∩ (⋂ k, A k)).Subsingleton) :
    Nonempty (↥(live A B n) ≃ ↥(⋂ k, A k)) := by
  classical
  let pick : ↥(live A B n) → ↥(⋂ k, A k) :=
    fun j => ⟨j.property.choose, j.property.choose_spec.2⟩
  have hpick (j : ↥(live A B n)) : (pick j).val ∈ B n j.val :=
    j.property.choose_spec.1
  refine ⟨Equiv.ofBijective pick ⟨?_, ?_⟩⟩
  · intro i j hij
    apply Subtype.ext
    by_contra hne
    have he : (pick i).val = (pick j).val := congrArg Subtype.val hij
    have hj : (pick i).val ∈ B n j.val := by rw [he]; exact hpick j
    exact Set.disjoint_left.mp (hdisj i.val j.val hne) (hpick i) hj
  · intro x
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hcover (mem_iInter.mp x.property n))
    let i : ↥(live A B n) := ⟨j, ⟨x.val, hj, x.property⟩⟩
    refine ⟨i, Subtype.ext ?_⟩
    exact hsep j ⟨hpick i, (pick i).property⟩ ⟨hj, x.property⟩

/-- The exact number of angles can be recovered from finite contact
censuses: after a separating depth, a sufficiently long finite lookahead
gives a set of sector labels equivalent to the whole limiting footprint.
The two horizons are existential, not a claimed computable stopping test. -/
theorem exact_finite_lookahead_rank (A : ℕ → Set X) (s : ℕ)
    (B : ℕ → Fin s → Set X) (ha : Antitone A)
    (hc : ∀ k, IsClosed (A k)) (hb : ∀ n j, IsCompact (B n j))
    (hcover : ∀ n, A n ⊆ ⋃ j, B n j)
    (hdisj : ∀ n i j, i ≠ j → Disjoint (B n i) (B n j))
    (hsmall : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ j x y,
      x ∈ B n j → y ∈ B n j → dist x y < ε) :
    ∃ N, ∀ n ≥ N, ∃ M ≥ n, ∀ k ≥ M,
      Nonempty (↥({j : Fin s | (B n j ∩ A k).Nonempty}) ≃ ↥(⋂ l, A l)) := by
  obtain ⟨N, hN⟩ := sectors_eventually_separate A s B hcover hsmall
  refine ⟨N, ?_⟩
  intro n hn
  obtain ⟨M, hMn, hM⟩ := live_census_stabilizes A B ha hc n (hb n)
  refine ⟨M, hMn, ?_⟩
  intro k hk
  rw [← hM k hk]
  exact live_sector_equiv A B n (hcover n) (hdisj n) (hN n hn)

/-- Two disjoint sectors with contacts at all future horizons certify
failure of the ordinary whole-trace prime-end cofinality assertion.
This criterion does not assume that a landing point is nonunique. -/
theorem two_surviving_sectors_obstruct (A : ℕ → Set X) {s : ℕ}
    (B : ℕ → Fin s → Set X) (H : ℕ → ℝ) (ha : Antitone A)
    (hc : ∀ k, IsClosed (A k)) (hp : ∀ k, 0 < H k)
    (n : ℕ) (i j : Fin s) (hi : IsCompact (B n i)) (hj : IsCompact (B n j))
    (hd : Disjoint (B n i) (B n j))
    (hci : ∀ k, (B n i ∩ A k).Nonempty)
    (hcj : ∀ k, (B n j ∩ A k).Nonempty) :
    ∀ θ, ¬ PrimeEndSectorFilters.Cofinal A H θ := by
  obtain ⟨x, hxi, hx⟩ := (live_iff_all_contacts A B ha hc n i hi).2 hci
  obtain ⟨y, hyj, hy⟩ := (live_iff_all_contacts A B ha hc n j hj).2 hcj
  have hxy : x ≠ y := by
    intro he
    exact Set.disjoint_left.mp hd hxi (he.symm ▸ hyj)
  exact PrimeEndSectorFilters.two_angles_obstruct A H hp hxy hx hy

end PrimeEndSectorRank

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
    have hm : Antitone C := fun _ _ hkl x hx => ⟨hx.1, ha hkl hx.2⟩
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
      obtain ⟨k, hk⟩ := not_forall.mp hn
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
    fun j => ⟨Classical.choose (show (B n j.val ∩ (⋂ k, A k)).Nonempty from j.property),
      (Classical.choose_spec (show (B n j.val ∩ (⋂ k, A k)).Nonempty from j.property)).2⟩
  have hpick (j : ↥(live A B n)) : (pick j).val ∈ B n j.val :=
    (Classical.choose_spec (show (B n j.val ∩ (⋂ k, A k)).Nonempty from j.property)).1
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

/-- Ancestor map from labels at depth n+k to labels at depth n.
Each transition goes backwards, from a child sector to its unique
containing parent sector; the composition order is essential. -/
def ancestor {s : ℕ} (t : ℕ → Fin s → Fin s) (n : ℕ) :
    ℕ → Fin s → Fin s
  | 0 => id
  | k+1 => fun j => ancestor t n k (t (n+k) j)

/-- Containment along every finite path of the actual sector incidence. -/
theorem ancestor_sector_subset {s : ℕ} (B : ℕ → Fin s → Set X)
    (t : ℕ → Fin s → Fin s)
    (hstep : ∀ n j, B (n+1) j ⊆ B n (t n j))
    (n k : ℕ) (j : Fin s) :
    B (n+k) j ⊆ B n (ancestor t n k j) := by
  induction k generalizing j with
  | zero => simp [ancestor]
  | succ k ih =>
    rw [Nat.add_succ]
    exact (hstep (n+k) j).trans (ih (t (n+k) j))

/-- Exact geometric contact equals reachability in the finite ancestor
map. All child sectors must be nonempty and the footprints must be
their full union. No particular algebraic form of the angular lifts is
required. -/
theorem contact_iff_ancestor_range (A : ℕ → Set X) {s : ℕ}
    (B : ℕ → Fin s → Set X) (t : ℕ → Fin s → Fin s)
    (hstep : ∀ n j, B (n+1) j ⊆ B n (t n j))
    (hcover : ∀ n, A n = ⋃ j, B n j)
    (hne : ∀ n j, (B n j).Nonempty)
    (hdisj : ∀ n i j, i ≠ j → Disjoint (B n i) (B n j))
    (n k : ℕ) (j : Fin s) :
    (B n j ∩ A (n+k)).Nonempty ↔ j ∈ Set.range (ancestor t n k) := by
  constructor
  · rintro ⟨x, hx, hxA⟩
    rw [hcover] at hxA
    obtain ⟨i, hi⟩ := mem_iUnion.mp hxA
    have hxi := ancestor_sector_subset B t hstep n k i hi
    refine ⟨i, ?_⟩
    by_contra h
    exact Set.disjoint_left.mp (hdisj n (ancestor t n k i) j h) hxi hx
  · rintro ⟨i, rfl⟩
    obtain ⟨x, hx⟩ := hne (n+k) i
    refine ⟨x, ancestor_sector_subset B t hstep n k i hx, ?_⟩
    rw [hcover]
    exact mem_iUnion.mpr ⟨i, hx⟩

/-- The survivor set at depth n is the intersection of the descendant
ancestor ranges, not just the image of the very first transition. -/
theorem live_eq_ancestor_survivors (A : ℕ → Set X) {s : ℕ}
    (B : ℕ → Fin s → Set X) (t : ℕ → Fin s → Fin s)
    (ha : Antitone A) (hc : ∀ n, IsClosed (A n))
    (hb : ∀ n j, IsCompact (B n j))
    (hstep : ∀ n j, B (n+1) j ⊆ B n (t n j))
    (hcover : ∀ n, A n = ⋃ j, B n j)
    (hne : ∀ n j, (B n j).Nonempty)
    (hdisj : ∀ n i j, i ≠ j → Disjoint (B n i) (B n j))
    (n : ℕ) :
    live A B n = ⋂ k, Set.range (ancestor t n k) := by
  ext j
  constructor
  · intro hj
    apply mem_iInter.mpr
    intro k
    exact (contact_iff_ancestor_range A B t hstep hcover hne hdisj n k j).1
      ((live_iff_all_contacts A B ha hc n j (hb n j)).1 hj (n+k))
  · intro hj
    apply (live_iff_all_contacts A B ha hc n j (hb n j)).2
    intro m
    obtain ⟨x, hx, hxA⟩ :=
      (contact_iff_ancestor_range A B t hstep hcover hne hdisj n m j).2
        (mem_iInter.mp hj m)
    have hle : m ≤ n+m := by omega
    exact ⟨x, hx, ha hle hxA⟩

/-- Exact finite-state rank formula for a coherently labelled shrinking
sector system. After the separation depth, sufficiently long finite
backward ancestor maps have range in bijection with all limiting angles.
The existential lookahead may depend on the chosen depth and address. -/
theorem exact_ancestor_rank (A : ℕ → Set X) (s : ℕ)
    (B : ℕ → Fin s → Set X) (t : ℕ → Fin s → Fin s)
    (ha : Antitone A) (hc : ∀ n, IsClosed (A n))
    (hb : ∀ n j, IsCompact (B n j))
    (hstep : ∀ n j, B (n+1) j ⊆ B n (t n j))
    (hcover : ∀ n, A n = ⋃ j, B n j)
    (hne : ∀ n j, (B n j).Nonempty)
    (hdisj : ∀ n i j, i ≠ j → Disjoint (B n i) (B n j))
    (hsmall : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ j x y,
      x ∈ B n j → y ∈ B n j → dist x y < ε) :
    ∃ N, ∀ n ≥ N, ∃ M, ∀ k ≥ M,
      Nonempty (↥(Set.range (ancestor t n k)) ≃ ↥(⋂ l, A l)) := by
  have hcov : ∀ n, A n ⊆ ⋃ j, B n j := fun n => (hcover n).subset
  obtain ⟨N, hN⟩ := exact_finite_lookahead_rank A s B ha hc hb hcov hdisj hsmall
  refine ⟨N, ?_⟩
  intro n hn
  obtain ⟨M, _, hM⟩ := hN n hn
  refine ⟨M, ?_⟩
  intro k hk
  have heq : Set.range (ancestor t n k) = {j | (B n j ∩ A (n+k)).Nonempty} := by
    ext j
    exact (contact_iff_ancestor_range A B t hstep hcover hne hdisj n k j).symm
  rw [heq]
  exact hM (n+k) (by omega)

end PrimeEndSectorRank

import PlanarFullification
import Mathlib.Topology.Connected.LocallyPathConnected

/-!
# Continuity from above of the genuine planar filled hull

A compact path in an increasing union of open subsets is already contained
in one stage. This transfers to components in the plane, and then to the
unique unbounded complementary component of a decreasing compact carrier.
No regularity, connectivity or disjoint-packet assumption on the seeds
is needed.
-/

namespace LoopsFormal.ProtectedCarriers

open Set Bornology Metric

/-- Connected-component membership in an increasing union of open plane
domains has a finite-stage witness. The proof uses a compact actual path,
not a finite incidence graph. -/
theorem connectedComponentIn_iUnion_monotone_open (U : ℕ → Set ℂ)
    (ho : ∀ n, IsOpen (U n)) (hm : Monotone U) (z : ℂ) :
    connectedComponentIn (⋃ n, U n) z =
      ⋃ n, connectedComponentIn (U n) z := by
  apply Subset.antisymm
  · intro w hw
    have hz : z ∈ ⋃ n, U n :=
      connectedComponentIn_nonempty_iff.mp ⟨w, hw⟩
    have hCopen : IsOpen (connectedComponentIn (⋃ n, U n) z) :=
      (isOpen_iUnion ho).connectedComponentIn
    have hCconn : IsConnected (connectedComponentIn (⋃ n, U n) z) :=
      isConnected_connectedComponentIn_iff.mpr hz
    obtain ⟨p, hp⟩ := (hCopen.isConnected_iff_isPathConnected.mp hCconn).joinedIn
      z (mem_connectedComponentIn hz) w hw
    have hs : range (⇑p) ⊆ ⋃ n, U n :=
      range_subset_iff.mpr (fun t => connectedComponentIn_subset _ _ (hp t))
    have hd : Directed (· ⊆ ·) U := by
      intro i j
      exact ⟨max i j, hm (le_max_left i j), hm (le_max_right i j)⟩
    obtain ⟨n, hn⟩ := (isCompact_range p.continuous).elim_directed_cover U ho hs hd
    have hpre : IsPreconnected (range (⇑p)) :=
      isPreconnected_range p.continuous
    exact mem_iUnion.mpr ⟨n,
      hpre.subset_connectedComponentIn p.source_mem_range hn p.target_mem_range⟩
  · intro w hw
    obtain ⟨n, hn⟩ := mem_iUnion.mp hw
    exact connectedComponentIn_mono z (subset_iUnion U n) hn

/-- Fullification commutes with arbitrary decreasing sequences of compact
plane sets, including disconnected and empty seeds. -/
theorem planarFill_iInter_antitone_compact (S : ℕ → Set ℂ)
    (hc : ∀ n, IsCompact (S n)) (hm : Antitone S) :
    planarFill (⋂ n, S n) = ⋂ n, planarFill (S n) := by
  let K : Set ℂ := ⋂ n, S n
  have hK0 : K ⊆ S 0 := iInter_subset S 0
  have hK : IsCompact K :=
    (hc 0).of_isClosed_subset (isClosed_iInter fun n => (hc n).isClosed) hK0
  obtain ⟨a, _, haun, _, _⟩ := planarFill_exterior (hc 0).isBounded
  have ha0 : a ∉ planarFill (S 0) := haun
  have haK : a ∉ planarFill K := fun h => ha0 (planarFill_mono hK0 h)
  obtain ⟨d, _, _, hde, hsame⟩ := planarFill_exterior hK.isBounded
  have heq : (planarFill K)ᶜ = connectedComponentIn Kᶜ a :=
    hde.trans (hsame a haK).symm
  have hu : Kᶜ = ⋃ n, (S n)ᶜ := by
    dsimp [K]
    rw [compl_iInter]
  have hmono : Monotone (fun n => (S n)ᶜ) :=
    fun _ _ h => compl_subset_compl.mpr (hm h)
  change planarFill K = _
  apply Subset.antisymm
  · intro z hz
    exact mem_iInter.mpr fun n => planarFill_mono (iInter_subset S n) hz
  · intro z hz
    by_contra hzK
    have hzC : z ∈ connectedComponentIn Kᶜ a := by
      rw [← heq]
      exact hzK
    rw [hu, connectedComponentIn_iUnion_monotone_open _
      (fun n => (hc n).isClosed.isOpen_compl) hmono] at hzC
    obtain ⟨n, hn⟩ := mem_iUnion.mp hzC
    have haN : a ∉ planarFill (S n) :=
      fun h => ha0 (planarFill_mono (hm (Nat.zero_le n)) h)
    have hzN : z ∈ planarFill (S n) := mem_iInter.mp hz n
    change IsBounded (connectedComponentIn (S n)ᶜ z) at hzN
    change ¬ IsBounded (connectedComponentIn (S n)ᶜ a) at haN
    exact haN ((connectedComponentIn_eq hn).symm ▸ hzN :
      IsBounded (connectedComponentIn (S n)ᶜ a))

/-- Nested full compact carriers cannot acquire a bounded complementary
component at the limit. -/
theorem planarFill_iInter_fixed (S : ℕ → Set ℂ)
    (hc : ∀ n, IsCompact (S n)) (hm : Antitone S)
    (hf : ∀ n, planarFill (S n) = S n) :
    planarFill (⋂ n, S n) = ⋂ n, S n := by
  rw [planarFill_iInter_antitone_compact S hc hm]
  simp only [hf]

/-- No filled point persists outside any prescribed open neighborhood of
the filled limit. This is a uniform eventual inclusion, not merely a
pointwise statement. -/
theorem planarFill_eventually_subset_open (S : ℕ → Set ℂ)
    (hc : ∀ n, IsCompact (S n)) (hm : Antitone S)
    (V : Set ℂ) (hV : IsOpen V) (hsub : planarFill (⋂ n, S n) ⊆ V) :
    ∃ N : ℕ, ∀ n ≥ N, planarFill (S n) ⊆ V := by
  have hcompact : IsCompact (planarFill (S 0) ∩ Vᶜ) :=
    (planarFill_compact (hc 0)).inter_right hV.isClosed_compl
  have hclosed : ∀ n, IsClosed (planarFill (S n)) :=
    fun n => (planarFill_compact (hc n)).isClosed
  have hdis : (planarFill (S 0) ∩ Vᶜ) ∩ (⋂ n, planarFill (S n)) = ∅ := by
    rw [← planarFill_iInter_antitone_compact S hc hm]
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro z hz
    exact hz.1.2 (hsub hz.2)
  have hd : Directed (· ⊇ ·) (fun n => planarFill (S n)) := by
    intro i j
    exact ⟨max i j, planarFill_mono (hm (le_max_left i j)),
      planarFill_mono (hm (le_max_right i j))⟩
  obtain ⟨N, hN⟩ := hcompact.elim_directed_family_closed
    (fun n => planarFill (S n)) hclosed hdis hd
  refine ⟨N, ?_⟩
  intro n hn z hz
  by_contra hzV
  have hzbad : z ∈ (planarFill (S 0) ∩ Vᶜ) ∩ planarFill (S N) :=
    ⟨⟨planarFill_mono (hm (Nat.zero_le n)) hz, hzV⟩,
      planarFill_mono (hm hn) hz⟩
  rw [hN] at hzbad
  exact hzbad

end LoopsFormal.ProtectedCarriers

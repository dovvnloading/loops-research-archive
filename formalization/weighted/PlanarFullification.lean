import ProtectedCarrierLogic

/-!
# The filled hull of an actual subset of the complex plane

Paper 3, equation A-fill and Lemma E-fill-absorption. The extension to
arbitrary sets fills exactly their bounded complementary components. The
identification with the complement of a *single* exterior component below
requires boundedness. Compactness of the hull additionally uses closedness.
-/

namespace LoopsFormal.ProtectedCarriers

open Set Bornology Metric

/-- On a point of S the complementary component is empty and hence bounded. -/
def planarFill (S : Set ℂ) : Set ℂ :=
  {z | IsBounded (connectedComponentIn Sᶜ z)}

theorem planarFill_extensive (S : Set ℂ) : S ⊆ planarFill S := by
  intro z hz
  change IsBounded (connectedComponentIn Sᶜ z)
  rw [connectedComponentIn_eq_empty (show z ∉ Sᶜ from fun h => h hz)]
  exact isBounded_empty

/-- Outside the seed this is precisely the membership test in Paper 3. -/
theorem mem_planarFill_iff (S : Set ℂ) (z : ℂ) :
    z ∈ planarFill S ↔ z ∈ S ∨
      (z ∈ Sᶜ ∧ IsBounded (connectedComponentIn Sᶜ z)) := by
  by_cases h : z ∈ S
  · simp [h, planarFill_extensive S h]
  · simp [h, planarFill]

theorem planarFill_mono {S T : Set ℂ} (h : S ⊆ T) : planarFill S ⊆ planarFill T := by
  intro z hz
  change IsBounded (connectedComponentIn Sᶜ z) at hz
  exact hz.subset (connectedComponentIn_mono z (compl_subset_compl.mpr h))

theorem planarFill_idempotent (S : Set ℂ) : planarFill (planarFill S) = planarFill S := by
  apply Subset.antisymm _ (planarFill_extensive _)
  intro z hz
  change IsBounded (connectedComponentIn (planarFill S)ᶜ z) at hz
  by_contra h
  have outside : z ∈ Sᶜ := fun hS => h (planarFill_extensive S hS)
  have survives : connectedComponentIn Sᶜ z ⊆ (planarFill S)ᶜ := by
    intro w hw hfilled
    exact h ((connectedComponentIn_eq hw).symm ▸ hfilled :
      IsBounded (connectedComponentIn Sᶜ z))
  exact h (hz.subset (isPreconnected_connectedComponentIn.subset_connectedComponentIn
    (mem_connectedComponentIn outside) survives))

def planarFullifier : Fullifier ℂ where
  hull := planarFill
  extensive := planarFill_extensive
  monotone := fun _ _ h => planarFill_mono h
  idempotent := planarFill_idempotent

/-- Outside a sufficiently large closed disk there is only one component
to which an unbounded connected subset of the complement can escape. -/
private theorem exterior_preconnected {r : ℝ} (hr : 0 < r) :
    IsPreconnected (closedBall (0 : ℂ) r)ᶜ := by
  have image_eq : Complex.exp '' {w : ℂ | Real.log r < w.re} = (closedBall 0 r)ᶜ := by
    ext z
    simp only [mem_compl_iff, mem_closedBall, dist_zero_right, not_le]
    constructor
    · rintro ⟨w, hw, rfl⟩
      rw [Complex.norm_exp, ← Real.exp_log hr]
      exact Real.exp_lt_exp.mpr hw
    · intro hz
      have hne : z ≠ 0 := norm_pos_iff.mp (hr.trans hz)
      exact ⟨Complex.log z, by simpa [Complex.log_re] using Real.log_lt_log hr hz,
        Complex.exp_log hne⟩
  rw [← image_eq]
  exact (convex_halfSpace_re_gt _).isPreconnected.image _ Complex.continuous_exp.continuousOn

/-- The hull complement is the unique unbounded component of the complement
of a bounded seed, and contains the exterior of a disk enclosing the seed. -/
theorem planarFill_exterior {S : Set ℂ} (hs : IsBounded S) :
    ∃ a : ℂ, a ∈ Sᶜ ∧ ¬ IsBounded (connectedComponentIn Sᶜ a) ∧
      (planarFill S)ᶜ = connectedComponentIn Sᶜ a ∧
      ∀ b : ℂ, ¬ IsBounded (connectedComponentIn Sᶜ b) →
        connectedComponentIn Sᶜ b = connectedComponentIn Sᶜ a := by
  obtain ⟨r, hr, hS⟩ := hs.subset_closedBall_lt 0 0
  let D := closedBall (0 : ℂ) r
  have hD : IsBounded D := isBounded_closedBall
  have hfar : ¬ IsBounded Dᶜ := by
    intro h
    exact NormedSpace.unbounded_univ ℝ ℂ (by simpa using hD.union h)
  obtain ⟨a, ha⟩ : Dᶜ.Nonempty := nonempty_iff_ne_empty.mpr (fun he => hfar (he ▸ isBounded_empty))
  have outer : Dᶜ ⊆ connectedComponentIn Sᶜ a :=
    (exterior_preconnected hr).subset_connectedComponentIn ha (compl_subset_compl.mpr hS)
  have unbounded : ¬ IsBounded (connectedComponentIn Sᶜ a) := fun h => hfar (h.subset outer)
  have same (b : ℂ) (hb : ¬ IsBounded (connectedComponentIn Sᶜ b)) :
      connectedComponentIn Sᶜ b = connectedComponentIn Sᶜ a := by
    obtain ⟨w, hw, hnot⟩ := Set.not_subset.mp (fun hsub => hb (hD.subset hsub) :
      ¬ connectedComponentIn Sᶜ b ⊆ D)
    exact (connectedComponentIn_eq hw).trans (connectedComponentIn_eq (outer hnot)).symm
  refine ⟨a, connectedComponentIn_subset _ _ (outer ha), unbounded, ?_, same⟩
  ext b
  constructor
  · intro hb
    have hbc : b ∈ Sᶜ := fun h => hb (planarFill_extensive S h)
    rw [← same b hb]
    exact mem_connectedComponentIn hbc
  · intro hb hf
    exact unbounded ((connectedComponentIn_eq hb).symm ▸ hf :
      IsBounded (connectedComponentIn Sᶜ a))

theorem planarFill_compact {S : Set ℂ} (hs : IsCompact S) : IsCompact (planarFill S) := by
  obtain ⟨a, _, hu, he, _⟩ := planarFill_exterior hs.isBounded
  have hopen : IsOpen (planarFill S)ᶜ := he ▸ hs.isClosed.isOpen_compl.connectedComponentIn
  obtain ⟨r, hr, hS⟩ := hs.isBounded.subset_closedBall_lt 0 0
  have hbound : planarFill S ⊆ closedBall 0 r := by
    intro z hz
    change IsBounded (connectedComponentIn Sᶜ z) at hz
    by_contra hfar
    have hsub := (exterior_preconnected hr).subset_connectedComponentIn
      (show z ∈ (closedBall 0 r)ᶜ from hfar) (compl_subset_compl.mpr hS)
    have both := (isBounded_closedBall (x := (0 : ℂ)) (r := r)).union (hz.subset hsub)
    exact NormedSpace.unbounded_univ ℝ ℂ (by simpa using both)
  exact (isCompact_closedBall (0 : ℂ) r).of_isClosed_subset (isOpen_compl_iff.mp hopen) hbound

theorem planar_fill_absorption (S T : Set ℂ) :
    planarFill (planarFill S ∪ T) = planarFill (S ∪ T) :=
  fill_absorption planarFullifier S T

theorem planar_packet_completion (pieces : List (Set ℂ)) :
    complete planarFullifier pieces = planarFill (packetUnion pieces) :=
  complete_eq_hull_union planarFullifier pieces

#print axioms planarFill_exterior
#print axioms planarFill_compact
#print axioms planar_fill_absorption
#print axioms planar_packet_completion

end LoopsFormal.ProtectedCarriers

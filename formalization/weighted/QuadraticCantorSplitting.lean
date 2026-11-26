import QuadraticCantorGeometry
import Mathlib.Topology.Piecewise
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic.FinCases

/-!
# A generating physical two-sheet partition

The two disks from the quantitative quadratic geometry define the labels.
The actual polynomial, together with its disk label, gives a homeomorphism
of the bounded-orbit set onto two copies of itself. Its inverse sheets
contract by at least a factor of two in the ambient Euclidean metric.
-/

namespace QuadraticCantor

open Set Function QuadraticEscape

noncomputable section

/-- The escape-potential zero locus is closed in the actual complex plane. -/
theorem filled_closed (c : ℂ) : IsClosed (filled c) := by
  have hp : Continuous (fun z : ℂ => (c, z)) :=
    continuous_const.prodMk continuous_id
  have hc : Continuous (fun z : ℂ => escape c z) := by
    change Continuous ((fun x : ℂ × ℂ => escape x.1 x.2) ∘
      (fun z : ℂ => (c, z)))
    exact escape_continuous.comp hp
  exact isClosed_singleton.preimage hc

/-- Compactness is derived from the proved global bound on bounded orbits. -/
theorem filled_compact (c : ℂ) : IsCompact (filled c) := by
  apply (isCompact_closedBall (0 : ℂ) (1 + ‖c‖)).of_isClosed_subset (filled_closed c)
  intro z hz
  rw [Metric.mem_closedBall, dist_zero_right]
  exact escape_zero_orbit_bound c z hz 0

/-- Every quadratic has an actual fixed point, hence a nonempty bounded-orbit set. -/
theorem filled_nonempty (c : ℂ) : (filled c).Nonempty := by
  obtain ⟨r, hr⟩ := exists_square_root (1 - 4 * c)
  let z : ℂ := (1 + r) / 2
  have hz : z ^ 2 + c = z := by
    dsimp [z]
    linear_combination (1 / 4 : ℂ) * hr
  have horbit (n : ℕ) : orbit c n z = z := by
    induction n with
    | zero => rfl
    | succ n ih => simpa only [orbit, ih] using hz
  refine ⟨z, (escape_zero_iff_bounded c z).mpr ⟨‖z‖, ?_⟩⟩
  intro n
  rw [horbit]

/-- The genuine quadratic self-map of the bounded-orbit set. -/
def filledMap (c : ℂ) : filled c → filled c :=
  fun z => ⟨(z : ℂ) ^ 2 + c, filled_forward z.property⟩

theorem filledMap_continuous (c : ℂ) : Continuous (filledMap c) := by
  exact ((continuous_subtype_val.pow 2).add continuous_const).subtype_mk _

/-- The disk centered at `a` is labelled zero; the opposite disk is labelled one. -/
def diskLabel (a : ℂ) (z : ℂ) : Fin 2 :=
  by
    classical
    exact if z ∈ branchDisk a then 0 else 1

private theorem filled_branch_complement {c a : ℂ} (hc : 8 ≤ ‖c‖)
    (ha : a ^ 2 = -c) :
    {z : filled c | (z : ℂ) ∉ branchDisk a} =
      {z : filled c | (z : ℂ) ∈ branchDisk (-a)} := by
  have hane : a ≠ 0 := by
    intro h
    have hb := center_norm_ge_two hc ha
    simp only [h, norm_zero] at hb
    linarith
  ext z
  constructor
  · intro hz
    exact (filled_disk_cover hc ha z.property).resolve_left hz
  · intro hz hza
    exact Set.disjoint_left.mp (branchDisks_disjoint hane) hza hz

private theorem filled_branch_clopen {c a : ℂ} (hc : 8 ≤ ‖c‖)
    (ha : a ^ 2 = -c) :
    IsClopen {z : filled c | (z : ℂ) ∈ branchDisk a} := by
  have hclosed (b : ℂ) : IsClosed {z : filled c | (z : ℂ) ∈ branchDisk b} :=
    isClosed_le ((continuous_subtype_val.sub continuous_const).norm) continuous_const
  refine ⟨hclosed a, ?_⟩
  apply isClosed_compl_iff.mp
  change IsClosed {z : filled c | (z : ℂ) ∉ branchDisk a}
  rw [filled_branch_complement hc ha]
  exact hclosed (-a)

/-- Geometric separation makes the disk labels continuous on the physical filled set. -/
theorem diskLabel_continuous {c a : ℂ} (hc : 8 ≤ ‖c‖)
    (ha : a ^ 2 = -c) :
    Continuous (fun z : filled c => diskLabel a z) := by
  classical
  apply Continuous.if _ continuous_const continuous_const
  intro z hz
  have hfront := (filled_branch_clopen hc ha).frontier_eq
  rw [hfront] at hz
  simp only [Set.mem_empty_iff_false] at hz

/-- The disk label records a uniformly expanding physical branch. -/
theorem diskLabel_expansion {c a : ℂ} (hc : 8 ≤ ‖c‖)
    (ha : a ^ 2 = -c) (x y : filled c)
    (hlabel : diskLabel a x = diskLabel a y) :
    2 * dist x y ≤ dist (filledMap c x) (filledMap c y) := by
  classical
  have hnorm := center_norm_ge_two hc ha
  change 2 * dist (x : ℂ) (y : ℂ) ≤
    dist ((x : ℂ)^2+c) ((y : ℂ)^2+c)
  simp only [dist_eq_norm]
  by_cases hx : (x : ℂ) ∈ branchDisk a
  · have hy : (y : ℂ) ∈ branchDisk a := by
      by_contra hy
      simp [diskLabel, hx, hy] at hlabel
    exact same_disk_expansion hnorm hx hy
  · have hy : (y : ℂ) ∉ branchDisk a := by
      intro hy
      simp [diskLabel, hx, hy] at hlabel
    have hx' := (filled_disk_cover hc ha x.property).resolve_left hx
    have hy' := (filled_disk_cover hc ha y.property).resolve_left hy
    exact same_disk_expansion (by simpa only [norm_neg] using hnorm) hx' hy'

/-- Each physical target has a preimage in the designated positive disk. -/
theorem positive_disk_preimage {c a : ℂ} (hc : 8 ≤ ‖c‖)
    (ha : a ^ 2 = -c) (w : filled c) :
    ∃ z : filled c, (z : ℂ) ∈ branchDisk a ∧ filledMap c z = w := by
  obtain ⟨z, hz⟩ := exists_square_root ((w : ℂ) - c)
  have hq : z ^ 2 + c = (w : ℂ) := by rw [hz, sub_add_cancel]
  have hzK : z ∈ filled c := filled_backward (hq.symm ▸ w.property)
  rcases filled_disk_cover hc ha hzK with hp | hn
  · exact ⟨⟨z, hzK⟩, hp, Subtype.ext hq⟩
  · have hqneg : (-z) ^ 2 + c = (w : ℂ) := by simpa only [neg_sq] using hq
    have hnK : -z ∈ filled c := filled_backward (hqneg.symm ▸ w.property)
    refine ⟨⟨-z, hnK⟩, ?_, Subtype.ext hqneg⟩
    simpa only [neg_neg] using (branchDisk_reflection (-a) z).mpr hn

/-- A geometric splitting with the genuine polynomial as second coordinate.
The expansion estimate is established from the quadratic formula. -/
theorem expanding_two_sheet (c : ℂ) (hc : 8 ≤ ‖c‖) :
    ∃ e : filled c ≃ₜ (Fin 2 × filled c),
      (∀ z, (e z).2 = filledMap c z) ∧
      ∀ x y, (e x).1 = (e y).1 →
        2 * dist x y ≤ dist (filledMap c x) (filledMap c y) := by
  classical
  obtain ⟨a, ha⟩ := exists_square_root (-c)
  let f : filled c → (Fin 2 × filled c) :=
    fun z => (diskLabel a z, filledMap c z)
  have hf : Continuous f :=
    (diskLabel_continuous hc ha).prodMk (filledMap_continuous c)
  have hinj : Injective f := by
    intro x y hxy
    have hl : diskLabel a x = diskLabel a y := congrArg Prod.fst hxy
    have hq : filledMap c x = filledMap c y := congrArg Prod.snd hxy
    have he := diskLabel_expansion hc ha x y hl
    rw [hq, dist_self] at he
    exact dist_eq_zero.mp (le_antisymm (by linarith) dist_nonneg)
  have hsurj : Surjective f := by
    rintro ⟨i, w⟩
    obtain ⟨z, hz, hzw⟩ := positive_disk_preimage hc ha w
    have hzlabel : diskLabel a z = 0 := if_pos hz
    have hane : a ≠ 0 := by
      intro h
      have hb := center_norm_ge_two hc ha
      simp only [h, norm_zero] at hb
      linarith
    have hzneg : -(z : ℂ) ∈ branchDisk (-a) :=
      (branchDisk_reflection a z).mpr hz
    have hzneg_not : -(z : ℂ) ∉ branchDisk a := by
      intro h
      exact Set.disjoint_left.mp (branchDisks_disjoint hane) h hzneg
    let nz : filled c := ⟨-(z : ℂ), filled_backward (by
      simpa only [neg_sq] using (filled_forward z.property))⟩
    have hnz : filledMap c nz = w := by
      apply Subtype.ext
      have he := congrArg Subtype.val hzw
      simpa only [filledMap, nz, neg_sq] using he
    fin_cases i
    · exact ⟨z, Prod.ext hzlabel hzw⟩
    · exact ⟨nz, Prod.ext (if_neg hzneg_not) hnz⟩
  letI : CompactSpace (filled c) := isCompact_iff_compactSpace.mp (filled_compact c)
  let e : filled c ≃ₜ (Fin 2 × filled c) :=
    (Equiv.ofBijective f ⟨hinj, hsurj⟩).toHomeomorphOfContinuousClosed hf hf.isClosedMap
  exact ⟨e, fun _ => rfl, fun x y h => diskLabel_expansion hc ha x y h⟩

end

end QuadraticCantor

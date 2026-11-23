import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.IntermediateValue

/-! A shooting interval for a continuous real parameter family. -/

namespace LoopsParabolic

open Set

private theorem compactLevel {f : ℝ → ℝ} {c d t : ℝ}
    (h : ContinuousOn f (Icc c d)) : IsCompact (Icc c d ∩ f ⁻¹' {t}) :=
  isCompact_Icc.of_isClosed_subset
    (h.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton) inter_subset_left

/-- From any left-to-right crossing, extract a whole parameter interval between
successive hits of the two walls. No monotonicity assumption is needed. -/
theorem exists_crossing_Icc {f : ℝ → ℝ} {a b l u : ℝ}
    (hab : a ≤ b) (hf : ContinuousOn f (Icc a b))
    (ha : f a ≤ l) (hlu : l < u) (hb : u ≤ f b) :
    ∃ p q, a ≤ p ∧ p < q ∧ q ≤ b ∧ f p = l ∧ f q = u ∧
      MapsTo f (Icc p q) (Icc l u) := by
  obtain ⟨y, hy, hyu⟩ := intermediate_value_Icc hab hf ⟨ha.trans hlu.le, hb⟩
  obtain ⟨q, hq, hfirst⟩ := (compactLevel (t := u) hf).exists_isLeast ⟨y, hy, hyu⟩
  have haq : a ≤ q := hq.1.1
  have hqb : q ≤ b := hq.1.2
  have hqu : f q = u := hq.2
  have hlq : l ≤ f q := by simpa only [hqu] using hlu.le
  have hfaq := hf.mono (Icc_subset_Icc le_rfl hqb)
  obtain ⟨z, hz, hzl⟩ := intermediate_value_Icc haq hfaq ⟨ha, hlq⟩
  obtain ⟨p, hp, hlast⟩ := (compactLevel (t := l) hfaq).exists_isGreatest ⟨z, hz, hzl⟩
  have hap : a ≤ p := hp.1.1
  have hpq : p ≤ q := hp.1.2
  have hpl : f p = l := hp.2
  have hpq' : p < q := lt_of_le_of_ne hpq (fun heq ↦ hlu.ne (hpl.symm.trans ((congrArg f heq).trans hqu)))
  refine ⟨p, q, hap, hpq', hqb, hpl, hqu, ?_⟩
  intro x hx
  have hax : a ≤ x := hap.trans hx.1
  constructor
  · by_contra! hxl
    obtain ⟨w, hw, hwl⟩ := intermediate_value_Icc hx.2
      (hfaq.mono (Icc_subset_Icc hax le_rfl)) ⟨hxl.le, hlq⟩
    have hwp : w ≤ p := hlast ⟨⟨hax.trans hw.1, hw.2⟩, hwl⟩
    have hxp := le_antisymm (hw.1.trans hwp) hx.1
    exact hxl.ne ((congrArg f hxp).trans hpl)
  · by_contra! hux
    obtain ⟨w, hw, hwu⟩ := intermediate_value_Icc hax
      (hf.mono (Icc_subset_Icc le_rfl (hx.2.trans hqb))) ⟨ha.trans hlu.le, hux.le⟩
    have hqw : q ≤ w := hfirst ⟨⟨hw.1, hw.2.trans (hx.2.trans hqb)⟩, hwu⟩
    have hxq := le_antisymm hx.2 (hqw.trans hw.2)
    exact hux.ne' ((congrArg f hxq).trans hqu)

/-- The same crossing with the upper wall reached at the left endpoint. -/
theorem exists_descending_crossing_Icc {f : ℝ → ℝ} {a b l u : ℝ}
    (hab : a ≤ b) (hf : ContinuousOn f (Icc a b))
    (ha : u ≤ f a) (hlu : l < u) (hb : f b ≤ l) :
    ∃ p q, a ≤ p ∧ p < q ∧ q ≤ b ∧ f p = u ∧ f q = l ∧
      MapsTo f (Icc p q) (Icc l u) := by
  obtain ⟨p, q, hap, hpq, hqb, hpu, hql, hmaps⟩ :=
    exists_crossing_Icc (f := fun x ↦ -f x) hab hf.neg
      (neg_le_neg ha) (neg_lt_neg hlu) (neg_le_neg hb)
  refine ⟨p, q, hap, hpq, hqb, neg_inj.mp hpu, neg_inj.mp hql, ?_⟩
  intro x hx
  exact ⟨neg_le_neg_iff.mp (hmaps hx).2, neg_le_neg_iff.mp (hmaps hx).1⟩

/-- After the last hit of a level, the trajectory stays on the side containing
its right endpoint. -/
theorem exists_last_upper_hit {f : ℝ → ℝ} {a b u : ℝ}
    (hab : a ≤ b) (hf : ContinuousOn f (Icc a b)) (ha : u ≤ f a) (hb : f b < u) :
    ∃ q ∈ Icc a b, f q = u ∧ ∀ t ∈ Icc q b, f t ≤ u := by
  obtain ⟨z, hz, hzu⟩ := intermediate_value_Icc' hab hf ⟨hb.le, ha⟩
  obtain ⟨q, hq, hlast⟩ := (compactLevel (t := u) hf).exists_isGreatest ⟨z, hz, hzu⟩
  refine ⟨q, hq.1, hq.2, ?_⟩
  intro t ht
  by_contra! hut
  have hat := hq.1.1.trans ht.1
  obtain ⟨w, hw, hwu⟩ := intermediate_value_Icc' ht.2
    (hf.mono (Icc_subset_Icc hat le_rfl)) ⟨hb.le, hut.le⟩
  have hwq : w ≤ q := hlast ⟨⟨hat.trans hw.1, hw.2⟩, hwu⟩
  have htq := le_antisymm (hw.1.trans hwq) ht.1
  exact hut.ne' ((congrArg f htq).trans hq.2)

end LoopsParabolic

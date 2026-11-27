import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Tactic.Linarith

/-!
# First exits of continuous radial terminal coordinates

The selected endpoint is the first level crossing. Perturbed coordinates
need not be monotone and may have further crossings. Uniform approximation
to a strictly decreasing limit nevertheless controls every crossing and
the entire retained initial interval.
-/

namespace CrestFirstExit

open Set Filter
open scoped Topology

/-- A continuous coordinate starting above the level and ending below it
has a first interior crossing, with strict survival at every earlier radius. -/
theorem exists_first_exit (f : ℝ → ℝ) {a b level : ℝ}
    (hab : a < b) (hf : ContinuousOn f (Icc a b))
    (ha : level < f a) (hb : f b < level) :
    ∃ r ∈ Ioo a b, f r = level ∧ ∀ s ∈ Ico a r, level < f s := by
  have hnonempty : (Icc a b ∩ f ⁻¹' {level}).Nonempty := by
    obtain ⟨x, hx, hfx⟩ := intermediate_value_Icc' hab.le hf ⟨hb.le, ha.le⟩
    exact ⟨x, hx, hfx⟩
  have hcompact : IsCompact (Icc a b ∩ f ⁻¹' {level}) :=
    isCompact_Icc.of_isClosed_subset
      (hf.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton)
      inter_subset_left
  obtain ⟨r, hr, hmin⟩ := hcompact.exists_isMinOn hnonempty continuousOn_id
  have hroot : f r = level := hr.2
  have har : a < r := by
    by_contra h
    have he : r = a := le_antisymm (le_of_not_gt h) hr.1.1
    rw [he] at hroot
    linarith
  have hrb : r < b := by
    by_contra h
    have he : r = b := le_antisymm hr.1.2 (le_of_not_gt h)
    rw [he] at hroot
    linarith
  refine ⟨r, ⟨har, hrb⟩, hroot, ?_⟩
  intro s hs
  by_contra h
  have hfs : f s ≤ level := le_of_not_gt h
  have hsub : Icc a s ⊆ Icc a b := Icc_subset_Icc_right (hs.2.le.trans hr.1.2)
  obtain ⟨x, hx, hfx⟩ := intermediate_value_Icc' hs.1 (hf.mono hsub) ⟨hfs, ha.le⟩
  have hrx : r ≤ x := hmin ⟨hsub hx, hfx⟩
  linarith [hx.2, hs.2]

/-- The first crossing is exactly the maximal endpoint of a strictly
surviving initial half-open interval. -/
theorem first_exit_prefix_iff (f : ℝ → ℝ) {a r level s : ℝ}
    (har : a ≤ r) (hroot : f r = level)
    (hbefore : ∀ x ∈ Ico a r, level < f x) :
    (∀ x ∈ Ico a s, level < f x) ↔ s ≤ r := by
  constructor
  · intro h
    by_contra hs
    have hp := h r ⟨har, lt_of_not_ge hs⟩
    rw [hroot] at hp
    exact lt_irrefl _ hp
  · intro hs x hx
    exact hbefore x ⟨hx.1, hx.2.trans_le hs⟩

/-- First crossings are unique even if the coordinate has many later
crossings or tangent contacts with the same level. -/
theorem first_exit_unique (f : ℝ → ℝ) {a r s level : ℝ}
    (har : a ≤ r) (has : a ≤ s)
    (hr : f r = level) (hs : f s = level)
    (hbefore_r : ∀ x ∈ Ico a r, level < f x)
    (hbefore_s : ∀ x ∈ Ico a s, level < f x) : r = s := by
  apply le_antisymm
  · exact (first_exit_prefix_iff f has hs hbefore_s).mp hbefore_r
  · exact (first_exit_prefix_iff f har hr hbefore_r).mp hbefore_s

/-- The surviving connected component containing the inner endpoint
is exactly the initial half-open interval. Later surviving islands
cannot enlarge this selected component. -/
theorem first_exit_component (f : ℝ → ℝ) {a b r level : ℝ}
    (hr : r ∈ Ioo a b) (hroot : f r = level)
    (hbefore : ∀ x ∈ Ico a r, level < f x) :
    connectedComponentIn (Icc a b ∩ {x | level < f x}) a = Ico a r := by
  let S := Icc a b ∩ {x | level < f x}
  have ha : a ∈ S := ⟨⟨le_rfl, hr.1.le.trans hr.2.le⟩,
    hbefore a ⟨le_rfl, hr.1⟩⟩
  apply Subset.antisymm
  · intro x hx
    have hxS : x ∈ S := connectedComponentIn_subset S a hx
    refine ⟨hxS.1.1, ?_⟩
    by_contra h
    have hrc : r ∈ connectedComponentIn S a :=
      isPreconnected_connectedComponentIn.Icc_subset
        (mem_connectedComponentIn ha) hx ⟨hr.1.le, le_of_not_gt h⟩
    have hbad := (connectedComponentIn_subset S a hrc).2
    change level < f r at hbad
    rw [hroot] at hbad
    exact lt_irrefl _ hbad
  · apply isPreconnected_Ico.subset_connectedComponentIn ⟨le_rfl, hr.1⟩
    intro x hx
    exact ⟨⟨hx.1, hx.2.le.trans hr.2.le⟩, hbefore x hx⟩

/-- A uniform error smaller than the two limiting endpoint gaps
controls the signs on both entire outer intervals, not just at their ends. -/
theorem uniform_sign_margins (f g : ℝ → ℝ) {a b l u level ε : ℝ}
    (hanti : StrictAntiOn f (Icc a b))
    (hl : l ∈ Icc a b) (hu : u ∈ Icc a b)
    (hεl : ε < f l - level) (hεu : ε < level - f u)
    (herr : ∀ x ∈ Icc a b, |g x - f x| ≤ ε) :
    (∀ x ∈ Icc a l, level < g x) ∧
      (∀ x ∈ Icc u b, g x < level) := by
  constructor
  · intro x hx
    have hxfull : x ∈ Icc a b := ⟨hx.1, hx.2.trans hl.2⟩
    have horder : f l ≤ f x := hanti.antitoneOn hxfull hl hx.2
    have he := (abs_le.mp (herr x hxfull)).1
    linarith
  · intro x hx
    have hxfull : x ∈ Icc a b := ⟨hu.1.trans hx.1, hx.2⟩
    have horder : f x ≤ f u := hanti.antitoneOn hu hxfull hx.1
    have he := (abs_le.mp (herr x hxfull)).2
    linarith

/-- Uniform approximation to a strictly decreasing limit eventually
preserves the strict signs on every fixed pair of outer compact intervals. -/
theorem eventually_uniform_sign_margins (F : ℕ → ℝ → ℝ) (f : ℝ → ℝ)
    {a b l r u level : ℝ}
    (hconv : TendstoUniformlyOn F f atTop (Icc a b))
    (hanti : StrictAntiOn f (Icc a b))
    (hl : l ∈ Icc a b) (hr : r ∈ Icc a b) (hu : u ∈ Icc a b)
    (hlr : l < r) (hru : r < u) (hroot : f r = level) :
    ∀ᶠ n in atTop,
      (∀ x ∈ Icc a l, level < F n x) ∧
        (∀ x ∈ Icc u b, F n x < level) := by
  have hleft : 0 < f l - level := by
    have h := hanti hl hr hlr
    rw [hroot] at h
    linarith
  have hright : 0 < level - f u := by
    have h := hanti hr hu hru
    rw [hroot] at h
    linarith
  let ε := min (f l - level) (level - f u) / 2
  have hε : 0 < ε := div_pos (lt_min hleft hright) (by norm_num)
  have hεl : ε < f l - level := by
    have := min_le_left (f l - level) (level - f u)
    dsimp [ε]
    linarith
  have hεu : ε < level - f u := by
    have := min_le_right (f l - level) (level - f u)
    dsimp [ε]
    linarith
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hconv ε hε] with n hn
  apply uniform_sign_margins f (F n) hanti hl hu hεl hεu
  intro x hx
  have h := (hn x hx).le
  simpa only [Real.dist_eq, abs_sub_comm] using h

/-- Away from the limiting crossing, both retained and excluded sides
have one positive gap from the level, uniform in radius and in all
sufficiently late members of the approximating sequence. -/
theorem eventually_uniform_level_gap (F : ℕ → ℝ → ℝ) (f : ℝ → ℝ)
    {a b l r u level : ℝ}
    (hconv : TendstoUniformlyOn F f atTop (Icc a b))
    (hanti : StrictAntiOn f (Icc a b))
    (hl : l ∈ Icc a b) (hr : r ∈ Icc a b) (hu : u ∈ Icc a b)
    (hlr : l < r) (hru : r < u) (hroot : f r = level) :
    ∃ δ > 0, ∀ᶠ n in atTop,
      (∀ x ∈ Icc a l, level + δ ≤ F n x) ∧
        (∀ x ∈ Icc u b, F n x ≤ level - δ) := by
  have hleft : 0 < f l - level := by
    have h := hanti hl hr hlr
    rw [hroot] at h
    linarith
  have hright : 0 < level - f u := by
    have h := hanti hr hu hru
    rw [hroot] at h
    linarith
  let δ := min (f l - level) (level - f u) / 2
  have hδ : 0 < δ := div_pos (lt_min hleft hright) (by norm_num)
  have hδl : 2 * δ ≤ f l - level := by
    dsimp [δ]
    linarith [min_le_left (f l - level) (level - f u)]
  have hδu : 2 * δ ≤ level - f u := by
    dsimp [δ]
    linarith [min_le_right (f l - level) (level - f u)]
  refine ⟨δ, hδ, ?_⟩
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hconv δ hδ] with n hn
  have he (x : ℝ) (hx : x ∈ Icc a b) : |F n x - f x| ≤ δ := by
    simpa only [Real.dist_eq, abs_sub_comm] using (hn x hx).le
  constructor
  · intro x hx
    have hxfull : x ∈ Icc a b := ⟨hx.1, hx.2.trans hl.2⟩
    have horder : f l ≤ f x := hanti.antitoneOn hxfull hl hx.2
    have hbound := (abs_le.mp (he x hxfull)).1
    linarith
  · intro x hx
    have hxfull : x ∈ Icc a b := ⟨hu.1.trans hx.1, hx.2⟩
    have horder : f x ≤ f u := hanti.antitoneOn hu hxfull hx.1
    have hbound := (abs_le.mp (he x hxfull)).2
    linarith

/-- Every choice of perturbed roots tends to the unique limiting crossing.
No monotonicity, uniqueness, or continuity of the perturbed coordinates
is needed for this conclusion once their roots have been selected. -/
theorem uniform_root_tendsto (F : ℕ → ℝ → ℝ) (f : ℝ → ℝ) (roots : ℕ → ℝ)
    {a b r level : ℝ}
    (hconv : TendstoUniformlyOn F f atTop (Icc a b))
    (hanti : StrictAntiOn f (Icc a b))
    (hr : r ∈ Ioo a b) (hroot : f r = level)
    (hroots : ∀ᶠ n in atTop, roots n ∈ Icc a b ∧ F n (roots n) = level) :
    Tendsto roots atTop (𝓝 r) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let l := max a (r - ε / 2)
  let u := min b (r + ε / 2)
  have hlr : l < r := max_lt hr.1 (by linarith)
  have hru : r < u := lt_min hr.2 (by linarith)
  have hl : l ∈ Icc a b := ⟨le_max_left _ _, hlr.le.trans hr.2.le⟩
  have hu : u ∈ Icc a b := ⟨hr.1.le.trans hru.le, min_le_left _ _⟩
  have hsign := eventually_uniform_sign_margins F f hconv hanti hl
    ⟨hr.1.le, hr.2.le⟩ hu hlr hru hroot
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hsign.and hroots)
  refine ⟨N, ?_⟩
  intro n hn
  obtain ⟨⟨hleft, hright⟩, hmem, hlevel⟩ := hN n hn
  have hlroot : l < roots n := by
    by_contra h
    have hh := hleft (roots n) ⟨hmem.1, le_of_not_gt h⟩
    rw [hlevel] at hh
    exact lt_irrefl _ hh
  have hrootu : roots n < u := by
    by_contra h
    have hh := hright (roots n) ⟨le_of_not_gt h, hmem.2⟩
    rw [hlevel] at hh
    exact lt_irrefl _ hh
  have hlower : r - ε / 2 ≤ l := le_max_right _ _
  have hupper : u ≤ r + ε / 2 := min_le_right _ _
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

/-- Uniform convergence and eventual continuity construct convergent
first-exit endpoints automatically. All sufficiently late coordinates
have the full initial-component description, even if they oscillate
after their first crossing. -/
theorem exists_first_exits_converging (F : ℕ → ℝ → ℝ) (f : ℝ → ℝ)
    {a b r level : ℝ}
    (hconv : TendstoUniformlyOn F f atTop (Icc a b))
    (hanti : StrictAntiOn f (Icc a b))
    (hr : r ∈ Ioo a b) (hroot : f r = level)
    (hcont : ∀ᶠ n in atTop, ContinuousOn (F n) (Icc a b)) :
    ∃ roots : ℕ → ℝ, Tendsto roots atTop (𝓝 r) ∧
      ∀ᶠ n in atTop,
        roots n ∈ Ioo a b ∧ F n (roots n) = level ∧
          (∀ s ∈ Ico a (roots n), level < F n s) ∧
          connectedComponentIn (Icc a b ∩ {x | level < F n x}) a = Ico a (roots n) := by
  classical
  have hab : a < b := hr.1.trans hr.2
  have hsign := eventually_uniform_sign_margins F f hconv hanti
    ⟨le_rfl, hab.le⟩ ⟨hr.1.le, hr.2.le⟩ ⟨hab.le, le_rfl⟩
    hr.1 hr.2 hroot
  have hex : ∀ᶠ n in atTop,
      ∃ s ∈ Ioo a b, F n s = level ∧ ∀ x ∈ Ico a s, level < F n x := by
    filter_upwards [hsign, hcont] with n hn hc
    exact exists_first_exit (F n) hab hc
      (hn.1 a ⟨le_rfl, le_rfl⟩) (hn.2 b ⟨le_rfl, le_rfl⟩)
  let roots : ℕ → ℝ := fun n =>
    if h : ∃ s ∈ Ioo a b, F n s = level ∧ ∀ x ∈ Ico a s, level < F n x
    then h.choose else r
  have hspec : ∀ᶠ n in atTop,
      roots n ∈ Ioo a b ∧ F n (roots n) = level ∧
        ∀ x ∈ Ico a (roots n), level < F n x := by
    filter_upwards [hex] with n hn
    simp only [roots, dif_pos hn]
    exact hn.choose_spec
  refine ⟨roots, uniform_root_tendsto F f roots hconv hanti hr hroot ?_, ?_⟩
  · filter_upwards [hspec] with n hn
    exact ⟨⟨hn.1.1.le, hn.1.2.le⟩, hn.2.1⟩
  · filter_upwards [hspec] with n hn
    exact ⟨hn.1, hn.2.1, hn.2.2, first_exit_component (F n) hn.1 hn.2.1 hn.2.2⟩

end CrestFirstExit

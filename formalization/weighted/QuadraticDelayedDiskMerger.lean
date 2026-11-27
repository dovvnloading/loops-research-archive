import QuadraticDelayedMerger

/-!
# Delayed actual mergers through strictly increasing bounded disks

The target disks are centered at 1 and have radii
(2k+N+1)/(k+2(N+1)).  Every sequence starts with the same disk of
radius 1/2, its closures lie in the next disks, and its union is the
same disk of radius 2.  Nevertheless the actual roots 1 and -1 of
z² = 1 first join at the arbitrarily prescribed stage N+2.

Thus neither strict geometric growth, compact closure, nor fixed
initial and bounded limiting targets supply a uniform stage of finite-fiber
stabilization.  This is a sharpness example, not a realization of
native virtual-block markings.
-/

namespace LoopsQuadraticDelayedDiskMerger

open Set Function Metric Classical
open LoopsQuadraticCylinderCensus LoopsQuadraticCylinderRamification
open LoopsQuadraticComponentFiberDegree LoopsQuadraticDelayedMerger

noncomputable section

def diskRadius (N k : ℕ) : ℝ :=
  (2*(k : ℝ)+(N : ℝ)+1) / ((k : ℝ)+2*((N : ℝ)+1))

def diskTarget (N k : ℕ) : Set ℂ := ball 1 (diskRadius N k)

theorem diskRadius_pos (N k : ℕ) : 0 < diskRadius N k := by
  unfold diskRadius
  positivity

theorem diskRadius_zero (N : ℕ) : diskRadius N 0 = 1/2 := by
  have hN : (N : ℝ)+1 ≠ 0 := by positivity
  unfold diskRadius
  norm_num only [Nat.cast_zero, mul_zero, zero_add]
  field_simp [hN]
  <;> ring

theorem diskTarget_zero (N : ℕ) : diskTarget N 0 = ball (1 : ℂ) (1/2) := by
  unfold diskTarget
  rw [diskRadius_zero]

theorem diskRadius_lt_two (N k : ℕ) : diskRadius N k < 2 := by
  have hden : 0 < (k : ℝ)+2*((N : ℝ)+1) := by positivity
  rw [diskRadius, div_lt_iff₀ hden]
  have hN : (0 : ℝ) ≤ N := by positivity
  nlinarith

theorem diskRadius_le_one_iff (N k : ℕ) : diskRadius N k ≤ 1 ↔ k ≤ N+1 := by
  have hden : 0 < (k : ℝ)+2*((N : ℝ)+1) := by positivity
  rw [diskRadius, div_le_iff₀ hden]
  constructor
  · intro h
    have h' : (k : ℝ) ≤ (N : ℝ)+1 := by linarith
    exact_mod_cast h'
  · intro h
    have h' : (k : ℝ) ≤ (N : ℝ)+1 := by exact_mod_cast h
    linarith

/-- The unique critical value enters at precisely the merger stage. -/
theorem zero_mem_diskTarget_iff (N k : ℕ) :
    (0 : ℂ) ∈ diskTarget N k ↔ N+1 < k := by
  have h := not_congr (diskRadius_le_one_iff N k)
  simpa [diskTarget] using h

theorem diskRadius_strictMono (N : ℕ) : StrictMono (diskRadius N) := by
  intro i j hij
  have hdi : 0 < (i : ℝ)+2*((N : ℝ)+1) := by positivity
  have hdj : 0 < (j : ℝ)+2*((N : ℝ)+1) := by positivity
  have hij' : (i : ℝ) < j := by exact_mod_cast hij
  have hN : 0 < (N : ℝ)+1 := by positivity
  have hm := mul_pos (sub_pos.mpr hij') hN
  rw [diskRadius, diskRadius, div_lt_div_iff₀ hdi hdj]
  nlinarith only [hm]

theorem diskTarget_open_connected (N k : ℕ) :
    IsOpen (diskTarget N k) ∧ IsConnected (diskTarget N k) := by
  exact ⟨isOpen_ball,
    (convex_ball (1 : ℂ) (diskRadius N k)).isConnected
      ⟨1, mem_ball_self (diskRadius_pos N k)⟩⟩

theorem one_mem_diskTarget (N k : ℕ) : (1 : ℂ) ∈ diskTarget N k :=
  mem_ball_self (diskRadius_pos N k)

theorem diskTarget_compact_closure (N k : ℕ) :
    IsCompact (closure (diskTarget N k)) :=
  (isCompact_closedBall (1 : ℂ) (diskRadius N k)).of_isClosed_subset
    isClosed_closure closure_ball_subset_closedBall

/-- Every stage has its whole closure inside the next stage. -/
theorem diskTarget_closure_subset_next (N k : ℕ) :
    closure (diskTarget N k) ⊆ diskTarget N (k+1) := by
  intro z hz
  have hb : dist z 1 ≤ diskRadius N k :=
    closure_ball_subset_closedBall hz
  exact hb.trans_lt (diskRadius_strictMono N (Nat.lt_succ_self k))

/-- The sequence grows strictly at every stage; its delay is not
created by repeating identical target domains. -/
theorem diskTarget_strictMono (N : ℕ) : StrictMono (diskTarget N) := by
  intro i j hij
  have hr := diskRadius_strictMono N hij
  have hsub : diskTarget N i ⊆ diskTarget N j := ball_subset_ball hr.le
  apply (lt_iff_le_not_ge).mpr
  refine ⟨hsub, ?_⟩
  intro hback
  let r : ℝ := (diskRadius N i+diskRadius N j)/2
  have hr0 : 0 ≤ r := by
    dsimp [r]
    linarith [diskRadius_pos N i, diskRadius_pos N j]
  have hri : diskRadius N i < r := by dsimp [r]; linarith
  have hrj : r < diskRadius N j := by dsimp [r]; linarith
  have hd : dist ((1 : ℂ)+(r : ℂ)) 1 = r := by
    rw [dist_eq_norm]
    have he : ((1 : ℂ)+(r : ℂ))-1 = (r : ℂ) := by ring
    rw [he, Complex.norm_real, Real.norm_of_nonneg hr0]
  have hzj : ((1 : ℂ)+(r : ℂ)) ∈ diskTarget N j := by
    change dist ((1 : ℂ)+(r : ℂ)) 1 < diskRadius N j
    rwa [hd]
  have hzi : dist ((1 : ℂ)+(r : ℂ)) 1 < diskRadius N i := hback hzj
  rw [hd] at hzi
  exact (not_lt_of_ge hri.le) hzi

/-- All delays use the same bounded limiting disk. -/
theorem diskTarget_union (N : ℕ) : (⋃ k, diskTarget N k) = ball (1 : ℂ) 2 := by
  apply Subset.antisymm
  · intro z hz
    obtain ⟨k, hk⟩ := mem_iUnion.mp hz
    exact (show dist z 1 < diskRadius N k from hk).trans (diskRadius_lt_two N k)
  · intro z hz
    have ht : dist z 1 < 2 := hz
    have hgap : 0 < 2-dist z 1 := by linarith
    obtain ⟨k, hk⟩ := exists_nat_gt (dist z 1*(2*((N : ℝ)+1))/(2-dist z 1))
    have hk' : dist z 1*(2*((N : ℝ)+1)) < (k : ℝ)*(2-dist z 1) :=
      (div_lt_iff₀ hgap).mp hk
    apply mem_iUnion.mpr
    refine ⟨k, ?_⟩
    change dist z 1 < diskRadius N k
    have hden : 0 < (k : ℝ)+2*((N : ℝ)+1) := by positivity
    rw [diskRadius, lt_div_iff₀ hden]
    have hN : 0 < (N : ℝ)+1 := by positivity
    nlinarith only [hk', hN]

/-- A disk centered at 1 of radius at most 1 lies in the open
right half-plane; the radius-one disk still excludes zero. -/
theorem diskTarget_subset_rightHalfPlane (N k : ℕ) (hk : k ≤ N+1) :
    diskTarget N k ⊆ rightHalfPlane := by
  intro z hz
  have hnorm : ‖z-1‖ < diskRadius N k := by
    simpa only [diskTarget, mem_ball, dist_eq_norm] using hz
  have hlow := neg_le_abs (z-1).re
  have hbound := Complex.abs_re_le_norm (z-1)
  have hr : diskRadius N k ≤ 1 := (diskRadius_le_one_iff N k).mpr hk
  have hre : (z-1).re = z.re-1 := by simp
  change 0 < z.re
  rw [hre] at hlow hbound
  linarith

/-- Once the disk includes zero, the actual real segment from -1
to 1 connects both inverse points inside the quadratic preimage. -/
theorem roots_joined_in_large_disk (r : ℝ) (hr : 1 < r) :
    (-1 : ℂ) ∈ connectedComponentIn ((quad 0) ⁻¹' ball (1 : ℂ) r) 1 := by
  let S : Set ℂ := (fun t : ℝ => (t : ℂ)) '' Icc (-1 : ℝ) 1
  have hS : IsPreconnected S :=
    isPreconnected_Icc.image _ Complex.continuous_ofReal.continuousOn
  have hp : (1 : ℂ) ∈ S := ⟨1, by norm_num, rfl⟩
  have hn : (-1 : ℂ) ∈ S := ⟨-1, by norm_num, by norm_num⟩
  have hsub : S ⊆ (quad 0) ⁻¹' ball (1 : ℂ) r := by
    rintro z ⟨t, ht, rfl⟩
    have hsq : t^2 ≤ 1 := by
      have hprod := mul_nonneg (sub_nonneg.mpr ht.2)
        (show 0 ≤ t+1 by linarith [ht.1])
      nlinarith only [hprod]
    have he : quad 0 (t : ℂ)-1 = ((t^2-1 : ℝ) : ℂ) := by
      simp [quad]
    have hnorm : ‖quad 0 (t : ℂ)-1‖ ≤ 1 := by
      rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith : t^2-1 ≤ 0)]
      nlinarith [sq_nonneg t]
    change dist (quad 0 (t : ℂ)) 1 < r
    rw [dist_eq_norm]
    exact hnorm.trans_lt hr
  exact hS.subset_connectedComponentIn hp hsub hn

/-- The same fixed regular inverse pair first joins exactly at
N+2 in these strictly increasing relatively compact target disks. -/
theorem disk_merger_exact (N k : ℕ) :
    (-1 : ℂ) ∈ connectedComponentIn ((quad 0) ⁻¹' diskTarget N k) 1 ↔ N+1 < k := by
  constructor
  · intro h
    by_contra hn
    have hk : k ≤ N+1 := by omega
    have hm := connectedComponentIn_mono (1 : ℂ)
      (preimage_mono (diskTarget_subset_rightHalfPlane N k hk))
    exact negative_one_not_in_positive_component (hm h)
  · intro hk
    have hr : 1 < diskRadius N k := by
      apply lt_of_not_ge
      intro h
      exact (Nat.not_le_of_gt hk) ((diskRadius_le_one_iff N k).mp h)
    exact roots_joined_in_large_disk (diskRadius N k) hr

/-- The full actual local inverse fiber is determined, not just a
pair of sample points: it is {1} until the merger and {1,-1} after. -/
theorem disk_selected_fiber (N k : ℕ) :
    localFiber 0 1 (connectedComponentIn ((quad 0) ⁻¹' diskTarget N k) 1) 1 =
      if k ≤ N+1 then {1} else {1, -1} := by
  classical
  have hp : (1 : ℂ) ∈ connectedComponentIn ((quad 0) ⁻¹' diskTarget N k) 1 := by
    apply mem_connectedComponentIn
    simpa [quad] using one_mem_diskTarget N k
  by_cases hk : k ≤ N+1
  · rw [if_pos hk]
    ext z
    simp only [mem_localFiber, Function.iterate_one, Finset.mem_singleton]
    constructor
    · rintro ⟨hz, he⟩
      have he' : quad 0 z = quad 0 1 := by simpa [quad] using he
      rcases quadratic_eq_or_neg 0 z 1 he' with h | h
      · exact h
      · subst z
        have hlate := (disk_merger_exact N k).mp hz
        omega
    · intro he
      subst z
      exact ⟨hp, by norm_num [quad]⟩
  · rw [if_neg hk]
    have hn := (disk_merger_exact N k).mpr (by omega)
    ext z
    simp only [mem_localFiber, Function.iterate_one, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨_, he⟩
      have he' : quad 0 z = quad 0 1 := by simpa [quad] using he
      exact quadratic_eq_or_neg 0 z 1 he'
    · rintro (he | he)
      · subst z
        exact ⟨hp, by norm_num [quad]⟩
      · subst z
        exact ⟨hn, by norm_num [quad]⟩

theorem disk_selected_fiber_count (N k : ℕ) :
    (localFiber 0 1 (connectedComponentIn ((quad 0) ⁻¹' diskTarget N k) 1) 1).card =
      if k ≤ N+1 then 1 else 2 := by
  classical
  rw [disk_selected_fiber]
  split_ifs <;> norm_num

/-- Strict nesting, compact closures inside the next stage, and
fixed initial and bounded limiting targets give no universal stage at
which the two-point regular fiber has stabilized. -/
theorem no_uniform_precompact_disk_stabilization_stage :
    ¬ ∃ B : ℕ, ∀ U : ℕ → Set ℂ,
      StrictMono U →
      (∀ k, IsOpen (U k) ∧ IsConnected (U k) ∧ IsCompact (closure (U k)) ∧
        closure (U k) ⊆ U (k+1)) →
      U 0 = ball (1 : ℂ) (1/2) → (⋃ k, U k) = ball (1 : ℂ) 2 →
      (-1 : ℂ) ∈ connectedComponentIn ((quad 0) ⁻¹' U B) 1 := by
  rintro ⟨B, hB⟩
  have h := hB (diskTarget B) (diskTarget_strictMono B)
    (fun k => ⟨(diskTarget_open_connected B k).1,
      (diskTarget_open_connected B k).2, diskTarget_compact_closure B k,
      diskTarget_closure_subset_next B k⟩)
    (diskTarget_zero B) (diskTarget_union B)
  have hlate := (disk_merger_exact B B).mp h
  omega

end

end LoopsQuadraticDelayedDiskMerger

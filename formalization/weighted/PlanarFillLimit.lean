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

/-- The filled hull is upper semicontinuous even without a nested sequence.
A sufficiently small one-sided thickening of a compact seed controls the
filled hull of every subset of that thickening. -/
theorem planarFill_upper_semicontinuous (K : Set ℂ) (hK : IsCompact K)
    (V : Set ℂ) (hV : IsOpen V) (hKV : planarFill K ⊆ V) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ T : Set ℂ, T ⊆ cthickening δ K → planarFill T ⊆ V := by
  let S : ℕ → Set ℂ := fun n => cthickening (1 / ((n : ℝ) + 1)) K
  have hc : ∀ n, IsCompact (S n) := fun _ => hK.cthickening
  have hm : Antitone S := by
    intro i j hij
    have hcast : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
    exact cthickening_mono
      (div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)) K
  have hI : (⋂ n, S n) = K := by
    apply Subset.antisymm
    · intro z hz
      by_contra hnot
      have hsub : K ⊆ ({z} : Set ℂ)ᶜ := by
        intro w hw he
        have heq : w = z := mem_singleton_iff.mp he
        exact hnot (heq ▸ hw)
      obtain ⟨δ, hδ, hδsub⟩ :=
        hK.exists_cthickening_subset_open isClosed_singleton.isOpen_compl hsub
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
      have hz' : z ∈ cthickening δ K :=
        cthickening_mono hn.le K (mem_iInter.mp hz n)
      exact (hδsub hz') (by simp)
    · intro z hz
      exact mem_iInter.mpr fun n => self_subset_cthickening K hz
  obtain ⟨N, hN⟩ := planarFill_eventually_subset_open S hc hm V hV (by rwa [hI])
  exact ⟨1 / ((N : ℝ) + 1), by positivity,
    fun T hT => (planarFill_mono hT).trans (hN N le_rfl)⟩

private theorem unbounded_radial_ray (a : ℂ) (ha : 0 < ‖a‖) (L : ℝ) :
    ¬ IsBounded ((fun t : ℝ => t • a) '' Ici L) := by
  intro h
  obtain ⟨R, _, hball⟩ := h.subset_closedBall_lt 0 (0 : ℂ)
  let t : ℝ := max L (max 1 ((R+1)/‖a‖))
  have htL : L ≤ t := le_max_left _ _
  have ht1 : 1 ≤ t :=
    (le_max_left (1 : ℝ) ((R+1)/‖a‖)).trans (le_max_right L _)
  have htR : (R+1)/‖a‖ ≤ t :=
    (le_max_right (1 : ℝ) ((R+1)/‖a‖)).trans (le_max_right L _)
  have hmul : R+1 ≤ t * ‖a‖ := (div_le_iff₀ ha).mp htR
  have htball : t • a ∈ closedBall (0 : ℂ) R := hball ⟨t, htL, rfl⟩
  rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (by linarith : 0 ≤ t)] at htball
  linarith

private theorem outward_ray_exterior {S : Set ℂ}
    (hS : S ⊆ sphere (0 : ℂ) 1) {z : ℂ}
    (hnorm : 1 ≤ ‖z‖) (hz : z ∉ S) : z ∉ planarFill S := by
  intro hfill
  let A : Set ℂ := (fun t : ℝ => t • z) '' Ici 1
  have hsub : A ⊆ Sᶜ := by
    rintro w ⟨t, ht, rfl⟩ hmem
    have ht1 : 1 ≤ t := ht
    have ht0 : 0 ≤ t := by linarith
    have hn := mem_sphere_zero_iff_norm.mp (hS hmem)
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0] at hn
    have hmul : t ≤ t * ‖z‖ := by
      simpa using mul_le_mul_of_nonneg_left hnorm ht0
    have heq : t = 1 := by linarith
    subst t
    exact hz (by simpa using hmem)
  have hcont : Continuous (fun t : ℝ => t • z) := by fun_prop
  have hpre : IsPreconnected A := isPreconnected_Ici.image _ hcont.continuousOn
  have hzA : z ∈ A := ⟨1, le_rfl, one_smul ℝ z⟩
  change IsBounded (connectedComponentIn Sᶜ z) at hfill
  exact unbounded_radial_ray z (by linarith) 1
    (hfill.subset (hpre.subset_connectedComponentIn hzA hsub))

/-- Removing even one point from the unit circle destroys its hole:
every subset of the remaining circle is full. No compactness of the
subset is needed. The missing point gives an actual radial exit. -/
theorem planarFill_of_proper_subset_unitSphere (S : Set ℂ)
    (hS : S ⊆ sphere (0 : ℂ) 1) (a : ℂ)
    (ha : a ∈ sphere (0 : ℂ) 1) (hmiss : a ∉ S) : planarFill S = S := by
  apply Subset.antisymm _ (planarFill_extensive S)
  intro z hz
  by_contra hnot
  have ha1 := mem_sphere_zero_iff_norm.mp ha
  let A : Set ℂ := (fun t : ℝ => t • a) '' Ici 0
  have hsub : A ⊆ Sᶜ := by
    rintro w ⟨t, ht, rfl⟩ hmem
    have ht0 : 0 ≤ t := ht
    have hn := mem_sphere_zero_iff_norm.mp (hS hmem)
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0, ha1, mul_one] at hn
    subst t
    exact hmiss (by simpa using hmem)
  have hcont : Continuous (fun t : ℝ => t • a) := by fun_prop
  have hpre : IsPreconnected A := isPreconnected_Ici.image _ hcont.continuousOn
  have h0A : (0 : ℂ) ∈ A := ⟨0, le_rfl, zero_smul ℝ a⟩
  have h0unbounded : ¬ IsBounded (connectedComponentIn Sᶜ (0 : ℂ)) :=
    fun h => unbounded_radial_ray a (by linarith) 0
      (h.subset (hpre.subset_connectedComponentIn h0A hsub))
  by_cases hz1 : ‖z‖ < 1
  · have hbsub : ball (0 : ℂ) 1 ⊆ Sᶜ := by
      intro w hw hs
      have hnorm := mem_sphere_zero_iff_norm.mp (hS hs)
      have hlt : ‖w‖ < 1 := by simpa [mem_ball, dist_zero_right] using hw
      linarith
    have hbpre : IsPreconnected (ball (0 : ℂ) 1) := (convex_ball _ _).isPreconnected
    have h0b : (0 : ℂ) ∈ ball (0 : ℂ) 1 := by simp
    have hzb : z ∈ ball (0 : ℂ) 1 := by simpa [mem_ball, dist_zero_right] using hz1
    have hzc := hbpre.subset_connectedComponentIn h0b hbsub hzb
    change IsBounded (connectedComponentIn Sᶜ z) at hz
    exact h0unbounded ((connectedComponentIn_eq hzc).symm ▸ hz :
      IsBounded (connectedComponentIn Sᶜ (0 : ℂ)))
  · exact outward_ray_exterior hS (le_of_not_gt hz1) hnot hz

/-- The full unit circle, in contrast to any proper subset, fills the
entire closed unit disk. -/
theorem planarFill_unitSphere :
    planarFill (sphere (0 : ℂ) 1) = closedBall (0 : ℂ) 1 := by
  apply Subset.antisymm
  · intro z hz
    by_contra hout
    have hgt : 1 < ‖z‖ := by
      simpa only [mem_closedBall, dist_zero_right, not_le] using hout
    have hnot : z ∉ sphere (0 : ℂ) 1 :=
      fun h => (ne_of_gt hgt) (mem_sphere_zero_iff_norm.mp h)
    exact outward_ray_exterior subset_rfl hgt.le hnot hz
  · intro z hz
    have hn : ‖z‖ ≤ 1 := by simpa [mem_closedBall, dist_zero_right] using hz
    rcases lt_or_eq_of_le hn with hlt | heq
    · let C := connectedComponentIn (sphere (0 : ℂ) 1)ᶜ z
      have hU : C ⊆ ball (0 : ℂ) 1 ∪ (closedBall (0 : ℂ) 1)ᶜ := by
        intro w hw
        have hnot : w ∉ sphere (0 : ℂ) 1 := connectedComponentIn_subset _ _ hw
        have hne : ‖w‖ ≠ 1 := fun h => hnot (mem_sphere_zero_iff_norm.mpr h)
        rcases lt_or_gt_of_ne hne with hl | hg
        · exact Or.inl (by simpa [mem_ball, dist_zero_right] using hl)
        · exact Or.inr (by simpa [mem_closedBall, dist_zero_right] using hg)
      have hd : Disjoint (ball (0 : ℂ) 1) (closedBall (0 : ℂ) 1)ᶜ :=
        disjoint_compl_right_iff_subset.mpr ball_subset_closedBall
      have hnot : z ∉ sphere (0 : ℂ) 1 :=
        fun h => (ne_of_lt hlt) (mem_sphere_zero_iff_norm.mp h)
      have hzc : z ∈ C := mem_connectedComponentIn hnot
      have hzb : z ∈ ball (0 : ℂ) 1 := by simpa [mem_ball, dist_zero_right] using hlt
      have hpre : IsPreconnected C := isPreconnected_connectedComponentIn
      have hC : C ⊆ ball (0 : ℂ) 1 :=
        hpre.subset_left_of_subset_union isOpen_ball isClosed_closedBall.isOpen_compl
          hd hU ⟨z, hzc, hzb⟩
      change IsBounded C
      exact isBounded_ball.subset hC
    · exact planarFill_extensive _ (mem_sphere_zero_iff_norm.mpr heq)

/-- Full compact connected carriers can be arbitrarily Hausdorff-close
to a nonfull continuum, even with two fixed antipodal marked points.
The entire open unit disk is absent from every approximant's fill
but present in the limit's fill. The witnesses are genuine circular arcs. -/
theorem full_connected_approx_nonfull_unitSphere (ε : ℝ) (hε : 0 < ε) :
    ∃ A : Set ℂ, IsCompact A ∧ IsConnected A ∧
      Complex.I ∈ A ∧ -Complex.I ∈ A ∧
      A ⊆ sphere (0 : ℂ) 1 ∧ sphere (0 : ℂ) 1 ⊆ thickening ε A ∧
      planarFill A = A ∧ Disjoint (planarFill A) (ball (0 : ℂ) 1) ∧
      ball (0 : ℂ) 1 ⊆ planarFill (sphere (0 : ℂ) 1) := by
  let f : ℝ → ℂ := fun t => Complex.exp ((t : ℂ) * Complex.I)
  have hf : Continuous f := by fun_prop
  let J : Set ℝ := Icc (-Real.pi) Real.pi
  have hJ : IsCompact J := isCompact_Icc
  obtain ⟨η, hη, huc⟩ := Metric.uniformContinuousOn_iff.mp
    (hJ.uniformContinuousOn_of_continuous hf.continuousOn) ε hε
  let d : ℝ := min (η/2) (Real.pi/2)
  have hd : 0 < d := lt_min (by linarith) (by positivity)
  have hdη : d < η := by
    have h : d ≤ η/2 := min_le_left _ _
    linarith
  have hdhalf : d ≤ Real.pi/2 := min_le_right _ _
  have hdπ : d < Real.pi := by linarith [Real.pi_pos]
  let Jd : Set ℝ := Icc (-Real.pi+d) (Real.pi-d)
  let A : Set ℂ := f '' Jd
  have hJsub : Jd ⊆ J := by
    intro t ht
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hAcomp : IsCompact A := isCompact_Icc.image hf
  have hab : -Real.pi+d ≤ Real.pi-d := by linarith
  have hAconn : IsConnected A := (isConnected_Icc hab).image f hf.continuousOn
  have hmark₁ : Complex.I ∈ A := by
    refine ⟨Real.pi/2, ⟨by linarith, by linarith⟩, ?_⟩
    simpa [f] using Complex.exp_pi_div_two_mul_I
  have hmark₂ : -Complex.I ∈ A := by
    refine ⟨-Real.pi/2, ⟨by linarith, by linarith⟩, ?_⟩
    simpa [f] using Complex.exp_neg_pi_div_two_mul_I
  have hAsub : A ⊆ sphere (0 : ℂ) 1 := by
    rintro z ⟨t, _, rfl⟩
    exact mem_sphere_zero_iff_norm.mpr (Complex.norm_exp_ofReal_mul_I t)
  have hmiss : (-1 : ℂ) ∉ A := by
    rintro ⟨t, ht, he⟩
    have htIoc : t ∈ Ioc (-Real.pi) Real.pi :=
      ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have harg : Complex.arg (f t) = t := by
      dsimp [f]
      rw [Complex.exp_mul_I]
      exact Complex.arg_cos_add_sin_mul_I htIoc
    have h := congrArg Complex.arg he
    rw [harg, Complex.arg_neg_one] at h
    linarith [ht.2]
  have hfull : planarFill A = A :=
    planarFill_of_proper_subset_unitSphere A hAsub (-1)
      (by simp [mem_sphere_zero_iff_norm]) hmiss
  have hcover : sphere (0 : ℂ) 1 ⊆ thickening ε A := by
    intro z hz
    obtain ⟨t, ht, he⟩ := Complex.norm_eq_one_iff'.mp (mem_sphere_zero_iff_norm.mp hz)
    have htJ : t ∈ J := ⟨ht.1.le, ht.2⟩
    have hnear : ∃ y ∈ Jd, dist t y ≤ d := by
      by_cases hl : t < -Real.pi+d
      · refine ⟨-Real.pi+d, ⟨le_rfl, hab⟩, ?_⟩
        rw [Real.dist_eq, abs_of_nonpos (by linarith : t-(-Real.pi+d) ≤ 0)]
        linarith [ht.1]
      · by_cases hr : Real.pi-d < t
        · refine ⟨Real.pi-d, ⟨hab, le_rfl⟩, ?_⟩
          rw [Real.dist_eq, abs_of_nonneg (by linarith : 0 ≤ t-(Real.pi-d))]
          linarith [ht.2]
        · exact ⟨t, ⟨le_of_not_gt hl, le_of_not_gt hr⟩, by simpa using hd.le⟩
    obtain ⟨y, hy, hdy⟩ := hnear
    have hdist := huc t htJ y (hJsub hy) (hdy.trans_lt hdη)
    have hft : f t = z := he
    rw [hft] at hdist
    exact mem_thickening_iff.mpr ⟨f y, ⟨y, hy, rfl⟩, hdist⟩
  refine ⟨A, hAcomp, hAconn, hmark₁, hmark₂, hAsub, hcover, hfull, ?_, ?_⟩
  · rw [hfull]
    apply Set.disjoint_left.mpr
    intro z hz hb
    have hn := mem_sphere_zero_iff_norm.mp (hAsub hz)
    have hl : ‖z‖ < 1 := by simpa [mem_ball, dist_zero_right] using hb
    linarith
  · rw [planarFill_unitSphere]
    exact ball_subset_closedBall

end LoopsFormal.ProtectedCarriers

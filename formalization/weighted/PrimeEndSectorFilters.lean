import Mathlib
import SaturatedTelescope

/-!
# Exact cofinality of multisector angular-height traces

The angular space is metric (in particular the external angle circle).
The rectangles refer to the exterior coordinate, not the planar landing
point. Heights are strictly positive. No single-sector assumption is made.
-/

namespace PrimeEndSectorFilters

open Set Metric

variable {X : Type*} [MetricSpace X]

def trace (A : Set X) (H : ℝ) : Set (X × ℝ) :=
  {p | p.1 ∈ A ∧ 0 < p.2 ∧ p.2 ≤ H}

def wedge (θ : X) (ε : ℝ) : Set (X × ℝ) :=
  {p | p.1 ∈ ball θ ε ∧ 0 < p.2 ∧ p.2 < ε}

/-- Both directions of neighborhood-filter cofinality, with the puncture
at height zero retained. -/
def Cofinal (A : ℕ → Set X) (H : ℕ → ℝ) (θ : X) : Prop :=
  (∀ ε > 0, ∃ n, trace (A n) (H n) ⊆ wedge θ ε) ∧
  (∀ n, ∃ ε > 0, wedge θ ε ⊆ trace (A n) (H n))

/-- A nested compact footprint lies in any open neighborhood of its
intersection at a finite stage. -/
theorem compact_footprint_eventually_inside (A : ℕ → Set X)
    (hc : ∀ n, IsCompact (A n)) (ha : Antitone A)
    (V : Set X) (hV : IsOpen V) (hI : (⋂ n, A n) ⊆ V) :
    ∃ n, A n ⊆ V := by
  have hbad : IsCompact (A 0 ∩ Vᶜ) := (hc 0).inter_right hV.isClosed_compl
  have hempty : (A 0 ∩ Vᶜ) ∩ (⋂ n, A n) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact hx.1.2 (hI hx.2)
  have hd : Directed (· ⊇ ·) A := by
    intro i j
    exact ⟨max i j, ha (le_max_left i j), ha (le_max_right i j)⟩
  obtain ⟨n, hn⟩ := hbad.elim_directed_family_closed A
    (fun i => (hc i).isClosed) hempty hd
  refine ⟨n, ?_⟩
  intro x hx
  by_contra hnot
  have hb : x ∈ (A 0 ∩ Vᶜ) ∩ A n :=
    ⟨⟨ha (Nat.zero_le n) hx, hnot⟩, hx⟩
  rw [hn] at hb
  exact hb

/-- Every surviving angle is a genuine exterior cluster angle, and no
other angle is. This uses closed angular footprints and positive heights,
not continuity of a planar landing map. -/
theorem angular_cluster_iff (A : ℕ → Set X) (H : ℕ → ℝ) (θ : X)
    (hc : ∀ n, IsClosed (A n)) (hp : ∀ n, 0 < H n) :
    θ ∈ (⋂ n, A n) ↔
      ∀ n ε, 0 < ε → (trace (A n) (H n) ∩ wedge θ ε).Nonempty := by
  constructor
  · intro h n ε he
    let t := min (H n) ε / 2
    have ht : 0 < t := by dsimp [t]; positivity
    have htH : t ≤ H n := by
      have hh := min_le_left (H n) ε
      dsimp [t] at *
      linarith
    have htε : t < ε := by
      have hh := min_le_right (H n) ε
      dsimp [t] at *
      linarith
    exact ⟨(θ,t), ⟨mem_iInter.mp h n, ht, htH⟩,
      ⟨by simpa [mem_ball] using he, ht, htε⟩⟩
  · intro h
    apply mem_iInter.mpr
    intro n
    by_contra hnot
    obtain ⟨ε, he, hball⟩ := Metric.isOpen_iff.mp (hc n).isOpen_compl θ hnot
    obtain ⟨p, hpA, hpW⟩ := h n ε he
    exact (hball hpW.1) hpA.1

/-- Forward cofinality already forces every surviving angle to equal
the proposed center, whether or not that center is an interior angle. -/
theorem forward_forces_unique_angle (A : ℕ → Set X) (H : ℕ → ℝ) (θ : X)
    (hp : ∀ n, 0 < H n)
    (hf : ∀ ε > 0, ∃ n, trace (A n) (H n) ⊆ wedge θ ε) :
    (⋂ n, A n) ⊆ {θ} := by
  intro x hx
  apply mem_singleton_iff.mpr
  by_contra hne
  obtain ⟨n, hn⟩ := hf (dist x θ) (dist_pos.mpr hne)
  have ht : (x,H n) ∈ trace (A n) (H n) :=
    ⟨mem_iInter.mp hx n, hp n, le_rfl⟩
  have hh : dist x θ < dist x θ := (hn ht).1
  exact (lt_irrefl _ hh)

/-- Reverse cofinality at one stage is exactly the ordinary angular
interior condition, including when the footprint has many components. -/
theorem reverse_stage_iff (A : Set X) (H : ℝ) (θ : X) (hp : 0 < H) :
    (∃ ε > 0, wedge θ ε ⊆ trace A H) ↔
    (∃ δ > 0, ball θ δ ⊆ A) := by
  constructor
  · rintro ⟨ε, he, hs⟩
    refine ⟨ε, he, ?_⟩
    intro x hx
    have hw : (x,ε/2) ∈ wedge θ ε := ⟨hx, by linarith, by linarith⟩
    exact (hs hw).1
  · rintro ⟨δ, hd, hs⟩
    refine ⟨min δ H, lt_min hd hp, ?_⟩
    intro p h
    refine ⟨hs ?_, h.2.1, ?_⟩
    · exact lt_of_lt_of_le h.1 (min_le_left _ _)
    · exact (lt_of_lt_of_le h.2.2 (min_le_right _ _)).le

/-- The exact criterion for the entire exterior trace to be cofinal at
an ordinary prime-end coordinate: one surviving angle and interiority
at every finite depth. This is independent of planar pointness. -/
theorem whole_trace_cofinal_iff (A : ℕ → Set X) (H : ℕ → ℝ) (θ : X)
    (hc : ∀ n, IsCompact (A n)) (ha : Antitone A)
    (hp : ∀ n, 0 < H n) (hh : Antitone H)
    (hsmall : ∀ ε > 0, ∃ n, H n < ε)
    (hθ : θ ∈ (⋂ n, A n)) :
    Cofinal A H θ ↔
      (⋂ n, A n) = {θ} ∧ (∀ n, ∃ δ > 0, ball θ δ ⊆ A n) := by
  constructor
  · intro h
    refine ⟨Subset.antisymm (forward_forces_unique_angle A H θ hp h.1) ?_, ?_⟩
    · intro x hx
      rw [mem_singleton_iff.mp hx]
      exact hθ
    · intro n
      exact (reverse_stage_iff (A n) (H n) θ (hp n)).mp (h.2 n)
  · rintro ⟨hI, hint⟩
    constructor
    · intro ε he
      have hsub : (⋂ n, A n) ⊆ ball θ ε := by
        rw [hI]
        intro x hx
        rw [mem_singleton_iff.mp hx]
        simpa [mem_ball] using he
      obtain ⟨i, hi⟩ := compact_footprint_eventually_inside A hc ha
        (ball θ ε) isOpen_ball hsub
      obtain ⟨j, hj⟩ := hsmall ε he
      refine ⟨max i j, ?_⟩
      intro p h
      exact ⟨hi (ha (le_max_left i j) h.1), h.2.1,
        lt_of_le_of_lt (h.2.2.trans (hh (le_max_right i j))) hj⟩
    · intro n
      exact (reverse_stage_iff (A n) (H n) θ (hp n)).mpr (hint n)

/-- Two retained external angles rule out whole-trace cofinality at
every candidate center, even if their planar impressions coincide. -/
theorem two_angles_obstruct (A : ℕ → Set X) (H : ℕ → ℝ)
    (hp : ∀ n, 0 < H n) {a b : X} (hne : a ≠ b)
    (ha : a ∈ ⋂ n, A n) (hb : b ∈ ⋂ n, A n) :
    ∀ θ, ¬ Cofinal A H θ := by
  intro θ h
  have hs := forward_forces_unique_angle A H θ hp h.1
  exact hne ((mem_singleton_iff.mp (hs ha)).trans (mem_singleton_iff.mp (hs hb)).symm)

/-- In a real angular lift the ordinary interior condition for a closed
sector is strict on both ends, including a degenerate sector. -/
theorem interval_interior_iff (l r θ : ℝ) :
    (∃ δ > 0, ball θ δ ⊆ Icc l r) ↔ l < θ ∧ θ < r := by
  constructor
  · rintro ⟨δ, hd, hs⟩
    have hminus : θ - δ/2 ∈ ball θ δ := by
      rw [mem_ball, Real.dist_eq]
      have he : θ - δ/2 - θ = -(δ/2) := by ring
      rw [he, abs_neg, abs_of_pos (by linarith : 0 < δ/2)]
      linarith
    have hplus : θ + δ/2 ∈ ball θ δ := by
      rw [mem_ball, Real.dist_eq]
      have he : θ + δ/2 - θ = δ/2 := by ring
      rw [he, abs_of_pos (by linarith : 0 < δ/2)]
      linarith
    have hl := (hs hminus).1
    have hr := (hs hplus).2
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨hl, hr⟩
    refine ⟨min (θ-l) (r-θ), lt_min (by linarith) (by linarith), ?_⟩
    intro x hx
    rw [mem_ball, Real.dist_eq, abs_lt] at hx
    have hleft := min_le_left (θ-l) (r-θ)
    have hright := min_le_right (θ-l) (r-θ)
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩

/-- Endpoint failure occurs at the first offending finite level; further
physical shrinking cannot repair the missing angular side. -/
theorem interval_endpoint_obstruct (l r H : ℕ → ℝ) (θ : ℝ)
    (hp : ∀ n, 0 < H n) (n : ℕ) (he : θ = l n ∨ θ = r n) :
    ¬ Cofinal (fun k => Icc (l k) (r k)) H θ := by
  intro h
  have hs := (reverse_stage_iff (Icc (l n) (r n)) (H n) θ (hp n)).mp (h.2 n)
  have hi := (interval_interior_iff (l n) (r n) θ).mp hs
  rcases he with he | he <;> linarith [hi.1, hi.2]

/-- A connected subset of two complex points cannot contain both unless
they coincide. This is used below rather than assuming an inverse branch
at an endpoint. -/
theorem connected_two_point_set (S : Set ℂ) (a b : ℂ)
    (hc : IsPreconnected S) (hs : S ⊆ ({a,b} : Set ℂ))
    (ha : a ∈ S) (hb : b ∈ S) : a = b := by
  by_contra hne
  have hcover : S ⊆ ({a} : Set ℂ)ᶜ ∪ ({b} : Set ℂ)ᶜ := by
    intro x hx
    by_cases he : x = a
    · exact Or.inr (by simpa [he] using hne)
    · exact Or.inl (by simpa using he)
  obtain ⟨x, hx, hxa, hxb⟩ := hc _ _ isClosed_singleton.isOpen_compl
    isClosed_singleton.isOpen_compl hcover
    ⟨b, hb, by simpa using Ne.symm hne⟩
    ⟨a, ha, by simpa using hne⟩
  have hmem : x = a ∨ x = b := by simpa using hs hx
  rcases hmem with he | he
  · exact hxa (mem_singleton_iff.mpr he)
  · exact hxb (mem_singleton_iff.mpr he)

/-- Every preconnected set on which the actual quadratic iterate is
constant is a singleton if nonempty. This needs no landing theorem,
regular boundary, inverse-branch choice, or local connectivity. -/
theorem quadratic_iterate_connected_fiber (c : ℂ) (n : ℕ)
    (S : Set ℂ) (hc : IsPreconnected S) (v : ℂ)
    (hconst : ∀ z ∈ S, QuadraticEscape.orbit c n z = v)
    {x y : ℂ} (hx : x ∈ S) (hy : y ∈ S) : x = y := by
  induction n generalizing v with
  | zero =>
      exact (hconst x hx).trans (hconst y hy).symm
  | succ n ih =>
      let f := QuadraticEscape.orbit c n
      have hpre : IsPreconnected (f '' S) :=
        hc.image f (LoopsSaturatedTelescope.quadratic_orbit_continuous c n).continuousOn
      have hsub : f '' S ⊆ ({f x, -(f x)} : Set ℂ) := by
        rintro w ⟨z, hz, rfl⟩
        have hzv : (f z)^2 + c = v := hconst z hz
        have hxv : (f x)^2 + c = v := hconst x hx
        have hsq : (f z)^2 = (f x)^2 := by linear_combination hzv - hxv
        have hmul : (f z - f x) * (f z + f x) = 0 := by
          calc
            _ = (f z)^2 - (f x)^2 := by ring
            _ = 0 := sub_eq_zero.mpr hsq
        rcases mul_eq_zero.mp hmul with h | h
        · exact Or.inl (sub_eq_zero.mp h)
        · exact Or.inr (mem_singleton_iff.mpr (eq_neg_of_add_eq_zero_left h))
      have hall : ∀ z ∈ S, f z = f x := by
        intro z hz
        have hzmem := hsub ⟨z, hz, rfl⟩
        have hcases : f z = f x ∨ f z = -(f x) := by simpa using hzmem
        rcases hcases with h | h
        · exact h
        · have hneg : -(f x) ∈ f '' S := ⟨z, hz, h⟩
          have he := connected_two_point_set (f '' S) (f x) (-(f x))
            hpre hsub ⟨x, hx, rfl⟩ hneg
          exact h.trans he.symm
      exact ih (f x) hall

/-- An endpoint with two connected side impressions and a common landing
point has both impressions equal to that point once each side maps to a
singleton by a finite physical iterate. Distinct side prime ends are
not identified by this conclusion. -/
theorem endpoint_impressions_singleton (c : ℂ) (n : ℕ)
    (L R : Set ℂ) (z : ℂ) (hL : IsPreconnected L) (hR : IsPreconnected R)
    (hzL : z ∈ L) (hzR : z ∈ R)
    (hmapL : ∀ w ∈ L, QuadraticEscape.orbit c n w = QuadraticEscape.orbit c n z)
    (hmapR : ∀ w ∈ R, QuadraticEscape.orbit c n w = QuadraticEscape.orbit c n z) :
    L = {z} ∧ R = {z} := by
  constructor
  · apply Subset.antisymm
    · intro w hw
      exact mem_singleton_iff.mpr (quadratic_iterate_connected_fiber c n L hL _ hmapL hw hzL)
    · intro w hw
      rw [mem_singleton_iff.mp hw]
      exact hzL
  · apply Subset.antisymm
    · intro w hw
      exact mem_singleton_iff.mpr (quadratic_iterate_connected_fiber c n R hR _ hmapR hw hzR)
    · intro w hw
      rw [mem_singleton_iff.mp hw]
      exact hzR

end PrimeEndSectorFilters

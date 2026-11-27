import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Topology.Separation.Connected
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Continuous rigidity of complex power fibers

On a punctured round disk a continuous map preserving every fiber of a
positive power is one fixed root-of-unity rotation. Continuity at the
central point is unnecessary: the central fiber alone forces its value.
For positive even powers this also excludes a continuous inverse section
on an entire punctured target disk.
-/

namespace LoopsPowerMapRigidity

open Set Metric Polynomial

/-- Removing the center of a complex round disk preserves preconnectedness.
The nonpositive-radius cases are included as empty sets. -/
theorem punctured_ball_preconnected (r : ℝ) :
    IsPreconnected (ball (0 : ℂ) r \ {0}) := by
  by_cases hr : 0 < r
  · let R : Set ℂ := ball 0 r ∩ {z | 0 < z.re}
    let T : Set ℂ := ball 0 r ∩ {z | 0 < z.im}
    let L : Set ℂ := ball 0 r ∩ {z | z.re < 0}
    let B : Set ℂ := ball 0 r ∩ {z | z.im < 0}
    have hR : IsPreconnected R :=
      ((convex_ball (0 : ℂ) r).inter (convex_halfSpace_re_gt 0)).isPreconnected
    have hT : IsPreconnected T :=
      ((convex_ball (0 : ℂ) r).inter (convex_halfSpace_im_gt 0)).isPreconnected
    have hL : IsPreconnected L :=
      ((convex_ball (0 : ℂ) r).inter (convex_halfSpace_re_lt 0)).isPreconnected
    have hB : IsPreconnected B :=
      ((convex_ball (0 : ℂ) r).inter (convex_halfSpace_im_lt 0)).isPreconnected
    let a : ℂ := (r / 4 : ℝ)
    have ha : ‖a‖ = r / 4 := by
      simp only [a, Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_pos (by linarith : 0 < r / 4)]
    have hpp : a + a * Complex.I ∈ ball (0 : ℂ) r := by
      rw [mem_ball, dist_zero_right]
      calc
        ‖a + a * Complex.I‖ ≤ ‖a‖ + ‖a * Complex.I‖ := norm_add_le _ _
        _ = r / 2 := by rw [norm_mul, Complex.norm_I, mul_one, ha]; ring
        _ < r := by linarith
    have hmp : -a + a * Complex.I ∈ ball (0 : ℂ) r := by
      rw [mem_ball, dist_zero_right]
      calc
        ‖-a + a * Complex.I‖ ≤ ‖-a‖ + ‖a * Complex.I‖ := norm_add_le _ _
        _ = r / 2 := by rw [norm_neg, norm_mul, Complex.norm_I, mul_one, ha]; ring
        _ < r := by linarith
    have hmm : -a - a * Complex.I ∈ ball (0 : ℂ) r := by
      rw [mem_ball, dist_zero_right]
      calc
        ‖-a - a * Complex.I‖ ≤ ‖-a‖ + ‖a * Complex.I‖ := norm_sub_le _ _
        _ = r / 2 := by rw [norm_neg, norm_mul, Complex.norm_I, mul_one, ha]; ring
        _ < r := by linarith
    have hRT : (R ∩ T).Nonempty := by
      refine ⟨a + a * Complex.I, ⟨hpp, ?_⟩, ⟨hpp, ?_⟩⟩ <;>
        simp [a] <;> linarith
    have hRTL : ((R ∪ T) ∩ L).Nonempty := by
      refine ⟨-a + a * Complex.I, Or.inr ⟨hmp, ?_⟩, ⟨hmp, ?_⟩⟩ <;>
        simp [a] <;> linarith
    have hRTLB : (((R ∪ T) ∪ L) ∩ B).Nonempty := by
      refine ⟨-a - a * Complex.I, Or.inr ⟨hmm, ?_⟩, ⟨hmm, ?_⟩⟩ <;>
        simp [a] <;> linarith
    have hconn := IsPreconnected.union' hRTLB
      (IsPreconnected.union' hRTL (IsPreconnected.union' hRT hR hT) hL) hB
    have heq : ((R ∪ T) ∪ L) ∪ B = ball (0 : ℂ) r \ {0} := by
      ext z
      simp only [R, T, L, B, mem_union, mem_inter_iff, mem_setOf_eq,
        mem_sdiff, mem_singleton_iff]
      constructor
      · rintro (((⟨hz, h⟩ | ⟨hz, h⟩) | ⟨hz, h⟩) | ⟨hz, h⟩) <;>
          exact ⟨hz, by intro he; simp [he] at h⟩
      · rintro ⟨hz, hne⟩
        by_cases h₁ : 0 < z.re
        · exact Or.inl (Or.inl (Or.inl ⟨hz, h₁⟩))
        by_cases h₂ : 0 < z.im
        · exact Or.inl (Or.inl (Or.inr ⟨hz, h₂⟩))
        by_cases h₃ : z.re < 0
        · exact Or.inl (Or.inr ⟨hz, h₃⟩)
        by_cases h₄ : z.im < 0
        · exact Or.inr ⟨hz, h₄⟩
        exact (hne (Complex.ext (by simp only [Complex.zero_re]; linarith)
          (by simp only [Complex.zero_im]; linarith))).elim
    rwa [heq] at hconn
  · have he : ball (0 : ℂ) r = ∅ := ball_eq_empty.mpr (le_of_not_gt hr)
    rw [he, empty_sdiff]
    exact isPreconnected_empty

/-- Continuity only on the punctured disk already forces a single root
rotation on the entire disk whenever a positive power is preserved. -/
theorem power_preserving_rigidity (m : ℕ) (hm : 0 < m)
    (r : ℝ) (hr : 0 < r) (g : ℂ → ℂ)
    (hg : ContinuousOn g (ball (0 : ℂ) r \ {0}))
    (hpow : ∀ z ∈ ball (0 : ℂ) r, (g z)^m = z^m) :
    ∃ ζ : ℂ, ζ^m = 1 ∧ ∀ z ∈ ball (0 : ℂ) r, g z = ζ*z := by
  let D : Set ℂ := ball 0 r \ {0}
  let q : ℂ → ℂ := fun z => g z / z
  have hqcont : ContinuousOn q D :=
    hg.div continuousOn_id (fun z hz => hz.2)
  have hqpow (z : ℂ) (hz : z ∈ D) : (q z)^m = 1 := by
    dsimp [q]
    rw [div_pow, hpow z hz.1, div_self (pow_ne_zero m hz.2)]
  have hsub : q '' D ⊆ (↑(nthRootsFinset m (1 : ℂ)) : Set ℂ) := by
    rintro _ ⟨z, hz, rfl⟩
    exact (mem_nthRootsFinset hm _).mpr (hqpow z hz)
  have hfinite : (q '' D).Finite := (Finset.finite_toSet _).subset hsub
  have hconn : IsPreconnected (q '' D) :=
    (punctured_ball_preconnected r).image q hqcont
  have hsingle : (q '' D).Subsingleton := Set.not_nontrivial_iff.mp
    (fun h => (hconn.infinite_of_nontrivial h) hfinite)
  let w : ℂ := (r / 2 : ℝ)
  have hw : w ∈ D := by
    constructor
    · rw [mem_ball, dist_zero_right]
      simp only [w, Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_pos (by linarith : 0 < r / 2)]
      linarith
    · change ((r / 2 : ℝ) : ℂ) ≠ 0
      exact_mod_cast (ne_of_gt (by linarith : 0 < r / 2))
  refine ⟨q w, hqpow w hw, ?_⟩
  intro z hz
  by_cases hz0 : z = 0
  · subst z
    have hzero : g 0 = 0 := by
      by_contra hne
      have hp := hpow 0 (mem_ball_self hr)
      rw [zero_pow (Nat.ne_zero_of_lt hm)] at hp
      exact pow_ne_zero m hne hp
    simp only [hzero, mul_zero]
  · have he : q z = q w := hsingle ⟨z, ⟨hz, hz0⟩, rfl⟩ ⟨w, hw, rfl⟩
    exact (div_eq_iff hz0).mp he

/-- A positive even complex power has no continuous right inverse on
an entire punctured round disk. The section is not required to stay
in a prescribed source neighborhood. -/
theorem even_power_no_continuous_section (m : ℕ) (hm : 0 < m)
    (heven : Even m) (R : ℝ) (hR : 0 < R) :
    ¬ ∃ s : ℂ → ℂ,
      ContinuousOn s (ball (0 : ℂ) R \ {0}) ∧
      ∀ w ∈ ball (0 : ℂ) R \ {0}, (s w)^m = w := by
  rintro ⟨s, hs, hsec⟩
  let r : ℝ := min 1 R / 2
  have hr : 0 < r := by dsimp [r]; positivity
  have hr1 : r < 1 := by dsimp [r]; linarith [min_le_left (1 : ℝ) R]
  have hrR : r < R := by dsimp [r]; linarith [min_le_right (1 : ℝ) R]
  have hpowmap : MapsTo (fun z : ℂ => z^m)
      (ball (0 : ℂ) r \ {0}) (ball (0 : ℂ) R \ {0}) := by
    intro z hz
    have hzn : ‖z‖ < r := by simpa only [mem_ball, dist_zero_right] using hz.1
    have hle : ‖z‖^m ≤ ‖z‖ := pow_le_of_le_one (norm_nonneg z)
      (hzn.trans hr1).le (Nat.ne_zero_of_lt hm)
    exact ⟨by simpa only [mem_ball, dist_zero_right, norm_pow] using
      hle.trans_lt (hzn.trans hrR), pow_ne_zero m hz.2⟩
  let g : ℂ → ℂ := fun z => if z = 0 then 0 else s (z^m)
  have hg : ContinuousOn g (ball (0 : ℂ) r \ {0}) := by
    apply (hs.comp (continuous_id.pow m).continuousOn hpowmap).congr
    intro z hz
    change (if z = 0 then 0 else s (z^m)) = s (z^m)
    exact if_neg (show z ≠ 0 from hz.2)
  have hpow : ∀ z ∈ ball (0 : ℂ) r, (g z)^m = z^m := by
    intro z hz
    by_cases hz0 : z = 0
    · subst z
      simp only [g, if_pos rfl]
    · simp only [g, if_neg hz0]
      exact hsec _ (hpowmap ⟨hz, hz0⟩)
  obtain ⟨ζ, hζ, hrot⟩ := power_preserving_rigidity m hm r hr g hg hpow
  let z : ℂ := (r / 2 : ℝ)
  have hz0 : z ≠ 0 := by
    dsimp [z]
    exact_mod_cast (ne_of_gt (by linarith : 0 < r / 2))
  have hz : z ∈ ball (0 : ℂ) r := by
    rw [mem_ball, dist_zero_right]
    simp only [z, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_pos (by linarith : 0 < r / 2)]
    linarith
  have hnz : -z ∈ ball (0 : ℂ) r := by
    simpa only [mem_ball, dist_zero_right, norm_neg] using hz
  have hsame : g (-z) = g z := by
    simp only [g, if_neg hz0, if_neg (neg_ne_zero.mpr hz0), heven.neg_pow]
  rw [hrot (-z) hnz, hrot z hz, mul_neg] at hsame
  have hzero : ζ*z = 0 := by linear_combination -hsame / 2
  have hζ0 : ζ ≠ 0 := by
    intro he
    rw [he, zero_pow (Nat.ne_zero_of_lt hm)] at hζ
    exact zero_ne_one hζ
  exact mul_ne_zero hζ0 hz0 hzero

end LoopsPowerMapRigidity

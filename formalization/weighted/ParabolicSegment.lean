import Mathlib.Analysis.Complex.Convex
import Mathlib.Tactic.Linarith

/-! The closed real shooting interval, embedded as a full plane continuum. -/
namespace LoopsParabolic
open Set
noncomputable section

def realSegment (e : ℝ) : Set ℂ := (fun x : ℝ => (x : ℂ)) '' Icc (-e) e

theorem mem_realSegment_iff {z : ℂ} {e : ℝ} :
    z ∈ realSegment e ↔ z.im = 0 ∧ z.re ∈ Icc (-e) e := by
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact ⟨rfl,hx⟩
  · rintro ⟨hi,hr⟩
    exact ⟨z.re,hr,Complex.ext rfl hi.symm⟩

theorem realSegment_compact (e : ℝ) : IsCompact (realSegment e) :=
  isCompact_Icc.image Complex.continuous_ofReal

theorem realSegment_connected {e : ℝ} (he : 0 ≤ e) : IsConnected (realSegment e) :=
  (isConnected_Icc (neg_le_self he)).image _ Complex.continuous_ofReal.continuousOn

/-- The four open half-planes surrounding the interval form a connected union. -/
theorem realSegment_compl_connected (e : ℝ) : IsConnected (realSegment e)ᶜ := by
  let U := { z : ℂ | 0 < z.im }
  let R := { z : ℂ | e < z.re }
  let D := { z : ℂ | z.im < 0 }
  let L := { z : ℂ | z.re < -e }
  have cover : (realSegment e)ᶜ = ((U ∪ R) ∪ D) ∪ L := by
    ext z
    change z ∉ realSegment e ↔ (((0 < z.im ∨ e < z.re) ∨ z.im < 0) ∨ z.re < -e)
    rw [mem_realSegment_iff]
    constructor
    · intro h
      by_contra! hbad
      exact h ⟨le_antisymm hbad.1.1.1 hbad.1.2,hbad.2,hbad.1.1.2⟩
    · rintro (((h|h)|h)|h) ⟨hi,hl,hh⟩ <;> linarith
  have UR : IsPreconnected (U ∪ R) :=
    (convex_halfSpace_im_gt 0).isPreconnected.union (⟨e+1,1⟩ : ℂ)
      (by change (0:ℝ)<1; norm_num) (by change e<e+1; linarith)
      (convex_halfSpace_re_gt e).isPreconnected
  have URD : IsPreconnected ((U ∪ R) ∪ D) :=
    UR.union (⟨e+1,-1⟩ : ℂ) (Or.inr (by change e<e+1; linarith))
      (by change (-1:ℝ)<0; norm_num) (convex_halfSpace_im_lt 0).isPreconnected
  rw [cover]
  refine ⟨⟨Complex.I,Or.inl (Or.inl (Or.inl (by change (0:ℝ)<1; norm_num)))⟩, ?_⟩
  exact URD.union (⟨-e-1,-1⟩ : ℂ) (Or.inr (by change (-1:ℝ)<0; norm_num))
    (by change -e-1 < -e; linarith) (convex_halfSpace_re_lt (-e)).isPreconnected

end
end LoopsParabolic

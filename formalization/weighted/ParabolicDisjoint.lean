import ParabolicPhaseBands
import ParabolicBranches

/-! The physical phases of a complete parabolic passage have mutually
disjoint real images. Distinct phase bands separate most pairs. Returns
with the same small phase are separated by their entrance magnitudes. -/
namespace LoopsParabolic
open Set Function
noncomputable section

private def phaseBand (k i : ℕ) : Fin 6 :=
  ⟨i%3 + (if i/3 ≤ k then 0 else 3), by split <;> omega⟩

private theorem split_iterate (f : ℝ → ℝ) (i : ℕ) (x : ℝ) :
    f^[i] x = f^[i%3] (f^[3*(i/3)] x) := by
  rw [←Function.iterate_add_apply]
  congr 2
  omega

private theorem phase_band_mem {t : ℝ} {k i : ℕ} {x : ℝ}
    (ht : t ∈ Icc 0 (1/100:ℝ)) (hi : i < 3*(k+2))
    (hsmall : ∀ j ≤ k, |(quad (-7/4+t))^[3*j] x| ≤ cap)
    (hexit : (quad (-7/4+t))^[3*(k+1)] x ∈ band 3)
    (hreturn : |(quad (-7/4+t))^[3*(k+2)] x| ≤ 1/10) :
    (quad (-7/4+t))^[i] x ∈ band (phaseBand k i) := by
  let f := quad (-7/4+t)
  change f^[i] x ∈ _
  rw [split_iterate f i x]
  by_cases small : i/3 ≤ k
  · have h := small_phase_bands ht (hsmall (i/3) small)
    rcases (show i%3=0 ∨ i%3=1 ∨ i%3=2 by omega) with r | r | r
    · simpa [phaseBand,small,r] using h.1
    · simpa [phaseBand,small,r] using h.2.1
    · simpa [phaseBand,small,r] using h.2.2
  · have last : i/3=k+1 := by omega
    have back : |f^[3] (f^[3*(k+1)] x)| ≤ 1/10 := by
      rw [←Function.iterate_add_apply, show 3 + 3*(k+1)=3*(k+2) by omega]
      exact hreturn
    have h := exit_phase_bands ht hexit back
    rcases (show i%3=0 ∨ i%3=1 ∨ i%3=2 by omega) with r | r | r
    · simpa [phaseBand,small,r,last] using h.1
    · simpa [phaseBand,small,r,last] using h.2.1
    · simpa [phaseBand,small,r,last] using h.2.2

/-- A physical collision would give equal phase labels. Equal labels at
different times force a common residual phase on different small blocks.
The residual iterates distinguish the absolute values of these blocks. -/
private theorem images_disjoint_of_blocks {t : ℝ} {k : ℕ} {I : Set ℝ}
    (ht : t ∈ Icc 0 (1/100:ℝ))
    (hsmall : ∀ x ∈ I, ∀ j ≤ k, |(quad (-7/4+t))^[3*j] x| ≤ cap)
    (hexit : ∀ x ∈ I, (quad (-7/4+t))^[3*(k+1)] x ∈ band 3)
    (hreturn : ∀ x ∈ I, |(quad (-7/4+t))^[3*(k+2)] x| ≤ 1/10)
    (hsep : ∀ x ∈ I, ∀ y ∈ I, ∀ a b : ℕ, a<b → b≤k →
      |(quad (-7/4+t))^[3*a] x| < |(quad (-7/4+t))^[3*b] y|)
    {i j : ℕ} (hij : i<j) (hj : j<3*(k+2)) :
    Disjoint ((quad (-7/4+t))^[i] '' I) ((quad (-7/4+t))^[j] '' I) := by
  let f := quad (-7/4+t)
  apply Set.disjoint_left.mpr
  rintro z ⟨x,hx,rfl⟩ ⟨y,hy,equal⟩
  have ix := phase_band_mem ht (lt_trans hij hj) (hsmall x hx) (hexit x hx) (hreturn x hx)
  have jy := phase_band_mem ht hj (hsmall y hy) (hexit y hy) (hreturn y hy)
  have eqb : phaseBand k i = phaseBand k j := by
    by_contra ne
    exact Set.disjoint_left.mp (band_disjoint ne) ix (equal ▸ jy)
  have eqv := congrArg Fin.val eqb
  change i%3+(if i/3≤k then 0 else 3)=j%3+(if j/3≤k then 0 else 3) at eqv
  have ar : i%3=j%3 ∧ i/3<j/3 ∧ j/3≤k := by split at eqv <;> split at eqv <;> omega
  have sep := hsep x hx y hy (i/3) (j/3) ar.2.1 ar.2.2
  change f^[j] y=f^[i] x at equal
  rw [split_iterate f j y,split_iterate f i x,ar.1] at equal
  have same := small_phase_abs_injective ht (hsmall y hy _ ar.2.2)
    (hsmall x hx _ (le_trans ar.2.1.le ar.2.2)) (r:=j%3) (by omega) equal
  exact (ne_of_lt sep) same.symm

/-- All p physical phases of the real restrictive interval are pairwise disjoint,
including their endpoints, for p = 3(k+2). -/
theorem phase_images_disjoint {t e : ℝ} {k : ℕ} (hs : Shot k t e)
    {i j : ℕ} (hij : i<j) (hj : j<3*(k+2)) :
    Disjoint ((quad (-7/4+t))^[i] '' Icc (-e) e)
      ((quad (-7/4+t))^[j] '' Icc (-e) e) := by
  apply images_disjoint_of_blocks ⟨hs.t_pos.le,hs.t_small⟩ _ _ _ _ hij hj
  · exact fun _ hx _ hj => block_small hs hx hj
  · exact fun _ hx => block_exit hs hx
  · intro x hx
    exact (abs_le.mpr (return_mem hs hx)).trans hs.e_small
  · intro x hx y hy a b hab hb
    rw [block_abs hs hx (by omega),block_abs hs hy (by omega)]
    exact block_interleave hs hx hy hab (by omega)

/-- Every point of the real interval has this same first positive return time. -/
theorem first_return_on_interval {t e x : ℝ} {k : ℕ} (hs : Shot k t e)
    (hx : x ∈ Icc (-e) e) :
    (quad (-7/4+t))^[3*(k+2)] x ∈ Icc (-e) e ∧
    ∀ j : ℕ, 0<j → j<3*(k+2) → (quad (-7/4+t))^[j] x ∉ Icc (-e) e := by
  refine ⟨return_mem hs hx, ?_⟩
  intro j hj hlt hit
  exact Set.disjoint_left.mp (phase_images_disjoint hs hj hlt)
    ⟨_,hit,rfl⟩ ⟨x,hx,rfl⟩

#print axioms phase_images_disjoint
#print axioms first_return_on_interval

end
end LoopsParabolic

import QuadraticEscapeFullness

/-!
# Two actual inverse sheets below the critical escape height

The compact target sublevel need not be connected or locally connected.
Its connected complement supplies a continuous logarithm after translation
by the critical value. The resulting two square-root branches give a
homeomorphism, and the second coordinate is the actual quadratic image.
-/

namespace LoopsQuadraticEscapeTree

open Set QuadraticEscape LoopsQuadraticEscapeFullness
open LoopsFormal.ProtectedCarriers

set_option maxHeartbeats 1000000

/-- The closed sublevel of the genuine quadratic escape potential. -/
def sublevel (c : ℂ) (t : ℝ) : Set ℂ := {z : ℂ | escape c z ≤ t}

private theorem sublevel_square_root (c : ℂ) (t : ℝ)
    (ht : 0 ≤ t) (hcrit : t < escape c 0) :
    ∃ r : sublevel c (2*t) → ℂ, Continuous r ∧
      (∀ w, r w ^ 2 + c = (w : ℂ)) ∧ (∀ w, r w ≠ 0) := by
  let S : Set ℂ := {z : ℂ | escape c (z+c) ≤ 2*t}
  have hTc : IsCompact (sublevel c (2*t)) :=
    quadratic_escape_sublevel_compact c (2*t) (by positivity)
  have hSeq : S = (fun w : ℂ => w-c) '' sublevel c (2*t) := by
    ext z
    constructor
    · intro hz
      exact ⟨z+c, hz, by ring⟩
    · rintro ⟨w, hw, rfl⟩
      change escape c (w-c+c) ≤ 2*t
      simpa only [sublevel, mem_setOf_eq, sub_add_cancel] using hw
  have hSc : IsCompact S := by
    rw [hSeq]
    exact hTc.image (continuous_id.sub continuous_const)
  have hSfull : planarFill S = S :=
    escape_pair_sublevel_full (fun _ => c) (fun z => z+c)
      (differentiable_const c) (differentiable_id.add_const c) (2*t)
  have hScompl : IsConnected Sᶜ := by
    obtain ⟨a, ha, _, he, _⟩ := planarFill_exterior hSc.isBounded
    rw [hSfull] at he
    rw [he]
    exact isConnected_connectedComponentIn_iff.mpr ha
  have hzero : (0 : ℂ) ∉ S := by
    intro h
    change escape c (0+c) ≤ 2*t at h
    simp only [zero_add] at h
    have he : escape c c = 2*escape c 0 := by
      simpa using escape_step c 0
    linarith
  obtain ⟨L, hLc, hL⟩ := compact_connected_complement_log S hSc hScompl hzero
  let shift : sublevel c (2*t) → S := fun w =>
    ⟨(w : ℂ)-c, by
      change escape c ((w : ℂ)-c+c) ≤ 2*t
      simpa only [sublevel, mem_setOf_eq, sub_add_cancel] using w.property⟩
  have hshift : Continuous shift :=
    ((continuous_subtype_val : Continuous
      (Subtype.val : sublevel c (2*t) → ℂ)).sub continuous_const).subtype_mk _
  let r : sublevel c (2*t) → ℂ := fun w => Complex.exp (L (shift w) / 2)
  have hrc : Continuous r :=
    Complex.continuous_exp.comp ((hLc.comp hshift).div_const 2)
  have hrsq (w : sublevel c (2*t)) : r w ^ 2 + c = (w : ℂ) := by
    have hs : r w ^ 2 = (w : ℂ)-c := by
      calc
        r w ^ 2 = Complex.exp (L (shift w)) := by
          dsimp [r]
          rw [pow_two, ← Complex.exp_add]
          congr 1
          ring
        _ = (w : ℂ)-c := hL (shift w)
    rw [hs, sub_add_cancel]
  exact ⟨r, hrc, hrsq, fun w => Complex.exp_ne_zero _⟩

/-- Every subcritical nonnegative escape sublevel is exactly two
topological copies of the doubled-height sublevel. The projection to
the second factor is the actual map `z ↦ z²+c`, with no supplied
inverse branch, Jordan boundary, or connectedness hypothesis. -/
theorem sublevel_split (c : ℂ) (t : ℝ)
    (ht : 0 ≤ t) (hcrit : t < escape c 0) :
    ∃ e : sublevel c t ≃ₜ (Fin 2 × sublevel c (2*t)),
      ∀ z, ((e z).2 : ℂ) = (z : ℂ)^2+c := by
  classical
  obtain ⟨r, hrc, hrsq, hrne⟩ := sublevel_square_root c t ht hcrit
  let B : (Fin 2 × sublevel c (2*t)) → ℂ :=
    fun p => if p.1 = 0 then r p.2 else -(r p.2)
  have hBq (p : Fin 2 × sublevel c (2*t)) : B p ^ 2 + c = (p.2 : ℂ) := by
    dsimp [B]
    split_ifs
    · exact hrsq p.2
    · calc
        (-(r p.2)) ^ 2 + c = r p.2 ^ 2 + c := by ring
        _ = (p.2 : ℂ) := hrsq p.2
  have hBmem (p : Fin 2 × sublevel c (2*t)) : B p ∈ sublevel c t := by
    have he := escape_step c (B p)
    rw [hBq] at he
    have hp := p.2.property
    change escape c (p.2 : ℂ) ≤ 2*t at hp
    change escape c (B p) ≤ t
    linarith
  let b : (Fin 2 × sublevel c (2*t)) → sublevel c t :=
    fun p => ⟨B p, hBmem p⟩
  have hBc : Continuous B := by
    apply continuous_prod_of_discrete_left.mpr
    intro i
    by_cases hi : i = 0
    · have hf : (fun w : sublevel c (2*t) => B (i,w)) = r := by
        funext w
        exact if_pos hi
      rw [hf]
      exact hrc
    · have hf : (fun w : sublevel c (2*t) => B (i,w)) =
          (fun w => -(r w)) := by
        funext w
        exact if_neg hi
      rw [hf]
      fun_prop
  have hbc : Continuous b := hBc.subtype_mk _
  have hbq (p : Fin 2 × sublevel c (2*t)) :
      (b p : ℂ)^2+c = (p.2 : ℂ) := hBq p
  have hbi : Function.Injective b := by
    rintro ⟨i, w⟩ ⟨j, v⟩ h
    have hwv : w = v := by
      apply Subtype.ext
      calc
        (w : ℂ) = (b (i,w) : ℂ)^2+c := (hbq (i,w)).symm
        _ = (b (j,v) : ℂ)^2+c := by rw [h]
        _ = (v : ℂ) := hbq (j,v)
    subst v
    have he : B (i,w) = B (j,w) := congrArg Subtype.val h
    have hij : i = j := by
      fin_cases i <;> fin_cases j
      · rfl
      · exfalso
        apply hrne w
        have he' : r w = -(r w) := by simpa [B] using he
        linear_combination (1 / 2 : ℂ) * he'
      · exfalso
        apply hrne w
        have he' : -(r w) = r w := by simpa [B] using he
        linear_combination (-1 / 2 : ℂ) * he'
      · rfl
    exact Prod.ext hij rfl
  have hbs : Function.Surjective b := by
    intro z
    have hqmem : (z : ℂ)^2+c ∈ sublevel c (2*t) := by
      change escape c ((z : ℂ)^2+c) ≤ 2*t
      rw [escape_step]
      have hz := z.property
      change escape c (z : ℂ) ≤ t at hz
      linarith
    let w : sublevel c (2*t) := ⟨(z : ℂ)^2+c, hqmem⟩
    have hsq : r w ^ 2 = (z : ℂ)^2 := by
      have h := hrsq w
      change r w ^ 2 + c = (z : ℂ)^2+c at h
      exact add_right_cancel h
    have hmul : ((z : ℂ)-r w)*((z : ℂ)+r w) = 0 := by
      calc
        _ = (z : ℂ)^2-r w ^ 2 := by ring
        _ = 0 := by rw [hsq, sub_self]
    rcases mul_eq_zero.mp hmul with h | h
    · refine ⟨(0,w), ?_⟩
      apply Subtype.ext
      change B (0,w) = (z : ℂ)
      simpa [B] using (sub_eq_zero.mp h).symm
    · refine ⟨(1,w), ?_⟩
      apply Subtype.ext
      change B (1,w) = (z : ℂ)
      have he : -(r w) = (z : ℂ) := by linear_combination -h
      simpa [B] using he
  letI : CompactSpace (sublevel c (2*t)) :=
    isCompact_iff_compactSpace.mp
      (quadratic_escape_sublevel_compact c (2*t) (by positivity))
  let e : (Fin 2 × sublevel c (2*t)) ≃ₜ sublevel c t :=
    (Equiv.ofBijective b ⟨hbi, hbs⟩).toHomeomorphOfContinuousClosed hbc hbc.isClosedMap
  refine ⟨e.symm, ?_⟩
  intro z
  have hbe : b (e.symm z) = z := e.apply_symm_apply z
  have hq := hbq (e.symm z)
  rw [hbe] at hq
  exact hq.symm

end LoopsQuadraticEscapeTree

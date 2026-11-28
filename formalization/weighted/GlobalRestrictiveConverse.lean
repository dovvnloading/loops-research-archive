import GlobalShootingParameter

/-!
# An exact endpoint criterion for the full physical return interval

The two positive inverse endpoints describe every intermediate image of
the actual interval.  Their displacement is therefore equivalent to the
whole restrictive-return condition, including all intermediate signs.
-/

namespace GlobalWindowShooting

open Set Function NearTwoInverse NearTwoShooting
open LimitingCrestQuadraticReturn GlobalRestrictiveWindow

noncomputable section

private theorem inverse_positive {c t : ℝ} (hc : c<0) (ht : c<t) (n : ℕ) :
    0<back c (n+1) t := by
  cases n with
  | zero =>
    simp only [back_succ,back_zero,B]
    exact Real.sqrt_pos.mpr (sub_pos.mpr ht)
  | succ n =>
    rw [back_succ,B]
    have hn : 0 ≤ back c (n+1) t := by
      rw [back_succ]
      exact B_nonneg c (back c n t)
    exact Real.sqrt_pos.mpr (by linarith)

private theorem inverse_square {c t : ℝ} (hc : c<0) (ht : c≤t) (n : ℕ) :
    (back c (n+1) t)^2=back c n t-c := by
  have hn : 0≤back c n t-c := by
    cases n with
    | zero => simpa only [back_zero] using sub_nonneg.mpr ht
    | succ n =>
      have h := B_nonneg c (back c n t)
      rw [← back_succ] at h
      linarith
  rw [back_succ,B,Real.sq_sqrt hn]

private theorem inverse_interval_forward {c a b z : ℝ} {n : ℕ}
    (hc : c<0) (ha : c≤a) (hb : c≤b)
    (hz : z ∈ Icc (back c n a) (back c n b)) :
    ∀ j≤n, (realMap c)^[j] z ∈
      Icc (back c (n-j) a) (back c (n-j) b) := by
  intro j
  induction j with
  | zero =>
    intro _
    simpa only [Function.iterate_zero, id_eq,Nat.sub_zero] using hz
  | succ j ih =>
    intro hj
    have hi := ih (by omega)
    have hsub : n-j=(n-(j+1))+1 := by omega
    have hn : 0≤back c (n-j) a := by
      rw [hsub,back_succ]
      exact B_nonneg c _
    have hl := pow_le_pow_left₀ hn hi.1 2
    have hu := pow_le_pow_left₀ (hn.trans hi.1) hi.2 2
    rw [hsub,inverse_square hc ha] at hl
    rw [hsub,inverse_square hc hb] at hu
    rw [Function.iterate_succ_apply']
    change (realMap c)^[j] z ^ 2+c ∈ _
    constructor <;> linarith only [hl,hu]

private theorem iterate_even (c x : ℝ) {n : ℕ} (hn : 1≤n) :
    (realMap c)^[n] (-x)=(realMap c)^[n] x := by
  cases n with
  | zero => omega
  | succ n =>
    rw [Function.iterate_succ_apply,Function.iterate_succ_apply]
    congr 1
    simp only [realMap,neg_sq]

private theorem shifted_phase (c x : ℝ) {j : ℕ} (hj : 2≤j) :
    (realMap c)^[j] x=(realMap c)^[j-1] (-realMap c x) := by
  calc
    _ = (realMap c)^[(j-1)+1] x := by
      rw [Nat.sub_add_cancel (by omega : 1≤j)]
    _ = (realMap c)^[j-1] (realMap c x) :=
      Function.iterate_succ_apply (realMap c) (j-1) x
    _ = _ := (iterate_even c (realMap c x) (by omega : 1≤j-1)).symm

/-- On the complete global shooting rectangle, invariance of the actual
return interval and every prescribed intermediate sign are equivalent to
one exact inverse-endpoint inequality. -/
theorem restrictive_iff_endpoint {c d : ℝ} {p : ℕ}
    (hp : 17≤p)
    (hc : c ∈ Icc (-2 : ℝ) (-2+20*scale p))
    (hd : 0<d) (hdu : d≤14*scale p)
    (hs : shooting (p-2) d c=0) :
    PositiveRestrictiveReturn c p ↔
      d^2≤back c (p-1) d-back c (p-1) (-d) := by
  have hq := scale_small hp
  have hcb := NearTwoShooting.parameter_band hp hc
  have hdb : d ∈ Icc (0 : ℝ) 2 := ⟨hd.le,by linarith⟩
  have hcneg : c<0 := by linarith [hcb.2]
  have hcnegd : c< -d := by linarith [hc.2]
  have hcv : criticalValue c p=d := by
    simpa only [Nat.sub_add_cancel (by omega : 2≤p)] using
      shooting_terminal_value hcb hdb hs
  have hbackcrit : back c (p-1) d= -c := by
    have heq : back c (p-2) d=c^2+c := by
      dsimp [shooting] at hs
      linarith only [hs]
    rw [show p-1=(p-2)+1 by omega,back_succ,heq,B,
      add_sub_cancel_right,Real.sqrt_sq_eq_abs,abs_of_neg hcneg]
  constructor
  · intro h
    have he := h.endpoint_return_mem
    have hid := h.inverse_displacement (by omega : 2≤p)
    rw [hcv] at hid
    have hlo : -d≤(realMap c)^[p] (criticalValue c p) := by
      simpa only [returnInterval,hcv] using he.1
    have hmono := back_mono_initial c (p-1) hlo
    rw [hcv] at hmono
    linarith only [hid,hmono]
  · intro hend
    have hnegative_inverse : 0<back c (p-1) (-d) := by
      simpa only [show p-2+1=p-1 by omega] using
        inverse_positive hcneg hcnegd (p-2)
    rw [hbackcrit] at hend
    have hfirst : d^2+c<0 := by linarith only [hend,hnegative_inverse]
    have hz : ∀ x∈Icc (-d) d,
        -realMap c x ∈ Icc (back c (p-1) (-d)) (back c (p-1) d) := by
      intro x hx
      have hsq := sq_le_sq' hx.1 hx.2
      rw [hbackcrit]
      dsimp [realMap]
      constructor <;> nlinarith only [hend,hsq,sq_nonneg x]
    have htrace : ∀ x∈Icc (-d) d, ∀ j≤p-1,
        (realMap c)^[j] (-realMap c x) ∈
          Icc (back c (p-1-j) (-d)) (back c (p-1-j) d) := by
      intro x hx
      exact inverse_interval_forward hcneg hcnegd.le (by linarith) (hz x hx)
    refine ⟨⟨hc.1,by linarith [hc.2]⟩,by rw [hcv]; exact hd,?_,?_,?_⟩
    · intro x hx
      have hx' : x∈Icc (-d) d := by simpa only [returnInterval,hcv] using hx
      have hsq := sq_le_sq' hx'.1 hx'.2
      dsimp [realMap]
      linarith only [hsq,hfirst]
    · intro j hj hjp x hx
      have hx' : x∈Icc (-d) d := by simpa only [returnInterval,hcv] using hx
      have hmem := htrace x hx' (j-1) (by omega)
      have hidx : p-1-(j-1)=(p-j-1)+1 := by omega
      rw [hidx] at hmem
      rw [shifted_phase c x hj]
      exact (inverse_positive hcneg hcnegd (p-j-1)).trans_le hmem.1
    · intro x hx
      have hx' : x∈Icc (-d) d := by simpa only [returnInterval,hcv] using hx
      have hmem := htrace x hx' (p-1) le_rfl
      change (realMap c)^[p] x∈Icc (-criticalValue c p) (criticalValue c p)
      rw [hcv,shifted_phase c x (by omega : 2≤p)]
      simpa only [Nat.sub_self,back_zero] using hmem

end
end GlobalWindowShooting

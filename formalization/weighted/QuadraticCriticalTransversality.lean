import Mathlib

/-!
# Critical-relation transversality for the actual quadratic family

The algebraic parity proof is independent of local linearization or
parameter uniformization. No global marked-width gate is asserted.
-/

namespace LoopsQuadraticTransversality

open Polynomial
noncomputable section

def orbit (c : ℂ) : ℕ → ℂ
  | 0 => 0
  | n + 1 => orbit c n ^ 2 + c

def slope (c : ℂ) : ℕ → ℂ
  | 0 => 0
  | n + 1 => 2 * orbit c n * slope c n + 1

/-- The recursively computed tangent is the actual complex parameter derivative. -/
theorem orbit_hasDerivAt (n : ℕ) (c : ℂ) :
    HasDerivAt (fun w : ℂ => orbit w n) (slope c n) c := by
  induction n with
  | zero => simpa [orbit, slope] using (hasDerivAt_const c (0 : ℂ))
  | succ n ih =>
    have hh := (ih.pow 2).add (hasDerivAt_id c)
    have heq : (fun w : ℂ => orbit w (n+1)) =
        (fun w : ℂ => orbit w n)^2 + id := by
      funext w
      simp [orbit]
    rw [heq]
    simpa only [slope, Nat.cast_ofNat, Nat.reduceSub, pow_one] using hh

/-- Integer polynomial representing the entire critical orbit. -/
def orbitPoly : ℕ → ℤ[X]
  | 0 => 0
  | n + 1 => orbitPoly n ^ 2 + X

theorem orbitPoly_aeval (c : ℂ) (n : ℕ) :
    aeval c (orbitPoly n) = orbit c n := by
  induction n with
  | zero => simp [orbitPoly, orbit]
  | succ n ih => simp [orbitPoly, orbit, ih]

theorem orbitPoly_monic_degree (n : ℕ) :
    (orbitPoly (n+1)).Monic ∧ (orbitPoly (n+1)).natDegree = 2^n := by
  induction n with
  | zero => simp [orbitPoly]
  | succ n ih =>
    have hp := ih.1.pow 2
    have hd : (orbitPoly (n+1)^2).natDegree = 2^(n+1) := by
      rw [ih.1.natDegree_pow, ih.2, pow_succ]
      ring
    have hlt : (X : ℤ[X]).natDegree < (orbitPoly (n+1)^2).natDegree := by
      rw [natDegree_X, hd, pow_succ]
      have hpos : 0 < (2:ℕ)^n := pow_pos (by decide) _
      omega
    change (orbitPoly (n+1)^2 + X).Monic ∧
      (orbitPoly (n+1)^2 + X).natDegree = 2^(n+1)
    exact ⟨hp.add_of_left (degree_lt_degree hlt),
      (natDegree_add_eq_left_of_natDegree_lt hlt).trans hd⟩

theorem orbitPoly_degree_strictMono :
    StrictMono (fun n => (orbitPoly n).natDegree) := by
  apply strictMono_nat_of_lt_succ
  intro n
  cases n with
  | zero => simp [orbitPoly]
  | succ n =>
    change (orbitPoly (n+1)).natDegree < (orbitPoly (n+1+1)).natDegree
    rw [(orbitPoly_monic_degree n).2, (orbitPoly_monic_degree (n+1)).2, pow_succ]
    have hpos : 0 < (2:ℕ)^n := pow_pos (by decide) _
    omega

/-- Every actual collision parameter, including every center, is an algebraic integer. -/
theorem integral_of_collision (c : ℂ) (a b : ℕ) (hab : a < b)
    (h : orbit c a = orbit c b) : IsIntegral ℤ c := by
  have hm : (orbitPoly b).Monic := by
    cases b with
    | zero => omega
    | succ b => exact (orbitPoly_monic_degree b).1
  refine ⟨orbitPoly b - orbitPoly a,
    hm.sub_of_left (degree_lt_degree (orbitPoly_degree_strictMono hab)), ?_⟩
  rw [← aeval_def]
  simp [orbitPoly_aeval, h]

theorem orbit_integral {c : ℂ} (hc : IsIntegral ℤ c) (n : ℕ) :
    IsIntegral ℤ (orbit c n) := by
  induction n with
  | zero => exact isIntegral_zero
  | succ n ih =>
    simpa only [orbit, pow_two] using (ih.mul ih).add hc

theorem slope_integral {c : ℂ} (hc : IsIntegral ℤ c) (n : ℕ) :
    IsIntegral ℤ (slope c n) := by
  induction n with
  | zero => exact isIntegral_zero
  | succ n ih =>
    have h2 : IsIntegral ℤ (2 : ℂ) := isIntegral_natCast 2
    change IsIntegral ℤ (2 * orbit c n * slope c n + 1)
    exact ((h2.mul (orbit_integral hc n)).mul ih).add isIntegral_one

/-- Two cannot have an inverse among the complex algebraic integers. -/
theorem integral_not_half {x : ℂ} (hx : IsIntegral ℤ x) :
    (2 : ℂ) * x ≠ 1 := by
  intro h
  have hx' : x = (1:ℂ)/2 := by linear_combination (1/2:ℂ) * h
  let f : ℚ →ₐ[ℤ] ℂ := IsScalarTower.toAlgHom ℤ ℚ ℂ
  have hmap : f (1/2 : ℚ) = (1:ℂ)/2 := by
    simp [f]
  have hq : IsIntegral ℤ (1/2 : ℚ) := by
    apply (isIntegral_algHom_iff f f.injective).mp
    rw [hmap, ← hx']
    exact hx
  obtain ⟨z,hz⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hq
  have hz' : (z : ℚ) = 1/2 := by simpa using hz
  have hz'' : (2:ℚ) * (z:ℚ) = 1 := by linarith
  have hzInt : (2:ℤ) * z = 1 := by exact_mod_cast hz''
  omega

/-- The weighted tangent is congruent to the orbit modulo two, even at time zero. -/
theorem orbit_slope_parity {c : ℂ} (hc : IsIntegral ℤ c) (n : ℕ) :
    ∃ t : ℂ, IsIntegral ℤ t ∧
      orbit c n * slope c n = orbit c n + 2*t := by
  cases n with
  | zero => exact ⟨0, isIntegral_zero, by simp [orbit, slope]⟩
  | succ n =>
    refine ⟨orbit c (n+1) * orbit c n * slope c n,
      ((orbit_integral hc (n+1)).mul (orbit_integral hc n)).mul
        (slope_integral hc n), ?_⟩
    simp only [slope]
    ring

/-- The signed predecessor relation has nonzero derivative at every algebraic-integer
parameter satisfying it. Both indices are positive, not fixed numerical periods. -/
theorem signed_relation_transverse {c : ℂ} (hc : IsIntegral ℤ c) (a b : ℕ)
    (hsign : orbit c (a+1) + orbit c (b+1) = 0) :
    slope c (a+1) + slope c (b+1) ≠ 0 := by
  intro hzero
  obtain ⟨u, huI, hu⟩ := orbit_slope_parity hc a
  obtain ⟨v, hvI, hv⟩ := orbit_slope_parity hc b
  simp only [slope] at hzero
  have hs : orbit c a + orbit c b = -1 - 2*(u+v) := by
    linear_combination (1/2:ℂ) * hzero - hu - hv
  have hsq : (orbit c a + orbit c b)^2 =
      2*(orbit c a * orbit c b - c) := by
    simp only [orbit] at hsign
    linear_combination hsign
  let t := u+v
  let w := orbit c a * orbit c b - c - 2*t - 2*t*t
  have ht : IsIntegral ℤ t := huI.add hvI
  have h2 : IsIntegral ℤ (2:ℂ) := isIntegral_natCast 2
  have hw : IsIntegral ℤ w :=
    ((((orbit_integral hc a).mul (orbit_integral hc b)).sub hc).sub
      (h2.mul ht)).sub ((h2.mul ht).mul ht)
  apply integral_not_half hw
  dsimp [w, t]
  rw [hs] at hsq
  linear_combination -hsq

/-- Actual centers are simple roots of the critical-return polynomial,
at every positive return time (not only the exact period). -/
theorem center_transverse (c : ℂ) (n : ℕ) (h : orbit c (n+1) = 0) :
    slope c (n+1) ≠ 0 := by
  have hc := integral_of_collision c 0 (n+1) (by omega) (by simpa [orbit] using h.symm)
  intro hd
  have hi := ((orbit_integral hc n).mul (slope_integral hc n)).neg
  apply integral_not_half hi
  simp only [slope] at hd
  linear_combination -hd

/-- A collision with unequal predecessors is transverse in the actual
complex parameter. No repelling multiplier or linearization is assumed. -/
theorem first_collision_transverse (c : ℂ) (a b : ℕ) (hab : a < b)
    (hcoll : orbit c (a+2) = orbit c (b+2))
    (hprev : orbit c (a+1) ≠ orbit c (b+1)) :
    slope c (b+2) - slope c (a+2) ≠ 0 := by
  have hc := integral_of_collision c (a+2) (b+2) (by omega) hcoll
  have hprod : (orbit c (a+1)-orbit c (b+1)) *
      (orbit c (a+1)+orbit c (b+1)) = 0 := by
    change orbit c (a+1)^2+c = orbit c (b+1)^2+c at hcoll
    linear_combination hcoll
  have hsign := (mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hprev)
  have hb : orbit c (b+1) ≠ 0 := by
    intro hz
    rw [hz, add_zero] at hsign
    exact hprev (hsign.trans hz.symm)
  intro hd
  have hfactor : 2*orbit c (b+1)*(slope c (a+1)+slope c (b+1)) = 0 := by
    change (2*orbit c (b+1)*slope c (b+1)+1) -
      (2*orbit c (a+1)*slope c (a+1)+1) = 0 at hd
    linear_combination hd + 2*slope c (a+1)*hsign
  exact signed_relation_transverse hc a b hsign
    ((mul_eq_zero.mp hfactor).resolve_left (mul_ne_zero (by norm_num) hb))

/-- Transversality expressed using mathlib's genuine complex derivative. -/
theorem first_collision_deriv_ne_zero (c : ℂ) (a b : ℕ) (hab : a < b)
    (hcoll : orbit c (a+2) = orbit c (b+2))
    (hprev : orbit c (a+1) ≠ orbit c (b+1)) :
    deriv (fun w : ℂ => orbit w (b+2) - orbit w (a+2)) c ≠ 0 := by
  have heq : (fun w : ℂ => orbit w (b+2) - orbit w (a+2)) =
      (fun w : ℂ => orbit w (b+2)) - (fun w : ℂ => orbit w (a+2)) := by
    funext w
    rfl
  rw [heq, ((orbit_hasDerivAt (b+2) c).sub (orbit_hasDerivAt (a+2) c)).deriv]
  exact first_collision_transverse c a b hab hcoll hprev

/-- Half the tangent of a signed predecessor relation is a unit modulo
two in the algebraic integers, with an explicit integral inverse witness. -/
theorem signed_relation_unit_mod_two {c : ℂ} (hc : IsIntegral ℤ c) (a b : ℕ)
    (hsign : orbit c (a+1) + orbit c (b+1) = 0) :
    ∃ q r k : ℂ, IsIntegral ℤ q ∧ IsIntegral ℤ r ∧ IsIntegral ℤ k ∧
      slope c (a+1) + slope c (b+1) = 2*q ∧ q*r = 1 + 2*k := by
  obtain ⟨u, huI, hu⟩ := orbit_slope_parity hc a
  obtain ⟨v, hvI, hv⟩ := orbit_slope_parity hc b
  let t := u+v
  let s := orbit c a * slope c a + orbit c b * slope c b
  let z := orbit c a * orbit c b - c + 2*(orbit c a + orbit c b)*t + 2*t*t
  have hA := orbit_integral hc a
  have hB := orbit_integral hc b
  have ht : IsIntegral ℤ t := huI.add hvI
  have h2 : IsIntegral ℤ (2 : ℂ) := isIntegral_natCast 2
  have h1 : IsIntegral ℤ (1 : ℂ) := isIntegral_one
  have hsI : IsIntegral ℤ s :=
    (hA.mul (slope_integral hc a)).add (hB.mul (slope_integral hc b))
  have hzI : IsIntegral ℤ z :=
    (((hA.mul hB).sub hc).add ((h2.mul (hA.add hB)).mul ht)).add
      ((h2.mul ht).mul ht)
  have hs : s = orbit c a + orbit c b + 2*t := by
    dsimp [s, t]
    linear_combination hu + hv
  have hsq : (orbit c a + orbit c b)^2 =
      2*(orbit c a * orbit c b - c) := by
    simp only [orbit] at hsign
    linear_combination hsign
  have hzsq : s^2 = 2*z := by
    rw [hs]
    change (orbit c a + orbit c b + 2*t)^2 =
      2*(orbit c a * orbit c b - c + 2*(orbit c a + orbit c b)*t + 2*t*t)
    linear_combination hsq
  refine ⟨1+s,1-s,-z,h1.add hsI,h1.sub hsI,hzI.neg,?_,?_⟩
  · change (2*orbit c a*slope c a+1)+(2*orbit c b*slope c b+1) = 2*(1+s)
    dsimp [s]
    ring
  · linear_combination -hzsq

/-- Exact arithmetic content of the genuine complex collision derivative:
after removing four times the nonzero predecessor, the remaining factor
is an algebraic integer with an explicit inverse modulo two. -/
theorem first_collision_deriv_factor_unit (c : ℂ) (a b : ℕ) (hab : a < b)
    (hcoll : orbit c (a+2) = orbit c (b+2))
    (hprev : orbit c (a+1) ≠ orbit c (b+1)) :
    ∃ q r k : ℂ, IsIntegral ℤ q ∧ IsIntegral ℤ r ∧ IsIntegral ℤ k ∧
      deriv (fun w : ℂ => orbit w (b+2) - orbit w (a+2)) c =
        4*orbit c (b+1)*q ∧ q*r = 1+2*k := by
  have hc := integral_of_collision c (a+2) (b+2) (by omega) hcoll
  have hprod : (orbit c (a+1)-orbit c (b+1)) *
      (orbit c (a+1)+orbit c (b+1)) = 0 := by
    change orbit c (a+1)^2+c = orbit c (b+1)^2+c at hcoll
    linear_combination hcoll
  have hsign := (mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hprev)
  obtain ⟨q,r,k,hq,hr,hk,hsum,hunit⟩ := signed_relation_unit_mod_two hc a b hsign
  have heq : (fun w : ℂ => orbit w (b+2) - orbit w (a+2)) =
      (fun w : ℂ => orbit w (b+2)) - (fun w : ℂ => orbit w (a+2)) := by
    funext w
    rfl
  refine ⟨q,r,k,hq,hr,hk,?_,hunit⟩
  rw [heq, ((orbit_hasDerivAt (b+2) c).sub (orbit_hasDerivAt (a+2) c)).deriv]
  change (2*orbit c (b+1)*slope c (b+1)+1) -
      (2*orbit c (a+1)*slope c (a+1)+1) = 4*orbit c (b+1)*q
  linear_combination 2*orbit c (b+1)*hsum - 2*slope c (a+1)*hsign

/-! The exact bridge from the collision tangent to the normalized
entrance derivative of a given moving periodic point and chart. -/

open Filter
open scoped Topology

/-- The actual return orbit, starting at any dynamical point. -/
def returnOrbit (c z : ℂ) : ℕ → ℂ
  | 0 => z
  | n+1 => returnOrbit c z n ^ 2 + c

/-- Parameter tangent of a return orbit starting with an arbitrary tangent. -/
def returnTangent (c z d : ℂ) : ℕ → ℂ
  | 0 => d
  | n+1 => 2 * returnOrbit c z n * returnTangent c z d n + 1

/-- Spatial multiplier of the actual return map. -/
def returnMultiplier (c z : ℂ) : ℕ → ℂ
  | 0 => 1
  | n+1 => 2 * returnOrbit c z n * returnMultiplier c z n

theorem returnOrbit_eq_iterate (c z : ℂ) (p : ℕ) :
    returnOrbit c z p = (fun w : ℂ => w^2+c)^[p] z := by
  induction p with
  | zero => rfl
  | succ p ih => simp only [returnOrbit, Function.iterate_succ_apply', ih]

theorem returnOrbit_orbit (c : ℂ) (m p : ℕ) :
    returnOrbit c (orbit c m) p = orbit c (m+p) := by
  induction p with
  | zero => rfl
  | succ p ih =>
    change returnOrbit c (orbit c m) p ^ 2 + c = orbit c (m+p) ^ 2 + c
    rw [ih]

theorem returnTangent_orbit (c : ℂ) (m p : ℕ) :
    returnTangent c (orbit c m) (slope c m) p = slope c (m+p) := by
  induction p with
  | zero => rfl
  | succ p ih =>
    change 2*returnOrbit c (orbit c m) p*returnTangent c (orbit c m) (slope c m) p+1 =
      2*orbit c (m+p)*slope c (m+p)+1
    rw [returnOrbit_orbit, ih]

theorem returnMultiplier_hasDerivAt (c z : ℂ) (p : ℕ) :
    HasDerivAt (fun w : ℂ => returnOrbit c w p) (returnMultiplier c z p) z := by
  induction p with
  | zero =>
    change HasDerivAt (id : ℂ → ℂ) 1 z
    exact hasDerivAt_id z
  | succ p ih =>
    have hh := (ih.pow 2).add (hasDerivAt_const z c)
    have heq : (fun w : ℂ => returnOrbit c w (p+1)) =
        (fun w : ℂ => returnOrbit c w p)^2 + fun _ => c := by
      funext w
      simp [returnOrbit]
    rw [heq]
    simpa only [returnMultiplier, Nat.cast_ofNat, Nat.reduceSub, pow_one, add_zero]
      using hh

theorem returnTangent_hasDerivAt (c : ℂ) (z : ℂ → ℂ) (d : ℂ)
    (hz : HasDerivAt z d c) (p : ℕ) :
    HasDerivAt (fun w : ℂ => returnOrbit w (z w) p)
      (returnTangent c (z c) d p) c := by
  induction p with
  | zero => simpa [returnOrbit, returnTangent] using hz
  | succ p ih =>
    have hh := (ih.pow 2).add (hasDerivAt_id c)
    have heq : (fun w : ℂ => returnOrbit w (z w) (p+1)) =
        (fun w : ℂ => returnOrbit w (z w) p)^2 + id := by
      funext w
      simp [returnOrbit]
    rw [heq]
    simpa only [returnTangent, Nat.cast_ofNat, Nat.reduceSub, pow_one] using hh

/-- The inhomogeneous parameter forcing cancels exactly in the difference
of tangents on the same dynamical trajectory. -/
theorem returnTangent_sub (c z u v : ℂ) (p : ℕ) :
    returnTangent c z u p - returnTangent c z v p =
      returnMultiplier c z p * (u-v) := by
  induction p with
  | zero => simp [returnTangent, returnMultiplier]
  | succ p ih =>
    simp only [returnTangent, returnMultiplier]
    calc
      2*returnOrbit c z p*returnTangent c z u p+1 -
          (2*returnOrbit c z p*returnTangent c z v p+1) =
        (2*returnOrbit c z p)*(returnTangent c z u p-returnTangent c z v p) := by ring
      _ = _ := by rw [ih]; ring

/-- At a differentiable moving periodic point the collision tangent is the
entrance displacement tangent multiplied by the spatial multiplier minus one. -/
theorem landing_motion_identity (c : ℂ) (m p : ℕ) (z : ℂ → ℂ) (dz : ℂ)
    (hz : HasDerivAt z dz c) (hmatch : z c = orbit c m)
    (hper : (fun w : ℂ => returnOrbit w (z w) p) =ᶠ[𝓝 c] z) :
    slope c (m+p) - slope c m =
      (returnMultiplier c (orbit c m) p - 1) * (slope c m - dz) := by
  have hret := (returnTangent_hasDerivAt c z dz hz p).unique
    (hz.congr_of_eventuallyEq hper)
  rw [hmatch] at hret
  have hdiff := returnTangent_sub c (orbit c m) (slope c m) dz p
  rw [returnTangent_orbit, hret] at hdiff
  linear_combination hdiff

/-- Normalizing a jointly differentiable chart to vanish at the moving
periodic point, with spatial derivative one, makes the entrance derivative
exactly the critical-orbit tangent minus the periodic-point tangent. -/
theorem normalized_chart_entrance_hasDerivAt (c : ℂ) (m : ℕ)
    (z : ℂ → ℂ) (dz : ℂ) (hz : HasDerivAt z dz c)
    (hmatch : z c = orbit c m) (chi : ℂ × ℂ → ℂ)
    (L : (ℂ × ℂ) →L[ℂ] ℂ)
    (hchi : HasFDerivAt chi L (c,z c)) (hnorm : L (0,1) = 1)
    (hzero : (fun w : ℂ => chi (w,z w)) =ᶠ[𝓝 c] (fun _ => 0)) :
    HasDerivAt (fun w : ℂ => chi (w,orbit w m)) (slope c m - dz) c := by
  have hzpath : HasDerivAt (fun w : ℂ => (w,z w)) (1,dz) c :=
    (hasDerivAt_id c).prodMk hz
  have hppath : HasDerivAt (fun w : ℂ => (w,orbit w m)) (1,slope c m) c :=
    (hasDerivAt_id c).prodMk (orbit_hasDerivAt m c)
  have hzD : HasDerivAt (fun w : ℂ => chi (w,z w)) (L (1,dz)) c :=
    hchi.comp_hasDerivAt c hzpath
  have hpD : HasDerivAt (fun w : ℂ => chi (w,orbit w m)) (L (1,slope c m)) c :=
    hchi.comp_hasDerivAt_of_eq c hppath (by rw [hmatch])
  have hz0 : L (1,dz) = 0 :=
    hzD.unique ((hasDerivAt_const c (0:ℂ)).congr_of_eventuallyEq hzero)
  have hvec : ((1,slope c m):ℂ × ℂ) - (1,dz) =
      (slope c m-dz) • ((0,1):ℂ × ℂ) := by
    apply Prod.ext <;> simp
  have hlin : L (1,slope c m) - L (1,dz) = slope c m-dz := by
    rw [← map_sub, hvec, map_smul, hnorm, smul_eq_mul, mul_one]
  rw [hz0, sub_zero] at hlin
  exact hpD.congr_deriv hlin

/-- Exact derivative identity for the normalized chart entrance of the
given moving periodic point; no transversality premise is used. -/
theorem normalized_entrance_collision_identity (c : ℂ) (a b : ℕ) (hab : a < b)
    (z : ℂ → ℂ) (dz : ℂ) (hz : HasDerivAt z dz c)
    (hmatch : z c = orbit c (a+2))
    (hper : (fun w : ℂ => returnOrbit w (z w) (b-a)) =ᶠ[𝓝 c] z)
    (chi : ℂ × ℂ → ℂ) (L : (ℂ × ℂ) →L[ℂ] ℂ)
    (hchi : HasFDerivAt chi L (c,z c)) (hnorm : L (0,1) = 1)
    (hzero : (fun w : ℂ => chi (w,z w)) =ᶠ[𝓝 c] (fun _ => 0)) :
    slope c (b+2) - slope c (a+2) =
      (returnMultiplier c (orbit c (a+2)) (b-a) - 1) *
        deriv (fun w : ℂ => chi (w,orbit w (a+2))) c := by
  rw [(normalized_chart_entrance_hasDerivAt c (a+2) z dz hz hmatch chi L
    hchi hnorm hzero).deriv]
  have hi := landing_motion_identity c (a+2) (b-a) z dz hz hmatch hper
  have hind : a+2+(b-a)=b+2 := by omega
  rwa [hind] at hi

/-- The nontrivial entrance derivative in Misiurewicz linearization is
nonzero, for every first collision and any given normalized moving chart
and periodic point satisfying the stated differentiability conditions. -/
theorem normalized_entrance_deriv_ne_zero (c : ℂ) (a b : ℕ) (hab : a < b)
    (hcoll : orbit c (a+2) = orbit c (b+2))
    (hprev : orbit c (a+1) ≠ orbit c (b+1))
    (z : ℂ → ℂ) (dz : ℂ) (hz : HasDerivAt z dz c)
    (hmatch : z c = orbit c (a+2))
    (hper : (fun w : ℂ => returnOrbit w (z w) (b-a)) =ᶠ[𝓝 c] z)
    (chi : ℂ × ℂ → ℂ) (L : (ℂ × ℂ) →L[ℂ] ℂ)
    (hchi : HasFDerivAt chi L (c,z c)) (hnorm : L (0,1) = 1)
    (hzero : (fun w : ℂ => chi (w,z w)) =ᶠ[𝓝 c] (fun _ => 0)) :
    deriv (fun w : ℂ => chi (w,orbit w (a+2))) c ≠ 0 := by
  have hi := normalized_entrance_collision_identity c a b hab z dz hz hmatch hper
    chi L hchi hnorm hzero
  intro ha
  rw [ha, mul_zero] at hi
  exact first_collision_transverse c a b hab hcoll hprev hi

end
end LoopsQuadraticTransversality

import DepthThreeReal

/-!
# Exhaustive real-parameter isolation by exact interval trees

Each split covers its entire closed parent interval.  A discarded leaf
has either a certified incompatible critical-orbit sign, a nonzero
collision enclosure, or a nonzero enclosure of the deflated collision.
The resulting theorem applies to every real parameter, including points
between the integer grid coordinates used to encode the endpoints.
-/

namespace LoopsGlobalTip

open Set LoopsFormal.Period27 LoopsFormal.DepthThree
open LoopsDepthThreeReal LoopsRealPeriod27

/-- The complete physical critical itinerary through the six returns. -/
def requiredPositive (p j : Nat) : Bool :=
  if j % p = 0 then decide (j / p = 1 ∨ j / p = 4 ∨ j / p = 6)
  else decide (j % p ≠ 1)

/-- Strict signs of every actual critical iterate through time `6 * p`. -/
def HasSigns (p : Nat) (c : ℝ) : Prop :=
  ∀ j, 1 ≤ j → j ≤ 6 * p →
    if requiredPositive p j then 0 < polynomial j c else polynomial j c < 0

/-- A finite proof certificate; the interval at a node is inherited from
its ancestors rather than being independently supplied by the leaf. -/
inductive CoverTree where
  | split (cut : Int) (left right : CoverTree)
  | keep
  | wrongSign (time : Nat)
  | nonzero
  | deflated
  deriving Repr, DecidableEq

def orbitBound (S : Int) (_p : Nat) (C : Bounds) (j : Nat) : Bounds :=
  (rowAt (trace S C j) j).orbit

def collisionBound (S : Int) (p : Nat) (C : Bounds) : Bounds :=
  addBounds (orbitBound S p C (3 * p)) (orbitBound S p C (6 * p))

/-- The difference-of-iterates factor after removing the factor `x_(3p)`.
The factor order is increasing critical-orbit time. -/
def deflatedBound (S : Int) (p : Nat) (C : Bounds) : Bounds :=
  let rows := trace S C (6 * p)
  let product := (List.range (3 * p)).foldl (fun b j =>
    mulBoundsAt S b
      (addBounds (rowAt rows (3 * p + j)).orbit (rowAt rows j).orbit)) (oneAt S)
  addBounds product (doubleBounds (oneAt S))

def excludesZero (b : Bounds) : Bool := decide (b.hi < 0 ∨ 0 < b.lo)

/-- Strict enclosures certify the entire selected critical itinerary on
every real parameter in one box. -/
def signBoxCheck (S : Int) (p : Nat) (C : Bounds) : Bool :=
  (List.range (6 * p)).all fun k =>
    let j := k + 1
    let v := orbitBound S p C j
    if requiredPositive p j then decide (0 < v.lo) else decide (v.hi < 0)

/-- A decidable exhaustive-cover verifier using only signed integer
arithmetic. No real approximation is an input to its soundness theorem. -/
def coverCheck (S : Int) (p : Nat) (C seed : Bounds) : CoverTree → Bool
  | .split m left right =>
      decide (C.lo ≤ m ∧ m ≤ C.hi) &&
        coverCheck S p ⟨C.lo, m⟩ seed left &&
        coverCheck S p ⟨m, C.hi⟩ seed right
  | .keep => decide (seed.lo ≤ C.lo ∧ C.hi ≤ seed.hi)
  | .wrongSign j =>
      decide (1 ≤ j ∧ j ≤ 6 * p) &&
        if requiredPositive p j then decide ((orbitBound S p C j).hi ≤ 0)
        else decide (0 ≤ (orbitBound S p C j).lo)
  | .nonzero => excludesZero (collisionBound S p C)
  | .deflated => excludesZero (deflatedBound S p C)

noncomputable section

private theorem zero_enclosed (S : Int) : RealEnclosed S zeroBound 0 := by
  simp [RealEnclosed, zeroBound]

private theorem one_enclosed (S : Int) : RealEnclosed S (oneAt S) 1 := by
  simp [RealEnclosed, oneAt]

private theorem orbit_bound_enclosed {S : Int} (hS : 0 < S)
    {p : Nat} {C : Bounds} {c : ℝ} (hc : RealEnclosed S C c)
    {j : Nat} (_hj : j ≤ 6 * p) :
    RealEnclosed S (orbitBound S p C j) (polynomial j c) :=
  (trace_enclosed hS hc j j le_rfl).1

private theorem excludes_zero_sound {S : Int} {b : Bounds} {x : ℝ}
    (hx : RealEnclosed S b x) (hb : excludesZero b = true) : x ≠ 0 := by
  intro hz
  subst x
  simp only [RealEnclosed, zero_mul] at hx
  simp only [excludesZero, decide_eq_true_eq] at hb
  rcases hb with hneg | hpos
  · have hh : (b.hi : ℝ) < 0 := by exact_mod_cast hneg
    linarith [hx.2]
  · have hl : (0 : ℝ) < (b.lo : ℝ) := by exact_mod_cast hpos
    linarith [hx.1]

private theorem fold_mul_enclosed {ι : Type} {S : Int} (hS : 0 < S)
    (is : List ι) (bounds : ι → Bounds) (values : ι → ℝ)
    (h : ∀ i ∈ is, RealEnclosed S (bounds i) (values i))
    {a : Bounds} {x : ℝ} (ha : RealEnclosed S a x) :
    RealEnclosed S
      (is.foldl (fun b i => mulBoundsAt S b (bounds i)) a)
      (is.foldl (fun y i => y * values i) x) := by
  induction is generalizing a x with
  | nil => exact ha
  | cons i is ih =>
      apply ih
      · intro j hj
        exact h j (List.mem_cons_of_mem i hj)
      · exact real_mul_enclosed hS ha (h i (List.mem_cons_self))

/-- The actual orbit difference factors into the initial difference and
the complete ordered product of quadratic difference factors. -/
theorem critical_difference_product (n k : Nat) (c : ℝ) :
    polynomial (n + k) c - polynomial k c = polynomial n c *
      ((List.range k).foldl
        (fun a j => a * (polynomial (n + j) c + polynomial j c)) 1) := by
  induction k with
  | zero =>
      simp [polynomial, state, realIter]
  | succ k ih =>
      have hn : polynomial (n + (k + 1)) c = polynomial (n + k) c ^ 2 + c := by
        simpa only [Nat.add_assoc] using polynomial_succ (n + k) c
      rw [hn, polynomial_succ, List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      linear_combination (polynomial (n + k) c + polynomial k c) * ih

/-- Exact deflation of the physical collision polynomial, before any
interval evaluation. -/
theorem collision_deflation (p : Nat) (c : ℝ) :
    collisionPolynomial p c = polynomial (3 * p) c *
      (((List.range (3 * p)).foldl
        (fun a j => a * (polynomial (3 * p + j) c + polynomial j c)) 1) + 2) := by
  have h := critical_difference_product (3 * p) (3 * p) c
  have hn : 3 * p + 3 * p = 6 * p := by omega
  rw [hn] at h
  dsimp only [collisionPolynomial]
  linarith

private theorem deflated_bound_enclosed {S : Int} (hS : 0 < S)
    {p : Nat} {C : Bounds} {c : ℝ} (hc : RealEnclosed S C c) :
    RealEnclosed S (deflatedBound S p C)
      (((List.range (3 * p)).foldl
        (fun a j => a * (polynomial (3 * p + j) c + polynomial j c)) 1) + 2) := by
  apply real_add_enclosed
  · apply fold_mul_enclosed hS
    · intro j hj
      have hj' : j < 3 * p := List.mem_range.mp hj
      exact real_add_enclosed
        (trace_enclosed hS hc (6 * p) (3 * p + j) (by omega)).1
        (trace_enclosed hS hc (6 * p) j (by omega)).1
    · exact one_enclosed S
  · simpa only [mul_one] using real_double_enclosed (one_enclosed S)

private theorem third_return_negative {p : Nat} (hp : 0 < p)
    {c : ℝ} (hs : HasSigns p c) : polynomial (3 * p) c < 0 := by
  have ht := hs (3 * p) (by omega) (by omega)
  have hsign : requiredPositive p (3 * p) = false := by
    simp [requiredPositive, Nat.ne_of_gt hp]
  simpa only [hsign, Bool.false_eq_true, ↓reduceIte] using ht

/-- The finite sign-box test proves the full strict itinerary uniformly
over the box, including all irrational parameter values in it. -/
theorem signBoxCheck_sound {S : Int} {p : Nat} {C : Bounds} {c : ℝ}
    (hS : 0 < S) (hcheck : signBoxCheck S p C = true)
    (hc : RealEnclosed S C c) : HasSigns p c := by
  intro j hj hjp
  have hk : j - 1 ∈ List.range (6 * p) := List.mem_range.mpr (by omega)
  have htest := (List.all_eq_true.mp hcheck) (j - 1) hk
  have hindex : j - 1 + 1 = j := by omega
  simp only [hindex] at htest
  have hx := orbit_bound_enclosed hS hc hjp
  have hSr : (0 : ℝ) < (S : ℝ) := by exact_mod_cast hS
  cases heq : requiredPositive p j with
  | false =>
      simp only [heq, Bool.false_eq_true, ↓reduceIte, decide_eq_true_eq] at htest ⊢
      have hh : ((orbitBound S p C j).hi : ℝ) < 0 := by exact_mod_cast htest
      apply (mul_lt_mul_iff_right₀ hSr).mp
      simpa only [mul_comm, zero_mul, mul_zero] using hx.2.trans_lt hh
  | true =>
      simp only [heq, ↓reduceIte, decide_eq_true_eq] at htest ⊢
      have hl : (0 : ℝ) < ((orbitBound S p C j).lo : ℝ) := by exact_mod_cast htest
      exact (mul_pos_iff_of_pos_right hSr).mp (hl.trans_le hx.1)

/-- Every accepted certificate isolates every actual real collision root
with the complete declared critical itinerary into the retained seed.
The full closed initial interval is covered, not only its grid points. -/
theorem coverCheck_sound {S : Int} {p : Nat} {C seed : Bounds}
    {tree : CoverTree} {c : ℝ} (hS : 0 < S) (hp : 0 < p)
    (hcheck : coverCheck S p C seed tree = true)
    (hc : RealEnclosed S C c) (hroot : collisionPolynomial p c = 0)
    (hs : HasSigns p c) : RealEnclosed S seed c := by
  induction tree generalizing C with
  | split m left right ihl ihr =>
      simp only [coverCheck, Bool.and_eq_true, decide_eq_true_eq] at hcheck
      rcases hcheck with ⟨⟨horder, hl⟩, hr⟩
      rcases le_total (c * (S : ℝ)) (m : ℝ) with hm | hm
      · exact ihl hl ⟨hc.1, hm⟩
      · exact ihr hr ⟨hm, hc.2⟩
  | keep =>
      simp only [coverCheck, decide_eq_true_eq] at hcheck
      have hl : (seed.lo : ℝ) ≤ (C.lo : ℝ) := by exact_mod_cast hcheck.1
      have hr : (C.hi : ℝ) ≤ (seed.hi : ℝ) := by exact_mod_cast hcheck.2
      exact ⟨hl.trans hc.1, hc.2.trans hr⟩
  | wrongSign j =>
      simp only [coverCheck, Bool.and_eq_true, decide_eq_true_eq] at hcheck
      have hx := orbit_bound_enclosed hS hc hcheck.1.2
      have ht := hs j hcheck.1.1 hcheck.1.2
      have hSr : (0 : ℝ) < (S : ℝ) := by exact_mod_cast hS
      cases heq : requiredPositive p j with
      | false =>
          simp only [heq, Bool.false_eq_true, ↓reduceIte, decide_eq_true_eq] at hcheck ht
          have hl : (0 : ℝ) ≤ ((orbitBound S p C j).lo : ℝ) := by
            exact_mod_cast hcheck.2
          have hprod : polynomial j c * (S : ℝ) < 0 := mul_neg_of_neg_of_pos ht hSr
          exact (not_lt_of_ge (hl.trans hx.1) hprod).elim
      | true =>
          simp only [heq, ↓reduceIte, decide_eq_true_eq] at hcheck ht
          have hh : ((orbitBound S p C j).hi : ℝ) ≤ 0 := by
            exact_mod_cast hcheck.2
          have hprod : 0 < polynomial j c * (S : ℝ) := mul_pos ht hSr
          exact (not_lt_of_ge (hx.2.trans hh) hprod).elim
  | nonzero =>
      have hx : RealEnclosed S (collisionBound S p C) (collisionPolynomial p c) :=
        real_add_enclosed (orbit_bound_enclosed hS hc (by omega))
          (orbit_bound_enclosed hS hc le_rfl)
      exact (excludes_zero_sound hx hcheck hroot).elim
  | deflated =>
      have hne := excludes_zero_sound (deflated_bound_enclosed hS hc) hcheck
      have hxne : polynomial (3 * p) c ≠ 0 := ne_of_lt (third_return_negative hp hs)
      rw [collision_deflation] at hroot
      exact (hne ((mul_eq_zero.mp hroot).resolve_left hxne)).elim

/-- Every real parameter in a certified root box has nonzero derivative
of the actual collision polynomial. In particular its isolated root is
simple. -/
theorem certified_collision_derivative_ne_zero {S : Int} {p : Nat}
    {C : Bounds} {c : ℝ} (h : RootCertificate S p C)
    (hc : RealEnclosed S C c) : collisionDerivative p c ≠ 0 := by
  apply excludes_zero_sound (collision_derivative_enclosed h.1 hc p)
  simp only [excludesZero, decide_eq_true_eq]
  exact h.2.2.2.elim Or.inr Or.inl

end

end LoopsGlobalTip

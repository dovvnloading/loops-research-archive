import Mathlib

/-!
# Tangent jets of literal quadratic orbit flights

Every normalized flight below is identified with a polynomial iterate of
`z ↦ z^2+c`.  The jet computation retains an exact polynomial remainder;
it is not an assumed Taylor law.
-/

namespace QuadraticFlightJet

open Polynomial
noncomputable section

/-- The coefficients of a tangent-to-identity polynomial through degree four. -/
@[ext] structure Jet where
  a : ℂ
  b : ℂ
  d : ℂ

namespace Jet

def identity : Jet := ⟨0, 0, 0⟩

def kick (a : ℂ) : Jet := ⟨a, 0, 0⟩

/-- Outer jet `u` composed with inner jet `v`. -/
def comp (u v : Jet) : Jet :=
  ⟨v.a + u.a,
    v.b + 2*u.a*v.a + u.b,
    v.d + u.a*(v.a^2 + 2*v.b) + 3*u.b*v.a + u.d⟩

theorem comp_assoc (u v w : Jet) :
    comp (comp u v) w = comp u (comp v w) := by
  apply Jet.ext <;> simp only [comp] <;> ring

@[simp] theorem identity_comp (u : Jet) : comp identity u = u := by
  apply Jet.ext <;> simp [comp, identity]

@[simp] theorem comp_identity (u : Jet) : comp u identity = u := by
  apply Jet.ext <;> simp [comp, identity]

end Jet

/-- The actual tangent quadratic `u ↦ u+a*u^2`. -/
def kickPoly (a : ℂ) : ℂ[X] := X + C a * X^2

/-- Successive quadratic steps in transported tangent coordinates. -/
def flight (a : ℕ → ℂ) : ℕ → ℂ[X]
  | 0 => X
  | n+1 => flight a n + C (a n) * (flight a n)^2

def flightJet (a : ℕ → ℂ) : ℕ → Jet
  | 0 => Jet.identity
  | n+1 => Jet.comp (Jet.kick (a n)) (flightJet a n)

/-- A split into consecutive orbit flights is literal polynomial composition. -/
theorem flight_add (a : ℕ → ℂ) (r n : ℕ) :
    flight a (r+n) =
      (flight (fun j => a (r+j)) n).comp (flight a r) := by
  induction n with
  | zero => simp [flight]
  | succ n ih =>
    simp only [Nat.add_succ, flight, ih, add_comp, mul_comp, pow_comp, C_comp]

/-- The corresponding exact composition identity for the retained jets. -/
theorem flightJet_add (a : ℕ → ℂ) (r n : ℕ) :
    flightJet a (r+n) =
      Jet.comp (flightJet (fun j => a (r+j)) n) (flightJet a r) := by
  induction n with
  | zero => simp [flightJet]
  | succ n ih =>
    change Jet.comp (Jet.kick (a (r+n))) (flightJet a (r+n)) =
      Jet.comp
        (Jet.comp (Jet.kick (a (r+n))) (flightJet (fun j => a (r+j)) n))
        (flightJet a r)
    rw [ih, Jet.comp_assoc]

def jetPoly (j : Jet) : ℂ[X] :=
  X + C j.a * X^2 + C j.b * X^3 + C j.d * X^4

/-- An exact polynomial remainder, not only a formal coefficient assertion. -/
def HasJet (p : ℂ[X]) (j : Jet) : Prop :=
  ∃ R : ℂ[X], p = jetPoly j + X^5 * R

private def stepRemainder (a : ℂ) (j : Jet) (R : ℂ[X]) : ℂ[X] :=
  R + C a *
    (C (2*j.d + 2*j.a*j.b) + C (j.b^2 + 2*j.a*j.d)*X +
      C (2*j.b*j.d)*X^2 + C (j.d^2)*X^3 +
      2*jetPoly j*R + X^5*R^2)

private theorem tangent_step_expansion (a : ℂ) (j : Jet) (R : ℂ[X]) :
    (jetPoly j + X^5*R) + C a*(jetPoly j + X^5*R)^2 =
      jetPoly (Jet.comp (Jet.kick a) j) + X^5*stepRemainder a j R := by
  simp [jetPoly, Jet.comp, Jet.kick, stepRemainder, map_add, map_mul, map_pow] <;> ring

/-- All retained coefficients are coefficients of the genuine composed polynomial. -/
theorem flight_hasJet (a : ℕ → ℂ) (n : ℕ) :
    HasJet (flight a n) (flightJet a n) := by
  induction n with
  | zero =>
    refine ⟨0, ?_⟩
    simp [flight, flightJet, jetPoly, Jet.identity]
  | succ n ih =>
    obtain ⟨R, hR⟩ := ih
    refine ⟨stepRemainder (a n) (flightJet a n) R, ?_⟩
    rw [flight, hR]
    exact tangent_step_expansion (a n) (flightJet a n) R

theorem HasJet.coeff_zero {p : ℂ[X]} {j : Jet} (h : HasJet p j) :
    p.coeff 0 = 0 := by
  obtain ⟨R, rfl⟩ := h
  simp [jetPoly, coeff_X_pow_mul']

theorem HasJet.coeff_one {p : ℂ[X]} {j : Jet} (h : HasJet p j) :
    p.coeff 1 = 1 := by
  obtain ⟨R, rfl⟩ := h
  simp [jetPoly, coeff_X_pow_mul']

theorem HasJet.coeff_two {p : ℂ[X]} {j : Jet} (h : HasJet p j) :
    p.coeff 2 = j.a := by
  obtain ⟨R, rfl⟩ := h
  simp [jetPoly, coeff_X_pow_mul']

theorem HasJet.coeff_three {p : ℂ[X]} {j : Jet} (h : HasJet p j) :
    p.coeff 3 = j.b := by
  obtain ⟨R, rfl⟩ := h
  simp [jetPoly, coeff_X_pow_mul']

theorem HasJet.coeff_four {p : ℂ[X]} {j : Jet} (h : HasJet p j) :
    p.coeff 4 = j.d := by
  obtain ⟨R, rfl⟩ := h
  simp [jetPoly, coeff_X_pow_mul']

theorem flight_coeff_two (a : ℕ → ℂ) (n : ℕ) :
    (flight a n).coeff 2 = (flightJet a n).a :=
  (flight_hasJet a n).coeff_two

theorem flight_coeff_three (a : ℕ → ℂ) (n : ℕ) :
    (flight a n).coeff 3 = (flightJet a n).b :=
  (flight_hasJet a n).coeff_three

theorem flight_coeff_four (a : ℕ → ℂ) (n : ℕ) :
    (flight a n).coeff 4 = (flightJet a n).d :=
  (flight_hasJet a n).coeff_four

/-- Literal quadratic orbit from an arbitrary phase point. -/
def orbit (c x : ℂ) : ℕ → ℂ
  | 0 => x
  | n+1 => (orbit c x n)^2 + c

def iteratePoly (c : ℂ) : ℕ → ℂ[X]
  | 0 => X
  | n+1 => (iteratePoly c n)^2 + C c

theorem iteratePoly_eval (c x : ℂ) (n : ℕ) :
    (iteratePoly c n).eval x = orbit c x n := by
  induction n with
  | zero => simp [iteratePoly, orbit]
  | succ n ih => simp [iteratePoly, orbit, ih]

theorem orbit_eq_iterate (c x : ℂ) (n : ℕ) :
    orbit c x n = (fun z : ℂ => z^2+c)^[n] x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    simp only [orbit, ih]

theorem orbit_add (c x : ℂ) (r n : ℕ) :
    orbit c x (r+n) = orbit c (orbit c x r) n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Nat.add_succ, orbit, ih]

theorem critical_orbit_shift (c : ℂ) (n : ℕ) :
    orbit c 0 (n+1) = orbit c c n := by
  have h := orbit_add c 0 1 n
  simpa [orbit, Nat.add_comm] using h

/-- The first quadratic step may be taken before the remaining iterate. -/
theorem iteratePoly_succ_comp (c : ℂ) (n : ℕ) :
    iteratePoly c (n+1) = (iteratePoly c n).comp (X^2+C c) := by
  induction n with
  | zero => simp [iteratePoly]
  | succ n ih =>
    change (iteratePoly c (n+1))^2+C c =
      ((iteratePoly c n)^2+C c).comp (X^2+C c)
    rw [ih]
    simp

theorem critical_substitution_identity (c s : ℂ) (n : ℕ) :
    (iteratePoly c (n+1)).comp (C s*X) =
      (iteratePoly c n).comp (C c+C (s^2)*X^2) := by
  rw [iteratePoly_succ_comp, comp_assoc]
  congr 1
  simp [map_pow] <;> ring

/-- The transported spatial tangent scale along the actual orbit. -/
def transport (c x σ : ℂ) : ℕ → ℂ
  | 0 => σ
  | n+1 => 2 * orbit c x n * transport c x σ n

def charge (c x σ : ℂ) (n : ℕ) : ℂ :=
  transport c x σ n / (2 * orbit c x n)

theorem transport_add (c x σ : ℂ) (r n : ℕ) :
    transport c x σ (r+n) =
      transport c (orbit c x r) (transport c x σ r) n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Nat.add_succ, transport, orbit_add, ih]

theorem charge_shift (c x σ : ℂ) (r n : ℕ) :
    charge c x σ (r+n) =
      charge c (orbit c x r) (transport c x σ r) n := by
  simp only [charge, transport_add, orbit_add]

theorem transport_ne_zero (c x σ : ℂ) (n : ℕ) (hσ : σ ≠ 0)
    (hx : ∀ j < n, orbit c x j ≠ 0) : transport c x σ n ≠ 0 := by
  revert hx
  induction n with
  | zero => intro _; exact hσ
  | succ n ih =>
    intro hx
    exact mul_ne_zero (mul_ne_zero (by norm_num) (hx n (by omega)))
      (ih (fun j hj => hx j (by omega)))

private theorem recenter_step (c x t : ℂ) (P : ℂ[X]) (hx : x ≠ 0) :
    (C x + C t*P)^2 + C c =
      C (x^2+c) + C (2*x*t)*(P + C (t/(2*x))*P^2) := by
  have hs : (2*x*t)*(t/(2*x)) = t^2 := by
    field_simp [hx] <;> ring
  calc
    (C x + C t*P)^2 + C c =
        C (x^2+c) + C (2*x*t)*P + C (t^2)*P^2 := by
          simp [map_add, map_mul, map_pow] <;> ring
    _ = C (x^2+c) + C (2*x*t)*(P + C (t/(2*x))*P^2) := by
      rw [← hs, map_mul]
      ring

/-- The transported-coordinate composition is exactly an actual iterate. -/
theorem flight_actual_identity (c x σ : ℂ) (n : ℕ)
    (hx : ∀ j < n, orbit c x j ≠ 0) :
    (iteratePoly c n).comp (C x + C σ*X) =
      C (orbit c x n) + C (transport c x σ n)*flight (charge c x σ) n := by
  revert hx
  induction n with
  | zero => intro _; simp [iteratePoly, orbit, transport, flight]
  | succ n ih =>
    intro hx
    have hprev := ih (fun j hj => hx j (by omega))
    calc
      (iteratePoly c (n+1)).comp (C x + C σ*X) =
          ((iteratePoly c n).comp (C x + C σ*X))^2+C c := by
            simp [iteratePoly]
      _ = (C (orbit c x n) + C (transport c x σ n)*
          flight (charge c x σ) n)^2+C c := by rw [hprev]
      _ = C (orbit c x (n+1)) + C (transport c x σ (n+1))*
          flight (charge c x σ) (n+1) := by
            exact recenter_step c (orbit c x n) (transport c x σ n)
              (flight (charge c x σ) n) (hx n (by omega))

/-- An actual iterate, with source and target centered and tangent-normalized. -/
def normalizedActualFlight (c x σ : ℂ) (n : ℕ) : ℂ[X] :=
  C ((transport c x σ n)⁻¹) *
    ((iteratePoly c n).comp (C x + C σ*X) - C (orbit c x n))

theorem normalizedActualFlight_eq_flight (c x σ : ℂ) (n : ℕ)
    (hσ : σ ≠ 0) (hx : ∀ j < n, orbit c x j ≠ 0) :
    normalizedActualFlight c x σ n = flight (charge c x σ) n := by
  have ht := transport_ne_zero c x σ n hσ hx
  unfold normalizedActualFlight
  rw [flight_actual_identity c x σ n hx]
  simp only [add_sub_cancel_left]
  rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ ht, map_one, one_mul]

/-- The exact jet belongs to the actual normalized iterate polynomial. -/
theorem normalizedActualFlight_hasJet (c x σ : ℂ) (n : ℕ)
    (hσ : σ ≠ 0) (hx : ∀ j < n, orbit c x j ≠ 0) :
    HasJet (normalizedActualFlight c x σ n) (flightJet (charge c x σ) n) := by
  rw [normalizedActualFlight_eq_flight c x σ n hσ hx]
  exact flight_hasJet (charge c x σ) n

/-- A consecutive subflight beginning at its actual moving orbit point. -/
def actualBlock (c x σ : ℂ) (r n : ℕ) : ℂ[X] :=
  normalizedActualFlight c (orbit c x r) (transport c x σ r) n

theorem actualBlock_eq_flight (c x σ : ℂ) (r n : ℕ)
    (hσ : σ ≠ 0) (hx : ∀ j < r+n, orbit c x j ≠ 0) :
    actualBlock c x σ r n = flight (fun j => charge c x σ (r+j)) n := by
  have ht : transport c x σ r ≠ 0 :=
    transport_ne_zero c x σ r hσ (fun j hj => hx j (by omega))
  have hshift : ∀ j < n, orbit c (orbit c x r) j ≠ 0 := by
    intro j hj
    rw [← orbit_add]
    exact hx (r+j) (by omega)
  unfold actualBlock
  rw [normalizedActualFlight_eq_flight c (orbit c x r) (transport c x σ r) n ht hshift]
  congr 1
  funext j
  exact (charge_shift c x σ r j).symm

theorem actualBlock_hasJet (c x σ : ℂ) (r n : ℕ)
    (hσ : σ ≠ 0) (hx : ∀ j < r+n, orbit c x j ≠ 0) :
    HasJet (actualBlock c x σ r n)
      (flightJet (fun j => charge c x σ (r+j)) n) := by
  rw [actualBlock_eq_flight c x σ r n hσ hx]
  exact flight_hasJet (fun j => charge c x σ (r+j)) n

/-- The normalization at the critical point is the even pullback of the
actual critical-value flight. This is an equality of entire polynomials. -/
theorem critical_return_identity (c s : ℂ) (n : ℕ) (hs : s ≠ 0)
    (hx : ∀ j < n, orbit c c j ≠ 0) :
    (iteratePoly c (n+1)).comp (C s*X) =
      C (orbit c 0 (n+1)) + C (transport c c (s^2) n)*
        (normalizedActualFlight c c (s^2) n).comp (X^2) := by
  rw [critical_substitution_identity, critical_orbit_shift,
    normalizedActualFlight_eq_flight c c (s^2) n (pow_ne_zero 2 hs) hx]
  have h := congrArg (fun P : ℂ[X] => P.comp (X^2))
    (flight_actual_identity c c (s^2) n hx)
  simpa only [comp_assoc, add_comp, mul_comp, C_comp, X_comp] using h

end QuadraticFlightJet

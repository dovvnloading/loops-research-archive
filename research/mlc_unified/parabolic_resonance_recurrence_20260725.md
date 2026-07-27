# Formal resonance recurrence for the quadratic satellite germ

## Purpose

The commutation lemma proves the all-order cancellation

`g^q(w) = w + O(w^(q+1))`

for `g(w) = lambda*w + w^2` and primitive `lambda` of order `q`. The
remaining local question is whether the coefficient of `w^(q+1)` can ever
vanish. This note records an exact finite recurrence that isolates that
question without treating numerical evidence as an all-q theorem.

## Formal calculation

Let

`phi(z) = z + b_2 z^2 + b_3 z^3 + ...`

and conjugate `g` formally through degree `q` to its resonant normal form

`h(z) = lambda*z + A*z^(q+1) + O(z^(q+2))`.

Comparing `g(phi(z))` with `phi(h(z))` gives, for `2 <= n <= q`,

`b_n = S_n/(lambda^n-lambda)`,

where

`S_n = sum_{i=1}^{n-1} b_i*b_(n-i)` and `b_1=1`.

At the first resonant degree,

`A = S_(q+1) = sum_{i=1}^q b_i*b_(q+1-i)`.

The q-th iterate of the normal form has coefficient

`[w^(q+1)] h^q = q*lambda^(q-1)*A`.

Consequently, the desired all-q nondegeneracy statement is equivalent to
`A != 0` in the cyclotomic field `Q(lambda)` for every primitive q-th root.

The denominators in the recurrence are nonzero for `2 <= n <= q`, because
primitivity rules out `lambda^(n-1)=1` in that range. Thus this is an exact
finite algebraic reduction, not a floating-point test.

## Exact validation

`validate_parabolic_resonance_recurrence.py` evaluates the recurrence and
independently expands the iterate in `Q[x]/(Phi_q(x))`. It checks agreement
for q=2,...,16 and checks that the resonant coefficient is nonzero there.
The independent direct expansion agrees with `q*x^(q-1)*A` at every checked
order.

This strengthens the local record in two ways:

1. it gives a reproducible algebraic expression for the first parabolic
   coefficient rather than only an iterate expansion; and
2. it identifies the exact remaining local proof: a uniform nonvanishing
   theorem for this recurrence.

## All-q nondegeneracy from the critical-point count

The remaining local statement can be closed by the standard parabolic-basin
critical-point count. For a rational map with a parabolic fixed point of
multiplier a primitive q-th root, if the multiplicity of the fixed point for
the q-th iterate is `m+1`, then `m=kq` and the immediate parabolic basins form
`k` periodic cycles of length q. Every periodic cycle of immediate parabolic
basins contains a critical point of the original map. These are the standard
root-of-unity basin facts recorded, for example, in Geyer's notes (Corollary
11.6 and Corollary 11.8), and the immediate-basin critical-point statement is
also the subject of Bergweiler's paper.

Apply this to the degree-two polynomial `g(w)=lambda*w+w^2`. Its only finite
critical point is `-lambda/2`; the other critical point on the sphere is
infinity, which is the superattracting basin of a polynomial and is not in the
parabolic basin of 0. Therefore at most one periodic cycle of immediate
parabolic basins can be attached to 0. Since a parabolic point has at least
one such cycle, `k=1`, hence `m=q`. Therefore

`g^q(w)-w = C_q*w^(q+1) + O(w^(q+2))`

with `C_q != 0` for every primitive q-th root `lambda`. This proves the
all-q nondegeneracy of this specific quadratic anchor. It is stronger than
the finite recurrence certificate and does not require a sign formula for the
cyclotomic recurrence.

References checked:

- <https://www.math.montana.edu/geyer/2016-fall-m597/materials/s2016-complex-dynamics-notes.pdf>
- <https://www.cambridge.org/core/journals/ergodic-theory-and-dynamical-systems/article/abs/on-the-number-of-critical-points-in-parabolic-basins/BB15221F8AB70937D675B98CFD9585F1>

## Boundary

The all-q local nondegeneracy is now closed by the basin-count argument, while
the recurrence remains a useful exact machine certificate for q=2,...,16.
This does not provide uniform cylinder/Lavaurs estimates, Ecalle-phase
transport, or realization of an arbitrary infinite satellite tower. The local
result still cannot be promoted to a global cylinder bridge; the arbitrary
unbounded-satellite comparison, virtual-Molecule interpolation, global
parameter rigidity, and MLC remain open.

Machine certificate: `validate_parabolic_resonance_recurrence.py`; output:
`parabolic_resonance_recurrence_20260725.json`; original artifacts are not
written.

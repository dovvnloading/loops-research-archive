# All-order resonance cancellation at a primitive satellite anchor

## Statement

Let `q >= 2`, let `lambda` be a primitive q-th root of unity, and let

`g(w) = lambda*w + w^2`.

Then `g^q(w) = w + O(w^(q+1))`. Equivalently, the coefficients of
`w^2, ..., w^q` in the q-th iterate vanish for every q, not merely for a
finite computer sweep.

This is only the cancellation half of the local parabolic anchor. It does
not prove that the coefficient of `w^(q+1)` is nonzero for every q, does not
give uniform cylinder/Lavaurs estimates, and does not address the global MLC
parameter bridge.

## Proof

Write `F = g^q`. Since iterates commute, `F o g = g o F`. Also
`F'(0) = lambda^q = 1`. If `F` is not the identity germ, let `m >= 2` be
the least index with

`F(w) = w + a_m*w^m + O(w^(m+1))`, with `a_m != 0`.

Expanding the two sides of the commutation identity through degree `m`
gives

`F(g(w)) = lambda*w + w^2 + a_m*lambda^m*w^m + O(w^(m+1))`,

and

`g(F(w)) = lambda*w + w^2 + a_m*lambda*w^m + O(w^(m+1))`.

Therefore `a_m*(lambda^m-lambda)=0`, so `lambda^(m-1)=1`. Primitivity of
`lambda` implies `q | (m-1)`, hence `m >= q+1`. The exceptional possibility
`F = id` cannot occur for this polynomial germ: an identity germ would make
the polynomial iterates `g^q` and `id` agree on a neighborhood and therefore
globally, contradicting `deg(g^q)=2^q`. Thus the least nonzero term exists and
the claimed cancellation follows.

The same resonance restriction is the standard local fact used in the
parabolic-degeneracy definition: for a primitive q-th multiplier, the first
possible term of `g^q-id` has degree `nu*q+1` for some positive integer `nu`.
See Buff--Ecalle--Epstein, *Limits of Degenerate Parabolic Quadratic Rational
Maps*, pp. 7--9, for that formulation and the distinction between
nondegenerate (`nu=1`) and degenerate parabolic points:

<https://www.math.univ-toulouse.fr/~buff/Preprints/DegenerateParabolic/DegenerateParabolic.pdf>

## Closure boundary

The finite exact sweep in `validate_parabolic_root_family.py` confirms
nonzero degree-(q+1) coefficients for q=2,...,16. The commutation lemma
extends the vanishing range to all q, and the companion
`parabolic_resonance_recurrence_20260725.md` closes all-q nondegeneracy using
the standard critical-point count for periodic cycles of immediate parabolic
basins. This local result still does not provide a uniform parabolic bridge:
the arbitrary unbounded-satellite cylinder-to-parameter transfer and
virtual-Molecule interpolation/rigidity remain open global obligations.

Machine certificate: `validate_parabolic_commutation_lemma.py`.
It returns `PARABOLIC_COMMUTATION_RESONANCE_VALID` and writes no original
artifact.

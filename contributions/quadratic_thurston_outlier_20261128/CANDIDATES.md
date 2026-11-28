# Candidate screen before formalization

This file records the candidate screen begun before formalization and its
unsuccessful outcome. No candidate below is submitted as a new theorem.

## A. The archive's terminal gap

The written implication `UPTCR_IMPLIES_MLC` assumes the open
`UNIVERSAL_PROTECTED_TOWER_CLOSURE`. The latter is a universal six-clause
package for every infinitely renormalizable quadratic. The actual construction
already stops at Clause 1; later rigidity and parameter-neighborhood clauses
are also hypotheses. See the packet note and the archive's
`mlc_closure_proposition.md`, Sections 5--7.

## B. Rejected classical consequences

1. **Recover a periodic quadratic center from the trace of its Thurston
   cotangent operator.** Rejected. For exact period at least three, the
   coefficient formula in Buff--Epstein--Koch, Proposition 9.7, immediately
   gives `tr(T)=-(1+c)/(2c)`. Its injectivity is elementary; it is not a new
   rigidity theorem.

2. **Relate the determinant at 1 to the derivative of the critical return
   equation.** Rejected. This is already Buff--Epstein--Koch, Proposition 9.8.

3. **Prove strict contraction from inverse-sheet cancellation or a finite
   pole-support obstruction.** Rejected. These are covered by the classical
   contraction principle and DeMarco--Koch--McMullen's four-point criterion
   (Proposition 3.1).
   Quantitative triangle-inequality stability alone would not supply a new
   actual-family theorem.

4. **Use angled internal addresses to separate combinatorial classes.**
   Rejected. This is already Schleicher's internal-address theory. Separating
   points *within* a class needs an additional analytic rigidity theorem;
   it is not implied by the combinatorial encoding.

5. **Prove center simplicity or critical-collision transversality.**
   Rejected both as classical mathematics and as duplicate archive work:
   `QuadraticCriticalTransversality.lean` and
   `QuadraticCriticalCoordinates.lean` already contain those results.

6. **Quantify an inverse-operator degeneration near the Chebyshev
   parameter.** Not pursued: even if its sharp norm asymptotic were new, its
   geometric-limit obstruction would conflict with the user's exclusions.
   The elementary pushforward formula alone is not new.

## C. Unproved candidate: spectral multiplicity

The initial search asked for an intrinsic critical-orbit condition guaranteeing
simple spectrum for an infinite class of actual quadratic centers, without
merely assuming a nonzero discriminant. Its concrete candidate was:

> For every k >= 2, if the critical point of f_c(z)=z^2+c has exact period
> 2^k, then the actual Thurston cotangent operator has simple spectrum.

A proposed sufficient arithmetic step was that this simplicity would already
be visible in characteristic-two reduction of the normalized polynomial.
Neither statement was proved. No formalization was started.

Buff--Epstein--Koch, Section 10.3, Question 6 asks whether the characteristic
polynomial has simple roots for every periodic unicritical polynomial. Thus
a proved genuinely new class would go beyond their general coefficient formula.
A finite collection of computer checks, or a generic resultant criterion, does
not by itself meet the mandate.

The broader assertion of universally squarefree reduction fails the exploratory
period-nine test. The integer-only program and its output are preserved as
`explore_reduced_spectrum.py` and `EXPLORED_REDUCED_SPECTRUM.txt`. Run:

```sh
python contributions/quadratic_thurston_outlier_20261128/explore_reduced_spectrum.py
```

The completed scope is periods 3 through 16. It finds nine reduced collisions
among 252 exact-period-nine parameters. In the field defined by
`c^9+c^4+c^2+c+1=0`, the gcd of the reduced normalized polynomial and its
derivative is `v^2+1+c+c^5`. The program checks this and the explicit repeated
root. This is not a repeated complex eigenvalue and says nothing about a
parameter fiber. A finite arithmetic computation using an existing spectral
formula does not meet the requested novelty threshold, so it is retained only
as a record of a rejected approach.

## D. Outcome

No candidate survived both the novelty screen and a complete mathematical
proof. No Lean theorem was added or compiled. The draft is closed according
to `AGENTS.md`, with its investigation history preserved and no requested
change to any ledger status.

## Primary sources checked

- Xavier Buff, Adam L. Epstein, Sarah Koch, *Eigenvalues of the Thurston
  operator*, arXiv:1707.01990, especially Sections 4, 9 and 10.3:
  https://websites.umich.edu/kochsc/eigenvalues.pdf
- Laura G. DeMarco, Sarah C. Koch, Curtis T. McMullen,
  *On the postcritical set of a rational map*,
  Proposition 3.1:
  https://people.math.harvard.edu/~ctm/papers/home/text/papers/postc/postc.pdf
- Dierk Schleicher, *Internal addresses of the Mandelbrot set and Galois
  groups of polynomials*, Arnold Mathematical Journal (2017):
  https://amj.math.stonybrook.edu/html-articles/Files-2015-2024/16-42/

This is a bounded literature comparison, not a priority certification.
No priority claim is made for the exploratory calculation.

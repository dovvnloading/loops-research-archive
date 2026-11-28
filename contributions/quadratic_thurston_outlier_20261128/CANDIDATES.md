# Candidate screen before formalization

This file records rejected statements as well as live candidates. Nothing below
is yet claimed as a new theorem. No candidate is being formalized before this
screen.

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
   contraction principle and McMullen's four-point criterion (Proposition 3.1).
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

## C. Live investigation: spectral multiplicity

**Candidate statement, before formalization.** Find an intrinsic, explicitly
checkable critical-orbit condition implying that the actual quadratic Thurston
cotangent operator has simple spectrum, valid for a nontrivial infinite class
of exact critical periods. The condition must be proved for actual quadratic
centers and must not merely assume the desired discriminant is nonzero.

Buff--Epstein--Koch, Section 10.3, Question 6 asks whether the characteristic
polynomial has simple roots for every periodic unicritical polynomial. Thus
a proved genuinely new class would go beyond their general coefficient formula.
A finite collection of computer checks, or a generic resultant criterion, does
not by itself meet the mandate.

Current exploratory computations suggest that reduction modulo 2 is not
universally squarefree: exact period nine already supplies failures. These
computations are exploratory only, have not been formally verified, and are
not a theorem or a result submitted for review.

## Primary sources checked

- Xavier Buff, Adam L. Epstein, Sarah Koch, *Eigenvalues of the Thurston
  operator*, arXiv:1707.01990, especially Sections 4, 9 and 10.3:
  https://websites.umich.edu/kochsc/eigenvalues.pdf
- Curtis T. McMullen, *On the postcritical set of a rational map*,
  Proposition 3.1:
  https://people.math.harvard.edu/~ctm/papers/home/text/papers/postc/postc.pdf
- Dierk Schleicher, *Internal addresses of the Mandelbrot set and Galois
  groups of polynomials*, Arnold Mathematical Journal (2017):
  https://amj.math.stonybrook.edu/html-articles/Files-2015-2024/16-42/

This is a bounded literature comparison, not a priority certification.
All candidates remain subject to independent mathematical review.

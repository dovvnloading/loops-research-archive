# Retained candidate, stated before Lean formalization

Historical pre-formalization record, committed as `773f3d5bdb76d4237999479c1392cd736bf6d637`. At that point the candidate was retained after the primary-source pre-check below, and no new Lean proof or successful CI run was claimed. See [NOTE.md](NOTE.md) for the implementation and current validation status.

## Candidate theorem: conditional mixed susceptibility forces local connectivity

Write
\[
P_0(c)=0,\qquad P_{n+1}(c)=P_n(c)^2+c,\qquad
M=\{c\in\mathbb C:\sup_n|P_n(c)|<\infty\}.
\]
For two actual quadratic parameters define
\[
D_0(c,d)=1,\qquad
D_n(c,d)=\prod_{j=1}^n(P_j(c)+P_j(d)),\qquad
Q_n(c,d)=1+\sum_{k=1}^n D_k(c,d)^{-1}.
\]

**Theorem to formalize.** Let \(Y\) be a Hausdorff locally connected space
and let \(q:M\to Y\) be a continuous monotone surjection: every inverse
image of a point is connected. Fix \(c\in M\), and put
\(F=q^{-1}(q(c))\), viewed as a subset of the actual complex parameter plane.
Suppose:

1. \(P_j(c)+P_j(d)\ne0\) for every \(d\in F\) and every \(j\ge1\);
2. the complex functions \(d\mapsto Q_n(c,d)\) converge **uniformly on
   \(F\)** to a complex-valued function \(L\);
3. \(L(c)\ne0\).

Then \(F=\{c\}\). Moreover, \(M\) has a basis of relatively open connected
neighborhoods at \(c\): for every neighborhood \(U\) of \(c\) in the
subspace \(M\), there is an open connected neighborhood \(V\) with
\(c\in V\subset U\).

Convergence here means ordinary convergence in \(\mathbb C\). No hypothesis
bounds the series of absolute values. In particular, condition 2 is not
absolute derivative summability, and the theorem will not be presented as a
new proof of a classical absolute-summability result.

The conclusion is pointwise local connectivity of the genuine bounded
critical-orbit locus. The supplied map \(q\) is an explicit hypothesis;
it is not an arbitrary relation silently renamed the combinatorial fiber.
The construction and identification of the classical pinched-disk quotient
are not part of this theorem. Its usual monotone-quotient setting motivates
the hypotheses, but the Lean theorem must prove the actual local-connectivity
conclusion without assuming that identification.

## Proof idea that distinguishes the candidate

The step to test is finite **parameter secant transport**, not differentiation
of a holomorphic family of conjugacies. Subtract the two quadratic recurrences.
Whenever the displayed products are nonzero, an induction gives the exact
identity
\[
\frac{P_{n+1}(c)-P_{n+1}(d)}{D_n(c,d)}
=(c-d)Q_n(c,d).
\tag{1}
\]
If \(Q_n(c,d)\) converges, its consecutive differences show
\(D_n(c,d)^{-1}\to0\). Both actual critical orbits are bounded. Consequently
the left-hand side of (1) tends to zero. For \(d\ne c\), this forces
\[
L(d)=0.
\tag{2}
\]
Each finite sum is continuous on \(F\), because the finitely many mixed
factors do not vanish there. Uniform convergence therefore makes \(L\)
continuous on \(F\). Equations (2) and \(L(c)\ne0\) isolate \(c\) in
\(F\). Connectedness of the fiber then forces \(F=\{c\}\).

The remaining implication is proved topology, not an assumed rigidity
bridge. The actual set \(M\) is compact: its closedness follows from the
archive's proved continuity and bounded-orbit characterization of the
quadratic escape function, and its boundedness follows from the elementary
escape estimate. Thus \(q\) is closed. Given a neighborhood \(U\) of
\(c\), the closed set \(q(M\setminus U)\) misses \(q(c)\).
Choose a connected open neighborhood of \(q(c)\) avoiding that set.
A closed monotone surjection has connected inverse images of connected
sets, so its inverse image is the required open connected neighborhood
inside \(U\).

This creates an actual-family reduction: a hypothetical nontrivial monotone
fiber cannot support the stated uniform conditional mixed susceptibility with
nonzero diagonal value. The new move being tested is the two-parameter
identity and its use on a fiber where no analytic parameter motion is
assumed. The elementary algebra and the supporting topology are not
individually claimed as new results.

## Primary-source pre-check

### Absolute summability: rejected specialization

Juan Rivera-Letelier, *Rational maps with decay of geometry: rigidity,
Thurston's algorithm and local connectivity*, IMS Preprint 2000/9,
Proposition 1.4(1), Theorem D and its following corollary:
https://www.math.stonybrook.edu/preprints/ims00-09.pdf .

On the diagonal,
\(D_n(c,c)=(f_c^n)'(c)\). Replacing condition 2 with a uniform sum of
absolute values would impose exponent-one critical derivative summability.
Rivera-Letelier's results already imply local connectivity in that regime.
That candidate is discarded.

### Conditional one-orbit sums: the closest result located

Carlos Cabrera, Peter Makienko and Alfredo Poirier,
*On Nörlund–Voronoi Summability and Instability of Rational Maps*,
Arnold Mathematical Journal 6 (2020), 523–549,
Proposition 1.2 and Corollary 1.3:
https://amj.math.stonybrook.edu/pdf-Springer-final/020-0158.pdf .

Those results use one-map derivative reciprocals and infinitesimal
deformations to obtain structural instability. Their proof does not give
(1) for two distinct parameters in a possibly nontrivial fiber and does not
conclude triviality of that fiber or local connectivity at its points.
The retained statement is not a specialization of their instability
conclusion.

### Derivative growth alone does not supply the missing implication

Huaibin Li and Weixiao Shen,
*On non-uniformly hyperbolicity assumptions in one-dimensional dynamics*,
Theorem A, arXiv:0911.0464:
https://arxiv.org/abs/0911.0464 .

Their complex-polynomial derivative-growth/backward-contraction result
assumes at most finite renormalizability and hyperbolic periodic points.
These hypotheses are absent from the retained statement. The theorem
therefore does not by itself cover the remaining infinitely renormalizable
regime.

### Finite transversality and the archive

Genadi Levin, Weixiao Shen and Sebastian van Strien,
*Positive Transversality via Transfer Operators and Holomorphic Motions with
Applications to Monotonicity for Interval Maps*, Nonlinearity 33 (2020):
https://arxiv.org/pdf/1902.06732 .

Finite transfer determinants and infinitesimal critical-relation
transversality are close antecedents, but the present hypothesis concerns
conditional convergence of mixed finite secants on an entire parameter
fiber, with an actual local-connectivity conclusion.

The archive's `QuadraticCollisionFactorization.lean` factors two initial
points for a fixed parameter. Its finite spatial secants do not give the
mixed-parameter conclusion above. The new proof will use the actual
quadratic orbit already defined in `QuadraticEscape.lean`, without KKL
Waves, marked widths, collars, protected carriers, mapping telescopes or
tip-family constructions.

**Pre-check verdict:** retain the theorem for formalization. No direct
classical implication was found in the sources checked. This is a bounded
literature check, not a certificate that no related statement has ever
appeared. The proof and its scope must remain open to mathematical review.

## Exact remaining limits

- The theorem is a sufficient criterion, not MLC.
- No infinitely renormalizable parameter satisfying the criterion has been
  exhibited. Verifying its hypotheses for a new parameter class remains open.
- The canonical pinched-disk quotient is not constructed in Lean here; any
  quotient used by the theorem must satisfy its stated topological hypotheses.
- A proof only of (1), or only of a theorem about an arbitrary compact space,
  would not fulfill this packet. The combined Lean theorem must conclude
  pointwise local connectivity for the actual quadratic bounded-orbit set.
- The universal tower closure in the archive remains open. No ledger status
  change is proposed.

---
ledger: MLC
result: partial
ai: OpenAI ChatGPT, GPT-6 Astra Pro
human_review: none
---

<a id="quadratic-outlier-rigidity-20261128"></a>

# Two-quadratic parameter rigidity with continuity on one real line

## Claim

Let \(c,d\in\mathbb C\), and let \(h:\mathbb C\to\mathbb C\) be a function whose restriction to the real axis is continuous. Assume, for every \(z\in\mathbb C\),
\[
h(z^2+c)=h(z)^2+d,\qquad
h(z^2+c+1)=h(z)^2+d+1.
\tag{1}
\]
Then
\[
d=c\quad\text{or}\quad d=\overline c.
\tag{2}
\]

Continuity elsewhere, injectivity, surjectivity, properness, holomorphicity, quasiconformality, and a normalization at infinity are not hypotheses.

The companion theorem concerns the actual Mandelbrot set
\[
M=\{c\in\mathbb C:\exists B\in\mathbb R\
 \forall n\in\mathbb N,\ |f_c^n(0)|\le B\},
\qquad f_c(z)=z^2+c.
\]
Let \(q:M\to Y\) be a continuous surjection with preconnected fibers, where \(Y\) is Hausdorff and locally connected. Fix \(c\in M\). Suppose every \(d\in q^{-1}(q(c))\) admits an \(h\) satisfying (1) and the stated real-axis continuity. Then
\[
q^{-1}(q(c))=\{c\},
\]
and every relative neighborhood \(U\) of \(c\) in \(M\) contains a relatively open connected neighborhood \(V\) of \(c\).

Thus a nontrivial connected parameter fiber necessarily contains a parameter for which the two simultaneous intertwining equations have no solution with this weak regularity. This is an actual-family conditional rigidity criterion and obstruction.

**Validation status at this note revision:** all three Lean modules and their registrations have been committed; the existing strict CI build is running. No successful compilation is claimed until its log and transitive proof-dependency audit have been inspected.

## Evidence

### 1. Candidate and classical screen preceded formalization

The first draft PR was opened with the research record. [CANDIDATE.md](CANDIDATE.md), committed as \`12d4434316d33ebbc864815dbbae6c694dbdf38d\`, records the first candidate and rejects its homeomorphism version as a classical consequence. The stronger parameter statement with continuity only on the real axis was then recorded in [SHARPENED_CANDIDATE.md](SHARPENED_CANDIDATE.md), commit \`bcc4cf53923482f6c5b42250cf104e8480077c1d\`, before any new Lean source.

The first source commit is \`a549bf31334050f3a4d93c08a93a28c2b453feb3\`. The original full-map classification and its inverse-branch flow proof are not claimed as part of the retained result. The implemented theorem is the sharper parameter statement above.

### 2. Exact quadratic proof

Since every complex number is a square, comparing (1) gives
\[
h(w+1)=h(w)+1.
\tag{3}
\]
Induction gives covariance under every integer translation.

For \(r=p/q\in\mathbb Q\), with \(q>0\), the identity
\[
(r+q)^2+c=(r^2+c)+(2p+q^2)
\]
contains an integer translation on the output side. Apply (3) and the first equation of (1) in both orders:
\[
(h(r)+q)^2+d=h(r)^2+d+2p+q^2.
\]
Cancellation yields \(h(r)=r\). Density of the rationals and continuity on the real axis imply
\[
h(x)=x\qquad(x\in\mathbb R).
\tag{4}
\]
In particular \(h(0)=0\), and the first equation of (1) at zero gives \(h(c)=d\).

For \(t\ge0\), evaluate at the real square root of \(t\):
\[
h(c+t)=d+t.
\]
For arbitrary real \(t\), add a sufficiently large integer and use (3). Therefore
\[
h(c+t)=d+t\qquad(t\in\mathbb R).
\tag{5}
\]
The first quadratic maps the real axis to a horizontal half-line through its critical value; integer covariance extends its rigidity to the full horizontal line.

Applying the same equation at \(iy\), and then (5), gives
\[
h(iy)^2=-y^2.
\tag{6}
\]
Write \(c=a+ib\), and set \(y=-b/2\). The choice of this point is the parameter-recovery step:
\[
(1+iy)^2+c=1-y^2+a\in\mathbb R.
\]
Its image is controlled by (4), while (3) gives \(h(1+iy)=1+h(iy)\). Hence
\[
1-y^2+a=(1+h(iy))^2+d.
\]
Use (6) to obtain \(a=d+2h(iy)\), and then
\[
(d-a)^2=-b^2,\qquad
(d-c)(d-\overline c)=0.
\]
This proves (2).

The proof uses global functional identities of two specified quadratic maps. It does not infer a dynamical conclusion from finite critical-orbit samples or from an abstract sampling criterion.

### 3. Proved implication to actual Mandelbrot neighborhoods

For the supplied quotient \(q\), map its fiber into the complex parameter plane. The image is preconnected because the subtype inclusion is continuous. Applying (2) to every point puts it inside
\[
\{c,\overline c\}.
\]
A nontrivial preconnected set in a Hausdorff space is infinite, so this finite set contains at most one fiber point. The fiber contains \(c\), hence it is exactly \(\{c\}\).

The actual bounded-orbit locus \(M\) is proved compact. The proof uses the archive's ordinary quadratic escape characterization only to prove closedness and a coarse uniform bound \(|c|\le3\). It uses no Green-potential density hypothesis.

The already proved classical lemma in \`QuadraticMonotoneFiberTopology\` then applies: a singleton fiber of a continuous monotone surjection from a compact space to a Hausdorff locally connected space gives a connected open neighborhood basis at that domain point. Thus the endpoint is a theorem about the actual subspace topology of \(M\), not an isolated algebraic assertion.

### 4. Lean declarations and integration

| Module | Main declarations |
|---|---|
| [QuadraticTwinReal.lean](../../formalization/weighted/QuadraticTwinReal.lean) | \`integer_covariance\`, \`fixes_rat\`, \`fixes_real\` |
| [QuadraticTwinSemiconjugacy.lean](../../formalization/weighted/QuadraticTwinSemiconjugacy.lean) | \`unit_translation\`, \`critical_line\`, \`imaginary_square\`, \`parameter_eq_or_conj\` |
| [QuadraticTwinMLC.lean](../../formalization/weighted/QuadraticTwinMLC.lean) | \`monotone_fiber_eq_singleton_of_twin\`, \`exists_parameter_without_twin_of_nontrivial_fiber\`, \`locallyConnectedAt_of_twin\` |

The final theorem has the explicit conclusion
\[
\forall U\in\mathcal N_M(c)\ \exists V\subseteq M:
  V\subseteq U,\quad V\text{ open in }M,\quad c\in V,\quad V\text{ connected}.
\]
Its \`TwinFiber\` premise contains the two functional equations and real-axis continuity, not parameter equality or singletonness.

All modules are registered as default targets in the existing Mathlib package, with every public theorem listed in the theorem index and each source listed in the source index. No workflow, audit rule, ledger status, or existing theorem is changed. The toolchain is Lean 4.32.0 with the repository's pinned Mathlib.

Local Lean is unavailable and the scratch filesystem cannot hold a checkout. The existing GitHub CI is the compiler and proof-dependency judge. The first weighted run is [46138258781](https://github.com/dovvnloading/loops-research-archive/actions/runs/46138258781); its result will be recorded after completion.

## Dependencies

### Exact archive gap

The starting point is main at \`0678a66d0915f73214db7899c9591ebb56afb67b\`.

The precise open hypothesis is **\`UNIVERSAL_PROTECTED_TOWER_CLOSURE\`**, the **Universal Protected-Tower Compactness and Rigidity Proposition (UPTCR)** in [the closure proposition, section 5](../../research/mlc_unified/mlc_closure_proposition.md). Its constants are chosen before the polynomial and tower, and every infinitely quadratic-like renormalizable quadratic must satisfy all six clauses:

1. canonical actual marked construction;
2. exact analytic realization;
3. uniformly finite response state with quantitative comparisons;
4. a universal backward transition with net factor greater than one and controlled errors;
5. coercive marked compactness;
6. rigidity giving singleton parameter fibers and connected relative neighborhoods.

The constants must be independent of periods, rotations, continued-fraction depth, horizons, marking counts, counters, stack lengths, and regime ordering. Parameter-by-parameter finite data do not supply this quantifier strength.

The ledger marks **\`UPTCR_IMPLIES_MLC\`** as a proved **conditional** implication, with UPTCR explicitly open. The written implication is Theorem 7.2 of that note. \`ResearchLedger.lean\` audits the documentary dependency record; it does not construct the missing analytic package. The present result does not discharge UPTCR or any of its six clauses.

### Formal dependencies

- Mathlib: complex algebraic closure, rational algebra and density, continuity, compactness, and connectedness.
- \`QuadraticEscape\`: actual quadratic orbit and ordinary closedness/compactness support.
- \`QuadraticMonotoneFiberTopology\`: the independently proved classical compact-monotone implication.
- The ordinary Mandelbrot compactness proof is reproduced with attribution from the earlier \`QuadraticMixedSusceptibilityMLC\` source, but none of the susceptibility modules is imported.
- No excluded geometric machinery, critical-orbit mixed products, or projective jets enter the new proof.

### Closest classical results and rejected alternatives

- **Schleicher**, *Internal Addresses of the Mandelbrot Set and Galois Groups of Polynomials*, Theorem 3.9: angled addresses classify combinatorial classes. They do not split the points of an unresolved class. [Primary text](https://armj.math.stonybrook.edu/html-articles/Files-2015-2024/16-42/).
- **Buff–Epstein–Koch**, *Eigenvalues of the Thurston Operator*, Theorems 1.4–1.5 and section 9.4: unicritical spectral bounds, accumulation, and characteristic formulas are already known. The finite-spectrum direction was discarded. [Primary author text](https://public.websites.umich.edu/kochsc/eigenvalues.pdf).
- **Rivera-Letelier**, *Rational Maps with Decay of Geometry: Rigidity, Thurston's Algorithm and Local Connectivity*, Theorem D and Appendix 9: recurrence-instability and Thurston-iteration routes have classical antecedents. [Primary text](https://www.math.stonybrook.edu/preprints/ims00-09.pdf).
- **Nakai**, *Separatrices for non solvable dynamics on \((\mathbb C,0)\)*, Proposition 1.7 and Theorem 4 / Theorem 5.1: rigidity of a linking homeomorphism for non-solvable germ groups. This defeats the initial homeomorphism-only candidate, which was discarded. The retained hypothesis requires no map of neighborhoods, inverse, germ isomorphism, or even global continuity. [Primary text](https://www.numdam.org/article/AIF_1994__44_2_569_0.pdf).
- **Cabrera–Makienko–Plaumann**, *Semigroup representations in holomorphic dynamics*, Proposition 7 and Theorems 13–14: full-semigroup bijections or isomorphisms have stronger hypotheses than the two intertwining equations used here. [Primary text](https://arxiv.org/pdf/1009.3000).
- **Schleicher**, *On Fibers and Local Connectivity of Mandelbrot and Multibrot Sets*, Proposition 3.5 and Corollary 3.6: the singleton-fiber/local-connectivity connection is classical supporting mathematics. [Primary text](https://arxiv.org/pdf/math/9902155).

The simple real square-and-unit-translation functional equation is also classical; rational normalization is not claimed as a new theme. The proposed originality is confined to the precise arbitrary-complex-parameter rigidity theorem with continuity on only one real line and its fully proved actual-fiber consequence. No checked source directly supplies this statement. A targeted source search cannot certify worldwide priority, and specialist review remains open.

## Boundary

- **This does not prove MLC or cover a newly verified class of infinitely renormalizable parameters.** The simultaneous intertwiner is an explicit additional condition. No construction from common kneading data, internal addresses, ray portraits, or renormalization data is provided.
- The quotient \(q\) is supplied with its topological hypotheses. A canonical pinched-disk quotient is not constructed or identified in Lean.
- Identity and conjugation supply the evident witnesses when \(d=c\) or \(d=\overline c\). Together with the parameter theorem, this explains the exact strength of the intertwiner condition. The remaining dynamical task is to obtain that condition from information weaker than parameter equality.
- No full classification of \(h\) is claimed by the implemented theorem. In particular, real-axis continuity is not being silently upgraded to global continuity.
- No ledger status change is proposed. H1–H4, UPTCR, and MLC remain open.
- The claimed mathematical contribution is conditional and the originality assessment is qualified. CI verifies proof correctness and dependencies, not literature priority or the unresolved applicability hypothesis.

## Attribution

Classical complex algebra, density, and connectedness arguments remain attributable to the standard literature and Mathlib. The topology endpoint is credited to the existing archive proof and classical fiber theory. The exact real-axis rational normalization and the quadratic crossing calculation were developed during this investigation and screened against the sources above. The earlier quarter-turn work in [PR #276](https://github.com/dovvnloading/loops-research-archive/pull/276) was inspected to avoid duplication and is neither imported nor used as a proof premise.

AI assistance comprised independent candidate screening, proof search, formalization, repository integration, and validation. Human review: none.

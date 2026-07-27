# Side-research library: assessment and integration record

Date: 2026-07-25  
Status: completed adversarial intake; selective integration only  
Global status: `MLC`, `UPTCR`, and `VAAPC-I` remain open

## 1. Scope and chain of custody

The intake directory

```text
research/mlc_unified/output/pdf/
```

contains the current manuscript and twenty-five side-research PDFs.  The
side-research files are not twenty-five independent proofs.  They are an
almost completely cumulative revision chain ending in

```text
mlc_subresearch_corrections_proposal_actual_closure_attempt_20260725_v24.pdf
```

The library was inventoried, hashed, and text-extracted by
`audit_side_research_library.py`.  The machine-readable custody record is

```text
external_inputs/side_research_library_20260725/manifest.json
```

and the extracted text is under

```text
tmp/pdfs/side_research_library_20260725/
```

Normalized-text prefix comparison shows that the revisions are cumulative,
apart from small edits in versions 4, 10, and 18.  Consequently, claims were
audited from the final revision and the earlier files were used only to
identify provenance and changed wording.  No claim was counted once per PDF.

The current manuscript at intake had SHA-256

```text
CBDA50A31513AEBE8AC5367A864031F5D698684246088147C7F26BEEEDB915E1
```

and 106 pages.  Historical hashes and historical ledger counts inside the
side PDFs are not current evidence.

## 2. Validation standard

Each side claim was assigned exactly one of the following dispositions.

1. **Retain as proved.**  A complete argument can be written from stated
   hypotheses, and every type and quantifier has been checked.
2. **Import with source scope.**  The exact theorem and its hypotheses were
   checked in a full primary source.  An abstract or a later report of an
   unavailable manuscript is insufficient.
3. **Duplicate.**  The claim is already represented by an equal or stronger
   ledger node.
4. **Correct but open.**  The item is a valid target or conditional interface,
   not a proved input.
5. **Reject.**  An exact counterexample or type error invalidates the claim.

Machine calculations were used only to check algebra, transcription, and
finite examples.  They do not establish analytic existence, source
hypotheses, period-independent constants, or global coverage.

## 3. Disposition of the cumulative appendix

| Items | Disposition | Reason |
|---|---|---|
| A.1--A.4 | Correct but dated status/program text | The counts are historical and the current dependency graph has additional all-depth contact and welding gates. |
| A.5 | Conditional endgame only | It assumes the analytic compactness and parameter hypotheses that remain open. |
| A.5a | Superseded | The asserted domain-typing failure is repaired by the source-supported nest; the remaining virtual target-selection and marking problems are real. |
| A.6--A.10 | Useful research targets and diagnostics | The sector recurrence is algebraic; the satellite-to-sector analytic comparison remains absent. |
| A.11--A.12 | Source-subclass map, after exact source correction | Cheraghi--Shishikura and Levin close named arithmetic subclasses, not their complement. |
| A.13 | Valid non-exhaustion diagnostic | The rotation-word example blocks a purely arithmetic exhaustion inference but is not a realization theorem for a quadratic parameter. |
| A.14 | Open bridge specification | None of the five analytic gates is proved there. |
| A.15--A.16 | Finite exact checks | Useful diagnostics; A.22 and A.25 supply the all-order proof. |
| A.17 | Duplicate of `BLOT_ROOT` | The exact quadratic-polynomial constant is \(2\pi/\log(4(s+1))\). |
| A.18 | Narrow source import | The Elephant-Eyes a-priori-bound theorem is retained only in its stated \(p=q+O(1)\) class; its parameter conclusion uses a separately cited in-preparation cylinder-copy input. |
| A.19 | Do not import | Lim's public note reports a theorem attributed to the unavailable manuscript `[DLL26]`; a proof summary is not an independently checked proof. |
| A.20--A.21 | Accurate source frontier | These are status/taxonomy records, not new theorems. |
| A.22 and A.25 | Retain as one narrow theorem | Commutation gives all-order resonance cancellation; the classical parabolic-basin critical-point theorem gives quadratic nondegeneracy. |
| A.23 | Duplicate | The valid trace calculus and the false serial-collar promotion are already represented by Push IV nodes. |
| A.24 | Reject | The response definition is unbounded below, the port quotient erases relative voltages, and arbitrary common energy destroys a strict factor. |
| A.26 | Accurate status audit | No promotion. |
| A.27 | Duplicate after correction | The well-typed finite conjugacy is already covered by the retimed finite-cylinder results; it does not select a virtual return base. |
| A.28 | Correct only after a type repair; duplicate | For \(F:A\to B\), \(K(F)\) must be defined using points of \(A\), not points of \(B\setminus A\). |
| A.29 | Retain after normalization repair | The symmetric-ellipse model is an exact interface counterexample to fixed-modulus end shrinking. |
| A.30 | Retain exact source statement after annulus repair | BLOT Theorem B concerns \(\operatorname{mod}(U_n\setminus K_n)\); the Lavaurs example bounds the different annulus \(\operatorname{mod}(V_n\setminus U_n)\). |
| A.31 | Open and non-exhaustive | It omits degenerate Hausdorff limits and failure of normalized precompactness. |
| A.32 | Retain | Divergent modulus of actual nested serial annuli forces a singleton end fiber. |
| A.33 | Reject and replace by a no-go | Its matrix is not a graph projection for a general bounded welding, and weak operator convergence does not preserve graph constraints or gluing. |
| A.34 | Retain sectorwise | Affine pullback is an exact isometry of the homogeneous \(\dot H^{1/2}\) seminorm on one declared external sector. |

## 4. Exact rejected claims

### 4.1 The proposed conditional response theorem

The side note proposed

\[
 a(u,v)=\inf_{\operatorname{Tr}U=u,\ \operatorname{Tr}V=v}
 \int_D \nabla U\cdot\nabla V .
\]

This is not a Dirichlet response.  With zero traces, take
\(U=t\psi\), \(V=-t\psi\), and \(0\ne\psi\in H^1_0(D)\).  Then the displayed
quantity is at most

\[
 -t^2\|\nabla\psi\|_2^2\longrightarrow-\infty.
\]

The correct object is first the quadratic form

\[
 q(u)=\min_{\operatorname{Tr}U=u}\int_D|\nabla U|^2,
\]

and then its polarization, equivalently the inner product of the harmonic
extensions.

The proposed quotient by the constants on *each port separately* is also
false.  On a width-one rectangle of length \(R\), constant endpoint
potentials \(a,b\) have energy

\[
 \frac{(a-b)^2}{R}.
\]

Independent port quotients send both constants to zero and therefore erase
this energy.  For one connected cell, the correct gauge is the full port
product modulo the single diagonal constant.  Equivalently, retain
mean-zero traces together with the finite vector of relative port
potentials.

Finally, a common nonnegative component energy does not preserve a strict
factor.  If \(q_{\rm out}=\mu q_{\rm in}\), \(0<\mu<1\), and
\(c=tq_{\rm in}\), then

\[
 \frac{q_{\rm out}+c}{q_{\rm in}+c}
 =\frac{\mu+t}{1+t}\longrightarrow1.
\]

Thus a strict transition after gluing needs a proved relative-error or
coercive comparison; positivity alone is insufficient.

### 4.2 The proposed weak graph compactification

The side note called

\[
 \frac12
 \begin{pmatrix}I&J^*\\J&I\end{pmatrix}
\]

the graph projection of a bounded operator \(J\).  This is true for unitary
\(J\), not for general bounded \(J\).  For scalar \(J=2\), the eigenvalues
are \(3/2\) and \(-1/2\), so the matrix is not positive.  For scalar
\(J=1/2\), it is not idempotent.

The actual orthogonal projection onto \(\operatorname{graph}J\) is

\[
 \Pi_J=
 \begin{pmatrix}
 A&AJ^*\\
 JA&JAJ^*
 \end{pmatrix},
 \qquad A=(I+J^*J)^{-1}.
\]

Even this correction does not make weak operator topology compatible with
welding.  On \(H=\ell^2(\mathbb Z)\), let \(U\) be the bilateral shift and
\(J_n=U^n\).  Then \(J_n\to0\) weakly while \(J_n^*J_n=I\).  Also
\(u_n=e_{-n}\rightharpoonup0\), but \(J_nu_n=e_0\).  Hence the varying graph
relations are not closed under simultaneous weak convergence.  The
projections \(\Pi_{J_n}\) converge weakly to \(\tfrac12I\), which is not a
projection and is not a graph.

Uniform boundedness therefore gives only subsequence extraction of matrix
coefficients.  It does not preserve composition, inversion, graph
membership, Dirichlet gluing, or a strict transition.  The welding
compactness gate remains open.

## 5. Retained mathematical content

Complete statements and proofs are in
`side_research_retained_lemmas.md`.  The retained content is:

1. all-order parabolic resonance cancellation and quadratic
   nondegeneracy at a primitive root multiplier;
2. the symmetric-ellipse fixed-modulus ambient-end no-go;
3. the serial-annulus singleton implication;
4. the sectorwise dyadic Böttcher \(\dot H^{1/2}\) isometry;
5. the correct multi-port trace gauge and strictness obstruction; and
6. the weak-operator welding-algebra no-go.

The finite conjugated quadratic-like lift is retained only with the corrected
definition

\[
 K(F)=\{z\in A:F^n(z)\in A\text{ for every }n\ge0\},
 \qquad F:A\to B,
\]

and is treated as a specialization of the existing retimed finite-cylinder
results, not as a new virtual return theorem.

## 6. Source-locked subclass information

The following literature results refine the coverage map without proving
the global conjecture.

- Cheraghi--Shishikura prove exponential parameter shrinking and rigidity
  for their high-type quadratic-growth class \(\mathcal QG_N\):
  <https://arxiv.org/abs/1509.07843>.
- Levin proves MLC at parameters satisfying his exponential
  numerator/denominator criteria and for specified all-satellite cascades;
  Theorem 7 supplies the broader conditions `(Y0a)`, `(Y0b)`, `(Y1)`:
  <https://arxiv.org/abs/0710.4406>.
- Kahn--Lyubich prove a priori bounds for their precisely typed
  Elephant-Eyes class \(p=q+b\) with bounded \(b\):
  <https://arxiv.org/abs/2601.21905>.  The separate Ecalle-cylinder
  parameter input cited in their MLC discussion is not imported here.
- BLOT Theorem B gives a conditional non-parabolic modulus-collapse
  statement for \(\operatorname{mod}(U_n\setminus K_n)\):
  <https://arxiv.org/abs/2205.03157>.

These are sufficient subclasses, not an exhaustive partition.  In
particular, arithmetic words can fail all the listed growth tests, and the
side packet does not prove that every remaining word is realized or controlled
by one of them.

The neutral-attractor theorem reported in
<https://arxiv.org/abs/2607.11408> is attributed there to a separate 2026
manuscript.  Until that full proof is available and checked, it is recorded
as a reported dependency, not an imported theorem.

## 7. Process correction

A single explicit fixture cannot establish that a constant is independent of
satellite period, corridor length, or transition depth.  Every future
fixture certificate must therefore include

\[
 (\text{admissible family},\ \text{free parameters},\
 \text{constant-dependency map},\ \text{proof-use closure hash}).
\]

A linter may check typing, dependency closure, evidence identifiers, and
quantifier order.  It may not certify the analytic truth of those fields.
The side packet's claimed Feigenbaum recomputation is not retained as
evidence: the generator hard-codes the displayed values and no independent
calculation artifact or normalization record was supplied.

## 8. Effect on the global program

The retained lemmas sharpen two local interfaces and eliminate two invalid
shortcuts.  They do **not** construct:

- the actual virtual return atlas or marked carrier;
- all-depth physical contact closure;
- a gluing-stable welding topology;
- uniform response realization or a backward transition;
- coercive marked compactness;
- the quasiconformal rigidity and parameter-fiber conclusion.

Accordingly no global open obligation is promoted.  `MLC`, `UPTCR`,
`VAAPC-I`, `MBTT`, `H3_COERCIVITY`, and `H4_RIGIDITY` remain open.


# Research log

This is the chronological record for the unified MLC proof program. A result is entered
in the proof ledger only after the corresponding log entry records its hypotheses,
source status, proof location, and an adversarial test. Dates use the local project
date.

## 2026-07-23 — Source lock and initial reduction

### Question

Can the two programs isolated by Dudko—unbounded-satellite control and interpolation
between positive- and zero-entropy regimes—be closed by one scalar extremal-width
functional on a virtual pseudo-Siegel hull?

### Sources checked

- D25, Problems 4.3 and 4.4;
- KKL26, Theorems A–C, “Future perspective,” and the translation-marking appendix;
- DL22 and DL25, including the \(\psi^\bullet\)-ql definition and inflation
  proposition;
- BLOT, the root-annulus theorem and its marked-geodesic corollary;
- DL23 and CS15 as bounded-combinatorics and high-type satellite recovery tests.

The exact files and hashes are in `source_ledger.md`.

### Accepted

1. The KKL precedence convention gives an exhaustive four-way partition of
   **families**.
2. The final proof must use a marked state, not an unmarked continuum.
3. A backward record argument is logically compatible with known renormalization
   proofs; forward growth alone is not a contradiction.

### Rejected

1. A bounded scalar uniformly additively comparable to inverse satellite root modulus.
   BLOT makes the discrepancy diverge with satellite relative period.
2. Treating the KKL family classification as a canonical decomposition of every
   individual tower.
3. Treating a priori bounds alone as a global rigidity theorem.

### Consequence

The proof target was replaced by the Marked Backward Transition Theorem (`MBTT`).

## 2026-07-23 — Translation-corridor pass

### Question

Can long satellite or parabolic corridors be replaced by bounded-topology quotients
while preserving all accesses needed by Wave and Wanderers arguments?

### Accepted

1. Short interactions have a bounded number of orbit types modulo the translation
   action.
2. KKL's exact long-tail estimate gives relative control when both standard width and
   marking complexity are small relative to the active degeneration.
3. A finite vector state can be reduced to a scalar recurrence if the chart transition
   matrices have uniformly positive expanding covectors.

### Rejected

A marking-faithful quotient of uniformly bounded cardinality. The KKL translation
marking has \(N=2(n+1)p\) distinct ideal intervals, and preserving their labels forces
at least \(N\) target marks.

### Consequence

The candidate state became a bounded active core plus faithfully marked translation
corridors. “Bounded complexity” now means bounded local interaction types modulo
translation, not bounded raw marking cardinality.

## 2026-07-23 — Degree and prime-end pass

### Question

Can the complement of a connected full virtual hull directly realize a uniformly
quadratic first return?

### Accepted

1. Fullification preserves genuine polynomial forward invariance.
2. Pullback of a full continuum by a quadratic polynomial obeys a critical-value
   dichotomy: two conformal components off the critical value, one degree-two
   component over it.
3. A selected inverse itinerary containing one critical target factors into exactly
   one quadratic step and conformal remaining steps.
4. **Withdrawn after the later fiber-product audit:** compatible stage maps do not by
   themselves assemble into a degree-two correspondence return.

### Rejected

Using the global complement map \(f^q\) as the virtual quadratic return. Its prime-end
degree is \(2^q\), not \(2\).

### Consequence

The virtual return must be a selected fiber-product or multiple-component
correspondence retaining the one-critical-step factorization.

## 2026-07-23 — Finite-horizon inflation pass

### Question

What is the strongest finite-horizon inflation statement supported by DL25, elementary
covering theory, and the selected degree-two factorization?

### Source facts rechecked

DL25 Definition `dfn:psi:Siegel:ql` requires more than a degree-two branched cover:

- \(\iota\)-properness of the core;
- homeomorphic identification of every iterated core \(K_n\);
- a covering-embedding property for \(\iota\) relative to \(K_1\);
- covering-embedding properties for every fiber-product iterate \(\iota^n\).

DL25 Proposition `prop:g:unwind` obtains these properties from a globally
forward-invariant postcritical set \(\Upsilon=f(\Upsilon)\), local saturation, and
relative-cover inflation. Its multiple-component remark is a proposed framework, not a
proved general finite-horizon theorem.

### Accepted

1. A finite-horizon \(\psi\)-ql datum can be defined by truncating the iterated-core and
   covering-embedding axioms at a stopping time \(q\).
2. Every genuine \(\psi\)-ql map has such a truncation.
3. Stage-dependent excluded sets must satisfy
   \[
     \Upsilon_j\subset f^{-1}(\Upsilon_{j+1})
     \quad\Longleftrightarrow\quad
     f(\Upsilon_j)\subset\Upsilon_{j+1}
   \]
   even to define the stage inclusion of complements.
4. Relative-cover lifts are governed by the usual fundamental-group subgroup
   criterion. Local saturation must be checked at every selected core; it is not a
   synonym for connectedness or fullness.

### Rejected

1. “Finite orbit marking automatically replaces global forward invariance.” It does
   not: the complement inclusion can fail at the first stage.
2. “Topological inflation controls extremal width.” The family
   \[
     z^2:\mathbb D_R\longrightarrow\mathbb D_{R^2},
     \qquad \iota:\mathbb D_R\hookrightarrow\mathbb D_{R^2},
   \]
   has the same degree, core, and marking topology for every \(R>1\), while
   \[
     W=\frac{1}{\operatorname{mod}
       (\mathbb D_{R^2}\setminus\overline{\mathbb D})}
      =\frac{\pi}{\log R}
   \]
   ranges from \(0\) to \(+\infty\).
3. “A proof using at most \(q\) visible iterates is automatically valid on a
   \(q\)-truncation.” Each curve family must also remain inside the declared
   covering-embedding locus and avoid unmarked critical values.

### Consequence

`H1_FINITE_HORIZON_INFLATION` splits into:

- a topological construction obligation;
- an orbit/access audit through the stopping time;
- a separate quantitative localization and width-loss obligation.

The full statement remains open. The next analytic target is not merely to inflate a
finite tower, but to construct it with a width comparison whose loss is relative or
entropy-amortized and independent of the horizon.

### One-sided analytic fact

If a locally saturated target collar \(B\setminus H\) has already been constructed and
the inflation contains \(B\) conformally, essential-annulus monotonicity gives
\[
  W(V\setminus H)\le W(B\setminus H).
\]
Thus unrestricted path extension does not increase target inverse annular modulus. The
remaining issue is to construct \(B\) with controlled local width and then compare the
marked WAD/sectorial/corridor families. This does not contradict the rescaling no-go:
that example varies the starting collar itself.

### Conditional local saturation

For a prescribed finite inverse itinerary of full quadratic hulls and compact obstacle
sets separated from each hull, shrinking selected pullback components and using Jordan
neighborhood bases constructs a finite telescope
\[
  f:A_j\to B_{j+1},\qquad A_j\Subset B_j.
\]
Exactly one stage is quadratic, the rest are conformal, and the annulus
\(B_j\setminus\overline A_j\) gives the required boundary homotopy relative to the
stage marking. This proves local saturation conditionally on the virtual hulls actually
forming the full inverse itinerary.

The construction is qualitative: arbitrary thin choices of \(B_j\) can make inverse
modulus arbitrarily large. The next target is therefore a marked collar calibration
lemma, not another topological collar-existence lemma.

### Connected-exterior calibration

If the exterior marking is one connected continuum \(E\), then
\[
  V=\widehat{\mathbb C}\setminus E
\]
is a conformal disk and \(V\setminus H\) is exactly the doubly connected marked
surface. Jordan exhaustions of \(V\) recover its modulus monotonically, so local collar
width can be made arbitrarily close to the marked width. Inflation then cannot increase
it.

This proof does not extend by joining arbitrary exterior components: such joins can
cross corridors, merge prime-end accesses, or erase Wave homotopy classes. The first
genuinely new calibration problem is therefore the disconnected, faithfully marked
multi-corridor case.

## 2026-07-23 — Corridor-network calibration pass

### Source facts rechecked

KKL's Thick–Thin Theorem gives
\[
  W-C(|\chi|+|\mathcal I|)
  \le2\|X_{\rm can}\|\le W.
\]
Its translation-marking theorem gives
\[
  \|X^{\rm long}\|\le2W_{\rm std}+6N.
\]
Restriction by an immersion is described by itineraries and domination; serial
families combine by harmonic sum, not ordinary addition.

### Accepted

For an actually realized corridor decomposition,
\[
  Q\le W\le Q+4S+C\kappa,
\]
where \(Q\) is retained core/short WAD weight, \(S\) is aggregate corridor standard
width, and \(\kappa\) is topology plus raw marking complexity. Hence relative
calibration follows whenever \(4S+C\kappa\le\varepsilon Q\).

### Rejected

1. Raw marking complexity as a uniformly positive coordinate of the final bounded
   scalar. Unbounded translation markings would force that scalar to diverge.
2. Automatic replacement of WAD transport by positive matrices. For
   \(x\oplus y=(x^{-1}+y^{-1})^{-1}\), no fixed positive linear form is uniformly
   comparable over all \(x,y>0\).
3. Repeating a bounded-fanout comparison at every elementary corridor step. Its
   multiplicative loss can grow exponentially with corridor length.

### Consequence

The transition category must first allow monotone homogeneous maps with harmonic/min
operations. A finite matrix family becomes valid only after a uniform
balance/bottleneck-chamber lemma. Raw complexity must be absorbed relatively, charged
to entropy, canceled, or eliminated before the positive-covector argument.

### Normalized topology criterion

The KKL proof that a good bounded-length family meets at most \(3\mathfrak b\)
translation classes is an orbit-packing argument. Abstractly,
\[
  k\le
  \frac{3|\chi(\mathcal V)|+|\mathcal I|}{q-b},
\]
where \(q\) is corridor length and \(b\) is the inactive buffer. Therefore the virtual
replacement need not bound raw topology; it must bound topology per accelerated
translation cell and prove that each class has a full admissible orbit across the
interior corridor.

This converts “bounded active core” into a checkable ratio
\[
  \tau_B=(3|\chi|+|\mathcal I|)/q_B.
\]
If \(\tau_B\) is unbounded under every valid block grouping, translation compression
alone cannot close the proof.

### Arithmetic gate

For a KKL \((n,p)\)-translation marking,
\[
  N/(n+1)=2p.
\]
Thus increasing corridor length \(n\) does not dilute an unbounded shift parameter
\(p\). The bounded-density WAD branch is intrinsically a bounded-\(p\) branch. Large
\(p\) must be transferred to pseudo-Siegel/sectorial control or to a newly constructed
acceleration whose usable dynamical length scales with \(N\). This gives a necessary
candidate seam for interpolation; the virtual construction must still prove that its
large translation parameter matches the continued-fraction/neutral scale used by the
pseudo-Siegel theorem.

## 2026-07-23 — Neutral transition absorption pass (normalization superseded below)

DL25's transitional neutral estimate has peripheral loss
\[
  O(\sqrt{A_m}),
  \qquad A_m=\ell_mK_F.
\]
The elementary inequality
\[
  C\sqrt x\le\delta x+C^2/(4\delta)
\]
shows this is a valid relative error for backward amplification.

Combining it with the corridor sandwich gives a checkable interface criterion:

- prove \(Q\asymp A_m\);
- prove \(4S+C\kappa=O(\sqrt Q)\), or charge the excess to entropy;
- identify the access markings and audit all finite pullbacks.

The square-root absorption is proved. None of those three geometric identifications is
imported from DL25; its application section explicitly calls for global external input.

### Correction: replication is enough for complexity

The initial sufficient condition
\[
4S+C\kappa=O(\sqrt Q)
\]
was too restrictive. If a block of \(r\) usable returns satisfies
\[
Q\ge arD,\qquad S\le br,\qquad\kappa\le cr,
\]
then
\[
4S+C\kappa
\le
\frac{4b+Cc}{aD}\,Q.
\]
Thus large successor degeneration \(D\) absorbs all complexity that grows linearly with
the return count, uniformly in \(r\). This matches the structure of established
positive-entropy replication arguments and is now the preferred virtual route.

### Nonlinear scalar reduction

The matrix cone lemma has been generalized. If each chart has a monotone, subadditive,
positively homogeneous gauge \(L_t\) and
\[
L_t(\Phi_{tu}(x))\ge\lambda L_u(x),
\]
then a componentwise transition with error \(e\) gives
\[
L_t(\mathscr D_{\rm out})
\ge\lambda L_u(\mathscr D_{\rm in})-L_t(e).
\]
Thus the backward record mechanism works directly for harmonic/min transition maps.
The open problem is construction of a common expanding gauge, not linearization for its
own sake.

The reduction was then widened to error-stable gauges:
\[
L((x-e)_+)\ge L(x)-G(e).
\]
This is necessary because the natural bottleneck gauge
\(L(x)=\min_i a_ix_i\) need not be subadditive. It is error-stable with
\(G(e)=\max_i a_ie_i\), so bottleneck chambers remain compatible with the backward
record argument.

## 2026-07-23 — Finite virtual-skeleton pass (hypotheses sharpened below)

A sufficient topology theorem has been isolated. If the \(r\) usable virtual return
cells form a finite tree of full continua with uniformly many vertex, edge, base, and
corridor labels, then
\[
\kappa\le c_{\rm tree}r.
\]
Combined with \(Q\ge arD\) and \(S\le br\), the corridor sandwich becomes
\[
Q\le W\le
\left(1+\frac{4b+C_{\rm net}c_{\rm tree}}{aD}\right)Q.
\]

The unresolved assertion is not the counting. It is that Dudko's connected hull of a
Cantor family admits such a finite access-faithful tree skeleton. Connectedness alone
does not exclude infinite dendritic branching, fullification loss, or unmarked Cantor
components separating declared accesses.

## 2026-07-23 — Independent normalization and replication correction

Three independent audits were run against the virtual/neutral interface. They found
two structural errors in the preliminary target.

First, DL25's
\[
A_m=\ell_mK_F
\]
is a per-tile scale. The transition tiling has
\(r_m=\mathfrak q_{m+1}\) tiles and
\(\ell_m\asymp1/\mathfrak q_{m+1}\), so
\[
W_{\rm cell}\asymp A_m,
\qquad
W_{\rm total}\asymp r_mA_m\asymp K_F.
\]
The earlier bullet “prove \(Q\asymp A_m\)” was therefore wrong for the project's total
WAD coordinate. It has been replaced by
\[
Q_{\rm cell}=Q_{\rm orb}/r_m\asymp A_m,
\qquad
Q_{\rm orb}\asymp K_F.
\]
The global peripheral loss is \(O(r_m\sqrt{A_m})\), which is
\(O(A_m^{-1/2})\) relative to total orbit width.

Second, a finite tree with \(r\) return cells does not imply \(r\) active replicas.
Equal cells in series give \(Q=D/r\), and repeated isotopic returns do not add WAD
weight. Marking and replication counts must be separated:
\[
\rho_B=\frac{r_{\rm mark}}{r_\parallel},
\qquad
4S+C_{\rm net}\kappa
\le
\frac{4b+C_{\rm net}c}{aD}\rho_BQ.
\]
The virtual theorem must bound \(\rho_B\), or at least \(\rho_B/D\) below the
amplification margin.

The tree model was also split into:

1. a monotone finite cell-tree extraction from the Cantor carrier;
2. analytic prime-end/access realization with exact KKL translation rules.

Bounded access incidence, \(\sum N_a=O(r)\), and \(S=O(r)\) are now explicit analytic
hypotheses. For \(N=2(n+1)p\), bounded incidence over \(n+1\) cells excludes unbounded
\(p\); the large-shift branch remains open.

## 2026-07-23 — Response-state and entropy bookkeeping pass

The bounded-terminal Dirichlet-to-Neumann response matrix is now the sharp candidate
interface state. Its algebra is exact:

- parallel gluing adds response matrices;
- eliminating an intermediate terminal takes a Schur complement;
- the scalar two-edge case is the harmonic sum.

This retains electrical orientation that a scalar total or fixed positive width vector
loses. The open theorem is comparison of the surface/WAD extremal energy with this
bounded-terminal response form.

Entropy payment was also made exact. If
\[
v_{j+1}\le e^{-\epsilon_j}v_j+\eta_j,
\]
then terminal error is the future-entropy-discounted sum
\[
\sum_j e^{-\sum_{k>j}\epsilon_k}\eta_j.
\]
A uniform contraction follows from a bound by
\[
\theta(1-e^{-E})v_0+C,\qquad\theta<1.
\]
Positive total entropy alone does not control arbitrarily many local errors. Directed
chart cycles must also expand as compositions; reciprocal changes forming an identity
cycle rule out a common edgewise expansion factor.

At that checkpoint, the machine ledger validated 69 obligations:
6 imported, 48 proved internally, and 15 open (including the MLC target). MLC remains
open.

## 2026-07-23 — Direction, state, and endpoint consistency pass

An independent cross-document audit found four hidden proof failures.

First, the collar/corridor estimates had the forward form
\[
  y\preceq\Psi(x)+e,
\]
while MBTT needs a backward lower estimate. Direction reversal is invalid without an
additional hypothesis. Lemma 5.4 now proves the exact reduction: if an error-stable
gauge satisfies
\[
  L_{\rm out}(\Psi x)\le\mu L_{\rm in}(x),\qquad0<\mu<1,
\]
then
\[
  L_{\rm in}(x)\ge
  \mu^{-1}L_{\rm out}(y)-\mu^{-1}G(e).
\]
Because individual localization/chart maps can be identities, they are first grouped
with the dynamical step of a complete entropy-clock block. The open analytic target is
strict forward contraction of that grouped map (with margin after relative error), or
an independently proved backward componentwise lower transition.

Second, the response state had incorrectly placed raw cell count and discrete ribbon
data inside a homogeneous cone. It is now split into
\[
  \mathscr R_B=
  (Q_B/r_B,\Lambda_B/r_B,S_B^{\rm std}/r_B)
\]
and side/error data
\[
  \sigma_B=(r_B,\rho_B,\kappa_B/r_B,\mathcal P_B).
\]
Only \(\mathscr R_B\) is scaled. Coercivity must be uniform over admissible
\(\sigma_B\) while allowing \(r_B\to\infty\).

Third, the global WAD count now explicitly requires injectivity of local translated
arcs into distinct global marked isotopy coordinates. Geometric disjointness in a
local corridor does not prove that condition. The exact KKL support bound
\(3|\chi(\mathcal V)|+|\mathcal I|\) is now a separate imported ledger node.

Fourth, shrinking diameters of a nested sequence do not by themselves prove local
connectivity. The rigidity endpoint now requires connected relative neighborhoods
forming a basis, or a precisely applicable trivial-fiber theorem that supplies that
basis.

The ledger schema now separates proof dependencies from open hypotheses of a proved
conditional implication and rejects every proved/imported node with an open proof
dependency. It validates 72 obligations:
7 imported, 49 proved internally, and 16 open (including MLC). The new open gate is
`H2_FORWARD_CONTRACTION_CALIBRATION`. MLC remains open.

## 2026-07-23 — Formal complete-block contraction task

`block_contraction_program.md` now states the exact next analytic theorem. Endpoint
cell counts and side records are allowed to differ:
\[
\sigma_{\rm in}
=(r_{\rm in},\rho_{\rm in},\kappa_{\rm in}/r_{\rm in},\mathcal P_{\rm in}),
\qquad
\sigma_{\rm out}
=(r_{\rm out},\rho_{\rm out},\kappa_{\rm out}/r_{\rm out},\mathcal P_{\rm out}).
\]
The block gauge may depend on these side records but is homogeneous only in the
geometric state, with constants uniform over admissible side pairs.

The abstract closure is now proved. If a complete forward block has contraction
\(\mu<1\) and output-relative error \(\delta<1-\mu\), then
\[
L_{\rm in}
\ge
\frac{1-\delta}{\mu}L_{\rm out}-\frac C\mu.
\]
The remaining work is analytic: surface-to-response realization, entropy contraction
in that same gauge, the large-shift neutral routing, error conversion, and complete
block/cycle auditing.

The same pass removed four overclaims:

1. a finite labeled telescope is no longer called a multiple-component
   depth-\(q\) \(\psi\)-ql object without a formal category;
2. neutral multiplicative comparison is asserted only for \(A_m\ge A_*\), with small
   \(A_m\) routed into the bounded normalized branch;
3. `WC-P`, `WC-N`, and `WC-V` now carry explicit raw, relative, density, or discounted
   errors rather than fictitious universal additive constants.
4. proper degrees are no longer multiplied through a correspondence without selected
   fiber-product components, closed routing, and base-change/projection-degree
   control; the former telescope claims are now open.

The machine ledger now validates 73 obligations:
7 imported, 48 proved internally, and 18 open (including MLC). MLC remains open.

## 2026-07-23 — Post-patch consistency audit

The final independent audit repaired two remaining topology/assembly scope defects.
Corollary 7.9 now chooses the stage neighborhoods recursively from the terminal
neighborhood, so the displayed restrictions genuinely compose; this does not promote
the still-open mapping telescope or finite-horizon assembly claims. Prime-end circles
are invoked only for nondegenerate full hulls with hyperbolic complements, not from
fullness alone.

After those repairs, `audit_proof.py` again validates all 73 obligations:
7 imported, 48 proved internally, and 18 open. The target `MLC` remains open.

## 2026-07-23 — BC1 finite-port solve and Value obstruction

The first BC1 pass separates an elementary finite-block theorem from the missing
uniform virtual theorem.

`bc1_finite_port_response.md` proves:

1. every fixed finite-electrode bordered surface has an exact
   Dirichlet-to-Neumann response matrix;
2. port compression is exact on fiber-constant potentials, but a quotient is a
   sufficient block state only when it is future closed;
3. a finite WAD with incidence-faithful ports has the exact graph Laplacian
   \(B\operatorname{diag}(w)B^{\mathsf T}\);
4. KKL coefficientwise domination with harmonic-sum itineraries implies Loewner
   domination after the intermediate itinerary ports are eliminated;
5. one fixed surface response and WAD response are spectrally comparable exactly when
   their componentwise kernels agree.

The fifth result is deliberately nonuniform. Its constants are generalized Rayleigh
eigenvalues. A fixed number of ports does not prevent those eigenvalues from tending
to zero or infinity along a degenerating family.

The same pass found a new exact state obstruction. If two distinct global WAD
coordinates are compressed to one port pair and have different KKL coefficients
\(\ell(a)^2\), then redistributing a fixed total weight between them preserves
\(Q_B\), the response matrix, and the unweighted port pattern while changing
\[
  \operatorname{val}(X)=\sum_aX(a)\ell(a)^2.
\]
Any auxiliary aggregate fixed by the same redistribution also fails to recover Value.
Thus BC2 cannot be transferred to the response-only state without one of:

- Value-faithful future-closed ports;
- a uniform coefficient-comparison theorem inside every merged class; or
- a retained homogeneous vector \(\mathbf V_B/r_B\) of outgoing Value moments.

The provisional geometric state is therefore
\[
  \mathscr R_B^{\rm val}
  =
  (Q_B/r_B,\Lambda_B/r_B,\mathbf V_B/r_B,S_B^{\rm std}/r_B).
\]
Uniformly bounding the dimension of \(\mathbf V_B\), or eliminating it by a proved
finite-feature theorem, is now the explicit obligation
`H2_VALUE_FEATURE_REALIZATION`.

The KKL source was rechecked at `waves-with-Misha.tex` lines 1881--1943 and
2086--2124, and `value1.tex` lines 6--20 and 103--111. The source proves rectangular
WAD realization, ordered harmonic itineraries, domination, and primitive
\(\psi\)-ql Value contraction. It does not prove future-closed port compression or
uniform response eigenvalue bounds.

`bc2_value_feature.md` then solves the finite lifted-state observability problem.
For a lifted linear WAD state \(z=Tw\) and valuation family \(Cw\), observability on
the nonnegative cone is equivalent to
\[
  \operatorname{row}(C)\subseteq\operatorname{row}(T).
\]
The exact minimum number of added moments is
\[
  \operatorname{rank}\!\begin{pmatrix}T\\C\end{pmatrix}
  -\operatorname{rank}T.
\]
Thus one fixed KKL valuation needs at most one extra scalar, independently of WAD
support size. On a source-licensed primitive block it obeys
\[
  V_F(Y)\le\lambda_F^{-n}V_F(X)+V_F(E)
\]
under the declared coefficientwise error comparison. The rank test is not applied to
a Schur-eliminated response, which is nonlinear in its edge weights; such a terminal
state must pass the direct fiber-observability test.

> **Superseded source status.** The later typed-incidence/clone audit recorded below
> found that the printed finite-\(n\) clone bridge is inconsistent. The limit in the
> next paragraph is now an open source-repair obligation, and the contraction is only
> a conditional implication from an independently proved limit.

At this stage of the log, the project treated KKL's fixed-cross-section claim as a
genuine entropy-clock special case:
\[
  \lambda_n\to1,
  \qquad
  \lambda_n^n\to h(1)>1.
\]
For every fixed clone datum, sufficiently long complete cloned primitive blocks
therefore contract their KKL Value by one uniform factor
\(\mu_{\rm cl}^{-1}<1\), although no elementary edge has a uniform contraction.
This validates the complete-block grouping mechanism on that exact source model. It
does not identify an arbitrary virtual corridor with a clone or control its
transpose-eigenweight/error comparisons.

After these additions, the machine ledger validates 84 obligations:
9 imported, 56 proved internally, and 19 open. MLC remains open.

## 2026-07-23 — Variable-template clone entropy theorem

`virtual_clone_entropy.md` removes the fixed-template restriction from the
graph-theoretic part of KKL cloning.

For every nontrivial primitive integer transition matrix \(A\) of dimension at most
\(d\), the directed multigraph contains two distinct closed walks which can be
equalized to a common length at most \(d^2\). Binary concatenation gives
\[
  \rho(A)\ge2^{1/d^2}.
\]
Therefore any source-licensed block satisfying the reduced clone equation
\[
  h(\lambda)=\lambda^n
\]
has the period-independent complete-block contraction
\[
  V((f^n)^*X)
  \le
  2^{-1/d^2}V(X).
\]
No finite list of graph templates is needed; a universal bound on reduced
cross-section dimension suffices.

The same note proves a bounded-entropy eigencone theorem. If reduced dimension,
edge-label depth, and \(h(1)\le H\) are bounded, then the clone multiplier lies in
\[
  2^{1/d^2}\le\lambda^n\le H^2,
\]
the weighted reduced matrices lie in a compact primitive family, and both normalized
left and right Perron coordinate ratios are uniformly bounded. The complementary
branch \(h(1)>H\) has contraction \(<H^{-1}\), but still needs its errors converted to
outgoing Value.

The dimension hypothesis is necessary. A directed \(d\)-cycle with one self-loop is
primitive and has Perron root determined by
\[
  \rho_d^d=\rho_d^{d-1}+1,
\]
so \(\rho_d\downarrow1\).

The exact stability margin is also recorded. If an actual reduced transition retains
at least an entrywise \((1-\epsilon)\) fraction of the clone transition, its total
multiplier is at least
\[
  (1-\epsilon)2^{1/d^2}.
\]
It remains strictly expanding when
\[
  \epsilon<1-2^{-1/d^2}.
\]
This tolerance tends to zero like \(d^{-2}\), so bounded reduced dimension must be
established before any perturbation is called uniformly small.

This does not yet construct a clone from a virtual corridor. The new open obligation
`H2_VIRTUAL_CLONE_REALIZATION` requires the bounded reduced graph, bounded label
depth, exact clone equation (or perturbation below the explicit gap), finite-horizon
WAD realization, future-closed ports, and outgoing Value-error control.

A diagnostic enumeration of primitive \(0/1\) matrices found minimum Perron roots
approximately \(1.6180,1.3247,1.2207\) in dimensions \(2,3,4\), all above the proved
crude bounds \(2^{1/4},2^{1/9},2^{1/16}\). The cycle-plus-loop roots decreased from
approximately \(1.6180\) at dimension \(2\) to \(1.0593\) at dimension \(50\), matching
the no-go limit. These computations are consistency checks only and are not ledger
evidence.

After this pass, the machine ledger validates 90 obligations:
9 imported, 61 proved internally, and 20 open. MLC remains open.

## 2026-07-23 — Exact corridor-to-clone criterion

`corridor_clone_criterion.md` isolates and proves the finite directed-graph statement
needed before the variable-template entropy theorem can be applied.

An exact translation corridor is a KKL cross-section clone precisely when its full
directed multigraph, including multiplicities, has:

1. one declared label-preserving chain edge at every corridor step and no other
   corridor-to-corridor edge;
2. all non-chain incidences entering at the first cell or exiting at the last;
3. a reduced quotient obtained by **deleting the distinguished chain edges before**
   identifying equal labels; and
4. the KKL cross-section recurrence in that reduced quotient.

The order in Item 3 matters. Literal graph contraction preserves each chain edge as an
\(E\)-self-loop and therefore does not recover KKL's base graph, whose cross section
has no \(E\)-to-\(E\) edge.

Two bounded-defect closure lemmas were also proved. Entry and exit defects confined to
fixed windows \((L,R)\) can be absorbed into the active graph without increasing
cross-section cardinality, provided the surviving central quotient is still a cross
section. Equal-length disjoint corridors combine into one clone only when their union
is a cross section of the combined quotient; their cross-section dimensions add.
Neither recurrence condition follows from a visible local product corridor.

The adversarial audit caught and repaired both hidden assumptions before promotion:
a closed active cycle destroys the cross-section property while leaving every local
chain edge unchanged, and an unbounded number of individually small parallel
corridors makes total reduced dimension unbounded.

The new open obligation `H2_VIRTUAL_CORRIDOR_GRAPH_REALIZATION` is now upstream of
`H2_VIRTUAL_CLONE_REALIZATION`. It requires the actual finite-horizon core/Hubbard
transition multigraph, its complete WAD-to-core and critical/immersion incidences,
primitivity, and universal bounds on cross-section dimension, endpoint windows,
parallel corridor count, and label depth. The graph criterion does not manufacture
any of these dynamical facts.

After this pass, the machine ledger validates 94 obligations:
9 imported, 64 proved internally, and 21 open. MLC remains open.

## 2026-07-23 — Finite-state clone certificate and source boundary

The complete D25 source archive was re-downloaded from arXiv v1. Its `main.tex` hash
matches the locked ledger:
`FD807D65C44852995182D23A4E96BB42717E8E7502F1D7B71636B16AF5D8A454`.
Lines 875--892 contain the entire virtual-Molecule proposal relevant here. They define
the interpolation gap and propose connected partially invariant hulls of Cantor small
Julia sets with finitely many critical first returns, but they do not construct a
finite transition graph, cross section, bounded return time, or mixing certificate.

The KKL source trace found the concrete licensing step omitted from the earlier
summary. In `not-all-good2.tex`, Lemma `lem:get-around` bounds return from the critical
limb using parabolic boundedness; Corollary `cor:cross-section` converts it to a finite
Hubbard-tree edge cross section; Proposition `prop:eigenweights` then identifies
longer parabolic types as clones and applies the clone appendix. This is a finite
Hubbard/core transition argument. It is not a theorem about an arbitrary WAD response
graph or Dudko virtual carrier.

`dynamical_corridor_certificate.md` turns the missing graph properties into finite
tests:

1. \(E\) is a cross section if and only if the active induced graph \(G[V\setminus E]\)
   is acyclic;
2. cloning preserves strong connectivity;
3. two closed walks with the same gate-passage count and lengths differing by one
   force every clone delay to be primitive;
4. primitivity of the base alone is insufficient.

The exact no-go example for Item 4 is a bouquet of directed \(3\)- and \(5\)-cycles
sharing the sole gate. Its base period is \(\gcd(3,5)=1\), while one inserted delay
changes the generators to lengths \(4,6\), producing period \(2\).

The resulting finite-state certificate `FC1`--`FC6` now distinguishes:

- the finite core/Hubbard transition cloned to control Perron eigenweights;
- the WAD pullbacks and their complete itinerary incidence with that core;
- the terminal response/Value feature state.

It also requires common surviving corridor length, bounded total gate size, active
acyclicity, delay-robust mixing, finite-horizon realization, and source identity. Under
those hypotheses the uniform graph contraction follows; proving the hypotheses for a
virtual hull remains exactly `H2_VIRTUAL_CORRIDOR_GRAPH_REALIZATION`.

After this pass, the machine ledger validates 99 obligations:
9 imported, 69 proved internally, and 21 open. MLC remains open.

## 2026-07-23 — Translation/entropy/shear trichotomy

The clone-realization target was adversarially too narrow. Neither D25 nor KKL proves
that every virtual bounded-type corridor has a pure bijective interior. A bounded
finite alphabet of local transitions also does not imply a single clone.

`corridor_entropy_shear_dichotomy.md` now proves the stationary finite-state
classification. If a nonnegative integer layer transfer is irreducible, then it is
either one directed-cycle permutation with spectral radius \(1\), or
\[
  \rho\ge2^{1/d^2}.
\]
The proof uses two distinct returns from a branching vertex, equalized to a common
length at most \(d^2\), and binary concatenation. A cocycle consisting only of
permutations is converted to the identity chain by transporting labels, so this
zero-entropy irreducible case is the exact translation branch.

Reducibility creates a third branch. Every integer matrix with spectral radius \(1\)
has Frobenius diagonal blocks that are directed cycles or zero. After a common cycle
power, all remaining non-permutation transport is nilpotent feed-forward shear and
its powers grow polynomially. The exact counterexample
\[
  \begin{pmatrix}1&1\\0&1\end{pmatrix}^{m}
  =
  \begin{pmatrix}1&m\\0&1\end{pmatrix}
\]
has one local type, zero exponential entropy, no exact clone gauge, and unbounded
linear transport. Therefore "clone or positive entropy" is false without a
pseudo-Siegel/sectorial or retained-shear branch.

Nonstationarity adds a separate obstruction. Upper and lower unipotent shears each
have spectral radius \(1\), but their product has Perron root
\((3+\sqrt5)/2\). Per-layer classification is therefore insufficient; a proof needs
a common Frobenius flag or must group the product before placing entropy checkpoints.

The open `H2_VIRTUAL_TRANSFER_TRICHOTOMY` now routes each virtual block through:

1. permutation/translation clone;
2. source-licensed irreducible positive entropy;
3. reducible zero-entropy shear, regularized or retained.

The older clone-realization obligations are retained but correctly scoped to Branch
1. This follows the completion rule: the shear example identifies the replacement
invariant instead of weakening the uniform theorem.

After this pass, the machine ledger validates 105 obligations:
9 imported, 74 proved internally, and 22 open. MLC remains open.

## 2026-07-23 — Nonstationary support pumping

The stationary transfer trichotomy left arbitrary changes of Frobenius flag as an
unbounded word problem. `corridor_support_automaton.md` now proves a finite reduction
at the Boolean-support level.

For an \(s\)-state automaton labeled by \(d\times d\) nonnegative integer transfers,
each prefix has a state
\[
  (q,\operatorname{supp}P)
\]
chosen from at most
\[
  s2^{d^2}
\]
possibilities. If two prefix states agree, the intervening word can be removed from
the **support skeleton** without changing either automaton admissibility or the final
Boolean support. Iterating leaves a skeleton of length at most
\[
  s2^{d^2}-1
\]
with every removed word recorded as an inserted support-neutral loop.

This is not numerical deletion. The constant unipotent shear has stable support but
linearly growing coefficients, so every pumped loop must remain in the entropy/shear
ledger.

A second theorem gives a bounded positive-entropy witness. If any accepted product
has a strongly connected support component that is not a directed cycle, a shortest
such word has no repeated prefix state and therefore has length at most the same
bound. Its numerical product has
\[
  \rho\ge2^{1/d^2}.
\]

The infinite nonstationary problem is consequently reduced to finitely many support
skeletons plus support-neutral loop products. The exact new open theorem
`H2_VIRTUAL_SUPPORT_AUTOMATON` must construct the finite automaton without enlarging
the actual dynamical language, retain complete WAD incidence, and route every loop to
source-licensed entropy or common-flag shear regularization.

After this pass, the machine ledger validates 109 obligations:
9 imported, 77 proved internally, and 23 open. MLC remains open.

## 2026-07-23 — Future-equivalence and counter correction

The support-pumping theorem has a nontrivial realization prerequisite: a finite local
alphabet does not imply a uniformly finite source-faithful language automaton.
`virtual_language_memory.md` identifies the exact invariant.

For a fully decorated dynamical language, the minimal deterministic state count equals
the number of distinct right future languages. Two exact no-go families were proved:

1. the prefix closure of \(x\#x\), \(x\in\{0,1\}^m\), uses a fixed alphabet and
   horizon \(2m+1\) but has at least \(2^m\) future classes, even if every atom has
   identity core support;
2. the unique-exit language \(\operatorname{Pref}\{a^m b\}\) has at least \(m+1\)
   future classes.

Thus finite horizon, bounded present cell type, and constant Boolean support do not
bound future WAD/access complexity.

A sufficient theorem was also proved: if decorated legality, output, endpoint
acceptance, and mode update depend on a finite mode and the last \(R\) atoms, then the
exact automaton has at most
\[
  |M|\sum_{j=0}^{R}|\mathcal A|^j
\]
states.

> **Later correction.** KKL's syntax retains the length, but its printed weighted
> equation is quarantined. The counter-memory conclusion below uses only retention of
> the length, not that equation.

Prescribed corridor lengths and first-return times are naturally unbounded additive
counters. Deleting a repeated control/support loop is dynamically valid only if its
increment in every exact counter is zero or the endpoint predicate is proved invariant
under that increment. KKL cloning retains precisely such a nonzero counter through
\(h(\lambda)=\lambda^n\); it does not pump the length away.

The corrected open obligation `H2_UNIFORM_COUNTER_FOLLOWER` asks for universally
finite decorated control, memory, and **counter dimension**, while allowing the
counter values themselves to diverge. The side state now records
\(\boldsymbol\nu_B\), and the finite support automaton is scoped to the counter-factored,
counter-safe language.

A further coding audit prevents this formulation from becoming vacuous. With \(s\)
finite states, \(k\) counters, and additive increments bounded by \(C\), only
\(s(2Cm+1)^k\) configurations are reachable after \(m\) symbols, so such counters
cannot hide the exponential copy-language memory. Encoding the entire satellite word
as one large integer would require arbitrary digit-decoding guards and is explicitly
forbidden: every counter needs a geometric meaning and a universal restricted update
rule.

After this pass, the machine ledger validates 115 obligations:
9 imported, 82 proved internally, and 24 open. MLC remains open.

## 2026-07-23 — Source automaton construction and adversarial repair

Three independent passes were run against the virtual support-automaton step.

> **Later correction.** “Clone” in this historical paragraph means the finite
> cross-section/length syntax. The printed spectral equation and its limit proof are
> not currently imported.

First, `virtual_automaton_source_research.md` checked the full locked TeX of D25,
KKL26, the bounded primitive/decorations/molecules papers, and postcritically infinite
Hubbard-tree literature. No checked source constructs a uniformly finite,
WAD-decorated follower automaton for Dudko's proposed virtual hull. The strongest
positive model remains KKL's parabolically \(b\)-bounded prime-primitive
cross-section clone, which explicitly retains its unbounded clone length in
\(h(\lambda)=\lambda^n\).

The focused nesting audit found an additional boundary. D25 `main.tex`, lines
875--892, and KKL26 `waves-with-Misha.tex`, lines 299--303, supply ordered nested
chains. They do not prove matched push/pop maps, reverse no-skipping order, or
recovery of predecessor WAD/access state. Thus a finite-alphabet LIFO stack is a
permitted explicit side-state model, not an imported dynamical theorem. The side
record was enlarged to
\[
  \sigma_B=
  (r_B,\boldsymbol\nu_B,\omega_B,\rho_B,\kappa_B/r_B,
   \mathcal P_B,\mathcal F_B),
\]
with \(\omega_B\in\mathcal T^*\) retained in full until a safe quotient is proved.

Second, `virtual_support_automaton_construction.md` proved the abstract construction
that had previously been left implicit. A resolved source-locked presentation has a
canonical minimal future quotient. A universally bounded Markov-complete marked-cell
signature gives a uniformly finite zero-counter automaton. WAD coordinates may be
merged exactly only when every future observation factors through the quotient.
A checkpoint-pure run admits a parameterized macro carrying its exact length and
matrix power, but that macro does not preserve layerwise prefixes. These are
conditional finite-state theorems; none constructs the missing analytic virtual
carrier.

Third, `support_automaton_redteam.md` falsified four literal statements with explicit
matrices and found three further material boundary errors:

1. a transient zero singleton SCC was incorrectly classified as branching;
2. the declared row-outgoing convention conflicted with reverse chronological
   products;
3. spectral radius of an open transfer changed under endpoint relabeling;
4. the counter-pumping “only if” condition was too strong;
5. the transfer trichotomy omitted nilpotent extinction;
6. permutation layers proved only an identity interior gauge, not clone purity;
7. the clone connectivity lemma included an edgeless singleton counterexample.

The affected claims were repaired rather than ignored. The project now uses the
source-column convention
\[
  B_{\text{target},\text{source}},
  \qquad
  B_{[1,m]}=B_m\cdots B_1.
\]
`transfer_convention_and_frame.md` proves that a closed return changes by similarity
under a base relabeling, while an open transfer has no intrinsic spectral radius.
Entropy certification is therefore restricted to a closed repeatable framed return
or a canonical source endomorphism. Branching requires a cyclic non-simple SCC.
The Frobenius theorem now covers all \(\rho\le1\) by a condensation-DAG walk count,
including nilpotent extinction. Clone connectivity now requires positive recurrence
at each gate. The graph clone certificate and conditional KKL Value corollary are
separate.

The exact counter condition is now the reachable-fiber equality
\[
  \Phi(\nu+\eta)=\Phi(\nu+\Delta+\eta).
\]
Zero increment or fiber invariance is sufficient but not necessary for one path.
Support pumping retains an ordered nested history of contextual
prefix-face-neutral loop occurrences; it does not produce a freely reorderable
finite loop list.

`audit_transfer_regressions.py` now executes the orientation, endpoint-gauge, Boolean
support, zero-SCC/extinction, future-index, and counter-fiber examples on every
manual audit run. All current tests pass. They are regression guards only and do not
establish uniform virtual dynamics.

After these repairs, the addition of the proved abstract construction nodes, and the
explicit separation of raw virtual core-cocycle realization from its finite follower
quotient, the machine ledger validates 124 obligations:
9 imported, 90 proved internally, and 25 open. The audit is syntactic and does not
replace the semantic counterexample pass. MLC remains open.

## 2026-07-23 — Second red team, typed KKL incidence, and clone quarantine

The first automaton repair was subjected to a second independent adversarial pass.
Three additional bridge failures were found.

1. A bounded signature catalog does not bound transfer dimensions. The family with
   one state and one identity loop \(B=I_d\) has one signature while \(d\to\infty\).
2. Projecting counters or a stack away does not license support pumping. In
   \(\operatorname{Pref}\{a^n b\}\), every finite-control/support pair repeats, but
   every positive \(a\)-loop changes the exact exit memory.
3. WAD output observability does not construct a compositional quotient. With
   \(P=(1\ 1)\) and \(R=\operatorname{diag}(1,2)\), even zero terminal observations
   do not make \(PR\) factor through \(P\).

The cell-tree theorem now has separate hypotheses `CT0` and `CTM`:
\[
  d\le d_0,\qquad w\le w_0,
\]
and exact memory compilation must precede pumping. A WAD quotient must satisfy
\[
  P_{\rm out}R_\gamma=\bar R_\gamma P_{\rm in}
\]
for every enabled branch, in addition to the fixed-family output-observability
criterion. Configuration-neutral loops retain every emitted core, WAD, Value,
critical, error, and shear record. These repairs are documented in
`virtual_automaton_second_redteam.md`,
`virtual_support_automaton_construction.md`, and
`virtual_core_cocycle_program.md`.

A complete source-orientation audit then found that the checked KKL TeX uses its
symbol \(T_F\) with incompatible orientation cues. The safe source lock is the raw
source-to-target incidence
\[
  N_{\beta\gamma}
  =
  \#\{\alpha\in\iota^*\beta:f_*\alpha=\gamma\},
  \qquad
  B=N^{\mathsf T}.
\]
The KKL coordinate sums give \(Nv=\lambda v\) and
\(N^{\mathsf T}w=\lambda w\). Thus KKL \(v\) is project-left, KKL \(w\) is
project-right, and Value uses \(v^2w\). No unconditional equation involving the
ambiguous symbol \(T_F\) is used.

The same audit found a stronger source defect. Under the literal clone definitions,
the primitive graph
\[
  e\to a,\qquad a\to e,\qquad a\to b,\qquad b\to e
\]
with cross section \(\{e\}\) has clone Perron root
\(\lambda_n^{n+3}=\lambda_n+1\). KKL's printed
\(+\lambda^k\) reduced equation would instead force
\(\lambda_n^n=\lambda_n^{n+5}\), which is impossible. The advertised asymptotic
\(\lambda_n^n\to2\) still holds for this graph. Therefore the printed finite-\(n\)
bridge is refuted, while the limit is quarantined for a corrected independent proof
rather than declared false.

This supersedes the earlier log shorthand that treated the KKL clone equation and
limit proof as imported. `KKL_CLONE_EIGEN` is now open; the internal variable-clone
theorems remain proved only conditional on an independently verified typed clone
equation. `CLONED_VALUE_BLOCK_CONTRACTION` is correspondingly a conditional
implication.

The compactness pass also records that unbounded counters and finite stack words in
their discrete topology are not precompact. `H3_SYMBOLIC_SIDE_COMPACTNESS` now
requires them to be forgotten after closure, bounded, or continuously extended to a
proved compact end/cylinder topology.

The executable diagnostic suite now contains eleven tests: product order, typed
incidence and Value weights, endpoint gauge, Boolean support, zero-SCC/extinction,
future index, counter fibers, memory projection, WAD transport quotient, signature
versus dimension, and the quarantined clone exponent. All pass. They are finite
regressions, not analytic evidence for MLC.

After this pass the machine ledger validates 132 obligations:
8 imported, 95 proved internally, and 29 open. MLC remains open.

## 2026-07-23 — Corrected literal-clone theorem and sharp delayed margin

The quarantined fixed-cross-section problem has now been solved internally, without
rehabilitating the false printed KKL recurrence.
`corrected_clone_theorem_derivation.md` derives the literal row-source Schur
reduction
\[
  H(t)
  =
  t^{-1}D(tI-Q)^{-1}C
  =
  \sum_{k=2}^{K}t^{-k}R_k
\]
and proves the exact equation
\[
  \rho(H(\lambda_n))=\lambda_n^n.
\]
For every fixed strongly connected cross-section datum with
\(\rho(H(1))>1\), it follows that
\[
  \lambda_n\to1,
  \qquad
  \lambda_n^n\to\rho(H(1)),
\]
and the gate-normalized row-source right/project-left and project-right/row-source
left Perron vectors converge to the corresponding rays of \(H(1)\) and
\(H(1)^{\mathsf T}\). The statement is normalized on the fixed gate; whole-graph
normalization would be false.

Two independent red-team passes verified the block equations and found the exact
finite-family loss. If \(m\le d\), \(K\) is the actual maximum first-return edge
length, and \(n>K\), then
\[
  \lambda_n^n
  \ge
  \rho(H(1))^{n/(n+K)}.
\]
The auxiliary integer theorem was sharpened: every irreducible non-permutation
integer \(m\times m\) matrix satisfies
\[
  \rho\ge2^{1/m}.
\]
The proof uses two first-edge-distinct first-return loops and pigeonholes their
binary concatenations by total length; a directed \(m\)-cycle with one doubled edge
shows sharpness. Consequently,
\[
  \lambda_n^n>2^{1/(2d)}.
\]
For a separately source-licensed KKL complete block whose outgoing WAD satisfies
\(Y\le(f^r)^*X+E\) with \(r\ge n\),
\[
  V_{\rm out}\le2^{-1/(2d)}V_{\rm in}+V(E).
\]
The pullback exponent may exceed, but may not be shorter than, the graph delay.

For a weighted retained operator satisfying its own corrected equation at its own
root,
\[
  \widetilde q
  \ge
  \bigl((1-\epsilon)2^{1/d}\bigr)^{n/(n+K)},
\]
so strict expansion requires
\(\epsilon<1-2^{-1/d}\). An unweighted comparison at \(t=1\) is insufficient, and
one-sided lower domination alone does not give eigencone compactness. In the exact
bounded-entropy branch \(\rho(H(1))\le H\), \(n\ge K\), both reduced Perron rays have
coordinate ratio at most \(H^{2(d-1)}\), and clone-layer ratios add at most one
factor \(H\). The large-entropy finite-delay factor is \(H^{-1/2}\), not
\(H^{-1}\).

Adversarial limits remain explicit:

- \(n/K\to0\) destroys a uniform delayed multiplier;
- fixed-template convergence is not uniform over multiplicities varying with \(n\);
- primitive bases need not have primitive delayed clones;
- side edges, unequal delays, omitted occurrences, or a non-nilpotent active block
  change the reduced equation;
- a graph delay does not imply a sufficient KKL pullback exponent without the
  explicit coefficientwise relation \(Y\le(f^r)^*X+E\) and \(r\ge n\);
- the theorem is finite graph theory and does not realize Dudko's virtual core,
  WAD incidence, or outgoing geometric error.

The regression test now checks the negative-weight equation and multiplier bound for
twenty clone lengths while retaining the positive-weight no-go. The integration map
`corrected_clone_integration_map.md` records every downstream constant and status
change. `KKL_CLONE_EIGEN` is promoted to proved internally; the printed-equation
no-go remains proved. The machine ledger validates 132 obligations:
8 imported, 96 proved internally, and 28 open. MLC remains open.

## 2026-07-23 — Post-integration clone audit and exponent-alignment repair

Two independent read-only audits rechecked the integrated theorem, ledger, source
orientation, and every downstream Value claim. The negative-weight reduction, sharp
integer entropy gap, perturbation threshold, and exact eigencone bounds survived.
The audit found one substantive interface omission:

\[
\text{literal graph delay }n
\quad\not\Longrightarrow\quad
\text{actual WAD pullback exponent }r.
\]

KKL Value contraction supplies \(\lambda^{-r}\) only for an actual \(r\)-fold
pullback. Therefore a graph corridor of delay \(n\) gives the desired total factor
only after proving
\[
  Y\le(f^r)^*X+E,
  \qquad r\ge n.
\]
Without that inequality, a shorter realization can give only
\(\lambda_n^{-r}\to1\). The theorem, corridor certificate, ledger,
dependency audit, manuscript, transfer convention, README, and virtual-core task
now state this hypothesis explicitly. The strict Value inequality was also replaced
by a non-strict inequality so the zero WAD is included.

The complete KKL source confirms that equality would be too restrictive:
`not-all-good2.tex` uses \(g=f^{\mathrm{per}}\) for the WAD pullback while its
cross-section clone has length \(q-(2B+2)\), where \(B\) is the fixed
limb-occupancy bound. The internal
timing lemma therefore uses the sharp sufficient direction \(r\ge n\); extra endpoint
travel improves rather than harms the Value factor.

The audit additionally separated literal cloning, irreducible return entropy, and
KKL primitivity: periodicity of a reduced return matrix does not invalidate an exact
clone, while KKL's required aperiodicity must be checked independently. The source
no-go is no longer listed as a proof dependency of the independent corrected
theorem.

The new regression stress report
`corrected_clone_regression_stress.md` found no finite-graph counterexample across
exhaustive and seeded tests. It also isolates the sharp \(n=K\) boundary: equality
can occur for an imprimitive single-return-length base, whereas a primitive base
forces a submaximal return length and hence strict square-root expansion already at
\(n=K\). This refinement is documented but is not yet used to weaken the safer
realization guard \(n>K\).

## 2026-07-23 — KKL virtual-occupancy scope audit

The complete proofs of KKL Proposition 3.7, Proposition 3.8, Proposition 3.9,
and Remark 4.14 were checked line by line. The result is recorded in
`kkl_virtual_occupancy_source_audit.md`.

A live title/author/arXiv search also checked whether the DKL virtual
renormalization manuscript cited by KKL had become public. No public
manuscript was located on 2026-07-23, and KKL's own bibliography still labels
it “in preparation.” No result from that unavailable work is therefore
treated as an import.

One exact theorem is now imported. For every \(B,M\), KKL gives a threshold
\(A(B,M)\) such that, inside its full periodically repelling prime primitive
\(\psi\)-ql category, per-limb occupancy at most \(B\) and
\(\mathbb W(\mathcal R F)\ge A(B,M)\) imply the static alternative:
\(M\)-amplification, \(M\)-tameness, or \(M\)-wide controllable waves.
Remark 4.14 removes the other parabolic-boundedness clauses only from that
Proposition 3.7 split.

The audit rejects two tempting extensions. First, a count of selected virtual
components does not imply KKL's access-complete ideal multi-interval bound;
extra prime ends, fjords, dams, and omitted dynamically used components must be
included. Second, Remark 4.14 does not import the tame or wave closures.
Proposition 3.8 uses a full-period return, localization, selected-degree
control, WAD/Wanderers transport, and Value. Proposition 3.9 uses compatible
pulled markings through an \(O_B(q)\) fast-forward and critical-visit horizon.

Accordingly the former virtual-occupancy task is split into three independent
analytic obligations:

1. Virtual Section-4 Interface;
2. Virtual Tame Full-Return Lemma;
3. Virtual Long-Iterate Wave Lemma.

The finite-tree subproblem of the Section-4 interface was then closed in
`virtual_limb_marking_bound.md`. If a reduced anchored limb carrier contains
\(m\) non-anchor access-complete atoms, it has at most \(4m-2\) oriented tree
sides; charging at most two local ideal decorations at every prescribed
vertex, including the anchor, its complete multi-interval has at most \(6m\)
members. The proof is the exact
handshaking count for a minimal spanning tree. An embedded star with one
selected component and arbitrarily many proof-used access leaves shows why
selected-component occupancy alone is insufficient.

This reduction does not construct the access-complete virtual carrier. It
turns that part of the interface into the precise requirement of a uniform
marked-atom load or bounded-fiber assignment per limb.

The diagnostic regression suite exhausts every labelled reduced anchored tree
through seven vertices and every admissible marked subset. It verifies both
the \(2|E|+2|S|\le6m\) bound and its sharp anchor-charge case. This finite
test guards the bookkeeping only; the handshaking proof discharges the
mathematical claim.

The branch logic was then isolated in `virtual_branch_assembly.md`. To request
an output factor \(L\), the static split must be invoked at the wave-selector
parameter \(P=P_w(B,L)\). A tame outcome must close at that same \(P\);
a wave outcome closes at \(L\); an amplification outcome descends from \(P\)
to \(L\). Every high-type and large-width threshold is taken in one maximum.
A logical countermodel proves that tame and wave implications at two unrelated
input parameters do not suffice without a monotonicity or common-input
theorem.

The machine ledger now validates 138 obligations: 9 imported, 98 proved
internally, and 31 open. MLC remains open.

## 2026-07-23 — Section-4, tame, and long-Wave integration

Three independent proof-facing audits were integrated:
`virtual_section4_interface.md`, `virtual_tame_full_return.md`, and
`virtual_long_iterate_wave.md`. Promotion was deliberately limited to
source-locked native-category theorems, self-contained algebraic/combinatorial
lemmas, and conditional reductions whose realization hypotheses remain visible.

The Section-4 pass closes the formal static logic. A datum satisfying
`S4-AC`--`S4-END` and
\[
 D\ge\max\{1,5E_X(B)\}
\]
is amplifying, tame, or has a wide controllable wave. This does not construct
the datum. Nine concrete realization requirements remain open, including
access completeness, all-cycle width/WAD comparison, restriction
multiplicity, and faithful flux/endpoint decomposition.

The tame pass imports KKL Proposition 3.8 only in its full native category and
proves four internal reductions:

1. \(m_I\) quadratic encounters give selected degree \(2^{m_I}\);
2. marking growth linear in the full-return period is absorbed by a WAD lower
   bound linear in that period;
3. near-self-domination contradicts strict Value contraction when
   \(C_V\delta<1-\mu^{-1}\);
4. `VR0`--`VR5` and `VR7` imply the same-parameter tame closure in a realized
   KKL coordinate.

The geometric `VR` clauses and unified-chart closure `VR6` remain open. The
audit also proves a needed no-go: conjugating a general rotation \(a/q\) to
translation by one through modular relabeling does not preserve cyclic order,
so an order-preserving accelerated corridor must be constructed.

The Wave pass imports KKL Proposition 3.9 only in its full native category.
The complete source stopping time is conservatively bounded by
\[
 H_B(q)=(216B^2+1)(q+B+4).
\]
A conditional `WA1`--`WA12` reduction is proved through this horizon. A single
proper endpoint return of total degree two cannot realize KKL's terminal
degree-\(2^L\) fan for \(L\ge2\); the virtual construction must retain a
degree-one central corridor plus a bounded auxiliary marked fan. The remaining
irreducible Wave constructions are the marked interval action, critical-limb
alignment, and selected marked fast-forward fan.

The source check found no public version of the DKL virtual-renormalization
manuscript, which KKL still lists as in preparation. No unavailable result was
used. The dependency and adversarial audits now explicitly reject four
shortcuts: treating the abstract Section-4 theorem as a realization, replacing
critical-encounter control by component count, relabeling arbitrary rotations,
and using one degree-two return as the long-Wave fan.

After integration the machine ledger validates 149 obligations: 11 imported,
107 proved internally, and 31 open. All 13 diagnostic transfer regressions pass,
including the new parameter-mismatch, limb-tree, and clone-timing tests. These
finite tests validate bookkeeping and counterexamples only; they discharge no
analytic realization obligation. MLC remains open.

## 2026-07-23 — Selected marked fast-forward fan pass

The exact KKL fast-forward proof was re-read at the point where
\(N=q-B-j-2\). It uses one long pair \((f^N,\iota_N)\), a degree-one central
corridor, and terminal pieces of degrees \(2^m\), \(1\le m\le M\). Properness,
end-properness, and the itinerary proposition—not the degree bound alone—give
the vertical/outgoing/lost/amplifying exhaustion.

`selected_marked_fast_forward_fan.md` proves a simultaneous local-saturation
theorem. Given a finite full inverse-component tree and compact separated
obstacles, one root Jordan neighborhood can be chosen so that every selected
iterated pullback is a disjoint proper Jordan sheet inside its prescribed
neighborhood. The proof applies polynomial component shrinking simultaneously
to all vertices and then avoids the finitely many iterated critical values on
the root boundary. Each edge is conformal or quadratic according to whether
its target contains the critical value. Hence a branch with \(m\) critical
encounters has degree \(2^m\).

Selecting one common-depth branch for each \(m=0,\ldots,M\) gives the exact
finite fan degree
\[
 \sum_{m=0}^{M}2^m=2^{M+1}-1.
\]
Thus the unmarked proper-sheet and dyadic-degree layer is closed once the
inverse tree and obstacle separation are available.

The audit rejects a stronger promotion. The theorem does not construct the
inverse tree from the virtual carrier, complete prime-end/access marking,
cyclic order, \(\psi\)-ql immersion, itinerary exhaustion, or one-shot
extremal-width transport. Those are exposed as `SMF1`--`SMF8`. The correct
finite routing record is the marked fan
\[
 \mathfrak F_N=(\mathscr T_N,\kappa_N,\mathcal I_N,\mathcal E_N,\prec_N,\pi_N),
\]
not its scalar total degree.

An exact counterexample shows why the inverse-tree hypothesis cannot be
replaced by partial invariance. For \(f(z)=z^2\), the closed right half-disk
maps surjectively onto the closed unit disk; both are full and contain the
critical point/value. But the unique component of the unit disk's pullback is
the whole unit disk, not the half-disk. Thus `SMF1` must prove
pullback-component saturation.

The machine ledger now validates 151 obligations: 11 imported, 109 proved
internally, and 31 open. The diagnostic suite now has 14 passing tests,
including the exact dyadic fan sum; that arithmetic test does not validate
the analytic marking or width clauses. MLC remains open.

## 2026-07-23 — Saturated seed forest and ribbon-marking pass

Dudko's public Problem 4.4 passage was checked again. It proposes connected
hulls of Cantor small Julia sets with a finite portion of the critical orbit,
but supplies no public definition of pullback-component saturation or complete
access marking. KKL continues to list the DKL virtual-renormalization paper as
in preparation. No unavailable result was imported.

`saturated_virtual_seed_forest.md` closes three formal layers.

First, a finite forest of connected seeds satisfying
\[
 f(C_u)\subset H_v
\]
has a canonical saturation: the child carrier is the unique component of
\(f^{-1}(H_v)\) containing \(C_u\). With sibling component separation, this
is a disjoint full inverse forest; branch degrees are exactly \(2^m\).
The construction is unique relative to the root and monotone under root
enlargement.

Second, finite compact obstacles disjoint from the saturated carriers admit
simultaneous separated neighborhoods. If
\[
 f(E_u)\subset E_v\cup H_v,
\]
the excluded sets \(\Upsilon_v=H_v\cup E_v\) are stagewise forward closed and
give the exact complement inclusions. The relative-cover subgroup lift and
immersion properness remain separate.

Third, on the simultaneous Jordan fan, a finite root endpoint marking pulls
back as an orientation-preserving circle covering. A branch of degree \(d\)
has exactly \(d|P_r|\) pulled endpoints and intervals. The dyadic terminal fan
therefore has
\[
 |P_r|(2^{M+1}-1)
\]
of each. This is period independent when \(M\) and \(|P_r|\) are fixed.
The count is complete only after proving that every proof-used future end
projects to \(P_r\).

The unresolved geometric input is now the six-part Virtual Seed Certificate:
forward-coherent connectors, sibling separation, saturation-location control,
absorb-or-separate remainder, bounded root future completeness, and
relative-cover/immersion closure. Atomwise dynamics, component labels, and
degree counts do not imply these clauses.

The machine ledger now validates 154 obligations: 11 imported, 112 proved
internally, and 31 open. MLC remains open.

## 2026-07-23 — Endpoint-birth accounting

Root future completeness was attacked quantitatively. For a sequence of
proper boundary coverings of degrees \(d_j\), let \(b_j\) be the number of
genuinely new proof-used endpoints first exposed at stage \(j\), after
removing endpoints already pulled back from the next marking. The exact
recurrence is
\[
 p_j=d_jp_{j+1}+b_j,
\]
hence
\[
 p_0
 =
 D_{0,N-1}p_N
 +
 \sum_{j=0}^{N-1}D_{0,j-1}b_j.
\]

This proves two sharp conclusions. In a degree-one central corridor, one new
endpoint per stage gives \(p_0=p_N+N\), so a bounded local incidence statement
is not period independent. Conversely, if all genuine births vanish before a
terminal window of depth \(M\), with degrees at most two and births at most
\(b_*\) there, then their total charge is at most
\[
 b_*(2^M-1),
\]
independent of the fast-forward length.

The new Virtual Endpoint-Birth Certificate requires a stage ledger, zero
births through the translation interior, bounded terminal births, the full fan
sum, and access completeness. Similar drawings or equal limb labels do not
identify prime ends; future equivalence must be proved.

The machine ledger now validates 155 obligations: 11 imported, 113 proved
internally, and 31 open. A new exhaustive regression checks the recurrence for
all degree-one/quadratic strings through length six with small birth data.
MLC remains open.

The KKL pullback description was then converted into a local no-birth
criterion. On a degree-one marked interval, if the pulled carrier has no new
component attached there, the immersion pullback is one interval, and the
polynomial map is conformal on both endpoint prime ends, then every pulled
endpoint already comes from the next marking and \(b_j=0\). Thus the virtual
central-corridor target is local carrier equality, not equality of coarse
translation labels.

After this refinement the machine ledger validates 156 obligations:
11 imported, 114 proved internally, and 31 open.

## 2026-07-23 — KKL corridor attachment-support source audit

KKL's native no-birth mechanism was checked against both the public HTML and
the local arXiv source. Proposition 6.5 gives an exact decomposition of an
ideal interval pullback: the ordinary inverse interval plus the ideal
boundaries of every component of
\(\mathcal T'\setminus\mathcal T\) attached there. Proposition 6.7 proves
proper action on the central limb range from the actual equality
\[
 \mathcal T'\cap\mathcal L_{[B,q-B-2]}
 =
 \mathcal T\cap\mathcal L_{[B,q-B-2]}.
\]
This is source evidence for local carrier equality in KKL's full
Hubbard-tree category only; it does not transfer by matching virtual labels.

The new abstract Attachment-Support Reduction proves that endpoint births
vanish outside the support of attached pulled-carrier excess. If that support
and every genuine birth lie in a terminal depth-\(M\) window with degree at
most two and at most \(b_*\) births per stage, then
\[
 \mathfrak b_0\le b_*(2^M-1).
\]
The virtual Wave target is now the period-independent Bounded
Attachment-Support Theorem: empty support in the degree-one interior,
bounded access-complete support in the defect windows, and proper/end-proper
relative-cover lifts through the full horizon.

The machine ledger now validates 159 obligations: 12 imported, 115 proved
internally, and 32 open. The new open count is intentional: a previously
implicit geometric assumption has been made explicit. A sixteenth regression
checks the terminal attachment-window bound and the linear hidden-attachment
failure in a degree-one corridor. MLC remains open.

## 2026-07-23 — One-root pullback carrier reduction

Dudko's public Problem 4.4 paragraph was checked again. It proposes connected
hulls of Cantor small Julia sets containing the critical orbit through an
appropriate number of first returns, but gives no canonical connectors,
component routing, or stability under future completion.

The new Root-Pullback Carrier Theorem removes independent stagewise connector
choices. For one full root continuum \(H_r\), each complete required package
must lie in one component of \(f^{-n}(H_r)\); those components must realize
the prescribed parent map, and distinct selected sheets must be distinct
components. These conditions are equivalent to a finite saturated carrier
forest.

The same theorem supplies two hard compatibility checks:

- a target carrier gives a degree-one edge exactly when it avoids the
  critical value;
- enlarging the root can only merge pullback-component classes.

Thus a critical orbit label cannot be placed in the target of an alleged
degree-one corridor, and root future completeness cannot be added after
sheet separation without rechecking all collisions. The live Virtual
Root-Carrier Certificate asks for one root satisfying all packages, routing,
critical windows, separation, and admissible location simultaneously.

The ledger now validates 162 obligations: 12 imported, 117 proved internally,
and 33 open. MLC remains open.

## 2026-07-23 — Formal LaTeX manuscript inception

The proof-facing material has been assembled into a source-locked LaTeX
manuscript, `latex/main.tex`. The first release is 31 pages and contains:

- a status contract that forbids presentation of the work as an unconditional
  MLC proof;
- a source and notation ledger;
- the unmarked satellite obstruction and corrected backward-record mechanism;
- formal root-carrier, endpoint-birth, attachment-support, and finite-fan
  theorems with proofs;
- a conditional MLC theorem whose hypotheses remain visibly open;
- the combined Virtual Seed and Attachment theorem as the next geometric gate;
- ten adversarial tests and a promotion rule; and
- a complete appendix generated from `proof_obligations.json`.

The generator rejects duplicate obligation IDs, unknown statuses, missing
dependencies, empty evidence fields, and any ledger that promotes `MLC` away
from `open`. The release validation produced:

```text
ledger: valid (162 obligations)
statuses: imported=12, proved=117, open=33
target: MLC [open]
diagnostic transfer regressions: 16 passed
LaTeX/package/box/reference/citation warnings: 0
PDF pages: 31
```

Representative pages and the generated appendix were rendered and inspected
for clipping, overlap, broken glyphs, and status-legibility. Full PDF text was
also extracted to verify the disclaimer, conditional label, open-obligation
count, and named next gate. These checks validate synchronization and
presentation; they do not discharge any mathematical obligation.

## 2026-07-23 — Corridor attachment-transport reduction

Dudko's public Interpolation Problem 4.4 and KKL Propositions 5.7, 6.5, and
6.7 were rechecked against the public HTML and the local KKL source. Dudko
proposes partially invariant connected hulls but does not specify canonical
connectors, a commuting pulled/immersed carrier-pair map, or an
attachment-free anchor. KKL use the stronger native equality
\(\mathcal T'_j=\mathcal T_j\) throughout their central range.

The new Corridor Attachment Transport Theorem proves that, if consecutive
actual carrier pairs fit into a commuting square of orientation-preserving
homeomorphisms extending to the access-complete prime ends, then:

\[
  \mathcal A_{j+1}(I)
  \longleftrightarrow
  \mathcal A_j(\phi_j(I)),
  \qquad
  \operatorname{Att}_j
  =
  \phi_j(\operatorname{Att}_{j+1}).
\]

Therefore one attachment-free anchor clears the entire degree-one central
corridor. Conversely, a persistent attachment that exposes a genuine
proof-used endpoint gives at least linear endpoint charge. Root routing does
not imply the commuting ambient-pair square, and one anchor is useless
without naturality; both failures have explicit finite countermodels.

The virtual gate is now split into:

1. `VIRTUAL_CORRIDOR_PAIR_NATURALITY`;
2. `VIRTUAL_ATTACHMENT_FREE_ANCHOR`; and
3. the remaining bounded defect-window and relative-cover clauses of
   `VIRTUAL_BOUNDED_ATTACHMENT_SUPPORT`.

The machine ledger and regression suite report:

```text
ledger: valid (165 obligations)
statuses: imported=12, proved=118, open=35
target: MLC [open]
diagnostic transfer regressions: 17 passed
```

This is a strict reduction of the central attachment problem, not a
construction of Dudko's virtual carrier.

## 2026-07-23 — Univalent carrier-pair construction and anchor obstruction

The planned pair-naturality pass rechecked Dudko's Interpolation Problem 4.4,
KKL Propositions 5.7, 6.5, and 6.7, and the 2025
\(\psi^\bullet\)-ql neutral-bounds scope. KKL's native central argument has
actual carrier equality; Dudko's published virtual-hull paragraph does not
define a canonical hull or an interface-exhaustion theorem.

Given one actual anchor pair, transporting the complete pulled/immersed pair,
packages, obstacles, and ideal marking through critical-value-free conformal
corridor branches proves the commuting square. Conformal functoriality on the
proof-used complement localizations transports the prime-end marking and its
cyclic order without assuming Euclidean boundary local connectivity.

The anchor construction itself fails at the published-hypothesis boundary.
The interval
\[
  T=[-1,1]
\]
and the triod
\[
  T^\dagger=[-1,1]\cup[0,i]
\]
are full connected carriers containing the same package and carrying the same
identity dynamics on \(T\). The pair \(T\subset T\) is attachment-free, while
\(T\subset T^\dagger\) has a hidden vertical branch at \(0\). Thus the
published description does not force anchor equality.

The replacement invariant is the least fixed point \(C_\infty\) of a finite
inflationary monotone attachment/access/transport completion operator. It
stabilizes after at most the number of omitted cells, transports under
conjugate corridor maps, and is contained in every attachment-complete
enlargement. Any sheet, critical-word, obstacle, access, or localization
collision in \(C_\infty\) is therefore unavoidable under monotone absorption.

The machine results are:

```text
ledger: valid (168 obligations)
statuses: imported=12, proved=121, open=35
target: MLC [open]
diagnostic transfer regressions: 20 passed
```

Neither `VIRTUAL_CORRIDOR_PAIR_NATURALITY` nor
`VIRTUAL_ATTACHMENT_FREE_ANCHOR` is promoted. The next actual theorem must
construct a canonical interface carrier satisfying KKL-style component
exhaustion, or prove that its least attachment-orbit closure is collision-free
and analytically realizable.

## Promotion protocol

Before changing an obligation from `open` to `proved` or `imported`, record:

1. the exact statement and all quantifiers;
2. the source label or an internal proof;
3. constant dependence;
4. an adversarial example aimed at each hypothesis;
5. the dependency-ledger update and audit result.

## 2026-07-23 — Canonical interface carrier and protected-access obstruction

The canonical-interface pass froze the proposed stage datum as an analytic
certificate
\[
  (U^-,U^+,F,\mathscr K,\mathscr O,\mathscr G,\mathscr R,\mathscr W;
    \mathscr Q),
\]
where \(\mathscr Q\) records every actual object read by Wave, Wanderers,
quasi-additivity, covering, or width arguments.  For a finite proof-use
ledger, the typed union of these supports is the unique minimal complete
inventory.  This closes the omission audit but does not construct a connected
carrier.

On any fixed finite resolved universe, the combined package, transport,
fullification, access, attachment, and collision rules have one
order-independent least fixed point when every rule is inflationary and
monotone.  Exact agreement with the planar construction requires the cell
quotient to be implication-complete and implication-sound.

The attempt to obtain the missing geometry by taking a least connected full
hull fails exactly.  The upper and lower semicircles joining \(-1\) to \(1\)
are full connected carriers whose intersection is the disconnected package.
Therefore no inclusion-minimal carrier exists, even with identity dynamics.
A regulated connector system and its access/isotopy class are new required
data.

The pass also produced a critical-value-free analytic obstruction for the
actual quadratic map \(f(z)=z^2\).  On the disk
\[
  U^-=\{|z-3/2|<1\},
\]
the map is conformal.  Let \(T_0=[1,2]\) and let \(T'_0\) be the closed upper
half-disk with diameter \(T_0\).  The first excess
\[
  X_0=T'_0\setminus T_0
\]
has attachment trace \(T_0\), right-sheet itinerary
\(X_0\mapsto z^2(X_0)\), and zero critical word.  Monotone absorption forces
the upper half-neighborhood of \(3/2\) into the carrier and therefore erases
the protected upper prime-end access at \(3/2\).  The collision tuple has
only its access coordinate nonzero.

The replacement invariant now retains:

1. the least absorbed-cell closure;
2. the complete collision tuple;
3. every full attachment trace \(\overline X\cap T\); and
4. the partial survival map on protected accesses.

This is the exact failure outcome required by the research pass.  It is an
obstruction to deriving the carrier theorem from current public hypotheses,
not a counterexample to a future virtual-renormalization construction or to
MLC.  `VIRTUAL_CANONICAL_INTERFACE_CARRIER`,
`VIRTUAL_CORRIDOR_PAIR_NATURALITY`,
`VIRTUAL_ATTACHMENT_FREE_ANCHOR`, and
`VIRTUAL_BOUNDED_ATTACHMENT_SUPPORT` remain open.

The machine ledger after integration reports:

```text
ledger: valid (173 obligations)
statuses: imported=12, proved=125, open=36
target: MLC [open]
diagnostic transfer regressions: 23 passed
```

## 2026-07-23 — Universal protected-tower closure proposition

The global closure pass introduced one exact open proposition rather than
relabeling the existing gaps as a theorem. The Universal Protected-Tower
Compactness and Rigidity Proposition (`UPTCR`) has six independently
auditable clauses:

1. canonical protected carriers built from rooted predecessor puzzle cells;
2. exact analytic carrier realization through every complete Wave horizon;
3. a uniformly finite, Value-observable response state;
4. a universal backward transition with a complete discounted error charge;
5. coercive compactness in an explicit marked topology; and
6. uniformly quasiconformal tower rigidity, no invariant line fields, and a
   connected relative parameter-neighborhood basis.

The source boundary was rechecked against the complete public HTML sources.
Dudko's Interpolation Problem 4.4 remains a proposed virtual-Julia-set
strategy and does not supply these clauses. KKL Theorem B remains restricted
to prime primitive types with both beau bounds and bounded puzzle
Teichmüller diameter; it is not used as a mixed-tower rigidity theorem.

The pass proves two logical results. First, nested nonempty compact sets with
singleton intersection have diameters tending to zero. Second, if all six
UPTCR clauses hold, the backward-record lemma bounds the calibrated
potential, UPTCR-5 supplies marked compactness, UPTCR-6 makes the full
parameter fiber a singleton, and the connected relative parapuzzle
neighborhoods shrink. Combined with Yoccoz's complementary theorem, this
implies MLC.

Only the conditional implication is promoted. The new ledger nodes are:

- `UNIVERSAL_PROTECTED_TOWER_CLOSURE` — open;
- `UPTCR_IMPLIES_MLC` — proved, with UPTCR listed as an open hypothesis.

`MLC`, `H1_MARKED_CONSTRUCTION`, `MBTT`, `H3_COERCIVITY`, and
`H4_RIGIDITY` remain open. The live machine snapshot after insertion is:

```text
ledger: valid (175 obligations)
statuses: imported=12, proved=126, open=37
target: MLC [open]
diagnostic transfer regressions: 26 passed
```

## 2026-07-23 — Independent UPTCR cross-validation

The UPTCR statement, its conditional implication, and their source boundary
were audited independently in `uptcr_cross_validation.md`.  Three material
errors were found and corrected before any attempt at promotion:

1. The degree quantifier now applies to the selected quadratic return spine:
   it has exactly one declared degree-two stage.  Auxiliary fan branches keep
   their complete critical words and have degree \(2^{m(\beta)}\); they are
   not falsely declared univalent.
2. A bounded defect window does not legalize a fatal sheet, critical,
   obstacle, access, or localization collision.  Analytic realization is
   permitted only after retiming or replacement produces a protected local
   model with zero collision invariant.
3. The entropy/regularization/transient alternatives need not be disjoint.
   The proposition now requires at least one certified route, with a fixed
   priority rule used only to make the bookkeeping deterministic.

The implication `UPTCR_IMPLIES_MLC` was then reproved with the previously
implicit steps made explicit: a nonzero invariant Beltrami coefficient
defines an invariant line field, absence of such a field forces the
normalized sphere conjugacy to be conformal, and coefficient comparison for
monic centered quadratics forces \(c=c'\).  The relative local-connectivity
step now includes the radius argument inside the relevant parameter locus.

The unconditional proof attempt was run in dependency order and stops at
UPTCR-1.  The available source data do not provide the regulated connector
and protected-access survival theorem needed to turn the finite
predecessor-cell inventory into an actual analytic carrier.  The failure is
sharp: the \(z^2\) upper-half-disk example has a critical-value-free
univalent branch, but monotone absorption erases a protected prime-end
access.  This refutes that proposed construction inference; it is not a
counterexample to UPTCR or MLC.

The synchronized machine snapshot is:

```text
ledger: valid (176 obligations)
statuses: imported=12, proved=127, open=37
target: MLC [open]
diagnostic transfer regressions: 29 passed
```

`UPTCR_CROSS_VALIDATION` is proved.  `UNIVERSAL_PROTECTED_TOWER_CLOSURE`,
`MLC`, `H1_MARKED_CONSTRUCTION`, `MBTT`, `H3_COERCIVITY`, and `H4_RIGIDITY`
remain open.

## 2026-07-23 — Protected regulated connector realization

The immediate UPTCR-1 pass separates topological realization from virtual
dynamical selection.

The new proved theorem starts from pairwise disjoint full root-shadow
clusters, explicit prime-end crosscut chains, free singleton attachment
ports, and an embedded finite ribbon tree avoiding every protected collar
and forbidden obstacle. The resulting union is full by the Janiszewski
one-point attachment argument. Because the connector misses the terminal
crosscut domains, the same nested chains remain prime-end chains of the new
complement; disjoint terminal domains prove injection, and their separation
order proves cyclic-order preservation. An orientation-preserving conformal
homeomorphism of Jordan localizations transports the entire construction
exactly. No local connectivity of an atom is used.

The source audit identifies KKL's native Hubbard-tree construction as the
correct positive control. In their non-locally-connected case the tree is
lifted from the locally connected rational-lamination model. This motivates
the canonical virtual candidate
\[
  H_{\rm lam}
  =
  \operatorname{Fill}\bigl(\pi^{-1}(T_{\rm com})\bigr).
\]
Monotonicity of \(\pi\) proves that this candidate is connected, but does not
prove that a projection fiber or filled complementary component avoids a
protected collar. Nor does it prove that every disconnected stage package
lies in the prescribed iterated pullback component.

Accordingly:

- `PROTECTED_REGULATED_CONNECTOR_REALIZATION` is proved;
- `VIRTUAL_PROTECTED_ROUTING_CERTIFICATE` is open; and
- `VIRTUAL_CANONICAL_INTERFACE_CARRIER`, UPTCR-1, UPTCR, and MLC remain
  open.

The first live failure record now names the block, stage, offending
projection fiber/edge/component, full attachment trace, protected chain,
complete critical word, collision coordinate, and localization. The three
new diagnostics check ribbon-boundary naturality, the singleton-trace/collar
gate, and the \(4s-6\) conditional side bound. Their first run exposed and
corrected the special two-leaf edge count.

```text
ledger: valid (178 obligations)
statuses: imported=12, proved=128, open=38
target: MLC [open]
diagnostic transfer regressions: 32 passed
```

## 2026-07-24 — Protected free-component criterion

The next UPTCR-1 pass removes the remaining arbitrary tree-selection step.
For a future-complete finite root package, all root-shadow atoms, terminal
protected collars, separated obstacles, the critical exclusion, and the
localization boundary are frozen first.  Their complement is the free
routing domain.

`virtual_protected_routing_domain.md`, Theorem 4.1, proves that a protected
ribbon-routing carrier exists exactly when one component of that free domain
has simultaneous singleton ports to every required atom.  The forward
direction is immediate from any protected connector.  In the reverse
direction, the port forest is joined by finitely many polygonal paths inside
the common open component, the resulting planar graph is subdivided at
crossings, and an inclusion-minimal connected subgraph is a finite tree.
The previously proved connector-realization theorem then gives fullness,
prime-end survival, cyclic order, and univalent naturality.

The contrapositive supplies an exact failure certificate: the first collar,
obstacle, critical exclusion, localization boundary, or late root shadow
that separates two required port classes cannot be repaired by further
monotone connector enlargement inside the same localization.  Every
connected joining set must meet the forbidden separator.

The current public sources do not prove that actual virtual-Molecule data
have the common component.  Dudko supplies only the connected-hull strategy,
while KKL still cite the Dudko--Kahn--Lyubich construction as in preparation.
Therefore:

- `PROTECTED_FREE_COMPONENT_CRITERION` is proved;
- `VIRTUAL_COMMON_FREE_COMPONENT` is open;
- `VIRTUAL_PROTECTED_ROUTING_CERTIFICATE`, UPTCR-1, UPTCR, and MLC remain
  open.

Two new finite regressions check the common-component criterion and the
failure caused by a late forbidden bridge insertion.

```text
ledger: valid (180 obligations)
statuses: imported=12, proved=129, open=39
target: MLC [open]
diagnostic transfer regressions: 34 passed
```

## 2026-07-24 — Augmented-atom common-domain reduction

The direct attack on `VIRTUAL_COMMON_FREE_COMPONENT` separates one fully
provable planar step from the still-missing virtual dynamics.

For the final finite Wave horizon, assign every protected collar, critical
exclusion, and ambient obstacle either to one root-shadow atom or to one
separated obstacle seed.  Fullify each connected assigned seed only after
the assignment is complete.  An augmented-atom packet requires the
resulting full continua to cover the frozen forbidden inventory, remain
pairwise disjoint and compactly inside the Jordan localization, and retain
one explicit pairwise disjoint unprotected singleton port arc on every
original atom.

`virtual_common_free_component.md`, Lemmas 4.1--4.2, prove the topological
core.  Compacta Alexander duality identifies connectedness of the complement
with vanishing first Čech cohomology.  Each full continuum has vanishing
first Čech cohomology, and finite additivity over pairwise disjoint compacta
gives the same for their union.  Adding the exterior of the Jordan disk as
one more full continuum proves that the augmented free domain is connected.
The explicit port arcs therefore lie in one component of the original free
domain.  The previously proved free-component criterion then constructs the
protected connector.

The proof uses arbitrary-compacta Čech duality, not the locally contractible
special case, and therefore does not assume local connectivity of any
root-shadow atom.  It is qualitative and supplies no period-independent
bound on atom, obstacle, port, or ribbon-side count.

The adversarial audit identified five distinct failure coordinates:
coverage, disconnected assignment, post-fullification merger, localization
escape, and port loss.  A surrounding annulus gives the sharp diagnostic.
If it is fullified as a separated obstacle, it swallows the enclosed atom;
if assigned to that atom, it makes the original atom interior to the
augmentation and destroys every singleton port.  The same annulus also
gives an exact underdetermination model: the atoms, connected full carrier,
and identity package dynamics can be held fixed while the completed free
domain changes from passing to failing `VCFC`.

This underdetermination model is not an actual quadratic virtual-Molecule
counterexample.  It proves only that Dudko's public connected-hull paragraph
does not imply the needed certificate.  KKL's native Hubbard tree remains a
positive control in the primitive category, and their bibliography still
lists the DKL virtual-renormalization manuscript as in preparation.

Accordingly:

- `ALEXANDER_DUALITY_COMPACTA` is imported with its exact compacta scope;
- `AUGMENTED_ATOM_COMMON_DOMAIN` is proved;
- `VIRTUAL_AUGMENTED_ATOM_PORT_CERTIFICATE` is open;
- `VIRTUAL_COMMON_FREE_COMPONENT`, UPTCR-1, UPTCR, and MLC remain open.

Two new finite-cell diagnostics check a collision-free augmented packet and
the annular merger/port-loss audit.  They are regression tests only.

```text
ledger: valid (183 obligations)
statuses: imported=13, proved=130, open=40
target: MLC [open]
diagnostic transfer regressions: 36 passed
```

## 2026-07-24 — Fixed augmented-packet closure and port audit

The next `VAAPC` pass removes two formal ambiguities without claiming the
missing virtual dynamics.

`augmented_packet_closure_audit.md` proves that planar fullification is a
closure operator and, in particular,
\[
  \operatorname{Fill}(\operatorname{Fill}(K)\cup L)
  =
  \operatorname{Fill}(K\cup L).
\]
Therefore processing finitely many pieces assigned to one fixed packet in
any order always produces the filled hull of their union.  A favorable
processing order cannot avoid a collision in the final fixed assignment.

The completed-packet audit now retains an actual witness point and, on each
side, either the raw seed or the bounded complementary chamber that contains
the witness.  Filled mergers and localization escapes persist under
monotone same-label enlargement.  The same monotonicity shows that an empty
original-atom exposure locus cannot be repaired merely by adding more
material to that packet.

The port clause also simplifies.  Once the completed packets are pairwise
disjoint and every original atom has one actual unprotected access arc from
the complement of its own packet, compact separation allows all arcs to be
truncated inside pairwise disjoint packet neighborhoods.  Hence long
representatives crossing is not a new obstruction.  The live issue is
individual exposure of the **original** atom, not global untangling.

The public-source audit was repeated against the hash-locked Dudko and KKL
TeX files and a fresh exact-title search.  Dudko still supplies only the
connected-hull proposal, KKL supplies its native complete Hubbard tree, and
the detailed virtual-renormalization manuscript remains unavailable.
Consequently no actual-block obstruction tuple is fabricated.

The live dynamical certificate is now split into:

- `VAAPC-I`: frozen actual component inventory and typed assignment;
- `VAAPC-C`: zero collision for the unique completed packets;
- `VAAPC-P`: one actual unprotected original-atom exposure per atom;
- `VAAPC-H`: full-packet transport through the complete horizon; and
- `VAAPC-U`: period-independent incidence or faithful compression.

`AUGMENTED_PACKET_CLOSURE_AUDIT` is proved.
`VIRTUAL_AUGMENTED_ATOM_PORT_CERTIFICATE`,
`VIRTUAL_COMMON_FREE_COMPONENT`, UPTCR-1, UPTCR, and MLC remain open.

```text
ledger: valid (184 obligations)
statuses: imported=13, proved=131, open=40
target: MLC [open]
diagnostic transfer regressions: 39 passed
```

## 2026-07-24 — VAAPC-I horizon-first inventory audit

The next pass attempted to instantiate the first live virtual clause,
`VAAPC-I`, from the hash-locked Dudko and KKL sources.

The attempt stops before packet geometry.  Dudko TeX lines 875--892 define
the virtual-Molecule copy chain and propose partially invariant connected
hulls carrying the critical orbit for an “appropriate number” of first
returns.  They do not define that number, a stopping rule, or a stopping
interface.  This is the first missing field: without a terminal stage,
“through last proof use” has no endpoint and there is no finite stage set on
which to enumerate components, collars, obstacles, accesses, or selected
transport branches.

The new note `vaapc_inventory_source_audit.md` formalizes the issue using a
finite typed dependency graph.  A proof-use seed forces every record
reachable along attachment, route, critical-word, access, or last-use
dependencies.  Theorem 4.1 proves:

\[
 I(\mathcal H)
 =
 \operatorname{Reach}^{*}_{E_{\mathcal H}}(S_{\mathcal H})
\]

is the unique least inventory for a fixed finite horizon.  Under an
extension \(\mathcal H\preceq\mathcal H'\), it is monotone, and its old-stage
slice is unchanged exactly when no extended seed has a dependency path to
an old omitted record.  A three-record regression
\[
 S=\{a\},\qquad S'=\{a,c\},\qquad c\to b
\]
checks the minimal late-use obstruction.

The audit also proves that the unlabelled dependency closure does not choose
packet labels.  Two geometric realizations can have the same unlabelled
graph while one declares a component separated and the other attaches it to
an atom.  The source attachment/routing data must decide the assignment.

KKL's native Hubbard tree remains a positive control.  It cannot be copied
to the partial virtual carrier without a typed bridge preserving every
proof seed, actual component incidence, dependency path, selected branch,
critical word, sheet, and proof-used prime end.  The checked KKL source
constructs no such bridge and still points to the virtual-renormalization
work as forthcoming.

The exact first replacement input is now the open
`VIRTUAL_WAVE_HORIZON_CERTIFICATE`: construct the finite stopping interface,
stage branches, complete proof ledger, resolved component/dependency
universe, and final-root-enlargement stability theorem for every actual
virtual-Molecule block.  Only afterward can the typed part of `VAAPC-I` and
the packet collision/port audits be attempted.

No analytic counterexample is claimed.  The emitted tuple has
\(N_{\rm stop}=\bot\) and records source non-instantiation, not failure of an
actual block.

```text
ledger: valid (186 obligations)
statuses: imported=13, proved=132, open=41
target: MLC [open]
diagnostic transfer regressions: 42 passed
```

## 2026-07-24 — Virtual Wave Horizon Certificate proof pass

The KKL Wave proof was re-read from the hash-locked v1 TeX, including the
ideal-marking and covering/immersion appendices.  The direct citation
universe of the Wave section contains 53 internal labels and one
bibliographic key.  The native stopping recursion is now explicit:

\[
  N_b=216b^2
\]

is the forbidden number of waves in a successive critical-visit chain.
The theorem-call recursion therefore terminates before it forms such a
chain.  Each selected visit records its own finite iterate \(r_\nu\), and
the exact dynamical horizon is the finite sum of those witnessed words.
No uniform iterate sum was inferred.

The native analytic branches were recorded as
\((f^r,\iota_r)\) on \(f^{-r}(U)\setminus f^{-r}(T)\), with exact marked
action \((f^r)_*\iota_r^*I=F_*^rI\).  The fast-forward support has a
degree-one central part and degree-\(2^m\) auxiliary ends.  Two v1 source
defects were quarantined: the undefined exponent at KKL line 1789 and the
malformed wording at line 1260.

`RESOLVED_FINITE_WAVE_HORIZON_COMPILER` is proved.  For a finite resolved
analytic decision program it gives a maximal finite iterate horizon, the
least complete proof-use inventory, the order-independent least
simultaneous final-root closure, and the exact program-extension criterion.

Virtual instantiation stops at the first analytic field:
`VIRTUAL_WAVE_MARKED_CORRESPONDENCE`.  The checked sources do not construct
the completed virtual marked complement or the covering/immersion pairs
with proper/end-proper action.  This is a missing theorem, not a claimed
counterexample.

```text
ledger: valid (189 obligations)
statuses: imported=13, proved=134, open=42
target: MLC [open]
diagnostic transfer regressions: 47 passed
```

`VIRTUAL_WAVE_HORIZON_CERTIFICATE`, `VAAPC-I`, UPTCR, and MLC remain open.

The warning-free 53-page manuscript was extracted and all pages were
rendered and inspected.  Release SHA-256:
`36013EC83F332A24C49E65BC972F4B0AD1A56E167B22A3F9F96D886B88E859EC`.

## 2026-07-24 — Virtual Wave Marked Correspondence proof pass

The marked-correspondence gate was decomposed before attempting the actual
virtual construction.  Four generic results are now proved:

1. actual paths in a typed return graph form a horizon-independent
   prefix-closed language and retain exact iterate sums;
2. a nondegenerate full carrier \(H\) containing every critical value of a
   polynomial return \(R\) and satisfying \(R(H)\subset H\) yields the
   actual complement pair \((R,\iota)\);
3. exact marked action is equivalent to inclusion of the two prime-end
   endpoint pullbacks \(E^\iota\subset E^g\); and
4. marked action survives final-root enlargement under commuting analytic
   squares and exact injective prime-end inverse-image transport.

An exterior-disk countermodel exposed a missing dependency.  For
\[
  g(z)=z^2,\qquad \iota_\alpha(z)=e^{i\alpha}z,
\]
the carrier and degree data are independent of \(\alpha\), but the marking
with endpoint \(1\) acts only for \(\alpha=0,\pi\pmod{2\pi}\).  Thus
relative-cover existence does not fix the deck/prime-end phase.

The replacement record stores the complete target and pulled endpoint
sets, boundary transition, normalized phase, subgroup map, and
proper/end-proper flags.  The actual virtual gate is now split into the
open `VIRTUAL_RETURN_BRANCH_LANGUAGE`,
`VIRTUAL_PROVISIONAL_COMPLEMENT_PAIR`, and
`VIRTUAL_ACCESS_ACTION_CERTIFICATE`.

```text
ledger: valid (196 obligations)
statuses: imported=13, proved=138, open=45
target: MLC [open]
diagnostic transfer regressions: 52 passed
```

`VIRTUAL_WAVE_MARKED_CORRESPONDENCE`,
`VIRTUAL_WAVE_HORIZON_CERTIFICATE`, `VAAPC-I`, UPTCR, and MLC remain open.

The warning-free 56-page manuscript was extracted, all pages were rendered,
and every contact sheet was inspected, with full-resolution checks of the new
marked-correspondence section and the final ledger pages.  Extracted text
confirms that all three new source-facing subgates, the marked-correspondence
gate, the horizon certificate, UPTCR, and MLC are printed as open.  Release
SHA-256:
`26124529EB1979957E2A5971BC873C7CC40EBB9A85550066232178818C7A780B`.

## 2026-07-24 - Virtual Return Branch Language proof pass

The first source-facing marked-correspondence subgate was decomposed at the
analytic-domain level. A directed graph of actual edge labels is
insufficient because a labeled edge sequence can have no nonempty composite
domain. The new return-atlas compiler defines each child on an actual
component
\[
 C\in\pi_0\bigl(\Phi_\nu^{-1}(A_b)\bigr)
\]
and proves that its composite is exactly
\(f^{S_\nu+q_b}|_C\), with chronological metadata.

`DEMAND_CLOSED_RETURN_ATLAS_COMPILER` and
`RETURN_ATLAS_ENLARGEMENT_NATURALITY` are proved. Enlargement preserves old
words under an injective exact morphism, while full no-birth/no-loss
stability requires a bijection on demanded branch-component pairs at every
prefix.

`RETURN_BASE_UNDERDETERMINATION` is also proved explicitly. For
\(f(z)=z^2-1\) and seed \(\{-1\}\), the Jordan disks
\(D(-1,1/4)\) and \(D(-1/2,3/4)\) give first-return times two and one.
Therefore a compact virtual seed does not define a return branch before an
open return localization is selected.

The checked sources do not supply that localization. Dudko's virtual
paragraph gives the parameter-copy chain and strategy-level connected hull,
while KKL's bibliography classifies the promised DKL virtual-renormalization
work as unpublished and in preparation. The exact replacement inputs are
the open `VIRTUAL_RETURN_BASE_ATLAS` and
`VIRTUAL_WAVE_DEMAND_SCHEMA`.

```text
ledger: valid (201 obligations)
statuses: imported=13, proved=141, open=47
target: MLC [open]
diagnostic transfer regressions: 56 passed
```

`VIRTUAL_RETURN_BRANCH_LANGUAGE`,
`VIRTUAL_WAVE_MARKED_CORRESPONDENCE`,
`VIRTUAL_WAVE_HORIZON_CERTIFICATE`, VAAPC-I, UPTCR, and MLC remain open.

The warning-free 59-page manuscript was extracted and rendered into 59 page
images and 10 contact sheets. All contact sheets were inspected, with
full-resolution checks of pages 28--29, 52, and 58--59. Extracted text and
page-level searches confirm the new propositions and both new
source-facing inputs, while the return language, marked correspondence,
horizon certificate, UPTCR, and MLC remain printed as open. Release
SHA-256:
`A7DED72B98097817EEFDCDAAF44BF05AAA7C527405CFEB5D21F4E7D5668E495F`.

## 2026-07-24 - Native principal-nest return atlas and virtual selector pass

The return-base question was split into its native analytic part and its
virtual scale-selection part. Lyubich's Part I source
(`math/9503215`, locked archive SHA-256
`F799BDC011BEE5F89A467F7C24AFB3C53D0AE556FE7822952A0DE8ADD141FF16`;
`nest.tex` SHA-256
`069C10711C36F5358134B418FDF6C5133A5AF16208D2B1C267EA7B4D3A5DF83A`)
was checked at the Markov-puzzle, principal-nest, return-map, and
boundary-avoidance proofs.

`NATIVE_PRINCIPAL_NEST_RETURN_ATLAS` is proved. For a returning native
level \(n\ge2\), \(B_n=\operatorname{int}V^{n-1}\) is nice, its first
return domains are actual pairwise disjoint open puzzle components compactly
contained in \(B_n\), and their iterates are proper and onto. The central
degree word is \((2,1,\ldots,1)\); all lateral words are univalent. Jordan
puzzle boundaries give actual prime-end extensions and an external-angle
phase without assuming local connectivity of the full Julia set.

`ISOTOPY_CLASS_RETURN_UNDERDETERMINATION` is also proved. For
\(f(z)=z^2-1\), radial affine scaling explicitly isotopes
\(D(-1,1/4)\) to \(D(-1,5/4)\) while fixing the seed \(-1\), but the
seed's return times are two and one. Thus KKL's native choice of \(U_I\)
only up to isotopy relative to the small Julia cycle cannot determine the
analytic return atlas.

The virtual source-facing gap is now the open
`VIRTUAL_SCALE_TO_PUZZLE_SELECTOR`: the checked satellite-copy chain does
not define the map from an intermediate virtual index to an embedded nice
puzzle/principal-nest base, nor carrier placement, retained orbit, access,
obstacle, demand, and enlargement data at that base. The native theorem is
a positive control, not a proof of `VIRTUAL_RETURN_BASE_ATLAS`.

The source audit also caught and corrected a pre-existing Lyubich DOI typo:
the verified DOI is `10.1007/BF02392694`.

```text
ledger: valid (205 obligations)
statuses: imported=14, proved=143, open=48
target: MLC [open]
diagnostic transfer regressions: 59 passed
```

The warning-free 61-page manuscript was extracted and rendered into 61
page images and 11 contact sheets. All contact sheets from the pre-final
layout were inspected; the final pages 29--31 and 61 were then inspected
at full resolution after compacting the bibliography from an otherwise
orphaned final page. Extracted text confirms the new native theorem and
the open virtual selector, while the return language, marked
correspondence, horizon certificate, VAAPC-I, UPTCR, and MLC remain open.
Release SHA-256:
`3515612B9F7EBF661E75687F7CB7D4AC6D2FA5A0127CCFB97809784312B47A49`.

## 2026-07-24 - First decoration-scale selector and multi-base obstruction

The immediate `VIRTUAL_SCALE_TO_PUZZLE_SELECTOR` pass source-locked:

- Kahn--Lyubich, *Decorations*, arXiv:math/0609046:
  archive SHA-256
  `DA8FCF924793267421F80BE3E17CD7EB2B72CD4F5B08E3F5A38E2161EC608234`;
  `kingdom.tex` SHA-256
  `5DC04FEFF6B6A1D73040FFD50519C35D62EFF03C1049686DA71D595758E38FA7`;
- Kahn--Lyubich, *Local connectivity of Julia sets for unicritical
  polynomials*, arXiv:math/0505194:
  archive SHA-256
  `03221A00D020656BA3470E7F4C985CF613C4F26B1C766BFA87BA7A6D1A7B0C7F`;
  `kingdom.tex` SHA-256
  `2DF0B51CB7DC8BB421AD72684F187D3502A7CA8599F10CDF9DAC9A7E844253BA`.

For a fixed non-principal decoration outside a directly attached satellite
copy \(M_{p/q}\), the least critical \(q\)-return escape \(n\) selects the
actual puzzle piece

\[
V_{\rm esc}=f^{-nq}(Z_\kappa^1)|_0=Y^{nq+1}.
\]

Thus the first direct-decoration selector field is proved:

\[
\nu_{\rm dec}(1)=nq+1.
\]

`FIRST_DECORATION_SCALE_ESCAPE_ATLAS` records its actual first-return
domains, integer iterates, component/parent/sheet itineraries, central
degree word \((2,1,\ldots,1)\), univalent lateral words, and native branch
prime-end markings.

The pass then disproved the one-critical-base completion.  At the terminal
primitive first-return branch \(f^P:A_0\to B\), first return gives

\[
K_i=f^i(K_0)\subset f^i(A_0)\subset\mathbb C\setminus B,
\qquad1\le i<P.
\]

The first excluded component is \(K_1\), with complete cycle itinerary and
degree word.  The actual replacement skeleton is the multi-base chain

\[
A_0\to A_1\to\cdots\to A_{P-1}\to B
\]

plus \(A_0\hookrightarrow B\).  The checked sources still provide no
continuum in \(J(f)\) joining the pairwise-disjoint \(K_i\), so the first
attachment access is recorded as
\(\chi_{\rm access}=\bot\), not zero.

Finally, `DECORATION_FAN_GROWTH` records that the raw separator has exactly
\(2^n\) vertices and pairwise-disjoint pullbacks.  The construction is
finite for fixed \(n\) but not uniformly bounded.  The Wave demand audit
must prove either that a uniformly bounded subset is proof-complete or
that the demanded subset has a future-faithful compression passing the
exact WAD transport and observability kernel tests.

No recursive selector for \(s\ge2\) was claimed: repeating the
direct-decoration construction through a disconnected intermediate
satellite object would assume the missing virtual renormalization.
`VIRTUAL_SCALE_TO_PUZZLE_SELECTOR`, VAAPC-I, UPTCR, and MLC remain open.

The release audit validates 209 obligations: 15 imported, 146 proved, and
48 open. All 62 adversarial regressions pass. The warning-free manuscript has
64 pages; extracted text confirms the three new proved statuses and the open
selector, UPTCR, and MLC statuses. All 11 contact sheets were inspected, with
full-resolution inspection of the UPTCR statement, its conditional MLC
implication, the new selector results, and final ledger/status pages. Release
SHA-256:
`D4B5BA57CFD634CF49548EAB78846C5C9117BC9A29AE5CDC8580D7B4A83C5A7F`.

## 2026-07-24 - Terminal Hubbard-tree anchor and recursive package gate

The attempted \(s=2\) selector lift first re-audited the exact order of
construction.  The previous pass had an actual terminal primitive cycle
but treated its connector as entirely missing.  KKL's native prime
primitive category supplies more:

- the complete cycle \(\mathcal K\) of small filled Julia sets;
- its compact forward-invariant Hubbard tree \(\mathcal T\);
- a finite vertex-edge tree and native ideal marking; and
- in the non-locally-connected case, the corresponding
  rational-lamination model and lift.

The source lock is KKL `waves-with-Misha.tex`, SHA-256
`AD4C774806D9902AA54FA31C56AD6146D8034946F19CC5E9CEC3C51A3F94FDD5`,
lines 476--490, 512--570, 602--650, and 1254--1274.

`terminal_hubbard_anchor.md` proves the finite-tree consequences.  A finite
marked vertex package \(S\) has a unique convex subtree.  Every tree map
satisfies

\[
[\Phi(S)]\subset\Phi([S]),
\]

with equality when it is injective on the selected subtree.  Enlarging
\(S\) adds a forest with one old-tree gate per component.  For the complete
terminal cycle the hull is \(\mathcal T\); the first edge on the unique path
from \(K_1\) to \(K_0\) selects a native ideal attachment side.  This
promotes `NATIVE_HUBBARD_SUBTREE_FUNCTORIALITY` and
`TERMINAL_CYCLE_HUBBARD_ANCHOR`.

The adversarial audit retained the category boundary.  Connectedness does
not prove fullness.  A native ideal side is not yet a protected analytic
prime end for a partial Dudko carrier.  A folded tree branch may have
nonzero hull excess, and a one-gate enlargement may still enter a protected
collar.

The first recursive obstruction is now the missing map from a virtual copy
index to a typed terminal-tree package.  It must select actual Cantor
components, retained critical returns, protected sides, obstacles,
localization data, and frozen proof-use demands.  This is the new open
`VIRTUAL_VERTEX_PACKAGE_SELECTOR`.  The public Dudko and KKL sources do not
define it; a fresh primary-source search found no public DKL virtual
renormalization proof to import.

The machine ledger now validates 213 obligations: 16 imported, 148 proved,
and 49 open.  All 67 diagnostic regressions pass.  The recursive selector,
VAAPC-I, UPTCR, and MLC remain open.

The release manuscript was rebuilt after the ledger update and contains 66
pages.  Its LaTeX log has zero LaTeX, package, box, citation, and undefined
reference warnings.  Extracted text confirms the counts
\(213=16+148+49\), the proved native-tree statuses, and the open statuses of
`VIRTUAL_VERTEX_PACKAGE_SELECTOR`,
`VIRTUAL_SCALE_TO_PUZZLE_SELECTOR`,
`UNIVERSAL_PROTECTED_TOWER_CLOSURE`, and `MLC`.  All 11 contact sheets were
inspected, with full-resolution checks of the title disclaimer, the new
theorems and category warning on pages 33--35, their machine-ledger records,
and the final UPTCR/MLC status pages.  Release SHA-256:
`D6B98DD5BC7C276526052279E8E0F336CFBCF05786149169DFBFB5589EDB3816`.

## 2026-07-24 - Scale-2 Cantor-package type audit

The next \(s=2\) construction attempt stopped at an earlier field than the
terminal-tree selector.  Dudko's public description starts from
“Cantor small Julia sets,” while KKL's native terminal Hubbard tree starts
from one finite primitive cycle.  The checked sources do not construct the
scale-\(2\) address space, the embedded component map
\(\omega\mapsto K_{2,\omega}\), or its analytic branch action.  Therefore
no source-checkable component, itinerary, sheet, access, or localization
can yet be named at this scale.

`virtual_cantor_package_interface.md` records the exact type failure

\[
\mathfrak X^{\rm type}_2
=
(2,\mathcal M^{(0)},\mathcal M^{(1)},\mathcal M^{(2)},
  \mathscr K_2,\Omega_2,\mathcal R_2,\rho_2,\chi_{\rm type}=1),
\]

with the component-level collision fields equal to \(\bot\), not zero.
This is an obstruction to the previous construction order, not a
counterexample to unpublished virtual renormalization.

Two elementary interface theorems were proved:

1. an infinite distinct component family cannot inject into a finite
   terminal vertex set; and
2. a finite quotient supports a joint observable exactly when that
   observable is constant on every quotient fiber.

The corrected invariant separates the full geometric package from the
finite proof trace:

\[
\mathfrak V_s
=
(\mathfrak C_s,H_s,\mathscr A_s,\mathfrak F_{s,\mathscr D}).
\]

The corrected open order is
`VIRTUAL_CANTOR_PACKAGE_REALIZATION`, then
`VIRTUAL_PROOF_USE_TRACE_SELECTOR`, then the compatibility gate
`VIRTUAL_VERTEX_PACKAGE_SELECTOR`.  No downstream obligation is promoted.
Two adversarial regressions check finite-label pigeonholing and a
future-observable collision inside a coarse binary quotient.
## 2026-07-24 — Cantor-package type audit and manuscript release

The scale-\(2\) virtual-selector pass identified a construction-order obstruction:
the finite terminal Hubbard-tree package supplied by the currently source-locked
KKL material cannot, without an additional realization theorem, be identified
with Dudko's full Cantor family of virtual small Julia components.  The exact
failure certificate and the replacement interface are recorded in
`virtual_cantor_package_interface.md`.  Two elementary interface statements were
proved and entered in the machine ledger:
`FINITE_EXACT_CANTOR_ENCODING_OBSTRUCTION` and
`FINITE_QUOTIENT_OBSERVABILITY_CRITERION`.  The newly isolated analytic gates
`VIRTUAL_CANTOR_PACKAGE_REALIZATION` and
`VIRTUAL_PROOF_USE_TRACE_SELECTOR` remain open, as do
`VIRTUAL_VERTEX_PACKAGE_SELECTOR`, VAAPC-I, UPTCR, and MLC.

Final verification for this release:

- proof-ledger audit: 217 obligations, 16 imported, 150 proved, 51 open;
- adversarial regression suite: 69 tests passed;
- LaTeX manuscript: 67 pages, with no LaTeX/package warnings, no overfull or
  underfull boxes, and no undefined references or citations;
- extracted-text audit confirmed the new theorem identifiers and the open
  classifications of UPTCR and MLC;
- all 12 rendered contact sheets were inspected, together with full-resolution
  inspection of pages 1, 34, 35, 36, 60, and 67;
- released PDF SHA-256:
  `50D9EA26079C69447F564086C284C8B615965C78FEA169D09344C3028A373B97`.

## 2026-07-24 — Direct-decoration pullback compactification

### Question

Can the first source-defined analytic data be extended beyond the finite
terminal-tree proxy to an actual compact family of continua, and where does the
scale-\(2\) construction first become undefined?

### Construction

Kahn--Lyubich's decoration source supplies the separator
\(P=Y^{(n-1)q+1}\), the actual iterate \(g=f^q\), and two actual univalent
pullbacks \(Q_0,Q_1\subset P\).  Their inverse branches
\(\phi_0,\phi_1\) were composed before assigning any symbolic record.

For finite binary words \(w\), the construction sets

\[
K_w=\phi_w(K_0).
\]

For infinite words \(\omega\), it sets

\[
E_\omega=\bigcap_{m\ge1}Q_{\omega|m}.
\]

The terminated finite words together with binary ends form a compact address
space.  Under the explicit hypothesis \(K(f)=J(f)\), all fibers lie in the
Julia set.  The planar union is compact and its connected components are
exactly the finite pullbacks and end fibers.  The actual \(f^q\)-action deletes
the first symbol.

### Cross-examination and correction

The first proof draft used one word map for both geometry and dynamics.  This
was incorrect.  Geometric nesting removes the last symbol,

\[
\operatorname{gpar}(wa)=w,
\]

while the analytic branch action removes the first,

\[
\sigma(aw)=w.
\]

The proof and ledger were corrected before promotion.  Regressions now force
these operations to differ on a length-three word.

The construction proves upper semicontinuity, not Hausdorff continuity, and
does not call the end fibers small Julia sets.  Root-enlargement naturality is
proved only while the root stays in
\(P\setminus(Q_0\cup Q_1)\).  Outside that gap, an actual intersection in the
collision ledger is required; a gap breach alone is not called a collision.

### Status

The following are proved:

```text
DIRECT_DECORATION_PULLBACK_COMPACTIFICATION
PULLBACK_GAP_ENLARGEMENT_NATURALITY
```

The first unresolved scale-\(2\) datum is now the map transferring the second
satellite marking to actual bases and iterates on the finite cylinders and end
fibers:

```text
VIRTUAL_DISCONNECTED_MARKING_TRANSFER  open
```

Thus `VIRTUAL_CANTOR_PACKAGE_REALIZATION`, VAAPC-I, UPTCR, and MLC remain open.
The diagnostic suite has three new tests for word orientation, end convergence,
and root-collision bookkeeping.

### Release verification

- proof-ledger audit: 220 obligations, 16 imported, 152 proved, 52 open;
- adversarial regression suite: all 72 tests passed;
- LaTeX manuscript: 70 pages, with no LaTeX/package warnings, overfull or
  underfull boxes, or undefined references/citations;
- extracted text contains both new proved identifiers, the new open marking
  gate, the correct ledger counts, and the unconditional-MLC disclaimer;
- all 12 contact sheets were inspected; pages 35, 36, and 61 were additionally
  inspected at full resolution;
- released PDF SHA-256:
  `AED78021088824B54E3AFAF4625D6C51E8A15000992A05ABCC5DCA044F219A11`.

## 2026-07-24 — External referee issue-resolution pass

### Question

Which objections in the supplied referee report identify real defects in
the present source, which refer to stale or lossy extracted text, and what
is the strongest theorem that can be promoted after repairing them?

### Verified repairs

The attachment trace and orbit-hull definitions in the current source
already used closure, but their ambient and logical roles were hardened.
The remaining substantive objections were confirmed and repaired:

- the KKL carrier equality is now imported only on its proved central
  interval;
- the complement-pullback proof now classifies the punctured-disk cover
  before deducing connectedness and fullness;
- the decoration package uses closed sibling disjointness and boundary
  homeomorphisms;
- the pre-root shift is partial, with a separate root transition;
- safe-gap enlargement is explicitly only a topological finite-fiber
  theorem;
- connector and routing proofs now expose their crosscut, cyclic-order,
  and one-ended-slit lemmas;
- simultaneous pullback uses an open connected neighborhood;
- the horizon graph uses an upstream prefix-local selector and a
  downstream final selector;
- unprotected-atom exposure is an independent VAAPC input;
- attachment support depends on an explicit two-route resolution
  disjunction;
- the BLOT title is corrected to *Maps with no a priori bounds*.

### New proved theorem and residual gate

For equal-depth actual cylinder homeomorphisms, an already selected target
cylinder, and actual target containment, commutation gives

\[
 f^r|_{A_w}=h_v^{-1}\circ F\circ h_w.
\]

Surjectivity yields exact image equality, and homeomorphic conjugacy
preserves proper and local degree.  This proves
`FINITE_CYLINDER_COMMUTING_ITERATE_LIFT`.

The formula does not choose \(v\).  The new exact first gate is
`VIRTUAL_CYLINDER_TARGET_ADDRESS_SELECTOR`, requiring component-level
existence and uniqueness, prefix and partial-shift compatibility, a
separate root rule, marked compatibility, and final-root enlargement
naturality.  Its failure record names the first actual image component
meeting two targets or escaping the authorized target family.

### Status

The formal issue resolution is recorded in
`referee_issue_resolution_20260724.md`.  The ledger has 225 obligations:
16 imported, 153 proved, and 56 open.  `VIRTUAL_DISCONNECTED_MARKING_TRANSFER`,
VAAPC-I, UPTCR, and MLC remain open.  No regression result is used as an
analytic proof.

### Release verification

- proof-ledger audit: valid and acyclic, 225 obligations;
- adversarial regression suite: all 74 tests passed;
- LaTeX manuscript: 73 pages and no warning, box, citation, reference, or
  BibTeX diagnostic;
- extracted text confirms the corrected source title, statuses, counts,
  proved finite-cylinder theorem, open target selector, and unconditional
  proof disclaimer;
- all 13 contact sheets were inspected, covering every page; pages 1, 17,
  29, 38, 64, 72, and 73 were inspected at full resolution;
- build and released artifacts have identical SHA-256:
  `BE6FA8737D106313FDB949BC357301DB750BB065B846F3607BDD8813579D7EA2`.

## 2026-07-24 — Stone follower, cell packets, and target uniqueness

### External input and audit

The second external research report, SHA-256
`AC108271E833A74B1B4287703E64DC9E889BE4B722227BB53E03018C490527EC`,
was checked theorem by theorem.  The complete assessment is
`external_research_input_assessment_20260724b.md`.

### Narrow proved results

Three source-independent statements survive the audit.

1. `COUNTABLE_FOLLOWER_STONE_COMPACTIFICATION`: a fixed countable exact
   symbolic follower with countably many partial deterministic transitions
   and countably many Boolean observables has a compact metrizable
   zero-dimensional Stone compactification with clopen guards and
   continuous transition extensions.
2. `CELLWISE_PACKET_PORT_CERTIFICATE`: pairwise-disjoint closed Jordan
   cell envelopes, complete connected packet seeds, and one actual
   unprotected cell-exit arc per original atom imply disjoint localized
   fullifications, simultaneous ports, a common free component, and a
   protected connector.
3. `FIXED_BASE_CONNECTED_IMAGE_TARGET_UNIQUENESS`: after one target base is
   fixed, a connected image contained in a finite union of pairwise
   disjoint connected compact cylinders lies in one unique cylinder.

### Preserved analytic boundary

None of these statements constructs its virtual-dynamical hypotheses.
The Stone theorem does not supply compact hull geometry or its continuous
coupling.  The cell theorem does not construct dynamically natural cells
or unprotected accesses.  Fixed-base uniqueness does not choose the target
base or prove image containment.

The exact new open subgate is
`VIRTUAL_REACHED_CYLINDER_COMPONENT_EXHAUSTION`.  The selector must first
type or choose the target base, then prove actual reached-component
containment, and only then use fixed-base uniqueness.  Localized and
unrestricted preimage components are identified only through the new
closed-Jordan-disk component lemma.

`H3_SYMBOLIC_SIDE_COMPACTNESS`, VAAPC-I, UPTCR, and MLC remain open.

### Release verification

- proof-ledger audit: valid and acyclic, 229 obligations;
- adversarial regression suite: all 74 tests passed;
- LaTeX manuscript: 75 pages and no LaTeX, package, box, citation,
  reference, or BibTeX diagnostic;
- extracted text confirms the open MLC disclaimer, the 229/16/156/57
  obligation counts, the three narrow proved results, and the open reached-
  component exhaustion gate;
- all 13 contact sheets were inspected, covering every page; pages 16, 26,
  39, 40, and 65 were inspected at full resolution;
- the verified build SHA-256 is
  `BC686EB86F04D2E7809741EFEDC5230D3FEC92BA0C5B6F71C7997858A1D6DC88`.

## 2026-07-24 — Future-observable and direct-decoration research push

### Co-agent packet and corrections

The packet headed by `mlc_research_push_1.md`, SHA-256
`A85A9FF97A4FA6A356149F97DD10A5D5FB631F5A671760238919E58A2E48D433`,
was audited against the current ledger and source-locked direct-decoration
hypotheses. The complete decision record is
`research_push_1_assessment_and_integration.md`.

The future-observable compactification is a genuine strengthening of the
earlier Boolean Stone theorem. It records arbitrary compact-metrizable
observables after every finite continuation, makes exact word domains
clopen, extends partial transitions by coordinate shifts, and preserves
finite transition identities. This proves the compact-topology branch of
`H3_SYMBOLIC_SIDE_COMPACTNESS` and the compact-end-topology interface in
`VIRTUAL_PROOF_USE_TRACE_SELECTOR`. It does not prove an admissible
nondegenerate analytic limit, finite response dimension, or pumping.

The direct-decoration package now has proved full finite and end fibers,
global nonseparation, an equivariant gap-cell atlas, finite packet
replacement, protected exposure away from a proper total impression, and
a finite protected carrier against the complete rooted-end background.
These statements are confined to the already realized first
direct-decoration scale.

`INTERIOR_PULLBACK_COMPONENT_FORCING` proves that target-interior
containment forces one open pullback component. The co-agent proposal to
delete the target-selector gate was rejected: target-base selection,
component authorization, marked metadata, cross-base ownership, and
enlargement stability remain open.

### Status and verification

- authoritative ledger: 239 obligations, 16 imported, 168 proved, 55 open;
- `H3_COERCIVITY`, `VIRTUAL_REACHED_CYLINDER_COMPONENT_EXHAUSTION`,
  `VIRTUAL_CYLINDER_TARGET_ADDRESS_SELECTOR`, VAAPC-I, UPTCR, and MLC remain
  open;
- proof-ledger audit: valid and acyclic;
- diagnostic regression suite: all 77 tests passed;
- LaTeX manuscript: 80 pages, with no LaTeX, package, box, citation,
  reference, or BibTeX warning;
- extracted text confirms the 239/16/168/55 counts, proved symbolic-side
  topology, open analytic coercivity, and both open component gates;
- all 14 contact sheets were inspected; pages 16, 17, 40--43, 69--71,
  78, and 79 were inspected at higher resolution;
- verified build SHA-256:
  `C14A76BDC8BD644B8B90CD48C79732C5345BB40C7A14ED0D312DD9360C274045`.

## 2026-07-24 - Reproducible fractal illustration release

### Graphics construction

Four print-resolution plates were generated by direct iteration of
\(f_c(z)=z^2+c\):

1. a Mandelbrot parameter-plane overview with six marked parameters;
2. three independently rendered windows around
   \(c=-0.743643887037151+0.131825904205330i\);
3. a common-window Julia atlas for the Basilica, Douady rabbit center,
   parabolic cusp, golden-mean Siegel parameter, Feigenbaum
   approximation, and \(c=i\);
4. a golden-mean Siegel portrait carrying the first 5000 computed critical
   iterates and the analytically specified neutral fixed point.

The generator, image files, and exact render metadata are stored in
`figures/`. The rabbit center was checked by the residual
\(\lvert f_c^3(0)\rvert=2.64\times10^{-16}\); the golden-mean parameter was
checked by exact fixed-point and multiplier residuals at machine precision;
and the orbit of \(c=i\) was checked to return to its second point after two
additional iterates. These checks validate annotations only. No rendering
or numerical residual promotes a proof obligation.

The plates were integrated into the manuscript with an explicit warning
that finite escape-time coloring does not prove boundary membership, local
connectivity, renormalization control, coercivity, rigidity, UPTCR, or MLC.

### Release verification

- proof-ledger audit: valid and acyclic, 239 obligations;
- statuses: 16 imported, 168 proved, and 55 open;
- adversarial regression suite: all 77 tests passed;
- LaTeX manuscript: 84 pages and zero LaTeX, package, box, citation,
  reference, or BibTeX warnings;
- extracted text confirms the 239/16/168/55 counts, the illustration-only
  warning, open `H3_COERCIVITY`, open
  `UNIVERSAL_PROTECTED_TOWER_CLOSURE`, and open MLC;
- all 14 contact sheets were inspected, covering every page; the four
  fractal pages were additionally inspected at full resolution;
- verified build SHA-256:
  `B60D8DC7BA328BEC6217F0C87F0942E9A2E0E185C244B0C4529713D9126A0A33`.

## 2026-07-24 - Research Push II critical-chronology integration

### Input quarantine and reproduction

The complete Push II bundle and accompanying report were hashed and read in
full.  The supplied seven-page PDF was extracted, rendered, and inspected
page by page.  The chronology script was compiled and run on its example;
it reproduces the integer recurrence report but does not test analytic
geometry.  The complete inventory is
`research_push_2_assessment_and_integration.md`.

Three independent adversarial audits examined:

1. the finite-word and source-interface claims;
2. the critical-spine telescope and end claims; and
3. the proposed machine-ledger patch.

All three rejected the proposed promotions of `MAPPING_TELESCOPE` and
`FINITE_HORIZON_ASSEMBLY`.  The packet assumes, rather than constructs, the
scale-two root portrait and its protected marking.

### Proved narrow results

The integrated proof
`critical_chronology_and_retimed_telescope.md` establishes fourteen new
local or compiler-level obligations:

- `CRITICAL_CUT_POINTWISE_CONSERVATION`;
- `PROPER_COMMUTING_SQUARE_DEGREE_LAW`;
- `LOCAL_OFF_CRITICAL_CYLINDER_SQUARE`;
- `RETIMED_FINITE_CYLINDER_PAIR`;
- `CRITICALITY_LOCATION_SWAP_NO_GO`;
- `CRITICAL_TIME_SHEAR_NO_GO`;
- `STAGEWISE_CRITICAL_WORD_LADDER`;
- `QUADRATIC_JORDAN_BASE_CHANGE_DICHOTOMY`;
- `PLANAR_CRITICAL_SPINE_TELESCOPE_COMPILER`;
- `FINITE_PLANAR_TELESCOPE_IDENTITY`;
- `PLANAR_END_COLLAPSE_NO_GO`;
- `NORMALIZED_RETIMED_GERM_CONSTANCY`;
- `END_BLOWUP_PROJECTION_NO_GO`; and
- `FIXED_ITERATE_END_FIBER_EXTENSION`.

The retimed pair is explicitly conditional on an independently realized
root branch.  The telescope compiler is planar and requires closure
embeddings onto relatively compact Jordan subdisks.  The end theorem is a
collapse/no-go statement, not an end construction.

### Newly exposed open residuals

The integration adds:

- `VIRTUAL_FINITE_WORD_ROOT_PORTRAIT_AUTHORIZATION`;
- `DIRECT_DECORATION_END_PRIME_END_COFINALITY`; and
- `VIRTUAL_END_BLOWUP_REALIZATION`.

The first records safe-gap source identification, proof-complete marking,
simultaneous component ownership, and final-root stability.  The second
records the missing multisector angular-lift and fundamental-chain proof.
The third records the actual analytic nontrivial-fiber/rescaled end
attachment.  `VIRTUAL_DISCONNECTED_MARKING_TRANSFER`, VAAPC-I, UPTCR, and
MLC remain open.

### Adversarial corrections

The audit added exact counterexamples for:

- boundary identification of an interior-univalent Jordan-disk branch;
- critical-time shear with correct endpoint degrees;
- invalid arbitrary prime-end markings;
- unsafe enlargements inside \(P\);
- non-Jordan postcritical base changes;
- misuse of a conformal embedding as a target-circle map; and
- Boolean “retention” flags that do not encode geometry.

It also corrected the documented SHA-256 of the locked
arXiv:math/0505194 `kingdom.tex` to
`2DF0B51CB7DC8BB421AD72684F187D3502A7CA8599F10CDF9DAC9A7E844253BA`.

### Final release verification

- proof ledger: valid and acyclic, 256 obligations;
- statuses: 16 imported, 182 proved, 58 open;
- diagnostic regressions: all 86 passed;
- MLC, UPTCR, and VAAPC-I: open;
- LaTeX manuscript: 91 pages and zero LaTeX, package, box, citation,
  reference, or BibTeX warnings;
- extracted text confirms the 256/16/182/58 counts, the Research Push II
  status boundary, and the open MLC disclaimer;
- all 16 contact sheets were inspected, covering every page; after the
  equation-reference correction, rendered-page hash comparison showed that
  only pages 50--53 changed, and each changed page was reinspected at full
  resolution;
- verified build and release SHA-256:
  `198BBD3A029D9A8F156A95E36C1F8E35EF1A1E26C4501C1D329C47D37A42652D`.

## 2026-07-24 - Research Push II second adversarial release audit

### Defects found and repaired

A fresh audit did not merely repeat the first release checks.  Two
independent mathematical/ledger reviews and a separate source/PDF review
found the following defects:

1. `FIXED_ITERATE_END_FIBER_EXTENSION` was false without a separation
   hypothesis.  In the cofinite topology on \(\mathbb N\), the compact
   tails \(C_n=\{n,n+1,\ldots\}\) have empty intersection, while a constant
   map is surjective at every finite level.  The theorem now requires
   Hausdorff ambient spaces, exactly as its planar application does.
2. The quadratic Jordan base-change proof had not excluded multiple
   boundary components.  Riemann--Hurwitz now gives
   \(\chi(C)=2\chi(E)-1=1\), and planarity forces one boundary component.
3. The telescope compiler had conflated strict exterior omission with
   critical-value contact on the target boundary.  The latter is now a
   separate stopped boundary-critical collision.
4. The normalized retimed chart had an incorrect codomain.  It is now
   \(h_w|_{U_w}:U_w\to A\).
5. Closed puzzle pieces and open Jordan domains are now typed separately;
   the telescope identity is restricted to its exact domain
   \(I_m(T_m)\); the \(z^2-1\) shear model has an explicit
   \(0<\rho<1/2\) injectivity check; and the projection no-go proof now
   supplies the missing local noninjectivity argument.
6. The root-authorization node now depends explicitly on
   `VIRTUAL_WAVE_DEMAND_SCHEMA`.
7. The local off-critical square, criticality-location swap, and
   fixed-iterate nested-fiber theorem now have formal proofs in the main
   LaTeX body, not only evidence links in the generated appendix.
8. The planar compiler was retitled “critical-spine,” because it proves no
   protected marking, and every release roadmap now puts
   `VIRTUAL_REACHED_CYLINDER_COMPONENT_EXHAUSTION` before its dependent
   `VIRTUAL_CYLINDER_TARGET_ADDRESS_SELECTOR`.

The finite regression tests were also strengthened where possible, but
remain diagnostic checks rather than analytic proof evidence.  The complete
counterexample and repair ledger is in `adversarial_audit.md`, entries
A246--A258.

### Source and status boundary

The official Dudko preprint still presents Interpolation Problem 4.4 and
the connected virtual-Julia-set paragraph as a strategy to be developed,
not as a carrier construction theorem.  The official KKL preprint treats
virtual renormalization as future perspective and lists the DKL work as in
preparation.  No unavailable result was imported to fill the virtual
source-facing gates.

No global status changed in this audit.  MLC, UPTCR, VAAPC-I,
`MAPPING_TELESCOPE`, `FINITE_HORIZON_ASSEMBLY`, root authorization,
prime-end cofinality, and analytic end realization remain open.

### Final verification

- proof ledger: valid and acyclic, 256 obligations;
- statuses: 16 imported, 182 proved, 58 open;
- diagnostic regressions: all 88 passed;
- LaTeX manuscript: 93 pages with no LaTeX, package, box, citation,
  reference, or BibTeX warning;
- extracted text confirms all fourteen narrow Push II results, the
  Hausdorff and boundary-critical repairs, the added Wave-demand
  dependency, the 256/16/182/58 counts, and the open global targets;
- all 16 contact sheets were inspected, covering every page; repaired
  pages 53--55 and generated-ledger page 84 were inspected at full
  resolution;
- all 93 page rasters have the expected dimensions, are nonblank, and
  contain no ink in the outer 20-pixel edge band;
- verified build and release SHA-256:
`07935F6BA208F81CB035AEC593B318CA1FB5B5F95B224F49980FF39043E1E6F6`.

## 2026-07-25/26 - Actual MLC frontier continuation

The active objective remains the global Mandelbrot local-connectivity theorem;
the MLC ledger is intentionally still open.  The separate closure-attempt PDF
was extended with a coverage-complement audit and a source-faithful
transitional bridge theorem.

- The finite satellite data (q_m=m+3, p_m=1) fail the imported
  Cheraghi--Shishikura QG_N test and Levin Theorems 1, 2, and 7.  The audit is
  deliberately only a data-level witness and makes no unproved claim that a
  limiting quadratic parameter is realized.
- The DL25 source boundary was typed as five gates: neutralization with actual
  domains, psi-bullet-ql admissibility, transitional-scale control, parameter
  and marking transfer, and infinite assembly.  A rational satellite root is
  parabolic, not Siegel, so matching its multiplier does not supply the neutral
  theorem hypotheses.
- New PDF artifact:
  `mlc_subresearch_corrections_proposal_actual_closure_attempt_20260725_v4.pdf`.
- Verification remains clean: ledger 256 obligations (182 proved, 16
  imported, 58 open); diagnostic transfer regressions pass; source validators
  pass; original manuscript PDFs were read only.

### Exact parabolic anchor (continuation)

The (1/3) satellite root was checked in exact arithmetic over
(\mathbb{Q}(\sqrt{-3})): (\lambda^3=1), (z_\alpha=\lambda/2),
(c=-1/8+(3/8)\sqrt{-3}), and the local third-iterate germ has zero
quadratic and cubic coefficients and nonzero quartic coefficient
((9+\sqrt{-3})/2). This repairs the bridge target from “neutralize the
rational satellite” to “construct a marked parabolic/cylinder (Lavaurs) pair
and then transfer it to sector/pseudo-Siegel control.”

- Certificate: `PARABOLIC_SATELLITE_ANCHOR_VALID`;
- machine script: `validate_parabolic_satellite_anchor.py`;
- PDF release: `mlc_subresearch_corrections_proposal_actual_closure_attempt_20260725_v5.pdf`.

This is an exact finite anchor, not a global MLC proof; uniform cylinder
bounds, Molecule hyperbolicity, virtual interpolation, and rigidity remain
open.

### Finite primitive-root family sweep (2026-07-26)

To test whether the corrected parabolic anchor was special to the 1/3
example, an exact cyclotomic computation was added.  For each primitive root
order q=2,...,16, the local germ g(w)=lambda*w+w^2 was iterated q times in
Q[x]/(Phi_q(x)) through degree q+1.  Every checked order has multiplier one,
exact cancellation of degrees 2 through q, and a nonzero degree-(q+1)
coefficient.  The q=3 coefficient reduces to x+5 and therefore reproduces
the previous (9+sqrt(-3))/2 value.

- Certificate: `PARABOLIC_ROOT_FAMILY_FINITE_SWEEP_VALID`;
- machine script: `validate_parabolic_root_family.py`;
- JSON output: `parabolic_root_family_20260726.json`;
- PDF release: `mlc_subresearch_corrections_proposal_actual_closure_attempt_20260725_v6.pdf`.

This closes only a finite exact local-family check.  It does not establish an
all-q theorem, uniform cylinder/Lavaurs estimates, Ecalle-phase transport,
virtual Molecule interpolation, or MLC.  The active analytic bridge remains
open.

### Source-backed no-bound obstruction (2026-07-25)

The primary paper *Maps with No a Priori Bounds* was checked against the
unbounded-satellite branch.  Its satellite PL-cycle estimate gives, for
relative period (s) and PL degree (d_*),

\[
(d_*-1)\operatorname{mod}(U\setminus K_*)
 < \frac{d_*(d_*-1)\pi}{\log(4(s+1))}.
\]

For quadratic degree (d_*=2), this is (2\pi/\log(4(s+1))), which tends to
zero as (s\to\infty).  This definitively rules out using a uniform positive
ql modulus as the missing closure argument for arbitrary unbounded satellite
towers.  It does not prove non-local-connectivity or disprove MLC; it forces
the proof target to tolerate degenerating annuli and retain marked
parabolic/cylinder data.

- Source: <https://publications.hse.ru/pubs/share/direct/1052158150.pdf>;
- certificate: `UNBOUNDED_SATELLITE_NO_BOUNDS_ESTIMATE_VALID`;
- machine script: `validate_unbounded_satellite_no_bounds.py`;
- PDF release: `mlc_subresearch_corrections_proposal_actual_closure_attempt_20260725_v7.pdf`.

The active global MLC objective remains open: the missing cylinder-to-parameter
rigidity and virtual-Molecule interpolation have not been constructed.

### Elephant Eyes source branch (2026-07-25)

The 2026 Kahn--Lyubich preprint *A priori bounds for some infinitely
renormalizable quadratics: IV. Elephant Eyes* was downloaded, source-locked,
and audited.  Its E1--E3 class assumes an even quadratic-like map with
connected Julia set and repelling fixed points, rotation (1/q), and period
(p=q+b) with bounded (b) and unbounded (q).  The source proves a priori
bounds using a uniform thin--thick decomposition and an amplification theorem.

This closes the a-priori-bound obligation for that specifically typed
unbounded branch.  Section 8 states the corresponding MLC conclusion, but it
explicitly invokes little Mandelbrot copies on Ecalle--Voronin cylinders and
cites the DLP project as “in preparation”; therefore the MLC consequence is
kept dependency-audited rather than promoted as an independent completed
import.

- Source: <https://arxiv.org/html/2601.21905>;
- source SHA-256: `5EB36430A51A3FB6A1C04DB15713AEBC86068118450893BA2042021E4A8DB725`;
- certificate: `ELEPHANT_EYE_SOURCE_BRANCH_VALID`;
- machine script: `validate_elephant_eye_branch.py`;
- PDF release: `mlc_subresearch_corrections_proposal_actual_closure_attempt_20260725_v8.pdf`.

The arbitrary unbounded-satellite complement, the published cylinder-copy
input, and virtual-Molecule interpolation remain open.

### Neutral-attractor rigidity correction (2026-07-25)

Willie Rush Lim's public note *The combinatorics of sector renormalization*
records a current neutral-renormalization result attributed to Dudko--Lim--
Lyubich [DLL26].  The note states that neutral quadratic sector
renormalizations can be chosen precompact and capture the critical orbit well;
its infinity compactification retains simple parabolic bifurcations, the full
Lavaurs--Epstein tower, top/bottom Lavaurs data, parabolic blow-ups, and cyclic
critical-orbit order.  Theorem 1.1 states combinatorial rigidity of the full
neutral renormalization attractor and shift conjugacy modulo conformal
conjugacy, with uniform complex bounds for neutral cascades and affine
conjugacy of combinatorially equivalent cascades in the proof summary.

This repairs the neutral-attractor rigidity interface in the gap map, subject
to the status actually reported by the source: [DLL26] is listed as a 2026
manuscript.  It does not produce a satellite-to-neutral comparison for
arbitrary unbounded quadratic-like returns, virtual-Molecule interpolation,
global parameter rigidity, or a global MLC theorem.

- Source: <https://arxiv.org/html/2607.11408v1>;
- source PDF SHA-256: `68ACBB258E456A4A6F2EDF43E2E26030401251036E92662D507059DD08BEC91D`;
- certificate: `NEUTRAL_ATTRACTOR_RIGIDITY_SOURCE_VALID`;
- machine script: `validate_neutral_attractor_rigidity.py`;
- independent scope cross-check: <https://www.math.stonybrook.edu/cal/agenda.php?LocationID=10>;
- PDF release: `mlc_subresearch_corrections_proposal_actual_closure_attempt_20260725_v11.pdf`.

The active global MLC objective remains open.  Original manuscript and main
PDF artifacts remain untouched.

### Current global-status audit (2026-07-25)

The final web cross-check searched for a complete global MLC theorem.  The
checked sources do not support importing one.  Dudko's survey still states MLC
as a conjecture and identifies the remaining unbounded-satellite cases and
positive/zero-entropy interpolation as the two global problems.  Kahn--
Kapiamba--Lyubich's June 2026 result proves MLC for a class of parabolically
bounded primitive infinitely renormalizable parameters, not every quadratic
parameter.  The neutral-attractor result is similarly branch-specific and
does not provide the arbitrary satellite-to-neutral comparison or virtual
Molecule parameter interpolation.

- Survey: <https://arxiv.org/html/2512.24171>;
- primitive-class result: <https://arxiv.org/abs/2606.27272>;
- neutral branch: <https://arxiv.org/html/2607.11408v1>;
- KKL taxonomy audit: `kkll_global_taxonomy_20260725.json`;
- PDF release: `mlc_subresearch_corrections_proposal_actual_closure_attempt_20260725_v12.pdf`.

### All-q resonance cancellation lemma (2026-07-25)

The local quadratic satellite anchor admits a rigorous all-q cancellation
upgrade.  If `g(w) = lambda*w + w^2` with lambda a primitive q-th root and
`F = g^q`, then `F` commutes with `g`.  If the first nonzero term of
`F(w)-w` has degree `m`, coefficient comparison in `F o g = g o F` gives
`lambda^(m-1)=1`; primitivity forces `q | (m-1)`.  Since `g^q` is a polynomial
of degree `2^q`, it is not the identity, so the first nonzero term exists.
Therefore all terms through degree q cancel for every q.

This closes only the all-q resonance-cancellation half.  It does not prove
degree-(q+1) nondegeneracy for every q, uniform cylinder/Lavaurs estimates,
or the unbounded-satellite and virtual-Molecule parameter bridge.

- proof note: `parabolic_commutation_lemma_20260725.md`;
- certificate: `PARABOLIC_COMMUTATION_RESONANCE_VALID`;
- machine script: `validate_parabolic_commutation_lemma.py`;
- cross-check range: q=2,...,32;
- PDF release: `mlc_subresearch_corrections_proposal_actual_closure_attempt_20260725_v13.pdf`;
- original artifacts remain untouched.

### KKL frontier taxonomy correction (2026-07-25)

The June 2026 Kahn--Kapiamba--Lyubich paper was downloaded and source-locked.
Its introduction gives the four-way family taxonomy: anti-molecule/bounded
satellite, near-parabolic, near-neutral, and virtually-satellite, indexed by
the eventual limb depth (l), continued-fraction height (h), and depth (d).
The paper's theorem is for parabolically bounded prime primitive families.
It says the neutral theory is believed to be promotable to all forms of
unbounded satellite renormalization, and lists virtual renormalization as in
preparation. Both are prospective boundaries, not global imports.

- Source: <https://arxiv.org/html/2606.27272>;
- source PDF SHA-256: `4C08805384B473DC0E55D76491C52C9FBE7C027E6DA301F2C365A170ED7D9140`;
- certificate: `KKL_GLOBAL_TAXONOMY_SOURCE_VALID`;
- machine script: `validate_kkll_global_taxonomy.py`;
- PDF release: `mlc_subresearch_corrections_proposal_actual_closure_attempt_20260725_v12.pdf`.

## 2026-07-25 — Research Push III end-rescaling and plumbing audit

The [Research Push III bundle](../mlc_research_push_3_bundle/) was source-locked for audit.  Its SHA-256 is
`D6A2B5074CF55AB7983AE0E835A4F38B5388DFB4043B3A57E254C9A6EED2DD62`;
every bundled checksum was reproduced.  The supplied seven-page PDF was
text-extracted, rendered, and inspected.  Its README incorrectly says six
pages, but the layout itself is clean.

The complete assessment is
`research_push_3_assessment_and_integration.md`.  Five narrow statements
survive:

1. `NORMALIZED_END_DIRECT_LIMIT`;
2. `DEPTH_GRADED_CYLINDER_MATERIALIZATION`;
3. `END_CHART_OBSERVABLE_INVARIANCE`;
4. `SERIAL_EXHAUSTION_RESISTANCE_BOUND`; and
5. `SCALAR_NECK_TRACE_MODE_NO_GO`.

The main proposed response theorem is not proved.  At a cut analytic
cross-section the trace is functional, not scalar.  On
\([0,L]\times S^1\), the constant-mode conductance is \(2\pi/L\), while
the energy of the trace \(\cos(k\theta)\) against zero is
\(\pi k\coth(kL)\).  The latter does not tend to zero.  The exact replacement
gate is `END_PLUMBING_TRACE_RESPONSE_CONTROL`.

The supplied finite graph script was reproduced for 250 randomized trials.
It validates scalar Schur-complement algebra only and cannot see analytic
trace modes.  The supplied ledger patch was rejected because it names stale
nodes and treats open `FINITE_HORIZON_ASSEMBLY` as available.  The proposed
adaptive nodal response, finite-horizon inflation, strict transition
transfer, planar-free execution, and dependency deletion were not promoted.

Verification:

- proof ledger: valid and acyclic, 262 obligations;
- statuses: 16 imported, 187 proved, 59 open;
- transfer regressions: all passed, including the exact cylinder-mode,
  grading-conflict, and input-alignment diagnostics;
- LaTeX: no warnings, undefined references, box warnings, or citation
  warnings;
- extracted text confirms the 262/16/187/59 counts, the 2026-07-25 source
  lock, the trace-mode no-go theorem, and the open trace-response gate;
- final manuscript: 98 letter-size pages, all contact sheets inspected,
  with pages 57--61 inspected at full resolution; and
- final PDF SHA-256:
  `A144CB7E6D90825FEC1527E6035FE58FA7FA0B0A62361A70DDF40E715E311C15`.

VAAPC-I, UPTCR, and MLC remain open.

## 2026-07-25 — Research Push IV full-trace and collar audit

The [Research Push IV bundle](../mlc_research_push_4_bundle/) was source-locked for audit.  All eight source/destination hashes
match; the complete manifest is recorded in
`research_push_4_assessment_and_integration.md`.  The six-page supplied PDF
was rendered and visually inspected.

The 500-trial Fourier/Schur-complement audit was reproduced.  It correctly
tests finite truncations of the abstract rectangle response but contains no
model of dynamically changing angular footprints.

Eight proposed local operator statements survive:

1. `FULL_TRACE_RECTANGLE_DTN`;
2. `TRACE_RESPONSE_SEMIGROUP`;
3. `EQUIPOTENTIAL_COLLAPSE_CRITERION`;
4. `SHORTED_EQUIPOTENTIAL_NODAL_RESPONSE`;
5. `TRACE_RENORMALIZED_NECK_ESTIMATE`;
6. `END_TRACE_RESPONSE_COMPACTIFICATION`;
7. `HILBERT_TRACE_GLUE_CALCULUS`; and
8. `TRACE_STABLE_STRICT_TRANSITION_TRANSFER`.

The exact source-facing obstruction is new:
`PULLED_EQUIPOTENTIAL_SERIAL_RECTANGLE_NO_GO`.  Under
\(z\mapsto z^{2^q}\), inverse pullback divides angular width by \(2^q\).
Thus the full parent and child equipotential arcs cannot be opposite sides
of one ray-bounded rectangle.  The packet's
`BOTTCHER_TRACE_COLLAR_ATLAS` is not proved, and the claimed serial
semigroup cannot be applied to the physical nested end.

The replacement open node is
`DIRECT_DECORATION_TRACE_COLLAR_REALIZATION`.  It must retain the unequal
trace footprints, every additional side port, the actual cell response, and
protected enlargement data.  It must also prove enough accumulated
resistance for any asserted finite-depth strict margin; positive cell
resistance alone is insufficient.

The principal `END_PLUMBING_TRACE_RESPONSE_CONTROL` node remains open and
now depends explicitly on this geometric realization.  H2, MBTT, VAAPC-I,
UPTCR, and MLC remain open.

Verification:

- proof ledger: valid and acyclic, 272 obligations;
- statuses: 16 imported, 196 proved, 60 open;
- all 95 transfer/adversarial diagnostics passed;
- the 500-trial supplied Fourier/Schur audit reproduced to floating-point
  tolerance;
- LaTeX, reference, citation, and box-warning audit: zero warnings;
- extracted text confirms the 272/16/196/60 counts, the proved
  pulled-equipotential no-go, both open collar/plumbing nodes, and open MLC;
- final manuscript: 101 letter-size pages, all 17 contact sheets inspected,
  with full-resolution checks of pages 60--62, 91, and 101;
- build and synchronized output SHA-256:
  `3CDE615F3A4BEB626216A680D98D3F25BCF7488AF28182E595562D172F523181`.

### Trace-plumbing collar correction (2026-07-25)

The latest trace-plumbing push was independently audited. Its local
full-trace rectangle Dirichlet-to-Neumann formula, exact Hilbert-space
Schur-complement gluing, and finite Fourier/Schur stress test are valid under
the complete trace-compatible rectangle hypothesis. Its proposed promotion
to arbitrary dynamically pulled parent/child equipotential collars is not
valid.

Under the exact model pullback `z -> z^(2^q)`, an inverse branch changes a
parent angular footprint `Delta` to `Delta/(2^q)`. Full arcs with those two
widths cannot be opposite sides of one ray-bounded serial rectangle. The
research package therefore rejects `BOTTCHER_TRACE_COLLAR_ATLAS` as a proved
global node and keeps the exact failure certificate
`PULLED_EQUIPOTENTIAL_SERIAL_RECTANGLE_NO_GO`.

The corrected open target is
`DIRECT_DECORATION_TRACE_COLLAR_REALIZATION`: retain the unmatched boundary
pieces, all future-relevant trace ports, phase, and actual accumulated
resistance. The scalar constant-mode collapse is allowed only for an
explicitly shorted constant trace space. This correction is recorded only in
the separate subresearch artifact; the validation and PDF-build scripts do
not write the original documents.

- machine certificate: `PULLED_EQUIPOTENTIAL_SERIAL_RECTANGLE_NO_GO`;
- script: `validate_trace_collar_no_go.py`;
- cross-check: `audit_transfer_regressions.py` test
  `test_pulled_equipotential_arcs_do_not_form_serial_rectangle`;
- separate PDF release:
  `mlc_subresearch_corrections_proposal_actual_closure_attempt_20260725_v14.pdf`.

### Conditional trace-complete response theorem (2026-07-25)

The collar repair was formalized as a conditional theorem in
`direct_decoration_trace_response_conditional_20260725.md`.  It retains the
complete trace on every actual parent, child, and unmatched side port.  Under
five explicit certificates - universal port bound, uniform reference charts,
uniform quotient coercivity, phase-preserving future-closed trace maps, and
response-safe elimination with a lower-semicontinuous homogeneous gauge -
Lax--Milgram, Hilbert-space Schur complements, Loewner monotonicity, and
weak-operator compactness give the correct trace-complete interface.

This reduces the collar obligation to five source-facing hypotheses without
reviving the false serial-rectangle promotion.  The hypotheses are not yet
proved for every direct-decoration, virtual, or mixed tower, so END_PLUMBING,
MBTT, coercivity, rigidity, and MLC remain open.

- separate PDF release:
  `mlc_subresearch_corrections_proposal_actual_closure_attempt_20260725_v15.pdf`;
- original documents are not written.

## 2026-07-25: cumulative side-research library audit

The twenty-five side-research PDFs were hashed, text-extracted, and
deduplicated as one cumulative revision chain.  The custody manifest is
`external_inputs/side_research_library_20260725/manifest.json`; the
mathematical disposition is
`side_research_library_assessment_and_integration.md`.

An independent mathematical red-team found two fatal claims:

- the proposed conditional response used an unbounded-below bilinear
  infimum, quotiented away relative port voltages, and asserted a strictness
  stability that fails under arbitrary common energy;
- the proposed weak welding state used a graph-projection formula valid only
  for unitary maps, while bilateral shifts show that even corrected graph
  projections are not closed under weak-operator limits.

Both notes and validators were rewritten as rejection/no-go records.  The
finite quadratic-like lift was corrected so its filled Julia set is typed in
the source domain.  The BLOT audit now distinguishes
\(U_n\setminus K_n\) from the outer annulus \(V_n\setminus U_n\), and the
two-case target now records degenerate and non-precompact alternatives.

The retained proofs are:

- primitive-root parabolic nondegeneracy;
- fixed-modulus ambient-end no-go;
- serial-annulus singleton bridge;
- sectorwise dyadic Böttcher \(\dot H^{1/2}\) isometry;
- correct multi-port trace gauge and strictness no-go; and
- weak-operator welding-algebra no-go.

After integration, `audit_proof.py` validates 294 obligations: 23 imported,
208 proved, and 63 open.  MLC, UPTCR, VAAPC-I, MBTT, coercivity, and rigidity
remain open.

### Research Push V: physical contact and welding audit (2026-07-25)

The fifth co-agent bundle was copied to
`external_inputs/push_5_20260725` with all eight SHA-256 values matching.
Its six-page PDF was rendered and inspected, its 250-trial finite-network
calculation was reproduced, and the proposed ledger patch was checked
against the live schema and dependencies.

The defensible advance is local:

- a nested Jordan shell with exactly one common boundary arc splits into an
  active Jordan cell and an inactive attachment arc;
- two attachment arcs admit a corrected disjoint open-atom refinement after
  their genuine endpoints are removed;
- regular common trace interfaces compose by an exact fiber-product
  Dirichlet infimum;
- extended-valued infimum pushforwards are functorial;
- arbitrary continuous projection does not preserve closed quadratic forms;
  and
- fixed cap forms around a fixed-coordinate standard neck have the stated
  exponential plus \(R^{-1}\) compactification estimate.

Two exact obstructions defeat the physical gate promotions.

First, an alternating chain of four nested rectangles has a boundary arc
active for shells \(C_1,C_3\) but inactive for \(C_2\).  The side port
therefore reactivates two levels later and bypasses the middle shell.
Consecutive pair refinement does not prove physical serial exhaustion or
resistance addition.

Second, whole-tail uniformization introduces endpoint trace maps
\(J_w^\pm\).  The fixed physical response is

\[
 (J_w^-\oplus J_w^+)^*\mathcal N_{R_w}(J_w^-\oplus J_w^+),
\]

and no bounded/precompact welding cocycle has been proved.  Absorbing those
maps into the caps makes the caps depend on the word and depth.

The accepted assessment is
`research_push_5_assessment_and_integration.md`; the exact diagnostic is
`validate_push5_contact_welding_no_go.py`.  The authoritative ledger now
contains 281 obligations: 16 imported, 202 proved, and 63 open.
`DIRECT_DECORATION_TRACE_COLLAR_REALIZATION`,
`END_PLUMBING_TRACE_RESPONSE_CONTROL`, VAAPC-I, UPTCR, and MLC remain open.

### Global frontier source re-audit (2026-07-25)

The current KKL primary source was re-read at its theorem and future-perspective
sections.  Theorem A gives beau bounds for parabolically bounded families of
prime primitive types; Theorem B gives rigidity under bounded puzzle
Teichmuller diameter; Theorem C combines these for that parabolically bounded
family.  The same source explicitly classifies the remaining families as
general near-parabolic, near-neutral/unbounded-satellite, and
virtually-satellite regimes, and says that the latter theories require further
development.

The virtual occupancy audit therefore narrows the next valid target to a
static KKL Section-4 interface: an access-complete finite-tree carrier,
bounded marked intervals per limb, full-cycle width/WAD comparison,
restriction multiplicity, faithful flux/wave decomposition, and a checked
large-width amplification threshold.  It does not import the KKL tame or wave
propositions, whose proofs additionally need full-return Value dynamics,
fiber-product pullbacks, selected degree control, and itinerary-complete long
stopping horizons.

- source: `https://arxiv.org/html/2606.27272`;
- audit: `kkl_virtual_occupancy_source_audit.md`;
- separate PDF release:
  `mlc_subresearch_corrections_proposal_actual_closure_attempt_20260725_v17.pdf`;
- global MLC remains open and original documents are not written.

### Formal parabolic resonance recurrence (2026-07-25)

The local quadratic satellite anchor was pushed one step beyond the
all-order commutation cancellation.  For `g(w)=lambda*w+w^2` and a primitive
q-th root `lambda`, formal conjugacy through degree q gives the exact
recurrence

`b_n = S_n/(lambda^n-lambda)`,
`S_n = sum_{i=1}^{n-1} b_i*b_(n-i)`,
and
`A = S_(q+1)`,

with first resonant coefficient
`[w^(q+1)]g^q = q*lambda^(q-1)*A`.

`validate_parabolic_resonance_recurrence.py` evaluates this in the exact
cyclotomic field and independently expands the iterate.  The two values
agree, intermediate coefficients cancel, and the resonant coefficient is
nonzero for every q=2,...,16.  The new note is
`parabolic_resonance_recurrence_20260725.md` and the certificate is
`parabolic_resonance_recurrence_20260725.json`.

The finite algebraic certificate is supplemented by an all-q basin-count
argument.  For a primitive q-th multiplier, the q-th iterate has multiplicity
`m+1` with `m=kq`, and the immediate parabolic basins form `k` cycles.  Each
cycle contains a critical point.  The quadratic germ has one finite critical
point, while infinity lies in the separate superattracting basin at infinity,
so `k=1` and the first resonant coefficient is nonzero for every q.  The
recurrence is therefore a finite machine cross-check of an all-q local
theorem, not the theorem's sole evidence.

This closes the local nondegeneracy anchor but not the arbitrary
unbounded-satellite cylinder-to-parameter bridge, virtual-Molecule
interpolation, global rigidity, or MLC.

- recurrence certificate: `PARABOLIC_RESONANCE_RECURRENCE_FINITE_VALID`;
- separate PDF release:
  `mlc_subresearch_corrections_proposal_actual_closure_attempt_20260725_v16.pdf`;
- protected originals retain SHA-256
  `3CDE615F3A4BEB626216A680D98D3F25BCF7488AF28182E595562D172F523181`;
- original documents are not written.

## 2026-07-25: independent Push-V re-verification

The independent verification with source SHA-256
`D3D415FE17ED85977469A45BA8E241A5709E1AB51FEE00A8B3DD6661ADA33E0F`
was ingested as secondary corroboration.  It reproduces the source-package,
nonconsecutive-contact, closed-form-pushforward, welding, and numerical
conditioning objections.  It does not promote the physical collar or
end-plumbing response gates.

One Markdown typo was corrected: the fixed-coordinate cap error is the sum
of the exponentially decaying term and
\(2B^2/(\alpha_*^2R)\).  The LaTeX and ledger formulas were already
correct.

The Kahn--Lyubich source typing was sharpened.  With
\(g=f^q|_{Q_L\cup Q_R}\), the \(2^n\) pieces \(Q^v\) are the components of
\(\operatorname{dom}(g^n)\).  The defect is therefore an untyped switch
between binary one-step branches and length-\(n\) macrobranches, not an
absence of any relationship between the packages.

The new proved node `FINITE_TAME_CONTACT_OVERLAY_RESPONSE` gives the exact
finite \(H^1\) fiber-product theorem for an already realized finite
Lipschitz cell overlay.  It does not realize the dynamical overlay.
`DIRECT_DECORATION_ALL_DEPTH_CONTACT_CLOSURE` was strengthened to require
canonical contact atoms with complete incidence data, and
`DIRECT_DECORATION_TRACE_WELDING_COMPACTNESS` now depends explicitly on
that closure.

After integration, `audit_proof.py` validates 295 obligations: 23 imported,
209 proved, and 63 open.  MLC, UPTCR, VAAPC-I, the all-depth contact gate,
the welding gate, and end-plumbing response remain open.

## 2026-07-25: project-wide novelty and mathematical-value audit

A previous rapid assessment was withdrawn because it did not support a
project-wide novelty judgment.  The replacement audit read the substantive
proofs behind every plausible originality candidate, compared them with
primary sources, classified all 209 internally proved ledger nodes, and
computed their actual effect on the `MLC` dependency closure.

The classification is:

- 71 standard or classical results;
- 85 direct formal corollaries or compilers;
- 8 finite or source diagnostics;
- 41 counterexamples or no-go results;
- 3 candidate-original positive entries belonging to one first-scale
  direct-decoration construction; and
- 1 substantive result whose novelty remains unresolved.

The strongest candidate-original output is the literal three-vertex
counterexample to the positive-delay clone equation printed in Appendix C of
Kahn--Kapiamba--Lyubich v1 and the independently proved negative-delay
Schur/renewal repair
\[
H(t)=t^{-1}D(tI-Q)^{-1}C,\qquad
\rho(H(\lambda_n))=\lambda_n^n.
\]
The correction appears mathematically sound and was not found in a public
erratum, but publication priority requires author confirmation and independent
expert review.  It repairs a finite spectral bridge; it does not refute the
paper's main restricted MLC theorem or close a virtual-dynamics gate.

The direct-decoration rooted-end compactification, gap-cell atlas, and finite
protected carrier are a promising specialized construction under strong
source-locked hypotheses.  Their symbolic core is classical, their novelty is
unverified, and they stop before the scale-two marking and virtual return.

The dependency closure of `MLC` has 259 nodes: 15 imported, 185 proved, and
59 open including `MLC`.  H1, MBTT, H3, and H4 all remain open; all six direct
prerequisites of MBTT are open; no new MLC parameter class or published
virtual/unbounded-satellite problem is solved.

The full assessment is
`novelty_and_value_audit_20260725.md`.  The machine-readable 209-node sidecar
and its exact-ID validation are
`novelty_classification_20260725.json` and
`novelty_classification_20260725_validation.md`.  No ledger status was changed.

## 2026-07-25: Research Push VI separator and response-cocycle audit

The Push-VI bundle at
`research/mlc_research_push_6_bundle/push6` was preserved in place.  All
eleven entries agree with its SHA-256 manifest.  The complete mathematical,
source, computational, and ledger disposition is
`research_push_6_assessment_and_integration.md`.

The valid result is a narrow nested-separator theorem.  For one fixed
source-locked binary \(f^q\) address chain, write
\[
\Omega_j=\operatorname{int}D_0\setminus D_j,\qquad
S_{j+1}=\operatorname{int}D_j\setminus D_{j+1}.
\]
Then, for every \(k>j\),
\[
\overline{\Omega_j}\cap\overline{S_k}\subset\partial D_j,
\]
and
\[
\Omega_{j+1}
=
\Omega_j\sqcup
\bigl((\operatorname{int}D_0\cap\partial D_j)\setminus D_{j+1}\bigr)
\sqcup S_{j+1}.
\]
If one physical boundary point belongs to levels \(i\) and \(k\), nesting
forces it to belong to every intermediate boundary.  Thus raw
past-to-future contact for one chain is exposed on the current separator,
and the Push-V alternating-rectangle bypass is captured by
prefix-to-next-shell rather than shell-to-shell composition.

The proposed finite atom automaton fails as written.  On a shared external
ray, Böttcher height obeys \(t\mapsto2^qt\).  If \(v\) is the first positive
vertex of a finite root partition, the atom \((0,v)\) maps to
\((0,2^qv)\), which crosses \(v\) and cannot be one root atom.  The exact
survivor is the set recurrence
\[
B_{j+1}=g(B_j\cap\partial Q_a),
\]
pending a source-realized one-to-many incidence atlas with endpoint and
trace-restriction data.  A finite relational mask is proved abstractly when
the complete root contact sets are finite unions of arcs, positive-height
endpoints escape them under forward \(2^q\)-expansion, and height-zero
endpoints are preperiodic.  The checked source does not yet supply the
complete binary contact list and endpoint ledger needed to instantiate that
conditional result.

Two additional analytic failures block the submitted response cocycle.
The normalized overlay
\[
\zeta_j=h_{w_j}(Z\cap S_{j+1})
\]
is generally word- and stage-dependent, so two fixed protected cell forms
do not suffice without an equivariance theorem.  Also, the full \(H^1\)
norm is not conformally invariant, while the Dirichlet seminorm requires
componentwise constant quotients or grounding.

The code audit reproduced 2,276 exhaustive and 700 additional random
finite-network cases, exposed the sample SCC overclassification, and found
unsupported singular-internal-mode and repeated-terminal cases in the
Schur routine.  The independent certificate is
`validate_push6_separator_audit.py` with output
`push6_independent_audit_20260725.json`.

Only `BINARY_DIRECT_DECORATION_NESTED_SEPARATOR_CALCULUS` was added as a
proved ledger node.  The ledger now has 296 obligations: 23 imported, 210
proved, and 63 open.  The broad marked-contact, welding, collar, end-plumbing,
H2, MBTT, VAAPC-I, UPTCR, and MLC gates remain open.

## 2026-07-25: Research Push VII binary-contact, pseudo-trace, and Value audit

The Push-VII bundle at
`research/mlc_research_push_7_bundle/push7` was preserved unchanged.  All
fifteen files match the supplied SHA-256 manifest.  The eight finite compiler
tests, 800 exact Kronecker checks, and 300 exact moment checks reproduce.
The complete disposition is
`research_push_7_assessment_and_integration.md`.

The source audit recovers one genuine structural theorem.  For the actual
binary \(f^q\) pullbacks of one fixed Kahn--Lyubich decoration block,

\[
\widehat C_{wa}=g_a(\widehat C_w\cap C_a),
\]

and incomparable cylinders are disjoint, while

\[
\partial D_u\cap\partial D_{ut}=\phi_u(C_t).
\]

The depth-\(n\) source attachment fan gives the exact prefix endpoint
itineraries.  After depth \(n\), the normalized structural contact skeleton
has the complete \(\alpha\)-ray pair or the empty state.  This yields
`FIXED_BLOCK_BINARY_CONTACT_AUTOMATON`.

The submitted boundary compiler is not a source realization.  Its
ray/equipotential alternation omits the source distinction between a vertex
join and an equipotential connector.  The fixture is synthetic, not an
actual parameter block.  Adversarial records with missing boundary words,
false shift vertices, multiple same-branch lifts, empty flags, or empty
refinement relations still return `passed=true`.  The independent
reproduction is `validate_push7_audit.py`.

The pseudo-trace theorem is not promoted.  The source constructs
pseudo-piece covers and immersions with finite ideal-boundary arcs and
continuous boundary extension, but it does not construct the proposed
\(H^1_{\rm fin}\) space, bounded ideal-arc traces, closed compatible
quotients, or response forms.  Moreover, the packet tracks only the
dynamical cover and omits the inclusion-induced immersion; the physical
welding problem therefore remains.  The safe-gap theorem also overreaches:
avoiding \(Q_L,Q_R\) does not prevent a root enlargement from reaching
\(\partial P\) or a marked interface.

One additional fixed-tree identity survives.  Grouping KKL pulled
bivertical intersections by
\((f_*^m\alpha,(\iota_m)_*\alpha)\) gives

\[
\operatorname{Val}(X)
=
\lambda^{-2m}
\langle aa^\top,\mathsf M_m(X)\rangle
\]

with a positive-semidefinite moment of dimension
\(|E|^2(|E|^2+1)/2\).  This adds
`FIXED_KKL_PAIR_STATE_MOMENT_FACTORIZATION`.  The binary incidence maps,
completely positive transport, universal edge bound, and future-observability
gap remain open.

The generic matrix-product identity is documented but not ledger-promoted.
The proposed fifteen-node patch and duplicate umbrella gate are rejected.
The ledger now has 298 obligations: 23 imported, 212 proved, and 63 open.
The complete marked contact, trace/welding/collar, end-plumbing, H2, MBTT,
VAAPC-I, UPTCR, and MLC gates remain open.

## 2026-07-25: Research Push VIII marked-interface source audit

The Push-VIII bundle at `research/mlc_research_push_8_bundle` was audited
against the complete finite programs and the locked Kahn--Lyubich and KKL
source files.  Its submitted randomized computations reproduce, but they
test the packet's finite label predicate and matrix associativity rather
than an analytically realized pseudo-piece correspondence.  The complete
disposition is `research_push_8_assessment_and_integration.md`.

The proposed boundary-hull identity is not a consequence of KKL's
immersion-pullback definition.  KKL define \(\iota^*X\) through proper
target paths, unique proper lift components, and ideal-boundary
subordination homotopy.  The submitted atom table records only a target
micro-atom or a nonproper symbol; it omits the lift relation, subgroup,
monodromy, and homotopy data.  KKL's native explicit component formula
uses the actual Hubbard-tree inclusion and exhausts every attached
component.  The checked pseudo-piece source supplies coverings,
immersions, finite boundary arcs, and continuous boundary extension, but
no analogous component-exhaustion theorem.

The compiler also misstates KKL end-properness.  KKL require properness on
whole end-intervals of the multi-interval in \(f^*\mathcal I\), whereas the
compiler tests only its first and last micro-atoms.  A coarse covering
interval with a nonproper middle is therefore falsely accepted.  Moreover,
the positive fixture is not a realizable covering atlas: an atom declared
homeomorphic to \(M_0\) has both covering endpoint images equal to \(0\).

The proposed word-welding formula has a further exact typing obstruction.
A pull--push operator has separately typed immersion-restriction and
covering-transport factors.  Consecutive correspondences require a
fiber-product domain and a Beck--Chevalley interchange square; ordinary
matrix associativity does not move a restriction factor through a
covering factor.  Final-root commuting squares also need a bijection of
complete pullback components and explicit no-new-sheet and
no-new-nonproper-bridge clauses.

Two narrow proved nodes are retained:

- `FINITE_LINEAR_LABEL_MARKING_ENUMERATOR`, solely for the abstract
  deletion-and-seed label model; and
- `PULL_PUSH_WELDING_WORD_COMPOSITION_NO_GO`, recording the exact
  pull--push composition obstruction.

The action/trace endpoint distinction is retained as a no-laundering rule.
The proposed analytic pullback, end-germ, trace, welding, slit,
normalized-word, enlargement, and fixed-horizon completion nodes are not
promoted.

The authoritative ledger now has 300 obligations: 23 imported, 214 proved,
and 63 open.  The complete marked contact, trace-collar, welding,
end-plumbing, virtual marked correspondence, Wave horizon, H2, MBTT,
VAAPC-I, UPTCR, coercivity, rigidity, and MLC gates remain open.

## 2026-07-25: Fixed direct-decoration embedding and path-lift exhaustion pass

The follow-up source pass is recorded in
[`direct_decoration_path_lifted_collar_certificate.md`](direct_decoration_path_lifted_collar_certificate.md).
It used the official Kahn--Lyubich arXiv:math/0609046 archive and the
official KKL arXiv:2606.27272v1 source.  The audited hashes are:

```text
.tmp_kl08_source.tar
  DA8FCF924793267421F80BE3E17CD7EB2B72CD4F5B08E3F5A38E2161EC608234
kingdom.tex
  5DC04FEFF6B6A1D73040FFD50519C35D62EFF03C1049686DA71D595758E38FA7
psiql.tex
  6CC9726461473812A5FBA93377F2DC0B088DB6CAC4B9DE90C7B2AE625DFB49AF
moduli.tex
  CBDB9EF7D6AC94C33FDB0AB7167E19C39EB23D27373C266A296CF6031E0CAF7E
waves-with-Misha.tex
  AD4C774806D9902AA54FA31C56AD6146D8034946F19CC5E9CEC3C51A3F94FDD5
```

Theorem 4.1 proves that, for either fixed KL direct-decoration branch
\(g=f^q|_{Q_a}:Q_a\to P\), the inclusion-induced pseudo-piece immersion
\(\boldsymbol\iota_a:\mathbf Q_a\to\mathbf P\) is an interior holomorphic
embedding.  The verified chain is:

1. \(g(K(f)\cap Q_a)=K(f)\cap P\), hence \(g\) bijects the finite
   complementary-component sets;
2. KL's inclusion component map is surjective, hence bijective here;
3. each annular inclusion induces \(+1\) on
   \(\pi_1\cong\mathbb Z\), so every chosen universal-cover lift is
   injective; and
4. central/central, same-tile, distinct-tile, and tile/central collision
   checks show that every target equality is already a source gluing
   equality.

This removes interior sheet collisions for one fixed branch.  It does not
promote boundary injectivity, immersion properness, ideal-marking
pullback, complete end-interval properness, uniform constants, or a full
Wave horizon.

The attempted KKL path-lift construction stops at an exact accessible-
footprint datum.  With
\(\Omega=\boldsymbol\iota_a(\mathbf Q_a)\), each nonproper source ideal
side \(E\) has an adjacent complement component
\(C_E\subset\mathbf P\setminus\Omega\) and footprint

\[
 \Phi_{\rm acc}(E)=
 \{x\in\partial_i\mathbf P:
   C_E\text{ contains a proper arc from the side }E\text{ to }x\}.
\]

The first unresolved component is adjacent to an immersed
deeper-equipotential outer side and may connect, through a target-tile
overlap, to multiple target ports.  If its footprint meets two marked
target intervals and one proves extensions avoiding all further
\(\Omega\)-intersection, target proper paths ending in the two intervals
share the same unique proper source crosscut.  The KKL pullback definition
then forces a merge or an exclusion proof; proper/nonproper labels and
flanking labels decide neither.  The checked KL source gives no complete
port enumeration, no single-footprint theorem, no no-further-intersection
lemma, and no exclusion-crosscut atlas.  Thus the next source-specific
obligation is to enumerate every
\(C_E\), compute its complete footprint with based sheet and subgroup
data, prove the unique-lift implication, and verify whole end-interval
properness.

This pass promotes precisely:

- `DIRECT_DECORATION_DEGREE_ONE_PSEUDO_EMBEDDING`;
- `KL_TILE_INTERIOR_HOMOGENEOUS_TRACE`;
- `NONPROPER_LABEL_HULL_PULLBACK_NO_GO`.

It adds and leaves open:

- `DIRECT_DECORATION_PSEUDO_PIECE_PATH_LIFT_EXHAUSTION`.

The authoritative counts are now 304 obligations: 23 imported,
217 proved, and 64 open.  Complete marked contact, trace-collar and
welding realization, end plumbing, virtual marked correspondence,
`VIRTUAL_WAVE_HORIZON_CERTIFICATE`, H2, MBTT, VAAPC-I, UPTCR, coercivity,
rigidity, and MLC all remain open.

### Release verification

The machine ledger audit is valid at 304 obligations, and the transfer
regression suite passes.  All 29 standalone `validate_*.py` programs pass
after updating the historical Push-V count assertion to the current ledger
and retaining its marked-incidence check.  The LaTeX build is warning-free.

The synchronized manuscript release is:

```text
output/pdf/marked_width_mlc_manuscript.pdf
pages: 124
SHA256: 3D222822737F50FBADA4AF21BBFEED6258CFF28A4B3FAED3337A9F8044EB00F2
```

Extracted text confirms the three new proved theorem labels, the open
path-lift exhaustion problem, the 304/23/217/64 counts, and the explicit
statement that UPTCR and MLC remain open.  Targeted rendered inspection was
limited to the abstract/status page and the changed proof pages 73--75; no
bulk PDF image sweep was performed.

## 2026-07-25: Outer-port footprint and exact disk-pullback pass

### Question

For the fixed KL direct-decoration inclusion

\[
 \boldsymbol\iota:\mathbf Q_a\hookrightarrow\mathbf P,
\]

does the nonproper source \(O\)-side have a computable target footprint,
and is that footprint sufficient—not merely necessary—for the universal
KKL pullback condition?

### Source correction

The first draft treated the named KL boundary-to-prime-end
identification as an extra open hypothesis.  A complete source re-audit
showed that this was too conservative.

- Kahn I, `wad.tex`, lines 169--175, defines ideal boundary by universal
  disk uniformization.
- KL II, `psiql.tex`, lines 109--160, supplies a finite open star cover of
  every pseudo-piece by the central disk and simply connected
  universal-cover tiles.  Van Kampen gives simple connectivity.
- If the bold target disk uniformizes as \(\mathbb D\), Liouville
  excludes a plane source.  If it uniformizes as \(\mathbb C\), the
  path-space projection omits at least two source-obstacle vertices, so
  Little Picard excludes a plane source.  Thus the pseudo-piece is
  conformally a disk.
- `psiql.tex`, lines 231--253, calls
  \(\lambda,\xi,\eta\) a tiling of that ideal boundary and extends the
  inclusion immersion continuously to it.

Thus the named KL boundary is already the conformal ideal circle.  No
physical-Julia local connectivity is used.

An initially proposed shortcut—claiming that every proper curve
eventually remains in one tile—was rejected.  Near a shared ideal vertex,
a curve can alternate through adjacent sectors.  The proof uses Kahn's
uniformization definition instead.

### Abstract theorem proved

For a holomorphic embedding of conformal disks with continuous extension
to the closed ideal disks:

1. every connected boundary fiber is a singleton, by a self-contained
   Jensen--Fatou boundary uniqueness argument;
2. every component of a target proper path intersected with the embedded
   image is topologically proper and has a connected endpoint cluster set
   in one light boundary fiber, hence two actual source ideal limits;
3. repeated copies of a unique source restriction are finite, by
   compactness and openness of the embedded image; and
4. a complement access can be traversed in both directions around a
   source hairpin, so no local perturbability or simplicity of the target
   path is assumed.

For

\[
 \Phi_\iota(p)
 =
 \{\text{target ideal ends accessible from the complement at }p\},
\]

the unique maximal KKL pullback is therefore

\[
 \iota^*I=\{p:\Phi_\iota(p)\subset I\}.
\]

The theorem holds for arbitrary source subsets in the admissibility test,
so the displayed safe set is a genuine maximum, not one of several
incomparable maximal connected candidates.

### Fixed-branch geometry proved

Common Böttcher/logarithmic coordinates give

\[
 \widehat A_{s,i}\cong\Pi(h_s),\qquad
 \widehat A_{t,j}\cong\Pi(h_t),\qquad
 h_s=2^{-q}h_t,
\]

and the inclusion lift is a real translation of the complete lower
strip.  The upper target cap is a full component of
\(\mathbf P\setminus\Omega\); reaching another tile or the central Julia
seam would cross the occupied lower strip.  Its complete ideal footprint
is the closed target \(O\)-port.

An adversarial correction strengthened ``full component'' from a path
argument to a connected-set argument.  The continuous Green height sends
connected sets to intervals; a complement continuum meeting height \(0\)
and height at least \(h_s\) would meet the forbidden occupied band
\(0<G<h_s\).  This excludes wild non-path-connected attachments as well
as ordinary bypasses.

Consequently:

\[
 \operatorname{relint}\lambda_{s,i}
 \subset\boldsymbol\iota^*I
 \iff
 \overline{\lambda}_{t,j(i)}\subset I.
\]

The open target \(O\)-atom fails because it omits the two wrapping
corners.  The unique local open interval between the neighboring Julia
vertices—the \(O\)-atom plus both adjacent \(J\)-atoms and the two
wrapping corners—succeeds.  It has combinatorial length three,
independent of period and corridor length.

### Promotion boundary and next gate

Promoted as proved:

- `KL_PSEUDOPIECE_CONFORMAL_IDEAL_BOUNDARY`;
- `EMBEDDED_DISK_ACCESSIBLE_FOOTPRINT_THEOREM`;
- `DIRECT_DECORATION_OUTER_CAP_FOOTPRINT`.

Still open:

- `DIRECT_DECORATION_PSEUDO_PIECE_PATH_LIFT_EXHAUSTION`;
- `DIRECT_DECORATION_ALL_DEPTH_CONTACT_CLOSURE`;
- `VIRTUAL_WAVE_MARKED_CORRESPONDENCE`;
- VAAPC-I;
- UPTCR;
- MLC.

The exact next geometric task is to enumerate the actual complement
components landing on each source \(\xi/\eta\) central-seam side, compute
their complete target ideal footprints, and then prove family-level
pullback disjointness, covering refinement, and complete
proper/end-proper action.

The authoritative ledger after this pass contains 307 obligations:
23 imported, 220 proved, and 64 open.

### Release verification

The final audit sequence completed as follows:

- `audit_proof.py`: valid at 307 obligations, with MLC open;
- `audit_transfer_regressions.py`: every transfer regression passed;
- all 30 standalone `validate_*.py` programs passed, including the new
  source-lock/status/finite-formula audit
  `validate_outer_port_footprint.py`;
- the LaTeX build completed without warnings, undefined references,
  overfull boxes, or underfull boxes;
- programmatic PDF text extraction found the three new theorem headings on
  pages 75--76 and the 307/23/220/64 status with ``MLC is open'' on page
  4; and
- no page-image or bulk visual sweep was performed.

The synchronized release is:

```text
output/pdf/marked_width_mlc_manuscript.pdf
pages: 126
bytes: 5662385
SHA256: F9F1BE10B233D1B87B83B422A3DD70D3E75FDAD59F7D139DE4E6183DC8A882F9
```

## 2026-07-25 -- Hostile re-audit of the direct-decoration embedding and cap

This entry supersedes the current-status conclusions, but not the historical
record, in the two preceding direct-decoration entries.

### Retraction of two source-specific promotions

A line-by-line rereading of the Kahn--Lyubich sources found that the earlier
fixed-branch argument conflated two different settings:

- physical nesting \(U^{m+q}\subset U^m\) in the initial ordinary
  quadratic-like model; and
- the bold ambient maps at a general \(\psi\)-quadratic-like stage, where
  KL assert only holomorphic immersions.

The earlier proof of
`DIRECT_DECORATION_DEGREE_ONE_PSEUDO_EMBEDDING` therefore lacked same-tile
global injectivity.  Degree one and local univalence cannot repair the gap:
for \(a>e^{2\pi h}\),

\[
F_a(z)=z+\frac{a}{2\pi i}e^{2\pi iz}
\]

is a \(\mathbb Z\)-equivariant locally univalent strip map with distinct
points in one fundamental strip having the same image.

The earlier proof of
`DIRECT_DECORATION_OUTER_CAP_FOOTPRINT` also used an unproved simultaneous
common logarithmic coordinate.  Even global embedding does not force the
claimed geometry: for sufficiently small nonzero real \(\varepsilon\),

\[
L_\varepsilon(z)=z+\varepsilon\sin(2\pi z)
\]

is an embedded degree-one strip map whose upper boundary has nonconstant
height.  Hence the exact lower-strip cap and closed-\(O\)-port footprint
remain valid only under an explicit common-coordinate hypothesis.

The two source-specific nodes are returned to **open** status.  No global
claim ever depended on treating them as closed, and MLC, UPTCR, and VAAPC-I
remain open.

### Results that survive

The audit retains:

- `KL_PSEUDOPIECE_CONFORMAL_IDEAL_BOUNDARY`;
- `EMBEDDED_DISK_ACCESSIBLE_FOOTPRINT_THEOREM`, under its explicit
  embedding and continuous ideal-extension hypotheses;
- `KL_TILE_INTERIOR_HOMOGENEOUS_TRACE`;
- `NONPROPER_LABEL_HULL_PULLBACK_NO_GO`;
- the new proved no-go nodes
  `DEGREE_ONE_ANNULUS_IMMERSION_INJECTIVITY_NO_GO` and
  `GENERAL_ANNULUS_IMMERSION_LOWER_STRIP_NO_GO`;
- the conditional criterion
  `TILE_INJECTIVITY_GLUE_EMBEDDING_CRITERION`; and
- the conditional positive control
  `COMMON_COORDINATE_NESTED_ANNULUS_OUTER_CAP`.

The authoritative ledger now contains 311 obligations:
23 imported, 222 proved, and 66 open.

### Correct next source-specific gate

The immediate task is
`DIRECT_DECORATION_DEGREE_ONE_PSEUDO_EMBEDDING`: prove global injectivity
of every actual KL direct-decoration tile immersion, or produce the first
actual collision with its two source points, tile, deck data, and induced
quotient collision.  Only after that gate closes can the actual
\(O\)-footprint be computed and the \(\xi/\eta\), family-level,
covering-refinement, and end-properness stages resume.

The corrected release audit and PDF identifiers are recorded after the
machine artifacts and manuscript are regenerated.

### Second hostile pass

A second independent pass found and repaired five additional
proof-presentation defects without changing any ledger status:

1. The pseudo-piece van Kampen proof may not call the closed physical
   puzzle piece an open cover member.  The corrected cover uses
   \(\operatorname{int}Y\) and the open tile images.  Boundary vertices
   lie in the omitted set, all other central-boundary points lie in tiles,
   and a Schoenflies collar proves the nonempty intersections
   path-connected.
2. The common-coordinate cap proof now establishes the footprint
   pointwise from each fixed source prime end, not merely after taking a
   union over the whole \(O\)-side.
3. The actual KL immersion record now retains every landing complement
   component; it no longer assumes one adjacent component, an embedded
   boundary crosscut, or a physical equipotential shell.
4. The finite label-hull no-go now claims only what its endpoint predicate
   proves: all open source atoms, including the obstructing nonproper atom,
   are retained.  It makes no unproved claim about the two intervening
   vertices.
5. Quotient injectivity of the wavy-strip positive countermodel is now
   proved by the deck calculation, rather than inferred from equivariance.

These repairs preserve the 311/23/222/66 ledger split and leave the actual
KL embedding, actual \(O\)-footprint, VAAPC-I, UPTCR, and MLC open.

### Corrected release verification

The post-correction audit completed with:

- `audit_proof.py`: valid at 311 obligations
  (23 imported, 222 proved, 66 open), with MLC open;
- all 30 standalone `validate_*.py` programs passing;
- `audit_transfer_regressions.py` passing;
- regenerated ledger appendices agreeing with the JSON statuses and
  counts;
- a warning-free LaTeX build with no undefined references, overfull
  boxes, or underfull boxes; and
- programmatic PDF text extraction confirming the 311/23/222/66 status,
  the open fixed KL pseudo-piece embedding problem, the open actual KL
  outer-port footprint, the pointwise conditional footprint theorem, and
  absence of the retracted ``entire source ideal circle'' and actual-cap
  claims.

Per the user's instruction, no bulk page-image or VLM visual sweep was
performed.

The synchronized corrected release is:

```text
output/pdf/marked_width_mlc_manuscript.pdf
pages: 128
bytes: 5673981
SHA256: 94ED69E91CC7120A484B7AB14F7FF84D7DCFCA1D1932E03BB85D18A707046AFB
```

## 2026-07-25 — Actual KL tile/base injectivity reduction

The next source pass attacked the first open gate left by the hostile
Push-VIII audit.  It first tested a tempting physical-nesting proof and
rejected it.

### Rejected route

For an ordinary quadratic-like map, Kahn I `pullback.tex`, lines 2--7 and
25--36, has the physical inclusions \(U^{m+1}\subset U^m\).  A lift of
such an annulus inclusion is injective.

That is not the general KL situation.  KL II `macros.tex`, line 261,
defines `\BU` to mean \(\mathbf U\).  KL II `psiql.tex`, lines 118 and
198--206, constructs the tiles from
\(\mathbf U^m\setminus K(f)\) and calls the ambient transition and its
universal-cover extensions immersions.  Kahn I `conclusions.tex`, lines
39--49, explicitly describes replacement of the former embedding by an
immersion.  Thus physical nesting of the central puzzle pieces cannot be
extended silently to the full bold ambient annuli.

### Proved exact reduction

Let \(I:A_s\to A_t\) be a degree-one holomorphic annulus immersion and let
\(L:\widetilde A_s\to\widetilde A_t\) be a compatible lift.  With positive
deck generators,
\[
 LT_s=T_tL.
\]
The new theorem proves
\[
 L\text{ injective}\quad\Longleftrightarrow\quad I\text{ injective}.
\]

If \(I(u)=I(v)\), \(u\ne v\), choose lifts \(x,y\).  There is a unique
\(k\) with \(L(y)=T_t^kL(x)\), and therefore
\[
 L(T_s^{-k}y)=L(x)
\]
at two distinct source points.  Conversely, a lift collision projects to
a base collision; if the base is injective, the source points differ by a
deck translate, and target deck freeness forces that translate to be
trivial.

A second proposition proves that a proper degree-one holomorphic
immersion between connected annuli is a biholomorphism: it is an open and
closed proper local biholomorphism, hence a finite covering of the
connected target, and degree one makes it one-sheeted.

### Source obstruction and status

Kahn I `psiql2.tex`, lines 87--130 and 155--177, supplies only an embedded
inner collar.  Kahn I `conclusions.tex`, lines 39--49, uses only the
properness at the required little-Julia-set ends.  KL II `psiql.tex`,
lines 248--253, explicitly allows source ideal boundary to map into target
interior.  Full base-annulus properness and global base univalence are not
source-proved.

The exact remaining question is therefore global univalence of the actual
bold ambient annulus immersion.  It is equivalent to tile injectivity and,
combined with the already proved gluing criterion, would prove the fixed
pseudo-piece interior embedding.  No global gate is promoted.

The new proved ledger node is:

- `KL_TILE_INJECTIVITY_BASE_ANNULUS_REDUCTION`.

At that intermediate point the ledger validated 312 obligations:
23 imported, 223 proved, and 66 open.
`DIRECT_DECORATION_DEGREE_ONE_PSEUDO_EMBEDDING`, VAAPC-I, UPTCR, and MLC
remained open.

### Exact abstract-annulus counterexample

A second adversarial pass tested whether Kahn's complete stated annulus
hypotheses might nevertheless imply the missing global base univalence.
They do not.

For
\[
 r'=\frac{1287}{1000},\qquad r=(r')^{16},
\]
the finite Blaschke quotient
\[
 R(z)=
 \frac{
 B_{(1+6i)/10}(z)B_{(-3-i)/10}(z)B_{(-7+2i)/10}(z)}
 {B_{(-6+2i)/10}(z)B_{4i/10}(z)}
\]
maps \(\mathbb A(1,r')\) immersively into \(\mathbb A(1,r)\), extends
analytically to the inner circle as an orientation-preserving degree-one
homeomorphism, and is noninjective.

This is an exact proof rather than a numerical root observation:

- Gaussian-integer expansions identify every zero, pole, derivative
  numerator, and collision polynomial;
- two exact Sturm chains prove the positive angular derivative and the
  outer-circle inequality \(|R|>1\);
- the harmonic minimum principle and an explicit rational bound prove
  \(1<|R|<r\) on the source annulus;
- eight pairwise-disjoint rational Rouche disks exhaust all eight
  derivative-numerator roots outside the source annulus; and
- a ninth rational Rouche disk isolates a second exact root of
  \(N-R(z_1)D_0\), \(z_1=-1+4i/5\), inside the source annulus.

The complete proof is
`kahn_annulus_global_injectivity_no_go.md`; the independent exact
recomputation is `validate_kahn_annulus_no_go.py` with output
`kahn_annulus_no_go_validation_20260725.json`.

This proves `KAHN_ANNULUS_GLOBAL_INJECTIVITY_NO_GO`.  It is not an actual
KL dynamical-stage counterexample, so
`DIRECT_DECORATION_DEGREE_ONE_PSEUDO_EMBEDDING` remains open.

The current ledger now validates 313 obligations: 23 imported, 224 proved,
and 66 open.  VAAPC-I, UPTCR, and MLC remain open.

## 2026-07-25 — KL tile-injectivity release verification

The source-locked KL pass and the exact Kahn-annulus counterexample are now
integrated into the formal manuscript.  Two local nodes are proved:

- `KL_TILE_INJECTIVITY_BASE_ANNULUS_REDUCTION`;
- `KAHN_ANNULUS_GLOBAL_INJECTIVITY_NO_GO`.

The first reduces universal-cover tile injectivity at a degree-one stage
exactly to injectivity of the bold base-annulus immersion and proves that
full properness would suffice.  The second gives an exact finite-Blaschke
counterexample to the attempted inference from Kahn's complete abstract
annulus-lemma hypotheses to global injectivity.  It is not an actual KL
dynamical-stage counterexample.

An independent line-by-line audit found and corrected four omitted addition
signs in the Markdown display of the critical polynomial.  The executable
coefficient array and LaTeX display had already been correct.  The validator
now checks the signed polynomial terms in both documents, proves positivity
of every angular-denominator factor by exact discriminants, and verifies the
Blaschke-factor maximization identities and all rational modulus bounds.
The source ledger's earlier fixed-branch embedding claim is now explicitly
marked superseded rather than left in present-tense theorem language.

All 34 project validators and proof/transfer audits pass.  The regenerated
ledger has 313 obligations: 23 imported, 224 proved, and 66 open.  The LaTeX
log has no LaTeX/package warnings, undefined citations or references,
missing characters, or overfull/underfull boxes.  Extracted text confirms
the ledger counts, both new proved records, the open direct-decoration
pseudo-embedding gate, and the open UPTCR and MLC records.  In accordance
with the user's instruction, this text-only revision received no bulk
page-image/VLM sweep.

The synchronized release artifact is:

```text
pages: 131
bytes: 5689734
SHA256: AF6B6892A6E705F25A62235AEC3B5BB3248B5FF3C407AAB0EE71EAD868446A26
```

The exact next mathematical gate is
`DIRECT_DECORATION_DEGREE_ONE_PSEUDO_EMBEDDING`: prove global univalence of
the actual KL bold base-annulus immersion, or construct an actual
dynamically realized collision certificate.  Kahn's collar lemma, winding
degree one, and limited end-properness cannot discharge it.  The documented
replacement route is a collar-truncated pseudo-piece with a complete
outer-exit defect ledger.  VAAPC-I, UPTCR, and MLC remain open.

## 2026-07-25 — abstract \(\psi\)-ql no-go, conditional collars, and overlap-reflection correction

This pass closes three narrow internal statements without promoting any
global theorem.

1. `PSI_QL_GLOBAL_INJECTIVITY_NO_GO` is proved by the complete abstract
   degree-two pair
   \[
   f(z)=z^2,\qquad
   i(z)=\frac{e^{\pi(z+1)/50}-1}{e^{\pi/25}-1},
   \qquad
   K=[0,1],\quad K'=[-1,1],
   \]
   on \(\mathbb D_{75}\to\mathbb D_{5625}\).  Exact logarithmic-sheet
   enumeration gives \(i^{-1}(K)=f^{-1}(K)=K'\), the complementary
   annular degree is \(+1\), and \(i(50i)=i(-50i)\).  This is not an actual
   KL localization-stage collision.
2. `KL_LOCALIZATION_SUBGROUP_REFLECTION_CRITERION` is proved: a lift of an
   independently verified physical embedding is injective exactly when
   \(a_*^{-1}(H_t)=H_s\).  The KL application is conditional because a
   general bold \(\psi\)-ql map is supplied only as an immersion.
3. `FINITE_HORIZON_KAHN_COLLAR_EMBEDDING` is proved as an explicitly
   conditional theorem.  Full Kahn annulus data, central embeddings,
   tile-component bijections, exact embedded gluing, and overlap
   reflection on the retained collars yield coherent Kahn collars and
   collar-truncated pseudo-piece embeddings over one fixed finite horizon.
   Complete footprints give the safe-set formula, whose maximal connected
   candidates need not be unique.

The hostile quotient audit found a material gap in the older
`TILE_INJECTIVITY_GLUE_EMBEDDING_CRITERION`: tile injectivity and forward
overlap commutation do not exclude a tile point outside the declared source
overlap from entering the target central overlap.  The criterion is now
corrected to assume
\[
 L_i^{-1}\!\left(\widetilde e_{j(i)}(P_{j(i)})\right)=e_i(Q_i).
\]
The actual source-specific statement is recorded separately as the open
`DIRECT_DECORATION_TILE_CENTRAL_OVERLAP_REFLECTION` obligation.  The
common-coordinate outer-cap control was correspondingly narrowed to
include this equality as part of its explicit model hypothesis.

The authoritative ledger is valid and acyclic with 317 obligations:
23 imported, 227 proved, and 67 open.  All 35 validators and all three
independent audits pass.  The LaTeX build has zero LaTeX/package warnings,
box warnings, undefined citations/references, missing characters, or
errors.  Extracted text confirms the three new proved nodes and the open
overlap-reflection, full pseudo-piece, VAAPC-I, UPTCR, and MLC nodes.  Four
changed pages were inspected as targeted layout checks; no bulk page-image
sweep was performed.

The synchronized release artifact is:

```text
pages: 136
bytes: 5712199
SHA256: 53A11EE52C304A83E9CF89AE5CE749124006F45C92BD5B27BC4DBCF864E4BBAE
```

The immediate analytic gate is now two-pronged: instantiate the actual KL
base/localization data and prove both base univalence (or subgroup
reflection after a verified physical-embedding realization) and
tile--central overlap reflection.  If either fails, record the first base
collision or the first point outside the source overlap entering the
target overlap.  Only after both may the full pseudo-piece embedding and
actual \(O,\xi,\eta\) footprint exhaustion proceed.  VAAPC-I, UPTCR, and
MLC remain open.

## 2026-07-25 -- relative overlap cartesianity and removal of an overconstraint

This pass corrects the final paragraph of the immediately preceding entry.
The full inverse-image equality

\[
 L_i^{-1}\!\left(\widetilde e_{j(i)}(P_{j(i)})\right)=e_i(Q_i)
\]

is not an independent prerequisite for injectivity of the **full** fixed
direct-decoration pseudo-piece map.

The exact quotient invariant is reflection of the gluing equivalence
relation.  In a finite star this becomes the mixed central--tile fiber
product over the source-central image.  For the fixed KL direct pair,

\[
 Q\setminus K_Q=Q\cap(P\setminus K_P)
\]

and the proved bijectivity of the component map give

\[
 Q\cap P_{j(i)}=Q_i.
\]

If the full tile map \(L_i\) is injective, overlap commutation gives

\[
 L_i^{-1}\!\left(\widetilde e_{j(i)}(Q_i)\right)=e_i(Q_i).
\]

A complete central--central, same-tile, different-tile, and tile--central
collision audit therefore proves

\[
 \boldsymbol\iota:\mathbf Q\to\mathbf P\text{ injective}
 \quad\Longleftrightarrow\quad
 \text{every full tile map }L_i\text{ is injective}.
\]

The proof is recorded in `kl_relative_overlap_cartesianity.md` and
integrated into `direct_decoration_path_lifted_collar_certificate.md`,
`actual_kl_tile_injectivity_gate.md`, the ledgers, and the formal
manuscript.  Two hostile controls delimit the theorem:

1. nested disk pushouts give an injective quotient map while full overlap
   reflection fails, because the excess target-overlap points have no
   source-central mates;
2. two overlapping rectangles mapped by \(e^z\) give embedded central and
   tile restrictions with commuting declared overlap but a mixed collision
   \(e^0=e^{2\pi i}=1\), proving that relative relation reflection is a
   real condition rather than formal bookkeeping.

The strong
`DIRECT_DECORATION_TILE_CENTRAL_OVERLAP_REFLECTION` node remains open only
as a non-gating saturation question for any collar, footprint, or carrier
theorem that explicitly needs all of \(P_j\).  It has no descendants in
the machine ledger and is no longer a dependency of
`DIRECT_DECORATION_DEGREE_ONE_PSEUDO_EMBEDDING`.  The collar-truncated
theorem retains its stronger overlap hypothesis: collar injectivity cannot
compare with a canonical overlap representative that may lie outside the
retained collar.

The authoritative ledger remains valid and acyclic with 317 obligations:
23 imported, 227 proved, and 67 open.  The obsolete saturation node no
longer appears among the backward blockers of MLC.  All 36 validators and
all three independent audits pass.  The LaTeX log contains no
LaTeX/package, box, citation, reference, character, or fatal warnings.
Extracted release text confirms the corrected equivalence on page 73, the
non-gating saturation warning on page 74, the narrowed open problem on
page 81, the corrected machine dependency on page 126, and `MLC open` on
page 137.  Only pages 73, 74, 81, and 82 were rendered and inspected; no
bulk page-image sweep was performed.

The synchronized release artifact is:

```text
pages: 137
bytes: 5715805
SHA256: 5A8B1EE20D358E2F071EECCA63CBD20262D2D08FBED6FBCE25F01F49F4388384
```

The immediate analytic gate is now single-pronged for the full fixed pair:
prove global univalence of the actual degree-one bold base-annulus
immersion, equivalently injectivity of every full tile lift, or exhibit
the first dynamically realized base collision and its forced deck-shifted
tile collision.  Only after this may the actual \(O,\xi,\eta\) footprint
and whole-end exhaustion chain proceed.  VAAPC-I, UPTCR, and MLC remain
open.

## 2026-07-25 -- actual canonical-localization collision and route correction

The alternative demanded in the preceding entry is now resolved on every
ordinary primitive canonical seed, negatively.  The complete analytic
proof is `kl_canonical_localization_forced_collision.md`; its focused
machine audit is
`validate_kl_canonical_localization_forced_collision.py`.

For \(F=f^p:U^p\to U^0\), \(A=K_p\), and
\(B=\mathcal K_p\), Kahn's canonical source removes \(F^{-1}B\) and its
target removes \(B\).  The proof proceeds through the following audited
chain.

1. Nested Jordan neighborhoods, the unbranched-cover dichotomy, and
   bordered Riemann--Hurwitz prove that the pullback of a full continuum
   by one quadratic disk map is one degree-two full continuum or two
   degree-one full continua.
2. Iteration makes \(F^{-1}B\) a finite pairwise-disjoint family of full
   continua.  An explicit connectivity lemma proves that its complement
   in \(U^p\) is path connected.
3. Global degree \(2^p\) and central degree two force an excess component
   \(X\ne A\) of \(F^{-1}A\).
4. The actual identities \(F(K_p(j))=K_p(j)\) and primitive pairwise
   disjointness prove \(X\cap B=\varnothing\).
5. Finiteness and fullness give a Jordan disk \(D_X\Subset U^p\) whose
   closure misses \((F^{-1}B\setminus X)\cup B\).
6. A based peripheral loop has winding one about \(X\), whereas every
   source-local loop near \(A\) has winding zero.  Thus
   \([\gamma]\notin H_s\).
7. The same loop contracts across \(D_X\) in the target complement, so
   \(a_*[\gamma]=1\in H_t\).  Its source lift has distinct endpoints that
   the target lift identifies.
8. Kahn's exact equalizer pullback propagates the point collision to every
   \(i_r\).  Whenever the same seed carries KL direct-decoration data,
   the propagation reaches the exact depths
   \(m=\nu q+1\), \(n=(\nu-1)q+1\); degree-one deck equivariance gives a
   same-tile collision in every full tile copy and hence in the full glued
   pseudo-piece immersion.

Three independent audits checked the finite full-pullback argument,
subgroup-kernel loop, equalizer orientation, and exact KL depth
propagation.  The same-seed parameter/stage alignment implication remains
separate and is not used to infer a narrower existential parameter claim.

The ledger promotes only
`KL_CANONICAL_LOCALIZATION_FORCED_COLLISION`.  The former
`DIRECT_DECORATION_DEGREE_ONE_PSEUDO_EMBEDDING` node remains open as a
non-gating restricted-class classification question and has no
descendants.  The actual \(O\)-footprint, path-exhaustion, and all-depth
contact obligations are rerouted through a sheet-sensitive groupoid state
retaining
\[
 a_*^{-1}(H_t)/H_s.
\]
At that pass the ledger had 318 obligations: 23 imported, 228 proved, and
67 open.  VAAPC-I, UPTCR, and MLC remained open.

### Same-seed airplane realization audit

The tempting double-airplane witness was independently source-checked in
`kl_aligned_double_airplane_source_lock_20260725.md`.  Shen--Wang and
Inou--Kiwi license an actual externally marked physical return germ hybrid
equivalent to the airplane, but the checked statements do not literally
prove all downstream clauses for that same germ: pairwise disjointness of
the three outer physical little Julia sets, KL finite non-satellite escape,
both repelling fixed points of the physical germ, and preservation of the
complete KL puzzle marking through Kahn localization.

The promotion was rejected.  No ledger node or manuscript theorem names a
double-airplane counterexample.  The unconditional canonical-localization
collision remains proved; its direct-decoration propagation remains an
explicit same-seed implication.

## 2026-07-25 -- canonical sheet resolution and infinite defect

The next gate is no longer represented by an informal coset list.
`kl_localization_sheet_resolution_factorization.md` proves
`KL_LOCALIZATION_SHEET_RESOLUTION_FACTORIZATION`.

For any based physical embedding \(a:X_s\hookrightarrow X_t\), connected
localization covers with subgroups \(H_s,H_t\), and based lift \(A\), put
\[
 K=a_*^{-1}(H_t).
\]
The based pullback component \(P_K\) is the \(K\)-cover of \(X_s\), and
\[
 \widehat X_s\xrightarrow qP_K\xrightarrow e\widehat X_t,
 \qquad A=e\circ q,
\]
where \(q\) is a covering and \(e\) is embedded.  The kernel pairs of
\(A\) and \(q\) coincide.  This is the unique connected intermediate
factorization in the based, commuting comparison class stated in the
proof.  The category of elements of the path-lifting functor of \(q\) is
the canonical sheet groupoid.

Two independent adversarial audits checked the pullback subgroup,
surjectivity and local covering proof, embedded second leg, kernel-pair
identity, nonnormal coset convention, based uniqueness, compact path
classification, and enlargement algebra.  Their corrections were
incorporated:

1. \(K/H_s\) is only the based fiber, not the full object set of the
   groupoid;
2. the endpoint-coset inversion convention and monodromy action are
   explicit;
3. compact-segment lifting is not called KKL path exhaustion;
4. exact base change propagates the factorization through full, unselected
   complementary-cover equalizers only; filled/prime-end extension,
   component alignment, and same-seed alignment were not proved by that
   stage alone; and
5. the subgroup enlargement criterion is restricted to the based coset
   map and is not called full geometric no-birth.

The winding certificate strengthens the canonical obstruction:
\[
 w(H_s)=0,\qquad w(\gamma)=1,\qquad\gamma\in K.
\]
Therefore \(\gamma^nH_s\), \(n\in\mathbb Z\), are pairwise distinct and
\[
 [K:H_s]=\infty.
\]
Every full canonical collision fiber is infinite.  This rules out a raw
finite sheet list; a finite response state now requires a proved
future-faithful compactification or sufficient quotient preserving all
proof-used path, access, and Value observables.

For an enlargement map \(\varphi\), the induced based coset map is
injective exactly when
\[
 K\cap\varphi^{-1}(H_s^+)=H_s
\]
and surjective exactly when
\[
 K^+=\varphi(K)H_s^+.
\]
These equalities do not detect a new simply connected lobe, component, or
prime-end access.  The geometric final-root gate still requires a
Cartesian cover square, component/path-fiber bijection, obstacle and
nonproper-bridge audit, and authorized endpoint compatibility.

A conditional sheet-isolated footprint criterion is also proved: the
safe-set formula is valid only after endpoint necessity, singleton
KKL-proper-lift hairpins, and the explicit endpoint-subordination axioms
are established on an authorized ideal-boundary model.  Since the raw fiber
is infinite, every competing proper lift must be excluded or retained
explicitly.

At the end of that sheet-resolution stage, the ledger had 319
obligations: 23 imported, 229 proved, and 67 open.
The actual \(O,\xi,\eta\) footprint, selected direct-decoration component,
future-faithful infinite-sheet compactification, whole-end properness,
width and transition gates remain open.  VAAPC-I, UPTCR, and MLC remain
open.

### Release-stage precision audit

A third independent mathematical audit found no counterexample to the
factorization, kernel-pair identity, infinite-index argument, or exact
equalizer base change.  It did identify nine statement-level defects, all
repaired before release:

1. interface subgroup tests now claim only bijectivity of the induced
   based-coset fiber map, not preservation of the full geometric state;
2. \(K/H_s=\{kH_s\}\) is correctly called a pointed left-coset set;
3. Hausdorff is explicit, and the properness proof uses relative closedness
   of interval components rather than an unsupported sequential argument;
4. the conditional safe-set theorem states all endpoint-subordination
   axioms used by its proof;
5. the monodromy functor is distinguished from its
   category-of-elements groupoid;
6. enlargement witnesses are called based-coset merger/birth witnesses,
   not geometric sheet certificates;
7. compact-path exhaustion is restricted to target paths wholly contained
   in \(e(P_K)\);
8. uniqueness is stated only in the connected, based, commuting
   intermediate-cover comparison class proved in Theorem 5.1; and
9. Kahn base change is restricted to the full, unselected exact equalizer
   on the complementary-cover locus, with filled and prime-end extension
   explicitly open.

The focused validator now locks these scope clauses.  No downstream node
was promoted.

### Release audit

The source build `latex/build/main.pdf` was independently checked before
release synchronization.  Unicode NFKC normalization of text extracted
from all 144 pages found:

* that release's ledger totals `319 obligations`, `23 imported`, `229 proved`, and
  `67 open`;
* the theorem markers `Canonical localization sheet resolution`,
  `Infinite canonical sheet defect`, `Base-change propagation of sheet
  resolution`, `Exact based-coset merger and birth tests`, and
  `Sheet-isolated footprint criterion`;
* the explicit notices `MLC is open` and `does not claim an unconditional
  proof`.

Searches for an unconditional MLC, UPTCR, or VAAPC-I promotion found none.
One deliberately broad expression matched the negated sentence “does not
... prove MLC”; inspection confirmed that it is not an overclaim.  All 38
validators, `audit_proof.py`, and `audit_transfer_regressions.py` pass.
The LaTeX log contains no warnings, missing references, missing characters,
or overfull/underfull boxes.  Consistent with the standing no-bulk-render
rule, only the five affected pages 82--84 and 90--91 were rendered and
visually inspected.

The synchronized release has 144 pages, 5,746,997 bytes, and SHA-256
`3AF6E230EA7FF4ECF2C3F24BA1646DDF6D04816E2C8D1054C0EB6429F184C397`.
The date `2026-07-25` records the research-pass date; filesystem
synchronization completed after local midnight.

## 2026-07-25 -- Kahn iterate component and tilewise interior alignment

The next source-locked pass is
`kahn_iterate_complementary_component_alignment.md`, promoting only
`KAHN_ITERATE_COMPLEMENTARY_COMPONENT_ALIGNMENT`.

Kahn's special immersion-pullback lemma proves that the iterate uses the
ordinary topological equalizer; the unrelated general desingularization
discussion is not needed.  The exact membership chain gives
\[
 \mathbf U^{r+2}\setminus K^{r+2}
 =
 (\mathbf U^{r+1}\setminus K^{r+1})
 \times_{\mathbf U^r\setminus K^r}
 (\mathbf U^{r+1}\setminus K^{r+1}).
\]
Kahn proves the pulled pair is again a disk/FJ pair, so this full
complementary equalizer is connected.  The base-changed \(q\)-cover is
surjective, hence its resolved intermediate target is connected as well.

The source audit then sharpened the typing.  KL do not use one
complementary pseudo-piece component: they glue a separate universal-cover
copy for every component of \(Y\setminus K_Y\).  Kahn's oriented
annular-degree-\(+1\) theorem implies that, for every source tile \(a\),
the pullback of its target tile \(j_\iota(a)\) is connected and is the
source universal cover.  The compatible lifted basepoints fix the deck
phase.  Distinct source labels over one target remain separate.
Conditional on a separately supplied annular covering/embedding
factorization \(A_s\xrightarrow qP\xrightarrow eA_t\), base-changing
\(q/e\) through each labelled tile gives a connected resolved
intermediate followed by an embedding.  This is a family-valued
conditional interior theorem; it neither constructs that factorization
for the whole actual KL tile, identifies the canonical infinite
sheet-resolution cover with that tile, collapses source tile indices, nor
identifies the dynamical covering component map with the inclusion
component map.

For one fixed eligible seed, KL use the same Kahn \(\mathbf U^m\)-iterate
tower.  This is conditional fixed-seed alignment, not a theorem that every
canonical seed realizes prescribed decoration combinatorics.

Two independent source audits accepted the finite complementary and
tilewise interior route after two correction rounds.  First, the draft
incorrectly described the iterate pullback as a desingularization; the
proof now cites Kahn's special immersion-pullback lemma and states that no
desingularization occurs.  Second, the first tilewise statement indexed
the construction by a target tile and under-specified the deck phase.
KL's inclusion component map is only surjective, so the corrected theorem
is indexed by each source tile \(a\), retains distinct source labels over
one target \(j_\iota(a)\), and defines the based cover isomorphism from the
actual KL lift \(L_a\) and compatible lifted basepoints.  The audits also
required the FJ/full hypothesis, surjectivity of the resolved cover,
fixed-seed quantifier, separate component maps, and exact nonconclusions.

The immediate open theorem is the **resolved intermediate ideal-boundary
realization**.  For every tile it must construct
\(\overline{\mathcal R}_{r,i}\), extensions of \(q_{r,i}\) and \(e_{r,i}\),
and a declared intermediate outer set with exact deck phase.  KL's
continuous boundary extension of the composite immersion does not extend
either factor automatically.

The authoritative ledger now has 320 obligations: 23 imported, 230
proved, and 67 open.  The actual \(O,\xi,\eta\) footprint,
future-faithful infinite-sheet compactification, whole-end properness,
final-root geometric stability, width, transition, compactness, and
rigidity gates remain open.  VAAPC-I, UPTCR, and MLC remain open.

### Component-alignment release audit

All 39 validators pass: 31 on the bundled runtime and eight SymPy
validators on the project/system Python.  `audit_proof.py`,
`audit_transfer_regressions.py`, and recursive Python compilation pass.
The LaTeX build is warning-free.

Unicode NFKC extraction from all 145 pages confirms:

* `320 obligations`, `23 imported`, `230 proved internally`, and
  `67 open`;
* the theorem marker `Kahn iterate complementary-component alignment`;
* the ordinary-topological-fiber-product and source-indexed
  family-valued scope;
* the immediate authorized ideal-completion gate;
* `MLC is open` and the disclaimer that the manuscript does not claim an
  unconditional proof.

The sole printed target sentence “The Mandelbrot set is locally
connected” occurs in the generated ledger on page 145 immediately after
the status `MLC open`.  No unconditional MLC, UPTCR, or VAAPC-I promotion
was found.

Only the newly affected pages 84, 85, and 92 were rendered.  Their theorem
continuation, equations, references, open-problem statement, headers,
footers, and margins are legible and unclipped.  No bulk visual sweep was
performed.

The synchronized 145-page release has 5,756,582 bytes and SHA-256
`8FFD09351AE47464A09DF3DE2FEBB2FC37D0E647A05B48A4C7E5F8C8D1DEE2E6`.

## 2026-07-25 -- Resolved-intermediate full-boundary no-go and relative ideal descent

The proposed next step after the Kahn component-alignment pass was a full
factorwise ideal-boundary realization
\[
 \overline q_a:\overline{\mathcal E}_a\longrightarrow
 \overline{\mathcal R}_a,\qquad
 \overline e_a:\overline{\mathcal R}_a\longrightarrow
 \overline{\widetilde A}_{t,j_\iota(a)}.
\]
The source and deck-action audit proves that this proposal is impossible
when \(q_a\) is a nontrivial universal cover.  The result is recorded in
`resolved_intermediate_relative_ideal_boundary.md` and promoted only as
`RESOLVED_INTERMEDIATE_RELATIVE_IDEAL_BOUNDARY`.

### Source locks and source scope

The proof and validator use the following locked source files:

- Kahn I, `.tmp_kl06_source/wad.tex`, SHA-256
  `B5DF40A5D33B6B590B430D47693514088AF6FC287BAA5D87B4D11015B990E580`.
  Lines 169--175 define the covering ideal bordification by deleting the
  deck limit set:
  \(\widehat S=\overline{\mathbb D}\setminus\Lambda\).
- Kahn I, `.tmp_kl06_source/psiql2.tex`, SHA-256
  `E4EFCCEC65D8C9C2BDFE2AF8203B3D4D63ECF992B40D302F56FBA78259547228`.
  This locks the degree-one annular/localization input; it does not
  supply a boundary extension.
- Kahn--Lyubich II, `.tmp_kl08_source/psiql.tex`, SHA-256
  `6CC9726461473812A5FBA93377F2DC0B088DB6CAC4B9DE90C7B2AE625DFB49AF`.
  Lines 231--253 identify the named \(\lambda,\xi,\eta\) boundary and
  state continuous extension of the actual composite pseudo-piece
  immersion, not of a resolved factor.
- Kahn--Lyubich II, `.tmp_kl08_source/moduli.tex`, SHA-256
  `CBDB9EF7D6AC94C33FDB0AB7167E19C39EB23D27373C266A296CF6031E0CAF7E`.
  Lines 389--392 give the strip model, deck translation
  \(z\mapsto z+1\), and the upper side covering the \(O\)-boundary.
- KKL, `.tmp_wave_audit/waves-with-Misha.tex`, SHA-256
  `AD4C774806D9902AA54FA31C56AD6146D8034946F19CC5E9CEC3C51A3F94FDD5`.
  Its ideal boundary is
  \((\partial\mathbb D\setminus\Lambda)/\Gamma\), and the checked covering
  extension is from an open dense domain-of-discontinuity subset, not
  the complete prime-end circle.

No finite-topology hypothesis, full factor extension, or whole-end
properness statement was imported beyond those exact source scopes.

### Exact algebraic and analytic theorem

Assume a typed holomorphic annular factorization
\[
 A_s\xrightarrow qP\xrightarrow eA_t,\qquad
 eq=\iota,\qquad \iota_*=\operatorname{id}_{\mathbb Z},
\]
with \(q\) a surjective connected covering and \(e\) an embedding.  With
\[
 G=\pi_1(P),\qquad H=q_*\pi_1(A_s),\qquad N=\ker e_*,
\]
the identity \(e_*q_*=\operatorname{id}_{\mathbb Z}\) gives
\[
 G=N\rtimes H.
\]
After the labelled target-tile pullback, all groups act in one fixed
based universal-cover action and
\[
 \mathcal E_a/H=A_s,\qquad
 \mathcal E_a/N=\mathcal R_a,\qquad
 \mathcal E_a/G=P.
\]
Thus \(q_a:\mathcal E_a\to\mathcal R_a\) is the universal cover with
deck group literally \(N\leq G\), and base change preserves every fiber:
\[
 q_a^{-1}(a,p,\widetilde t)\cong q^{-1}(p).
\]

For a nonconstant universal cover
\(\pi:\mathbb D\to R\), a deck-limit point
\(\zeta\in\Lambda(\Gamma)\), and a sequence
\(\gamma_nz_0\to\zeta\), hyperbolic isometry plus the bounded-distance
lemma gives
\[
 \gamma_nz\longrightarrow\zeta
 \quad\text{for every }z\in\mathbb D.
\]
Deck invariance gives \(\pi(\gamma_nz)=\pi(z)\).  A continuous
point-valued extension at \(\zeta\) into any Hausdorff completion that
retains distinct interior points would therefore make its boundary value
equal to \(\pi(z)\) for every \(z\), contradicting nonconstancy.  The
identical argument applies to every nonconstant \(\Gamma\)-invariant
composite.  This proves:

1. a nontrivial resolved universal cover has no full prime-end
   extension;
2. transport of the full source prime-end circle across \(q_a\) is
   available exactly when that cover is one-sheeted; extension of
   \(e_a\) still requires the composite boundary values independently;
   and
3. the strongest general positive statement is quotient descent on a
   supplied invariant set
   \(J\subset\Omega(\Gamma)=\partial\mathbb D\setminus\Lambda(\Gamma)\).

The relative theorem descends a supplied continuous invariant composite
to \((\mathbb D\cup J)/\Gamma\).  It does not prove that a KL marked
interval lies in \(J\), that an image is the physical \(O\)-side, that
impressions are singleton, that accesses remain injective, or that the
embedding is end-proper.

### Source-locked KL incompatibility and exact obstruction

For the finite-modulus annulus \(A_s\), the oriented source generator
\(h\in H\) is hyperbolic with wrapping fixed points
\(\zeta_-,\zeta_+\).  If \(N\ne1\), then \(G\) is non-elementary and
the nontrivial normal subgroup \(N\triangleleft G\) has a closed
\(G\)-invariant limit set.  Iterating any nonfixed point of
\(\Lambda(N)\) by \(h^{\pm n}\) proves
\[
 \zeta_-,\zeta_+\in\Lambda(N).
\]
KL's strip and named-boundary constructions identify actual-tile ends
\(\omega_-,\omega_+\) with the infinitely wrapping \(\lambda/J\)
vertices, and KL's actual inclusion-induced tile map \(L_a\) extends
continuously there.  The domains must be kept distinct: the based cover
biholomorphism
\(\Phi_a:\widetilde A_{s,a}\to\mathcal E_a\) extends to the prime-end
fixed points with
\(\overline\Phi_a(\omega_\pm)=\zeta_\pm\), and the transported composite is
\[
 K_a:=L_a\Phi_a^{-1}=e_aq_a.
\]
If \(N\ne1\), then \(K_a\) would be a nonconstant \(N\)-invariant map
extending at two points of \(\Lambda(N)\), contradicting the theorem
above.  Therefore every whole-actual-KL-tile covering/embedding
factorization of this typed form is one-sheeted.

The abstract full-boundary failure certificate is
\[
 \mathfrak C_a=
 \bigl(
 a,\Gamma_a,\gamma,\zeta_+,\{\gamma^nz\}_{n\ge0},
 q_a(\gamma^nz)=q_a(z),\text{ full-prime-end extension}
 \bigr).
\]
For the actual KL tile the sharper incompatible tuple is
\[
 \bigl(
 N\ne1,\ \zeta_\pm\in\Lambda(N),\
 K_a=L_a\Phi_a^{-1}=e_aq_a,\
 K_a\text{ continuous at }\zeta_\pm
 \bigr).
\]
The first unsupported datum is the map-level identification of the
canonical infinite sheet-resolution cover with the covering leg of the
whole actual KL tile.  The abstract equalizer theorem and conditional
base-change theorem remain valid; their simultaneous application to the
whole KL tile is quarantined.

### Cross-validation correction, 2026-07-26

An independent domain audit found that the first draft of Theorem 8.3
had suppressed \(\Phi_a^{-1}\) and had used the same symbol for wrapping
points on two different source disks.  Equations (3.8)--(3.10) and
Lemma 8.2 of
`resolved_intermediate_relative_ideal_boundary.md` now make the
conjugacy and endpoint transport explicit.  The correction changes no
conclusion: the invariant map on \(\mathcal E_a\) is \(K_a\), not the
untransported \(L_a\).  The focused validator requires this typed
identity and the endpoint-transport equations.

### Adversarial corrections incorporated

Two independent source/skeptic audits required the following corrections
before promotion:

1. \(G\), \(H\), and \(N\) are typed in one based universal-cover
   action, so the deck group of \(q_a\) is literally \(N\), not merely
   an abstract isomorphic copy.
2. Holomorphic/Riemann-surface typing and the positive finite modulus
   \(K^m\Subset\mathbf U^m\) are explicit; the annular generator is
   therefore hyperbolic.
3. The no-extension proof establishes
   \(\gamma_nz\to\zeta\) for every \(z\), rather than asserting orbit
   constancy without the bounded-hyperbolic-distance argument.
4. KL's named wrapping points are not left as an open incidence issue:
   the strip model and \(\lambda/J\) description identify them with
   \(\zeta_\pm\), and this forces the one-sheet theorem.
5. Limit-set incidence is split into
   \[
   \chi_{\rm hit}
   =1_{\operatorname{inc}(I)\cap\Lambda\ne\varnothing}
   \quad\text{and}\quad
   \chi_{\rm edge}
   =1_{\overline{\operatorname{inc}(I)}\cap\Lambda\ne\varnothing}.
   \]
   A hit forbids point-valued descent on an included point.  An edge
   warning alone does not invalidate a complete relative boundary
   component whose omitted endpoints lie in \(\Lambda\).
6. The prior Kahn-alignment wording is restricted to a separately
   supplied annular \(q/e\) factorization; it no longer asserts that the
   canonical infinite cover is the whole actual KL tile.
7. Relative descent is not promoted to access injectivity, cyclic-order
   fidelity, end-properness, footprint realization, or final-root
   naturality.

### Immediate next gate and status

The immediate gate is the **canonical-resolution/KL-tile correspondence
audit**.  It must start from the exact canonical equalizer factorization
and the independently source-defined KL tile map, construct the actual
comparison square, and locate the first failure of the former
whole-tile identification.  The admissible outcomes to test are:

1. a proper interior or collar restriction;
2. a non-covering immersion comparison;
3. a different selected equalizer component; or
4. a retimed or localization-revised interface.

Only after this comparison map is typed may the project construct the
canonical relative boundary \(\Omega_a/\Gamma_a\), compare it with the
actual KL \(\lambda,\xi,\eta\) marking and target cluster data, and test
equivariance under final-root enlargement.

The authoritative ledger now has **321 obligations: 23 imported, 231
proved, and 67 open**.  `DIRECT_DECORATION_OUTER_CAP_FOOTPRINT`,
`VIRTUAL_WAVE_MARKED_CORRESPONDENCE`,
`VIRTUAL_WAVE_HORIZON_CERTIFICATE`, VAAPC-I,
`H2_RESPONSE_REALIZATION`, MBTT, H3, H4, UPTCR, and MLC all remain open.

## 2026-07-25 -- Canonical-resolution/whole-KL-tile correspondence no-go

### Question and exact answer

The preceding pass left one sharply typed question: could the canonical
infinite \(q/e\) resolution nevertheless be identified with the complete
actual KL tile through a map-level comparison square?

The answer is **no** for every end-compatible whole-tile comparison.  The
proof is
[`canonical_resolution_kl_tile_correspondence_no_go.md`](canonical_resolution_kl_tile_correspondence_no_go.md),
with machine checks in
`validate_canonical_resolution_kl_tile_correspondence_no_go.py`.

No new source theorem was imported.  The proof reuses the locked Kahn
limit-set convention and the locked KL universal-tile, strip,
infinite-wrapping, and continuous-composite statements.

### Minimal comparison data

Write the canonical resolved tile factorization as
\[
 \mathcal E\xrightarrow q\mathcal R\xrightarrow eT,\qquad
 L=eq,\qquad N=\operatorname{Deck}(q)\ne1.
\]
A forbidden whole-tile comparison consists of:

1. a based biholomorphic source universal-cover identification
   \(\Phi:\mathcal E\to\widehat A_s\);
2. conjugacy of the positive annular deck generators;
3. a target comparison \(B\) injective on \(L(\mathcal E)\);
4. the complete interior equality
   \[
    L_{\rm KL}\Phi=BL;
   \]
5. transport of one, hence both, annular wrapping fixed points to the
   corresponding named KL wrapping vertices.

No extension of either factor \(q\) or \(e\) is assumed.

### Derivation

Normality in the split tower \(G=N\rtimes H\), finite annular modulus,
and non-elementarity put the two wrapping points
\(\zeta_\pm\) in \(\Lambda(N)\).  Choose
\(\gamma_n\in N\) with
\[
 \gamma_nz\longrightarrow\zeta_+
 \quad\text{for every }z\in\mathcal E.
\]
Deck invariance gives \(L(\gamma_nz)=L(z)\).  The comparison square,
end compatibility, and KL continuity then give
\[
 \overline L_{\rm KL}(\omega_+)
 =
 \lim_n L_{\rm KL}(\Phi(\gamma_nz))
 =
 BL(z)
\]
for every \(z\).  Since \(L\) is nonconstant and \(B\) separates its
image, this is impossible.

The ordinary primitive canonical fiber is infinite, so its tilewise
universal-cover deck group is nontrivial.  This proves
`CANONICAL_KL_WHOLE_TILE_CORRESPONDENCE_NO_GO`.

### Adversarial scope corrections

Two independent audits confirmed the proof and required the following
scope:

1. The annular generator \(h\in H\) is not a deck generator in \(N\).
   The proof uses normality to put the fixed points of \(h\) in
   \(\Lambda(N)\), then sequences from \(N\).
2. Generator conjugacy by an arbitrary homeomorphism does not imply end
   compatibility.  On a strip,
   \(u(x,y)=(x-1/y,y)\) commutes with \(x\mapsto x+1\) while reversing
   a wrapping sequence.  The theorem uses a biholomorphic based-cover
   identification and its conformal ideal extension.
3. Infinite sheet number alone is insufficient for an arbitrary
   nonregular cover.  The proof needs the already proved fact that the
   tilewise resolved map is a universal cover.
4. The result is not an injectivity theorem for the actual KL immersion.
   The exact map
   \[
    F(z)=e^{4(z-1)}:\mathbb D\to\mathbb D
   \]
   is a noninjective holomorphic immersion with continuous closed-disk
   values but is not a covering onto its image.
5. The result does not prove the independently defined same-seed class
   empty or nonempty.  It excludes only members carrying the forbidden
   whole-tile end-compatible comparison.
6. Proper collar/interior restrictions, non-covering relation-valued
   comparisons, retimed one-sheet stages, and revised localizations are
   not excluded.

The stale demand for full extensions of both resolved factors was removed
from the Kahn-alignment narrative and the open
`DIRECT_DECORATION_PSEUDO_PIECE_PATH_LIFT_EXHAUSTION` node.  Nontrivial
resolved covers permit only relative boundary work on the domain of
discontinuity.

### Immediate positive gate and status

The next task is the **canonical/KL restricted-interface construction**.
It must select one of the admissible replacement types, prove complete
Wave proof-use exhaustion or a universal defect-window charge, construct
the canonical-to-KL relative-boundary incidence and target cluster maps,
and prove component, proper-path, cyclic-order, and final-root
naturality.  If every admissible collar meets a recurrent canonical deck
orbit, the first such orbit is the required obstruction certificate.

The authoritative ledger now has **322 obligations: 23 imported, 232
proved, and 67 open**.  `DIRECT_DECORATION_OUTER_CAP_FOOTPRINT`,
`DIRECT_DECORATION_PSEUDO_PIECE_PATH_LIFT_EXHAUSTION`,
`VIRTUAL_WAVE_MARKED_CORRESPONDENCE`,
`VIRTUAL_WAVE_HORIZON_CERTIFICATE`, VAAPC-I,
`H2_RESPONSE_REALIZATION`, MBTT, H3, H4, UPTCR, and MLC all remain open.

## 2026-07-25 -- Relative-boundary/no-go integration and release audit

### Dependency reroute

The whole-tile no-go was propagated through every live direct-decoration
interface document.  The path-lift, all-depth-contact, and trace-collar
ledger nodes now require a source-locked restricted interior/collar,
relation-valued, retimed one-sheet, or revised-localization interface.
They may not substitute a factorwise-completed whole pseudo-piece.  The
path-lift node directly depends on
`CANONICAL_KL_WHOLE_TILE_CORRESPONDENCE_NO_GO`; no status was promoted.

The corresponding proof documents now make three points explicit:

1. the five-clause end-compatible whole-tile square is impossible for the
   nontrivial canonical kernel;
2. this does not prove that the actual KL immersion is injective; and
3. every footprint, properness, trace, and final-root claim is conditional
   on first constructing and exhausting an admissible replacement
   interface.

### Mechanical failures found and repaired

The release audit did not treat failed checks as cosmetic.  It found and
repaired:

1. three validators whose exact dependency or documentation markers still
   encoded the pre-no-go graph;
2. one ledger evidence anchor left behind when the path-lift section was
   renamed;
3. two undefined LaTeX uses of `\id`, replaced by
   `\operatorname{id}`; and
4. the ambiguous appended equation tags `10.53a--c`, replaced by the
   independent tags `10.54--10.56`.

The adversarial ledger was also corrected so its repair for a nontrivial
resolved cover asks for a restricted or revised canonical/KL interface,
not an unqualified comparison map.

### Final verification

The final source state passes:

- all **41** focused validators;
- `audit_proof.py`, with an acyclic ledger of
  \(322=23+232+67\);
- all transfer regressions;
- Python bytecode compilation; and
- a warning-free Tectonic/BibTeX LaTeX build.

Extracted PDF text confirms the ledger totals, the resolved-cover boundary
theorem, the whole-tile correspondence no-go, and the generated `MLC open`
entry.  The four occurrences of the sentence “the Mandelbrot set is
locally connected” occur only in two explicitly conditional theorems, the
proved conditional-implication ledger node, and the `MLC open` ledger
statement.  Only pages 92--94, which contain the new theorem and its scope
warnings, were rendered and visually inspected; no bulk visual sweep was
performed.

The synchronized manuscript has **149 pages**, **5,773,823 bytes**, and
SHA-256
`392646E58424B77FC3C64249ED990A1075FDCEE3A3DBF5CE3E3B8393296540A0`.

The immediate open task remains the **canonical/KL restricted-interface
construction** with complete Wave proof-use exhaustion or a universal
defect-window charge.  VAAPC-I, the Wave certificates, MBTT, UPTCR,
rigidity, and MLC remain open.

## 2026-07-26 -- Cross-validation repair and restricted-interface classification

### Backward audit before promotion

Two independent audits re-derived the resolved-cover and whole-tile
no-go proofs from the locked Kahn/KL source files.  They found one genuine
domain error in the already-promoted relative-boundary proof: its first
draft had written \(L_a=e_aq_a\), although \(L_a\) is defined on the
actual KL source tile and \(e_aq_a\) is defined on the resolved source
disk.  The corrected derivation is
\[
 \Phi_at_a=h\Phi_a,\qquad
 \overline\Phi_a(\omega_\pm)=\zeta_\pm,\qquad
 K_a:=L_a\Phi_a^{-1}=e_aq_a.
\]
Here \(\Phi_a\) is the based source-cover biholomorphism,
\(\omega_\pm\) are the actual-tile wrapping ends, and \(\zeta_\pm\) are
the resolved-source wrapping ends.  KL continuity for \(L_a\) at
\(\omega_\pm\) therefore transports to continuity of the
\(N\)-invariant \(K_a\) at \(\zeta_\pm\in\Lambda(N)\).  The deck-limit
contradiction and the one-sheet conclusion are unchanged.

The proof, manuscript, ledger statement, source ledger, dependency audit,
adversarial audit, README files, and LaTeX statement were all corrected
to retain this domain distinction.  This correction is substantive
traceability, not a theorem-status change.

### Restricted relation construction

For every supplied fixed labeled same-source canonical/KL datum, based
universal-cover uniqueness constructs
\[
 \mathcal R\mathop{\longleftarrow}^{q}\mathcal E
 \mathop{\longrightarrow}^{K}\widehat A_t^{\rm KL}.
\]
It is a span, not a map on \(\mathcal R\).  If \(N=\operatorname{Deck}(q)\)
is nontrivial, a descent \(K=\kappa q\) would make \(K\) a nonconstant
\(N\)-invariant map extending at the two wrapping points in
\(\Lambda(N)\), which is impossible.

For each target path, its fiber product with \(K_i\) is an étale space
over the parameter interval.  A corrected one-manifold argument proves
that each path component is the graph of exactly one maximal interior
restriction.  Taking the tagged disjoint union over all source labels
retains repeated labels \(i_1\ne i_2\) with \(j(i_1)=j(i_2)\), as well as
resolved traces, sheets, and deck phases.  No groupoid operations,
proper endpoints, or final-root functoriality are inferred.

### Boundary scope correction

KL extends the glued pseudo-piece immersion on its pseudo-piece ideal
boundary.  It does not supply a continuous extension of one universal
cover tile over its entire standalone prime-end circle.  The promoted
partial extension domain is therefore only
\[
 D_{\rm ext}=\{\zeta_-,\zeta_+\}.
\]
For every resolved point \(r\), the two transported KL values belong to
the closure of the orbit trace
\(\{K(\gamma z):\gamma\in N\}\).  No value on
\(\Lambda(N)\setminus D_{\rm ext}\) is asserted, and the displayed
uncompressed relation state is only a conservative candidate, not a
proved minimal or finite-state invariant.

### Two negative branch controls

For
\[
 A_s=\mathbb A(1,e^{\varepsilon/2})
 \hookrightarrow
 A_t=\mathbb A(1,e^\varepsilon),
\]
the full target crossing width is \(2\pi/\varepsilon\), while every
essential embedded source inner collar has width at least
\(4\pi/\varepsilon\).  Hence Kahn's annulus hypotheses alone do not
supply a universal **unscaled** additive collar/target crossing-width
charge.  This does not rule out a degree-calibrated or source-specific
response.

At an exact Kahn base change, the new fiber is canonically the old fiber.
Induction shows that selecting a later finite stage in the unchanged
equalizer tower cannot make an infinite factor one-sheeted.  A genuinely
new return or localization remains possible.  For revised covers, the
subgroup-reflection criterion is typed only after the lift condition
\(a_*(H_s)\le H_t\) is supplied.

### Promotion and next gate

Only `CANONICAL_KL_RESTRICTED_INTERFACE_CLASSIFICATION` is promoted.  The
ledger now has **323 obligations: 23 imported, 233 proved, and 67 open**.
The immediate open theorem is the **canonical/KL relation proper-end
response theorem**: realize the same-source relation at every complete
Wave stage, freeze the full proof-use path ledger, classify all
proper/end-proper/nonproper tagged components and actual
\(\lambda,\xi,\eta\) incidences, and prove complete exhaustion or a
uniform Value-observable response for every omitted component.  Actual
retained-collar cartesianity and Cartesian final-root no-birth remain
separate gates.  VAAPC-I, Wave certificates, MBTT, UPTCR, rigidity, and
MLC remain open.

## 2026-07-26 -- Geometric-trace proper-end cross-validation

### The proposed next theorem was not correctly typed

Three independent read-only audits cross-examined the restricted-interface
classification against the locked KKL definitions.  They found that the
proposed “classify every path component as proper, end-proper, or
nonproper” step conflated three different predicates:

1. a source path is proper when it has two source ideal endpoints;
2. an immersion is proper on a source ideal subset; and
3. an immersion is end-proper on a pulled multi-interval only when it is
   proper on every complete end-interval.

They also found a quantifier mismatch.  The existing étale fiber product
enumerates maximal lifts of one target **parametrization**.  KKL define
the restriction of a target path as every proper source path contained in
the **geometric inverse trace**.  These are not the same object.

### Fixed-map positive theorem

For one supplied full KL pseudo-piece inclusion immersion
\[
\iota:\mathbf Y_s\to\mathbf Y_t
\]
between conformal disks, with KL's continuous extension on the full ideal
closures, every maximal parametrized lift of a KKL proper target path has
two unique source ideal endpoints.  The proof constructs each end cluster
as a nested compact connected set, rules out source-interior clusters by
local inverse continuation and maximality, and uses the Jensen--Fatou
boundary-uniqueness argument to show that a connected boundary fiber of
the nonconstant bounded holomorphic map is a point.  Exact endpoint
naturality follows.

This promotes
`FULL_KL_PSEUDOPIECE_MAXIMAL_LIFT_PROPERNESS`.  An internal parameter end
may map to target interior, so the theorem proves path properness, not map
properness on an ideal interval.

### Exact exhaustion and multiplicity no-go

For the identity disk, choose a proper lollipop path whose trace contains
upper and lower routes between two interior vertices.  Its parametrized
pullback has only the chronological graph, while the lower route alone is
a second proper KKL restriction.  Thus parametrized lift enumeration is
strictly smaller than geometric-trace restriction.

The holomorphic immersion
\[
 C(z)=\frac{1+z}{1-z},
 \qquad
 K(z)=e^{-C(z)}
\]
gives a stronger multiplicity model.  For \(k\in\mathbb Z\),
\[
 u_k(t)=-\log t+2\pi ik,\qquad
 z_k(t)=\frac{u_k(t)-1}{u_k(t)+1}
\]
satisfies \(K(z_k(t))=t\), and both ends of \(z_k\) land on the source
ideal circle.  The second endpoint depends on \(k\), so one proper target
diameter has infinitely many proper source restrictions.

Disjoint logarithmic rectangles map biholomorphically to one target
sector and have aggregate raw **interior-crossing** width
\((2m+1)w_0\).  This last calculation is explicitly not a complete
KKL-marked WAD/Value counterexample.  It only proves that local univalence
and sheet labels do not supply a bounded raw sheetwise crossing response.

These results promote
`PARAMETRIZED_PULLBACK_KKL_EXHAUSTION_NO_GO` in that exact scope.  They are
not asserted to be actual quadratic counterexamples.

### Replacement invariant and dependency split

The corrected state retains the glued covering/immersion relation, the
complete proof-use family schema, the tagged end-compactified geometric
inverse-trace path space, three separate endpoint frames, all KKL
subordination and properness predicates, an actual WAD/Value response, and
independent geometric naturality data.

The former single gate was split acyclically:

1. `DIRECT_DECORATION_WAVE_PROOF_USE_LEDGER`;
2. `DIRECT_DECORATION_CANONICAL_KL_STAGE_ALIGNMENT`;
3. `DIRECT_DECORATION_RELATION_PROPER_PATH_END_INTERVAL_CLASSIFICATION`;
4. `DIRECT_DECORATION_CANONICAL_KL_RELATION_PROPER_END_RESPONSE`; and
5. `DIRECT_DECORATION_FINAL_ROOT_RELATION_NO_BIRTH`.

Nodes 4 and 5 are independent successors of node 3.  Physical
complement-access footprints remain downstream of node 4; response-weight
equivariance under enlargement, if needed, requires both nodes 4 and 5.

The authoritative ledger now has **330 obligations: 23 imported, 235
proved, and 72 open**.  The dedicated source/model/dependency validator
and the acyclic ledger audit pass.  MLC, UPTCR, VAAPC-I, both Wave nodes,
and every global compactness/rigidity gate remain open.

### Final validation and release

All 43 project validators pass in the post-edit state.  The slow exact
parabolic-resonance validator independently checks every order
\(q=2,\ldots,16\); every exact recurrence/iterate comparison passes and
the error stream is empty.  The complete hostile transfer-regression
suite passes, as do the source-locked geometric-trace validator, the
restricted-interface validator, the outer-footprint validator, the
path-lifted-collar validator, the localization-sheet validator, the
acyclic proof-ledger audit, and Python byte-compilation.

The LaTeX build is warning-free.  Extracted text confirms both new
propositions, the conditional status of every occurrence of the MLC
conclusion, the final `MLC open` ledger entry, and the
330/23/235/72 counts.  Only changed pages 96--99 were rendered and
inspected; they have no clipping, overlap, or malformed mathematics.  No
bulk PDF visual sweep was performed.  The 154-page release has 5,802,430
bytes and SHA-256
`44B480F8A08BCE842EBAD9996DAEEF0C481F1D47596645B474770A9F79597E3B`.

## 2026-07-26 -- Dense terminal obstruction and width-route replacement

### The proposed protected collar is impossible

The terminal access-survival equivalence converted the remaining collar
question into a precise prime-end avoidance condition.  Applying
Douady--Hubbard external dynamics to that condition produced a stronger
result than a failed construction attempt.

For a connected polynomial-like map with empty-interior filled continuum
\(K\), let \(T\subsetneq K\) be a nondegenerate compact connected
forward-invariant carrier.  If any open external prime-end arc had all
impressions in \(T\), impression covariance and exactness of the external
degree-\(d\) map would propagate that property to the whole prime-end
circle.  Prime-end impressions cover \(\partial K\), and
\(\operatorname{int}K=\varnothing\), so this would force \(K\subset T\),
a contradiction.

The local access-survival equivalence then shows that the prime-end closure
of \(K\setminus T\) fills the complete inner ideal boundary of the carrier
complement.  Deck translates of one obstacle lift also accumulate at both
deck-limit corners.  KKL's locally connected native primitive carrier is
proper because its leastness excludes the nondividing fixed point
\(\beta_F\).  Therefore the universal
`TERMINAL_DYNAMICAL_ACCESS_NONACCUMULATION` proposal is not merely open:
it is false already in a native KKL subcategory.

The non-locally-connected physical properness statement remains separate
and open.  Nothing in the no-go proof silently promotes KKL's brief
“lift by \(\pi\)” sentence to a physical fiber theorem.

### A proved replacement at the correct extremal-length type

The replacement uses KL's ordered submulticurves rather than a welded
collar.  A pushforward-metric argument was written for finite ordered
multicurves with length equal to the sum of component lengths.  If every
target curve contains pairwise parameter-disjoint images of the ordered
source components, then
\[
 \mathcal L(\mathcal H)\ge\mathcal L(\mathcal G),
 \qquad
 \mathcal W(\mathcal H)\le\mathcal W(\mathcal G).
\]
KL Lemma `lifts` now gives, with coefficient one,
\[
 \mathcal W(\mathcal H_Y(v,w))
 \le
 \mathcal W(\Gamma_Y(v,w))
 =
 \operatorname{Bd}_Y(v,w)^{-1}.
\]
The complete \((\gamma,\gamma',\gamma^*)\) relation is retained, so no
arbitrary choice of a lift or loss of multiplicity occurs.

### Crest-compatible source audit

The next attempted shortcut also failed exactly.  KKL's phrase “Wave over
\(I_{1\to0}\)” places the terminal side in the crest, not at a leaf end.
At the corresponding KL vertex \(v_i\), the half-accesses
\(\eta_i\) and \(\xi_{i+1}\) lie in adjacent tiles.  KL's one-tile
crossing family instead joins \(\xi_i\) to \(\eta_i\).  Moreover two
adjacent boundary arcs meeting at one vertex have zero extremal length
locally, so the tags alone provide no finite width control.

KL's skipping-over estimate is a viable conditional route only after a
binder-level theorem supplies distinct endpoint vertices \(v,w\), one
fixed separating piece \(Z\), a literal ordered restriction subcurve, and
a componentwise skip witness.  Under those hypotheses the exact chain is
\[
 \mathcal W(S_0)
 \le \mathcal W(\mathcal H)
 \le \mathcal W(\widehat{\mathcal H})
 \le \mathcal W(\mathcal T_{Y,Z}(v,w))
 \le \frac{2^{2m+q+2}}{\mu}.
\]
The first three comparisons have sharp coefficient one; the displayed KL
depth estimate is period/depth dependent and therefore is not yet the
universal UPTCR response.

### Native stationary branch: exact off-by-one repair

KKL's stationary-alignment source contains an undefined \(A_N\) at line
1605.  The actual construction stops at \(A_{N-1}\).  Applying the valid
nonbreaking-incidence statement at \(n=b\) and \(n=b+1\) was initially
recorded as proving that every occurrence in
\[
 A_{N-1}=A_{b+2}
\]
passes through \(K_0^b\) and \(K_0^{b+1}\) in KKL's
successive-pullback sense.  A later occurrence-level audit retracted that
promotion: line 1603 itself requires a two-sided retained-Wave
noncollision theorem not proved in the locked source.  What survives is
the conditional indexing theorem
`KKL_STATIONARY_OFF_BY_ONE_PASS_THROUGH_REDUCTION`;
`KKL_STATIONARY_TWO_PULLBACK_PASS_THROUGH` is open.

An independent hostile audit rejected a stronger first draft.  The source
continua still require explicit graph lifts into the single final
fiber-product surface \(U^{N-1}\); final-level incidence refinement,
distinctness, and order are not consequences of the two separate-level
statements.  Those missing steps are now
`KKL_STATIONARY_GRAPH_LIFT_AND_FINAL_REFINEMENT` and
`KKL_STATIONARY_NESTED_INCIDENCE_ORDER`.  After them come
`KKL_STATIONARY_FIXED_PAIR_PROPER_RESTRICTION` and
`TERMINAL_STATIONARY_RESTRICTION_KL_PUZZLE_SELECTOR`.

### Status boundary

This pass proves a no-go and a sharp local width transfer.  It does not
construct the required binder-complete physical endpoint/separator
certificate.  `VIRTUAL_WAVE_MARKED_CORRESPONDENCE`, VAAPC-I, UPTCR, MBTT,
rigidity, and MLC remain open.

## 2026-07-26 -- Filled-set graph closure and Wave-source reclassification

### Canonical graph naturality

The finite Kahn fiber-product tower was checked at the level of actual
filled sets.  For
\[
 I_m=i_0\circ\cdots\circ i_{m-1},
 \qquad
 P_m=f_0\circ\cdots\circ f_{m-1},
\]
the iterated immersion restricts to a homeomorphism
\[
 I_m|_{K^m}:K^m\longrightarrow K^0,
\]
and
\[
 P_m^{-1}(K^0)=K^m,
 \qquad
 P_m=F^m\circ I_m\quad\hbox{on }K^m.
\]
It follows that every connected base filled-set package has a unique
connected graph lift, and components of inverse images are transported
bijectively.  This proves `PQL_ITERATE_FILLED_GRAPH_NATURALITY`.

The notation in this historical entry is superseded by the corrected
\(Q_n=\phi_0^n(Q_0)\) formulation recorded in the 2026-07-27 Gate N2
entry below; no live theorem uses the undefined printed \(K_0^0\).
At the KKL stationary depth \(m=N-1=b+2\), the graph lifts of
\(K_0^b\) and \(K_0^{b+1}\) are not merely subsets of two unspecified
components: they are whole, distinct components of
\(\mathcal K^m=P_m^{-1}(\mathcal K)\), with respective images
\(F^2(K_0^0)\) and \(F(K_0^0)\).  This proves
`KKL_STATIONARY_FINAL_COMPONENT_REALIZATION`.  The former combined
ledger name `KKL_STATIONARY_GRAPH_LIFT_AND_FINAL_REFINEMENT` is retained
only in the preceding historical entry; the live graph theorem is proved,
while final occurrence refinement is the separate open node
`KKL_STATIONARY_FINAL_INCIDENCE_REFINEMENT`.

### Degree-two correction

Every selected inverse leg toward the central small Julia set is
univalent because its target avoids the critical value.  The remaining
itinerary crosses the unique critical point exactly once.  Therefore
\[
 \deg(P_m|\widehat K_b)
 =
 \deg(P_m|\widehat K_{b+1})
 =
 2,
\]
not one as printed in the v1 KKL stationary paragraph.  This proves
`KKL_STATIONARY_DEGREE_TWO_CORRECTION`.  If the required proper-path
lamination is constructed, the corrected pushforward chain is
\[
 \mathcal W(B)\le2\mathcal W(C)+4,
 \qquad
 \mathcal W(A_m)\le4\mathcal W(\mathcal RF)+4.
\]
No coefficient-one stationary estimate is used downstream.

### Exact remaining native Wave gaps

The graph theorem does not turn KKL's source-language phrase
“passes through” into one retained proper final restriction.  Splitting,
the subordinate/non-marked filter, prime-end landing, the
non-locally-connected rational-lamination model, measurable-lamination
assembly, and
\(\mathcal W(A_m)\le\mathcal W(B)\) remain
`KKL_STATIONARY_FINAL_PASS_THROUGH_PATH_EXTRACTION`.  Consequently
`KKL_PARABOLIC_WAVE_STATIONARY_PROOF_REPAIR` remains open.

An independent bounded-visits gap was also isolated.  The corrected
number of length-\(k\) multi-intervals meeting the critical limb is at
most \(6b+k-1\), so the repetition argument needs a strict pigeonhole
excess.  Even a repeated marked interval is not contradicted by the
global Perron--Frobenius inequality \(\lambda_F>1\) without a separate
interval-level strict-growth or no-periodicity theorem.  This is
`KKL_BOUNDED_VISITS_INTERVAL_GROWTH_REPAIR`.

Because these two independent repairs are open,
`KKL_PARABOLIC_WAVE_AMPLIFICATION` is now classified
**open/source-stated**, not imported as a project-certified theorem.  The
stronger final-incidence, nested-order, fixed-pair proper-restriction, and
physical KL-selector chain also remains open; whole distinct graph
components do not establish common-occurrence persistence or order.

### Status boundary

The authoritative audit reports:

```text
ledger: valid (390 obligations)
statuses: imported=25, proved=275, open=90
target: MLC [open]
```

VAAPC-I, UPTCR, MBTT, coercivity, rigidity, and MLC remain open.  This
pass closes a finite filled-set construction and corrects a source
coefficient; it does not prove the native Wave theorem or any global MLC
gate.

## 2026-07-26 -- Stationary occurrence audit and exact two-occurrence gate

### Retraction of the unconditional pass-through promotion

The off-by-one calculation itself is valid, but its earlier promotion was
too strong.  KKL line 1603 argues that two separator-side portions both
push to Waves and therefore the original leaf breaks.  Under KKL's
untagged set-valued action, two distinct retained restriction components
can have one identical covering image.  Thus the implication requires an
additional source-specific noncollision theorem.

The live status is now:

```text
KKL_STATIONARY_OFF_BY_ONE_PASS_THROUGH_REDUCTION    proved conditional
KKL_STATIONARY_TWO_PULLBACK_PASS_THROUGH            open
KKL_STATIONARY_TWO_SIDED_WAVE_NONCOLLISION          open
```

No undefined \(A_N\) is used.  Once noncollision is proved, the two
applications at \(n=b\) and \(n=b+1\) yield the source predicates on
\(A_{N-1}=A_{b+2}\).

### Raw multiplicity no-go

The explicit pair
\[
 U'=\mathbb D_{75},\quad U=\mathbb D_{5625},\quad
 f(z)=z^2,\quad
 i(z)=\frac{e^{(\pi/50)(z+1)}-1}{e^{\pi/25}-1},
\]
with \(K'=[-1,1]\), \(K=[0,1]\), has two distinct proper components of
one immersion inverse trace whose \(f\)-images are identical.  All disk,
properness, common-inverse, sheet, and path calculations were checked.
The common image joins the inner and outer ideal boundaries and therefore
is not a KKL Wave.  The complete acting outer marking is also not
established.  The proved node `PQL_RAW_UNTAGGED_PATH_IMAGE_COLLISION` is
therefore a precise multiplicity warning, not a counterexample to KKL's
exact Wave antecedent.

### Source-specific deck reduction

The \(K_0^s\) notation in the following historical paragraph is
superseded by the \(Q_s\) chain in the 2026-07-27 Gate N2 entry below.
It is retained only to document the chronology of the audit.

Every selected small-Julia pull \(K_0^s\to K_0^{s-1}\), \(s\ge1\),
has a conformal Jordan branch.  The next central map
\(K_0^0\to K_1\) has degree two, and deleting the two full continua
leaves a connected two-sheeted annular cover.  For actual simple proper
paths confined to this collar, equality of unparametrized images is
equivalent to the nontrivial deck transformation.

This does not prove the KKL noncollision theorem.  The source must still
construct marked separator accesses, realize and retain both portions,
confine their complete occurrences to the selected collar, and exclude
deck-related collar paths.  Coarse Hubbard-tree labels cannot discharge
the last step: both central parent routes lie in one component of
\(T\setminus K_1\).

### One retained chain and the first missing binder

The source definitions do prove
`KKL_STATIONARY_ONE_RETAINED_CHAIN`.  If
\(\alpha\in A_{n+1}\), \(N\)-unbreakability makes every successive
\(F_*^r\alpha\) a nonempty singleton path.  Since \(F_*\) is the
untagged set of covering images of retained restriction components, every
retained component at that stage has the same singleton image and at
least one exists.

This is strictly weaker than line 1603.  KKL never bind the two named
topological portions to two distinct coherent components of the complete
iterated immersion restriction.  Their itinerary proposition permits
adjacency and same-pulled-interval transitions instead of actual paths.
Their pulled-tree formula also exposes a real filter hazard: a new
attachment boundary can be absorbed into one coarse
\(\iota^*\mathcal I\)-interval and is discarded if the candidate path is
subordinate there.  The source does not give the attachment itinerary,
both endpoint intervals, or whole-path subordination needed to turn this
hazard into an actual counterexample.

At this historical checkpoint, the proposed next theorem was
`KKL_STATIONARY_TWO_OCCURRENCE_BINDER`.  It would have had to build both complete
restriction components first, project them through every stage, and audit
each endpoint, sheet, parent access, and filter decision before any deck
calculation.  The later post-freeze QA entry supersedes this as the active
native proof route.

### Status boundary

```text
ledger: valid (399 obligations)
statuses: imported=25, proved=277, open=97
target: MLC [open]
```

The graph-naturalness and degree corrections remain proved.  The native
stationary Wave proof, KKL amplification, VAAPC-I, UPTCR, MBTT, rigidity,
and MLC remain open.

## 2026-07-26 -- Segmented stationary occurrences and the quantitative-defect route

### Retraction of the full-path semantic binder

The exact common-parameter equalizer theorem is valid but was assigned
too much semantic force.  A KKL immersion restriction satisfies
\[
 \iota(|\gamma_r|)\subset |\beta_{r-1}|,
 \qquad
 \beta_r=f\gamma_r .
\]
The first inclusion can be strict.  Consequently there need not be a
reparameterization for which
\(\iota\gamma_r=\beta_{r-1}\) on all of \((0,1)\).  A complete
fiber-product trace retains only the nested portion of each earlier
path and can discard proper shoulders needed to audit endpoint landing,
marking survival, and the subordinate-path filter.

This is not merely a logical possibility.  For
\[
 X_0=A(\rho,1),\qquad X_1=A(\sqrt\rho,1),\qquad
 i(z)=z,\qquad f(z)=z^2,
\]
put
\[
 \beta(t)=\rho^{\,1-t},\qquad
 \gamma(t)=\rho^{(1-t)/2},\qquad
 a(t)=\frac{1+t}{2}.
\]
Then \(f\gamma=\beta\), \(i\gamma=\beta a\), and \(a((0,1))\) is a
strict terminal window.  Both \(\beta\) and \(\gamma\) are proper
annular crosscuts, whereas
\[
 \gamma a(t)=\rho^{(1-t)/4}\longrightarrow \rho^{1/4}
 \quad(t\downarrow0),
\]
and \(\rho^{1/4}\) is an interior point of \(X_1\).  Thus the earlier
coordinate of the synchronized terminal trace is not proper.  The
model is an exact unbranched degree-two holomorphic relation; it is a
semantic counterexample to the proposed *minimal invariant*, not a
counterexample to the KKL Hubbard-tree theorem.

`PQL_STRICT_SYNCHRONIZED_CHAIN_RECONSTRUCTION` is therefore retained as
a proved strict-equality special case.  It is not used as the actual
KKL occurrence binder.

### Proved segmented prefix-flag theorem

For full stage paths
\[
 \gamma_r:J_r\to X_1,\qquad \beta_r=f\gamma_r,
\]
the correct transition datum is an orientation-preserving occurrence
map
\[
 a_{r-1}:J_r\longrightarrow J_{r-1},
 \qquad
 \beta_{r-1}a_{r-1}=i\gamma_r .
\]
Writing \(a_{r\mid m}=a_r\circ\cdots\circ a_{m-1}\), the data determine
the unique prefix path
\[
 \Theta_m(t)=
 \bigl(
   \gamma_1a_{1\mid m}(t),\ldots,
   \gamma_{m-1}a_{m-1}(t),\gamma_m(t)
 \bigr)
\]
in the \(m\)-fold Kahn relation.  Direct substitution proves
\[
 f\gamma_ra_{r\mid m}
 =\beta_ra_{r\mid m}
 =i\gamma_{r+1}a_{r+1\mid m},
\]
so every adjacent coordinate satisfies the defining fiber-product
equation.  The projections obey
\[
 q_{m,r}\Theta_m=\gamma_ra_{r\mid m},\qquad
 i_{m-1}\Theta_m=\Theta_{m-1}a_{m-1},
\]
\[
 I_m\Theta_m=\beta_0a_{0\mid m},\qquad
 P_m\Theta_m=\beta_m.
\]
Conversely, a compatible prefix flag with full terminal projections
recovers every \(\gamma_r\) and \(a_{r-1}\).  The forward and converse
constructions are inverse modulo the permitted orientation-preserving
path reparameterizations.  This proves
`PQL_SEGMENTED_OCCURRENCE_RECONSTRUCTION`.

The theorem is finite and categorical.  It does not construct the two
line-1603 portions, prove their proper remote landing, retain them
through the fine/coarse markings, or show that their terminal outputs
are Waves.  Hence `KKL_STATIONARY_TWO_OCCURRENCE_BINDER` and
`KKL_STATIONARY_RETAINED_PORTION_REALIZATION` remain open.

### Finite collar theorem and its exact limitation

For each fixed finite Kahn horizon, the complete immersion is an
embedding on a neighborhood of the pulled filled set.  On the
complement of the pulled tree in such a neighborhood it is conformal,
and its collar extension preserves the induced prime-end accesses and
cyclic order.  A literal proof-used route portion contained in this
collar, with access survival and obstacle avoidance, therefore has a
proper unique lift.  This proves
`KKL_STATIONARY_FINITE_EMBEDDED_COLLAR_NATURALITY`.

Wave subordination does not imply this literal containment.  A slit-disk
route can have valid local lift germs at the selected central point
while the maximal continuations stop at earlier slit accesses.  The
missing continuation equation is that the maximal lift window equals
the whole named route window, followed by landing at the declared
remote ideal end.

If \(O_h^-\Subset O_h^+\) are nested Jordan neighborhoods inside the
finite embedding domain and
\[
 Q_h=I_h(O_h^+\setminus\overline{O_h^-}),\qquad
 \mu_h=\operatorname{mod}Q_h,
\]
then every measurably selected first-exit route overflows an annular
crosscut.  Ordered overflow gives the block-dependent estimate
\[
 \mathcal W(E_h)\le \mu_h^{-1}.
\]
This proves `KKL_STATIONARY_COLLAR_EXIT_OVERFLOW`.  Qualitative
embedded-neighborhood existence gives only \(\mu_h>0\), not a uniform
lower bound.

### Quantitative Stationary Defect Bound

The pointwise binder is stronger than the width induction needs.  Let
\(Y_m\) be the final stationary subwave.  The proposed weaker analytic
gate is a partition in KKL's native transverse width measure
\[
 Y_m=G\sqcup D\quad\text{modulo width zero},
\]
where the restricted transverse measure agrees with the proof-used
lamination widths, \(G\) has the actual segmented incidence and
measurable final route realization, and
\[
 \mathcal W(D)
 \le a_b\mathcal W(\mathcal U\setminus\mathcal T)
    +c_b\mathcal W(\mathcal RF)+c_b.
\]
The corrected degree-two estimate on \(G\), together with KKL's
telescoping bound, gives
\[
 \mathcal W(Y^{N\text{-nbr}})
 \le \mathcal W(Y^{\rm sh})
    +a_b\mathcal W(\mathcal U\setminus\mathcal T)
    +(c_b+4)\mathcal W(\mathcal RF)+C_b.
\]
For a \(k\)-controllable Wave \(A\), the source decomposition then gives
\[
 \mathcal W(A)
 \le \mathcal W(A^{N\text{-br}})
    +\mathcal W(A^{\rm sh})
    +a_b\mathcal W(\mathcal U\setminus\mathcal T)
    +c_b\mathcal W(\mathcal RF)+C_b(k+1).
\]

General curve-family modulus is used only subadditively.  The native
transverse measure is needed for complementary breakable/unbreakable
families and for the following disjoint strengthening.  Put
\[
 B=A^{N\text{-br}}\cup A^{\rm sh}.
\]
Partitioning off the remaining nonshort, \(N\)-unbreakable leaves
before applying the \(X,Y,Z_j\) estimates gives
\[
 \mathcal W(A)
 \le\mathcal W(B)
    +a_b\mathcal W(\mathcal U\setminus\mathcal T)
    +c_b\mathcal W(\mathcal RF)+C_b(k+1).
\]

The additive constant requires an absolute scale.  It is absorbable in
KKL's high-type near-degenerate regime, where
\(\mathcal W(\mathcal RF)\) is required large, or under the explicit
condition
\[
 \mathcal W(A)\ge
 C_{b,k,\lambda}\bigl(\mathcal W(\mathcal RF)+1\bigr).
\]
A relative \([k,\lambda]\)-wide hypothesis alone cannot absorb a fixed
constant when \(\mathcal W(\mathcal RF)\downarrow0\).

Under that scale condition, QSDB is sufficient, but the proof needs
more than a verbal ``short-or-terminal'' substitution.  Choose
\(\lambda<\lambda_3<1\), take \(\delta_3,\eta_3\) from KKL
`small breaking` at \(n=N\), \(k_0=12b\), and choose
\[
 \max\left\{\frac{\lambda}{\lambda_3},
             \frac1{1+\delta_3}\right\}<\theta<1.
\]
After splitting off the vertical terminal alternative and absorbing the
remaining charges, the disjoint estimate gives
\(\mathcal W(B)\ge\theta\mathcal W(A)\).
The source proves \(B^{N\text{-nbr}}\) is \(12b\)-controllable, so
`small breaking` applies to \(B\).  If \(B\) is terminal, its terminality
transfers to \(A\), because
\[
 \delta_A=
 \min\{\delta_3\theta,(1+\delta_3)\theta-1\}>0.
\]
If \(B\) is \((N,\lambda_3)\)-unbreakable, then
\(B^{N\text{-nbr}}\subset A^{\rm sh}\), whence
\[
 \mathcal W(A^{\rm sh})
 \ge\lambda_3\mathcal W(B)
 \ge\lambda_3\theta\mathcal W(A)
 >\lambda\mathcal W(A).
\]
This is strict KKL shortness.  It proves
`KKL_STATIONARY_QSDB_SUFFICIENCY` conditional on the strengthened
transverse-measure QSDB and absolute-scale hypothesis.  QSDB itself
remains open.

### Uniform-collar no-go and replacement conductance

The proposed linear collar estimate cannot be derived from qualitative
Kahn collar existence.  For \(0<a<1\) and \(1<R<2\), let
\[
 U_R=\mathbb D_R,\quad U'_R=\mathbb D_{\sqrt R},\quad
 K=\overline{\mathbb D},\quad T=[-a,a],\quad
 f_R(z)=z^2,\quad i_R(z)=z.
\]
This is an exact degree-two pseudo-polynomial-like map with globally
embedded immersion and forward-invariant full tree \(T\).  The vertical
width is uniformly bounded:
\[
 \mathcal W(U_R\setminus T)
 \le\operatorname{mod}(\mathbb D\setminus T)^{-1}.
\]
At horizon \(h\), however, \(U_R^h=\mathbb D_{R^{1/2^h}}\), and every
collar around \(K\) has
\[
 \operatorname{mod}Q_h
 \le\frac{\log R}{2\pi\,2^h},
 \qquad
 \frac1{\operatorname{mod}Q_h}
 \ge\frac{2\pi\,2^h}{\log R}\longrightarrow\infty.
\]
This proves `KAHN_QUALITATIVE_COLLAR_VERTICAL_CHARGE_NO_GO`.
The example is not a native periodically repelling primitive KKL block:
\(z^2\) is superattracting and \(T\) is not asserted to be the native
Hubbard tree.  It refutes source derivability, not the intended native
theorem.

The corrected open gate is intrinsic.  Either prove a linear bound for
the optimized prefix-compatible collar conductance
\[
 \mathfrak C_{\le b+2}^{\rm comp}(F)
 \le C_b\bigl(\mathcal W(\mathcal U\setminus\mathcal T)+1\bigr)
\]
with measurable source first-exit selection, or prove directly the
weaker route-localized estimate
\[
 \sum_{h=1}^{b+2}\mathfrak E_h(F)
 \le C_b\bigl(\mathcal W(\mathcal U\setminus\mathcal T)+1\bigr),
\]
where \(\mathfrak E_h\) is the width of the fully marked selected
first-failure continuation family.  The latter ignores thin collar
geometry never visited by a proof-used route and builds measurability
into the invariant.

Eight new finite diagnostics check the strict shortness slack, admissible
terminal constant, failure of relative-width absorption, the
\(\theta\)-transfer inequalities, the disjoint-\(B\) survivor inclusion,
the exact \(2^h\) collar formula, degeneration of qualitative collars,
and the strict containment of annular crossings in the full continuation
failure class.  They are diagnostic only and promote no analytic claim.

### Status boundary

```text
ledger: valid (407 obligations)
statuses: imported=25, proved=283, open=99
target: MLC [open]
```

The new progress is a corrected exact occurrence invariant, a finite
analytic collar theorem, a proved block-dependent exit estimate, a
source-derivability no-go, and a strictly weaker sufficient width target.
The optimized collar/route calibration,
the full QSDB partition and charges, the native stationary Wave repair,
KKL amplification, VAAPC-I, UPTCR, MBTT, rigidity, and MLC remain open.

### Verified manuscript release

The generated ledger, complete transfer regressions, eight new
quantitative-defect diagnostics, and atomic KKL source manifest all pass.
The 176-page LaTeX manuscript builds with no TeX, BibTeX, box, citation,
or reference warnings.  Extracted text confirms the
407/25/283/99 status, conditional QSDB theorem, proved qualitative-collar
no-go, open uniform native charge, and unconditional-MLC disclaimer.
Only changed pages 104--107 were rendered, with final visual inspection
focused on pages 105 and 107; no bulk PDF visual sweep was performed.

The build and exported manuscript are byte-identical:

```text
bytes: 5,895,666
sha256: 07F567C1384D29C48D82DAB527A12D95807B335E2F404C31A275FD0779E00458
```

## 2026-07-26 — stationary survivor/fixed-end source reduction

### Objective

The pass asked whether the stationary route-exit residual could be
turned into a source-native finite response family, rather than merely
audited again.  The answer is partly positive:

- the residual is reduced to one exact ambient-survivor family;
- every survivor has a pointwise marked route-switch certificate;
- KKL's fixed-end immersion theorem gives a valid, coefficient-preserving
  full/other-end WAD split on supplied eligible ends; and
- an actual proper vertical packet has an explicit finite-horizon
  width charge.

The answer is not yet a stationary repair.  The measurable marked
packet, uniform multiplicity, and the critical-end \(BL_0\) response
remain open.

### Byte-locked sources

```text
.tmp_wave_audit/waves-with-Misha.tex
SHA-256 AD4C774806D9902AA54FA31C56AD6146D8034946F19CC5E9CEC3C51A3F94FDD5

.tmp_wave_audit/not-all-good2.tex
SHA-256 B5D40812E40D2E44037A8FC249DB687211CD67275E66EFFF8E7F29BC7CEDFB01

.tmp_kl06_source/wad.tex
SHA-256 B5DF40A5D33B6B590B430D47693514088AF6FC287BAA5D87B4D11015B990E580

.tmp_kl06_source/psiql2.tex
SHA-256 E4EFCCEC65D8C9C2BDFE2AF8203B3D4D63ECF992B40D302F56FBA78259547228

.tmp_kl06_source/appendix.tex
SHA-256 EA2BE5CC544100D7931C9992E7ED476EBBE4CCE52FAF620BFF357071CB3916F3
```

The relevant master-source ranges are 1355--1392 for
breakability/\(B_A\), 1423--1494 for actual breaking response,
1547--1622 for the stationary alignment, 2065--2097 for
pushforward/restriction/filter calculus, and 2128--2178 for
\(F_*\), Wave pushforward, breaking, and Shift.  The fixed-end theorem
is `not-all-good2.tex` 514--545.  The extremal-width overflow and
parallel/series laws are `appendix.tex` 12--68.

### 1. Horizon repair

The source uses two different depths:

\[
H=N=b+3,\qquad m=N-1=b+2.
\]

Ambient breakability and short-family absorption are tested through
\(N\).  Named route pullbacks are indexed only by \(1\le h\le m\).
For the covering \(P_h\), the safe degree is \(D_h\le2^h\), so

\[
\sum_{h=1}^{m}D_h
\le2^{m+1}-2
=2^{b+3}-2.
\]

This correction is structural: using \(m\) in the ambient partition
could misclassify a last-stage break as a new survivor; using \(N\) in
the route sum would add a route level that was never constructed.

### 2. Exact survivor partition

After a complete single-valued first-exit selector is supplied, define

\[
\begin{aligned}
E_A^{\rm br}&=E_A\cap A^{N\text{-br}},\\
E_A^{\rm sh}&=E_A\cap A^{N\text{-nbr}}\cap A^{\rm sh},\\
E_A^{\rm surv}&=E_A\cap A^{N\text{-nbr}}\setminus A^{\rm sh}.
\end{aligned}
\]

These families are disjoint and exhaustive.  The first two lie in
\(B_A=A^{N\text{-br}}\cup A^{\rm sh}\), so they are not new defect
mass.  Only \(E_A^{\rm surv}\) remains.  This family is ambient
unbreakable by definition, which blocks the attempted reuse of KKL's
one-step breaking response.

The selector hypotheses are substantive.  A valid construction must
choose no more than one record per physical target leaf, use a standard
Borel occurrence space, preserve the native transverse measure, and
retain complete stage paths only before the first continuation failure.
At the failure stage it stores a maximal partial lift and endpoint;
a full path may be stored there only when the failure occurs after
path construction in a marking or filter predicate.

### 3. Pointwise route switch

For an ambient singleton transition
\(F_*\delta_j=\{\delta_{j+1}\}\), define the retained predecessor fiber

\[
\operatorname{Ret}_j(\delta_j,\delta_{j+1})
=\{\gamma\in\iota_j^*\delta_j:
 \gamma\text{ survives the native filters and }
 f_{j*}\gamma=\delta_{j+1}\}.
\]

The definition of \(F_*=f_*\iota^*\) proves this fiber is nonempty.
At the first named failure, either:

1. the named occurrence is not retained and another full retained path
   is a strict replacement; or
2. the geometric path remains retained but its access, sheet,
   obstacle, occurrence, complete-portion, localization, monodromy,
   cover, filter, or future-compatibility state fails.

Pointwise finite choice gives a retained predecessor flag through the
remaining stages.  The simple-path containment lemma identifies the
corresponding occurrence windows, producing a segmented alternative
chain.  It is not a single deepest fiber-product path and it does not
prove Borel selection, bounded multiplicity, ideal landing, or width
control.

A sufficient survivor-exclusion theorem would show that every named
occurrence is itself a full retained witness realizing every frozen
predicate.  That marked-witness completeness statement remains open.

### 4. Fixed-end WAD split

KKL's `thm:immer-decomp` starts with a finite-topology immersion, a set
of source ends on which it is proper of degree one, and a valid target
WAD whose arcs meet the images of those ends.  Its lifted realizing
foliation gives valid paired pieces

\[
Y=Y_{\rm full}+Y_{\rm exit},\qquad
Y'\ge Z'_{\rm full}+Z'_{\rm exit},
\]

with

\[
\|Y_{\rm full}\|=\|Z'_{\rm full}\|,
\qquad
\|Y_{\rm exit}\|=\|Z'_{\rm exit}\|.
\]

The equalities are coefficient-norm equalities for the paired
foliation subdivision.  They neither assert
\(\|Y'\|=\|Y\|\) nor identify arbitrary marked extremal widths.
On an ambient survivor, almost every other-end lifted leaf has a
nonempty retained-successor fiber.  This yields a witness-relative,
relation-valued switch, not a canonical replacement WAD.

If a finite eligible-end relation has already been proved Borel and
fiberwise nonempty, an ordering gives a Borel least-end selector and a
finite leaf partition.  This is only the last selection step.  Finite
topology does not construct the eligibility relation or bound marked
accesses, occurrence windows, or retained fibers uniformly over
stationary blocks.

### 5. Why the two line-1603 portions are still open

Line 1600 gives one existential restriction reaching a marked deep
\(L_0^h\)-continuum.  It does not construct a Freudenthal source end
representing that access.  Under
\(\mathrm{TWO}_h\wedge\mathrm{INC}_h\), the unsplit physical inner
Freudenthal end is additionally nonproper; unconditionally the first
failure is the access/end type mismatch.  The original \(BL_0\) and
remote starts therefore require a genuinely typed construction.

The complete two-orientation dependency is

\[
C_h^-\wedge X_h^-\wedge C_h^+\wedge X_h^+
\wedge P_h\wedge M_h.
\]

- \(C_h^-\): original \(BL_0\) source end, proper degree one, with a
  measurable access partition;
- \(X_h^-\): its maximal lift exits at the declared \(L_0^h\)
  occurrence;
- \(C_h^+\): corresponding proper-degree-one certification for every
  proof-used remote source end;
- \(X_h^+\): the reverse maximal lift exits at the same \(L_0^h\)
  occurrence;
- \(P_h\): same target leaf, transverse parameter, window, sheet,
  access, and occurrence coupling;
- \(M_h\): both source paths survive the fine/coarse filters and have
  the asserted Wave covering images.

Neither line 1600 nor the fixed-end WAD theorem supplies these clauses.

### 6. Conditional vertical charge

For a survivor sublamination with a Borel single-valued, injective
modulo-zero selection of full proper source paths joining the
pulled-tree and outer ideal boundaries, with native marking survival
and ideal-end degree at most \(D_h\), domination and KKL's
pushforward-lamination estimate give

\[
\mathcal W(\mathscr S_h^{\rm ver})
\le D_h(V(F)+2)
\le2^h(V(F)+2).
\]

Summation through \(m=b+2\) gives

\[
\sum_{h=1}^{b+2}\mathcal W(\mathscr S_h^{\rm ver})
\le(2^{b+4}-4)(V(F)+1).
\]

The arithmetic was hostile-checked.  Packet construction,
measurability, endpoint extension/degree, and filter survival remain
hypotheses; no source clause turns all survivor exits into such
packets.

For one packet with the exact final stationary small-Julia incidence,
the analogous conditional estimate is

\[
\mathcal W(\mathscr S_h^{\rm ren})
\le2^{h+1}(R(F)+1).
\]

Uniform summation additionally needs a packet-count bound \(q_b\), and
there is no locked comparison \(R(F)\le C_b(V(F)+1)\).

### 7. First uncontrolled output and next theorem

After measurable route selection and all easy absorptions, the first
uncontrolled output is an excess tree-side survivor whose retained
pushforward is a Wave ending at \(BL_0\).  It is not a vertical packet,
need not have the exact final small-Julia incidence, and is not covered
by the independent bounded/Shift alternatives.  Invoking the
critical-limb proposition would be circular because its proof uses the
disputed stationary alignment.

The immediate analytic target is therefore the marked fixed-end
survivor partition and response theorem:

1. construct a native measurable target partition by eligible
   proper-degree-one end and complete occurrence;
2. transport all access, sheet, window, marking, and filter data through
   the fixed-end WAD witness;
3. construct a Borel retained-predecessor packet with uniformly bounded
   or summably charged multiplicity;
4. classify every survivor as vertical, exact small-Julia incident,
   independently bounded, independently responsive, or an explicit
   retained residual; and
5. resolve the \(BL_0\) residual without using line 1603.

Finite route codes do not finish item 3: raw paths and occurrence
windows remain noncompressed Borel witness data.  A uniform finite
response theorem requires a separate width-faithful quotient with an
alphabet bounded in terms of \(b\).

### Status boundary

This pass proves reductions and conditional source estimates, not the
native marked packet theorem.  The separate machine-ledger integration
at that checkpoint recorded 414 obligations: 26 imported, 287 proved,
and 101 open.
`KKL_PARABOLIC_WAVE_STATIONARY_PROOF_REPAIR`,
`VIRTUAL_WAVE_MARKED_CORRESPONDENCE`,
`VIRTUAL_WAVE_HORIZON_CERTIFICATE`, VAAPC-I, UPTCR, MBTT, coercive
compactness, rigidity, and MLC remain open.

## 2026-07-26 — access-local continuation and paired-Wave response

Three source-checkable proof documents were completed and independently
hostile-audited:

- `kkl_stationary_fixed_end_topological_obstruction.md`;
- `kkl_access_seeded_maximal_lift_measurability.md`; and
- `kkl_stationary_bl0_survivor_analysis.md`.

The first corrects the prior unconditional impropriety wording.  The
locked theorem/access mismatch is unconditional; two-end topology,
inner-end nonproperness, and outer-end vertical classification are
conditional on their displayed physical and applicability hypotheses.

The second proves the abstract continuous-product continuation theorem:
the joint maximal-lift domain is open, the lift is continuous, exit time
is lower semicontinuous, and landing/first-failure data are Borel in a
supplied compact metric ideal model.  It does not infer continuous
flow boxes from a merely Borel KL06 lamination, and it does not prove
seed-side properness or a source WAD.

The third proves, for exact full-width untrimmed occurrence families,

\[
\mathcal W(S)\le\bigoplus_i\mathcal W(B^i),
\]

and, conditional on actual source Waves, whole-ending-set degrees, and
one common Wave-pushforward constant,

\[
\max_i\mathcal W(C^i)\ge r\mathcal W(S)-C_b.
\]

The \(r=2\) case supplies the desired packet-local factor two even
under certified common-output collision.  The entire native residual
is not yet paired, the hidden constant is not fully source-audited,
and packet response is not yet ambient terminality.

At this pre-QA checkpoint the machine ledger contained 423 obligations: 28 imported,
291 proved, and 104 open.  The immediate open chain is
`KKL_WAVE_PUSHFORWARD_UNIFORM_PACKET_CONSTANT`,
`KKL_STATIONARY_TYPED_PAIRED_WAVE_REALIZATION`, and
`KKL_STATIONARY_BL0_UNIFORM_SURVIVOR_RESPONSE`.  The post-freeze QA entry
below supersedes that chain as the active native route.  All global gates
remain open.
## 2026-07-26 — post-freeze mathematical QA reconciliation

The QA pass froze proof construction and independently audited source
custody/dependencies, the native KKL stationary proof, and all new
extremal-width/Wave arguments.

Accepted corrections:

- retracted `kkl_wave_local_end_collision_reduction.md`;
- recorded the cyclic-cover counterexample to the literal broad KKL
  coefficient-one Wave claim;
- retained the Dudko--Lyubich annular theorem only in its native
  one-common-boundary-interval scope;
- split the active native stationary repair into four gates:
  relative continuation, pointwise two-path break, final fixed-component
  exit, and typed bounded-degree pushforward;
- narrowed the proved degree-two node to continuum degree only;
- moved the paired-response chain out of the active native dependency;
- rendered formal hypotheses separately from proof dependencies in the
  generated ledger; and
- added a clause-map promotion guard and focused adversarial tooling
  regressions.

No global status was promoted.  The post-QA ledger is
430 total / 30 imported / 292 proved / 108 open.  MLC, UPTCR,
VAAPC-I, MBTT, coercivity, rigidity, and the native stationary repair
remain open.

The immediate proof-development target after this QA stop is Gate N1,
`KKL_STATIONARY_RELATIVE_WAVE_CONTINUATION`.  It is prior to the
line-1603 alignment sentence because the printed preliminary telescope
is not established.  Any attempted proof must either certify coherent
single-coordinate source Waves or carry a multiplicity-aware linear
conductance state.

## 2026-07-26 — Gate N1 stationary relative continuation

Gate N1 was pursued in isolation and is now proved.  The frozen main
proof is `kkl_stationary_relative_wave_continuation.md`, SHA-256
`ADFC7BCD5A73CE7E7ABE12C11C3E2C4D778826B995BF9114C6F8B431EF38094F`.

The pass produced two substantive constructions:

1. a standard-Borel ordered-Wave realization with a filtered
   occurrence code, complete prime-end markings, singleton target
   direction, common whole-component Wave typing, and full source
   saturation; and
2. a Borel width envelope that contains an arbitrary bounded-width
   non-Borel discard in a Borel superfamily with arbitrarily small
   width overhead.

Before the native DL theorem is invoked, round-annulus total variation
gives a Borel rectifiable-core/zero-width-nonrectifiable decomposition
of every KKL packet.  This prevents an unstated rectifiability
assumption.

The final source audit also found and rejected one attractive but
unsupported shortcut.  Exact width additivity on disjoint measurable
supports is proved, but the frozen Feigen phrase “genuine subwave”
does not explicitly source-lock measurability of the retained support.
The Gate-N1 proof instead uses the original DL proof-internal deletion:
\(T=O(\log m)\) nonzero span packets of \(O(1)\) width plus one final
\(O(1)\) outer buffer.  The Parallel Law gives the required relative
discard bound directly, absolute at \(m=2\).

Full source saturation and sequential degree-two relative transfer
then give

\[
 \mathcal W(A_n\setminus A_{n+1})
 \le 2^n c_b^{\rm step}
 \le 2^{b+1}c_b^{\rm step},
\]

and hence the uniform \(C_b\) required by Gate N1.

The post-promotion ledger contains 437 obligations: 31 imported, 299
proved, and 107 open.  Gates N2--N4, the complete native stationary
repair, VAAPC-I, UPTCR, MBTT, coercivity, rigidity, and MLC remain open.

## 2026-07-27 — Gate N2 selected-predecessor frontier

The N2 pass stayed on the line-1598 selected-predecessor slice.  It
constructed the unique critical-limb inverse branch, the finite
\(H=b+2\) component and fixed-point chains, and the corrected
small-Julia chain
\[
 Q_n=\phi_0^n(Q_0),\qquad Q_n\subset L_0^n.
\]
This replaces, without silently identifying, the undefined printed
\(K_0^0\).

The hostile review found and removed an unjustified local-germ
argument.  The replacement compares the two same-image preimages in
the critical and \(q-1\) limbs and uses local injectivity at
\(\alpha_F\).  It proves the stronger, non-LC statement
\[
 \overline{\Omega_n}=\Omega_n\cup\{\alpha^n\},
 \qquad
 \Omega_n\in\pi_0(K(F)\setminus\{\alpha^n\}).
\]

In the locally connected physical category, dendrite geometry and
finite-tree pruning now prove actual marked incidence and hence the
line-1598 disjointness at \(h=b,b+1,b+2\) when \(q>b\).  The same
incidence is proved in KKL's locally connected combinatorial model.

For the non-locally-connected case, a new monotone full-lift criterion
is proved.  A monotone semiconjugacy with correctly labelled
predecessors and a singleton fixed fiber automatically has singleton
selected predecessor fibers.  With
\(T=\pi^{-1}(T_{\rm com})\), selected-sheet correspondence, and
\(\pi(K_i)\subset\bar K_i\) for the corresponding geometric model
small-Julia continua, one obtains
\[
 \pi^{-1}(L_{0,\rm com}^n)=L_0^n
\]
and model whole-continuum incidence forces \(K_i\subset L_0^n\).

The subsequent primary-source red team found a genuine quotient-level
typing error in the first formulation: the canonical monotone model
cannot satisfy \(\pi(K_i)=\{\bar v_i\}\), because it is injective on
finite-orbit points while a nondegenerate periodic \(K_i\) contains
distinct periodic points.  KKL's \(\bar v_i\) is the vertex of a
second, finite-tree quotient; it is not a point of the geometric
rational-lamination model.  The manuscript, ledger, and failure
certificate were retyped to the two-level continuum formulation.

The source audit does not promote that package.  Kiwi's Theorem 2,
Proposition 4.2, and the factorization
\(h=\widehat w^{-1}\circ q\) in the proof of Theorem 5.12 supply
singleton complete fibers at periodic and preperiodic points for the
transported Kiwi model.  KKL 542--543 and Dudko--Lyubich 956--978 do
not construct a marked dynamical homeomorphism of target models
intertwining their projections, or prove the full-carrier lift and
exact selected-sheet/marked-continuum correspondence.  The global
non-LC selected full-preimage and geometric continuum lift remains
open.

The accepted audit is
`kkl_stationary_n2_frontier_audit_20260727.md`.  The machine ledger
contains 465 obligations: 34 imported, 316 proved, and 115 open.
`KKL_STATIONARY_SELECTED_SEPARATOR_REALIZATION`, proof-used occurrence
binding, the line-1600 incoming host, line-1603 noncollision, Gate N2,
VAAPC-I, UPTCR, and MLC remain open.

# Corridor-network calibration

## 1. Purpose and status

This note carries the marked collar problem into the weighted-arc-diagram category.
It proves:

1. an abstract width sandwich for a surface whose long corridor arcs are genuinely
   realized by KKL translation markings;
2. a relative-error corollary;
3. a no-go theorem for replacing harmonic series laws by fixed positive matrices
   without balance or bottleneck data.

The missing dynamical theorem is to realize this decomposition for every virtual block
and charge the raw marking-complexity term.

## 2. Source-locked estimates

The following statements are imported from KKL26 with their original hypotheses.

### Thick–thin estimate

For a hyperbolic Riemann surface \(\mathcal V\) with ideal marking \(\mathcal I\),
KKL Theorem `main estimate` gives a universal constant \(C_{\rm TT}\) such that
\[
  W(\mathcal V,\mathcal I)
  -C_{\rm TT}\bigl(|\chi(\mathcal V)|+|\mathcal I|\bigr)
  \le 2\|X_{\rm can}\|
  \le W(\mathcal V,\mathcal I).
\tag{2.1}
\]

### Translation-tail estimate

For an \((n,p)\)-translation marking with
\[
  N=2(n+1)p,
\]
KKL Theorem `thm:bounded short` proves the exact estimate
\[
  \|X^{\rm long}\|
  \le 2W_{\rm std}+6N.
\tag{2.2}
\]

### Pullback warning

KKL Proposition `prop:itineraries` shows that restriction by an immersion can split a
path into an itinerary through intervals on which the immersion is improper. Lemma
`lem:domination` combines widths of serial restrictions by the harmonic sum
\[
  x_1\oplus\cdots\oplus x_m
  =
  \left(\sum_{j=1}^m x_j^{-1}\right)^{-1}.
\tag{2.3}
\]
Thus a linear transition matrix is not part of the source theorem.

## 3. Translation-realized corridor data

### Definition 3.1

A **translation-realized corridor decomposition** of
\((\mathcal V,\mathcal I)\) consists of a partition of its canonical WAD
\[
  X_{\rm can}
  =
  X^{\rm core}
  +
  \sum_{a=1}^r X_a^{\rm short}
  +
  \sum_{a=1}^r X_a^{\rm long}
\tag{3.1}
\]
such that:

1. the summands have disjoint arc support;
2. the short summands are partitioned into declared interaction types modulo the
   corridor translation actions;
3. for each \(a\), \(X_a^{\rm long}\) is the restriction of, or is dominated by, the
   long canonical WAD of an actual KKL translation marking with standard width \(S_a\)
   and marking cardinality \(N_a\);
4. every access label used by a later pullback is retained.

Define
\[
  Q=
  2\left(
    \|X^{\rm core}\|
    +
    \sum_a\|X_a^{\rm short}\|
  \right),
\qquad
  S=\sum_a S_a,
\tag{3.2}
\]
and
\[
  \kappa=
  |\chi(\mathcal V)|+|\mathcal I|+\sum_aN_a.
\tag{3.3}
\]

The adjective “translation-realized” is essential. A topological corridor that has not
been placed in the KKL marking category does not satisfy (2.2) by definition.

## 4. Corridor sandwich

### Theorem 4.1 (WAD corridor sandwich)

There is a universal \(C_{\rm net}\) such that every translation-realized corridor
decomposition satisfies
\[
  Q
  \le
  W(\mathcal V,\mathcal I)
  \le
  Q+4S+C_{\rm net}\kappa.
\tag{4.1}
\]

**Proof.** Since the WAD split (3.1) is a partition by support,
\[
  2\|X_{\rm can}\|
  =
  Q+2\sum_a\|X_a^{\rm long}\|.
\]
The right inequality in (2.1) gives
\[
  Q\le2\|X_{\rm can}\|\le W(\mathcal V,\mathcal I).
\]
Applying (2.2) to every realized corridor gives
\[
  2\sum_a\|X_a^{\rm long}\|
  \le4\sum_aS_a+12\sum_aN_a
  =4S+12\sum_aN_a.
\]
The left inequality in (2.1), rewritten as an upper bound for total width, now yields
\[
  W(\mathcal V,\mathcal I)
  \le Q+4S+12\sum_aN_a
    +C_{\rm TT}\bigl(|\chi(\mathcal V)|+|\mathcal I|\bigr).
\]
Absorb the two universal coefficients into \(C_{\rm net}\). \(\square\)

### Corollary 4.2 (relative calibration)

If \(Q>0\) and
\[
  4S+C_{\rm net}\kappa\le\varepsilon Q,
\tag{4.2}
\]
then
\[
  Q\le W(\mathcal V,\mathcal I)\le(1+\varepsilon)Q.
\tag{4.3}
\]

This is the exact form in which long corridors may be discarded from the scalar
calibration. Neither \(S=O(1)\) nor \(\kappa=O(1)\) is required, but their combined
contribution must be small relative to the retained degeneration.

### Corollary 4.3 (finite short state)

If the number of short interaction types modulo translation is at most \(R\), then
\[
  \mathscr Q=
  \bigl(
    2\|X^{\rm core}\|,
    2\|X^{\rm short}_{[1]}\|,\ldots,
    2\|X^{\rm short}_{[R]}\|,
    S
  \bigr)
\tag{4.4}
\]
is finite dimensional independently of corridor length. The scalar \(Q+4S\) is a
positive linear functional of this vector. The term \(C_{\rm net}\kappa\) remains an
external complexity charge.

## 5. Raw complexity cannot be a coercive coordinate

### Proposition 5.1 (complexity-coordinate no-go)

Suppose a proposed uniformly bounded tower potential has the form
\[
  L(\mathscr Q,\kappa)
  =
  v^{\mathsf T}\mathscr Q+a\kappa
\]
with \(a>0\). Then \(L\) cannot remain uniformly bounded on any family with unbounded
translation-marking cardinality.

**Proof.** Since all coordinates are nonnegative,
\[
  L(\mathscr Q,\kappa)\ge a\kappa.
\]
If \(\kappa\to\infty\), then \(L\to\infty\). \(\square\)

Thus \(\kappa\) may be used as bookkeeping in an affine inequality, but it cannot be
assigned a uniformly positive coefficient in the final coercive scalar. It must first
be:

- absorbed by relative degeneration as in (4.2);
- charged to accumulated entropy;
- canceled telescopically; or
- removed by a sharper dynamical estimate.

This also limits the cone-reduction strategy in `master_transition.md`: uniform
positivity may be required only on the retained geometric coordinates after complexity
has been amortized, not on raw marking cardinality.

## 6. Harmonic transport is not uniformly linear

### Lemma 6.1 (bounded-fanout bottleneck estimate)

For \(x_1,\ldots,x_m>0\),
\[
  \frac{1}{m}\min_jx_j
  \le
  x_1\oplus\cdots\oplus x_m
  \le
  \min_jx_j.
\tag{6.1}
\]

**Proof.** If \(b=\min_jx_j\), then
\[
  \frac1b
  \le
  \sum_j\frac1{x_j}
  \le
  \frac mb.
\]
Take reciprocals. \(\square\)

### Theorem 6.2 (no fixed positive linearization)

There are no nonnegative coefficients \(a,b\) and constants \(0<c\le C<\infty\) such
that
\[
  c(x\oplus y)
  \le ax+by
  \le C(x\oplus y)
\tag{6.2}
\]
for every \(x,y>0\).

**Proof.** Fix \(y=1\) and let \(x\to\infty\). Then \(x\oplus1\to1\), so the upper bound
forces \(a=0\). Fix \(x=1\) and let \(y\to\infty\); similarly \(b=0\). The lower bound
then fails. \(\square\)

### Corollary 6.3

A chart transition involving unrestricted serial splitting cannot be represented,
up to universal multiplicative constants, by a fixed positive matrix on the raw width
coordinates.

There are three possible repairs:

1. retain the bottleneck operation \(\min\) and use monotone homogeneous transition
   maps rather than matrices;
2. prove a balance bound \(x_i/x_j\in[R^{-1},R]\), after which harmonic and arithmetic
   coordinates are comparable with constants depending on \(m,R\);
3. prove uniformly bounded fanout and choose a chamber recording which branch is the
   bottleneck.

Repeated use of Lemma 6.1 through an unbounded elementary corridor can lose a factor
\(m\) at each step. Therefore the corridor must be compressed dynamically before this
bounded-fanout comparison is used.

## 7. Forward calibration and the missing contraction

The one-stage calibration theorem should initially produce an order-preserving,
positively homogeneous map
\[
  \mathscr Q_{\rm out}
  \le
  \Psi_{ut}(\mathscr Q_{\rm in})+\mathbf e_{ut}
\tag{7.1}
\]
from predecessor chart \(t\) to successor chart \(u\), for a bounded set of active
interaction types. A matrix inequality
\[
  \mathscr Q_{\rm out}
  \le
  A_{ut}\mathscr Q_{\rm in}+\mathbf e_{ut}
\tag{7.2}
\]
may be asserted only after proving a balance/chamber lemma that linearizes every
harmonic sum with uniform constants.

The forward upper estimate (7.1) does not have the direction needed by the backward
record lemma. Pure localization or chart-change maps may be identities, so contraction
is required only after composing them with the dynamical step of a complete
entropy-clock block. For the resulting grouped map, scalar closure requires either:

- monotone, positive homogeneous, error-stable Lyapunov gauges satisfying the strict
  forward contraction
  \[
    L_u(\Psi_{ut}(x))\le\mu L_t(x),
    \qquad 0<\mu<1;
  \]
  or
- a verified matrix reduction with the same forward contraction in its calibrated
  gauge; or
- an independently proved backward componentwise lower transition, followed by
  Lemmas 5.1--5.3 of `master_transition.md`.

Lemma 5.4 of `master_transition.md` proves that the first two alternatives give a
backward scalar amplification estimate, including relative errors. The resulting
factor is \((1-\delta)/\mu>1\), where \(\delta<1-\mu\) is the relative error budget.
Lemmas 5.1--5.3 apply only to the third alternative. Bottleneck gauges
\(L=\min_i a_ix_i\), with error measured by \(\max_i a_ie_i\), remain admissible, but
their contraction must be proved rather than inferred from (7.1).

## 8. Remaining virtual realization theorem

### Virtual Corridor-Network Lemma (`OPEN`)

Every entropy-clock virtual block admits a translation-realized corridor decomposition
such that:

1. the number of active and short interaction types modulo translation is universal;
2. all Wave/Wanderers pullbacks are admissible in the finite-horizon correspondence;
3. \(4S+C_{\rm net}\kappa\) is either a fixed small fraction of \(Q\) or is charged to
   accumulated entropy;
4. the active transition has uniformly bounded itinerary fanout;
5. every harmonic series split is either balanced or assigned a declared bottleneck
   chamber;
6. the corridor has a source-faithful bounded-dimensional layered core model satisfying
   the finite support-automaton reduction and transfer trichotomy of
   `corridor_support_automaton.md` and
   `corridor_entropy_shear_dichotomy.md`: permutation windows enter the clone branch
   only after the independent purity/gate certificate holds, cyclic branching is
   credited as entropy only on a closed source-framed primitive return, and
   nonexpanding transfers are routed to extinction, sectorial regularization, or a
   retained shear state, with nonstationary frame/flag changes controlled;
7. in the clone branch, the core graph satisfies the chain-interior,
   endpoint-incidence, and reduced cross-section hypotheses of
   `corridor_clone_criterion.md`, with universally bounded endpoint windows and total
   parallel cross-section size, and the WAD pullbacks have a complete compatible
   incidence with that core graph;
8. after identity chart/localization steps are grouped with the dynamical step, the
   resulting forward block maps admit a common strictly contracting Lyapunov
   calibration, or an independent backward lower transition admits a common expanding
   calibration.

Failure of Item 3 identifies raw marking complexity as the missing state charge.
Failure of Items 4–5 identifies an unrecorded itinerary/bottleneck coordinate. Failure
of Item 6 identifies an unrecorded shear/flag coordinate or unbounded reduced
complexity. Failure of Item 7 identifies a false clone model. Failure of Item 8
refutes the proposed scalar closure even after geometric calibration.

## 9. Orbit packing and normalized complexity

KKL's bound on the number of good translation classes comes from a counting argument
that has an abstract form.

### Lemma 9.1 (orbit packing)

Let a translation corridor have \(q\) cells and an inactive buffer of total length
\(b<q\). Suppose a good family meets \(k\) distinct translation classes and:

1. every such class contributes at least \(q-b\) proper arcs whose marked isotopy
   classes inject into distinct **global** canonical-WAD support coordinates;
2. the coordinate sets contributed by different translation classes are disjoint;
3. the union of representatives is a nonintersecting arc diagram on
   \((\mathcal V,\mathcal I)\).

Then
\[
  k(q-b)\le3|\chi(\mathcal V)|+|\mathcal I|,
\tag{9.1}
\]
and hence
\[
  k\le
  \frac{3|\chi(\mathcal V)|+|\mathcal I|}{q-b}.
\tag{9.2}
\]

**Proof.** By Items 1--2, the \(k\) classes contribute at least \(k(q-b)\) distinct
global WAD coordinates. Item 3 realizes those coordinates as an arc diagram. KKL's
support bound for a WAD on \((\mathcal V,\mathcal I)\) is
\(3|\chi(\mathcal V)|+|\mathcal I|\), which proves (9.1). \(\square\)

Geometric distinctness of translates is not enough: different local arcs may become
one marked isotopy class on the global surface. Items 1--2 are therefore genuine
realization hypotheses, not consequences of disjoint drawing in a corridor chart.

### Corollary 9.2 (bounded normalized topology)

If \(q\ge2b\) and
\[
  3|\chi(\mathcal V)|+|\mathcal I|\le\tau q,
\tag{9.3}
\]
then
\[
  k\le2\tau.
\tag{9.4}
\]

Thus bounded active orbit complexity follows from bounded **normalized marked
topology**
\[
  \tau_B=
  \frac{3|\chi(\mathcal V)|+|\mathcal I|}{q},
\tag{9.5}
\]
not from bounded raw topology.

### Source recovery

In KKL Lemma `lem:bounded good`, a bounded-length arc with no long segment stays in a
window of length \(O(L)\). Each good translation class then supplies approximately
\(q-2\mathfrak b-3L\) disjoint arcs, while the total arc-diagram support is at most
\(3\mathfrak b q\). Lemma 9.1 is exactly this counting mechanism with the
parabolic-bounded constant \(\mathfrak b\) replaced by a normalized complexity
parameter.

### Virtual implication

An accelerated virtual block need not have bounded \(|\mathcal I|\) or
\(|\chi|\). It must instead prove:

1. a translation length \(q_B\) after block grouping;
2. a buffer \(b_B=o(q_B)\), or at least \(q_B\ge2b_B\);
3. a universal bound on
   \[
     \tau_B=
     \frac{3|\chi(\mathcal V_B)|+|\mathcal I_B|}{q_B};
   \]
4. the orbit-realization premise that each good class actually supplies
   \(q_B-b_B\) admissible translates.

If \(\tau_B\) is unbounded, the KKL packing mechanism cannot give a universal number of
active interaction types. The replacement invariant would then need a complexity
density coordinate or a stronger equivalence relation than translation alone.

## 10. Arithmetic density gate

### Lemma 10.1 (translation-marking density identity)

For an \((n,p)\)-translation marking, the number of ideal intervals is
\[
  N=2(n+1)p,
\]
while the shift \(j\mapsto j+2p\) has \(n+1\) cells before crossing the marking.
Therefore
\[
  \frac{N}{n+1}=2p.
\tag{10.1}
\]

**Proof.** This is the defining cardinality relation for a KKL translation marking.
\(\square\)

### Corollary 10.2

Lengthening the corridor by increasing \(n\) does not produce a uniform bound on
marking complexity per translation step when \(p\to\infty\). The density remains
\(2p\).

Consequently a universal proof needs an arithmetic chart gate:

1. **bounded-shift branch:** \(p\le p_0\), where orbit packing and translation-tail
   estimates have bounded normalized marking density;
2. **large-shift branch:** \(p>p_0\), which must be regularized in a
   near-neutral/pseudo-Siegel chart or regrouped into a new block whose usable dynamical
   length grows proportionally to its marking complexity.

Simply declaring the original translation marking “accelerated” does not establish the
second branch: the new action, its admissible pullbacks, and its width comparison must
be constructed.

### Interpolation consequence

The arithmetic gate is a necessary candidate interface for positive/zero-entropy
interpolation. The WAD engine controls bounded shift density. To identify the
complementary large-\(p\) branch with a pseudo-Siegel chart, one must still relate this
translation-marking parameter to the relevant continued-fraction/neutral scale in the
virtual construction. If that identification is proved, an alternating sequence of
bounded and unbounded \(p\) forces the interface loss to be summable or
entropy-relative.

## 11. Replication absorbs linear complexity

The square-root complexity condition is sufficient but not necessary. Positive-entropy
blocks naturally produce a stronger period-replication estimate.

### Lemma 11.1 (replication amortization)

Let \(r\ge1\) be a block length and \(D>0\) a successor degeneration. Suppose
\[
  Q\ge a\,rD,
\qquad
  S\le b\,r,
\qquad
  \kappa\le c\,r
\tag{11.1}
\]
for constants \(a,b,c>0\) independent of \(r,D\). Then
\[
  4S+C_{\rm net}\kappa
  \le
  \frac{4b+C_{\rm net}c}{aD}\,Q.
\tag{11.2}
\]
Consequently, for every \(\varepsilon>0\),
\[
  D\ge
  \frac{4b+C_{\rm net}c}{a\varepsilon}
\tag{11.3}
\]
implies
\[
  4S+C_{\rm net}\kappa\le\varepsilon Q
\tag{11.4}
\]
uniformly in \(r\).

**Proof.** The two upper bounds in (11.1) give
\[
  4S+C_{\rm net}\kappa
  \le(4b+C_{\rm net}c)r.
\]
The lower bound for \(Q\) gives \(r\le Q/(aD)\). Substitute. \(\square\)

### Source alignment

D25's positive-entropy sketch has the same structure: for primitive return period
\(r\), total degeneration is of order \(rW(f_1)\) with an additive topology error
depending on \(r\). The virtual theorem cannot import that sketch outside its stated
setting, but Lemma 11.1 identifies the exact replacement estimates:

1. active width replicates linearly in the number of usable returns;
2. standard corridor width and marked topology grow at most linearly in the same
   count.

No bound on raw \(r\) is needed. At a record scale where \(D\) is large, the entire
linear complexity charge is relatively small.

### Revised virtual target

Item 3 of the Virtual Corridor-Network Lemma may be discharged by either:

- the direct relative condition (4.2);
- the replication hypotheses (11.1);
- an entropy charge; or
- a stronger square-root estimate.

The replication route is the closest match to the established positive-entropy
mechanism.

The count \(r\) in Lemma 11.1 must simultaneously control marking complexity and
genuinely parallel active replicas. This is an additional hypothesis, not a
consequence of having \(r\) return cells.

## 12. Density and congestion form

Let \(r_{\rm mark}\) be the count controlling \(S\) and \(\kappa\), and let
\(r_\parallel\) be the number of genuinely distinct parallel active replicas. Assume
\[
  S\le b\,r_{\rm mark},
  \qquad
  \kappa\le c\,r_{\rm mark},
  \qquad
  Q\ge a\,r_\parallel D.
\tag{12.1}
\]
Define
\[
  \rho_B=\frac{r_{\rm mark}}{r_\parallel}.
\tag{12.2}
\]

### Corollary 12.1 (congestion amortization)

Under (12.1),
\[
  4S+C_{\rm net}\kappa
  \le
  \frac{4b+C_{\rm net}c}{aD}\rho_B\,Q.
\tag{12.3}
\]

**Proof.** The left side is at most
\((4b+C_{\rm net}c)r_{\rm mark}\). Divide by the active lower bound in
(12.1). \(\square\)

Lemma 11.1 is the case \(r_{\rm mark}=r_\parallel\). A serial path or a collection of
isotopic returns can have \(r_{\rm mark}\to\infty\) while
\(r_\parallel\) stays bounded, so topology alone does not control \(\rho_B\).

For the density variables
\[
  q_B=\frac{Q}{r_{\rm mark}},
  \qquad
  s_B=\frac S{r_{\rm mark}},
  \qquad
  k_B=\frac\kappa{r_{\rm mark}},
\tag{12.4}
\]
the corridor sandwich becomes
\[
  q_B
  \le
  \frac{W(\mathcal V,\mathcal I)}{r_{\rm mark}}
  \le
  q_B+4s_B+C_{\rm net}k_B.
\tag{12.5}
\]
This is the normalization compatible with the DL25 per-tile scale. The raw count
\(r_{\rm mark}\) remains necessary to reconstruct total width and audit multiplicity.

# Cross-validation and proof attempt for UPTCR

## 1. Verdict

The cross-validation has two different outcomes.

1. The conditional theorem
   \[
     \mathrm{UPTCR}\Longrightarrow\mathrm{MLC}
   \]
   is valid after making its normalization and relative-neighborhood steps
   explicit.
2. UPTCR itself is **not proved**. The proof attempt stops at UPTCR-1:
   the checked public hypotheses do not construct a regulated virtual carrier
   with protected-access survival. The existing upper-half-disk example proves
   that the most direct monotone-absorption construction is false.

This pass found and corrected three genuine specification errors:

- the one-degree-two-stage condition was incorrectly quantified over the
  auxiliary Wave fan;
- a nonzero fatal collision was incorrectly permitted merely because it lay
  in a bounded defect window; and
- the three block routes were incorrectly declared mutually exclusive.

None of these corrections proves an open analytic clause. MLC remains open.

## 2. Independent source and availability check

The source check was repeated on 2026-07-23.

- Hubbard's written account of Yoccoz's Theorem III states that every
  \(c\in\mathcal M\) which is not infinitely renormalizable has a basis of
  closed connected neighborhoods in \(\mathcal M\):
  [Hubbard 1993, Theorem III](https://pi.math.cornell.edu/~hubbard/Yoccoz.pdf).
  This is exactly the complementary parameter case used in Theorem 4.1.
- Dudko's public Section 4.5 calls the target “Interpolation Problem 4.4”
  and describes virtual Julia sets as a proposed strategy:
  [arXiv:2512.24171, Section 4.5](https://arxiv.org/html/2512.24171#S4.SS5).
  It does not contain a protected-carrier construction theorem.
- KKL Theorem B proves rigidity for prime primitive types with both beau
  bounds and bounded puzzle Teichmüller diameter:
  [arXiv:2606.27272, Theorem B](https://arxiv.org/html/2606.27272).
  It does not state a rigidity theorem for arbitrary mixed towers.
- A targeted arXiv search found no later public full proof of MLC, no public
  solution of Dudko's Interpolation Problem 4.4, and no public theorem
  supplying UPTCR-1--UPTCR-6.

Thus the missing clauses cannot be source-imported.

## 3. Specification errors found and repaired

### CV-1 — selected quadratic spine versus auxiliary Wave fan

The first UPTCR statement said that every complete Wave horizon has exactly
one quadratic stage. This is too broad.

The proved internal no-go
[virtual_long_iterate_wave.md](virtual_long_iterate_wave.md#proposition-51-a-degree-two-endpoint-return-is-insufficient)
shows that a lone degree-two component cannot realize the proof-used KKL
fast-forward fan when its fixed terminal depth is at least two. The fan
contains branches of degree

\[
  2^m,\qquad 0\leq m\leq L,
\]

and therefore branches with \(m\) critical encounters.

The corrected quantifier is:

> The selected quadratic-like return **spine** has exactly one declared
> degree-two stage. Every auxiliary proof branch has a complete critical word
> and degree \(2^{m(\beta)}\). The central Wave corridor is degree one.

This retains the quadratic-like checkpoint while allowing the required
bounded auxiliary fan.

### CV-2 — a bounded window does not cure a fatal collision

The collision coordinates

\[
  \chi_{\rm sheet},\quad
  \chi_{\rm crit},\quad
  \chi_{\rm obs},\quad
  \chi_{\rm access},\quad
  \chi_{\rm loc}
\]

record failures of the current protected analytic realization. The earlier
wording allowed a nonzero collision provided it occurred in a bounded entry,
exit, or terminal window. That does not follow.

For example, erasing a Wave endpoint in a terminal window still changes the
proof-used curve family. A window controls cost, not logical admissibility.

The corrected rule is:

1. the realized protected core has \(\chi=0\);
2. a raw defect may be assigned to a window only after a declared replacement
   localization, sheet set, timing, or carrier resolves every fatal collision
   on the protected core; and
3. only the resulting collision-free local model may contribute a bounded
   endpoint or width charge.

### CV-3 — the three block routes need not be disjoint

A block can simultaneously have positive accumulated entropy and admit a
pseudo-Siegel description. No theorem in the source package makes the three
routes disjoint. The prior phrase “exactly one proved route” was therefore
unsupported.

The corrected statement requires **at least one certified route**. If later
bookkeeping needs a deterministic classification, it must specify a priority
rule; it may not infer mathematical disjointness.

### CV-4 — two implicit steps in the rigidity implication

Two steps were correct but underexplained.

First, the limiting conjugacy in UPTCR-6 must be a global quasiconformal
conjugacy of the sphere, normalized at infinity. If its Beltrami coefficient
\(\mu\) were nonzero on a positive-measure invariant set, then
\(\mu/|\mu|\) would define an invariant line field. The no-line-field clause
therefore gives \(\mu=0\) almost everywhere.

Second, a conformal conjugacy between monic centered quadratics is affine.
Write it as \(h(z)=az+b\). From

\[
  h\circ(z^2+c)=(z^2+c')\circ h
\]

comparison of the \(z^2\) and \(z\) coefficients gives

\[
  a=a^2,\qquad 2ab=0.
\]

Since \(a\neq0\), one has \(a=1\) and \(b=0\), and the constant term then
gives \(c=c'\).

## 4. Revalidated proof that UPTCR implies MLC

### Theorem 4.1

If the corrected UPTCR proposition holds, then the Mandelbrot set is locally
connected.

#### Proof

Let \(c\in\mathcal M\).

If \(f_c\) is not infinitely quadratic-like renormalizable, apply the
source-locked Yoccoz theorem.

Suppose \(f_c\) is infinitely renormalizable. Put

\[
  \lambda=\lambda_{\rm raw}-\delta>1.
\]

UPTCR-4 gives finite \(L_n\geq0\) and, whenever \(L_n>D_*\),

\[
  L_{p(n)}\geq\lambda L_n-E_0,
  \qquad p(n)<n.
\]

Let

\[
  K(c)=
  \max\left\{
    L_{\rm prefix}(c),D_*,
    \frac{E_0}{\lambda-1}
  \right\}.
\]

If some later record \(L_n>K(c)\), then

\[
  L_{p(n)}
  \geq\lambda L_n-E_0
  >
  L_n,
\]

contradicting \(p(n)<n\) and the choice of \(L_n\) as a running record.
Hence \(\sup_nL_n\leq K(c)\).

UPTCR-5 supplies precompactness in the marked topology. UPTCR-6 supplies the
global normalized quasiconformal limit. By CV-4, its Beltrami coefficient
vanishes and equal full marked combinatorics force equality of parameters.
Thus the full marked fiber at \(c\) is \(\{c\}\).

Let \(\Pi_N(c)\) be the compact connected relative neighborhoods from
UPTCR-6. Their intersection is \(\{c\}\). The nested-compact argument gives

\[
  \operatorname{diam}\Pi_N(c)\longrightarrow0.
\]

For any relatively open \(U\subset\mathcal M\) containing \(c\), choose
\(r>0\) such that

\[
  B(c,r)\cap\mathcal M\subset U.
\]

For large \(N\), \(c\in\Pi_N(c)\) and
\(\operatorname{diam}\Pi_N(c)<r\), so

\[
  \Pi_N(c)\subset B(c,r)\cap\mathcal M\subset U.
\]

Thus every point of \(\mathcal M\) has arbitrarily small connected relative
neighborhoods. Components of relatively open subsets are consequently open:
for a point in such a component, one of these connected neighborhoods lies
inside the open set and hence inside its component. Therefore
\(\mathcal M\) is locally connected. \(\square\)

The theorem proves only a conditional implication.

## 5. Attempt to prove UPTCR in dependency order

### Gate 1 — UPTCR-1

The first required step is to construct the actual protected carrier from
Dudko's virtual-Molecule data.

The source provides the required Cantor small Julia sets, a finite critical
orbit package, and the strategy of taking a connected hull. It does not
select a regulated connector or an access/isotopy class. The internal
no-minimum theorem proves that inclusion minimality cannot select one:
the upper and lower semicircles joining two prescribed points are connected
full carriers whose intersection is the disconnected two-point package.

The next possible construction is monotone absorption of every pulled excess.
That construction also fails under the available hypotheses. For

\[
  f(z)=z^2,\qquad
  U^-=\{|z-3/2|<1\},\qquad
  T=[1,2],
\]

the branch is univalent and critical-value-free. Let \(T'\) be the closed
upper half-disk with diameter \(T\). Its first excess

\[
  X=T'\setminus T
\]

attaches along the whole interval. Absorbing \(X\) erases the protected upper
prime-end access at \(3/2\). The itinerary has no critical encounter, sheet
merger, obstacle conflict, or localization escape, so

\[
  \chi_{\rm access}\neq0
\]

is the first collision. Monotonicity makes this collision permanent under
all further attachment-complete enlargements.

Consequently, the checked source hypotheses do not imply UPTCR-1.

This is not a counterexample to UPTCR for actual virtual-Molecule blocks:
the example does not assert that every possible dynamically selected carrier
must be the upper half-disk. It is an exact obstruction to the only
currently specified construction rules.

### Exact missing theorem

To continue the proof, one must supply:

> For every actual virtual-Molecule block and complete proof-use horizon,
> there is a dynamically selected regulated connector system whose rooted
> predecessor closure realizes every required component, whose protected
> access-survival maps are injective and cyclic-order preserving, whose
> selected quadratic spine and auxiliary critical-word fan have the corrected
> degree profile, and whose raw window defects admit collision-free protected
> local models with universal window depth.

No checked public theorem proves this statement. It is precisely the
UPTCR-1/UPTCR-2 interface.

### Gates 2--6

Because Gate 1 is unavailable, the analytic carriers on which Gates 2--4
operate are not defined in the required generality. Independently:

- Gate 2 still needs component exhaustion, relative-cover subgroup
  compatibility, properness, end-properness, and complete auxiliary-fan
  realization;
- Gate 3 still needs uniform core and WAD dimensions and exact Value
  observability;
- Gate 4 still needs the mixed entropy/sectorial transition and discounted
  error theorem;
- Gate 5 still needs compactification or forgetting of unbounded memory; and
- Gate 6 still needs mixed-tower quasiconformal pullback and no invariant
  line fields.

It would be circular to use any of these conclusions to construct Gate 1.

## 6. Promotion decision

The cross-validation proves:

- the corrected conditional implication `UPTCR_IMPLIES_MLC`;
- the selected-spine/auxiliary-fan quantifier correction;
- the zero-collision requirement on every realized protected core; and
- the inclusive, rather than disjoint, block-route semantics.

It does not prove:

- `UNIVERSAL_PROTECTED_TOWER_CLOSURE`;
- any of UPTCR-1--UPTCR-6;
- `H1_MARKED_CONSTRUCTION`;
- `MBTT`;
- `H3_COERCIVITY`;
- `H4_RIGIDITY`; or
- `MLC`.

The proof attempt has therefore reached an exact, documented first
obstruction rather than an unsupported final claim.

## 7. Subsequent connector-realization advance

`protected_regulated_connector.md` now proves the topological part of the
missing theorem: an explicit protected ribbon-routing certificate has an
actual full carrier with singleton traces, injective cyclic-order-preserving
crosscut-chain survival, and exact univalent naturality, without local
connectivity.

The first obstruction has consequently narrowed but has not vanished. The
subsequent free-component criterion proves that a protected connector exists
exactly when one component of the completed free routing domain has
simultaneous singleton ports to every root-shadow cluster. The actual
virtual-Molecule dynamics must first supply
`VIRTUAL_COMMON_FREE_COMPONENT`; it must then close the remaining
`VIRTUAL_PROTECTED_ROUTING_CERTIFICATE` component, route, sheet, critical
word, and complexity clauses. UPTCR-1 remains open until those statements
are proved.

The later augmented-atom pass narrows this first assertion further.
`AUGMENTED_ATOM_COMMON_DOMAIN` proves that pairwise disjoint full augmented
atom/obstacle packets inside one Jordan localization have connected common
complement; explicit surviving ports then imply
`VIRTUAL_COMMON_FREE_COMPONENT`.  The actual
`VIRTUAL_AUGMENTED_ATOM_PORT_CERTIFICATE`—future-complete assignment,
post-fullification disjointness, and surviving ports—remains open.  Thus the
cross-validation stop remains UPTCR-1.

The subsequent fixed-packet audit proves that fullification is
order-independent for a fixed assignment, that closure collisions and
empty original-atom exposure persist under monotone same-label
enlargement, and that individual ports can be truncated in disjoint packet
neighborhoods.  It does not construct the actual virtual inventory or prove
zero collision, exposure, horizon transport, or uniform incidence.  The
stop therefore remains UPTCR-1.

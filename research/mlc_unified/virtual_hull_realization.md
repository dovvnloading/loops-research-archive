# Virtual-hull carrier and WAD realization

## 1. Purpose and status

D25 proposes connected virtual Julia sets built from Cantor families of small Julia
sets and carrying a finite segment of the critical orbit. This note separates two
logically different tasks:

1. constructing a finite topological carrier for the dynamically used continua and
   accesses;
2. realizing that carrier as an actual KKL marked surface whose active curve families
   occur in parallel with controlled standard width.

The counting and width algebra below are proved. The dynamical and analytic
realization is open. In particular, a finite tree, by itself, implies neither bounded
access incidence nor active-width replication.

## 2. Recursive full carriers

### Definition 2.1 (finite carrier)

A **recursive full carrier** consists of:

1. a finite rooted tree \(T=(V,E)\) with a parent-before-child ordering;
2. a full continuum \(K_v\subset\mathbb C\) for every \(v\in V\), with distinct
   \(K_v\) pairwise disjoint after touching continua have been clustered;
3. for every non-root vertex \(v\), a compact continuum \(G_v\) meeting \(K_v\) in a
   nonempty connected set, and a branch piece
   \[
     A_v=K_v\cup G_v
   \]
   that is a full continuum;
4. if \(H_{<v}\) is the union of the previously attached branch pieces, then
   \(A_v\cap H_{<v}\) is nonempty and connected, is contained in the parent branch,
   and \(A_v\) has no other intersection with \(H_{<v}\);
5. a set \(\mathcal C\) of \(R\) declared dynamical cells and a carrier-to-cell
   assignment with
   \[
     |V|+|E|\le B_{\rm occ}R
   \tag{2.1}
   \]
   for a universal occupancy constant.

Touching small Julia sets are first clustered into one \(K_v\). To realize D25
literally, the continua and connectors must lie in the relevant Julia set. That
dynamical inclusion is not part of this abstract definition.

Set
\[
  H=K_{\rm root}\cup\bigcup_{v\ne{\rm root}}A_v.
\tag{2.2}
\]

### Lemma 2.2 (no filling loss inside the tree-nerve model)

Under Definition 2.1, \(H\) is a full continuum.

**Proof.** A full planar continuum is nonseparating. Start with \(K_{\rm root}\) and
attach the full branch pieces \(A_v\) in parent-before-child order. At each step the
old carrier and \(A_v\) are nonseparating compacta with nonempty connected
intersection. The planar Janiszewski union lemma says their union is nonseparating.
Induction proves that \(\mathbb C\setminus H\) is connected. Connectedness of \(H\) is
part of the same induction. \(\square\)

Consequently \(\operatorname{Full}(H)=H\) for this exact carrier. The lemma says
nothing about corridors after adding other hull pieces, fjords, dams, or analytic
regularizations. Filling loss remains a real danger until the final dynamical carrier
satisfies the recursive hypotheses.

## 3. Access-complete incidence

### Definition 3.1

A carrier marking is **access complete through a declared horizon** if every prime-end
or boundary-access class used by a Wave, Wanderers, quasi-additivity, localization, or
selected pullback argument is declared and assigned to a carrier cell.

It has **bounded incidence** if, for universal constants
\(m_A,m_I,m_T,m_\chi\), there are explicit assignment maps with:

1. every declared dynamical access assigned to a carrier element, with every fiber of
   the assignment having size at most \(m_A\);
2. every member of the complete ideal marking \(\mathcal I\) assigned to a carrier
   element, with every fiber having size at most \(m_I\);
3. the multiset of all translation-interval occurrences counted by
   \(\sum_aN_a\) mapped to the \(R\) cells, with every fiber having size at most
   \(m_T\), so
   \[
     \sum_a N_a\le m_TR;
   \tag{3.1}
   \]
4. the realized surface \(\mathcal V\) is of finite type and satisfies
   \[
     |\chi(\mathcal V)|\le m_\chi R.
   \tag{3.2}
   \]

The last condition may instead be proved from an explicit construction using \(O(R)\)
elementary cuts, holes, or handles, each with universally bounded Euler effect.

The first clause forbids hiding arbitrarily many dynamically used accesses inside one
vertex continuum. The second clause is not a notational convention: it is a
substantive dynamical density bound.

### Proposition 3.2 (linear network charge)

Let a recursive full carrier satisfy (2.1), and let its realized marked surface have an
access-complete bounded-incidence marking. Then
\[
  \kappa
  =
  |\chi(\mathcal V)|+|\mathcal I|+\sum_aN_a
  \le c_{\rm inc}R
\tag{3.3}
\]
for a constant depending only on the occupancy and incidence bounds.

**Proof.** Equation (2.1) and the bounded-fiber ideal-marking assignment give
\(|\mathcal I|=O(R)\). Equation (3.1) gives
\(\sum_aN_a=O(R)\), and (3.2) gives
\(|\chi(\mathcal V)|=O(R)\). Summing gives (3.3). \(\square\)

If \(H\Subset D\) for a Jordan disk \(D\), then the unmodified base
\(D\setminus H\) has annular Euler type. That observation does not identify the later
KKL surface \(\mathcal V\); its finite-type complexity is the separate clause (3.2).

### Large-shift gate

For a KKL \((n,p)\)-translation marking,
\[
  N=2(n+1)p.
\tag{3.4}
\]
If the original action supplies only \(R\asymp n+1\) cells, then
\[
  \frac NR\asymp2p.
\tag{3.5}
\]
Thus bounded incidence fails when \(p\to\infty\). Such a block must be transferred to
a proved neutral/sectorial chart or supplied with a new accelerated action having
enough admissible cells. Merely renaming \(N\) as the cell count does not construct
those cells.

## 4. Active replication is analytic

Let
\[
  X^{\rm ret}=X^{\rm core}+\sum_aX_a^{\rm short},
\]
and
\[
  Q=
  2\left(
    \|X^{\rm core}\|+\sum_a\|X_a^{\rm short}\|
  \right)
\tag{4.1}
\]
be the retained WAD weight of `corridor_network_calibration.md`.

### Lemma 4.1 (parallel-replica criterion)

Suppose \(X_1,\ldots,X_{r_\parallel}\) inject into distinct global canonical-WAD
coordinates, their coefficientwise sum is a sub-WAD of the retained state
\(X^{\rm ret}\), and
\[
  2\|X_j\|\ge aD
\tag{4.2}
\]
for every \(j\). Then
\[
  Q\ge ar_\parallel D.
\tag{4.3}
\]

**Proof.** Injectivity makes the global supports disjoint. The WAD norm is additive on
that coefficientwise sub-WAD, and monotonicity under inclusion in \(X^{\rm ret}\)
gives the lower bound for \(Q\). \(\square\)

Geometrically disjoint local arcs are not enough: after projection to the global
surface they may represent one isotopy class. The global-coordinate injectivity is the
substantive hypothesis.

A bounded-overlap version would require an explicit quasi-additivity theorem and its
multiplicity constant; it does not follow from the topology of the carrier.

### Definition 4.2 (replication efficiency)

For \(R\) declared cells and \(D>0\), define
\[
  \eta_B=\frac{Q}{RD}.
\tag{4.4}
\]
The desired replication statement is the lower bound
\(\eta_B\ge\eta_0>0\). Lemma 4.1 supplies it if
\(r_\parallel\ge\rho R\) for a universal \(\rho>0\).

It is often clearer to retain the reciprocal density
\[
  \rho_B=\frac{R}{r_\parallel},
\tag{4.5}
\]
the marking-to-parallel-replica congestion ratio. Bounded \(\rho_B\) says that a
definite fraction of marked cells contribute genuinely distinct parallel support.

### Proposition 4.3 (topology does not imply replication)

Neither a recursive full carrier nor bounded incidence implies a positive lower bound for
\(\eta_B\).

**Proof.** Give each of \(R\) path cells width \(D\) and force the active restrictions
to occur in series. The source-locked harmonic law gives
\[
  Q=
  \underbrace{D\oplus\cdots\oplus D}_{R\ {\rm terms}}
  =\frac DR,
\]
so \(\eta_B=R^{-2}\). Alternatively, if all \(R\) pulled-back arcs represent the same
WAD class, repeated counting does not change its weight and \(Q=D\), giving
\(\eta_B=R^{-1}\). \(\square\)

The transition theorem must therefore preserve the electrical orientation of the
curve families: parallel neutral or dynamical tiles cannot silently become serial
corridor restrictions.

## 5. Conditional WAD calibration

### Theorem 5.1 (incidence, standard width, and replication)

Assume a virtual block with \(R\) declared cells satisfies:

1. it has a recursive full carrier with access-complete bounded incidence;
2. its marked complement is an actual translation-realized KKL corridor
   decomposition;
3. its aggregate standard width satisfies
   \[
     S\le bR;
   \tag{5.1}
   \]
4. its replication efficiency satisfies \(\eta_B\ge\eta_0>0\), equivalently
   \[
     Q\ge\eta_0RD.
   \tag{5.2}
   \]

Then
\[
  Q
  \le
  W(\mathcal V,\mathcal I)
  \le
  \left(
    1+
    \frac{4b+C_{\rm net}c_{\rm inc}}{\eta_0D}
  \right)Q.
\tag{5.3}
\]

**Proof.** Proposition 3.2 gives \(\kappa\le c_{\rm inc}R\). Substitute (5.1) and
(5.2) into the corridor sandwich
\[
  Q\le W\le Q+4S+C_{\rm net}\kappa.
\]
\(\square\)

Here \(W(\mathcal V,\mathcal I)\) is the total KKL marked width of the realized surface.
It is not yet the proposed unified virtual-hull functional. Identifying those two
objects is another chart-comparison theorem.

The hypothesis \(S\le bR\) is essential. Even with one cell and bounded topology, the
standard width of a separate quadrilateral can vary without bound while \(Q\) stays
fixed.

### Corollary 5.2 (two-count congestion form)

Assume a translation-realized corridor decomposition and constants
\(R,D,a>0\), \(r_\parallel\ge1\). If
\[
  \kappa\le cR,\qquad
  S\le bR,\qquad
  Q\ge ar_\parallel D,
\tag{5.4}
\]
then
\[
  W(\mathcal V,\mathcal I)
  \le
  \left[
    1+
    \frac{4b+C_{\rm net}c}{aD}\rho_B
  \right]Q.
\tag{5.5}
\]

**Proof.** The additive corridor charge is at most
\((4b+C_{\rm net}c)R\). Divide it by
\(Q\ge ar_\parallel D\). \(\square\)

For a prescribed relative budget \(\delta>0\), the sufficient condition is
\[
  \frac{4b+C_{\rm net}c}{a}\frac{\rho_B}{D}\le\delta.
\tag{5.6}
\]
A uniform congestion bound is the clean period-independent case; no optimality is
claimed.

## 6. Finite Virtual WAD Realization Theorem

### 6.1 Finite cell-tree extraction (`OPEN`)

For a virtual block \(B\) with pullback horizon \(h_B\) and \(\ell_B\) usable
translation cells, first construct:

1. a **full** connected carrier \(C_B\subset J_f\) containing every Cantor small Julia
   set and critical-orbit point used through time \(h_B\), or an explicit charge for
   every component added by filling;
2. a continuous monotone surjection
   \[
     \pi_B:C_B\to T_B
   \]
   onto a finite ribbon tree \(T_B\), with an upper-semicontinuous fiber decomposition;
3. saturated selected clusters that remain distinct unless explicitly clustered, and
   declared access gates mapping injectively to distinct tree flags with cyclic order
   preserved;
4. connected cell subtrees \(T_{B,i}\), \(0\le i<\ell_B\), plus universally many
   defect pieces, covering \(T_B\), with uniformly many marked clusters and gates per
   cell;
5. each \(T_{B,i}\) equal to the minimal subtree spanning its marked objects, every
   leaf marked, and all unmarked valence-two vertices suppressed;
6. partial dynamics on specified saturated domains descending to cellular maps
   \(\tau_i\) through the semiconjugacy
   \[
     \pi_B\circ f^{q_i}=\tau_i\circ\pi_B,
   \tag{6.1}
   \]
   and, outside the defect pieces, preserving cell, side, access, and orbit labels;
7. a quotient fiber containing every ambient Cantor component relevant to separation,
   with inactive components proved not to merge declared flags or add branch data.

For a cell with \(b\ge2\) marked objects, the minimal-tree hypotheses give
\[
  |V(T_{B,i})|\le2b-2,
  \qquad
  |E(T_{B,i})|\le2b-3.
\tag{6.2}
\]
Indeed, the number of unmarked vertices of valence at least three is at most the
number of marked leaves minus two. The ribbon structure then gives \(O(b)\) flags or
sides. Hence the extraction would give \(O(\ell_B)\) combinatorial sides.

A monotone quotient alone is insufficient: a separating lollipop continuum can map
monotonically onto an interval after its circular part is collapsed. Fullness and
access-faithfulness are independent clauses. This extraction still does not produce
prime-end intervals, an analytic marked surface, or a width estimate.

`saturated_virtual_seed_forest.md` now closes the component-saturation step once
this extraction supplies forward-coherent connected seeds. It also proves the
finite-obstacle complement inclusions and exact degree-weighted pullback of a
future-complete root endpoint marking. Accordingly, the unresolved part of this
section is not the formal saturation recursion. It is the Virtual Seed Certificate:
the connectors must map forward as connected sets, siblings must occupy the
declared distinct pullback components, saturation additions must be audited,
the ambient remainder must be absorbed or separated, and a bounded root access
set must capture every proof-used future end.

### 6.2 Analytic access realization (`OPEN`)

Starting from that cell tree, construct the full analytic core, access-faithful
prime-end intervals in the prescribed cyclic order, and stage correspondences
\[
  F_j=(g_j,\iota_j):
  (\mathcal U_j,H'_j)\rightrightarrows
  (\mathcal V_{j+1},H_{j+1})
\]
with
\[
  g_j^{-1}(H_{j+1})=H'_j=\iota_j^{-1}(H_j).
\tag{6.3}
\]
Exactly one \(g_j\) must have degree two. The remaining properness, saturation,
covering-embedding, orbit-admissibility, and KKL boundary-translation rules are part
of this analytic theorem.

### 6.3 Combined dynamical-analytic realization theorem (`OPEN`)

For every entropy-clock virtual block, construct a number \(R\) of declared cells, a
carrier, and a marked surface satisfying all of the following.

#### Topological and orbit layer

1. **Julia-set carrier:** the carrier lies in the intended virtual Julia hull, or every
   excursion outside it is explicitly justified.
2. **Coverage:** every small Julia component and critical-orbit segment used by any
   later estimate is represented.
3. **Access completeness:** every dynamically used prime-end/access class is declared,
   with bounded incidence per cell.
4. **Controlled occupancy:** carrier size and cell count satisfy (2.1); a one-vertex
   encoding is not accepted unless it also proves the incidence bound.
5. **Inactive remainder:** omitted Cantor components neither separate declared
   accesses nor enter selected pullback domains; claimed translation equivalence must
   include an access-orbit and width-tail proof.
6. **Carrier topology:** either the embedded carrier satisfies the recursive full
   attachment model of Definition 2.1, or the full access-faithful ribbon-tree quotient
   of Section 6.1 is accompanied by an independent \(O(R)\) surface-complexity proof.
7. **Finite-horizon dynamics:** the carrier maps through an admissible selected
   telescope with one critical stage and all required covering embeddings.

#### Analytic WAD layer

8. **Translation realization:** construct the prime-end intervals, boundary maps, and
   lifted immersion data satisfying KKL's actual translation-marking hypotheses.
9. **Density dichotomy:** prove (3.1), or transfer the block to a valid
   neutral/sectorial branch; unbounded \(p\) cannot be hidden in a local-marking
   constant.
10. **Standard-width charge:** prove \(S\le bR\), a direct relative bound
    \(4S\le\delta Q+E\), or a local telescoping/entropy charge.
11. **Parallel replication:** prove \(\eta_B\ge\eta_0\) by injective global
    canonical-WAD support as in Lemma 4.1 or by a stated bounded-overlap
    quasi-additivity theorem.
12. **Unified chart comparison:** identify the realized KKL width with the virtual
    functional by an access-faithful analytic map with controlled distortion,
    multiplicity, and electrical orientation.

Only after Items 1--12 are proved does Theorem 5.1 provide a period-independent
virtual-block comparison.

## 7. Adversarial tests and replacement coordinates

1. **One-vertex vacuity.** Any full hull can be called one vertex. An \(N\)-arm full
   dendrite then hides \(N\) relevant accesses unless access completeness and incidence
   are proved.
2. **Serial path.** \(R\) equal cell widths in series give
   \(\eta_B=R^{-2}\).
3. **Isotopic returns.** \(R\) copies of the same class give
   \(\eta_B=R^{-1}\).
4. **Unbounded standard width.** Fixed topology does not control \(S\).
5. **Large translation shift.** If \(R\asymp n+1\), then marking density is
   \(N/R\asymp2p\).
6. **Ambient Cantor obstruction.** Omitted components may accumulate on a connector
   or merge nominally distinct parallel accesses.
7. **Carrier-location failure.** Arbitrary planar connectors need not belong to the
   Julia set proposed by D25.
8. **Seed-forward failure.** Correct dynamics on every Cantor atom does not imply
   forward coherence of the connectors joining those atoms.
9. **Incomplete root marking.** Exact dyadic pullback of a bounded endpoint set is
   useless if a later fjord or omitted component supplies a proof-used end that
   does not project to that set.

The present state is insufficient if any adversarial block forces:

- unbounded access or translation incidence per usable cell;
- \(S/R\to\infty\) without a telescoping charge;
- \(\eta_B\to0\);
- unbounded comparison multiplicity or a parallel-to-series chart change.

The corresponding replacement coordinates are, respectively, incidence density,
standard-width density, replication efficiency, and transport congestion/orientation.

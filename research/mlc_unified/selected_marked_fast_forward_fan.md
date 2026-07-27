# Selected marked fast-forward fan

## 1. Status and exact result

This note attacks the sharp open Wave-side target isolated in
`virtual_long_iterate_wave.md`: the Selected Marked Fast-Forward Fan Lemma.

One genuinely new part can be closed without assuming MLC or an a priori bound.
If the proof-required finite inverse-component tree of full continua has already
been constructed, then one can choose a single root Jordan neighborhood whose
simultaneous iterated pullbacks:

- follow every selected branch;
- are pairwise disjoint at each depth;
- avoid every prescribed finite-stage compact obstacle;
- are proper Jordan-disk maps at every edge;
- have degree exactly \(2^{m}\) along a branch with \(m\) critical encounters;
  and
- realize a finite dyadic fan of total degree less than \(2^{M+1}\).

This is proved in Theorem 5.1 and Corollary 6.1. It extends the one-chain local
saturation theorem in `finite_horizon_inflation.md` to a simultaneous finite
inverse tree.

The result is topological/analytic local saturation only. It does **not**
construct the inverse-component tree from Dudko's virtual carrier, the complete
prime-end marking, the \(\psi\)-ql immersion, the exhaustive wave itinerary, or
the period-independent extremal-width estimate. Those remaining requirements
are stated as `SMF1`--`SMF8` in Section 8.

## 2. Exact KKL source profile

In the proof of KKL Proposition 3.9, let a short wave crest over limb \(j\),
with
\[
 B<j<q-B-M-1,
\]
and put
\[
 N=q-B-j-2.
\tag{2.1}
\]
KKL uses the single long pair \((f^N,\iota_N)\), not \(N\) separately
estimated one-step pushes. On the proof-used terminal region it has:

\[
 \deg f^N=1
 \quad\text{on the central translation corridor},
\tag{2.2}
\]
and
\[
 \deg f^N=2^m
 \quad (1\le m\le M)
\tag{2.3}
\]
on the terminal pieces. Consequently its selected terminal degree is bounded
by \(2^{M+1}\).

The wave is then partitioned into:

1. a vertical family;
2. an outgoing family continuing through the degree-one corridor;
3. lost families indexed by \(1\le m\le M\);
4. amplifying families indexed by the same terminal windows.

Properness on the crest, end-properness on the crossed limb intervals, and the
source itinerary proposition prove that these families exhaust the wave.

The dyadic degree profile is therefore necessary but not sufficient. The source
also uses the exact location and cyclic order of the sheets.

## 3. Finite inverse trees

Fix a quadratic polynomial
\[
 f(z)=z^2+c_0.
\]

### Definition 3.1 (full inverse tree)

A finite rooted tree \(\mathscr T\), with root \(r\), is a **full inverse
tree of depth \(L\)** if:

1. every vertex \(v\) has a depth \(d(v)\in\{0,\ldots,L\}\);
2. each vertex carries a nondegenerate full continuum \(H_v\);
3. if \(u\) is a child of \(v\), then \(H_u\) is a connected component of
   \(f^{-1}(H_v)\);
4. distinct vertices at the same depth carry distinct components of
   \(f^{-d(v)}(H_r)\).

For an edge \(u\to v\), define its critical label by
\[
 \kappa(u\to v)=
 \begin{cases}
 1,&c_0\in H_v,\\
 0,&c_0\notin H_v.
 \end{cases}
\tag{3.1}
\]
For a vertex \(u\), put
\[
 m(u)=\sum_{e\in[u,r]}\kappa(e).
\tag{3.2}
\]

Because \(f\) has one critical value, a vertex \(v\) with \(c_0\in H_v\)
has one full preimage component. A vertex avoiding \(c_0\) has at most two.

### Definition 3.2 (obstacle-admissible neighborhoods)

For each vertex \(v\), let \(E_v\) be a compact set disjoint from \(H_v\).
An indexed family of neighborhoods \(N_v\) is obstacle-admissible when:

1. \(H_v\Subset N_v\);
2. \(\overline{N_v}\cap E_v=\varnothing\);
3. the closures of \(N_v,N_w\) are disjoint for distinct vertices at the
   same depth;
4. if \(c_0\notin H_v\), then \(c_0\notin\overline{N_v}\).

For a finite tree such a family exists whenever the same-depth continua and
the declared compact obstacles are disjoint. The last clause is possible
because both \(H_v\) and \(\{c_0\}\) are compact.

The \(E_v\) are intended to contain every finite-stage orbit point, access
crosscut, omitted carrier component, or dam that the chosen disk must avoid.
Whether the virtual construction supplies compact separated \(E_v\) is an
open dynamical question.

### Proposition 3.3 (forward-full-hull component no-go)

Fullness, critical-orbit inclusion, and even surjective forward invariance do
not imply the component clause in Definition 3.1.

**Proof.**
Let
\[
 f(z)=z^2,\qquad
 H_+=\{z:|z|\le1\},
\]
and let
\[
 H_-=\{z:|z|\le1,\ \operatorname{Re}z\ge0\}
\]
be the closed right half-disk. Both continua are nondegenerate and full, and
both contain the critical point/value \(0\). Doubling arguments under
\(z\mapsto z^2\) shows
\[
 f(H_-)=H_+.
\]
Nevertheless,
\[
 f^{-1}(H_+)=H_+
\]
is connected, so its unique component is the whole closed disk, strictly
larger than \(H_-\). Thus \(H_-\) is not a component of
\(f^{-1}(H_+)\). \(\square\)

The missing hypothesis is **pullback-component saturation**, not stronger
wording of forward invariance. In particular, adding a prescribed finite
critical-orbit segment to a connected virtual hull does not by itself
construct `SMF1`.

## 4. Simultaneous pullback shrinking

### Lemma 4.1 (polynomial component shrinking)

Let \(P\) be a polynomial, \(K\) a nondegenerate full continuum, and \(H\) a
component of \(P^{-1}(K)\). For every neighborhood \(N\) of \(H\), there is
a neighborhood \(O\) of \(K\) such that the component of \(P^{-1}(O)\)
containing \(H\) has closure in \(N\).

**Proof.**
The compact set \(P^{-1}(K)\) has finitely many components, at most
\(\deg P\). Choose a bounded neighborhood \(N'\) satisfying
\[
 H\Subset N'\Subset N,
 \qquad
 \partial N'\cap P^{-1}(K)=\varnothing,
\]
and containing no other component of \(P^{-1}(K)\).
The compact sets \(P(\partial N')\) and \(K\) are disjoint. Choose a
neighborhood \(O\) of \(K\) whose closure misses \(P(\partial N')\).

The component of \(P^{-1}(O)\) containing \(H\) cannot cross
\(\partial N'\). Its closure cannot meet that boundary either, because any
such point would map into
\(\overline O\cap P(\partial N')\). Hence its closure lies in
\(N'\Subset N\). \(\square\)

### Lemma 4.2 (one root controls a finite inverse tree)

Let \(\mathscr T\) be a full inverse tree with an obstacle-admissible family
\((N_v)\). There is a neighborhood \(O_r\) of \(H_r\) such that, for every
open connected neighborhood \(B\) satisfying
\[
  H_r\subset B\subset O_r
\]
(in particular, for every admissible Jordan root neighborhood used later)
and every vertex \(v\), the
component
\[
 A_v(B)
 :=
 \operatorname{Comp}_{H_v}\bigl(f^{-d(v)}(B)\bigr)
\tag{4.1}
\]
has closure in \(N_v\).

**Proof.**
For each vertex \(v\), apply Lemma 4.1 to
\[
 P=f^{d(v)},\qquad K=H_r,\qquad H=H_v,\qquad N=N_v.
\]
This gives a neighborhood \(O_v\) of \(H_r\). Since the tree is finite,
\[
 O_r:=\bigcap_{v\in\mathscr T}O_v
\]
is still a neighborhood of \(H_r\). If \(B\subset O_r\), then
\[
 f^{-d(v)}(B)\subset f^{-d(v)}(O_v).
\]
The selected component exists: the inverse-tree relation gives
\(f^{d(v)}(H_v)=H_r\subset B\), so the connected set \(H_v\) lies in one
component of \(f^{-d(v)}(B)\). That component lies in the corresponding component over
\(O_v\), whose closure is contained in \(N_v\). \(\square\)

This simultaneous intersection is the finite-tree point that a separate
one-chain construction does not record.

## 5. Finite inverse-tree fan saturation

### Theorem 5.1 (simultaneous proper fan)

Let \(\mathscr T\) be a finite full inverse tree for \(f(z)=z^2+c_0\), and
let \((N_v)\) be obstacle-admissible. Then there is a Jordan disk \(B\)
containing \(H_r\) such that, for every vertex \(v\), the set
\[
 A_v
 :=
 \operatorname{Comp}_{H_v}\bigl(f^{-d(v)}(B)\bigr)
\tag{5.1}
\]
has the following properties:

1. \(H_v\Subset A_v\Subset N_v\);
2. \(A_v\) is a Jordan disk;
3. distinct \(A_v,A_w\) at the same depth are disjoint;
4. if \(u\) is a child of \(v\), then
   \[
   f:A_u\longrightarrow A_v
   \]
   is proper;
5. the edge degree is
   \[
   \deg(f:A_u\to A_v)=2^{\kappa(u\to v)};
   \tag{5.2}
   \]
6. the full branch map is proper with
   \[
   \deg(f^{d(v)}:A_v\to B)=2^{m(v)};
   \tag{5.3}
   \]
7. \(\overline{A_v}\cap E_v=\varnothing\), and if
   \(c_0\notin H_v\), then \(c_0\notin\overline{A_v}\).

**Proof.**
Use Lemma 4.2 to obtain \(O_r\). A full plane continuum has a basis of
Jordan neighborhoods, obtained for example from exterior equipotentials.
Choose a Jordan disk
\[
 H_r\Subset B\Subset O_r
\tag{5.4}
\]
inside \(N_r\). If \(c_0\in H_r\), then it lies in the interior of \(B\);
if \(c_0\notin H_r\), obstacle admissibility lets \(B\) be chosen with
\(c_0\notin\overline B\). Thus \(c_0\notin\partial B\).

Lemma 4.2 gives
\(\overline{A_v}\subset N_v\). This proves Items 1 and 7. We prove the
Jordan and degree assertions together by induction on depth. The root
\(A_r=B\) is a Jordan disk and its boundary avoids \(c_0\).

Suppose \(A_v\) is a Jordan disk. If \(c_0\notin H_v\), then
\(A_v\Subset N_v\) and obstacle admissibility give
\(c_0\notin\overline{A_v}\). Under the translated squaring map
\(f(z)-c_0=z^2\), the preimage of \(A_v\) therefore consists of two
conformal Jordan disks. If \(c_0\in H_v\), then \(c_0\in A_v\); the lift of
the Jordan boundary under \(z\mapsto z^2\) is one Jordan curve and its
interior maps properly with degree two onto \(A_v\). Thus every selected
child \(A_u\) is a Jordan disk, of degree one or two according to (5.2).
The induction proves Items 2 and 5. Item 3 follows from the disjointness of
the \(N_v\) at each depth.

If \(u\) is a child of \(v\), then \(f(A_u)\) lies in the component of
\(f^{-(d(v))}(B)\) containing \(H_v\), namely \(A_v\). The restriction is
proper, and its image is both open and closed in \(A_v\); it is therefore
onto.

Proper degrees multiply along the branch. Equation (5.3) follows from
(3.2) and (5.2). \(\square\)

### What Theorem 5.1 does not use

The proof uses neither a modulus bound nor compactness of a family of
renormalizations. It is finite and local. Its hypotheses may therefore be
used safely inside an attempted a priori-bound proof.

It also does not prove that an arbitrary virtual hull supplies the full
inverse tree or obstacle separation. Those are hypotheses, not conclusions
smuggled into the notation.

## 6. Dyadic terminal fans

### Corollary 6.1 (dyadic fan degree)

Assume Theorem 5.1 and choose vertices
\[
 v_0,v_1,\ldots,v_M
\]
at one common depth \(N\), lying over the same root, with
\[
 m(v_j)=j.
\tag{6.1}
\]
Then
\[
 f^N:
 \bigsqcup_{j=0}^{M}A_{v_j}
 \longrightarrow B
\tag{6.2}
\]
is a proper map from a finite disconnected Jordan domain, and its degree is
\[
 \sum_{j=0}^{M}2^j
 =
 2^{M+1}-1
 <
 2^{M+1}.
\tag{6.3}
\]

**Proof.**
Each restriction in (6.2) is proper of degree \(2^j\) by (5.3).
The source components are disjoint. The number of preimages of a regular
target point is therefore the sum of their degrees, giving (6.3).
\(\square\)

This recovers the arithmetic size of KKL's terminal fan. It also identifies
the exact missing geometric datum: one needs selected branches with every
critical word \(m=0,\ldots,M\), not merely one endpoint component of total
degree two.

### Corollary 6.2 (fixed-depth degree uniformity)

If \(M\) is selected as a function only of the desired terminal margin, then
the degree bound \(2^{M+1}\) is independent of \(q\), the fast-forward time
\(N\), and the virtual transition depth.

This is the degree uniformity needed by the Wave pushforward estimate. It
does not bound the extremal-width error caused by incomplete marking or a
non-proper immersion.

## 7. The marking that the degree theorem does not provide

Theorem 5.1 constructs Jordan sheets. KKL needs a **marked fan**, which
contains more information:

\[
 \mathfrak F_N=
 \bigl(
   \mathscr T_N,\kappa_N,
   \mathcal I_N,\mathcal E_N,
   \prec_N,\pi_N
 \bigr).
\tag{7.1}
\]

Here:

- \(\mathscr T_N\) is the selected inverse-component forest;
- \(\kappa_N\) records every quadratic encounter;
- \(\mathcal I_N\) is the complete pulled ideal/access marking;
- \(\mathcal E_N\) assigns the two ends of every proof-used wave leaf;
- \(\prec_N\) is the cyclic/ribbon order;
- \(\pi_N\) records the projection of every selected sheet and end to the
  original marked surface.

Neither the scalar total degree nor the unmarked forest determines
\(\mathcal I_N,\mathcal E_N,\prec_N,\pi_N\). Two fans can have the same
degree profile and different itinerary partitions because an omitted fjord
or access changes which endpoint lies between two others.

Consequently the correct finite side invariant for the Wave branch is
\(\mathfrak F_N\), or a proved future-equivalent quotient of it. The
degeneration functional \(D\) remains the geometric magnitude; it cannot
replace this finite routing certificate.

## 8. Exact Selected Marked Fast-Forward Fan target

Fix \(B,L\), choose the source terminal depth \(M=M(B,L)\), and let
\[
 N=q-B-j-2
\]
be the proof-used fast-forward time. A virtual block must establish:

### `SMF1` Full inverse-component forest

Construct every full continuum \(H_v\) required by the central branch and
the \(m=1,\ldots,M\) terminal branches, and prove the component relation
\[
 H_u=\operatorname{Comp}_{H_u} f^{-1}(H_v)
\]
at every edge.

### `SMF2` Future-closed separated obstacles

Through the whole fast-forward, put every omitted critical value, postcritical
point, access crosscut, dam, and proof-used carrier component into compact
sets \(E_v\) disjoint from the selected \(H_v\). Verify stagewise forward
closure and the relative-cover subgroup condition.

Once `SMF1`--`SMF2` hold, Theorem 5.1 supplies the simultaneous proper
Jordan fan and Corollary 6.1 supplies its degree bound.

### `SMF3` Complete access/ribbon marking

Construct \(\mathcal I_N,\mathcal E_N,\prec_N\) in (7.1), including every
endpoint used by the vertical, outgoing, lost, and amplifying families.
Prove a bound depending on \(B,M\), not on \(q\).

### `SMF4` Correspondence realization

Promote the polynomial fan to the selected \(\psi\)-ql/fiber-product
correspondence. Prove that the immersion is proper on the central corridor
and end-proper on every proof-used terminal interval. Theorem 5.1 controls
the polynomial map \(f\); it does not prove these immersion statements.

### `SMF5` Central degree-one corridor

Prove that the selected outgoing branch has no critical encounter for the
whole time \(N\), retains every stage marking, and projects to the geometrically
contiguous translation corridor. A degree-one total map without the marked
stage itinerary is insufficient.

### `SMF6` Itinerary exhaustion

For every original wave leaf, prove that its restriction contains a path in
exactly the required vertical/outgoing/lost/amplifying alternatives. No leaf
may escape through an omitted carrier component or an unmarked prime end.

### `SMF7` One-shot analytic transport

Apply Wave/covering estimates to the long map in one shot. With
\(d\le2^{M+1}\), the degree loss is \(O(M)\). All buffer, localization,
and chart errors together must be \(O_{B,L}(1)\), relative to the successor
width, or explicitly telescoping. An \(O(1)\) loss repeated \(N\) times is
not accepted.

### `SMF8` Unified-chart output

Identify the outgoing or amplifying family in the same calibrated chart
used by the static trichotomy and branch assembly. Prove the comparison
constants independent of \(q\), the original rotation after geometric
acceleration, and transition depth.

The **Selected Marked Fast-Forward Fan Lemma** is the assertion that
`SMF1`--`SMF8` hold for every virtual block routed to the Wave branch.
Theorem 5.1 closes the simultaneous local-saturation conclusion between
`SMF1`--`SMF2` and `SMF3`; it does not close the whole lemma.

## 9. Error and dependence audit

| quantity | permitted dependence | forbidden hidden dependence |
|---|---|---|
| terminal depth \(M\) | \(B,L\) | \(q,N\), transition depth |
| fan degree \(d\) | at most \(2^{M+1}\) | \(2^N\) |
| number of marked terminal ends | \(B,M\) | raw corridor length |
| one-shot Wave loss | \(B,M\) | one additive charge per stage |
| fast-forward horizon | linear in \(q\) per visit | an undeclared extra return cycle |
| total terminality horizon | \(H_B(q)\) | truncation at only \(q\) |
| chart error | absolute, relative, or telescoping | \(Cq\) |

Theorem 5.1 is uniform in all geometric moduli because it asserts no modulus
estimate. Any later analytic estimate must be proved separately and cannot
be read back into this theorem.

## 10. Adversarial tests

### 10.1 Same degrees, wrong cyclic order

Permute two terminal access intervals while preserving every component degree.
Equation (6.3) is unchanged, but a leaf previously classified as outgoing may
become amplifying or escape between the swapped ends.

**Verdict:** the degree profile does not imply `SMF3` or `SMF6`.

### 10.2 One critical branch only

Retain only the component with one quadratic encounter. Its degree is two,
but the \(m=2\) terminal sheet required when \(M\ge2\) is absent.

**Verdict:** a quadratic endpoint return is not the fan.

### 10.3 Unseparated omitted carrier

Let omitted continua accumulate on a selected \(H_v\). Then no neighborhood
\(N_v\) can avoid the omitted set, so obstacle admissibility fails before
Lemma 4.2.

**Verdict:** Theorem 5.1 exposes, rather than hides, the needed separation
theorem.

### 10.4 Correct forest, wrong immersion

Construct all polynomial pullback disks but let another immersion sheet enter
the declared core or terminal interval.

**Verdict:** polynomial properness does not imply \(\iota\)-properness or
end-properness; `SMF4` is independent.

### 10.5 Correct fan, accumulated buffers

Charge a fixed buffer loss at each of the \(N\asymp q\) stages.

**Verdict:** the degree stays bounded while the analytic error is \(O(q)\).
`SMF7` must use the one-shot long map or a telescoping charge.

### 10.6 Algebraic rotation conjugacy

Relabel a rotation \(a/q\) by multiplication with \(a^{-1}\bmod q\). The
permutation becomes \(+1\), but the circle order and geometric adjacency
usually change.

**Verdict:** the inverse tree must be built in an actual order-preserving
accelerated corridor; the label conjugacy does not prove `SMF3` or `SMF5`.

## 11. Ledger consequence and next proof move

Theorem 5.1 should be recorded as a proved internal node:

`FINITE_INVERSE_TREE_FAN_SATURATION`.

Its statement is conditional only on a finite full inverse tree and separated
compact obstacles, both explicit in the theorem. It has no open proof
dependency.

The live Wave realization node should depend on this theorem but remain open.
The next nonformal construction is `SMF1`--`SMF3` for one actual virtual
Cantor carrier:

1. enumerate the \(M+1\) source-required critical words;
2. identify their full pullback components through time \(N\);
3. prove omitted carrier components and postcritical data form separated,
   future-closed obstacles;
4. construct the complete cyclic access marking on the resulting fan.

Only after that construction should the project attempt the extremal-width
transport in `SMF7`.

Proposition 3.3 should be recorded separately as
`FORWARD_HULL_COMPONENT_NO_GO`; it prevents partial forward invariance from
being used as a substitute for `SMF1`.

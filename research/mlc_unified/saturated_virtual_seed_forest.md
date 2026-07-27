# Saturated virtual seed forests

## 1. Purpose and source boundary

Dudko's [Interpolation Problem 4.4](https://arxiv.org/html/2512.24171)
proposes partially invariant virtual Julia sets: connected hulls of Cantor
small Julia sets containing the critical orbit through an appropriate finite
number of first returns. The public note does not define a pullback-component
saturation rule, a finite inverse forest, or a complete prime-end marking.
KKL still lists the planned virtual-renormalization manuscript as in
preparation.

This note closes the formal layer between such a connected-hull proposal and
`SMF1`--`SMF3` of `selected_marked_fast_forward_fan.md`.

The main results are:

1. a forward-coherent finite forest of connected seeds has a unique canonical
   pullback-component saturation;
2. finite disjoint forward-closed obstacle lists give the exact stage
   complement inclusions;
3. a complete finite root boundary marking pulls back through the saturated
   Jordan fan with exact cardinality and cyclic order.

These results do not construct the seeds from a virtual Cantor carrier and do
not prove that the root marking is access-complete. The remaining dynamical
input is isolated in Section 8.

## 2. Forward-coherent seed data

Fix
\[
 f(z)=z^2+c_0.
\]

### Definition 2.1 (seed forest)

Let \(\mathscr T\) be a finite rooted tree with root \(r\). A **connected seed
forest** is a collection
\[
 \mathscr C=(C_v)_{v\in\mathscr T}
\]
of nondegenerate connected compact sets.

The seed forest is **forward coherent** if, recursively, after the parent
carrier \(H_v\) has been defined, every child \(u\) satisfies
\[
 f(C_u)\subset H_v.
\tag{2.1}
\]

The stronger condition
\[
 f(C_u)\subset C_v
\tag{2.2}
\]
is sufficient but not required.

The forest has a **sibling-separation certificate** if distinct children
\(u_1,u_2\) of a vertex \(v\) lie in distinct connected components of
\[
 f^{-1}(H_v).
\tag{2.3}
\]

Condition (2.1) is a set-theoretic forward-closure assertion about the entire
connector seed, not merely its Cantor atoms or orbit points. Arbitrary planar
connectors do not satisfy it automatically.

### Definition 2.2 (saturation recursion)

Define
\[
 H_r:=\operatorname{Fill}(C_r),
\tag{2.4}
\]
where `Fill` adjoins every bounded complementary component.

After \(H_v\) is defined, let
\[
 H_u:=
 \operatorname{Comp}_{C_u}\bigl(f^{-1}(H_v)\bigr)
\tag{2.5}
\]
for each child \(u\). Equation (2.1) and connectedness of \(C_u\) imply that
the component in (2.5) is unique.

The family \(\mathscr H=(H_v)\) is the **pullback saturation** of
\(\mathscr C\).

## 3. Canonical saturation theorem

### Theorem 3.1 (saturated seed forest)

Every finite forward-coherent connected seed forest has a well-defined
pullback saturation. It satisfies:

1. every \(H_v\) is a nondegenerate full continuum;
2. \(C_v\subset H_v\);
3. for every child \(u\) of \(v\),
   \[
   H_u\in\pi_0\bigl(f^{-1}(H_v)\bigr);
   \tag{3.1}
   \]
4. if the sibling-separation certificate holds, distinct vertices at the
   same depth have disjoint carriers;
5. the restriction \(f:H_u\to H_v\) is onto and has degree
   \[
   \deg(f:H_u\to H_v)=
   \begin{cases}
   2,&c_0\in H_v,\\
   1,&c_0\notin H_v;
   \end{cases}
   \tag{3.2}
   \]
6. along a branch with \(m\) critical targets, the total degree is \(2^m\);
7. every critical-orbit point or small Julia atom placed in \(C_v\) remains
   in \(H_v\).

**Proof.**
The root is full by definition. Suppose \(H_v\) is full. Equation (2.1)
puts the connected set \(C_u\) in one component of \(f^{-1}(H_v)\), so
(2.5) is well-defined and contains \(C_u\).

For a quadratic polynomial, the pullback of a full continuum has two
conformal full components when the target avoids the critical value and one
quadratic full component when it contains the critical value. This proves
Items 1--3 and (3.2). The selected component maps onto \(H_v\); otherwise
its image would be a proper relatively open-and-closed subset of the
connected target. The sibling certificate gives disjointness one depth at a
time, and induction gives Item 4. Proper degrees multiply along a branch,
giving Item 6. Item 7 follows from \(C_v\subset H_v\). \(\square\)

### Proposition 3.2 (uniqueness relative to the root)

Fix \(H_r\) and the connected anchors \(C_v\). There is at most one saturated
forest satisfying (3.1) and containing every \(C_v\).

**Proof.**
At the root there is no choice. If the parent \(H_v\) is fixed, the connected
anchor \(C_u\) lies in exactly one component of \(f^{-1}(H_v)\). Thus the
child is forced. Induct on depth. \(\square\)

### Proposition 3.3 (monotonicity under root enlargement)

Let \(H_r\subset\widehat H_r\) be full continua, and construct two saturated
forests using the same connected anchors whenever both recursions are
defined. Then
\[
 H_v\subset\widehat H_v
\tag{3.3}
\]
for every vertex.

**Proof.**
Assume \(H_v\subset\widehat H_v\). Then
\[
 f^{-1}(H_v)\subset f^{-1}(\widehat H_v).
\]
The connected component of the smaller pullback containing \(C_u\) lies in
the connected component of the larger pullback containing the same anchor.
Induct on depth. \(\square\)

This monotonicity makes all carrier enlargement visible: adding one root
atom can only enlarge, never shrink, every anchored descendant component.

## 4. What saturation repairs—and what it can change

The half-disk counterexample in `selected_marked_fast_forward_fan.md`,
Proposition 3.3, shows that forward coherence alone does not give (3.1).
The recursion (2.5) is the required repair.

It may strictly enlarge a seed:
\[
 C_v\subsetneq H_v.
\tag{4.1}
\]
Every component, orbit point, access, or corridor erased or absorbed by this
enlargement must therefore be audited. In particular:

- saturation may join two sides that were distinct in the seed picture;
- a filled region may erase an intended curve family;
- an omitted Cantor component may meet the new \(H_v\);
- the saturated carrier may leave a narrowly defined “connected hull” if that
  term was intended to prohibit whole pullback components.

Thus Theorem 3.1 solves the component relation, not the access-completeness or
width-comparison problem.

## 5. Finite obstacle closure

### Definition 5.1 (admissible obstacle system)

For each vertex \(v\), let \(E_v\) be a compact set. The obstacle system is
**separated** if
\[
 E_v\cap H_v=\varnothing
\tag{5.1}
\]
and distinct same-depth carriers are pairwise disjoint.

It is **forward closed** if, for every child \(u\) of \(v\),
\[
 f(E_u)\subset E_v\cup H_v.
\tag{5.2}
\]

The sets \(E_v\) may be finite unions of omitted small Julia components,
postcritical points, access crosscuts, dams, or other compact proof
obstacles.

### Proposition 5.2 (simultaneous obstacle neighborhoods)

For a finite saturated forest with a finite separated obstacle system, there
are neighborhoods \(N_v\) satisfying Definition 3.2 of
`selected_marked_fast_forward_fan.md`.

**Proof.**
At each fixed depth there are finitely many pairwise disjoint compact
carriers and compact obstacle sets. Their pairwise distances are positive.
Choose pairwise disjoint neighborhoods of the carriers with closures missing
their obstacle sets. If \(c_0\notin H_v\), shrink \(N_v\) to avoid the
compact singleton \(\{c_0\}\). \(\square\)

### Proposition 5.3 (stage complement inclusion)

Put
\[
 \Upsilon_v:=H_v\cup E_v.
\tag{5.3}
\]
If the obstacle system is forward closed, then for every child \(u\to v\),
\[
 f(\Upsilon_u)\subset\Upsilon_v,
\tag{5.4}
\]
equivalently,
\[
 \Upsilon_u\subset f^{-1}(\Upsilon_v).
\tag{5.5}
\]
Hence there is a canonical inclusion
\[
 \widehat{\mathbb C}\setminus f^{-1}(\Upsilon_v)
 \hookrightarrow
 \widehat{\mathbb C}\setminus\Upsilon_u.
\tag{5.6}
\]

**Proof.**
The carrier relation gives \(f(H_u)=H_v\), and (5.2) handles \(E_u\).
This proves (5.4), hence (5.5). Taking complements gives (5.6).
\(\square\)

Proposition 5.3 closes only the set-theoretic complement inclusion. A lift
between chosen relative covers still requires the fundamental-group subgroup
criterion in `finite_horizon_inflation.md`, Lemma 5.1.

### Corollary 5.4 (finite collision dichotomy)

For any finite proposed obstacle list, exactly one of the following occurs:

1. every obstacle is disjoint from its saturated carrier, so Proposition 5.2
   applies; or
2. some obstacle intersects a saturated carrier and cannot be treated as
   omitted—it must be absorbed, split by a proved rule, or shown irrelevant
   to every later access and curve family.

There is no third option in which a colliding compact set remains an
unrecorded obstacle.

## 6. Pullback ribbon marking

The simultaneous proper fan of `selected_marked_fast_forward_fan.md`,
Theorem 5.1, supplies Jordan disks
\[
 f:A_u\to A_v
\]
on the saturated tree. The critical value is never on a selected boundary,
so the boundary maps are finite orientation-preserving circle coverings.

### Definition 6.1 (root endpoint marking)

Let \(P_r\subset\partial A_r\) be a nonempty finite set of ideal endpoints.
For a vertex \(v\), define
\[
 P_v:=
 \left(f^{d(v)}\big|_{\partial A_v}\right)^{-1}(P_r).
\tag{6.1}
\]
The components of
\[
 \partial A_v\setminus P_v
\]
are the pulled ideal intervals, with cyclic order inherited from the
oriented Jordan boundary.

### Theorem 6.2 (exact finite ribbon pullback)

Let
\[
 d_v:=\deg(f^{d(v)}:A_v\to A_r).
\]
Then:

1. \(\partial A_v\to\partial A_r\) is an orientation-preserving covering of
   degree \(d_v\);
2. \[
   |P_v|=d_v|P_r|;
   \tag{6.2}
   \]
3. the number of pulled ideal intervals on \(\partial A_v\) is also
   \(d_v|P_r|\);
4. the marking is functorial under every intermediate edge;
5. cyclic order is preserved locally on every covering sheet.

**Proof.**
Every proper holomorphic map between the selected Jordan disks extends
continuously to the boundary. Since no critical point lies on a boundary,
the boundary restriction is a covering. Holomorphic orientation gives the
positive circle orientation. A degree-\(d_v\) circle covering has exactly
\(d_v\) preimages of each marked endpoint, proving (6.2). Removing \(n>0\)
points from a circle gives \(n\) cyclic intervals. The definition by the
full composite pullback agrees with successive edge pullbacks, proving
functoriality. \(\square\)

### Corollary 6.3 (dyadic fan marking bound)

Suppose selected common-depth fan branches have critical counts
\[
 0,1,\ldots,M.
\]
Across their disjoint boundary circles, the total number of pulled endpoints
and the total number of pulled intervals are both
\[
 |P_r|\sum_{m=0}^{M}2^m
 =
 |P_r|(2^{M+1}-1).
\tag{6.3}
\]
If \(M=M(B,L)\) and \(|P_r|\le K(B,L)\), this bound is independent of the
satellite period \(q\) and fast-forward time.

### Completeness qualification

Theorem 6.2 pulls back every declared root endpoint. It does not prove that
\(P_r\) was complete. A hidden fjord, omitted Cantor component, or later
immersion sheet can introduce a proof-used access not projecting to
\(P_r\). Therefore `SMF3` additionally needs:

\[
 \text{every proof-used fan end projects to }P_r.
\tag{6.4}
\]

Equation (6.4) is the **root future-completeness certificate**. Without it,
the exact count (6.3) is a count of an incomplete marking.

## 7. Combined `SMF1`--`SMF3` reduction

### Theorem 7.1 (seed-to-marked-fan reduction)

Fix \(B,L\), and let \(M=M(B,L)\). Assume:

1. a finite forward-coherent connected seed tree through the fast-forward
   horizon;
2. the sibling-separation certificate;
3. one selected common-depth branch for each critical count
   \(m=0,\ldots,M\);
4. a finite separated forward-closed obstacle system;
5. a finite root endpoint set \(P_r\) satisfying (6.4), with
   \(|P_r|\le K(B,L)\).

Then:

- `SMF1` holds;
- the set-theoretic forward-closure and obstacle-neighborhood portions of
  `SMF2` hold;
- the polynomial pullback and cyclic-cardinality portions of `SMF3` hold;
- the terminal fan degree is \(2^{M+1}-1\);
- its total pulled marking is
  \(K(B,L)(2^{M+1}-1)\);
- all these bounds are independent of \(q\) and the fast-forward time.

**Proof.**
Apply Theorem 3.1, Propositions 5.2--5.3, the simultaneous proper-fan theorem,
and Theorem 6.2. The two geometric sums give the displayed degree and marking
bounds. \(\square\)

The theorem is a conditional construction with explicit, checkable inputs.
It does not claim that Dudko's connected hull proposal supplies Inputs 1--5.

## 8. Exact remaining Virtual Seed Certificate

The next dynamical theorem must construct the five inputs of Theorem 7.1 from
one actual virtual-Molecule block.

### `VSC1` Forward-coherent connectors

Join the required Cantor small Julia sets and finite critical-orbit labels by
connected compact seeds \(C_v\) satisfying
\[
 f(C_u)\subset C_v
\]
or the weaker certified inclusion (2.1). Arbitrary planar hull connectors are
not accepted.

Equivalently, use the Virtual Root-Carrier Certificate `VRC1`--`VRC7` from
`root_pullback_virtual_carrier.md`: one full root continuum whose iterated
pullback components contain the whole required packages and realize the
prescribed routing. Theorem 3.1 of that note then supplies the connectors by
taking each seed to be its selected component.

### `VSC2` Sibling component separation

Prove that the central branch and terminal critical-word branches occupy the
required distinct pullback components. If two anchors lie in one component,
they are one sheet and cannot be counted twice.

Under the root formulation, this is exactly the component-quotient collision
test `VRC5`, after every future-required root atom has been included. Root
enlargement can merge previously distinct classes.

### `VSC3` Saturation-location audit

After applying (2.5), prove every enlarged \(H_v\) lies in the admissible
virtual carrier or explicitly charge each added region and erased curve
family.

### `VSC4` Absorb-or-separate remainder

For every ambient Cantor component, postcritical point, fjord, and dam used
through the horizon, prove it is contained in the selected carrier or belongs
to a finite compact obstacle set disjoint from it. Then verify (5.2).

### `VSC5` Root future completeness

Construct \(P_r\) with a \(B,L\)-dependent bound and prove (6.4) for every
vertical, outgoing, lost, and amplifying leaf. Component count alone does not
bound this access set. If endpoints are first exposed at intermediate stages,
apply the exact degree-weighted birth formula and verify `EBC1`--`EBC5` from
`marked_endpoint_birth_ledger.md`; bounded births per corridor stage are not
enough.

### `VSC6` Relative-cover and immersion closure

Verify the subgroup lift, core properness, and end-proper immersion on the
resulting marked fan. These are the remaining parts of `SMF2`--`SMF4`.

The **Virtual Seed Certificate** is `VSC1`--`VSC6`. It is now the sharp
topological/dynamical input to the fast-forward fan; the saturation, finite
obstacle inclusion, dyadic degree, and ribbon pullback arithmetic no longer
need to be reproved inside it.

## 9. Adversarial audit

### 9.1 Atom-forward but connector-backward

Let every small Julia atom map to its declared parent but choose a connecting
arc whose image exits the parent hull.

**Verdict:** atom dynamics does not imply (2.1); `VSC1` must include the
connectors.

### 9.2 Siblings in one pullback component

Place two connected anchors in the unique critical pullback component.

**Verdict:** labeling them as two fan sheets double-counts one component;
the sibling certificate is essential.

### 9.3 Saturation swallows an omitted atom

An atom disjoint from the seed lies in a region added by component saturation.

**Verdict:** it is not an obstacle satisfying (5.1). It must be absorbed and
marked, or proved irrelevant after the new topology is audited.

### 9.4 Infinite obstacle accumulation

Let omitted continua accumulate on \(H_v\).

**Verdict:** compact separation and Proposition 5.2 fail. A finite-horizon
theorem must prove that only a finite closed obstacle union is relevant or
absorb the accumulation set.

### 9.5 Incomplete root endpoints

Pull back a root marking of size one while a hidden fjord defines a second
proof-used prime end.

**Verdict:** (6.3) remains arithmetically true but marks the wrong family.
The future-completeness certificate cannot be inferred from the degree.

### 9.6 One new endpoint per corridor stage

Add a genuinely new proof-used access at each of \(N\asymp q\) stages.

**Verdict:** the complete marking grows like \(q\), not (6.3). Either all
ends project to a bounded root set, or the width error must be density
normalized/amortized.

### 9.7 Complement inclusion without cover lift

Choose relative covers whose fundamental-group subgroups violate the lift
criterion even though (5.6) holds.

**Verdict:** Proposition 5.3 does not prove `VSC6`.

## 10. Ledger proposal

The following internal results are proved:

- `SATURATED_SEED_FOREST`;
- `FINITE_OBSTACLE_FORWARD_CLOSURE`;
- `FINITE_FAN_RIBBON_PULLBACK`.

The live `H2_VIRTUAL_LONG_ITERATE_WAVE` node should depend on these results
and remain open. No source import or MLC claim is promoted.

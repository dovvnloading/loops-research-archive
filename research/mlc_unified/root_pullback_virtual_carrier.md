# Root-pullback virtual carrier criterion

## 1. Purpose

The Virtual Seed Certificate currently asks for a connected connector at
every stage. This note proves that independent stagewise connector choices
are unnecessary.

For a finite horizon, the entire saturated carrier forest is determined by:

1. one full root continuum;
2. the components of its iterated pullbacks containing the required compact
   atom/orbit packages; and
3. the routing and separation of those components.

This is a genuine reduction of `VSC1`--`VSC3`. It does not construct the
required root continuum for Dudko's virtual-Molecule data and does not prove
the immersion carrier equality needed for zero endpoint births.

## 2. Required packages and root shadows

Fix a quadratic polynomial
\[
 f(z)=z^2+c_0
\]
and a finite rooted combinatorial tree \(\mathscr T\). Let \(d(v)\) denote
the depth of a vertex \(v\).

At each vertex prescribe a nonempty compact **required package**
\[
 S_v\subset\mathbb C.
\tag{2.1}
\]
It may be disconnected. It is intended to contain all Cantor small Julia
sets, critical-orbit points, dams, or other objects that must belong to that
selected carrier at that stage.

For a proposed root continuum \(H_r\), the elementary inclusion condition is
\[
 f^{d(v)}(S_v)\subset H_r.
\tag{2.2}
\]
Equation (2.2) puts \(S_v\) in \(f^{-d(v)}(H_r)\), but it does not imply that
all of \(S_v\) lies in one component. We therefore require:

### `RC1` Component containment

For every vertex \(v\), the whole package \(S_v\) lies in one component
\[
 H_v\in\pi_0\bigl(f^{-d(v)}(H_r)\bigr).
\tag{2.3}
\]

### `RC2` Routing

For every child \(u\) of \(v\),
\[
 f(H_u)=H_v.
\tag{2.4}
\]

### `RC3` Selected-sheet separation

Distinct selected vertices at the same depth which are to represent
different sheets have different components \(H_v\).

The data `RC1`--`RC3` are the **root component-routing certificate**.

## 3. Root-pullback equivalence

### Theorem 3.1 (one root determines the saturated forest)

Let \(H_r\) be a nondegenerate full continuum and suppose `RC1`--`RC3`
hold. Then the component family \((H_v)\):

1. consists of nondegenerate full continua;
2. contains every required package \(S_v\);
3. is a forward-coherent saturated inverse forest;
4. has disjoint carriers for every pair of selected same-depth sheets;
5. is unique relative to \(H_r\) and the component assignments.

Conversely, every finite saturated seed forest rooted at \(H_r\) is obtained
in this way by taking \(S_v\) to be any nonempty compact package contained
in its carrier that selects that component.

**Proof.**
For a polynomial, every component of the pullback of a nondegenerate full
continuum is a nondegenerate full continuum. Hence Item 1 follows from
(2.3), and Item 2 is `RC1`.

If \(u\) is a child of \(v\), `RC2` says that \(H_u\) is a component of
\(f^{-1}(H_v)\). It is therefore exactly the pullback saturation of any
connected anchor inside it, proving Item 3. Distinct components of one closed
set are disjoint, so `RC3` proves Item 4. A package lying in one component
selects that component uniquely, which proves Item 5.

Conversely, induction on depth shows that a saturated carrier \(H_v\) is a
component of \(f^{-d(v)}(H_r)\). Any nonempty compact selector package in
that component recovers it, and the saturated edge relation gives `RC2`.
\(\square\)

### Corollary 3.2 (stage connectors can be eliminated)

Once a root component-routing certificate is proved, one may set each stage
seed equal to its selected component \(H_v\). Forward coherence and
pullback-component saturation then hold automatically.

Thus the live connector problem is equivalent to constructing one admissible
root and proving component containment, routing, and separation.

## 4. Exact degree-one corridor criterion

### Proposition 4.1 (critical-value merger)

Let \(K\) be a nondegenerate full continuum. Then
\[
 f^{-1}(K)
 \text{ has }
 \begin{cases}
 1\text{ component of degree }2,&c_0\in K,\\
 2\text{ components of degree }1,&c_0\notin K.
 \end{cases}
\tag{4.1}
\]

Consequently, an edge \(H_u\to H_v\) of the root-pullback forest is
degree one exactly when
\[
 c_0\notin H_v,
\tag{4.2}
\]
and is degree two exactly when \(c_0\in H_v\).

**Proof.**
This is the quadratic pullback dichotomy for a full continuum. When the
target avoids the unique critical value, its preimage is an unbranched
two-sheeted cover split into two full components. When the target contains
the critical value, the two sheets meet through the critical point and form
one degree-two component. \(\square\)

### Corollary 4.2 (central translation exclusion)

A selected fast-forward segment
\[
 H_N\longrightarrow H_{N-1}\longrightarrow\cdots\longrightarrow H_0
\]
is a degree-one corridor if and only if
\[
 c_0\notin H_j
 \qquad(0\le j<N).
\tag{4.3}
\]

Therefore a required package satisfying \(c_0\in S_j\) cannot be placed in a
degree-one target carrier at stage \(j\). It must be assigned to a declared
quadratic/terminal window or the proposed time slicing is inconsistent.

This is an exact compatibility test, not an estimate.

## 5. Component collision partition

For a fixed root \(H_r\) and depth \(n\), define an equivalence relation on
the depth-\(n\) packages by
\[
 v\sim_{H_r,n}w
 \quad\Longleftrightarrow\quad
 S_v\text{ and }S_w\text{ lie in the same component of }f^{-n}(H_r).
\tag{5.1}
\]

### Proposition 5.1 (sheet count is the component quotient)

At depth \(n\), the maximum number of distinct selected sheets supported by
the required packages is exactly the number of equivalence classes of
\(\sim_{H_r,n}\).

In particular, labels cannot create more sheets than this quotient.

**Proof.**
Every sheet is one pullback component, so packages in the same component
cannot define different sheets. Selecting one component for every
equivalence class realizes all classes. \(\square\)

### Proposition 5.2 (root enlargement only merges routing classes)

Let
\[
 H_r\subset\widehat H_r
\]
be full continua. If both component routings are defined, every component of
\(f^{-n}(H_r)\) lies in one component of
\(f^{-n}(\widehat H_r)\). Hence the partition for \(\widehat H_r\) is a
coarsening of the partition for \(H_r\).

**Proof.**
The pullback inclusion
\[
 f^{-n}(H_r)\subset f^{-n}(\widehat H_r)
\]
puts each connected component of the smaller set in one component of the
larger set. \(\square\)

### Consequence

Adding future-required atoms to the root carrier can merge formerly
separated sheets. Root future completeness and sheet separation must
therefore be solved simultaneously; they cannot be proved in either order
without a stability theorem.

## 6. Relation to attachment support

The root-pullback criterion proves that the selected polynomial source
carrier is an actual pullback component. It does **not** prove
\[
 T_j'=T_j
\tag{6.1}
\]
near the copy embedded by the \(\psi\)-ql immersion.

An extra part of \(T_j'\setminus T_j\) can remain inside the correct selected
pullback component and attach at a central ideal interval. Therefore:
\[
 \text{root component routing}
 \not\Longrightarrow
 \text{empty attachment support}.
\tag{6.2}
\]

The Virtual Bounded Attachment-Support Theorem remains a separate
requirement after Theorem 3.1.

The later Corridor Attachment Transport Theorem in
`corridor_attachment_transport.md` identifies the exact bridge that would
propagate attachment-freeness: a commuting marked homeomorphism of the
*pair* consisting of the pulled carrier and the immersed carrier copy,
including its proof-used prime ends. Root routing supplies only the selected
polynomial-carrier homeomorphism, not this pair naturality. Once pair
naturality is constructed, a single attachment-free anchor would suffice for
the whole degree-one central corridor.

The subsequent pass in `virtual_corridor_pair_naturality.md` constructs pair
naturality conditionally by transporting one complete anchor pair through the
univalent corridor branches. It also proves that package data and selected
root routing do not construct that anchor: the interval/triod model has the
same package and selected dynamics but different ambient excess. If equality
fails, the least finite attachment-orbit closure must be formed and its
sheet-collision partition re-audited against Proposition 5.2.

## 7. Refined virtual root-carrier target

For each virtual-Molecule block and complete Wave horizon, construct a full
root continuum \(H_r\) satisfying:

### `VRC1` Package completeness

Every Cantor small Julia set, prescribed first-return orbit point, proof-used
dam/fjord boundary, and selected terminal-fan anchor is assigned to a
package \(S_v\).

### `VRC2` Root shadow inclusion

Every forward shadow \(f^{d(v)}(S_v)\) lies in \(H_r\).

### `VRC3` Component containment

Each whole package lies in one component of \(f^{-d(v)}(H_r)\).

### `VRC4` Exact routing

Those components realize the prescribed stage and terminal-fan parent map.

### `VRC5` Collision exclusion

The component quotient has every selected sheet required by the Wave
itinerary; no two of them collide after all future-required root data are
included.

### `VRC6` Critical-window compatibility

The critical value is absent from every central degree-one target and
present exactly at the declared quadratic encounters.

### `VRC7` Admissible location

Every selected component stays in the allowed virtual localization, and all
objects outside it satisfy the absorb-or-separate obstacle audit.

`VRC1`--`VRC7` are the **Virtual Root-Carrier Certificate**. By Theorem 3.1
they imply the connector, saturation, routing, and sheet-separation portions
of `VSC1`--`VSC3`.

## 8. Adversarial tests

1. **Late root enlargement.** Start with separated inverse components and
   enlarge the root across the critical value. Proposition 5.2 allows the
   two classes to merge.
2. **Disconnected package split.** Put two atoms of one declared package in
   different components of \(f^{-n}(H_r)\). Root-shadow inclusion holds but
   `RC1` fails.
3. **Wrong parent.** Put a child package in a component whose image is a
   different depth-\((n-1)\) component. Same-depth separation holds but
   routing fails.
4. **Critical point in the corridor.** Put \(c_0\) in a central target
   package. Proposition 4.1 forces degree two.
5. **Hidden immersion excess.** Keep the correct polynomial pullback
   component but attach \(T_j'\setminus T_j\) at an ideal interval.
   Root routing survives while attachment support fails.

## 9. Exact conclusion

The finite-horizon carrier problem no longer requires a free connector choice
at every stage. It requires one root continuum whose iterated pullback
component partition simultaneously realizes all packages, all routing, all
future marks, and the intended critical word. Constructing that root for the
actual virtual-Molecule geometry is open.

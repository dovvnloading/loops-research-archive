# Protected regulated connectors and the lamination-lift candidate

## 1. Purpose and verdict

This pass attacks the first missing input in UPTCR-1: a connected carrier
whose connector is dynamically transportable and does not erase any
proof-used prime end.

Two different statements must not be conflated.

1. **Topological realization.** Once a finite protected ribbon-routing
   certificate is supplied, there is an actual compact full carrier
   realizing it. Every protected crosscut chain survives injectively and in
   cyclic order. The construction is functorial under univalent changes of
   Jordan localization.
2. **Virtual dynamical selection.** The current public virtual-Molecule
   theory does not yet supply that certificate. The source-faithful candidate
   is the full lift of a regulated tree in the locally connected lamination
   model, following KKL's native Hubbard-tree construction. It remains to
   prove that this lift realizes every required component itinerary and
   avoids every protected collar.

The first statement is proved below. The second is isolated as the exact
next open theorem. Consequently this pass does not promote UPTCR-1,
`VIRTUAL_CANONICAL_INTERFACE_CARRIER`, or MLC.

## 2. Source boundary

Dudko's Interpolation Problem 4.4 describes virtual Julia sets as connected
hulls of the relevant Cantor small Julia sets, containing a finite portion
of the critical orbit. It does not select a connector or prove access
survival:

- Dzmitry Dudko, *On the MLC Conjecture and the Renormalization Theory in
  Complex Dynamics*, Section 4.5:
  <https://arxiv.org/html/2512.24171#S4.SS5>.

KKL have a stronger native object. For a primitively renormalizable
periodically repelling \(\psi\)-ql map, their Hubbard tree is the smallest
connected subset of the full dynamical carrier containing the complete
cycle of small filled Julia sets. When the carrier is not locally connected,
they pass to the locally connected rational-lamination model, construct the
tree there, and lift it:

- Jeremy Kahn, Alex Kapiamba, and Mikhail Lyubich, *MLC for parabolically
  bounded primitive renormalization*, Sections 2.5--2.6:
  <https://arxiv.org/html/2606.27272>.

That theorem is a positive control in its native primitive category. It does
not state that an arbitrary collection of virtual Cantor small Julia sets has
the same lifted tree, component routing, or protected-access behavior.

A repeated exact-title and author search on 2026-07-23 found no public
Dudko--Kahn--Lyubich virtual-renormalization manuscript. No result from an
unavailable manuscript is used here.

## 3. Protected ribbon-routing data

Let \(U\Subset\mathbb C\) be a Jordan disk. Let
\[
  A_1,\ldots,A_s\Subset U
\tag{3.1}
\]
be pairwise disjoint nonempty full continua. These are the touching clusters
of root shadows after every intersection has been resolved. Let
\[
  Z\Subset U\setminus\bigcup_i A_i
\tag{3.2}
\]
be the closed forbidden set containing every separated obstacle and every
critical value forbidden at the selected stage.

For one \(A_i\), put
\[
  \Omega_i=\widehat{\mathbb C}\setminus A_i.
\tag{3.3}
\]
A **protected access representative** is a prime-end crosscut chain
\[
  \Gamma_{i,a}
  =
  \bigl(\gamma_{i,a,n},D_{i,a,n}\bigr)_{n\geq1},
\tag{3.4}
\]
where \(\gamma_{i,a,n}\) is a crosscut of \(\Omega_i\) and
\(D_{i,a,n}\) is its selected nested side. For a finite family of distinct
prime ends, truncate the chains so that:

1. every \(\overline{D_{i,a,1}}\setminus A_i\) lies in \(U\);
2. these closed collar tails are pairwise disjoint, including across
   different \(i\); and
3. they miss \(Z\) and every \(A_j\), \(j\ne i\).

The truncation is part of the certificate. It uses only the prime-end
topology: finitely many distinct prime ends have disjoint terminal
neighborhoods, and different compact atoms have disjoint Euclidean
neighborhoods.

Write
\[
  \mathcal D
  =
  \bigcup_{i,a}
  \left(\overline{D_{i,a,1}}\setminus A_i\right).
\tag{3.5}
\]

### Definition 3.1 (free ports)

A free-port system consists of simple arcs
\[
  \alpha_i:[0,1]\longrightarrow\overline U
\tag{3.6}
\]
such that:

1. \(x_i:=\alpha_i(0)\in A_i\) and
   \(\alpha_i((0,1])\subset
     U\setminus(\bigcup_jA_j\cup Z\cup\mathcal D)\);
2. \(\alpha_i\cap A_i=\{x_i\}\), and \(\alpha_i\) misses every other
   \(A_j\);
3. the arcs are pairwise disjoint; and
4. each \(x_i\) is reached through an access different from every protected
   access in (3.4).

Thus the attachment trace at \(A_i\) is the singleton \(\{x_i\}\).

### Definition 3.2 (protected ribbon-routing certificate)

Put \(a_i=\alpha_i(1)\). A **protected ribbon-routing certificate**
\[
  \mathfrak R
  =
  \left(
    U,\{A_i\},Z,\{\Gamma_{i,a}\},\{\alpha_i\},G,\operatorname{rot}
  \right)
\tag{3.7}
\]
consists of the preceding data and a finite embedded tree
\[
  G\subset U\setminus
  \left(\bigcup_iA_i\cup Z\cup\mathcal D\right)
\tag{3.8}
\]
containing every \(a_i\), satisfying
\[
  G\cap\alpha_i=\{a_i\},
\tag{3.9}
\]
and having no unlabeled leaf after degree-two vertices are suppressed.
The datum \(\operatorname{rot}\) is the cyclic order of half-edges at every
vertex induced by the plane orientation.

All accesses read by Wave, Wanderers, covering, quasi-additivity, or width
arguments must occur either among the protected chains or as a declared side
of an edge of the ribbon tree. This last assertion is the
**proof-use completeness clause**. It is not inferred from the number of
atoms.

## 4. The protected connector theorem

Define
\[
  C(\mathfrak R)=G\cup\bigcup_i\alpha_i([0,1])
\tag{4.1}
\]
and
\[
  H(\mathfrak R)
  =
  C(\mathfrak R)\cup\bigcup_iA_i.
\tag{4.2}
\]

### Lemma 4.1 (one-point tree attachment is full)

Let \(T\) be a finite plane tree and let \(K_1,\ldots,K_s\) be pairwise
disjoint full continua. Suppose \(T\cap K_i=\{x_i\}\), with the \(x_i\)
distinct, and \(T\) otherwise misses the \(K_i\). Then
\[
  T\cup\bigcup_iK_i
\tag{4.3}
\]
is a full continuum.

#### Proof

A finite plane tree is compact, connected, and nonseparating. Attach the
\(K_i\) one at a time. At each step the old continuum and \(K_i\) are
nonseparating and meet in the connected set \(\{x_i\}\). The Janiszewski
separation lemma says that the union of two nonseparating plane continua
with connected intersection is nonseparating. Hence every intermediate
union has connected complement. The final union is compact and connected,
so it is full. \(\square\)

For completeness, the separation lemma can be expressed through Alexander
duality and the Mayer--Vietoris sequence. A compact plane set is
nonseparating exactly when its reduced first Čech cohomology vanishes.
For \(X\cup Y\), the relevant exact segment has outer terms
\(\widetilde H^0(X\cap Y)\) and
\(\widetilde H^1(X)\oplus\widetilde H^1(Y)\); all vanish when
\(X\cap Y\) is connected and both \(X,Y\) are nonseparating.

### Lemma 4.2a (protected crosscuts remain crosscuts)

Let \(H\supset A_i\) be a full continuum. If
\[
  (H\setminus A_i)
  \cap
  \bigl(\overline{D_{i,a,1}}\setminus A_i\bigr)
  =\varnothing,
\tag{4.4}
\]
then the tail of \(\Gamma_{i,a}\) is a prime-end crosscut chain in
\(\widehat{\mathbb C}\setminus H\). Its two endpoints remain boundary
points of the enlarged complement and its selected side is the component
containing the old selected domain.

#### Proof

For every sufficiently large \(n\),
\[
  D_{i,a,n}\subset D_{i,a,1}.
\]
The interior of \(\gamma_{i,a,n}\) therefore misses \(H\), while its two
distinct endpoints remain in \(A_i\subset H\). Each endpoint is still a
boundary point of \(\widehat{\mathbb C}\setminus H\): every one of its
neighborhoods meets the interior of the same crosscut, which lies outside
\(H\). Thus \(\gamma_{i,a,n}\) is an arc with interior in the enlarged
complement and distinct endpoints on its boundary, hence a crosscut.

Any path from \(D_{i,a,n}\) to the opposite side without crossing the
crosscut or \(H\) would also be such a path in
\(\widehat{\mathbb C}\setminus A_i\), contradicting the definition of
\(D_{i,a,n}\). Hence the selected sides remain nested crosscut domains and
define a prime end. The original null-chain diameter condition is unchanged
because the crosscuts themselves have not changed. \(\square\)

### Lemma 4.2b (distinctness and cyclic order survive)

Under the hypotheses of Lemma 4.2a, suppose a finite family of protected
chains has pairwise disjoint terminal selected domains before enlargement.
Then the induced prime ends after enlargement are distinct and have the same
cyclic order.

#### Proof

Equivalent prime-end chains eventually divide one another: every
sufficiently deep selected domain of either chain contains a sufficiently
deep selected domain of the other. Pairwise disjoint terminal domains make
that impossible, so the induced prime ends are distinct.

For cyclic order, choose one sufficiently deep crosscut from each of the
finitely many chains. Their closed selected domains are pairwise disjoint.
The cyclic order of the corresponding prime ends is the separation order of
these oriented crosscuts in the complement of the full continuum. The
enlargement changes neither the crosscuts nor their selected sides by Lemma
4.2a. Hence every ordered triple has the same orientation before and after
enlargement, which is exactly preservation of the finite cyclic order.
\(\square\)

### Theorem 4.3 (protected regulated connector realization)

Every protected ribbon-routing certificate \(\mathfrak R\) has an actual
carrier \(H(\mathfrak R)\) satisfying:

1. \(H(\mathfrak R)\) is a compact connected full continuum in \(U\);
2. it contains every root-shadow atom \(A_i\) and misses \(Z\);
3. its connector meets each \(A_i\) in exactly the declared singleton
   trace \(\{x_i\}\);
4. every protected prime end in (3.4) survives, the survival map is
   injective, and cyclic order is preserved;
5. the cyclic order of the connector-created sides is the boundary order of
   the ribbon tree \((G,\operatorname{rot})\);
6. if the proof-use completeness clause holds, the resulting finite marking
   contains every proof-used access; and
7. the construction uses no local-connectivity hypothesis on any \(A_i\).

#### Proof

The set \(C(\mathfrak R)\) is a finite plane tree after the degree-two
vertices \(a_i\) are suppressed. It meets \(A_i\) only at \(x_i\).
Lemma 4.1 proves Item 1. Equations (3.2), (3.6), and (3.8) prove Items 2--3.

By construction,
\[
  \bigl(H(\mathfrak R)\setminus A_i\bigr)
  \cap
  \bigl(\overline{D_{i,a,1}}\setminus A_i\bigr)
  =\varnothing
\tag{4.5}
\]
for every protected chain. Lemmas 4.2a--4.2b therefore define the survival
map and prove its injectivity and cyclic-order preservation. For connector
sides,
take a sufficiently small regular neighborhood of the finite tree away from
the protected collars. Its oriented boundary traverses every edge twice and
has exactly the boundary word determined by \(\operatorname{rot}\). Shrinking
the regular neighborhood changes neither the crosscut separation order nor
the induced prime-end order. This proves Items 4--5.

Item 6 is exactly the proof-use completeness clause. Item 7 follows because
the proof used crosscut chains, not Euclidean boundary extension.
\(\square\)

### Corollary 4.4 (finite side bound)

Suppose \(s\ge2\), every \(A_i\) is a leaf of the quotient ribbon tree, all
degree-two vertices are suppressed, and there are no unlabeled leaves. Then
the tree has at most
\[
  2s-3
\tag{4.6}
\]
edges. Consequently the connector creates at most
\[
  4s-6
\tag{4.7}
\]
oriented side intervals.

#### Proof

Every unlabeled internal vertex has degree at least three. The degree-sum
formula for a finite tree with \(s\) labeled leaves gives at most \(s-2\)
internal vertices and \(2s-3\) edges. A regular-neighborhood boundary meets
each edge on two sides. \(\square\)

This is a bound in terms of the number of retained atoms. It is not a
period-independent bound until the virtual construction proves that \(s\)
is uniformly bounded or supplies a faithful compression.

## 5. Functoriality and corridor transport

### Proposition 5.1 (univalent naturality)

Let \(U,V\) be Jordan disks and let
\[
  \phi:U\longrightarrow V
\tag{5.1}
\]
be an orientation-preserving conformal homeomorphism. Transport every entry
of \(\mathfrak R\) by \(\phi\). Then
\[
  H(\phi_*\mathfrak R)=\phi\bigl(H(\mathfrak R)\bigr),
\tag{5.2}
\]
and the protected survival maps and ribbon boundary orders commute with the
prime-end map induced by \(\phi\).

#### Proof

A conformal homeomorphism of Jordan disks extends to their boundaries.
Gluing an exterior extension gives an orientation-preserving sphere
homeomorphism. It therefore preserves compactness, fullness, intersections,
crosscuts, selected crosscut sides, and cyclic order. Formula (4.2) is
set-theoretic and commutes exactly with \(\phi\), proving (5.2). The same
transport sends every chain used in Lemmas 4.2a--4.2b to its image chain, proving
the commuting survival statement. \(\square\)

### Corollary 5.2 (one-anchor protected connector transport)

Choose one actual protected certificate at the central-to-terminal anchor.
Define every central-stage carrier by transport through the unique univalent
corridor branches. Then all central carriers, connector traces, protected
accesses, and ribbon orders commute exactly through the complete degree-one
horizon.

This corollary proves the connector part of corridor naturality once the
anchor certificate exists. It does not prove equality between the
polynomially pulled carrier and the copy supplied by the \(\psi\)-ql
immersion; that remains an UPTCR-2/component-exhaustion obligation.

## 6. Root-pullback integration

Let the atoms \(A_i\) in (3.1) be all touching clusters of the forward root
shadows
\[
  f^{d(v)}(S_v)
\tag{6.1}
\]
from `root_pullback_virtual_carrier.md`. Construct \(H_r=H(\mathfrak R)\).

### Proposition 6.1 (protected root-to-forest reduction)

Assume:

1. the protected ribbon-routing certificate exists for all root shadows;
2. every package \(S_v\) lies in one selected component of
   \(f^{-d(v)}(H_r)\);
3. those components realize the prescribed parent map and distinct selected
   sheets;
4. the selected critical word agrees with membership of the critical value
   in each target component; and
5. all selected components stay in their authorized localizations.

Then the iterated pullback components form a forward-coherent saturated
forest containing every required package. Along every degree-one central
edge, the protected connector marking transports injectively and in cyclic
order.

#### Proof

Items 2--4 are the root component-routing certificate and critical-window
criterion. The root-pullback equivalence theorem therefore gives the unique
saturated inverse forest. Theorem 4.3 supplies the root marking, and
Proposition 5.1 transports it through every univalent central edge. Item 5
gives admissible location. \(\square\)

The proposition is stronger than arbitrary stagewise connected hulls: one
actual root carrier selects every descendant component. Its remaining
hypotheses are component and critical-word assertions about the actual
virtual-Molecule data, not choices of planar connectors.

## 7. Canonical source-faithful candidate

KKL Section 2.5 suggests a canonical candidate that avoids arbitrary
geometric spanning trees.

Suppose an ambient carrier \(K\) admits:

1. a compact locally connected combinatorial model \(K_{\rm com}\);
2. a continuous monotone semiconjugacy
   \[
     \pi:K\longrightarrow K_{\rm com};
   \tag{7.1}
   \]
3. a dynamically defined regulated tree
   \(T_{\rm com}\subset K_{\rm com}\) containing the images of every
   root-shadow atom and prescribed orbit point; and
4. forward coherence
   \(F_{\rm com}(T_{\rm com})\subset T_{\rm com}\).

Define
\[
  H_{\rm lam}
  =
  \operatorname{Fill}\bigl(\pi^{-1}(T_{\rm com})\bigr).
\tag{7.2}
\]

### Proposition 7.1 (monotone lamination lift)

Under Items 1--4, \(H_{\rm lam}\) is a canonical compact connected full
continuum containing every required root shadow. It is forward coherent
whenever fullification is taken in a localization on which the
semiconjugacy and dynamics commute.

#### Proof

A monotone map has connected point fibers, and the inverse image of a
connected compact set under a compact monotone map is connected. Thus
\(\pi^{-1}(T_{\rm com})\) is a compact continuum containing every required
shadow. Fullification makes it full without destroying connectedness.

The semiconjugacy and Item 4 give forward invariance before fullification.
Polynomial forward images take bounded complementary components into
bounded complementary components or the carrier, so fullification preserves
forward coherence. Every operation in (7.2) is determined by
\((\pi,T_{\rm com})\), proving canonicity relative to that model. \(\square\)

Proposition 7.1 does **not** prove protected-access survival. A fiber of
\(\pi\), or a bounded complementary component added by `Fill`, may occupy a
protected collar. It also does not prove that one disconnected stage package
lies in a single iterated pullback component.

## 8. Exact next virtual theorem

The remaining target is the following falsifiable certificate.

### Virtual Protected Routing Certificate (`VPRC`; open)

For every actual virtual-Molecule block and complete Wave horizon, the
lamination-lift candidate (7.2), or an explicitly equivalent puzzle-cell
candidate, satisfies:

1. **Model availability:** the model, projection, and regulated tree are
   defined on the authorized virtual localization and include every object
   in the proof-use inventory.
2. **Protected collars:** every projection fiber, regulated edge, and filled
   complementary component misses the terminal domain of every proof-used
   protected crosscut chain, except at its declared free singleton port.
3. **Component routing:** every complete stage package lies in one iterated
   pullback component, the parent map is exact, and all selected sheets
   remain distinct after the last root enlargement.
4. **Critical word:** the critical value belongs exactly to the declared
   quadratic target components and to no degree-one central target.
5. **Obstacle and location audit:** every ambient component is absorbed or
   separated, and no selected component leaves its prescribed localization.
6. **Future completeness:** every Wave/width access is represented by a
   protected chain or a connector-side flag through its final proof use.
7. **Uniform complexity interface:** either the retained atom/side incidence
   is uniformly bounded, or a proved quotient preserves every future
   functional and protected survival relation.

By Theorem 4.3 and Proposition 6.1, `VPRC` supplies the regulated-connector
and protected-access portion of UPTCR-1.

## 9. First-failure certificate

A failed `VPRC` proof must stop at the first tuple
\[
  \mathfrak F_{\rm route}
  =
  \left(
    B,j,X,\tau(X),\Gamma,w,\chi,\mathcal L
  \right),
\tag{9.1}
\]
where:

- \(B\) is the virtual block and \(j\) the first stage;
- \(X\) is the first projection fiber, lifted edge, filled component, or
  pullback component causing failure;
- \(\tau(X)\) is its full attachment trace;
- \(\Gamma\) is the first protected chain it enters or erases;
- \(w\) is its complete return/critical word and sheet address;
- \(\chi\) is the first nonzero collision coordinate; and
- \(\mathcal L\) is the authorized localization and the exact escape or
  subgroup defect.

The repair is determined by the first coordinate:

- a collar collision requires another regulated edge or block retiming;
- a component merger requires a revised root or sheet set;
- a critical-word failure requires a different stopping interface;
- a location failure requires a new localization; and
- unbounded side incidence requires a future-faithful compression theorem.

Deleting the affected proof-used access is not a repair.

## 10. Adversarial audit

| Attack | Outcome |
|---|---|
| KKL native Hubbard tree | Positive control: its tree and induced ideal sides supply the ribbon datum in the published primitive category. |
| Upper-half-disk absorption | Rejected: its attachment trace is the full interval and it enters the protected upper collar, violating Definitions 3.1--3.2. |
| Non-locally-connected atom | Allowed: protected accesses are represented by crosscut chains; no Euclidean boundary extension is used. |
| Two distinct protected accesses with overlapping impressions | Allowed only with disjoint terminal prime-end domains; Lemma 4.2 preserves those domains. |
| Connector creates a loop | Rejected: the quotient connector must be a tree. A loop can separate the plane and force uncontrolled fullification. |
| Connector touches an atom twice | Rejected: the trace must be one declared free port; a two-point trace may enclose and erase an access. |
| Hidden access | Rejected by proof-use completeness; the finite side bound does not prove completeness. |
| Late root enlargement | `VPRC-3` is checked only after all future root shadows are inserted. |
| Critical value on a central target | `VPRC-4` fails and the stage must be declared quadratic or retimed. |
| Lamination fiber crosses a protected fjord | `VPRC-2` fails with that fiber as \(X\) in (9.1). |
| Topology is collision-free but width degenerates | No width conclusion is made; analytic calibration remains a later gate. |
| Unbounded satellite period | Theorem 4.3 is qualitative. Uniformity requires `VPRC-7`; no period-dependent constant is hidden. |

## 11. Promotion decision

The following result is proved:

- `PROTECTED_REGULATED_CONNECTOR_REALIZATION`.

The following new exact dynamical obligation is open:

- `VIRTUAL_PROTECTED_ROUTING_CERTIFICATE`.

The existing

- `VIRTUAL_CANONICAL_INTERFACE_CARRIER`,
- `VIRTUAL_CORRIDOR_PAIR_NATURALITY`,
- `H1_MARKED_CONSTRUCTION`,
- `UNIVERSAL_PROTECTED_TOWER_CLOSURE`, and
- `MLC`

remain open. The next analytic task is to build the candidate (7.2) for one
actual virtual-Molecule block and either verify `VPRC-1`--`VPRC-7` or emit
the first certificate (9.1).

## 12. Free-component reduction

The subsequent pass in `virtual_protected_routing_domain.md` removes the
remaining arbitrary tree choice from `VPRC-2`.

After all root shadows, terminal protected collars, obstacles, the critical
exclusion, and the localization boundary are frozen, let
\(\Omega_{\rm free}\) be their complement.  The Protected Free-Component
Criterion proves:

> A protected ribbon-routing certificate exists if and only if one
> component of \(\Omega_{\rm free}\) has simultaneous singleton access ports
> to every required root-shadow cluster.

The proof joins the finite port forest inside that open component, takes a
spanning tree, and invokes Theorem 4.3.  Conversely, every protected
connector lies in one free component.  Thus the first collar or obstacle
separating two required port classes is an exact monotone-unrepairable
obstruction within the current localization.

This promotes `PROTECTED_FREE_COMPONENT_CRITERION`, but the dynamical
existence assertion `VIRTUAL_COMMON_FREE_COMPONENT` remains open.  The
public virtual-hull description does not supply the completed collars,
ports, or free component, and the new criterion gives no uniform incidence
bound.  Consequently `VIRTUAL_PROTECTED_ROUTING_CERTIFICATE`, UPTCR-1, and
MLC remain open.

## 13. Augmented-atom common-domain reduction

The subsequent pass `virtual_common_free_component.md` gives one rigorous
sufficient route to the common component.  Assign the complete finite
forbidden inventory to connected root-shadow seeds and connected separated
obstacle seeds, and fullify them.  If the completed packets are pairwise
disjoint inside the Jordan localization and each original atom retains an
explicit free singleton port, their common complement is connected by the
compacta form of Alexander duality.  All ports therefore lie in one
component of the original free routing domain, so Section 12 supplies the
connector.

This promotes `AUGMENTED_ATOM_COMMON_DOMAIN`.  The actual virtual-Molecule
assignment and port theorem,
`VIRTUAL_AUGMENTED_ATOM_PORT_CERTIFICATE`, is open.  It must audit coverage,
connected seed assignment, post-fullification mergers, localization escape,
port loss, complete-horizon equivariance, and uniform incidence.  The
published connected-hull strategy supplies none of these clauses.

The fixed-assignment mechanics are now proved separately in
`augmented_packet_closure_audit.md`: completion order does not change the
filled packets, irreversible closure collisions have actual chamber
witnesses, and individual ports can be truncated to be pairwise disjoint.
This leaves the source-facing `VAAPC-I`, `VAAPC-C`, `VAAPC-P`, `VAAPC-H`,
and `VAAPC-U` clauses open.

The horizon-first audit in `vaapc_inventory_source_audit.md` orders
`VAAPC-I` further.  Before the inventory or labels are constructed, the
actual block must prove `VIRTUAL_WAVE_HORIZON_CERTIFICATE`: an explicit
finite stopping interface, complete proof-use seed/dependency data, and
absence of any later dependency path to an omitted earlier record.

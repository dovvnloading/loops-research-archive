# Research push I: assessment and corrected integration

## 1. Verdict and source lock

This note audits the co-agent packet received on 2026-07-24.  The packet
consists of:

| Artifact | SHA-256 |
|---|---|
| `mlc_research_push_1.md` | `A85A9FF97A4FA6A356149F97DD10A5D5FB631F5A671760238919E58A2E48D433` |
| `mlc_manuscript_insertions.tex` | `B37C13E5962567B723129A792D6600366EF3F877734EDACF2CB2B6B395592001` |
| `mlc_manuscript_insertions_compiled.pdf` | `9C79F34D756B59B186F3348A9BA5B7C7FE11323FDF51A31A59CD41ABACB789A6` |
| `mlc_ledger_patch_proposal.json` | `239656875947EE73FE17E7A523B855C95E9FFDABCDEA225258579D70BCB4A7E4` |
| attached synopsis | `17E85CDD9A10A78A9DF2E3AEC26422C4574AFFC6420397E61FE2A0BD723A00F8` |

The following results survive mathematical and dependency audit after the
corrections made below:

1. `FUTURE_OBSERVABLE_COMPACTIFICATION`;
2. `FUTURE_FAITHFUL_END_TOPOLOGY`;
3. `NESTED_FULL_PACKET_NONSEPARATION`;
4. `DIRECT_DECORATION_FULL_FIBERS`;
5. `DIRECT_DECORATION_GLOBAL_NONSEPARATION`;
6. `DIRECT_DECORATION_GAP_CELL_ATLAS`;
7. `DIRECT_DECORATION_FINITE_PACKET_REPLACEMENT`;
8. `PROPER_PROTECTED_IMPRESSION_EXPOSURE`;
9. `DIRECT_DECORATION_FINITE_PROTECTED_CARRIER`; and
10. `INTERIOR_PULLBACK_COMPONENT_FORCING`.

The future-observable theorem supplies the compact-end-topology alternatives
in `H3_SYMBOLIC_SIDE_COMPACTNESS` and
`VIRTUAL_PROOF_USE_TRACE_SELECTOR`.  These are conditional interface
theorems: their actual virtual transition systems, horizons, and observable
catalogs are still supplied only by their open upstream dependencies.
Neither promotion proves analytic nondegeneration, finite response
dimension, or a virtual carrier.

The proposed deletion of the target-selector gate is rejected.  The target
word is forced after a target base and an authorized reached component are
known, but target-base typing, component authorization, marked metadata,
and enlargement stability remain open.  The existing granular IDs are
therefore retained.

VAAPC-I, UPTCR, H3 coercivity, rigidity, and MLC remain open.

## 2. Future-observable compactification

Let \(X\) be a set, let \(E\) be countable, and for \(e\in E\) let
\[
  T_e:D_e\longrightarrow X
\tag{2.1}
\]
be a partial deterministic map.  Let \(J\) be countable and let
\[
  O_j:X\longrightarrow Y_j,\qquad j\in J,
\tag{2.2}
\]
where every \(Y_j\) is compact metrizable.  Add a constant observable
\(O_*:X\to\{0\}\).  For a finite word \(w\in E^{<\mathbb N}\), let
\(T_w\) be the chronological composition and \(D_w\) its domain.  Give
\[
  Y_j^\bot=Y_j\sqcup\{\bot\}
\]
the topological-sum topology, so it is again compact metrizable.  Define
\[
  Z=\prod_{(w,j)\in E^{<\mathbb N}\times(J\cup\{*\})}Y_j^\bot
\tag{2.3}
\]
and
\[
  \Phi(x)_{w,j}=
  \begin{cases}
    O_j(T_wx),&x\in D_w,\\
    \bot,&x\notin D_w.
  \end{cases}
\tag{2.4}
\]

### Theorem 2.1 (`FUTURE_OBSERVABLE_COMPACTIFICATION`)

The closure
\[
  K_{\rm fut}=\overline{\Phi(X)}\subset Z
\tag{2.5}
\]
is compact metrizable.  For every \(e\in E\),
\[
  \widehat D_e
  =
  \{z\in K_{\rm fut}:z_{e,*}=0\}
\tag{2.6}
\]
is clopen and
\[
  (\widehat T_ez)_{w,j}=z_{ew,j}
\tag{2.7}
\]
defines a continuous map
\(\widehat T_e:\widehat D_e\to K_{\rm fut}\).  Every \(O_j\) extends
continuously by the empty-word coordinate.  Every finite transition
identity or commuting square which is valid on its exact domain remains
valid on the corresponding compactified domain.

The quotient relation
\[
  x\sim_{\rm fut}y\quad\Longleftrightarrow\quad\Phi(x)=\Phi(y)
\tag{2.8}
\]
is equality of all declared observations after all finite continuations,
including agreement about which continuations are defined.

If a compact Hausdorff dynamical realization \(L\) has a dense exact-state
map and continuously extends the same observables and transitions on
clopen domains, then there is a canonical continuous surjection
\[
  L\twoheadrightarrow K_{\rm fut}
\tag{2.9}
\]
which agrees with \(\Phi\) on exact states.  If \(X\) is countable and all
point predicates are declared, then \(\Phi\) is injective.

#### Proof

The coordinate set in (2.3) is countable.  A countable product of compact
metrizable spaces is compact metrizable, and (2.5) is closed.

Let \(S_e:Z\to Z\) be the coordinate shift
\[
  (S_ez)_{w,j}=z_{ew,j}.
\]
It is continuous.  Equation (2.6) is clopen because
\(\{0,\bot\}\) is discrete.  If \(z\in\widehat D_e\) and
\(\Phi(x_n)\to z\), convergence of the discrete \((e,*)\)-coordinate
implies \(x_n\in D_e\) eventually.  For those \(n\),
\[
  S_e\Phi(x_n)=\Phi(T_ex_n).
\]
Consequently \(S_ez\in K_{\rm fut}\), which proves (2.7).

For a finite word \(w\), the same argument shows that its compactified
domain
\[
  \widehat D_w=\{z:z_{w,*}=0\}
\tag{2.10}
\]
is clopen and that \(\Phi(D_w)\) is dense in \(\widehat D_w\).  Indeed,
every nonempty relatively open subset of the clopen set
\(\widehat D_w\) meets the dense set \(\Phi(X)\), and every such exact
point belongs to \(\Phi(D_w)\).  Thus two continuous finite compositions
which agree on \(D_w\) agree on all of \(\widehat D_w\).  This proves the
identity and commuting-square assertion.

For (2.9), define the map \(F:L\to Z\) coordinatewise by the extended
future observation on the clopen word domain and by \(\bot\) off that
domain.  Every coordinate is continuous, hence so is \(F\), and
\(F\) agrees with \(\Phi\) on the dense exact subset.  Continuity and
compactness give
\[
  F(L)=\overline{F(X)}
      =\overline{\Phi(X)}
      =K_{\rm fut}.
\]
Finally, the point predicate of \(a\) separates \(a\) from every other
exact state. \(\square\)

### Corollary 2.2 (`FUTURE_FAITHFUL_END_TOPOLOGY`)

Suppose an actual component or side-state system has countably many
transition labels and a frozen countable proof-use catalog with specified
compact metrizable target encodings.  Equality of all finite-future
observations defines a canonical future-faithful quotient, and its closure
has a compact metrizable end topology on which every declared transition,
guard, branch, transport, and authorized enlargement extends continuously.

If the system contains a countable side projection \(s:X\to S\), then
declaring the countable predicates
\(\mathbf 1_{\{s=a\}}\), \(a\in S\), keeps distinct exact counter/stack
configurations separated even when the full state set \(X\) is
uncountable.

#### Proof

Apply Theorem 2.1.  The second assertion follows because the displayed
predicates separate the fibers of the side projection. \(\square\)

### Exact status consequence

Corollary 2.2 proves the compact-topology branch of
`H3_SYMBOLIC_SIDE_COMPACTNESS` once the exact presentation and compact
target encodings are named.  It also proves the compact-end-topology branch
of `VIRTUAL_PROOF_USE_TRACE_SELECTOR` after the actual component system and
complete horizon are supplied.

This is not analytic compactness.  Encoding a carrier as a point of a
compact hyperspace permits a degenerate limit.  Proving that limits remain
nondegenerate admissible renormalizations is still exactly the open
`H3_COERCIVITY` problem.  Likewise, the construction gives no universal
finite WAD/core dimension and no pumping theorem.

## 3. Nested full packets

### Theorem 3.1 (`NESTED_FULL_PACKET_NONSEPARATION`)

Let
\[
  F_0\supset F_1\supset\cdots
\]
be nonempty compact subsets of \(\widehat{\mathbb C}\).  If each \(F_m\)
is a finite union of pairwise disjoint full continua, then
\[
  F_\infty=\bigcap_mF_m
\]
has connected complement.

If \(U\) is an open Jordan disk, \(F_m\Subset U\), and
\[
  F_m\cup(\widehat{\mathbb C}\setminus U)
\]
is a finite pairwise-disjoint full packet for every \(m\), then
\(U\setminus F_\infty\) is connected.

#### Proof

The finite full-packet lemma, proved from Alexander duality in
`virtual_common_free_component.md`, gives connectedness of every
\(\widehat{\mathbb C}\setminus F_m\).  These complements increase, all
contain infinity, and
\[
  \widehat{\mathbb C}\setminus F_\infty
  =
  \bigcup_m(\widehat{\mathbb C}\setminus F_m).
\]
An increasing union of connected sets with a common point is connected.
The localized statement applies the same argument after adjoining the
exterior full continuum. \(\square\)

The theorem is a criterion, not a construction of virtual approximants.
Every application must still prove fullness, disjointness, localization,
and nesting at every finite stage.

## 4. Direct-decoration full fibers and global nonseparation

Use the actual direct-decoration data
\[
  g=f^q:Q_a\longrightarrow P,\quad
  \phi_a=(g|_{Q_a})^{-1},\quad
  Q_w=\phi_w(P),\quad
  K_w=\phi_w(K_0),\quad
  E_\omega=\bigcap_mQ_{\omega|m}
\tag{4.1}
\]
from `DIRECT_DECORATION_PULLBACK_COMPACTIFICATION`.  In particular,
\(P,Q_0,Q_1\) are closed Jordan disks, \(Q_0\cap Q_1=\varnothing\),
the closed-piece maps are homeomorphisms, \(K_0\) is a full terminal
filled Julia set, and
\[
  K_0\cap(Q_0\cup Q_1)=\varnothing.
\tag{4.2}
\]

### Theorem 4.1 (`DIRECT_DECORATION_FULL_FIBERS`)

Every \(K_w\) and every \(E_\omega\) is a full continuum.

#### Proof

A homeomorphism between closed Jordan disks extends to a sphere
homeomorphism by extending its boundary map over the complementary Jordan
disks.  Therefore each \(\phi_w\) extends to a sphere homeomorphism and
carries the full continuum \(K_0\) to a full continuum \(K_w\).

For an end address, the closed Jordan disks \(Q_{\omega|m}\) decrease.
Their complements increase, are connected, and contain infinity.  Hence
\[
  \widehat{\mathbb C}\setminus E_\omega
  =
  \bigcup_m
  \bigl(\widehat{\mathbb C}\setminus Q_{\omega|m}\bigr)
\]
is connected. \(\square\)

### Theorem 4.2 (`DIRECT_DECORATION_GLOBAL_NONSEPARATION`)

The complete rooted-end compactum
\[
  \mathcal H_\partial
  =
  \bigcup_wK_w\cup\bigcup_\omega E_\omega
\tag{4.3}
\]
has connected sphere complement.

#### Proof

For \(m\ge0\), put
\[
  \mathcal H_m
  =
  \bigcup_{|u|<m}K_u
  \ \cup\
  \bigcup_{|w|=m}Q_w.
\tag{4.4}
\]
Every term is full.  Equal-depth cylinders are disjoint.  Two finite
fibers are disjoint by the root-gap theorem.  If \(u\) is a strict prefix
of \(w\), then \(K_u\) lies outside the two children of \(Q_u\), whereas
\(Q_w\) lies in one of those children.  Thus (4.4) is a finite
pairwise-disjoint full packet.

Inside each depth-\(m\) cylinder, the next approximation retains only its
root fiber and its two children, so
\(\mathcal H_{m+1}\subset\mathcal H_m\).  Every finite fiber belongs to
all approximants, first through its prefix cylinder and then as an explicit
term.  Every end fiber belongs through all of its prefix cylinders.
Conversely, a point in every \(\mathcal H_m\) either belongs to an explicit
finite fiber or lies at every depth in a unique compatible cylinder, hence
belongs to the associated \(E_\omega\).  Therefore
\[
  \mathcal H_\partial=\bigcap_m\mathcal H_m.
\]
Apply Theorem 3.1. \(\square\)

## 5. Equivariant gap cells

The following elementary neighborhood fact closes a hypothesis left
implicit in the submitted packet.

### Lemma 5.1 (Jordan neighborhood of a full continuum)

If a nondegenerate full continuum \(K\) is compactly contained in an open
set \(G\), then there is a closed Jordan disk \(D\) with
\[
  K\subset\operatorname{int}D\subset D\Subset G.
\tag{5.1}
\]

#### Proof

The exterior \(\widehat{\mathbb C}\setminus K\) is simply connected.
Let \(\psi:\{|z|>1\}\to\widehat{\mathbb C}\setminus K\) be its normalized
external uniformization.  For \(R>1\), the curve \(\psi(\{|z|=R\})\) is
a Jordan curve and its filled interior \(D_R\) is a closed Jordan disk
containing \(K\).  As \(R\downarrow1\), the disks \(D_R\) decrease to
\(K\).  If no \(D_R\) lay in \(G\), compactness would produce points of
\(\widehat{\mathbb C}\setminus G\) in every \(D_R\) and hence in their
intersection \(K\), a contradiction. \(\square\)

Let \(G_0\) be the component of
\(\operatorname{int}P\setminus(Q_0\cup Q_1)\) containing \(K_0\).
Compactness, connectedness, and (4.2) give \(K_0\Subset G_0\).  Choose
\(D\) by Lemma 5.1 and put \(D_w=\phi_w(D)\).

### Theorem 5.2 (`DIRECT_DECORATION_GAP_CELL_ATLAS`)

The closed Jordan cells \(D_w\) are pairwise disjoint, including for
ancestor--descendant addresses, and
\[
  K_w\subset\operatorname{int}D_w,\qquad
  D_w\Subset
  \operatorname{int}Q_w\setminus(Q_{w0}\cup Q_{w1}),
\tag{5.2}
\]
\[
  D_w\cap\mathcal H_\partial=K_w,\qquad
  g(D_{aw})=D_w.
\tag{5.3}
\]
If a compact connected seed \(S_w\Subset\operatorname{int}D_w\), then
\[
  \operatorname{Fill}(S_w)\Subset\operatorname{int}D_w.
\tag{5.4}
\]

#### Proof

Equation (5.2) follows by applying \(\phi_w\) to the root cell.  Cells of
incomparable words lie in disjoint cylinders.  If \(v=uat\), then \(D_v\)
lies in the child \(Q_{ua}\), while \(D_u\) lies outside both children of
\(Q_u\).  This proves disjointness.

Every component of \(\mathcal H_\partial\) other than \(K_w\) lies either
in an incomparable cylinder or in a descendant child of \(Q_w\), proving
the first identity in (5.3).  The second follows from
\(g\circ\phi_a=\operatorname{id}\).

Finally, a collar of \(\partial D_w\), together with the exterior of
\(D_w\), is a connected subset of the unbounded component of
\(\mathbb C\setminus S_w\).  Every bounded complementary component of
\(S_w\) therefore lies away from that collar and inside
\(\operatorname{int}D_w\).  This proves (5.4). \(\square\)

### Theorem 5.3 (`DIRECT_DECORATION_FINITE_PACKET_REPLACEMENT`)

Let \(F\) be a finite set of finite words and let
\[
  K_w\subset L_w\Subset\operatorname{int}D_w,\qquad w\in F,
\]
where every \(L_w\) is full.  Replacing the selected \(K_w\) by \(L_w\)
in \(\mathcal H_\partial\) produces a compact set with connected sphere
complement.

#### Proof

The isolation (5.3) makes every selected \(K_w\) clopen in
\(\mathcal H_\partial\), hence the replacement is compact.  For
\(m>\max_{w\in F}|w|\), make the same replacements in (4.4).  The result
is still a finite pairwise-disjoint full packet, the modified approximants
still decrease, and their intersection is exactly the modified rooted-end
compactum.  Theorem 3.1 applies. \(\square\)

## 6. Protected exposure and the finite direct-scale carrier

### Lemma 6.1 (`PROPER_PROTECTED_IMPRESSION_EXPOSURE`)

Let \(K\Subset D^\circ\) be a nondegenerate full continuum in a closed
Jordan disk \(D\), and let \(P\subsetneq\partial K\) be compact.  There
are \(x\in\partial K\setminus P\) and a Jordan arc
\(\alpha:[0,1]\to D\) such that
\[
  \alpha(0)=x,\qquad
  \alpha((0,1))\subset D^\circ\setminus K,\qquad
  \alpha(1)\in\partial D.
\tag{6.1}
\]
If finitely many protected crosscut chains have compact impressions whose
union lies in \(P\), their collar tails can be truncated so that, for the
connected union \(S\) of \(K\) and those tails,
\[
  \alpha\cap\operatorname{Fill}(S)=\{x\}.
\tag{6.2}
\]

#### Proof

Choose \(y\in\partial K\setminus P\) and set
\(\delta=\operatorname{dist}(y,P)>0\).  Choose
\(z\in D^\circ\setminus K\) with \(|z-y|<\delta/4\), and let \(x\in K\)
minimize distance to \(z\).  The segment \((x,z]\) misses \(K\), since
any point of \(K\) on it would be closer to \(z\).  Moreover,
\[
  |x-y|\le |x-z|+|z-y|\le2|z-y|<\delta/2,
\]
so \(x\notin P\).

The full continuum has connected open complement, hence that complement
is arcwise connected.  Join \(z\) to a point outside \(D\), concatenate
with \([x,z]\), take a simple subarc joining the endpoints, and stop at
its first hit on \(\partial D\).  This gives (6.1).

The whole compact arc is disjoint from \(P\).  For each protected chain,
the nested compact closures of its defining domains intersect in its
impression.  Therefore every neighborhood of that impression contains a
sufficiently deep tail; otherwise a convergent sequence outside the
neighborhood would belong to the intersection.  Choose finitely many such
neighborhoods disjoint from \(\alpha\) and truncate the chains.  Extend
\(\alpha\) from \(\partial D\) to infinity outside \(D\).  Every point of
\(\alpha\setminus\{x\}\) is then in the unbounded component of
\(\mathbb C\setminus S\), proving (6.2). \(\square\)

### Theorem 6.2 (`DIRECT_DECORATION_FINITE_PROTECTED_CARRIER`)

Fix finitely many finite direct-decoration addresses.  Suppose that at the
root there are finitely many actual protected prime-end chains whose total
impression is a proper subset of \(\partial K_0\), and transport their
truncated collars through the inverse branches.  Then their packet seeds
fullify in the pairwise-disjoint cells \(D_w\), retain transported free
ports, and remain disjoint from every unselected finite fiber and every end
fiber.  All port interiors lie in one complementary component, and the
protected regulated-connector theorem supplies a carrier preserving the
transported prime ends and cyclic order.

#### Proof

Apply Lemma 6.1 at the root and transport the collars and free arc by the
orientation-preserving homeomorphisms \(\phi_w\).  Theorem 5.2 gives
localization, disjointness, equivariance, and isolation from the entire
rooted-end package.  Theorem 5.3 gives one connected complement after all
selected fibers are replaced by the full packets.  The existing protected
free-component criterion and regulated-connector theorem then apply.
\(\square\)

This theorem is finite and first-scale only.  It does not construct the
second satellite marking, a uniform bound on protected incidence, a
virtual end-fiber return map, or any later fjord, dam, or attachment trace.

## 7. Interior pullback component forcing

Let
\[
  h_w=f^N|_{Q_w}:Q_w\longrightarrow P_\sigma
\]
be a homeomorphism of closed Jordan disks, let \(A\subset P_\sigma^\circ\)
be connected, let \(F=f^r|_A\), and put \(A_w=h_w^{-1}(A)\).

### Theorem 7.1 (`INTERIOR_PULLBACK_COMPONENT_FORCING`)

If
\[
  F(A)\subset P_\tau^\circ,
\tag{7.1}
\]
then the connected set \(f^r(A_w)\) lies in one component \(C\) of
\(f^{-N}(P_\tau^\circ)\).  If an authorized closed target cylinder
\(Q_v\) satisfies
\[
  f^N|_{Q_v}:Q_v\longrightarrow P_\tau
\]
homeomorphically and \(Q_v^\circ=C\), then \(v\) is unique within every
pairwise-disjoint authorized fixed-base family and
\[
  f^r|_{A_w}=h_v^{-1}\circ F\circ h_w.
\tag{7.2}
\]

If the branch extends to the relevant closures and
\[
  F(\overline A)\Subset P_\tau^\circ,
\tag{7.3}
\]
then
\[
  \overline{f^r(A_w)}\Subset C.
\tag{7.4}
\]

#### Proof

For \(x\in A_w\), commutation of polynomial iterates gives
\[
  f^N(f^r(x))
  =
  f^r(f^N(x))
  =
  F(h_w(x))
  \in P_\tau^\circ.
\]
Thus the connected image lies in a unique open pullback component \(C\).
The localized/global component lemma identifies an authorized cylinder
interior with its global component, and fixed-base disjointness gives
uniqueness.  Equation (7.2) is the already proved commuting-iterate lift.

Under (7.3), the lifted closure is a compact subset of
\((f^N)^{-1}(F(\overline A))\cap\overline C\).  Every point of
\(\overline C\) mapping into \(P_\tau^\circ\) belongs to the open preimage
and hence to a component of it.  That component meets \(C\), so it equals
\(C\).  The displayed compact set is therefore contained in the open set
\(C\), which proves (7.4). \(\square\)

Parent, pre-root-shift, and enlargement compatibility follow by uniqueness
only after the corresponding component partitions are nested and the
actual diagrams preserve the target base, component, and metadata.  Those
hypotheses are not produced by Theorem 7.1.

## 8. Rejected shortcuts and corrected dependency effect

1. The old Stone theorem alone still does not prove H3.  The promotion uses
   the stronger future-observable theorem with arbitrary compact metrizable
   targets and all finite continuations.
2. A compact hyperspace encoding does not prove analytic admissibility of
   a limit.  That is retained in `H3_COERCIVITY`.
3. The future-faithful quotient does not prove a uniform finite state
   bound, WAD dimension, or pumping theorem.
4. The nested-packet theorem does not construct nested virtual packets.
5. Global nonseparation is proved only for the already realized
   direct-decoration rooted-end compactum.
6. The protected-carrier theorem assumes actual protected chains with a
   proper total impression and is finite at the direct-decoration scale.
7. The target base, authorized reached component, critical chronology,
   access data, and enlargement stability remain open.  Consequently
   `VIRTUAL_CYLINDER_TARGET_ADDRESS_SELECTOR` and
   `VIRTUAL_REACHED_CYLINDER_COMPONENT_EXHAUSTION` are retained.
8. The submitted ledger counted from an obsolete 56-open baseline.  Counts
   must be regenerated from the repository after integration.

The next source-facing problem remains a two-scale analytic realization:
construct actual second-scale bases, polynomial branches, authorized
components, protected prime ends, and final-root naturality.  The formal
compactifications above activate only after those objects exist.

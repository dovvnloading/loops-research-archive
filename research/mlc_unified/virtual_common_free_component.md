# Virtual common free component: augmented-atom reduction

## 1. Purpose, result, and proof boundary

This pass attacks the first open dynamical assertion isolated in
`virtual_protected_routing_domain.md`:

`VIRTUAL_COMMON_FREE_COMPONENT` (`VCFC`).

The pass proves a new sufficient theorem.  If the complete forbidden
inventory of one finite virtual Wave horizon can be absorbed into finitely
many pairwise disjoint full **augmented atoms** and full separated obstacles,
and every root-shadow atom retains one explicitly represented free singleton
access from their common complement, then the required common free component
exists.  The proof works for non-locally-connected continua and uses no
modulus estimate.

The published virtual-Molecule data do not prove the hypotheses of that
theorem.  In particular, they do not provide:

1. a future-complete assignment of every protected collar, critical
   exclusion, and ambient component to an augmented atom or separated
   obstacle;
2. disjointness after fullification; or
3. a surviving free singleton access to every original root-shadow atom.

The exact new dynamical obligation is
`VIRTUAL_AUGMENTED_ATOM_PORT_CERTIFICATE` (`VAAPC`).  It is strictly more
structured than the phrase “connected hull” and is sufficient, but is not
asserted to be necessary, for `VCFC`.

Verdict:

- `ALEXANDER_DUALITY_COMPACTA`: **imported**;
- `AUGMENTED_ATOM_COMMON_DOMAIN`: **proved**;
- `VIRTUAL_AUGMENTED_ATOM_PORT_CERTIFICATE`: **open**;
- `VIRTUAL_COMMON_FREE_COMPONENT`: **open**;
- UPTCR-1 and MLC: **open**.

## 2. Source lock

### 2.1 Dudko's public virtual-Molecule statement

Dudko's Interpolation Problem 4.4 is an open problem.  The proposed virtual
Julia sets are described as connected hulls of the relevant Cantor small
Julia sets that carry only a finite part of the critical orbit:

- Dzmitry Dudko, *On the MLC Conjecture and the Renormalization Theory in
  Complex Dynamics*, Section 4.5, especially lines 418--429 of the arXiv
  HTML:
  <https://arxiv.org/html/2512.24171#S4.SS5>.

That paragraph does not define augmented atoms, protected terminal collars,
separated obstacle packages, fullification collisions, or free port arcs.
It therefore cannot be cited for any of those assertions.

### 2.2 KKL's native positive control

For a primitively renormalizable periodically repelling \(\psi\)-ql map,
KKL define the Hubbard tree as the smallest connected set containing the
complete native cycle of small filled Julia sets.  In the
non-locally-connected case they construct the tree in the locally connected
rational-lamination model and lift it:

- Jeremy Kahn, Alex Kapiamba, and Mikhail Lyubich, *MLC for parabolically
  bounded primitive renormalization*, Sections 2.5--2.6:
  <https://arxiv.org/html/2606.27272#S2.SS5>.

This is a positive control in KKL's native primitive category.  It is not a
carrier theorem for a partial Dudko virtual package.  KKL's reference list
still records Dudko--Kahn--Lyubich, *Virtual renormalization: interpolating
between primitive and satelite regimes*, as “In preparation”; see line 1743:
<https://arxiv.org/html/2606.27272#bib.bib22>.

An exact-title and author search on 2026-07-24 found no public arXiv version
of that manuscript.  No theorem from it is imported here.

### 2.3 Topological input

We use the compacta form of Alexander duality:

\[
  \widetilde H_0(S^2\setminus K;\mathbb Z)
  \cong
  \check H^1(K;\mathbb Z)
\tag{2.1}
\]

for every nonempty proper compact \(K\subset S^2\).  Hatcher states the
locally contractible form as Corollary 3.45 and explicitly records the
extension to arbitrary compacta by replacing singular cohomology with
\v Cech cohomology on pages 256--257:

- Allen Hatcher, *Algebraic Topology*, Chapter 3:
  <https://pi.math.cornell.edu/~Hatcher/AT/ATch3.pdf>.

Equation (2.1), rather than the locally contractible special case, is the
imported statement.  This distinction is essential because the root-shadow
atoms are not assumed locally connected.

## 3. Frozen data and augmented packets

Let \(U\Subset\mathbb C\) be a Jordan disk.  Let

\[
  A_1,\ldots,A_s\Subset U
\tag{3.1}
\]

be the final touching clusters of all proof-required root shadows.  They are
pairwise disjoint nonempty full continua.

Let \(Q_{\rm dyn}\Subset U\) be the finite closed union of:

1. every terminal protected collar through its last proof use;
2. every critical-value exclusion used to certify a degree-one stage;
3. every absorbed or separated ambient component retained by the obstacle
   ledger; and
4. every localization-forbidden compact set inside \(U\).

The atoms themselves are included in the total forbidden set

\[
  Q=\left(\bigcup_{i=1}^s A_i\right)\cup Q_{\rm dyn},
  \qquad
  \Omega_{\rm free}=U\setminus Q.
\tag{3.2}
\]

The inventory must be frozen after the final root enlargement and through
the complete Wave horizon.

For a compact plane set \(K\), write

\[
  \operatorname{Fill}(K)
  =
  K\cup
  \{\text{bounded components of }\mathbb C\setminus K\}.
\tag{3.3}
\]

If \(K\) is connected, then \(\operatorname{Fill}(K)\) is a full continuum.

### Definition 3.1 (augmented-atom packet)

An **augmented-atom packet**

\[
  \mathfrak C_{\rm aug}
  =
  \left(
    \{\widehat A_i\}_{i=1}^s,
    \{\widehat O_\ell\}_{\ell=1}^t,
    \{\alpha_i\}_{i=1}^s,
    \mathfrak a
  \right)
\tag{3.4}
\]

for the frozen data consists of the following.

1. **Typed assignment.**  The finite typed list \(\mathfrak a\) assigns
   every connected piece of \(Q_{\rm dyn}\) either to exactly one atom
   \(A_i\) or to exactly one separated-obstacle seed \(O_\ell\).  Assignment
   records the original component name, proof-use stages, attachment trace,
   return word, selected sheet, and absorb-or-separate decision.

2. **Connected atom seeds.**  If \(E_i\) is the union of pieces assigned to
   \(A_i\), then \(A_i\cup E_i\) is compact and connected, and
   \[
     \widehat A_i=\operatorname{Fill}(A_i\cup E_i).
   \tag{3.5}
   \]

3. **Connected obstacle seeds.**  Every \(O_\ell\) is compact and connected,
   and
   \[
     \widehat O_\ell=\operatorname{Fill}(O_\ell).
   \tag{3.6}
   \]

4. **Coverage.**
   \[
     Q
     \subset
     \bigcup_i\widehat A_i
     \cup
     \bigcup_\ell\widehat O_\ell.
   \tag{3.7}
   \]
   Enlargement caused by fullification is permitted; omission of a frozen
   forbidden piece is not.

5. **No merger and no escape.**  All continua in
   \[
     \widehat{\mathscr C}
     =
     \{\widehat A_1,\ldots,\widehat A_s,
       \widehat O_1,\ldots,\widehat O_t\}
   \tag{3.8}
   \]
   are pairwise disjoint and compactly contained in \(U\).

6. **Explicit surviving ports.**  For each \(i\), there is a Jordan arc
   \(\alpha_i:[0,1]\to U\) and a point \(x_i\in A_i\) such that
   \[
   \begin{aligned}
     &\alpha_i(0)=x_i,\\
     &\alpha_i\cap\widehat A_i=\{x_i\},\\
     &\alpha_i((0,1])
       \subset
       U\setminus\bigcup\widehat{\mathscr C},
   \end{aligned}
   \tag{3.9}
   \]
   the arcs are pairwise disjoint, and \(x_i\) is not the impression of a
   protected chain.  The arc is part of the certificate; accessibility is
   not inferred from local connectivity.

The **augmented free domain** is

\[
  \Omega_{\rm aug}
  =
  U\setminus
  \left(
    \bigcup_i\widehat A_i
    \cup
    \bigcup_\ell\widehat O_\ell
  \right).
\tag{3.10}
\]

## 4. The planar theorem

### Lemma 4.1 (finite disjoint full compacta do not separate)

Let \(K_0,\ldots,K_N\subset S^2\) be pairwise disjoint nonempty full
continua.  Then

\[
  S^2\setminus\bigcup_{r=0}^N K_r
\tag{4.1}
\]

is connected.

#### Proof

Because \(K_r\) is full, \(S^2\setminus K_r\) is connected.  Hence

\[
  \widetilde H_0(S^2\setminus K_r;\mathbb Z)=0.
\tag{4.2}
\]

Apply (2.1) to \(K_r\):

\[
  \check H^1(K_r;\mathbb Z)=0.
\tag{4.3}
\]

Put \(K=\bigcup_rK_r\).  Since the family is finite, compactness and
pairwise disjointness give pairwise disjoint open neighborhoods of the
\(K_r\).  Every sufficiently fine open cover of \(K\) therefore splits into
the disjoint union of covers of the individual \(K_r\).  Its nerve is the
disjoint union of the corresponding nerves.  Taking first cohomology and
then the direct limit defining \v Cech cohomology gives

\[
  \check H^1(K;\mathbb Z)
  \cong
  \bigoplus_{r=0}^N
  \check H^1(K_r;\mathbb Z)
  =0.
\tag{4.4}
\]

A second application of (2.1) gives

\[
  \widetilde H_0(S^2\setminus K;\mathbb Z)=0.
\tag{4.5}
\]

For a nonempty space, vanishing reduced \(H_0\) is equivalent to
path-component connectedness at the level detected by singular \(H_0\);
in particular it implies connectedness.  Thus (4.1) is connected.
\(\square\)

### Lemma 4.2 (Jordan-localized common complement)

Let \(U\) be a Jordan disk and let
\(K_1,\ldots,K_N\Subset U\) be pairwise disjoint full continua.  Then

\[
  U\setminus\bigcup_{r=1}^N K_r
\tag{4.6}
\]

is connected and hence path connected.

#### Proof

Let

\[
  K_0=S^2\setminus U.
\tag{4.7}
\]

Because \(U\) is a Jordan disk, \(K_0\) is a nonempty full continuum.
Compact containment makes \(K_0,K_1,\ldots,K_N\) pairwise disjoint.  Lemma
4.1 says that their common complement is connected.  That complement is
exactly (4.6).  Finally, (4.6) is open in the plane.  Every connected open
subset of the plane is locally path connected and therefore path connected.
\(\square\)

### Theorem 4.3 (Augmented-Atom Common-Domain Theorem)

Every augmented-atom packet in the sense of Definition 3.1 determines one
component \(\Omega_0\) of \(\Omega_{\rm free}\) having simultaneous
singleton ports to every \(A_i\).  Consequently:

1. `VIRTUAL_COMMON_FREE_COMPONENT` holds for that frozen block and horizon;
2. the Protected Free-Component Criterion supplies a protected regulated
   connector; and
3. after one such connector is selected, transporting that connector and
   its protected access marking by a univalent map transporting the complete
   augmented packet gives a valid target connector.  No canonical choice of
   the spanning tree is asserted.

#### Proof

Every member of (3.8) is a full continuum, the family is finite and
pairwise disjoint, and all members are compactly contained in \(U\).
Lemma 4.2 therefore gives that \(\Omega_{\rm aug}\) is connected.

Coverage (3.7) implies

\[
  \Omega_{\rm aug}\subset\Omega_{\rm free}.
\tag{4.8}
\]

Hence the connected set \(\Omega_{\rm aug}\) lies in a unique component
\(\Omega_0\) of \(\Omega_{\rm free}\).  By (3.9),

\[
  \alpha_i((0,1])\subset\Omega_{\rm aug}\subset\Omega_0.
\tag{4.9}
\]

Also,

\[
  \alpha_i\cap A_i
  \subset
  \alpha_i\cap\widehat A_i
  =\{x_i\},
\tag{4.10}
\]

and \(x_i\in A_i\), so equality holds in (4.10).  The arcs are pairwise
disjoint and miss the other augmented packets, hence the other atoms.  They
are exactly simultaneous singleton ports in the sense of Definition 2.1 of
`virtual_protected_routing_domain.md`.

The first conclusion is the definition of `VCFC`.  The second follows from
the Protected Free-Component Criterion and the Protected Regulated Connector
Realization Theorem.

For the third, an orientation-preserving conformal homeomorphism of Jordan
disks extends over their Jordan boundaries and can be glued, by the
Schoenflies theorem, to an orientation-preserving sphere homeomorphism.
Consequently it transports full continua to full continua, commutes with
taking the filled hull, preserves pairwise disjointness, and carries the
port arcs to port arcs.  It maps \(\Omega_{\rm aug}\) homeomorphically to
the augmented free domain at the target.  The univalent naturality clauses
of the two previous theorems then transport any selected connector and its
complete protected marking.
\(\square\)

### Corollary 4.4 (no local-connectivity or width hypothesis)

Theorem 4.3 requires neither local connectivity of an \(A_i\) nor a lower
bound on any Euclidean distance or extremal width.

#### Proof

The proof uses arbitrary-compacta \v Cech-Alexander duality and the explicit
arcs (3.9).  No boundary extension to \(A_i\) and no quantitative separation
estimate occurs.
\(\square\)

### Corollary 4.5 (period independence of the implication)

The logical implication

\[
  \text{augmented-atom packet}
  \Longrightarrow
  \text{common free component}
\tag{4.11}
\]

has no constant depending on satellite period, rotation number, or corridor
length.

This does **not** bound the number of augmented atoms, obstacles, ports, or
ribbon sides.  Such a bound is a separate part of `VPRC-7` and UPTCR-1.

## 5. Collision audit for an attempted packet

For a frozen finite inventory define

\[
  \chi_{\rm aug}
  =
  (\chi_{\rm cov},\chi_{\rm conn},\chi_{\rm merge},
   \chi_{\rm loc},\chi_{\rm port}).
\tag{5.1}
\]

The coordinates have the following meanings.

1. \(\chi_{\rm cov}\ne0\): some frozen forbidden component has no typed
   assignment, or (3.7) fails.
2. \(\chi_{\rm conn}\ne0\): an assigned atom or obstacle seed is not
   connected, so its fullification is not certified as one full continuum.
3. \(\chi_{\rm merge}\ne0\): two completed atom/obstacle packets intersect
   after fullification.
4. \(\chi_{\rm loc}\ne0\): a completed packet meets
   \(S^2\setminus U\).
5. \(\chi_{\rm port}\ne0\): at least one original atom has no declared
   permissible arc satisfying (3.9), or two required port arcs cannot be
   represented disjointly.

If \(\chi_{\rm aug}=0\), Theorem 4.3 applies.  If
\(\chi_{\rm aug}\ne0\), this **specific sufficient route** fails.  It is not
valid to infer that `VCFC` itself fails: a different decomposition of the
same frozen free domain may still display a common component.  Only the
separator certificate of Corollary 4.2 in
`virtual_protected_routing_domain.md` refutes `VCFC` in the current
localization.

The first failed item in the source-ordered inventory must be recorded as

\[
  \mathfrak F_{\rm aug}
  =
  (B,j,Y,\operatorname{type}(Y),\tau(Y),w(Y),\varsigma(Y),
   i,k,\chi_{\rm aug},\Gamma_i,\Gamma_k,\mathcal L).
\tag{5.2}
\]

Here \(B,j\) identify the block and stage; \(Y\) is the first failed
component, collar, or filled complementary component; \(\tau(Y)\) is its
full attachment/separation trace; \(w(Y)\) is its complete return word;
\(\varsigma(Y)\) is its selected sheet; \(i,k\) name the first packets
merged or separated when applicable; \(\Gamma_i,\Gamma_k\) are the affected
access chains; and \(\mathcal L=U\) is the authorized localization.

The collision coordinate determines the first repair that must be tested:

- coverage: complete the proof-use inventory;
- disconnected assignment: split by an actual dynamical rule or add a
  justified connector;
- merger: revise the sheet set, root, or block stopping time;
- localization escape: enlarge or retime the localization;
- port loss: choose a different dynamically justified free access before
  its last proof use, or retime the block.

Deleting a required atom or protected access is not a repair.

## 6. Why the published virtual data do not close the certificate

The source comparison is clause-by-clause.

| Packet clause | Dudko Section 4.5 | KKL native primitive carrier | Virtual conclusion |
|---|---|---|---|
| Complete typed assignment | Not defined | Native carrier and marking only | Open |
| Connected assigned seeds | “Connected hull” only for the selected virtual set | True for native Hubbard-tree pieces | Open for partial virtual pieces |
| Fullification coverage | Not stated | Built into native full carrier | Open |
| Pairwise disjoint completion | Not stated | Available for the native small-Julia cycle under KKL hypotheses | Open |
| Localization containment | Not stated | Native \(\psi\)-ql localization | Open |
| Explicit free port per original atom | Not stated | Native tree-side marking | Open |
| Future completeness | Finite first returns proposed, horizon not formalized | Native complete proof horizon | Open |

Thus the first unsupported implication is

\[
  \text{Dudko connected virtual hull}
  \centernot\Longrightarrow
  \text{augmented-atom packet}.
\tag{6.1}
\]

This is not an argument from silence alone.  The next proposition gives two
frozen routing extensions with the same connected package data and opposite
`VCFC` outcomes.

## 7. Exact underdetermination model

### Proposition 7.1 (connected-hull data do not determine `VCFC`)

There are two finite frozen routing systems having the same Jordan
localization, the same two full root-shadow atoms, the same connected full
carrier containing them, and the same identity package dynamics, such that
one satisfies `VCFC` and the other does not.

#### Proof

Let

\[
  U=\{z:|z|<4\},
  \qquad
  A_1=\{z:|z|\le 1/4\},
  \qquad
  A_2=\{z:|z-2|\le 1/4\}.
\tag{7.1}
\]

The atoms are disjoint full continua.  Let \(H\) be the filled hull of

\[
  A_1\cup[1/4,7/4]\cup A_2.
\tag{7.2}
\]

It is a connected full carrier containing the same package in both
systems.  Put identity dynamics on the package.

For the positive system, take \(Q_{\rm dyn}=\varnothing\).  The two atoms
are already a pairwise disjoint augmented packet.  Explicit outward radial
arcs from \(-1/4\) to \(-1/2\) and from \(9/4\) to \(5/2\), shortened and
slightly separated if desired, satisfy (3.9).  Theorem 4.3 proves `VCFC`.

For the negative system, add the closed annulus

\[
  R=\{z:1/2\le |z|\le1\}
\tag{7.3}
\]

to \(Q_{\rm dyn}\).  It is compact, lies in \(U\), and misses both atoms.
The component

\[
  \{|z|<1/2\}\setminus A_1
\tag{7.4}
\]

of \(U\setminus(A_1\cup A_2\cup R)\) accesses \(A_1\) but cannot access
\(A_2\).  Every component outside \(R\) can access \(A_2\) but cannot access
\(A_1\).  Any path from the inside of \(R\) to its outside meets \(R\).
Therefore no free-domain component has simultaneous ports to both atoms,
and `VCFC` fails by the Protected Free-Component Criterion.

The connected carrier (7.2), the atoms, and the identity package dynamics
are unchanged.  Only the frozen obstacle inventory differs.  Hence those
common data do not determine `VCFC`.
\(\square\)

### Corollary 7.2 (the annular failure is visible to the collision audit)

For the negative system in Proposition 7.1:

1. treating \(R\) as a separated obstacle makes
   \(\operatorname{Fill}(R)=\{|z|\le1\}\), which intersects \(A_1\), so
   \(\chi_{\rm merge}\ne0\); while
2. assigning \(R\) to \(A_1\) gives
   \(\widehat A_1=\{|z|\le1\}\), so \(A_1\) lies in the interior of
   \(\widehat A_1\) and no arc can satisfy
   \(\alpha_1\cap\widehat A_1=\{x_1\}\); hence
   \(\chi_{\rm port}\ne0\).

Thus fullification cannot hide the separator.

This is a topological underdetermination model, not a counterexample to a
published virtual-renormalization theorem and not an actual quadratic
virtual-Molecule block.

## 8. Exact remaining dynamical proposition

### `VIRTUAL_AUGMENTED_ATOM_PORT_CERTIFICATE` (`VAAPC`; open)

For every actual virtual-Molecule Wave block and complete finite Wave
horizon, after the final future root enlargement:

1. the root shadows form a finite family of pairwise disjoint full touching
   clusters \(A_i\);
2. every proof-used terminal collar, ambient component, critical exclusion,
   and localization-forbidden component has one source-faithful typed
   assignment;
3. every assigned atom seed and obstacle seed is compact and connected;
4. their fullifications cover the frozen forbidden inventory, remain
   pairwise disjoint, and stay compactly inside the authorized localization;
5. every \(A_i\) retains an explicitly represented unprotected singleton
   access arc from the augmented free domain;
6. the port arcs are pairwise disjoint and survive through the last proof
   use;
7. the construction is equivariant under all selected univalent corridor
   branches; and
8. the incidence of atoms, obstacles, and ports is uniformly bounded or
   admits a proved future-faithful compression independent of satellite
   period, rotation number, and corridor length.

Items 1--7 imply `VCFC` by Theorem 4.3.  Item 8 is additionally required by
`VIRTUAL_PROTECTED_ROUTING_CERTIFICATE` and UPTCR-1; it does not follow from
the qualitative planar theorem.

The source-independent closure mechanics in this statement are now settled
by the [Fixed-Packet Closure and Port Audit](augmented_packet_closure_audit.md).
For a fixed typed assignment, its final fullifications are independent of
processing order; filled mergers, localization escapes, and empty
original-atom exposure loci are monotone-persistent; and individual
unprotected ports can be truncated to a pairwise disjoint simultaneous
family.  Thus the remaining analytic input is exactly:

1. the finite stopped Wave horizon and finality certificate
   (`VIRTUAL_WAVE_HORIZON_CERTIFICATE`), followed by the frozen actual
   component inventory and typed assignment (`VAAPC-I`);
2. zero collision for the unique completed packets (`VAAPC-C`);
3. one actual unprotected exposure arc or metric collar witness on every
   original atom (`VAAPC-P`);
4. full-packet transport through the complete horizon (`VAAPC-H`); and
5. uniform incidence or a future-faithful compression (`VAAPC-U`).

If `VAAPC` fails, the proof must emit (5.2).  If the failed packet also
produces an actual free-domain separator, it must additionally emit the
separator tuple \(\mathfrak F_{\rm free}\) from
`virtual_protected_routing_domain.md`.  Without an actual source-defined
block and complete obstacle inventory, neither tuple may be fabricated.

## 9. Adversarial cross-examination

| Attack | Result |
|---|---|
| Two disjoint disks, no extra forbidden set | Positive control.  The augmented complement is connected and explicit ports exist. |
| KKL native Hubbard tree | Positive control in KKL's published category; the native carrier supplies more structure than Definition 3.1. |
| Non-locally-connected atom | Allowed.  The proof uses \v Cech duality and requires only the declared access arc. |
| Full disjoint obstacles | Allowed.  Adding finitely many such obstacles leaves one connected complement. |
| Non-full annular obstacle | Rejected unless fullification is audited.  Proposition 7.1 shows a genuine separator. |
| Collar bridge joins two atoms | The assigned fullifications merge, so \(\chi_{\rm merge}\ne0\).  This refutes the packet, not automatically `VCFC`. |
| Fullification surrounds an atom | The original atom can become interior to its augmentation, causing \(\chi_{\rm port}\ne0\). |
| Augmented packet touches \(\partial U\) | Rejected by \(\chi_{\rm loc}\); Lemma 4.2 requires disjointness from \(S^2\setminus U\). |
| Each atom is accessible, but access arcs cross | Not silently repaired.  Pairwise disjoint representatives are a certificate clause. |
| All accessible points are protected | Rejected by \(\chi_{\rm port}\); a protected impression cannot be relabeled free. |
| Late root enlargement | The packet is built only after enlargement.  Any merger or lost port is re-audited. |
| Infinite accumulating obstacles | Outside the finite theorem unless they have a proved compact finite replacement preserving every proof-used access. |
| Vanishing analytic width | Not addressed.  The theorem is qualitative and does not prove collars of uniform modulus. |
| Rapidly increasing satellite period | The implication remains valid, but no uniform complexity bound follows. |
| Alternative decomposition succeeds after one packet fails | Permitted.  Nonzero \(\chi_{\rm aug}\) refutes only the attempted sufficient certificate. |

## 10. Skeptic audit

The following shortcuts were rejected.

1. **“Connected hull implies connected free domain.”**  False by
   Proposition 7.1.
2. **“Fullify every forbidden set separately.”**  Separate fullification
   can swallow another atom or erase its last port.
3. **“Pairwise disjoint seeds stay disjoint after filling.”**  False for an
   annulus surrounding another seed.
4. **“A boundary point is automatically accessible.”**  False without
   local connectivity; the port arc is explicit data.
5. **“Failure of this sufficient certificate refutes `VCFC`.”**  False
   unless the exact free-domain separator is also proved.
6. **“A qualitative planar theorem gives a uniform marking bound.”**  It
   does not control the number of packets or ports.
7. **“The in-preparation DKL citation can be imported.”**  No public theorem
   was available at the source-lock date.
8. **“The finite annular model is an actual dynamical counterexample.”**  It
   is only an underdetermination model for the stated public data.

## 11. Promotion decision and next proof move

Promote:

- `ALEXANDER_DUALITY_COMPACTA` as an imported topological theorem;
- `AUGMENTED_ATOM_COMMON_DOMAIN` as a proved internal theorem; and
- `AUGMENTED_PACKET_CLOSURE_AUDIT` as a proved internal theorem.

Add and keep open:

- `VIRTUAL_AUGMENTED_ATOM_PORT_CERTIFICATE`.

Keep open:

- `VIRTUAL_COMMON_FREE_COMPONENT`;
- `VIRTUAL_PROTECTED_ROUTING_CERTIFICATE`;
- `VIRTUAL_ROOT_CARRIER_SEPARATION`;
- `VIRTUAL_CANONICAL_INTERFACE_CARRIER`;
- UPTCR-1; and
- MLC.

The immediate next analytic step is now finite and falsifiable: for the
first source-defined virtual-Molecule block, prove the stopped horizon and
extension-stability clauses in
`vaapc_inventory_source_audit.md`, construct the remaining typed part of
`VAAPC-I`, compute
the unique completed packets, and prove `VAAPC-C` and `VAAPC-P`; otherwise
emit the chamber-refined first failure tuple in equation (9.1) or (9.2) of
`augmented_packet_closure_audit.md`.  The published public data do not yet
specify enough geometry to perform that enumeration.

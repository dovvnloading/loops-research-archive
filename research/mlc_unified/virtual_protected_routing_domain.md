# Virtual protected routing domain

## 1. Purpose and verdict

This pass attacks Item 2 of the open Virtual Protected Routing Certificate
(`VPRC`): the existence of a regulated root connector avoiding every
proof-used protected collar.

The topological selection problem has an exact answer.  After the complete
finite proof-use inventory is frozen, an admissible protected connector
exists if and only if all required atoms have simultaneous singleton ports
from one component of the free routing domain.  This is proved below without
local connectivity of the atoms.

The theorem does **not** prove that an actual virtual-Molecule block has such
a component.  Dudko's public description does not define the collars,
regulated edges, or complete Wave marking needed to formulate that fact, and
the Dudko--Kahn--Lyubich virtual-renormalization manuscript is still cited by
KKL as in preparation.  The new exact dynamical obligation is therefore
`VIRTUAL_COMMON_FREE_COMPONENT`.

Verdict:

- `PROTECTED_FREE_COMPONENT_CRITERION`: **proved**;
- `VIRTUAL_COMMON_FREE_COMPONENT`: **open**;
- `VIRTUAL_PROTECTED_ROUTING_CERTIFICATE`: **open**;
- UPTCR and MLC: **open**.

## 2. Frozen routing data

Let \(U\Subset\mathbb C\) be a Jordan disk.  Let
\[
  A_1,\ldots,A_s\Subset U
\tag{2.1}
\]
be pairwise disjoint nonempty full continua.  They are the touching clusters
of all root shadows retained after the final future enlargement.

Let \(Z\Subset U\) be the union of the closed critical-value exclusion,
separated obstacles, and localization-forbidden sets.  For every proof-used
protected prime end choose a terminal crosscut domain
\[
  D_{i,a}\Subset U.
\tag{2.2}
\]
The terminal domains are selected sides of pairwise disjoint crosscuts and
are truncated at the final proof-use depth.  Define the closed forbidden
set
\[
  Q
  =
  Z\cup\bigcup_{i=1}^{s}A_i
  \cup\bigcup_{i,a}\overline{D_{i,a}}
\tag{2.3}
\]
and the **free routing domain**
\[
  \Omega_{\rm free}=U\setminus Q.
\tag{2.4}
\]
If an access collar has its impression in \(A_i\), its closure may meet
\(A_i\); this causes no ambiguity because both sets are removed in (2.3).
The data are finite, so \(Q\) is relatively closed in \(U\) and
\(\Omega_{\rm free}\) is open.

### Definition 2.1 (simultaneous singleton ports)

A component \(\Omega_0\) of \(\Omega_{\rm free}\) has simultaneous singleton
ports to (2.1) if there are pairwise disjoint Jordan arcs
\[
  \alpha_i:[0,1]\longrightarrow U
\tag{2.5}
\]
such that
\[
  \alpha_i(0)=x_i\in A_i,\qquad
  \alpha_i\cap A_i=\{x_i\},\qquad
  \alpha_i((0,1])\subset\Omega_0,
\tag{2.6}
\]
and \(\alpha_i\) misses every other atom.  The point \(x_i\) is a declared
free port, not the impression of a protected chain.

This is an accessibility condition, not local connectivity.  Only the
finitely many declared ports must be represented by arcs.

## 3. A finite tree in an open planar component

### Lemma 3.1a (a finite family of one-ended slits is nonseparating)

Let \(\Omega\subset\mathbb C\) be a domain and let
\(\delta_1,\ldots,\delta_s:[0,1]\to\overline\Omega\) be pairwise disjoint
Jordan arcs with
\[
  \delta_i(0)\in\partial\Omega,
  \qquad
  \delta_i((0,1])\subset\Omega.
\]
Then
\[
  \Omega\setminus\bigcup_i\delta_i((0,1])
\tag{3.1}
\]
is path connected.

#### Proof

It is enough to treat one slit and then induct, because the slits are
pairwise disjoint and each remaining slit is again one-ended in the domain
obtained after the preceding removals.

Fix \(x,y\) outside one slit \(\delta((0,1])\). Choose a polygonal path
\(\gamma\subset\Omega\) from \(x\) to \(y\). Its image is compactly
contained in \(\Omega\), so for some \(\varepsilon>0\) it misses
\(\delta((0,\varepsilon))\). After a perturbation relative to \(x,y\), it
meets the compact embedded arc \(\delta([\varepsilon,1])\) in finitely many
transverse points and misses its endpoints.

Take a thin closed topological rectangle around
\(\delta([\varepsilon,1])\), contained in \(\Omega\), whose two long sides
avoid \(\delta\). The two long sides join around the free endpoint
\(\delta(1)\). Replace every portion of \(\gamma\) crossing the rectangle
by a path on those sides, using the small semicircle around \(\delta(1)\)
whenever the replacement must pass from one side to the other. The
resulting path has the same endpoints and avoids the entire slit. This
proves the one-slit assertion. Repeating the construction for the finite
disjoint family proves (3.1). \(\square\)

### Lemma 3.1b (finite port forest extension)

Let \(\Omega\subset\mathbb C\) be open and connected, and let
\(\alpha_1,\ldots,\alpha_s\) be pairwise disjoint arcs whose interiors and
outer endpoints lie in \(\Omega\).  After shortening only their portions
inside \(\Omega\), there is a finite embedded tree \(G\Subset\Omega\) such
that
\[
  G\cup\bigcup_i\alpha_i
 \tag{3.2}
\]
is a tree and \(G\) joins all port arcs.

#### Proof

Choose \(t_i\in(0,1)\), discard \(\alpha_i((t_i,1])\), and retain the
shortened port arc \(\alpha_i([0,t_i])\).  A connected open subset of the
plane is polygonally connected.  The finitely many disjoint retained
  interiors \(\alpha_i((0,t_i])\) are one-ended slits: one endpoint tends to
  \(\partial\Omega\) while the other is free in \(\Omega\). Lemma 3.1a
  shows that their complement is path connected. Choose points immediately
  beyond the free endpoints and join
\(\alpha_1(t_1)\) to every \(\alpha_i(t_i)\) by finitely many polygonal arcs
whose interiors lie in the complement of the initial pieces.

Because the construction is finite and all chosen paths are compactly
contained in \(\Omega\), a sufficiently small general-position perturbation
relative to their endpoints has only finitely many transverse
intersections and misses the shortened port arcs except at their free
endpoints.  Subdivide at every intersection.  The union is a finite
connected planar graph containing those free endpoints.

Choose an inclusion-minimal connected subgraph containing one point on each
port arc.  It has no cycle, since deletion of an edge from a cycle would
preserve connectivity of all retained points.  It is therefore a finite
tree.  Truncate each \(\alpha_i\) at its first encounter with this tree and
absorb the remaining terminal segment into the tree.  The resulting union
has no cycle, meets every port arc exactly at its outer endpoint, and is
compactly contained in \(\Omega\). \(\square\)

No metric lower bound on the distance to \(\partial\Omega\) is asserted
uniformly over blocks.  Compact containment is obtained separately for each
finite certificate.

## 4. Exact protected routing criterion

### Theorem 4.1 (Protected Free-Component Criterion)

For the frozen data (2.1)--(2.4), the following are equivalent.

1. There is a protected ribbon-routing certificate in the sense of
   `protected_regulated_connector.md`, with one singleton attachment to
   every atom and with every connector edge avoiding \(Z\) and every
   terminal protected domain.
2. Some component \(\Omega_0\) of \(\Omega_{\rm free}\) has simultaneous
   singleton ports to all atoms.

When these conditions hold, the carrier
\[
  H
  =
  G\cup\bigcup_i\alpha_i\cup\bigcup_iA_i
\tag{4.1}
\]
is compact, connected, and full; every declared protected prime-end chain
survives injectively and in cyclic order; and its connector-side marking is
the boundary word of the finite ribbon tree.

#### Proof

Assume Item 1.  Delete the atoms from the connector and shorten each port
arc away from its attachment point.  The remaining connected tree lies in
\(\Omega_{\rm free}\), hence in one component \(\Omega_0\).  The original
port arcs, shortened if necessary, satisfy (2.5)--(2.6).  Thus Item 2 holds.

Conversely, assume Item 2 and choose the arcs (2.5). Lemma 3.1b supplies a
finite embedded tree \(G\Subset\Omega_0\) joining them.  Since
\(\Omega_0\cap Q=\varnothing\), every connector edge and every port interior
misses \(Z\), the other atoms, and all closed terminal collar domains.  The
union of \(G\) with the port arcs is a tree meeting each \(A_i\) in the
single point \(x_i\).  It is therefore a protected ribbon-routing
certificate.

The final assertions are exactly the Protected Regulated Connector
Realization Theorem: one-point tree attachments to pairwise disjoint full
continua remain full, while avoidance of the terminal domains preserves the
crosscut chains and their cyclic order. \(\square\)

### Corollary 4.2 (first separating-collar obstruction)

If the required atoms cannot all be simultaneously singly accessed from one
component of \(\Omega_{\rm free}\), no monotone connector enlargement
confined to the current localization can satisfy protected routing.

In particular, if a terminal protected collar or separated obstacle divides
the available free ports between distinct components of
\(\Omega_{\rm free}\), it is an exact obstruction.  Adding more connector
edges cannot repair it: every connected set joining the two port classes
must meet \(Q\).

#### Proof

The first statement is the contrapositive of Theorem 4.1.  For the second,
any connected connector joining different components of the complement of
\(Q\) must intersect \(Q\).  Because the offending part of \(Q\) is
protected or forbidden, such an intersection violates the certificate.
\(\square\)

### Corollary 4.3 (univalent naturality of the criterion)

Let \(\phi:U\to V\) be an orientation-preserving conformal homeomorphism of
Jordan disks transporting the complete frozen data.  Then \(\phi\) induces
a bijection between the components of the two free routing domains,
preserves simultaneous singleton accessibility, and transports the carrier
(4.1), its protected survival map, and its ribbon boundary order.

#### Proof

The map \(\phi\) is a homeomorphism, hence maps (2.3) to the transported
closed forbidden set and maps components of (2.4) bijectively.  It
transports the port arcs and the finite tree.  The univalent naturality
proposition for protected regulated connectors gives the remaining
statements. \(\square\)

## 5. Application to the virtual root

At the central-to-terminal anchor of an actual virtual-Molecule Wave block,
freeze the complete proof-use inventory before choosing the root carrier:

1. form the touching clusters of every final root shadow;
2. insert every protected terminal crosscut domain through its final proof
   use;
3. insert the critical-value exclusion, separated obstacles, and the
   boundary of the authorized localization; and
4. form \(\Omega_{\rm free}\) by (2.4).

Theorem 4.1 proves that the connector part of `VPRC-2` is equivalent to one
check:

> **Virtual Common Free-Component Certificate.**  Some component
> \(\Omega_0\) of the completed \(\Omega_{\rm free}\) has simultaneous
> singleton ports to every root-shadow cluster.

Only after this check is passed may the connector be built.  The root
component-routing and critical-word clauses of
`root_pullback_virtual_carrier.md` must then be verified independently.

This order matters.  A later root shadow, protected access, or obstacle can
enlarge \(Q\), split the formerly selected \(\Omega_0\), or remove a free
port.  Thus the common component must be selected after future completion,
not stage by stage.

## 6. Source-hypothesis audit

The public sources do not prove the Virtual Common Free-Component
Certificate.

- Dudko's Interpolation Problem 4.4 defines the proposed virtual objects
  only as connected hulls of the corresponding Cantor small Julia sets
  containing a finite critical-orbit segment.  It does not define
  proof-used terminal collars, singleton free ports, or a component of their
  complement.
- KKL Sections 2.5--2.6 construct the native primitive Hubbard tree and its
  ideal marking, including a lift from a rational-lamination model in the
  non-locally-connected case.  Their proper central translation statement
  later uses actual equality of native pulled and immersed tree components.
  It is not a theorem for Dudko's partial virtual packages.
- KKL's reference list still records Dudko--Kahn--Lyubich,
  *Virtual renormalization: interpolating between primitive and satelite
  regimes*, as “in preparation.”

Consequently, the common-component assertion cannot be imported, and the
bare phrase “connected hull” cannot prove it.  Two connected full hulls
containing the same finite package may route on opposite sides of a
protected collar; the protected-access collision in
`canonical_virtual_interface_carrier.md` gives an analytic model where
monotone absorption erases the access.

## 7. Exact open certificate and failure record

### Virtual Common Free-Component (`VCFC`; open)

For every actual virtual-Molecule block and complete Wave horizon, the
completed root-shadow atoms and proof-used forbidden data determine a free
routing domain having one component with simultaneous singleton ports to
all atoms.  The component and ports remain valid after the final root
enlargement and avoid the critical value on every declared degree-one
target.

A failed proof must stop at
\[
  \mathfrak F_{\rm free}
  =
  (B,j,Q_*,\Omega^-,\Omega^+,A^-,A^+,\Gamma_*,\tau_*,w_*,\mathcal L),
\tag{7.1}
\]
where:

- \(B,j\) identify the block and first failed stage;
- \(Q_*\) is the first collar, obstacle, critical exclusion, or localization
  boundary whose insertion destroys common accessibility;
- \(\Omega^-\) is the free component before that insertion and
  \(\Omega^+\) is the resulting component partition;
- \(A^-,A^+\) are the first required atoms placed in different components;
- \(\Gamma_*\) is the protected chain when \(Q_*\) is a collar;
- \(\tau_*\) is the complete attachment/separation trace of \(Q_*\);
- \(w_*\) is its return word and selected sheet address; and
- \(\mathcal L\) is the authorized localization.

The required repair is determined geometrically:

- a protected collar separator requires block retiming or a different free
  port justified before the access's last proof use;
- an obstacle separator requires a new absorb-or-separate decision;
- a critical exclusion separator requires moving the quadratic stopping
  stage;
- a localization-boundary separator requires a new localization; and
- a late root-shadow separator requires a future-complete root selection.

Deleting either separated atom or a proof-used access is not a repair.

## 8. Adversarial cross-examination

| Attack | Result |
|---|---|
| KKL native Hubbard tree | Positive control.  Its already constructed native tree supplies the common component and ports in its published category. |
| Upper-half-disk protected-access collision | Fails VCFC: the forced absorbed excess occupies the protected upper collar; no allowed monotone enlargement restores that access. |
| Annular or multiply connected free domain | Allowed.  The theorem needs one component, not simple connectivity; polygonal paths inside it give a finite graph and spanning tree. |
| Non-locally-connected atom | Allowed only when the declared singleton port arc exists.  No boundary local connectivity is inferred. |
| Two atoms individually accessible but only from different components | Rejected.  Individual accessibility does not imply simultaneous accessibility. |
| Connector paths cross | Harmless before reduction.  Subdivide the finite general-position graph and take a spanning tree. |
| A connector loop surrounds a protected collar | Removed by the spanning-tree reduction; no fullification across the loop is needed. |
| Late future access or root shadow | The free domain is formed only after the complete proof-use inventory.  Earlier common components carry no certificate. |
| Infinitely accumulating ambient pieces | Outside the theorem unless the proof-use forbidden union is proved relatively closed and the required finite horizon is justified. |
| Rapidly increasing satellite period | The existence theorem is qualitative.  It gives no uniform atom, port, or side bound; `VPRC-7` remains open. |
| Collision-free topology but vanishing analytic width | Not addressed.  Width calibration and analytic collars remain later gates. |

## 9. Promotion decision

Promote:

- `PROTECTED_FREE_COMPONENT_CRITERION`.

Keep open:

- `VIRTUAL_COMMON_FREE_COMPONENT`;
- `VIRTUAL_PROTECTED_ROUTING_CERTIFICATE`;
- `VIRTUAL_ROOT_CARRIER_SEPARATION`;
- `VIRTUAL_CANONICAL_INTERFACE_CARRIER`;
- UPTCR-1; and
- MLC.

The immediate next analytic target is no longer an arbitrary connector.  It
is to prove VCFC for the first actual virtual-Molecule block using a
source-complete definition of that block, or to emit the first separator
tuple (7.1).

## 10. Augmented-atom reduction update

`virtual_common_free_component.md` proves a sufficient route to VCFC.
After the frozen forbidden pieces are assigned to connected atom seeds or
connected separated-obstacle seeds, fullify the seeds.  If the resulting
full continua:

1. cover the complete forbidden inventory;
2. are pairwise disjoint and compactly contained in the Jordan
   localization; and
3. leave one explicit pairwise disjoint unprotected singleton port on every
   original atom,

then their common complement is connected.  The proof uses the
arbitrary-compacta form of Alexander duality, so no local connectivity is
assumed.  All port interiors lie in that connected augmented complement and
hence in one component of \(\Omega_{\rm free}\).  Theorem 4.1 then supplies
the protected connector.

This promotes `AUGMENTED_ATOM_COMMON_DOMAIN`, not VCFC.  The actual
source-faithful construction is the open
`VIRTUAL_AUGMENTED_ATOM_PORT_CERTIFICATE`.  Its collision vector records
coverage failure, disconnected assignment, post-fullification merger,
localization escape, and port loss.  A nonzero vector refutes only the
attempted sufficient packet; VCFC itself is refuted only by an actual
separator tuple (7.1).

The immediate next block-level task is therefore to construct the augmented
packet from an actual source-defined virtual-Molecule block, or emit its
first augmented collision together with (7.1) whenever the original free
domain is genuinely separated.

The fixed-packet closure audit in
`augmented_packet_closure_audit.md` proves that the completed packets do not
depend on processing order and that individual unprotected ports, once
they exist, can be truncated to a pairwise disjoint family.  Accordingly,
the live task first requires the stopped-horizon and extension-stability
input `VIRTUAL_WAVE_HORIZON_CERTIFICATE` from
`vaapc_inventory_source_audit.md`.  It must then construct the actual typed inventory, prove zero
collision of its unique closure and original-atom exposure, and then close
complete-horizon transport and uniform incidence.

# Research Push VI
## Nested-separator contact closure, frozen-collar calculus, and the exact physical response cocycle

**Status.** This note does not prove the Mandelbrot local connectivity conjecture. It proves a new geometric and variational method for the first direct-decoration pullback system. The method removes the need for an all-pairs historical contact graph: the complete effect of every past shell on every future shell is carried by the current nested separator and its exact Dirichlet-to-Neumann response. The method captures nonconsecutive bypasses rather than assuming them away, works with the actual binary \(f^q\)-package, and retains word-dependent presentation maps exactly. The largest remaining obstruction is now quantitative: universal compactness/strict contraction and Value/WAD observability of the resulting contact-aware response cocycle across unbounded mixed blocks.

---

# 1. Source lock and corrected package

Fix the first direct-decoration system

\[
P=Y^{(n-1)q+1},\qquad g=f^q.
\]

Use only the two actual univalent pullbacks

\[
Q_L,Q_R\subset P,\qquad g:Q_a\longrightarrow P,
\quad a\in\mathcal A:=\{L,R\}.
\]

This is the binary package used by the existing direct-decoration rooted-end compactification. It is not identified with the separate \(2^n\)-element family of \(f^{nq}\)-pullbacks from the decoration source.

Let

\[
\phi_a=(g|_{Q_a})^{-1}:P\longrightarrow Q_a.
\]

For a word \(w=a_1\cdots a_m\), define

\[
\phi_w=\phi_{a_1}\circ\cdots\circ\phi_{a_m},\qquad
D_w=\phi_w(P),\qquad
h_w=g^m|_{D_w}:D_w\to P.
\]

For one address prefix \(w_j=a_1\cdots a_j\), write

\[
D_j=D_{w_j},\qquad D_0=P.
\]

Then

\[
D_0\supset D_1\supset\cdots\supset D_H
\tag{1.1}
\]

is a nested chain of closed Jordan puzzle disks. Their boundaries are finite unions of ray and equipotential arcs. We do **not** assume that \(\partial D_j\cap\partial D_{j+1}\) is one arc, connected, or empty. The finite common refinement of the actual boundary graphs is used instead.

---

# 2. The separator is the exact all-depth contact state

Define the accumulated open prefix

\[
\Omega_j=\operatorname{int}D_0\setminus D_j
\tag{2.1}
\]

and the next open shell

\[
S_{j+1}=\operatorname{int}D_j\setminus D_{j+1}.
\tag{2.2}
\]

The sets may have several connected components. This causes no difficulty: the response is a multi-port response on all components.

## Theorem 2.1 - Nested-separator Markov property

For every finite nested chain (1.1) and every \(j<H\):

1. \(\Omega_j\) and \(S_{j+1}\) are disjoint open sets;
2. every contact between their closures lies on the current separator:
   \[
   \overline{\Omega_j}\cap\overline{S_{j+1}}
   \subset\partial D_j;
   \tag{2.3}
   \]
3. away from the finite boundary vertices, the active interface is
   \[
   I_j=
   \bigl(\partial D_j\cap\operatorname{int}D_0\bigr)
   \setminus D_{j+1};
   \tag{2.4}
   \]
4. Sobolev gluing of \(\Omega_j\) and \(S_{j+1}\) along equal traces on \(I_j\) reconstructs
   \[
   \Omega_{j+1}=\operatorname{int}D_0\setminus D_{j+1};
   \tag{2.5}
   \]
5. for every \(k>j\), every contact of \(\overline{\Omega_j}\) with the future shell \(\overline{S_k}\) lies on \(\partial D_j\).

### Proof

The first statement follows from

\[
S_{j+1}\subset\operatorname{int}D_j,
\qquad
\Omega_j\subset\operatorname{int}D_0\setminus D_j.
\]

If \(x\) lies in both closures, approach from \(S_{j+1}\) puts \(x\in D_j\), while approach from \(\Omega_j\) puts \(x\) in the closure of the complement of \(D_j\). Thus \(x\in\partial D_j\), proving (2.3).

At a nonvertex point of \(\partial D_j\), the prefix approaches from the exterior side of \(D_j\) exactly when the point lies in \(\operatorname{int}D_0\). The new shell approaches from the interior side exactly when the point is not contained in the closed child \(D_{j+1}\). This is (2.4).

Ray/equipotential boundary arcs are piecewise analytic. Finite corner sets have zero relevance for the \(H^1\) patching relation. On every open interface arc, the two pieces occupy opposite sides. Hence pairs of \(H^1\)-functions patch to one \(H^1\)-function precisely when their traces agree on \(I_j\), and Dirichlet energy adds. The union after restoring the interface is (2.5).

Finally, \(S_k\subset D_j\) for \(k>j\), while \(\Omega_j\) lies outside \(D_j\). Repeating the closure argument proves the last statement. \(\square\)

## Why this defeats the audit bypass

The alternating-rectangle example has a nonconsecutive \(C_1\)-to-\(C_3\) contact. At the stage where \(C_3\) is attached, however, \(C_1\cup C_2\) is the accumulated prefix and the entire bypass arc lies on the current separator \(\partial D_2\). The recursion therefore glues it exactly. The failed model was **shell-to-shell** composition; the correct model is **prefix-to-next-shell** composition.

---

# 3. Frozen collars and obstacles do not destroy the separator theorem

Let \(Z\subset\overline{D_0}\) be a finite, horizon-frozen union of regular protected collar tails, obstacle interfaces, ideal-interval walls, and declared electrode arcs. Define the conducting pieces

\[
\Omega_j^Z=(\operatorname{int}D_0\setminus D_j)\setminus Z,
\qquad
S_{j+1}^Z=(\operatorname{int}D_j\setminus D_{j+1})\setminus Z.
\tag{3.1}
\]

## Theorem 3.1 - Frozen-collar separator calculus

Every common contact of \(\overline{\Omega_j^Z}\) and \(\overline{S_{j+1}^Z}\) still lies on \(\partial D_j\). The active glue is the part of \(I_j\) not declared forbidden by \(Z\). Every boundary arc of \(Z\) is retained as a side port, obstacle wall, or prescribed boundary condition; it is never silently glued or discarded.

### Proof

Removing \(Z\) can delete approach regions but cannot create a point that is simultaneously approached from the exterior and interior of the closed separator \(D_j\) away from \(\partial D_j\). Thus (2.3) remains true. The rest is the standard finite regular-interface patching theorem after refining \(I_j\) by the finitely many endpoints of \(Z\cap\partial D_j\). \(\square\)

This theorem does not construct the global future inventory \(Z\). It proves that, once VAAPC-I or another source theorem freezes a finite inventory, its physical collar calculus is exact and does not require a no-bypass hypothesis.

---

# 4. Boundary persistence is interval-convex

For a finite horizon, take the common refinement

\[
\Gamma_H=\bigcup_{j=0}^H\partial D_j.
\]

Remove all vertices. A boundary atom is a connected open arc of the remainder.

## Theorem 4.1 - Persistence interval theorem

For one boundary atom \(J\), let

\[
\mathcal I(J)=\{j:J\subset\partial D_j\}.
\]

Then \(\mathcal I(J)\) is empty or an integer interval.

### Proof

Suppose \(i<k\) lie in \(\mathcal I(J)\), and let \(i<j<k\). Since

\[
D_k\subset D_j\subset D_i,
\]

we have \(J\subset D_j\). If a point of \(J\) were interior to \(D_j\), a small disk around it would lie in \(D_j\subset D_i\), contradicting its membership in \(\partial D_i\). Therefore \(J\subset\partial D_j\). \(\square\)

## Corollary 4.2 - No physical port reactivation

If \(\mathcal I(J)=[a,b]\), then the arc is transported along consecutive shared boundaries from levels \(a\) through \(b\), becomes active exactly when the nested boundary leaves it, and can never reappear later. Apparent nonconsecutive contacts are maximal persistence intervals viewed from a shell-only bookkeeping system.

---

# 5. Root-normalized finite contact automaton

Let \(V_{\rm geom}\subset\partial P\) contain every endpoint of:

- every common subarc of \(\partial P\) with \(\partial Q_L\) or \(\partial Q_R\);
- every ray/equipotential corner of the three root pieces;
- every image endpoint needed to make the maps below atom maps.

The set is finite. Put

\[
\mathcal E=\pi_0(\partial P\setminus V_{\rm geom}),
\qquad M=|\mathcal E|.
\tag{5.1}
\]

Proof-used access, obstacle, electrode, and enlargement endpoints may further refine the trace ports for a finite horizon, but they do not change the structural contact mask.

For \(a\in\{L,R\}\), let \(A_a\subset\mathcal E\) be the root atoms whose physical arcs are shared by \(\partial P\) and \(\partial Q_a\). Refine \(V_{\rm geom}\) so that

\[
\tau_a:A_a\to\mathcal E,
\qquad \tau_a(J)=g(J),
\tag{5.2}
\]

is an oriented atom map. Because \(g|_{Q_a}\) is a homeomorphism, \(\tau_a\) is injective on each open atom.

At level \(j\), define

\[
R_j=
\{J\in\mathcal E:
 h_{w_j}^{-1}(J)\subset\partial D_0\}.
\tag{5.3}
\]

This mask records exactly where the current separator still coincides with the fixed root boundary, so the accumulated prefix has no exterior-side trace.

## Theorem 5.1 - Exact contact-mask recursion

For the next symbol \(a=a_{j+1}\),

\[
\boxed{R_{j+1}=\tau_a(R_j\cap A_a).}
\tag{5.4}
\]

### Proof

Let \(z\in\partial D_{j+1}\cap\partial D_0\) lie in an open atom. By persistence, \(z\in\partial D_j\). Put \(x=h_{w_j}(z)\). Then \(x\in R_j\), and because \(h_{w_j}(D_{j+1})=Q_a\), we have \(x\in\partial Q_a\). Hence \(x\in R_j\cap A_a\), while

\[
h_{w_{j+1}}(z)=g(x)=\tau_a(x).
\]

Conversely, if \(x\in R_j\cap A_a\), then \(h_{w_j}^{-1}(x)\) belongs simultaneously to \(\partial D_0\), \(\partial D_j\), and \(\partial D_{j+1}\), so its \(h_{w_{j+1}}\)-label lies in \(R_{j+1}\). \(\square\)

## Corollary 5.2 - Finite structural contact state

The complete geometric contact history factors through

\[
R_j\in 2^{\mathcal E},
\qquad
T_a(R)=\tau_a(R\cap A_a).
\tag{5.5}
\]

Thus a fixed direct-decoration block has at most \(2^M\) structural contact states, independent of address depth. This is a blockwise bound, not a universal bound over all decorations.

---

# 6. Four-way prefix/cell refinement

For a current mask \(R\) and next symbol \(a\), define

\[
\begin{aligned}
G(R,a)&=(\mathcal E\setminus R)\cap(\mathcal E\setminus A_a),\\
T(R,a)&=(\mathcal E\setminus R)\cap A_a,\\
O(R,a)&=R\cap(\mathcal E\setminus A_a),\\
Z(R,a)&=R\cap A_a.
\end{aligned}
\tag{6.1}
\]

These disjoint classes have exact physical meanings:

- **\(G\), genuine glue:** both accumulated prefix and new cell approach the arc; impose equality of traces and eliminate the internal interface.
- **\(T\), zero-energy transport:** the prefix approaches, while the new cell has no interior there because parent and child boundaries coincide; transport the trace to the child label \(\tau_a(J)\) with no cell energy.
- **\(O\), outer-only cell port:** the prefix is absent because the current separator still equals the root boundary, while the new cell opens there; couple to the fixed outer/root boundary data.
- **\(Z\), double inactive:** neither conducting piece approaches; transport it into the new root-shared mask \(\tau_a(Z)\).

A frozen collar/obstacle overlay simply subdivides these atoms and changes selected \(G\)-atoms into declared walls or side ports. It does not change the four structural approach types.

---

# 7. Exact Dirichlet response recursion

For every finite union \(B\) of regular active boundary arcs, use the intrinsic quotient trace space

\[
\mathcal T_\Omega(B)=
H^1(\Omega)/\{u:\operatorname{Tr}_B u=0\},
\tag{7.1}
\]

with the minimum-energy quotient norm. This avoids assuming an unproved Euclidean/Douglas equivalence on arbitrary wild Jordan boundaries.

Let \(q_j\) be the exact closed Dirichlet response of the actual frozen-inventory prefix \(\Omega_j^Z\) on:

- all fixed external proof terminals;
- the active atoms of the current separator, normalized by \(h_{w_j}\);
- every protected or proof-live side port.

Let \(c_a\) be the exact response of the fixed root cell

\[
(\operatorname{int}P\setminus Q_a)\setminus Z_a
\]

on its complete finite root overlay.

## Theorem 7.1 - Separator response recursion

There is an exact variational operation

\[
q_{j+1}=\mathfrak R_{a_{j+1},R_j}(q_j)
\tag{7.2}
\]

which:

1. glues equal traces on \(G(R_j,a_{j+1})\) not blocked by the frozen inventory;
2. transports \(T\)-traces by \(\tau_{a_{j+1}}\) with zero cell energy;
3. couples \(O\)-traces to fixed root-side data;
4. removes \(Z\) from the active DtN trace and updates the mask by (5.4);
5. retains every declared live side port;
6. minimizes over exactly the internal interface traces.

Its output is the Dirichlet response of the actual physical prefix \(\Omega_{j+1}^Z\). In particular, the output is a closed form.

### Proof

Transport the new shell by the actual conformal map \(h_{w_j}\); it becomes the fixed root cell for symbol \(a_{j+1}\). Theorems 2.1 and 3.1 identify the complete interface with the refined current separator. The four classes (6.1) are exactly the four possible approach patterns. Piecewise analytic Sobolev patching imposes equality only on the genuine glue atoms. Dirichlet energy adds, and minimizing internal traces gives the response of the actual union (2.5) with the frozen walls removed. Closedness follows from the actual-domain Dirichlet form; no abstract assertion that arbitrary quadratic-form pushforward preserves closedness is used. \(\square\)

## Theorem 7.2 - DtN Markov sufficiency

Suppose two accumulated prefixes have the same:

- current contact mask;
- external terminal labels;
- current separator trace-coordinate map;
- exact Dirichlet response form.

Then every common finite future continuation by the binary root-cell catalog produces identical external responses and identical live trace data.

### Proof

Every continuation is obtained by iterating the deterministic operations \(T_a\) and \(\mathfrak R_{a,R}\). These operations read no historical geometry beyond the displayed state. Induction on continuation length proves the claim. \(\square\)

This is the exact replacement for the audit's proposed all-pairs contact graph.

---

# 8. Genuine finite geometric live frontier

## Corollary 8.1

At every depth, every future direct-decoration cell can interact with the accumulated past only through the active atoms of the current separator. Their structural number is at most \(M\), independently of the word length.

An old physical side port not retained by the proof ledger and not represented on the current separator is separated from all future cells by \(D_j\) and is therefore genuinely unreachable. Eliminating it through the **actual-domain** response causes no future loss.

For a finite frozen proof horizon, the additional protected/obstacle/electrode overlay is finite. A universal bound for that overlay is still part of VAAPC-I and H2; it is not inferred from the structural bound \(M\).

---

# 9. Co-moving coordinates remove the finite-horizon welding defect

The audit correctly rejects dropping word-dependent endpoint maps after globally uniformizing an entire physical tail. The present construction never performs that uniformization.

Each

\[
h_{w_j}:D_j\to P
\]

is an actual conformal map. Pullback is an isometry of intrinsic Dirichlet trace spaces, and

\[
h_{w_j}(S_{j+1})=\operatorname{int}P\setminus Q_{a_{j+1}}.
\]

Every update therefore uses only:

- one of the two fixed physical root-cell forms \(c_L,c_R\);
- one of finitely many structural masks \(R\subset\mathcal E\);
- the exact atom maps \(\tau_L,\tau_R\);
- the finite frozen phase/orientation and proof-port overlay.

## Theorem 9.1 - Contact-aware co-moving response cocycle

The exact finite-horizon physical response is generated by

\[
(R,q)\longmapsto
\bigl(T_a(R),\mathfrak R_{a,R}(q)\bigr),
\qquad a\in\{L,R\},
\tag{9.1}
\]

on one fixed root-normalized trace category. No global welding maps are discarded: the maps \(h_{w_j}\) define the coordinates at every stage and the update itself is one of a fixed root-cell catalog.

Consequently, the fixed-conjugated-modulus obstruction is removed from finite-horizon contact/collar realization. The theorem does **not** imply norm precompactness of the orbit \(q_j\); that is a separate quantitative theorem.

---

# 10. Contact transport versus conducting energy

Define the finite labeled contact graph \(\mathscr C\) with vertex set \(\mathcal E\) and edge

\[
J\xrightarrow{a}\tau_a(J)
\]

for \(J\in A_a\). Such an edge is exact zero-cell-energy persistence of a boundary arc.

## Theorem 10.1 - Contact transient/recurrent dichotomy

Every contact-atom trajectory is either:

1. transient and leaves the zero-energy contact graph before visiting more than \(M\) distinct atoms; or
2. recurrent and enters a strongly connected component of \(\mathscr C\), where it must be retained as an exact neutral presentation mode.

This is a finite graph theorem. It supplies a source-local version of the manuscript's transient/neutral alternative.

## Theorem 10.2 - Blockwise finite-feature Gramian gap

Fix a finite-dimensional proof-use feature space for one direct-decoration block. For each admissible finite word \(\nu\) of length \(L\), let \(G_\nu\ge0\) be the exact accumulated physical-energy Gramian on those features and let

\[
N_\nu=\ker G_\nu.
\]

Because there are finitely many words of length \(L\) and finite-dimensional feature spaces, there is

\[
\gamma_L>0
\]

such that for every \(\nu\),

\[
\langle G_\nu x,x\rangle
\ge
\gamma_L\operatorname{dist}(x,N_\nu)^2.
\tag{10.1}
\]

Here \(\gamma_L\) is the minimum of the positive eigenvalues of the finitely many nonzero Gramians. Thus every finite block has an exact split into a word-specific neutral kernel and a quantitatively conducting complement.

No universal lower bound for \(\gamma_L\), no universal feature dimension, and no uniform control across unbounded decorations is claimed. Those are precisely the next H2/MBTT requirements.

---

# 11. Gate effect

## Proved split nodes

The arguments support the following new proved modules:

1. `NESTED_SEPARATOR_CONTACT_MARKOV_PROPERTY`;
2. `FROZEN_COLLAR_SEPARATOR_CALCULUS`;
3. `BOUNDARY_PERSISTENCE_INTERVALS`;
4. `DIRECT_DECORATION_CONTACT_MASK_AUTOMATON` for the binary \(f^q\)-package;
5. `PREFIX_CELL_FOUR_WAY_TRACE_REFINEMENT`;
6. `GEOMETRIC_SEPARATOR_RESPONSE_RECURSION`;
7. `DTN_MARKOV_SUFFICIENCY`;
8. `DIRECT_DECORATION_BLOCKWISE_GEOMETRIC_LIVE_FRONTIER`;
9. `CO_MOVING_PHYSICAL_RESPONSE_COCYCLE`;
10. `CONTACT_TRANSIENT_RECURRENT_DICHOTOMY`;
11. `BLOCKWISE_FINITE_FEATURE_GRAMIAN_GAP`.

## Conservative status of the broad gates

The broad source-facing gates should **not** be promoted wholesale.

- The all-depth **puzzle-contact** part of `PHYSICAL_END_CONTACT_WELDING_CONTROL` is proved for the binary direct-decoration package.
- The finite-horizon calculus for any already frozen finite collar/obstacle inventory is proved.
- `DIRECT_DECORATION_TRACE_COLLAR_REALIZATION` remains open in its global protected/source-complete sense because the future inventory itself is not constructed uniformly.
- `END_PLUMBING_TRACE_RESPONSE_CONTROL` remains open until the cocycle orbit is controlled in the response/Value topology actually used by H2.
- VAAPC-I, H2, MBTT, coercivity, rigidity, UPTCR, and MLC remain open.

A defensible ledger split is:

\[
\boxed{
\texttt{PHYSICAL\_END\_SEPARATOR\_CONTACT\_REALIZATION}
\quad\text{proved}
}
\]

and

\[
\boxed{
\texttt{CONTACT\_AWARE\_RESPONSE\_COCYCLE\_COMPACTNESS\_AND\_VALUE\_OBSERVABILITY}
\quad\text{open}.
}
\]

---

# 12. The absolute biggest next gap

The most consequential remaining theorem is no longer an all-depth contact-graph theorem. It is:

## `CONTACT_AWARE_RESPONSE_COCYCLE_COMPACTNESS_AND_VALUE_OBSERVABILITY`

For every actual mixed virtual-Molecule block, construct a universally controlled quotient of the exact state (9.1) such that:

1. every recurrent zero-energy contact mode is retained in a finite neutral/shear module;
2. every transient complement has a universal positive observability Gramian;
3. all KKL Value rows and WAD transports factor exactly through the quotient;
4. the primitive, neutral, and virtual response charts are uniformly comparable in one Loewner-monotone calibrated gauge;
5. every complete block is strictly contracting, or its neutral module is grouped with a later strictly contracting block;
6. the complete discounted non-plumbing error stays below the contraction margin.

A proof with universal constants would simultaneously attack:

- `H2_RESPONSE_REALIZATION`;
- `H2_VALUE_FEATURE_REALIZATION`;
- `H2_VIRTUAL_TRANSFER_TRICHOTOMY`;
- `H2_DISCOUNTED_ERROR_CHARGE`;
- and ultimately MBTT.

That is the largest current needle-moving gap because the manuscript's MBTT requires uniform backward amplification of the full response-density/Value/shear state, not merely formal existence of a carrier or collar.

---

# 13. Computational falsification audit

The companion exact audit performs two independent attacks.

1. It checks the audit's alternating-rectangle example and verifies that the complete nonconsecutive bypass contact lies on the current separator.
2. It generates randomized finite contact systems with rational conductances. It compares:
   - one-shot Kron reduction of the complete historical network; and
   - genuinely recursive separator composition, retaining only the current response and mask.

The arithmetic is exact SymPy rational arithmetic; no pseudoinverse or numerical cutoff is used.

Across 250 randomized trials:

- the maximum one-shot versus recursive discrepancy was exactly zero;
- the contact-mask recursion had zero failures;
- the known bypass was captured on the current separator.

The computation does not prove source authorization, Sobolev patching, a universal Gramian gap, H2, MBTT, coercivity, rigidity, or MLC. The theorems above carry the mathematical content.

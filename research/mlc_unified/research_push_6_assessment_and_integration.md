# Research Push VI assessment: separator localization survives; the finite cocycle does not

## 1. Decision

Research Push VI contains one useful and correct reorganization of the
direct-decoration contact problem:

\[
\boxed{\text{accumulated prefix}+\text{next shell}
       \text{ interact only through the current separator}.}
\]

For one fixed binary \(f^q\)-address chain, this observation captures the
nonconsecutive contact in the Push-V alternating-rectangle example.  It
replaces a shell-to-shell recursion by an exact prefix-to-next-shell
decomposition.  The corresponding set-theoretic separator lemma and the
interval-convexity of physical boundary persistence are valid.

The submitted finite contact automaton and protected response cocycle are not
proved.  Four independent defects prevent their promotion:

1. the asserted finite atom-to-atom maps are incompatible with the expanding
   external-ray model unless a different, incidence-valued atomization is
   constructed;
2. an arbitrary frozen physical overlay becomes word- and stage-dependent
   after normalization, so it is not represented by two fixed root-cell
   forms;
3. the trace norm is not typed consistently: full \(H^1\) is not conformally
   invariant, while pure Dirichlet energy is only a seminorm until constants
   are quotiented or grounded; and
4. the union-of-symbols strongly connected components computed by the packet
   do not classify recurrence along the actual address.

Accordingly, the submitted ledger patch and manuscript insertion are not
merged.  One narrower node is adopted:

```text
BINARY_DIRECT_DECORATION_NESTED_SEPARATOR_CALCULUS  proved
```

All broad gates retain their previous status:

```text
DIRECT_DECORATION_ALL_DEPTH_CONTACT_CLOSURE   open
FINITE_LIVE_COMMON_REFINEMENT_FRONTIER        open
DIRECT_DECORATION_TRACE_WELDING_COMPACTNESS   open
DIRECT_DECORATION_TRACE_COLLAR_REALIZATION    open
END_PLUMBING_TRACE_RESPONSE_CONTROL           open
H2 / MBTT / VAAPC-I / UPTCR / MLC             open
```

This is a genuine local simplification, not a proof of a new MLC parameter
class and not evidence that the remaining obstruction is merely
quantitative.

## 2. Chain of custody and integrity

The supplied bundle was audited in place and left unchanged:

```text
research/mlc_research_push_6_bundle/push6
```

All eleven entries match the supplied `SHA256SUMS_PUSH6.txt` manifest.

| File | SHA-256 |
|---|---|
| `README_PUSH6.txt` | `90ed24c4a8f8a8c4b65db2b2241749c51a1f373a4610293383d0b1220a9b7387` |
| `mlc_research_push_6.md` | `5990a581ee8150c0dace6d0c3e3b1f8dd3d68ecd5f89877c8b4717779e88cab3` |
| `mlc_manuscript_insertions_push_6.tex` | `9e60dc345245f1a29d4e1c51a03c772e7b2040cfb08a269c1dcf0a4b2d1c7dfe` |
| `mlc_manuscript_insertions_push_6.pdf` | `b95c05d13d7a869e20509fa5737f294a3aeae55c2629d96fceb3fa4fdbbfb011` |
| `mlc_ledger_patch_push_6.json` | `c5e92c9c8b4ba0af3a64a736398e062b25a5f053d856cf21f1f5720ffd007557` |
| `separator_contact_audit.py` | `e4660ad315f8550b306515a25f841f4943e4fb7034d42ad32f3798c9dd88acf3` |
| `separator_contact_report.json` | `7a581523d4fce5d13e0f1369b6c41b2a606205e0c7f4dc353d33458b15464bf5` |
| `contact_mask_compiler.py` | `a985021b244a0020fe4f13f37bacc17cad078ed2471075ecbc0fa5a080d2eb70` |
| `contact_mask_example.json` | `46a60340fbd02e114fe8f75602a6d3b924ecdfe1fc9bd0b4fd34ee40aad14b91` |
| `contact_mask_example_output.json` | `dfaf71dabe1ae6a7f48b5fa0dab2739e917f5f54d5b3833899eaa85bf4423187` |
| `pdf_preflight_push6.txt` | `89716a8d88a0656a13318f2828e32e7b4fd7a702a8fa180392293e357a66fec9` |

The PDF was not subjected to another page-by-page image inspection.  The
user explicitly asked that massive PDF visual checks stop; the source,
extracted claims, preflight record, and mathematical content were sufficient
for this audit.

## 3. Audit method

The audit used four independent layers.

1. **Source layer.**  The Kahn--Lyubich Decorations source was checked at
   `kingdom.tex`, especially lines 28--48, 116--118, 133--137, and
   140--154.
2. **Proof layer.**  Every theorem in the Markdown and LaTeX packet was
   reduced to its exact topological, trace-theoretic, dynamical, and
   quantitative hypotheses.
3. **Machine layer.**  Both scripts were reproduced, then attacked outside
   their random-generator support.
4. **Dependency layer.**  Every proposed node and dependency was compared
   with the live machine ledger and with the current Push-III--V response
   chain.

The analytic proof boundary was enforced throughout: a finite graph or
network experiment is a regression only and cannot prove source
realizability, Sobolev trace compatibility, compactness, Value
observability, or a uniform transition.

## 4. Exact source boundary

The locked source is Kahn--Lyubich,
*A priori bounds for some infinitely renormalizable quadratics. II.
Decorations*, [arXiv:math/0609046](https://arxiv.org/abs/math/0609046).
It supplies the following facts used here.

- Puzzle pieces are closed topological disks (`kingdom.tex`, lines 28 and
  32).
- Their boundaries are finite unions of equipotential and external-ray arcs
  (lines 45--48).
- For
  \[
  P=Y^{(n-1)q+1},
  \]
  the critical value of \(f^q\) is outside \(P\), so \(P\) has two univalent
  \(f^q\)-pullbacks \(Q_L,Q_R\subset P\) (lines 133--137).
- With \(g=f^q|_{Q_L\cup Q_R}\), the domain of \(g^n\) has \(2^n\)
  univalent pullback components (lines 150--154).

Thus Push VI correctly chooses the binary one-step package and does not
repeat Push V's untyped switch between a binary \(f^q\) branch and a
length-\(n\), \(2^n\)-component macrobranch.

The source does **not** provide:

- a finite branch-invariant boundary Markov partition;
- atom maps \(\tau_a\) on such a partition;
- a horizon-complete protected collar or obstacle overlay;
- a common invariant trace norm;
- compactness of a response/welding cocycle;
- a universal state dimension, Gramian gap, or Value observability constant;
  or
- stability of any of those objects under final-root enlargement.

These omissions are proof obligations, not details that can be supplied by
the finite scripts.

## 5. The theorem that survives

### Theorem 5.1 (nested-separator contact calculus)

Let

\[
D_0\supset D_1\supset\cdots\supset D_H
\tag{5.1}
\]

be nested closed subsets of the plane.  For \(0\le j<H\), set

\[
\Omega_j=\operatorname{int}D_0\setminus D_j,
\qquad
S_{j+1}=\operatorname{int}D_j\setminus D_{j+1},
\tag{5.2}
\]

and define the complete active set-theoretic interface

\[
J_j=
(\operatorname{int}D_0\cap\partial D_j)\setminus D_{j+1}.
\tag{5.3}
\]

Then:

1. \(\Omega_j\) and \(S_{j+1}\) are disjoint open sets;
2. for every \(k>j\),
   \[
   \overline{\Omega_j}\cap\overline{S_k}
   \subset\partial D_j;
   \tag{5.4}
   \]
3. there is the exact disjoint set decomposition
   \[
   \Omega_{j+1}
   =
   \Omega_j\sqcup J_j\sqcup S_{j+1};
   \tag{5.5}
   \]
4. if \(i<k\) and
   \(x\in\partial D_i\cap\partial D_k\), then
   \[
   x\in\partial D_j
   \quad\text{for every }i\le j\le k.
   \tag{5.6}
   \]

If, in addition, the pieces are the source-locked binary
direct-decoration puzzle disks, then (5.1) is realized by the actual
univalent inverse branches.  If every proof-used positive-length part of
\(J_j\) has an independently verified finite Lipschitz or otherwise
admissible Sobolev interface decomposition, gluing the prefix and next shell
by equality of the two traces on those parts and minimizing the common
trace gives the actual-domain Dirichlet response of \(\Omega_{j+1}\).

No assertion is made here about a finite invariant atomization, protected
overlay naturality, final-root enlargement, a fixed trace category,
compactness, or uniform constants.

### Proof

Because \(D_j\) and \(D_{j+1}\) are closed, both differences in (5.2) are
open.  Also

\[
\Omega_j\subset\mathbb C\setminus D_j,
\qquad
S_{j+1}\subset D_j,
\]

so they are disjoint.

For \(k>j\), nesting gives

\[
S_k\subset D_{k-1}\subset D_j.
\]

Since \(D_j\) is closed,

\[
\overline{S_k}\subset D_j.
\tag{5.7}
\]

On the other hand,

\[
\Omega_j\subset\mathbb C\setminus D_j
\]

implies

\[
\overline{\Omega_j}
\subset
\overline{\mathbb C\setminus D_j}
=
\mathbb C\setminus\operatorname{int}D_j.
\tag{5.8}
\]

Intersecting (5.7) and (5.8) yields

\[
\overline{\Omega_j}\cap\overline{S_k}
\subset
D_j\setminus\operatorname{int}D_j
=
\partial D_j,
\]

which proves (5.4).

Now take \(x\in\Omega_{j+1}\).  Exactly one of the mutually exclusive
relations

\[
x\notin D_j,\qquad
x\in\partial D_j,\qquad
x\in\operatorname{int}D_j
\]

holds.  In the first case \(x\in\Omega_j\).  In the second,
\(x\in J_j\) because \(x\in\operatorname{int}D_0\) and
\(x\notin D_{j+1}\).  In the third, \(x\in S_{j+1}\).  Conversely, every
point in any of the three sets lies in
\(\operatorname{int}D_0\setminus D_{j+1}\).  This proves (5.5), including
the finite boundary vertices that the submitted formula excluded only for
trace purposes.

Finally, suppose \(i<j<k\) and
\(x\in\partial D_i\cap\partial D_k\).  Since
\(D_k\subset D_j\), we have \(x\in D_j\).  If
\(x\in\operatorname{int}D_j\), then
\(\operatorname{int}D_j\subset\operatorname{int}D_i\), contradicting
\(x\in\partial D_i\).  Hence
\(x\in D_j\setminus\operatorname{int}D_j=\partial D_j\).  The endpoint
cases \(j=i,k\) are immediate, proving (5.6).

For the source specialization, let

\[
\phi_a=(g|_{Q_a})^{-1},\qquad
D_w=\phi_w(P).
\]

Every \(\phi_a\) is a homeomorphism of the relevant closed puzzle disks, so
for an address prefix \(w_j\) and next symbol \(a\),

\[
D_{w_ja}=\phi_{w_j}(Q_a)\subset\phi_{w_j}(P)=D_{w_j}.
\]

This is exactly (5.1).  On a verified finite tame interface, the existing
`REGULAR_INTERFACE_FIBER_PRODUCT_RESPONSE` and
`FINITE_TAME_CONTACT_OVERLAY_RESPONSE` theorems identify \(H^1\) of the
union with the fiber product of the two cell spaces and add their Dirichlet
energies.  Taking the infimum over the common trace gives the stated
conditional response conclusion. \(\square\)

### Corollary 5.2 (persistence intervals)

For a fixed finite common refinement of the curves
\(\partial D_0,\ldots,\partial D_H\), let \(A\) be any open boundary atom.
Then

\[
\{j:A\subset\partial D_j\}
\]

is an integer interval.

This follows pointwise from (5.6).  It means that one *physical open arc*
cannot leave the nested boundary and later become the same physical
boundary arc again.  It does not bound the lifetime of normalized labels,
does not control vertices or prime ends, and does not prove invariance under
changing the final root.

### Corollary 5.3 (fixed-set removal)

Let \(Z\) be any fixed subset and put

\[
\Omega_j^Z=\Omega_j\setminus Z,\qquad
S_k^Z=S_k\setminus Z.
\]

Then

\[
\overline{\Omega_j^Z}\cap\overline{S_k^Z}
\subset\partial D_j
\qquad(k>j).
\tag{5.9}
\]

Indeed, closure is monotone under inclusion, so the left side of (5.9) is
contained in the left side of (5.4).  This is only a contact-localization
statement.  It does not prove that \(Z\) is regular, complete,
dynamically equivariant, correctly typed as a wall or port, or compatible
with protected accesses.

## 6. What this repairs from Push V

The alternating rectangles from Push V have shells

\[
C_\ell=\overline{\operatorname{int}D_{\ell-1}\setminus D_\ell}.
\]

The first and third shells approach the same right-hand arc while the
second shell does not.  Therefore a recursion that retains only the
response of the most recent shell is invalid.

At the stage when the third shell is attached, however, the state is not
\(C_2\); it is the accumulated prefix

\[
\Omega_2=\operatorname{int}D_0\setminus D_2.
\]

The common \(C_1\)-to-\(C_3\) arc lies on \(\partial D_2\), exactly as
(5.4) requires.  A complete response on the whole current separator can
therefore glue that bypass when it becomes active.

This removes the need for an all-pairs **raw shell-contact graph** for a
single nested chain.  It does not by itself construct:

- the complete proof-used separator trace;
- simultaneous sibling or multi-branch incidence;
- protected endpoints and prime-end access data;
- a finite last-live quotient;
- a physical no-bypass resistance lower bound;
- a compact welding/response state; or
- stability under root enlargement.

Consequently the broad all-depth contact node remains open, but its unknown
content is narrower and more accurately typed.

## 7. The exact response statement that remains valid

Assume at one stage that:

1. the relevant prefix and shell admit regular Dirichlet domains after a
   finite cell decomposition;
2. every positive-length common interface has two compatible Sobolev trace
   maps;
3. all one-sided boundaries, obstacles, electrodes, and protected ports are
   retained as external variables or given explicit boundary conditions;
4. junction and landing-point sets are proved negligible for the chosen
   \(W^{1,2}\) gluing theorem; and
5. the cell response at that stage is the response of the **actual**
   normalized shell, not an unproved fixed representative.

Let \(q_j\) be the exact prefix response and \(c_{j,a}\) the exact response
of the normalized next shell, including its stage-specific overlay.  If
\(\mathcal F_j\) is the fiber product imposing equality on exactly the
two-sided active traces, then

\[
q_{j+1}(x)
=
\inf_{(\xi,\zeta)\in\mathcal F_j(x)}
\bigl(q_j(\xi)+c_{j,a}(\zeta)\bigr).
\tag{7.1}
\]

Equation (7.1) is a direct application of the already proved
finite-interface gluing theorems.  It is exact but nonautonomous.  It does
not yield a finite catalog, a compact orbit, or a strict transition.

This is the maximum analytic statement licensed by Push VI without adding
new source geometry.

## 8. Failure of the finite atom-to-atom automaton

Push VI asserts a finite partition \(\mathcal E\) of the root boundary and
maps

\[
\tau_a:A_a\longrightarrow\mathcal E,\qquad
\tau_a(J)=g(J),
\tag{8.1}
\]

which send every shared open atom \(J\) to one open root atom.  The reason
given is that \(g|_{Q_a}\) is a homeomorphism.  A homeomorphism sends an
open arc to an open arc; it does not imply that the image is one atom of a
preselected finite partition.

The external-ray model gives an explicit obstruction.  Parameterize a
shared ray segment by Böttcher height \(t\in[0,1]\), with its landing point
at \(t=0\).  For

\[
d=2^q>1,
\]

the \(f^q\) branch acts by

\[
m_d(t)=dt,
\tag{8.2}
\]

and the child shared segment is \(A=[0,1/d]\).

Suppose a finite partition with vertex set \(V\) makes \(A\) a union of
atoms and makes \(m_d\) send every atom contained in \(A\) to one root
atom.  Let \(v>0\) be the smallest positive vertex.  Then
\((0,v)\) is the root atom adjacent to the landing point.  Since
\((0,v)\subset A\),

\[
m_d((0,v))=(0,dv).
\]

The only root atom having left endpoint \(0\) is \((0,v)\), but
\((0,dv)\ne(0,v)\) because \(d>1\).  Thus (8.1) is impossible.  Equivalently,
trying to repair it by subdivision forces the descending vertices
\(d^{-1},d^{-2},\ldots\).

What survives is a set-level recurrence.  Define

\[
B_j=h_{w_j}(\partial D_j\cap\partial D_0)\subset\partial P.
\]

For the next symbol \(a\), persistence and the commuting relation
\(h_{w_{j+1}}=g\circ h_{w_j}\) on \(D_{j+1}\) give

\[
\boxed{
B_{j+1}=g\bigl(B_j\cap\partial Q_a\bigr).
}
\tag{8.3}
\]

To turn (8.3) into finite combinatorics, one needs a proved
incidence-valued map such as

\[
\Pi_a(J)=
\{K\in\mathcal E:K\subset g(J)\},
\tag{8.4}
\]

together with endpoint images, restrictions of trace coordinates, and a
proof that images of the allowed sets remain unions of the chosen atoms.
The submitted compiler cannot express (8.4): it requires one injective
target label for every shared atom.

There is a finite **relational** repair under additional explicit
hypotheses.  Let

\[
\Gamma=\partial P,\qquad
C_a=\Gamma\cap\partial Q_a,\qquad
C=C_L\cup C_R.
\]

Assume:

1. \(\Gamma\) is a finite ray/equipotential Jordan graph;
2. every \(C_a\) is a finite union of closed subarcs and vertices;
3. \(g|_{\partial Q_a}\) is a homeomorphism onto \(\Gamma\);
4. positive Böttcher height is multiplied by \(2^q\) while an endpoint orbit
   remains in \(C\);
5. every height-zero seed endpoint is preperiodic; and
6. vertices and zero-length access data are carried in a separate ledger.

Let \(V_0\) contain the root vertices and the endpoints of \(C_L,C_R\), and
let \(V\) be the least forward-saturated set satisfying

\[
g(V\cap C)\subset V.
\tag{8.5}
\]

Then \(V\) is finite.  A positive-height seed can remain in the bounded
contact graph for only finitely many iterates because its height is
multiplied by \(2^q>1\); every height-zero seed has a finite orbit by
hypothesis.  With

\[
\mathcal E=\pi_0(\Gamma\setminus V)
\]

and

\[
\Theta_a(J)=
\{K\in\mathcal E:K\subset g(J)\}
\qquad(J\subset C_a),
\tag{8.6}
\]

the endpoints of \(g(J)\) lie in \(V\), so, modulo \(V\),

\[
g(J)=\bigcup_{K\in\Theta_a(J)}K.
\]

Consequently the open-arc masks satisfy

\[
R_{j+1}
=
\bigcup_{\substack{J\in R_j\\J\subset C_a}}
\Theta_a(J)
\tag{8.7}
\]

modulo the separately retained vertices.  This gives a block-dependent
bound of \(2^{|\mathcal E|}\) for raw positive-length masks.

This abstract repair does **not** yet instantiate the Kahn--Lyubich binary
package.  Their checked text gives finite puzzle boundaries, preimage
vertices, and univalent branches, but it does not list the complete sets
\(C_a=\partial P\cap\partial Q_a\), rule out additional closure contacts,
or prove the endpoint transition ledger.  Moreover, one input arc may map
across several target atoms.  The target trace pieces are constrained to
come from one trace on \(g(J)\); they are not independent ports.  The
actual restriction/presentation operators and subdivision compatibility
must therefore be retained.  Arbitrary protected or enlargement endpoints
may also have infinite forward orbits.

Therefore `DIRECT_DECORATION_CONTACT_MASK_AUTOMATON`, its claimed
single-atom transport, protected response interpretation, and every
downstream fixed-catalog result are not promoted.  The conditional
relational construction is retained as the replacement invariant to be
source-realized.

## 9. Failure of the fixed protected root-cell catalog

Let \(Z\) be the packet's frozen physical inventory.  The normalized
conducting next shell is

\[
\begin{aligned}
h_{w_j}(S_{j+1}\setminus Z)
&=
h_{w_j}(S_{j+1})
\setminus h_{w_j}(Z\cap S_{j+1})\\
&=
(\operatorname{int}P\setminus Q_a)
\setminus \zeta_j,
\end{aligned}
\tag{9.1}
\]

where

\[
\zeta_j=h_{w_j}(Z\cap S_{j+1}).
\tag{9.2}
\]

Nothing in the packet proves that \(\zeta_j\) depends only on
\(a\in\{L,R\}\), belongs to a finite catalog, or is carried
equivariantly by root enlargement.  In general it depends on the complete
word \(w_j\) and the stage.

Consequently, the asserted fixed cell form

\[
c_a=\operatorname{Resp}
\bigl((\operatorname{int}P\setminus Q_a)\setminus Z_a\bigr)
\]

cannot be substituted for the actual stage form without an additional
equivariance theorem.  The valid update has the form

\[
q_{j+1}
=
\mathfrak R_{j,a,B_j,\zeta_j}(q_j),
\tag{9.3}
\]

not the autonomous two-letter recursion claimed in the packet.

Theorems 7.1, 7.2, and 9.1 of Push VI are therefore valid only after either:

- setting \(Z=\varnothing\); or
- supplying and transporting the complete stage-specific overlay; or
- independently proving that all normalized overlays lie in one controlled
  equivariant catalog.

The third alternative is part of the still-open protected and trace-collar
work.

## 10. Trace-space type error

Push VI defines

\[
\mathcal T_\Omega(B)
=H^1(\Omega)/\{u:\operatorname{Tr}_B u=0\}
\]

with a “minimum-energy quotient norm,” and later says conformal pullback is
an isometry of these spaces.  There are two different objects here.

1. The full norm
   \[
   \|u\|_{H^1(\Omega)}^2
   =
   \int_\Omega |u|^2\,dA+
   \int_\Omega |\nabla u|^2\,dA
   \]
   is not conformally invariant: the area term changes by the Jacobian.
2. The homogeneous Dirichlet energy
   \[
   \mathcal E_\Omega(u)
   =
   \int_\Omega|\nabla u|^2\,dA
   \]
   is conformally invariant in dimension two, but it vanishes on constants.
   It is a seminorm until one quotients by the correct componentwise
   constants or supplies explicit grounding.

The trace category must therefore be rebuilt as either:

- homogeneous Dirichlet spaces modulo one constant on each connected
  conducting component, retaining all relative port potentials; or
- explicitly grounded spaces with grounding carried through every branch.

It must then be shown that the partial trace operator, endpoint
compatibility, finite-vertex removal, response closedness, and coordinate
pullback are well-defined in exactly that category.  The packet does not do
this, so the claimed fixed trace isometry and closed response cocycle cannot
be imported.

## 11. Graph and Gramian claims

### 11.1 The SCC output is not address recurrence

The compiler forms the union graph of all \(L\)- and \(R\)-edges and reports
its cyclic strongly connected components as
`recurrent_neutral_components`.  This ignores:

- the supplied word;
- reachability from the current mask;
- label order and admissibility; and
- whether the transported atom remains physically active.

The packet's own sample is a direct countercheck:

\[
\mathcal E
\longrightarrow
\{a_0,a_2,a_4\}
\longrightarrow
\{a_1\}
\longrightarrow
\varnothing.
\]

The realized mask is empty after the third symbol, yet the compiler labels
all five atoms as one recurrent neutral component.  Thus the output is at
most a set of *potential alphabet cycles*, not an actual recurrent neutral
mode.

Even in a valid finite labeled graph, SCC membership alone gives no
uniform exit-time bound for a nonrecurrent address: a path may loop \(N\)
times and then exit, for arbitrary \(N\).  Finally, zero combinatorial
transport cost does not prove zero analytic energy in the accumulated
response.

### 11.2 The finite Gramian bound is vacuous globally

For one fixed finite-dimensional space and finitely many positive
semidefinite matrices \(G_\nu\), the minimum of their positive eigenvalues
is positive after discarding the all-zero matrices.  If every matrix is
zero, any positive \(\gamma\) satisfies

\[
\langle G_\nu x,x\rangle
\ge
\gamma\,\operatorname{dist}(x,\ker G_\nu)^2
\]

because both sides vanish.  This is elementary finite-dimensional linear
algebra.

The resulting \(\gamma_L\) may tend to zero with word length, decoration
depth, period, trace dimension, or geometry.  It supplies none of the
uniform observability required by H2 or MBTT.  Adding it as a proof node
would increase ledger size without reducing the MLC dependency frontier.

## 12. Computational audit

The scripts have legitimate regression value, but their scope is much
narrower than the prose suggests.

### Reproduced successes

- all supplied hashes match;
- the sample compiler output reproduces semantically;
- the four declared mask classes partition the supplied finite atom set;
- the submitted mask recursion is implemented correctly for its own schema;
- Tarjan output agrees with an independent reachability oracle on 900
  random finite graphs;
- one-shot and recursive finite-network reductions agree in:
  - 2,276 exhaustive small cases,
  - 700 additional random trials over seven seeds, and
  - the packet's original 250 trials;
- the alternating-rectangle geometry is captured by the current separator;
  and
- repeated runs under different Python hash seeds are deterministic.

These checks confirm finite bookkeeping and Schur-complement associativity
for the generated resistor subclass.

### Adversarial failures and omissions

1. `separator_contact_audit.py` assumes a fixed terminal count, a full
   permutation of labels, positive integer conductances, and one chain
   coupling.  It has no actual puzzle geometry, protected ports, obstacles,
   trace Hilbert space, WAD coordinate, Value functional, or universal
   constant.
2. The two scripts use different symbol types: the compiler accepts a
   partial injection on shared atoms, while the network generator requires a
   full permutation on all atoms.
3. A harmless floating zero-energy internal component makes
   `schur_response` raise an exception even though the minimized terminal
   response exists.  The implementation needs quotient-safe
   pseudoinverse/component handling for that scope.
4. Repeated non-ground terminal labels are lifted incorrectly.  For one
   unit edge and terminals `[1,1]`, the routine returns the all-ones matrix;
   on the equality diagonal this represents \(4x^2\), not the correct
   \(x^2\).
5. The random generator avoids both preceding cases, so the passing trials
   cannot detect them.
6. The geometry check is one floating-point Shapely example with a numerical
   buffer.  It illustrates but does not prove Theorem 5.1.
7. The scripts do not fail their process exit code when a reported audit
   field is false.
8. SymPy and Shapely are runtime dependencies of the packet but are not
   declared in the repository requirements.
9. On Windows, regenerated JSON uses CRLF line endings.  The JSON objects
   match semantically and reproduce the stored hashes after newline
   normalization, but raw byte hashes differ without canonical output.

The adopted independent validator records both the successful finite checks
and these counterexamples.  No computational result is a premise of
Theorem 5.1.

## 13. Ledger-patch audit

The proposed JSON patch cannot be applied mechanically or mathematically.

### Mechanical defects

- `PHYSICAL_END_CONTACT_WELDING_CONTROL` is an umbrella phrase, not a live
  ledger ID.
- `VAAPC-I` is a clause of
  `VIRTUAL_AUGMENTED_ATOM_PORT_CERTIFICATE`, not a top-level ledger node.
- `PARTIAL_TRACE_FIBER_PRODUCT_RESPONSE` does not exist; the live node is
  `REGULAR_INTERFACE_FIBER_PRODUCT_RESPONSE`.
- `PHYSICAL_END_SEPARATOR_CONTACT_REALIZATION` is advertised in the README
  and verdict but is absent from `new_proved_split_nodes`.
- Every proposed evidence path is wrong relative to the authoritative
  `research/mlc_unified` directory.
- The new open target has no actual ledger dependencies or evidence path.
- Literal application would add eleven proved nodes and one open node; the
  stated “split” and count policy name no node being replaced.

### Logical defects

The following proposed nodes depend on the false or unproved finite
atomization:

```text
DIRECT_DECORATION_CONTACT_MASK_AUTOMATON
PREFIX_CELL_FOUR_WAY_TRACE_REFINEMENT
GEOMETRIC_SEPARATOR_RESPONSE_RECURSION
DTN_MARKOV_SUFFICIENCY
DIRECT_DECORATION_BLOCKWISE_GEOMETRIC_LIVE_FRONTIER
CO_MOVING_PHYSICAL_RESPONSE_COCYCLE
CONTACT_TRANSIENT_RECURRENT_DICHOTOMY
BLOCKWISE_FINITE_FEATURE_GRAMIAN_GAP
```

The frozen-collar statement proves only contact localization after removing
a fixed set; it does not construct or type the overlay.  The response nodes
also use the unproved fixed-overlay catalog and the inconsistent trace norm.
The SCC and Gramian nodes have no useful global conclusion even in their
finite abstract form.

The proposed meta-gate
`CONTACT_AWARE_RESPONSE_COCYCLE_COMPACTNESS_AND_VALUE_OBSERVABILITY` is not
added.  Its content is already distributed among the existing open nodes
`DIRECT_DECORATION_TRACE_WELDING_COMPACTNESS`,
`DIRECT_DECORATION_TRACE_COLLAR_REALIZATION`,
`END_PLUMBING_TRACE_RESPONSE_CONTROL`, and the H2 obligations.  Adding a
second umbrella would not discharge a dependency.

## 14. Claim-by-claim disposition

| Push-VI claim | Decision | Exact reason |
|---|---|---|
| Binary \(f^q\) source package | **Use** | Correct branch granularity and supported by Kahn--Lyubich. |
| Nested-separator contact theorem | **Use after repair** | The closure and decomposition arguments are correct; the full interface must include vertices set-theoretically. |
| Alternating bypass capture | **Use narrowly** | Exact for prefix-to-next-shell bookkeeping; gives no resistance or coercivity. |
| Frozen-collar separator theorem | **Use only set-theoretically** | Removing a set cannot create cross-separator contact, but regularity, typing, and equivariance are unproved. |
| Boundary-persistence intervals | **Use** | Correct for actual physical boundary points of one fixed nested chain. |
| Finite atom map \(\tau_a\) | **Reject** | Expanding ray height generally prevents finite atom-to-single-atom closure. |
| \(2^{|\mathcal E|}\) raw mask state | **Use only conditionally** | The forward-saturated relational construction proves it under the six hypotheses in Section 8; the KL contact sets and endpoint ledger are not yet source-realized. |
| Four approach types | **Use as a pointwise definition** | Exhaustive after a valid refinement; transport and endpoint data remain missing. |
| Fixed response recursion | **Reject in protected scope** | The normalized overlay is stage-dependent.  Retain only (7.1). |
| DtN Markov sufficiency | **Do not ledger** | Tautological only after the entire future update schedule is retained. |
| Finite geometric live frontier | **Use only as separator localization** | No proved finite protected or Value frontier and no universal bound. |
| Co-moving fixed response cocycle | **Reject** | Depends on the failed atom map, fixed overlay, and trace isometry. |
| Transient/recurrent dichotomy | **Discard as an analytic module** | Union-graph SCCs do not classify the actual labeled orbit or energy. |
| Finite Gramian gap | **Discard from proof chain** | Finite-dimensional tautology with no uniform constant. |
| Eleven-node ledger patch | **Reject** | Over-split, partly false, mechanically incompatible. |
| New global response meta-gate | **Reject** | Duplicates existing open nodes and has no proved interface. |

## 15. Adopted and discarded artifacts

### Adopted

- the binary source-package correction;
- Theorem 5.1 and its persistence corollary;
- the prefix-to-next-shell resolution of the rectangle bypass;
- the set-level recurrence (8.3);
- the finite relational mask theorem under its six explicit hypotheses;
- the stage-specific conditional response formula (7.1);
- the mask compiler's partition logic as a finite abstract diagnostic;
- the exact finite Schur calculation as a regression for invertible resistor
  models; and
- the packet's explicit disclaimer that computation does not prove MBTT,
  coercivity, rigidity, or MLC.

### Retained only as failure information

- the finite atom-to-atom obstruction;
- the normalized-overlay defect \(\zeta_j\);
- the trace norm/seminorm type error;
- the SCC overapproximation;
- the singular-block and repeated-terminal code defects; and
- the absence of final-root enlargement naturality.

### Discarded from the proof chain

- all eleven proposed node promotions as a group;
- the claim that finite-horizon welding has been removed in the protected
  setting;
- the claim that the direct-decoration structural live frontier has a
  proved finite source realization;
- the claim that every graph SCC is an exact neutral analytic mode;
- the finite Gramian minimum as progress toward a universal gap;
- the 250 trials as analytic evidence; and
- the claim that the remaining obstruction is now only quantitative.

## 16. Correct next obligation

The next response-side task is not to estimate the submitted cocycle.  The
cocycle has not yet been constructed in the required category.  The next
obligation is:

### Contact-incidence and normalized-overlay realization

For every proof-used binary direct-decoration horizon:

1. construct the actual current separators and complete proof-used
   interfaces, including endpoints, sides, phases, orientations, protected
   accesses, obstacles, sibling incidence, and enlargement data;
2. replace the impossible atom-to-single-atom maps by an exact
   incidence-valued or restriction-valued transport, and prove that its
   state is finite or future-faithfully compact;
3. construct the homogeneous, correctly grounded multi-port trace category;
4. carry the actual normalized overlay
   \(\zeta_j=h_{w_j}(Z\cap S_{j+1})\), or prove an equivariant compact
   catalog for it;
5. prove the resulting stagewise fiber-product response is closed and
   compatible with every Value/WAD observable; and
6. prove commuting naturality under final-root enlargement.

Only after those six clauses are discharged does it make sense to ask for
norm compactness, a uniform observability gap, or a strict transition.

## 17. Global status

The audit changes one narrow local theorem from open reasoning to a checked
proved node.  It changes no broad status and closes no MLC dependency gate.

The exact contribution is:

\[
\text{single nested binary chain}
\quad\Longrightarrow\quad
\text{all past--future raw contact is exposed on the current separator}.
\]

The missing global passage is still:

\[
\begin{gathered}
\text{source-complete protected separator/overlay}\\
\Downarrow\\
\text{correct trace and incidence cocycle}\\
\Downarrow\\
\text{uniform compactness and Value observability}\\
\Downarrow\\
\text{strict mixed-block transition}\\
\Downarrow\\
\text{coercivity and rigidity}.
\end{gathered}
\]

VAAPC-I, H2, MBTT, H3, H4, UPTCR, and MLC remain open.

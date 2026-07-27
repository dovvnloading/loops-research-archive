# Research Push VII assessment: structural contacts survive; the pseudo-trace response does not

## 1. Decision

Research Push VII contains two useful results, but its headline theorem is
not proved.

The results that survive are:

1. for one fixed source-locked Kahn--Lyubich direct-decoration block, the
   binary inverse cylinders have an exact finite **structural contact
   automaton**, including all-depth pairwise contacts, prefix endpoint
   itineraries, and a two-state normalized contact skeleton after the source
   depth \(n\); and
2. for one fixed finite KKL Hubbard tree, the Value functional admits an
   exact positive-semidefinite **pair-state moment factorization**.

The following advertised promotions do not survive:

- the submitted ray/equipotential boundary-word compiler is not a faithful
  encoding of an actual Kahn--Lyubich puzzle boundary;
- the source does not construct the proposed \(H^1_{\rm fin}\) trace spaces
  on pseudo-piece ideal arcs;
- the pulled dynamical cover is tracked, but the inclusion-induced immersed
  copy and its welding are omitted;
- no actual Dirichlet cell decomposition is constructed, so the recursive
  response grammar is only a conditional algebraic recurrence;
- the safe-gap hypothesis does not prevent a root enlargement from reaching
  the puzzle boundary or a declared interface; and
- the supplied compiler accepts several records that violate its own
  advertised geometric and functorial conclusions.

Accordingly, the proposed fifteen-node patch is not merged.  Two narrower
nodes are adopted:

```text
FIXED_BLOCK_BINARY_CONTACT_AUTOMATON          proved
FIXED_KKL_PAIR_STATE_MOMENT_FACTORIZATION     proved
```

The headline node proposed by the packet,
`DIRECT_DECORATION_BINARY_CONTACT_TRACE_ATLAS`, is not added.  The broad
statuses remain:

```text
DIRECT_DECORATION_ALL_DEPTH_CONTACT_CLOSURE   open
DIRECT_DECORATION_TRACE_WELDING_COMPACTNESS   open
DIRECT_DECORATION_TRACE_COLLAR_REALIZATION    open
END_PLUMBING_TRACE_RESPONSE_CONTROL           open
H2 / MBTT / VAAPC-I / UPTCR / MLC             open
```

This is measurable local progress.  It is not a proof of a new MLC parameter
class and does not move a global gate to proved.

## 2. Chain of custody and reproducibility

The supplied bundle was audited in place and left unchanged:

```text
research/mlc_research_push_7_bundle/push7
```

All fifteen files match `SHA256SUMS.txt`.

| File | SHA-256 |
|---|---|
| `README_PUSH7.txt` | `a4b8815faaf62ef8c563ea8d847d55f0fb244cc88e5083485e3c11b44c6079c9` |
| `binary_contact_trace_compiler.py` | `e9fc21b6d3b6b4c654f589210a33859c2401f370f4c09a9cc6c6c065ad0d0e3a` |
| `binary_contact_trace_test_report.txt` | `8f4f5952bf0382a385b845e298a3b08da18d3f61a00e2828da5469e964f0fbb6` |
| `kkl_value_moment_audit.py` | `4d485b5c62ffc656e4a872ac9f45136c7889c60f1b37733cf9888712080aefa3` |
| `kkl_value_moment_report.json` | `88693cf4e65dc78c0afae70dd5109f02e86cc4c6cb94f8b144e7b16160b70b64` |
| `matrix_product_observable_audit.py` | `5e0b03852c2979eea14db9caeb20bb0fe3ebbebb35f7adc4bba00c11318e1981` |
| `matrix_product_observable_report.json` | `54f62ba6677ba8cfb6b2b4b8b2d0317c1a8df720d8806971dd08a75fe3278ea5` |
| `mlc_ledger_patch_push_7.json` | `8c968d44c1c2ffb33761a31c9929864dffe15d4e267ff453ca1ae4f5e587cebb` |
| `mlc_manuscript_insertions_push_7.pdf` | `d07adad108cee5f6267b7b40002a4374ea7bb170cec017c1d139416afaeebfcf` |
| `mlc_manuscript_insertions_push_7.tex` | `36f504d2d4895814dd1b1b512bc7eb0f1c954968ca0a0e63608b779ff0fd321d` |
| `mlc_research_push_7.md` | `36281c9ee875544455f46bb0747d31e5411abf258afdc74cfcc58094254d20c5` |
| `pdf_preflight_push7.txt` | `071d93fe952dd1ea825f0602b7cab03225bcfd4645db97a04495e46c747df4fd` |
| `source_binary_contact_example.json` | `9a4db8c0e9c0221d1d908ab6f9a95b51fe9c48e8c59728527de4daa1ea3be08d` |
| `source_binary_contact_report.json` | `b0cbd62ce042023c5af72b0f50541073e5697a74798c5069765938c74a3c5241` |
| `test_binary_contact_trace_compiler.py` | `6cdd3607c080297708374ce25a3550e79b47f6cacc74a1cc04d7de55e0349d2e` |

The eight submitted unit tests pass.  The matrix-product script reproduces
800 exact checks with no failure, and the moment script reproduces 300 exact
checks with no failure.  Regenerated JSON objects are semantically identical
to the supplied reports.  Raw byte hashes differ under the local Python
runtime because newline encoding changes from LF to CRLF; this is not a
mathematical difference.

No bulk page-image review was performed.  The packet's LaTeX source,
preflight record, extracted claims, and mathematical dependencies were
sufficient for the present audit, and the user expressly asked that massive
PDF visual checks stop.

## 3. Audit method

The audit used four independent layers.

1. **Source audit.**  The actual Kahn--Lyubich source was checked at
   `kingdom.tex` and `psiql.tex`, not inferred from the submitted prose.
2. **Proof audit.**  Every proposed theorem was reduced to its set-theoretic,
   boundary, Sobolev, covering/immersion, and Value hypotheses.
3. **Machine audit.**  The supplied tests were reproduced and then attacked
   with records outside their positive fixture.
4. **Dependency audit.**  Every proposed node was compared with the live
   ledger and the still-open direct-decoration trace/welding chain.

The separation between these layers is essential.  A correct finite-label
recursion does not construct an actual puzzle boundary.  A continuous map on
an ideal compactification does not by itself give a bounded Sobolev trace
operator.  A finite matrix identity does not establish a universal dynamical
state.

## 4. Exact source lock

The locked source is Kahn--Lyubich,
*A priori bounds for some infinitely renormalizable quadratics. II.
Decorations*, arXiv:math/0609046.  The audited source file
`kingdom.tex` has SHA-256

```text
5DC04FEFF6B6A1D73040FFD50519C35D62EFF03C1049686DA71D595758E38FA7
```

The relevant source facts are:

- puzzle pieces are closed topological disks (`kingdom.tex`, lines 28 and
  32);
- their boundaries are finite unions of external-ray and equipotential arcs
  (lines 45--48);
- \(P=Y^{(n-1)q+1}\) has \(2^n\) vertices and contains all of the specified
  \(f^{qm}\)-preimages of \(\alpha\) (lines 116--118);
- the vertices have the dyadic/preimage labels used in the source
  (lines 122--130);
- \(P\) has two univalent \(f^q\)-pullbacks \(Q_L,Q_R\subset P\), attached
  at \(\alpha,\alpha'\) respectively (lines 133--137);
- for every vertex \(v\) of \(P\), the source constructs a pairwise-disjoint
  \(f^{nq}\)-pullback \(Q^v\), attached to the two boundary rays of \(P\)
  landing at \(v\) (lines 140--155); and
- a correct combinatorial boundary record distinguishes two consecutive rays
  that meet at one landing vertex from two rays connected by an
  equipotential arc (lines 293--301).

For pseudo-pieces, `psiql.tex` supplies:

- the path-space/universal-cover construction of the Riemann surface
  \(\mathbf Y\) (lines 95--123);
- a degree-\(k\) pseudo-piece covering induced by a puzzle covering and an
  immersion induced by puzzle inclusion (lines 169--207);
- a finite ideal-boundary tiling into \(O\)- and \(J\)-arcs (lines 231--244);
  and
- continuous extension of the induced immersion to that boundary, with the
  warning that its boundary image need not lie in the target boundary
  (lines 248--253).

The source does **not** construct the submitted \(H^1_{\rm fin}\) space,
ideal-arc trace theorem, closed trace quotient, Dirichlet-to-Neumann form,
pulled-versus-immersed welding operator, or physical binary cell
decomposition.

## 5. Proved structural contact theorem

### Theorem 5.1 (fixed-block binary structural contact automaton)

Assume the source-locked direct-decoration package and the already audited
closed-piece hypotheses:

\[
g=f^q,\qquad
g_a=g|_{Q_a}:Q_a\longrightarrow P,\quad a\in\{L,R\},
\tag{5.1}
\]

where \(P,Q_L,Q_R\) are closed Jordan puzzle pieces,
\(Q_L\cap Q_R=\varnothing\), and every degree-one proper branch extends to a
homeomorphism of the closed pieces.  Put

\[
\phi_a=g_a^{-1},\qquad
\phi_w=\phi_{a_1}\circ\cdots\circ\phi_{a_k},\qquad
D_w=\phi_w(P),\qquad
h_w=g^k|_{D_w}.
\tag{5.2}
\]

For \(C_w=\partial P\cap\partial D_w\), set

\[
\widehat C_w=h_w(C_w),\qquad
\widehat C_\varnothing=\partial P.
\tag{5.3}
\]

Then:

1. for \(a\in\{L,R\}\), the landing vertices of the open ray part of
   \(C_a\) are exactly
   \[
   \mathcal V_a
   =
   \{v_{at}:t\in\{L,R\}^{n-1}\},
   \qquad v_s=\phi_s(\alpha);
   \tag{5.4}
   \]
2. for every word \(w\) and letter \(a\),
   \[
   \boxed{\widehat C_{wa}
   =g_a(\widehat C_w\cap C_a)};
   \tag{5.5}
   \]
3. if \(u,v\) are incomparable, then \(D_u\cap D_v=\varnothing\), while
   for \(v=ut\),
   \[
   \boxed{\partial D_u\cap\partial D_v=\phi_u(C_t)};
   \tag{5.6}
   \]
4. for \(|w|=k\le n\), the landing vertices of the open ray contacts in
   \(\partial P\cap\partial D_w\) are exactly
   \[
   \mathcal V(w)=\{v_{wt}:|t|=n-k\},
   \tag{5.7}
   \]
   and
   \[
   h_w(v_{wt})=v_t;
   \tag{5.8}
   \]
5. if \(\mathscr R_\alpha\) is the pair of complete root ray atoms at
   \(\alpha\), then for every \(|s|=n\),
   \[
   \widehat C_s=\mathscr R_\alpha,\qquad
   T_L(\mathscr R_\alpha)=\mathscr R_\alpha,\qquad
   T_R(\mathscr R_\alpha)=\varnothing,
   \tag{5.9}
   \]
   and \(\varnothing\) is absorbing; and
6. after replacing the submitted boundary word by the connector-aware
   boundary incidence graph described in Section 6, the maps
   \[
   T_a(S)=g_a(S\cap C_a)
   \tag{5.10}
   \]
   form a finite exact contact automaton for this one fixed block.

This theorem concerns the structural puzzle-contact skeleton only.  It does
not give a uniform bound as \(q,n\) vary and does not encode arbitrary
protected, obstacle, carrier, Wave, WAD, Value, trace, or enlargement data.

### Proof

The source's separating-family lemma gives \(2^n\) components of
\(\operatorname{dom}(g^n)\), one for each vertex of \(P\).  Under (5.2)
these are the cylinders \(D_s\), each containing
\(v_s=\phi_s(\alpha)\) and attached to the two boundary rays of \(P\) at
that vertex.

If \(s=at\), then \(D_s\subset Q_a\).  A point of a common \(D_s/P\) ray
segment cannot be interior to \(Q_a\), because \(Q_a\subset P\) and the
point lies on \(\partial P\).  Hence that segment belongs to
\(\partial Q_a\cap\partial P\), proving the inclusion
\(\mathcal V_a\subset\operatorname{Vert}(C_a)\).

Conversely, let an open \(Q_a/P\) ray contact land at a vertex \(v\) of
\(P\).  The source gives a unique depth-\(n\) cylinder \(D_s\) attached
there.  If the first symbol of \(s\) were the other letter \(b\), then
\[
v\in Q_a\cap D_s\subset Q_a\cap Q_b,
\]
contrary to closed branch disjointness.  Thus \(s=at\), proving (5.4).

For (5.5), take \(z\in C_{wa}\).  Since
\[
D_{wa}\subset D_w\subset P
\]
and \(z\in\partial P\), the point \(z\) cannot lie in
\(\operatorname{int}D_w\).  Hence \(z\in\partial D_w\), so
\[
x=h_w(z)\in\widehat C_w.
\]
The identity \(D_{wa}=\phi_w(Q_a)\) also gives
\(x\in\partial Q_a\).  Therefore
\[
h_{wa}(z)=g_a(x)\in g_a(\widehat C_w\cap C_a).
\]
Conversely, if \(x\in\widehat C_w\cap C_a\), then
\(z=h_w^{-1}(x)\) lies on \(\partial P\) because
\(x\in\widehat C_w\), and lies on \(\partial D_{wa}\) because
\(x\in\partial Q_a\).  This proves (5.5).

For incomparable \(u,v\), their first differing symbols put the two pieces
in homeomorphic pullbacks of \(Q_L,Q_R\), so they are disjoint.  If \(v=ut\),
then
\[
D_v=\phi_u(D_t),\qquad D_u=\phi_u(P).
\]
Since \(\phi_u\) is a closed-piece homeomorphism,
\[
\partial D_u\cap\partial D_v
=
\phi_u(\partial P\cap\partial D_t)
=
\phi_u(C_t),
\]
which proves (5.6).

For (5.7), every completion \(t\) gives
\(D_{wt}\subset D_w\), attached to \(P\) at \(v_{wt}\).  Its shared ray
segments remain on \(\partial D_w\): a point on \(\partial P\) cannot be
interior to the intermediate subset \(D_w\subset P\).  Conversely, if a
contact vertex of \(D_w\) had source word \(s\) not beginning with \(w\),
then \(D_s,D_w\) would lie in incomparable disjoint cylinders while sharing
that vertex.  Hence \(s=wt\).  Finally,
\[
h_w(v_{wt})
=g^k\phi_w\phi_t(\alpha)
=\phi_t(\alpha)
=v_t,
\]
proving (5.8).

At \(k=n\), only the suffix \(\varnothing\) remains.  The source component
\(D_s\) is attached to the two \(P\)-boundary rays at \(v_s\), and \(g^n\)
maps its deeper equipotential to the root equipotential.  Hence its two
common ray segments map to the complete root ray pair
\(\mathscr R_\alpha\), proving the first part of (5.9).
The branch \(L\) fixes \(\alpha\), and \(f^q\) fixes each ray in the
\(\alpha\)-rotation orbit as a set, so \(T_L\) fixes the pair.  The
first-symbol classification (5.4), rather than closed-set disjointness
alone, shows that the \(R\)-contact has no ray atom landing at
\(\alpha=v_{L^n}\).  Thus \(T_R\) kills the pair.  Equation (5.5) makes
the empty state absorbing.

Finally, the connector-aware graph has finitely many ray edges,
equipotential connectors, vertex joins, and flags.  Subdivide it at the
finite contact endpoints and their branch images.  Landing endpoints move
forward through the finite source preimage tree, while a positive-height
outer endpoint maps to the root equipotential and leaves the child contact
interval.  The forward-saturated subdivision is therefore finite, and
(5.5) acts on its finite set of subcomplexes.  This proves (5.10).
\(\square\)

## 6. The submitted boundary compiler is not source-complete

Push VII encodes a boundary as

\[
\mathsf B(Y)=
\bigl(
\mathsf{Ray}(\theta_i),
\mathsf{Eq}(m;\theta_i,\theta_{i+1})
\bigr)_{i\bmod r}.
\tag{6.1}
\]

This alternation is false for the source boundary.  Kahn--Lyubich explicitly
distinguish:

1. two consecutive rays landing at the same vertex, in which case they are
   joined at that landing point; and
2. two rays with different landing points, in which case an equipotential
   arc joins them.

A faithful finite record must therefore include

\[
\begin{aligned}
\mathsf{RayEdge}
&=(\theta,[t_{\rm in},t_{\rm out}],v_{\rm land},
   \text{side},\text{orientation}),\\
\mathsf{Connector}
&\in
\{\mathsf{VertexJoin}(v),
  \mathsf{EqJoin}(m;\theta_i,\theta_{i+1})\}.
\end{aligned}
\tag{6.2}
\]

The landing-equivalence relation and incident flags are essential.  The
submitted program represents a ray endpoint by the coordinate
\((\theta,t)\); two distinct external angles landing at the same Julia
vertex therefore cannot be identified by its geometric matcher.  Its
source-shaped \(q=1\) fixture is expressly not an actual Kahn--Lyubich
parameter block and cannot establish source realization.

What remains correct is the mathematical fact that equal-angle ray
intervals determine the positive-length contacts once the actual landing
incidence is supplied, and distinct equipotential levels have no
positive-length overlap.

## 7. Pseudo-boundary topology is not Sobolev trace theory

The source justifies a narrow topological statement: after an appropriate
finite subdivision, a selected degree-one pseudo-piece covering transports
ideal-boundary arcs and their endpoint flags.  If the extension is proved
homeomorphic on the selected compactified arcs and the subdivision is
closed under branch images and preimages, then each child atom has one
parent and a root atom has at most one lift per branch.  These atom relations
compose along words.

Push VII does not prove those extra boundary-homeomorphism and closure
hypotheses in the complete marked setting, so no separate pseudo-boundary
ledger node is promoted here.

More importantly, the source does not define

\[
\mathcal T_{\mathbf Y}(B)
=
H^1_{\rm fin}(\mathbf Y)/
\{u:\operatorname{Tr}_B u=0\}.
\tag{7.1}
\]

To use (7.1), one must still prove:

1. a precise conformal or prime-end compactification for every selected
   pseudo-piece;
2. a homogeneous Dirichlet space modulo the correct global constants, or a
   consistently transported grounding;
3. bounded trace and extension operators on every selected ideal arc;
4. closed zero-trace kernels and complete quotient spaces;
5. closedness of every compatible tuple image;
6. unitary branch pullback for the homogeneous energy;
7. all cross-\(H^{1/2}\) compatibility terms under subdivision; and
8. uniform control if the spaces are to form a global state.

The packet's added local \(L^2\) normalization does not repair this.  If
\(\varphi\) is conformal, Dirichlet energy is invariant in two dimensions,
but

\[
\int |u\circ\varphi|^2\,dA
=
\int |u|^2|(\varphi^{-1})'|^2\,dA
\tag{7.2}
\]

is not invariant without transporting the normalization and proving an
equivalence estimate.

Endpoint flags must also remain separate combinatorial data.  An
\(H^{1/2}\) boundary trace is an almost-everywhere class; endpoint evaluation
is not a continuous coordinate at that regularity.

Finally, subdivision does not replace one trace space by an unrestricted
product.  On \((-1,1)\), the two half-interval functions

\[
u_-=0\text{ on }(-1,0),\qquad
u_+=1\text{ on }(0,1)
\]

belong separately to the half-interval trace spaces, but their union is not
in \(H^{1/2}(-1,1)\), since

\[
\int_{-\varepsilon}^{0}\int_0^\varepsilon
\frac{|u_-(x)-u_+(y)|^2}{|x-y|^2}\,dy\,dx
=\infty.
\tag{7.3}
\]

Thus the response-refinement conclusion requires the compatible image with
its quotient norm and nonlocal cross-energy.  It cannot be inferred from
finite atom refinement.

## 8. The omitted pulled-versus-immersed correspondence

The packet tracks only the dynamical pseudo-cover

\[
\mathbf g_a:\mathbf Q_a\longrightarrow\mathbf P.
\tag{8.1}
\]

The source also has the inclusion-induced map

\[
\mathbf i_a:\mathbf Q_a\longrightarrow\mathbf P,
\tag{8.2}
\]

which is generally an immersion.  Its routing need not be injective, and
its ideal-boundary image need not lie in the target ideal boundary
(`psiql.tex`, lines 198--206 and 248--253).

A physical shell/response comparison needs both copies and the
correspondence between them.  The assertion that the pseudo-puzzle removes
the welding problem is therefore false: the missing welding has moved to
the relation between (8.1) and (8.2).

The exact repair is to construct the pulled and immersed carriers together,
prove their interface equality or an admissible relative-cover
correspondence, retain the induced welding operator, and establish subgroup
compatibility, properness/end-properness, and full interface coverage.
These are still the live contents of
`DIRECT_DECORATION_TRACE_WELDING_COMPACTNESS` and
`DIRECT_DECORATION_TRACE_COLLAR_REALIZATION`.

## 9. Safe-gap and response counterchecks

The hypothesis

\[
K_0\subset S\subset S^+
\subset P\setminus(Q_L\cup Q_R)
\tag{9.1}
\]

does not imply that \(S^+\) is disjoint from \(\partial P\), a trace
interface, or a protected mark.  In a disk \(P\) containing two disjoint
child disks, a compact connected set can run through the gap from \(K_0\)
to an unused arc of \(\partial P\) while avoiding both children.  It then
creates a new boundary attachment.

Therefore the existing `PULLBACK_GAP_ENLARGEMENT_NATURALITY` conclusion
remains exactly topological: finite fibers, inverse words, and shift squares
are unchanged.  Protected-access and analytic-carrier admissibility do not
follow.

A trace-atlas invariance theorem would require at least

\[
S^+\Subset
\operatorname{component}_{K_0}
\left(
\operatorname{int}P\setminus(Q_L\cup Q_R)
\right)
\tag{9.2}
\]

and positive separation from every declared boundary interface, obstacle,
collar, electrode, port, and protected access.  Even then, only the boundary
atlas is unchanged; the cap response changes and must be retained as changed
input.

Likewise, the recurrence

\[
Q_{r+1}
=
\mathcal B\star
\left(Q_r^{(L)}\oplus Q_r^{(R)}\right)
\tag{9.3}
\]

is a valid conditional domain-decomposition identity only after
\(\mathcal B\), its two genuine interfaces, the trace Hilbert spaces, the
immersed copy, the cap, and the actual physical gluing have been constructed.
Pseudo-piece immersions are not a proof that the parent is a disjoint union
of one root cell and two embedded child cells.  Hence
`BINARY_OPERADIC_RESPONSE_COMPILER` is not a geometric theorem established
by the packet.

## 10. Fixed-tree KKL pair-state moment factorization

### Theorem 10.1

Let \(T\) be one fixed finite terminal Hubbard tree with edge set \(E\).
Use the source incidence

\[
N_{\beta\gamma}
=
\#\{\alpha\in\iota^*\beta:f_*\alpha=\gamma\},
\qquad
Nv=\lambda v,\qquad
N^\top w=\lambda w.
\tag{10.1}
\]

In the project's source-column convention \(B=N^\top\), \(v\) is the
project left eigenweight and \(w\) the project right eigenweight.  For

\[
\mathcal A_m=\iota_m^*\mathcal H^{\rm biv},
\qquad
s_m(\alpha)=
\bigl(f_*^m\alpha,(\iota_m)_*\alpha\bigr)\in E\times E,
\tag{10.2}
\]

define

\[
a_{e,e'}=v(e)\sqrt{w(e')},
\tag{10.3}
\]

and, for every level-\(m\) arc \(\gamma\),

\[
z_m(\gamma)_{e,e'}
=
\sum_{\substack{\alpha\in\mathcal A_m\\
s_m(\alpha)=(e,e')}}
\langle\alpha,\gamma\rangle.
\tag{10.4}
\]

For a finite nonnegative WAD \(X\), put

\[
\mathsf M_m(X)
=
\sum_\gamma
X(\gamma)z_m(\gamma)z_m(\gamma)^\top.
\tag{10.5}
\]

Then

\[
\boxed{
\operatorname{Val}(X)
=
\lambda^{-2m}
\left\langle aa^\top,\mathsf M_m(X)\right\rangle
}
\tag{10.6}
\]

and

\[
\dim\operatorname{Sym}
\left(\mathbb R^{E\times E}\right)
=
\frac{|E|^2(|E|^2+1)}2.
\tag{10.7}
\]

### Proof

KKL's pulled-arc coefficient is

\[
\ell_m(\gamma)
=
\lambda^{-m}
\sum_{\alpha\in\mathcal A_m}
\langle\alpha,\gamma\rangle
v(f_*^m\alpha)
\sqrt{w((\iota_m)_*\alpha)}.
\tag{10.8}
\]

Grouping the sum by the pair state (10.2) gives

\[
\ell_m(\gamma)
=
\lambda^{-m}a^\top z_m(\gamma).
\tag{10.9}
\]

Using KKL's definition
\(\operatorname{Val}(X)=\sum_\gamma X(\gamma)\ell_m(\gamma)^2\),

\[
\begin{aligned}
\operatorname{Val}(X)
&=
\lambda^{-2m}
\sum_\gamma X(\gamma)
a^\top z_m(\gamma)z_m(\gamma)^\top a\\
&=
\lambda^{-2m}
\left\langle
aa^\top,
\sum_\gamma
X(\gamma)z_m(\gamma)z_m(\gamma)^\top
\right\rangle,
\end{aligned}
\]

which is (10.6).  The pair-state space has cardinality \(|E|^2\), so its
symmetric matrices have dimension (10.7).  Positivity follows because
(10.5) is a nonnegative sum of rank-one positive-semidefinite matrices.
\(\square\)

The exponent \(\lambda^{-2m}\) is compatible with KKL's aggregate
\(\lambda^{-m}\) pullback contraction: the latter also sums over all pulled
arcs, and the eigenweight identities contribute the remaining factor.

The packet's completely positive branch update

\[
\mathsf M'\stackrel{?}=P_a\mathsf M P_a^\top
\tag{10.10}
\]

is not promoted.  It requires an actual typed incidence theorem proving
\(z'(b_a^*\gamma)=P_a z(\gamma)\) for every realized WAD support arc, with
correct weights, no omitted state, and no illicit merger.  The joint
two-branch formula also requires disjointness of the two contributions in
the relevant WAD category.  Push VII constructs neither factor.

The dimension (10.7) depends on \(|E|\).  The theorem gives neither a
universal dimension nor a Value comparison constant, future-observability
gap, or strict transition.  Its possible use is to carry several future
Value rows on one fixed tree, not to replace the existing scalar observation
of current Value.

## 11. Matrix-product identity

For fixed matrices, the submitted identity

\[
\sum_{s\in\{L,R\}^r}
(u^\top M_sv)R_sx
=
(u^\top\otimes I)
(M_L\otimes R_L+M_R\otimes R_R)^r
(v\otimes x)
\tag{11.1}
\]

is correct by expansion of the noncommutative matrix power.  The exact
script checks it successfully.

Equation (11.1) is a standard Kronecker word-sum identity, not a constructed
geometric future quotient.  It presupposes fixed stationary coefficient and
feature representations of dimensions \(d,w\).  The packet does not prove
that the required trace, WAD, protected, or Value observables have such a
universal representation.  The identity is retained in the assessment as
supporting algebra but is not added as a proof-ledger node.

## 12. Adversarial compiler audit

The positive tests establish self-consistency only for the supplied finite
fixture.  The compiler does not validate several conclusions claimed in its
prose.

The following adversarial mutations all return `passed=true`:

1. remove the entire parent and child boundary-word inventory;
2. replace a shorter-word normalized vertex by an arbitrary value that
   violates the claimed shift itinerary;
3. add a second \(L\)-branch child over one root atom, producing three total
   lifts although the theorem claims at most two;
4. replace the flag map by an arbitrary reversed permutation;
5. remove the endpoint-flag atlas entirely; and
6. provide empty refinement relations.

The exact observed examples include:

```text
missing_boundary_words       passed=true
false_vertex_shift           passed=true
two_L_lifts_same_atom        passed=true, maximum total lifts=3
arbitrary_flag_permutation   passed=true
```

There are additional schema defects:

- `source_vertex_shift_checks` reports suffix chains but does not test
  \(g(v_{as})=v_s\);
- `check_word_functoriality` leaves the normalized parent label fixed and
  compares two counts generated from the same declaration, so it does not
  verify an actual composed boundary map;
- cyclic order is never checked;
- at-most-one lift per branch is not enforced;
- `passed` ignores the completeness of point contacts and flags;
- an equipotential match tests the integer `level` while ignoring a
  conflicting explicit `potential`;
- the fixture's declared atom atlas is not tied to its boundary geometry:
  only \(4/16\) declared child-parent atom IDs per branch occur among the
  actual child boundary-edge IDs, and no child boundary flag occurs among
  the keys of the declared flag map;
- the compiler has no \(q\) field and never checks the
  \(2^q\)-angle or equipotential-level branch law; and
- it instantiates no Sobolev space, trace operator, Dirichlet form,
  inclusion immersion, response, or root-enlargement map.

The baseline report itself requests 24 parent and 8 child subdivisions.
That is not a failure, but it further shows that the fixture is a
user-supplied combinatorial schema rather than a compiled source block.

The scripts remain useful diagnostic tools for exact finite labels and the
two algebraic identities.  They are not proof certificates for the rejected
analytic claims.

## 13. Claim-by-claim disposition

| Push-VII claim | Decision | Exact reason |
|---|---|---|
| Binary branch setup and word orientation | **Use** | Correct under the explicit closed-disjoint Jordan branch package. |
| First-symbol contact vertices | **Use** | Follows from the source depth-\(n\) attachment fan and branch disjointness. |
| Submitted boundary-word compiler | **Reject** | Omits vertex joins/landing equivalence and is not instantiated on an actual source block. |
| Exact contact recursion | **Use** | Equation (5.5) is a direct closed-set/homeomorphism identity. |
| Complete pairwise cylinder contacts | **Use** | Equation (5.6) follows from first differing symbols and pullback homeomorphisms. |
| Prefix endpoint itinerary | **Use structurally** | Exact through depth \(n\); flags require the corrected incidence record. |
| Two-state post-\(n\) collapse | **Use structurally** | Valid only for the puzzle-contact skeleton, not protected or Value marks. |
| Finite pseudo-boundary atom relation | **Retain conditionally** | Needs boundary-homeomorphism and subdivision-closure proofs; it is not a Sobolev trace theorem. |
| \(H^1_{\rm fin}\) pseudo-trace atlas | **Reject** | The analytic trace space, quotient, extension, and closedness theorems are absent. |
| Trace word functoriality | **Reject analytically** | Topological maps compose, but the trace objects are undeclared and their typing is ambiguous. |
| Normalized overlay response naturality | **Reject** | Omits the inclusion immersion, welding, cap geometry, and physical gluing fibers. |
| Safe-gap trace-atlas invariance | **Reject as stated** | Avoiding \(Q_L,Q_R\) does not prevent a new boundary/interface attachment. |
| Certified refinement atom squares | **Use as a conditional finite-set identity** | Does not construct a final enlargement or justify trace/response refinement. |
| Binary operadic response compiler | **Retain only conditionally** | Requires an actual analytic cell decomposition and trace category not supplied. |
| Matrix-product future quotient | **Retain as standard algebra only** | The identity is exact; the required stationary geometric transducer is unproved. |
| Fixed-block KKL moment state | **Use after correction** | Equation (10.6) is exact; branch CP transport and universal dimension remain open. |
| Fifteen-node patch | **Reject** | Over-split, contains false analytic promotions, and has schema/evidence defects. |
| New umbrella open node | **Do not add** | Duplicates the live direct-decoration trace/welding and H2 gates. |

## 14. Ledger-patch defects

The submitted JSON patch is not mechanically authoritative.

- Six evidence anchors do not match the memo's actual section numbering.
- The evidence file is outside the authoritative ledger directory unless
  copied and audited.
- `source_hypothesis` is not an authoritative dependency status and would be
  ignored by the current generator.
- `maps_to` is not a live dependency edge.
- `VAAPC-I` is a clause label, not a top-level ledger ID.
- The proposed open node has neither live dependencies nor an authoritative
  evidence path.
- Several analytic nodes omit the still-open trace-collar and welding
  prerequisites.
- Adding fifteen proved nodes would create bookkeeping growth without
  corresponding independent theorem content.

The two adopted nodes are deliberately consolidated around independent
mathematical conclusions.

## 15. Correct next obligation

Push VII closes the **unmarked structural binary-contact skeleton** for one
fixed block.  It does not close the marked analytic interface.  The immediate
next theorem should therefore not be the packet's proposed strict transition.
The response state to which that transition would apply still does not
exist.

The correct next obligation is:

### Pulled/immersed connector-aware trace realization

For every proof-used fixed direct-decoration block:

1. augment the proved unmarked connector-aware structural graph with the
   complete proof-use marked incidence data, retaining landing equivalence,
   sides, cyclic order, and every marked point contact;
2. instantiate that marked overlay and both of its analytic map copies on an
   actual source-locked Kahn--Lyubich block rather than on the \(q=1\)
   schematic fixture;
3. freeze the complete proof-use overlay: protected accesses, obstacles,
   electrodes, phase, orientation, carrier contacts, and enlargement marks;
4. construct both the dynamical covering copy and the inclusion-immersed
   copy of every interface;
5. prove the required relative-cover subgroup compatibility,
   properness/end-properness, and interface coverage;
6. construct a homogeneous grounded trace Hilbert space with bounded trace
   and extension operators on the selected ideal arcs;
7. prove that all finite refinements retain the compatible image and its
   cross-\(H^{1/2}\) energy;
8. prove final-root naturality under a genuinely separated enlargement
   hypothesis; and
9. only then define and study the full response/welding cocycle and its KKL
   pair-state incidence factor.

After these clauses are proved, the fixed-tree moment factorization can be
tested against the actual trace/WAD transport.  Universal dimension and a
strict mixed-block transition remain later tasks.

## 16. Global status

Push VII sharpens the direct-decoration frontier from

\[
\text{unknown all-depth structural contacts}
\]

to

\[
\text{proved fixed-block structural contact automaton}.
\]

It also supplies the exact fixed-tree identity

\[
\text{KKL Value}
\longrightarrow
\text{finite pair-state PSD moment}
\]

with dimension depending on the tree.

The unresolved passage is still

\[
\begin{gathered}
\text{complete marked pulled/immersed interface}\\
\Downarrow\\
\text{valid trace Hilbert spaces and welding/response cocycle}\\
\Downarrow\\
\text{universal WAD/Value future observability}\\
\Downarrow\\
\text{strict mixed-block transition}\\
\Downarrow\\
\text{coercivity and rigidity}.
\end{gathered}
\]

VAAPC-I, H2, MBTT, H3, H4, UPTCR, and MLC remain open.

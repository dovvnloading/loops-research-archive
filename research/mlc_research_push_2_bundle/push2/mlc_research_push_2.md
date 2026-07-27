# Research push II: critical chronology conservation and quadratic telescope assembly

**Project:** A marked-width reduction of Mandelbrot local connectivity  
**Status:** theorem-level research note; no claim of an unconditional proof of MLC  
**Date:** 2026-07-24

## Executive result

This note attacks the next analytic/formal layer upstream of the virtual marked correspondence. The starting point is the directly visible decoration atlas already constructed in the manuscript: its root first-return map has exactly one central branch with chronological degree word

\[
(2,1,\ldots,1),
\]

and every other return branch is univalent. Its two univalent separator pullbacks also generate the rooted-end compactification from Research Push I. The remaining scale-two task is to transfer the next satellite portrait to finite cylinders and end fibers with exact critical chronology, prime-end action, and final-root naturality.

The main findings are:

1. **Critical-cut conservation law.** For commuting iterates \(f^N\) and \(f^r\), the complete critical word is conserved, but the cut between the cylinder map and the return branch moves. Consequently, cylinder conjugacy can shift the declared quadratic time even when the total degree and both endpoint cylinder maps are unchanged.
2. **Proper-square degree conservation.** In a proper commuting square, degrees satisfy
   \[
   \deg H\,\deg h_1=\deg h_0\,\deg F.
   \]
   With a univalent source cylinder and a quadratic root branch, the unique quadratic degree is forced either into the lifted branch or into the target-cylinder projection.
3. **All off-critical transfer closes.** If the root branch is univalent, its lift through any univalent direct-decoration cylinder is automatically univalent, and the target projection is automatically univalent. The actual target base is the image of the lifted branch. Prime-end phase and cyclic order transport functorially. Thus every noncentral finite-cylinder branch of the first decoration atlas is formal.
4. **The central finite-cylinder branch has an explicit retimed correspondence.** If a root quadratic-like restriction satisfies \(A\Subset B\Subset P\), then every finite cylinder \(w\) carries the actual pair
   \[
   (g_w,\iota_w)=(f^{N_w+r},f^{N_w}):U_w\rightrightarrows B.
   \]
   The common univalent prefix occurs in both entries, so the relative critical word is exactly the root word. The pair is shift-equivariant and transports every root marking by conformal pullback.
5. **Two exact no-go examples.** For \(f(z)=z^2-1\), a commuting lift can move the quadratic stage completely into the target projection. More strongly, both source and target cylinder maps and both total return degrees can be correct while the chronological words change from \((2,1)\) to \((1,2)\). Total degree and endpoint conjugacy do not certify chronology.
6. **Stagewise ladder criterion.** Exact critical chronology is equivalent to univalence of every transverse cylinder projection at every intermediate time. This converts a vague metadata condition into a finite geometric avoidance test.
7. **Quadratic base-change dichotomy.** Pulling a degree-two proper disk map back over an embedded Jordan subdisk preserves degree two exactly when the subdisk contains the critical value. If it omits the critical value, the pullback splits into two univalent components.
8. **Critical-spine telescope compiler.** A finite covering/embedded stage chain with one quadratic stage has a canonical connected degree-two fiber-product component precisely when every post-quadratic base change retains the propagated critical value. The first omitted critical value is an exact failure certificate.
9. **Marked finite-horizon assembly.** Once actual proper, core-proper, covering-embedded stages and their marked squares are supplied, the telescope has a degree-two endpoint covering, an endpoint immersion, exact summed iterate, exact concatenated critical word, compositional relative-cover lifts, and compositional prime-end action.
10. **Canonical end prime ends and planar collapse.** Under the source ray/equipotential puzzle geometry, every infinite address determines a canonical external prime end whose impression is the nested end fiber. Yet every unrescaled inverse-branch chart collapses on compact subsets; finite Julia copies have diameter tending to zero.
11. **The normalized end germ is exactly constant, and a blow-up is necessary.** In cylinder coordinates, every retimed finite portrait is identically the root pseudo-quadratic-like pair. Any Hausdorff end compactification retaining this nondegenerate carrier and projecting continuously to the original plane must therefore have a nontrivial projection fiber or use a rescaling/prime-end blow-up.
12. **Fixed-iterate end-fiber action is formal after finite-stage compatibility.** A compatible nested family for one fixed polynomial iterate extends by intersection to the corresponding end fibers. Retimed coverings whose exponents grow with the word are instead represented by the normalized germ.

### Measurable ledger effect

The latest library build inspected for this note records 52 open obligations. Because that build may already incorporate parts of earlier research pushes, no cross-push count is added here. The conservative status change proved here is:

- `FINITE_HORIZON_ASSEMBLY`: open to proved, as a compiler theorem under its stated compatible proper, core-proper, covering-embedded hypotheses.

The current `MAPPING_TELESCOPE` statement is under-specified and is false if it is intended to follow only from degree-two factorization. This note gives the exact replacement theorem and the counterexample. If the node is rewritten with the critical-value-retention hypothesis proved below, it can also be promoted. Hence:

- conservative count: **52 to 51**;
- corrected-statement count: **52 to 50**;

The source-facing problem does not disappear. It is sharply reduced to an **analytic end-blow-up and protected critical-spine realization theorem**, together with protected access/obstacle realization and final-root stability.

---

# Part I. Source boundary and exact target

## 1. What the manuscript already supplies

At the native principal-nest level and at the first directly visible decoration scale, the manuscript proves actual first-return atlases. Each atlas has:

- pairwise disjoint Jordan return domains compactly contained in the base;
- exact positive integer return times;
- exactly one central return whose first one-step factor has degree two and whose remaining factors are univalent;
- all noncentral returns univalent;
- actual component, parent, sheet, prime-end, and external-angle phase data.

The direct-decoration compactification additionally gives univalent cylinder maps

\[
h_w=f^{N_w}|_{Q_w}:Q_w\longrightarrow P,
\]

where \(N_w=q|w|\) for a finite binary word \(w\), together with connected end fibers obtained as nested intersections of cylinders.

The manuscript leaves the second satellite portrait open because a root branch must be transferred to these cylinders and end fibers with:

- the declared critical chronology;
- actual target bases;
- protected analytic prime ends;
- obstacle and sheet data;
- terminal compatibility;
- naturality under root enlargement.

## 2. Why this is the correct place to work

The direct-decoration topology is no longer the primary obstacle after Research Push I:

- finite pullback components have isolated equivariant gap cells;
- the entire rooted-end package is nonseparating;
- finite protected packet replacements preserve global nonseparation;
- target components, once authorized, are unique;
- future-faithful compact trace topology and symbolic side compactness have formal solutions.

The first genuinely analytic issue is therefore whether the polynomial branch on a root base can be transported through the univalent cylinder system **without moving its critical encounter to a different part of the commuting square**.

## 3. Source comparison

KKL define a pseudo-quadratic-like map as a pair consisting of a double branched covering and an immersion, and globally iterate such maps through component-wise projections. Dudko's virtual-Molecule proposal instead remains a strategy involving connected hulls of Cantor small Julia sets that retain the critical orbit through an appropriate number of first returns. Neither source supplies the scale-two critical-spine transfer established as the next target below.

Nothing in this note imports an unpublished virtual-renormalization theorem. All results below are elementary consequences of holomorphic local degree, proper maps of Jordan disks, fiber products along embeddings, and the already realized first decoration atlas.

---

# Part II. The critical-cut conservation law

## 4. Local degree and critical words

For a nonconstant holomorphic map \(G\) and a point \(z\), write

\[
e_G(z)\in\mathbb N
\]

for the local degree, or ramification index, of \(G\) at \(z\). Thus \(e_G(z)=1\) exactly when \(G\) is locally univalent at \(z\), and

\[
e_{G\circ H}(z)=e_H(z)e_G(H(z)).
\]

For a quadratic polynomial

\[
f(z)=z^2+c,
\]

let

\[
\chi_j(z)=
\begin{cases}
2,&f^j(z)=0,\\
1,&f^j(z)\ne0.
\end{cases}
\]

The chronological degree word of length \(r\) at \(z\) is

\[
\mathbf d_r(z)=(\chi_0(z),\chi_1(z),\ldots,\chi_{r-1}(z)).
\]

Its product is the local degree of \(f^r\):

\[
e_{f^r}(z)=\prod_{j=0}^{r-1}\chi_j(z).
\]

The definition continues to make sense for domains: the word of a proper branch is the ordered list of one-step degrees along its selected component chain.

## 5. Critical-cut identity

### Theorem 1 - Critical-cut conservation

Let \(f\) be a holomorphic map and let \(N,r\ge1\). For every point \(z\),

\[
e_{f^r}(z)e_{f^N}(f^r z)
=
 e_{f^N}(z)e_{f^r}(f^N z).
\tag{5.1}
\]

For a quadratic polynomial, the chronological words satisfy

\[
\mathbf d_r(z)\star \mathbf d_N(f^r z)
=
\mathbf d_N(z)\star \mathbf d_r(f^N z)
=
\mathbf d_{N+r}(z),
\tag{5.2}
\]

where \(\star\) denotes concatenation.

#### Proof

The iterates commute:

\[
f^N\circ f^r=f^r\circ f^N=f^{N+r}.
\]

Applying multiplicativity of local degree to the two factorizations gives (5.1). For the word statement, the first concatenation records critical encounters at absolute times

\[
0,1,\ldots,r-1,r,r+1,\ldots,r+N-1,
\]

while the second records the same absolute times with the cut after \(N\). Both are the complete length-\(N+r\) word. ∎

### Corollary 2 - Critical-count transfer

For a quadratic polynomial, define

\[
m_k(z)=\#\{0\le j<k:f^j(z)=0\}.
\]

If \(f^N\) is locally univalent at \(z\), then

\[
m_N(f^r z)=m_r(f^N z)-m_r(z).
\tag{5.3}
\]

In particular, the target \(N\)-step projection is locally univalent at \(f^r z\) exactly when the lifted and root \(r\)-step branches have the same total local degree at corresponding points.

#### Proof

For a quadratic polynomial, \(e_{f^k}(z)=2^{m_k(z)}\). Put \(e_{f^N}(z)=1\) in (5.1) and take base-two logarithms. ∎

### Warning 3 - Total degree is weaker than chronology

Equation (5.3) controls only the number of critical encounters. The ordered windows

\[
(\chi_0(z),\ldots,\chi_{r-1}(z))
\quad\text{and}\quad
(\chi_N(z),\ldots,\chi_{N+r-1}(z))
\]

can have the same product while placing the unique quadratic step at different times. Exact critical chronology therefore requires a stagewise condition, not merely equality of total degrees.

---

# Part III. Proper commuting squares and criticality transfer

## 6. Degree conservation in a proper square

Consider a commuting square of proper holomorphic maps between connected finite-type bordered Riemann surfaces:

\[
\begin{CD}
U @>H>> V\\
@Vh_0VV @VVh_1V\\
A @>F>> B.
\end{CD}
\tag{6.1}
\]

Thus

\[
h_1\circ H=F\circ h_0.
\]

### Theorem 4 - Proper-square degree conservation

The total degrees satisfy

\[
\deg(H)\deg(h_1)=\deg(h_0)\deg(F).
\tag{6.2}
\]

At every \(x\in U\),

\[
e_H(x)e_{h_1}(H(x))
=
 e_{h_0}(x)e_F(h_0(x)).
\tag{6.3}
\]

If \(h_0\) is univalent, then:

1. if \(F\) has degree one, both \(H\) and \(h_1\) have degree one;
2. if \(F\) has degree two, precisely one of the following occurs:
   \[
   (\deg H,\deg h_1)=(2,1)
   \tag{6.4a}
   \]
   or
   \[
   (\deg H,\deg h_1)=(1,2).
   \tag{6.4b}
   \]

#### Proof

The degree of a composition of proper maps is the product of degrees. Apply this to the two equal compositions in (6.1), proving (6.2). Equation (6.3) is the local version. If \(\deg h_0=1\), then (6.2) becomes

\[
\deg H\deg h_1=\deg F.
\]

The conclusions follow because all degrees are positive integers. ∎

### Interpretation

For a quadratic root branch and a univalent source cylinder, the unique quadratic degree cannot disappear. It has exactly two possible locations:

- **branch-retained:** the lifted branch is quadratic and the target projection is univalent;
- **criticality swap:** the lifted branch is univalent and the target projection is quadratic.

The first case is the desired finite-cylinder transfer. The second is an exact obstruction to treating the target as one of the univalent equal-depth cylinders.

## 7. Every off-critical branch transfers automatically

The preceding statement still assumes a completed proper square. For a univalent root branch, the target square can be constructed directly.

### Theorem 5 - Off-critical cylinder transfer

Let \(f\) be a polynomial. Let

\[
h_0=f^N|_U:U\longrightarrow A
\]

and

\[
F=f^r|_A:A\longrightarrow B
\]

be conformal isomorphisms between plane domains. Define

\[
H=f^r|_U,
\qquad
V=H(U),
\qquad
h_1=f^N|_V.
\]

Then:

1. \(H:U\to V\) is a conformal isomorphism;
2. \(h_1:V\to B\) is a conformal isomorphism;
3. the square
   \[
   h_1\circ H=F\circ h_0
   \tag{7.1}
   \]
   commutes;
4. if \(U,A,B\) are Jordan domains and the maps extend to their closures, then \(V\) is a Jordan domain and the square extends to orientation-preserving homeomorphisms of prime-end circles;
5. every finite endpoint marking, protected crosscut chain, phase, and cyclic order on the root square transports exactly to the lifted square.

#### Proof

Suppose \(H(x_1)=H(x_2)\). Applying \(f^N\) and using commutation gives

\[
F(h_0(x_1))=F(h_0(x_2)).
\]

Both \(F\) and \(h_0\) are injective, so \(x_1=x_2\). Hence \(H\) is injective and therefore a conformal isomorphism onto \(V\).

For \(y=H(x)\in V\),

\[
h_1(y)=f^N(f^r(x))=f^r(f^N(x))=F(h_0(x)).
\]

As \(x\) runs over \(U\), the right side runs bijectively over \(B\). Therefore \(h_1\) is a holomorphic bijection \(V\to B\), hence conformal. The prime-end and marking conclusions follow by functoriality of the Caratheodory compactification and the commuting square. ∎


## 7A. Retimed pullback correspondences solve the finite-cylinder criticality problem

The criticality-swap obstruction applies only if one insists on lifting the same return iterate from a source cylinder to an equal-depth target cylinder. A pseudo-quadratic-like correspondence permits a different and better construction: use the cylinder iterate itself as the immersion and append the root return to form the covering.

### Lemma 5A - Localized quadratic-like restriction

Let

\[
F_0=f^r|_{A_0}:A_0\longrightarrow B_0
\]

be a quadratic-like map with connected filled Julia set \(K\). If \(W\) is any Jordan neighborhood with

\[
K\Subset W\Subset B_0,
\]

then there are Jordan disks

\[
K\Subset A\Subset B\Subset W
\]

for which

\[
F=f^r|_A:A\longrightarrow B
\]

is quadratic-like of the same degree, has the same filled Julia set \(K\), and has the same chronological critical word as \(F_0\).

#### Proof

Use the external Böttcher coordinate of the connected polynomial-like map. Sufficiently low equipotentials give a Jordan target \(B\Subset W\); the component \(A\) of \(F_0^{-1}(B)\) containing \(K\) is compactly contained in \(B\), maps properly onto it with the original degree, and has the same nonescaping set. Restriction changes no iterate or critical encounter. ∎

This removes a possible localization ambiguity: once the actual next root renormalization and its filled Julia set lie in the direct-decoration gap, its root portrait can be chosen entirely inside that gap before any cylinder pullback.

### Theorem 5B - Retimed finite-cylinder pullback correspondence

Let

\[
F=f^r|_A:A\longrightarrow B
\]

be a proper holomorphic branch between Jordan disks with

\[
A\Subset B\Subset P.
\]

Let

\[
h_w=f^{N_w}|_{Q_w}:Q_w\longrightarrow P
\]

be one of the actual univalent direct-decoration cylinder maps. Put

\[
U_w=h_w^{-1}(A),
\]

and define two actual polynomial restrictions with common source and target:

\[
g_w=f^{N_w+r}|_{U_w}=F\circ h_w:U_w\longrightarrow B,
\tag{7.2}
\]

\[
\iota_w=f^{N_w}|_{U_w}:U_w\longrightarrow A\hookrightarrow B.
\tag{7.3}
\]

Then:

1. \(g_w\) is proper and
   \[
   \deg g_w=\deg F;
   \]
2. \(\iota_w\) is a conformal embedding;
3. the pair \((g_w,\iota_w)\) is a covering/embedded correspondence into the common target \(B\);
4. if the cylinder word is univalent, then
   \[
   \operatorname{word}(g_w)
   =
   (\underbrace{1,\ldots,1}_{N_w})\star\operatorname{word}(F),
   \qquad
   \operatorname{word}(\iota_w)
   =
   (\underbrace{1,\ldots,1}_{N_w});
   \tag{7.4}
   \]
   hence the relative critical word of the pair is exactly the root word of \(F\);
5. if \(K\subset A\) is the compact full filled carrier of \(F\), so \(F^{-1}(K)=K=F(K)\) within the polynomial-like restriction, then
   \[
   K_w=h_w^{-1}(K)
   \]
   is compact and full, and
   \[
   g_w^{-1}(K)=\iota_w^{-1}(K)=K_w,
   \qquad
   g_w(K_w)=\iota_w(K_w)=K;
   \tag{7.5}
   \]
6. every root endpoint set, protected crosscut chain, obstacle, sheet label, and normalized phase pulls back by the conformal map \(h_w\), and exact covering-versus-immersion marking action is preserved;
7. if \(s=f^q:Q_{aw}\to Q_w\) is the direct-decoration shift branch, then on the pulled source domains
   \[
   g_{aw}=g_w\circ s,
   \qquad
   \iota_{aw}=\iota_w\circ s;
   \tag{7.6}
   \]
8. every certified root enlargement inside \(P\) pulls back functorially to all finite words.

#### Proof

The identity (7.2) is commutation of polynomial iterates. Since \(h_w\) is conformal and \(F\) is proper, their composition is proper with the same degree. Equation (7.3) is a conformal embedding into \(A\subset B\).

The chronological word of a composition is the concatenation of the word of its first factor with that of its second factor. The \(N_w\)-step cylinder factor is univalent, proving (7.4). Thus the source prehistory occurs in both entries of the correspondence and cancels from the relative degree data; the unique quadratic stage remains in the covering relative to the immersion.

Equation (7.5) follows from \(F^{-1}(K)=K=F(K)\) and the definition of \(K_w\). The homeomorphism of closed Jordan pieces extends to a sphere homeomorphism, so it preserves fullness. For a closed endpoint set \(E\) in the marked target,

\[
E_{g_w}=h_w^{-1}(E_F),
\qquad
E_{\iota_w}=h_w^{-1}(E_{\mathrm{incl}}).
\]

Therefore every root endpoint containment, refinement, proper/end-proper interval, phase, and cyclic-order assertion pulls back exactly. Obstacles and component labels pull back by the same homeomorphism.

Finally, the direct-decoration inverse-word relation gives

\[
h_{aw}=h_w\circ s.
\]

Composing with \(F\) proves (7.6). Enlargement naturality follows from the same identities after restricting the conformal inverse branches. ∎

### Corollary 5C - The finite-cylinder quadratic branch is formally realized as a correspondence

Whenever the root central return \(F\) has an actual quadratic-like restriction with

\[
A\Subset B\Subset P,
\]

every finite direct-decoration cylinder carries an actual degree-two covering/embedded pair

\[
(f^{N_w+r},f^{N_w}):U_w\rightrightarrows B.
\tag{7.7}
\]

This pair has the correct relative critical word, exact shift equivariance, and exact pulled marking action. It avoids the criticality-swap obstruction because it does not demand that the return \(f^r\) alone map one equal-depth cylinder to another.

The remaining finite-cylinder task is no longer construction of the analytic pair. It is verification that the particular second satellite portrait and every proof-used carrier/access/obstacle record fit into one root restriction \(A\Subset B\Subset P\), and that the resulting family is compatible with the later Wave demand schema and final-root enlargement.

### Corollary 5D - Finite-cylinder second-portrait transfer

Assume the next actual quadratic-like renormalization at the terminal root has connected filled Julia set \(K\Subset\operatorname{int}P\), and freeze any finite protected root marking and obstacle ledger on a sufficiently small restriction. Then every finite direct-decoration word \(w\) carries an actual pseudo-quadratic-like copy

\[
(g_w,\iota_w)=
(f^{N_w+r},f^{N_w}):U_w\rightrightarrows B
\]

with filled Julia set \(K_w=h_w^{-1}(K)\), exact relative critical word, exact pulled prime-end marking, and shift-natural component and sheet data.

Thus the finite-word part of the disconnected second-marking transfer is solved once the actual root portrait is named. The unresolved part is the construction of a noncollapsed analytic component and marked correspondence over each infinite end address, together with complete Wave-horizon authorization.

### Remark - Relation to pseudo-quadratic-like iteration

The construction has exactly the covering/immersion form used for pseudo-quadratic-like maps: one entry is a degree-two proper map and the other is an immersion into the same target. It is also naturally composable by the component-wise fiber-product procedure. No same-depth target-cylinder conjugacy is required for the central branch.

### Corollary 6 - Off-critical part of the scale-two atlas is proved

At the first direct-decoration return atlas, every noncentral root branch is univalent. Therefore every such branch has an actual univalent lift through every finite direct-decoration cylinder for which the source pullback is defined. The target base is not chosen: it is forced to be the image \(V=f^r(U)\), and \(f^N:V\to B\) is automatically univalent.

At any fixed finite cylinder depth and for any finite root branch catalog, the collection of one-step lifted source/target squares is finite and uniquely determined. No target selector or degree audit is needed for these edges. Any further compositional demand closure remains the task of the already proved return-atlas compiler after actual branch composability is specified.

This closes the analytic lift of the noncentral branch part of the disconnected marking-transfer problem, subject only to source authorization of the resulting domains and ledgers. Only a same-iterate central lift can carry a criticality swap; the central finite-word portrait is handled instead by Theorem 5B.

## 8. Exact criticality-swap example

### Proposition 7 - The quadratic stage can move into the target projection

Let

\[
f(z)=z^2-1.
\]

Choose \(0<\rho<1\), set

\[
A=\mathbb D(0,\rho),
\qquad
B=\mathbb D(-1,\rho^2),
\]

and let \(U\) be the component of \(f^{-1}(A)\) containing \(1\). Then:

- \(h_0=f|_U:U\to A\) is conformal;
- \(F=f|_A:A\to B\) is proper of degree two;
- with \(H=f|_U=h_0\), \(V=A\), and \(h_1=f|_A=F\), the square commutes;
- \((\deg H,\deg h_1)=(1,2)\).

Thus a valid univalent source cylinder and a valid quadratic root branch do not force a univalent target cylinder.

#### Proof

The critical value of \(f\) is \(-1\), which is outside \(A\). Hence the two components of \(f^{-1}(A)\) map conformally onto \(A\); take the one containing \(1\). On the centered disk \(A\), the map \(z\mapsto z^2-1\) is the standard degree-two proper map onto \(B\). The commuting relation is associativity of iteration. ∎

## 9. Endpoint degree can be correct while chronology is wrong

### Proposition 8 - Critical-time shear

Again let \(f(z)=z^2-1\). Choose \(\rho>0\) sufficiently small and set

\[
A_0=\mathbb D(0,\rho),
\qquad
A_1=f(A_0)=\mathbb D(-1,\rho^2),
\qquad
A_2=f(A_1).
\]

Let \(U_0\) be the component of \(f^{-1}(A_0)\) containing \(1\). Define

\[
h_0=f|_{U_0}:U_0\to A_0,
\]

\[
F=f^2|_{A_0}:A_0\to A_2,
\]

\[
H=f^2|_{U_0}:U_0\to A_1,
\]

and

\[
h_2=f|_{A_1}:A_1\to A_2.
\]

For small \(\rho\), \(h_0\) and \(h_2\) are conformal, while \(F\) and \(H\) are both proper of degree two. The square

\[
h_2\circ H=F\circ h_0
\tag{9.1}
\]

commutes. Nevertheless,

\[
\operatorname{word}(F)=(2,1),
\qquad
\operatorname{word}(H)=(1,2).
\tag{9.2}
\]

Thus endpoint univalence, total degree two, and an exact commuting conjugacy do not preserve chronological critical metadata.

#### Proof

The branch \(h_0\) is conformal because \(A_0\) avoids the critical value \(-1\). The first factor of \(F\) is \(f:A_0\to A_1\), which contains the critical point and has degree two. The second factor is univalent on the small disk \(A_1\) around \(-1\). Hence \(F\) has word \((2,1)\).

For \(H\), the first factor \(f:U_0\to A_0\) is univalent, while the second factor \(f:A_0\to A_1\) is quadratic. Hence \(H\) has word \((1,2)\). The target map \(h_2=f|_{A_1}\) is univalent. Both compositions in (9.1) equal \(f^3|_{U_0}\). ∎

### Consequence

The finite-cylinder commuting-iterate identity from the manuscript correctly preserves the total proper map, but its warning that critical chronology is separate metadata is essential. Proposition 8 proves that no endpoint-only enhancement can remove that warning.

---

# Part IV. The stagewise cylinder ladder

## 10. Intermediate squares

Let a root branch

\[
F=f^r|_{A_0}:A_0\longrightarrow A_r
\]

be factored by its actual intermediate images

\[
A_j=f^j(A_0),
\qquad 0\le j\le r.
\]

Let

\[
h_0=f^N|_{U_0}:U_0\longrightarrow A_0
\]

be a univalent source cylinder. Put

\[
U_j=f^j(U_0),
\]

and suppose the restrictions

\[
h_j=f^N|_{U_j}:U_j\longrightarrow A_j
\]

are proper and onto for all \(j\). Let

\[
d_j=\deg(f:A_j\to A_{j+1}),
\]

\[
\widetilde d_j=\deg(f:U_j\to U_{j+1}),
\]

and

\[
e_j=\deg h_j.
\]

Every time step gives a commuting square

\[
\begin{CD}
U_j @>f>> U_{j+1}\\
@Vh_jVV @VVh_{j+1}V\\
A_j @>f>> A_{j+1}.
\end{CD}
\tag{10.1}
\]

## 11. Exact ladder criterion

### Theorem 9 - Stagewise degree-ladder recurrence

For every \(0\le j<r\),

\[
\widetilde d_j e_{j+1}=e_j d_j.
\tag{11.1}
\]

Since \(e_0=1\), the following are equivalent:

1. every transverse projection \(h_j\) is univalent;
2. \(d_j=\widetilde d_j\) for every \(j\);
3. the lifted branch has exactly the same chronological degree word as the root branch and no intermediate criticality is stored in a cylinder projection.

If only the endpoint projection \(h_r\) is univalent, then the root and lifted branches have the same total degree, but their chronological words may differ by one or more criticality swaps.

#### Proof

Apply Theorem 4 to each one-step square (10.1), obtaining (11.1). If all \(e_j=1\), then \(d_j=\widetilde d_j\) for every \(j\). Conversely, if all one-step degrees agree, (11.1) and \(e_0=1\) give \(e_j=1\) inductively.

Equality of one-step degrees is precisely equality of chronological degree words. If \(e_r=1\), multiplying (11.1) over \(j\) gives equality of total branch degrees, but the intermediate \(e_j\) may be nontrivial, as Proposition 8 demonstrates. ∎

### Corollary 10 - Geometric critical-spine test

For a quadratic polynomial, exact chronology transfer is equivalent to every selected intermediate domain \(U_j\) avoiding the critical set of \(f^N\):

\[
\operatorname{Crit}(f^N)\cap U_j=\varnothing,
\qquad 0\le j\le r.
\tag{11.2}
\]

Equivalently,

\[
0\notin f^k(U_j)
\quad
(0\le k<N,
\ 0\le j\le r).
\tag{11.3}
\]

The test is finite for every finite branch and finite cylinder depth. A failure certificate is the least pair \((j,k)\) such that

\[
0\in f^k(U_j),
\qquad 0\le k<N.
\]

At that point the transverse cylinder projection is branched, and the declared branch chronology is no longer transported by a stagewise univalent ladder.

### Correction to a tempting shortcut

It is not enough to prove only

\[
\deg(f^r|_{U_0})=
\deg(f^r|_{A_0})
\]

or only that \(h_r\) is univalent. Those statements check the product of the words, not their order. The correct object is the full ladder \((e_0,e_1,\ldots,e_r)\).

---

# Part V. Quadratic base change

## 12. Pulling a quadratic disk map over a smaller base

### Theorem 11 - Quadratic base-change dichotomy

Let

\[
p:X\longrightarrow Y
\]

be a proper holomorphic map of degree two between Jordan disks, with unique critical point \(c\) and critical value

\[
v=p(c).
\]

Let \(E\Subset Y\) be a Jordan disk whose boundary avoids \(v\). Then:

1. If \(v\in E\), the full preimage \(p^{-1}(E)\) is connected, is a Jordan disk, contains \(c\), and
   \[
   p:p^{-1}(E)\to E
   \]
   is proper of degree two.
2. If \(v\notin\overline E\), the preimage \(p^{-1}(E)\) has exactly two components, each a Jordan disk mapped conformally onto \(E\).

#### Proof

If \(v\in E\), the component \(C\) of \(p^{-1}(E)\) containing \(c\) maps properly onto \(E\). Its degree is at least two because the local degree at \(c\) is two. The total degree of \(p\) is two, so this component has degree exactly two and no other preimage component exists.

If \(v\notin\overline E\), the map is unbranched over \(E\). Every component of the preimage is an unbranched finite covering of the simply connected disk \(E\), hence has degree one. The total degree is two, so there are exactly two components. Boundary avoidance and the proper circle-covering extension make the components Jordan disks. ∎

### Corollary 12 - Exact base-change preservation criterion

Let \(\iota:Z\hookrightarrow Y\) be a conformal embedding of a Jordan disk. The normalized fiber product of \(p\) with \(\iota\) has a connected degree-two component over \(Z\) exactly when

\[
v\in\iota(Z).
\tag{12.1}
\]

If the embedded base omits \(v\), every connected component of the fiber product has degree one over \(Z\).

### Proposition 13 - Degree-two factorization alone does not imply telescope closure

Take

\[
p(z)=z^2:\mathbb D\to\mathbb D
\]

and let \(E\Subset\mathbb D\) be a small Jordan disk avoiding \(0\). Then \(p^{-1}(E)\) consists of two conformal components. Therefore no selected connected base-change component preserves degree two.

Consequently, a mapping-telescope theorem cannot follow from degree-two factorization alone. It must include critical-value retention, or an equivalent monodromy/full-degree condition, at every post-quadratic base change.

---

# Part VI. The critical-spine telescope compiler

## 13. Covering/embedded stage systems

A finite **covering/embedded stage system** consists of Jordan disks \(X_j,Y_j\), for \(0\le j<m\), and maps

\[
(g_j,\iota_j),
\]

where

\[
g_j:X_j\longrightarrow Y_{j+1}
\]

is proper holomorphic and

\[
\iota_j:X_j\hookrightarrow Y_j
\]

is a conformal embedding extending to the prime-end compactifications. On the embedded source

\[
A_j=\iota_j(X_j)\subset Y_j
\]

define the relative stage map

\[
R_j=g_j\circ\iota_j^{-1}:A_j\longrightarrow Y_{j+1}.
\tag{13.0}
\]

We set

\[
Y_m=Y_0
\]

for a closed stage cycle. When an actual polynomial realization is claimed, the additional hypothesis is that each \(R_j\) is an actual restriction \(f^{s_j}\) and that the selected fiber-product route lies in the natural domain of their chronological composition.

The chain fiber product is built recursively. Put

\[
T_1=X_0,
\qquad
G_1=g_0:T_1\to Y_1,
\qquad
I_1=\iota_0:T_1\to Y_0.
\]

Given \(T_k,G_k,I_k\), form

\[
\widetilde T_{k+1}
=
\{(t,x)\in T_k\times X_k:
G_k(t)=\iota_k(x)\}.
\tag{13.1}
\]

Because \(\iota_k\) is injective, projection to \(T_k\) identifies each component of \(\widetilde T_{k+1}\) with a component of

\[
G_k^{-1}(\iota_k(X_k)).
\]

On a selected component \(T_{k+1}\), let

\[
p_k:T_{k+1}\to T_k,
\qquad
q_k:T_{k+1}\to X_k
\]

be the coordinate projections and define

\[
G_{k+1}=g_k\circ q_k,
\qquad
I_{k+1}=I_k\circ p_k.
\tag{13.2}
\]

The endpoint pair

\[
(G_m,I_m):T_m\rightrightarrows Y_0
\]

is the telescope return.

## 14. Critical-value propagation

Suppose a partial telescope covering

\[
G_k:T_k\to Y_k
\]

has degree two and critical value \(v_k\). If

\[
v_k\in\iota_k(X_k),
\tag{14.1}
\]

then Theorem 11 gives a unique connected degree-two pullback component in (13.1). If \(g_k\) is univalent, the critical value after composition is

\[
v_{k+1}=g_k(\iota_k^{-1}(v_k)).
\tag{14.2}
\]

Condition (14.1) is called **critical-spine retention**.

## 15. Telescope theorem

### Theorem 14 - Critical-spine quadratic telescope

Assume a covering/embedded stage system satisfies:

1. every \(g_j\) has degree one except one stage \(j=j_*\), where \(g_{j_*}\) has degree two;
2. every embedded boundary \(\partial\iota_j(X_j)\) avoids the critical value of the current partial covering;
3. after the unique quadratic stage has occurred, every subsequent embedded stage satisfies critical-spine retention (14.1);
4. all domains are compactly contained in the authorized localizations.

Then the recursive fiber product has a unique connected full-degree component at every stage. Its endpoint pair satisfies:

- \(T_m\) is a Jordan disk;
- \(I_m:T_m\to Y_0\) is a conformal embedding;
- \(G_m:T_m\to Y_0\) is proper of degree two;
- there is exactly one quadratic factor in the chronological stage word;
- the routing closes at \(Y_m=Y_0\).

If critical-spine retention first fails at stage \(k\), the full-degree pullback splits into two univalent components there, and no connected continuation through that base change retains degree two.

#### Proof

Before the quadratic stage, every partial covering \(G_k\) is univalent. The preimage of the embedded connected disk \(\iota_k(X_k)\) is therefore one connected disk, and the next partial covering remains univalent until composition with \(g_{j_*}\).

At the quadratic stage, a univalent base-change projection is followed by the unique degree-two map \(g_{j_*}\), so the next partial covering has degree two and one critical value.

Inductively, suppose \(G_k\) has degree two. Critical-spine retention places its critical value in the next embedded disk. By Theorem 11, the complete pullback over that disk is connected and degree two. Since the next stage map is univalent, composition remains degree two and its critical value propagates by (14.2). This proves existence, uniqueness, and degree preservation through the rest of the chain.

The Jordan property follows inductively from proper pullback of Jordan disks with boundary avoiding critical values. The projection to the first factor is biholomorphic onto the recursively selected preimage domain because every \(\iota_j\) is injective; therefore \(I_m\) remains a conformal embedding. The final target is \(Y_m=Y_0\), so routing closes.

If retention fails, Theorem 11 gives two degree-one pullback components. Every selected connected continuation therefore has lost the quadratic degree. ∎

### Corollary 15 - Exact failure certificate

A failed proposed telescope must record the first stage \(k\) with:

- the current degree-two partial covering \(G_k\);
- its critical value \(v_k\);
- the embedded next base \(\iota_k(X_k)\);
- the separation
  \[
  v_k\notin\iota_k(X_k);
  \]
- the two resulting degree-one pullback components;
- the component chosen by the proposed routing.

This is stronger than a generic “fiber-product component missing” report: it identifies the exact degree-loss mechanism.

## 16. Relative-cover version

When \(\iota_j\) is only an immersion in the base surface, suppose the manuscript's relative-cover subgroup criterion supplies a selected connected cover on which \(\iota_j\) lifts to an embedding. Apply Theorem 14 in those covers.

The full-degree condition then has two independent parts:

1. the subgroup image selects the required connected cover component;
2. the lifted embedded disk contains the propagated critical value.

Failure of either part is explicit. The first is a subgroup/monodromy failure; the second is a critical-spine failure.

---

# Part VII. Marked finite-horizon assembly

## 17. Marked stage hypotheses

Assume the stages in Theorem 14 additionally carry:

- actual polynomial iterate lengths \(s_j\);
- selected component, parent, sheet, obstacle, and localization records;
- exact one-step and stagewise critical words;
- finite protected endpoint sets and normalized prime-end phases;
- covering/immersion endpoint containment;
- proper or end-proper flags for every proof-used interval;
- relative-cover subgroup inclusions;
- commuting analytic and prime-end squares under every certified enlargement.

These are inputs. The theorem below does not construct them.

## 18. Assembly theorem

### Theorem 16 - Marked finite-horizon telescope assembly

Under the marked stage hypotheses and the critical-spine conditions of Theorem 14, the endpoint telescope pair

\[
(G_m,I_m):T_m\rightrightarrows Y_0
\]

has the following properties:

1. **Actual relative iterate.** Under the explicit iterate-realization hypothesis after (13.0), the endpoint relative map on the embedded endpoint source is
   \[
   G_m\circ I_m^{-1}
   =R_{m-1}\circ\cdots\circ R_0
   =f^{S},
   \qquad
   S=\sum_{j=0}^{m-1}s_j.
   \tag{18.1}
   \]
   No claim that the covering projection \(G_m\) alone equals \(f^S\) is made without this identification.
2. **Degree two.** \(G_m\) is proper of degree two, while \(I_m\) is an immersion and is embedded in the selected relative cover.
3. **Exact chronology.** The complete endpoint critical word is the chronological concatenation of the retained stage words. It has one declared quadratic stage.
4. **Component and sheet routing.** Every intermediate component, parent relation, and sheet label is retained by the tuple projections; no intermediate record is inferred from the endpoint alone.
5. **Prime-end action.** The endpoint prime-end map is the composition of the stage boundary maps. Endpoint containment, marking refinement, normalized phase, and cyclic order therefore hold at the endpoint.
6. **Relative covers.** The stage subgroup inclusions compose, so the endpoint immersion lifts to the selected endpoint cover.
7. **Proper intervals.** A proof-used interval that is proper or end-proper at every stage remains proper or end-proper under the finite composition.
8. **Enlargement naturality.** If every stage participates in a certified injective commuting enlargement square preserving critical-spine retention, then the endpoint telescope square commutes and preserves all marked data.

#### Proof

The fiber-product identity gives, inductively,

\[
G_k=R_{k-1}\circ\cdots\circ R_0\circ I_k.
\]

Under the iterate-realization hypothesis, this proves (18.1); exponents add and the relative stage words concatenate in temporal order. This formulation is essential for a pseudo-quadratic-like telescope, where the covering and immersion projections are separate maps.

Degree two and the endpoint immersion are Theorem 14. Component, parent, and sheet records are coordinate records of the fiber product and therefore persist without endpoint reconstruction.

Proper maps of Jordan disks extend as finite-degree prime-end circle coverings, and conformal embeddings extend as orientation-preserving circle homeomorphisms. The endpoint boundary map is their composition. Exact endpoint containment and cyclic order are therefore compositional. Fundamental-group subgroup inclusions are transitive, giving the relative-cover conclusion. Properness and end-properness are stable under finite composition when every intermediate endpoint is retained.

Finally, compose the stagewise enlargement squares. Critical-spine retention prevents a degree-two component from splitting during enlargement, so the same selected component persists. ∎

### Status consequence

This proves the mathematical content of `FINITE_HORIZON_ASSEMBLY` as a compiler theorem: compatible proper, core-proper, covering-embedded stage correspondences assemble into a closed degree-two marked return while retaining their finite-horizon data.

The word **core-proper** must include the concrete condition used above: after the quadratic stage, the embedded next core contains the propagated critical value. If that is not part of the definition, it must be added; otherwise Proposition 13 refutes degree preservation.

### Corrected mapping-telescope node

The current `MAPPING_TELESCOPE` obligation should be replaced by:

> **Critical-spine mapping telescope.** A finite cyclic covering/embedded stage system with exactly one quadratic stage, boundary critical-value avoidance, relative-cover component compatibility, and post-quadratic critical-spine retention has a unique connected selected fiber-product component whose routing closes and whose endpoint covering has degree two. Failure is exactly a subgroup-orbit defect or the first embedded base omitting the propagated critical value.

With this exact statement, `MAPPING_TELESCOPE` is proved by Theorem 14. Without the added hypotheses, the old node is false by Proposition 13.

---

# Part VIII. End impressions, Euclidean collapse, and normalized germs

## 19. Canonical external prime ends

The direct-decoration pieces are ray/equipotential puzzle pieces. On the exterior Böttcher coordinate, \(f^q\) acts on angles by multiplication by \(2^q\), and every inverse branch \(\phi_a\) acts by one affine inverse branch

\[
t\longmapsto \frac{t+k_a}{2^q}.
\tag{19.1}
\]

For a finite word \(w\), let \(I_w\) be the angular hull of the exterior boundary rays of \(Q_w\), in a compatible lift of the circle. Its diameter satisfies

\[
\operatorname{diam}I_w
=2^{-q|w|}\operatorname{diam}I_\varnothing.
\tag{19.2}
\]

The outer equipotential height is pulled back by the same iterate and therefore tends to the Julia level as \(|w|\to\infty\).

### Theorem 17 - End fibers are canonical prime-end impressions

For every infinite address \(\omega\), the nested angular hulls have one point

\[
\{\theta_\omega\}=\bigcap_{m\ge1}I_{\omega|m}.
\tag{19.3}
\]

The direct-decoration end fiber is the impression of the external prime end of angle \(\theta_\omega\):

\[
E_\omega=\operatorname{Imp}(\theta_\omega).
\tag{19.4}
\]

Moreover,

\[
2^q\theta_{a\omega}=\theta_\omega\pmod 1,
\qquad
f^q(E_{a\omega})=E_\omega,
\tag{19.5}
\]

and the external prime-end crosscut chains give a canonical dynamically equivariant protected access to every end fiber.

#### Proof

Equation (19.1) gives (19.2), so the angular hulls shrink to one angle. Pullback of the exterior equipotential makes the radial height tend to one. Hence the exterior portions of the nested puzzle pieces form a fundamental chain of crosscut neighborhoods for the prime end \(\theta_\omega\). The intersection of their closures with the Julia boundary is, by definition, its impression. The direct-decoration theorem already puts \(E_\omega\) in the Julia set, so this intersection is exactly \(E_\omega\). Angle multiplication and the actual branch identity give (19.5). ∎

This does not identify \(E_\omega\) as a small Julia set. It does, however, replace the undefined end-access field by an actual canonical prime end with exact dynamics.

## 20. Euclidean collapse

### Theorem 18 - Planar end-collapse theorem

Fix an infinite address \(\omega\) and write

\[
\Phi_m=\phi_{\omega|m}:\operatorname{int}P\longrightarrow\operatorname{int}Q_{\omega|m}.
\]

For every compact set \(L\Subset\operatorname{int}P\),

\[
\operatorname{diam}\Phi_m(L)\longrightarrow0.
\tag{20.1}
\]

Every locally uniform subsequential limit of \(\Phi_m\) is a constant map with value in \(E_\omega\). In particular, no nonconstant analytic end chart can be obtained as an unrescaled planar limit of the finite inverse branches.

#### Proof

The maps \(\Phi_m\) form a normal family because their images lie in the bounded puzzle piece \(P\). Let a subsequence converge locally uniformly to \(\Phi\). For every fixed \(n\), all sufficiently deep images lie in the closed nested piece \(Q_{\omega|n}\); therefore

\[
\Phi(\operatorname{int}P)\subset\bigcap_nQ_{\omega|n}=E_\omega.
\]

The set \(E_\omega\) lies in the Julia set and has empty interior. The open mapping theorem forces \(\Phi\) to be constant. If (20.1) failed, a subsequence with diameter bounded below would have a locally uniform subsubsequence with constant limit, contradicting uniform convergence on \(L\). ∎

### Corollary 19 - Finite Julia copies collapse toward the end

For every compact \(K\Subset\operatorname{int}P\), in particular for the terminal or next-renormalization filled Julia set,

\[
\operatorname{diam}\phi_{\omega|m}(K)\longrightarrow0.
\tag{20.2}
\]

Thus a nondegenerate end component cannot be declared to be the ordinary Hausdorff limit of the finite small-Julia copies. The nontrivial end continuum lives in prime-end boundary geometry.

## 21. Normalized analytic germ

### Theorem 20 - Normalized end-germ constancy

Let \(F=f^r|_A:A\to B\) be the localized root portrait and let \((g_m,\iota_m)\) be its retimed pair on the prefix \(w_m=\omega|m\). In the source coordinate

\[
h_m=\iota_m=f^{N_m}:U_m\longrightarrow A,
\]

one has the exact identity

\[
(g_m,\iota_m)\circ h_m^{-1}
=(F,\operatorname{incl}_{A\hookrightarrow B})
\tag{21.1}
\]

for every \(m\). Hence the normalized pseudo-quadratic-like analytic germ is constant along every end address and has a unique nondegenerate analytic limit.

The Euclidean chart collapses by Theorem 18, while the normalized internal germ does not degenerate. Therefore the remaining end theorem is precisely a **blow-up/attachment theorem** realizing the constant internal germ over the canonical prime-end impression \(E_\omega\); it is not an analytic compactness problem for the internal map.

#### Proof

By construction, \(g_m=F\circ h_m\) and \(\iota_m=h_m\) followed by inclusion. Conjugating the common source by \(h_m\) gives (21.1) identically. ∎

### Theorem 21 - End blow-up necessity

Assume the root filled carrier \(K\) contains at least two points. Let \(w_m=\omega|m\), and suppose a Hausdorff marked end realization contains embeddings

\[
 j_m:K\longrightarrow \mathcal X
\]

for the finite carriers and an injective limiting embedding \(j_\infty:K\to\mathcal X\). Suppose there is a continuous plane projection

\[
 \pi:\mathcal X\longrightarrow \overline P
\]

with

\[
 \pi\circ j_m=\phi_{w_m}|_K
\]

and \(j_m(z)\to j_\infty(z)\) for every \(z\in K\). Then \(\pi\circ j_\infty\) is constant. Consequently, every end realization that retains the nondegenerate normalized carrier must satisfy one of the following:

1. the projection to the original dynamical plane has a nontrivial fiber containing \(j_\infty(K)\); or
2. the realization changes scale by a nontrivial rescaling/blow-up chart and therefore is not an unrescaled planar limit.

In particular, no continuous realization can simultaneously retain \(K\) injectively and remain locally embedded in the original plane at the end.

#### Proof

For \(z,z'\in K\), Theorem 18 gives

\[
 |\phi_{w_m}(z)-\phi_{w_m}(z')|\longrightarrow0.
\]

Passing to the marked limit and using continuity of \(\pi\),

\[
 \pi(j_\infty(z))=\pi(j_\infty(z')).
\]

Thus the entire nondegenerate carrier lies in one projection fiber. If the projection were locally injective there, this would contradict injectivity of \(j_\infty\). ∎

This theorem determines the correct category for the remaining construction: a virtual end carrier must be a prime-end blow-up or rescaled fiber over the original plane, unless an independent source theorem supplies a different actual planar component. Requiring a nondegenerate continuum inside \(E_\omega\) would be unjustified and can be impossible when the impression is a singleton.

### Exact consequence

The end part of disconnected marking transfer now splits into two sharply separated statements:

1. **proved:** the canonical end prime end and its dynamics, plus the constant normalized second-portrait germ;
2. **open:** a source-faithful prime-end blow-up or rescaled marked fiber carrying that germ over the canonical impression, with protected accesses, obstacles, a collapse/projection map to the original plane, and final-root naturality. A genuinely planar component is an allowed stronger outcome only when independently constructed.

---

# Part IX. Fixed-iterate end actions

## 22. Compatible finite-cylinder systems

Let

\[
Q_{\omega|1}\supset Q_{\omega|2}\supset\cdots
\]

be the nested source cylinders of an infinite address \(\omega\), and let

\[
E_\omega=\bigcap_{n\ge1}Q_{\omega|n}.
\]

Suppose a fixed polynomial iterate \(f^r\) is defined on a neighborhood of \(E_\omega\). For every \(n\), assume there is a target word \(v_n\) such that:

1. \(v_{n+1}\) has prefix \(v_n\);
2. \(f^r(Q_{\omega|n}\cap D)\subset Q_{v_n}\), where \(D\) is the branch domain;
3. the finite-cylinder component and marked data are compatible under parent deletion.

The compatible target prefixes determine one infinite address

\[
\nu=\lim_n v_n.
\]

## 23. End-fiber extension theorem

### Theorem 22 - Formal end-fiber action

Under the preceding assumptions,

\[
f^r(E_\omega\cap D)
\subset
E_\nu.
\tag{20.1}
\]

If, in addition, for every \(n\) the finite-cylinder branch maps the relevant nested source continuum onto the relevant target continuum and the inverse branches are parent-compatible, then

\[
f^r(E_\omega\cap D)=E_\nu.
\tag{20.2}
\]

Every finite marked observable that is constant under the parent system, including sheet, phase, cyclic order, and declared critical-spine word, passes to the end action.

#### Proof

For \(z\in E_\omega\cap D\), one has \(z\in Q_{\omega|n}\) for every \(n\). Hence

\[
f^r(z)\in Q_{v_n}
\]

for every \(n\). Parent compatibility makes the target cylinders nested, so

\[
f^r(z)\in\bigcap_n Q_{v_n}=E_\nu.
\]

This proves (20.1). Under the surjective compatible inverse-branch hypothesis, every point in the target intersection has a coherent preimage in every source level. Compactness of the nested source continua gives a point in their intersection, proving (20.2). The marking statement follows because every marked value is already fixed at all sufficiently deep finite levels. ∎

### Consequence

“Analytic realization at every end” is not an independent limiting theorem once the following finite data are available:

- one fixed actual iterate on a neighborhood of the end fiber;
- compatible finite target components;
- parent-compatible marked squares;
- compactness of the nested cylinders.

The unresolved work is constructing those finite critical-spine-compatible components. The passage to the end is formal **only for one fixed iterate**. It does not apply directly to the retimed finite-cylinder pairs, whose covering exponents \(N_w+r\) grow with word length. Their correct limiting object is the normalized germ of Theorem 20, followed by the still-open analytic end blow-up theorem.

---

# Part X. Revised scale-two reduction

## 24. What is now proved at the direct-decoration scale

The root return atlas has one central quadratic branch and all other branches univalent. The off-critical branches lift directly, while the central branch lifts as a retimed covering/immersion pair. Combining those facts with the localized restriction and end results yields:

### Theorem 23 - Finite-word scale-two portrait realization

Fix a finite direct-decoration cylinder depth and a finite root branch catalog. Assume every quadratic root portrait has been localized inside the direct-decoration gap and carries its finite protected root marking. Then every finite word has an actual finite-stage portrait:

- each noncentral root edge lifts as the same univalent polynomial iterate with a forced univalent target projection;
- each central quadratic portrait lifts as the retimed pseudo-quadratic-like pair \((f^{N_w+r},f^{N_w})\);
- every relative critical word, filled carrier, component, sheet, endpoint, phase, protected crosscut, and obstacle datum is the exact conformal pullback of the root datum;
- the family commutes with the direct-decoration shift and every certified root enlargement.

At fixed depth and for a finite root catalog, the generated finite-word atlas is finite. The canonical prime ends, normalized analytic germs, and blow-up necessity at infinite addresses are given by Theorems 17, 20, and 21. Constructing the actual rescaled/prime-end fiber that carries the germ remains open.

#### Proof

Apply the off-critical transfer theorem to every univalent root edge and Theorem 5B to every quadratic root portrait. The shift identities and conformal pullback formulas give all marked data. Finiteness at fixed depth follows because there are finitely many words and root edges. The end assertions are Theorems 17--21. ∎

### Important limitation

The cardinality of this finite atlas can grow rapidly with cylinder depth. The theorem is a realization result, not a uniform compression theorem. It does not discharge the manuscript's bounded-dimension WAD/core obligations.

## 25. The two remaining mechanisms

The finite-cylinder central portrait no longer requires a same-iterate target cylinder: Theorem 5B gives it directly as a retimed covering/immersion pair. Two genuinely analytic mechanisms remain.

### A. End blow-up

For each infinite address, construct a prime-end blow-up or rescaled marked fiber over the canonical impression \(E_\omega\) and attach the constant normalized root germ of Theorem 20 there. The fiber must realize the filled carrier, protected accesses, obstacle ledger, collapse map to the original plane, and actual shift map. Theorems 18 and 21 prove that a nondegenerate realization cannot be an unrescaled locally planar limit.

### B. Multi-stage critical-spine retention

When several virtual correspondences are composed through a Wave or antirenormalization horizon, construct a finite covering/embedded chain that:

- has one actual quadratic relative stage;
- retains the propagated critical value in every later embedded base;
- satisfies the relative-cover component condition;
- closes at the declared target base.

Theorem 14 then assembles the degree-two telescope, and Theorem 16 assembles the marking. The manuscript's multi-base terminal chain is therefore the natural model for the global composition problem, not a prerequisite for the already solved finite-cylinder pullback.

## 26. Exact residual theorem

The broad disconnected marking-transfer problem should be replaced, for its analytic core, by the following source-facing theorem.

### Open Problem - Virtual critical-spine and marked-base realization

For every two-step virtual satellite-copy chain and every demanded direct-decoration cylinder:

1. use the proved retimed pairs to realize every finite-word second portrait and freeze its proof-use marking;
2. construct, for every required infinite address, a prime-end blow-up or rescaled marked fiber over \(E_\omega\), together with a continuous collapse map to the original plane, and attach the constant normalized root germ to that fiber;
3. preserve the canonical external prime end and realize every additional protected access, obstacle, sheet, and localization datum;
4. for every demanded multi-stage composition, prove post-quadratic critical-spine retention;
5. prove the selected relative-cover component has full monodromy orbit;
6. prove compatibility under direct shift, geometric parent, and every authorized final-root enlargement;
7. when a genuinely fixed iterate acts on end fibers, freeze parent-compatible finite targets so the fixed-iterate extension theorem applies.

Finite-word analytic transfer, canonical end prime ends, normalized end germs, blow-up necessity, endpoint telescope assembly, and fixed-iterate inverse-limit passage are proved. Construction of the actual analytic blow-up/rescaled end fiber and the source-facing multi-stage critical spine remain open.

## 27. Finite critical-spine audit

For one proposed finite-cylinder lift, record:

\[
\mathcal L=
\bigl(
(d_j,\widetilde d_j,e_j,U_j,A_j)
\bigr)_{0\le j<r},
\]

with \(e_0=1\) and recurrence

\[
\widetilde d_j e_{j+1}=e_jd_j.
\]

The lift passes the exact chronology audit if and only if

\[
e_j=1
\quad\text{for every }j.
\]

If it fails, report the least \(j\) with \(e_{j+1}>1\), together with:

- the root stage degree \(d_j\);
- the lifted stage degree \(\widetilde d_j\);
- the critical point or critical-value preimage entering the transverse projection;
- the source and target puzzle components;
- the first later stage, if any, at which \(e_j\) returns to one.

The last item detects a hidden chronology shift of the type in Proposition 8.

---

# Part XI. Ledger and dependency revision

## 28. New proved obligations

### `CRITICAL_CUT_CONSERVATION` - proved

For commuting iterates, local degrees satisfy (5.1), and for a quadratic polynomial the two branch/cylinder factorizations are different cuts of the same complete critical word.

Dependencies: none.

### `PROPER_SQUARE_DEGREE_CONSERVATION` - proved

Every proper commuting square satisfies (6.2) and (6.3). With a univalent source projection, a quadratic root degree is located either in the lifted branch or in the target projection.

Dependencies: none.

### `OFF_CRITICAL_CYLINDER_TRANSFER` - proved

Every univalent root branch lifts through a univalent polynomial cylinder to an actual univalent branch with a forced univalent target projection, exact prime-end square, and functorial marking transfer.

Dependencies: direct-decoration univalent cylinder maps.

### `CRITICALITY_SWAP_NO_GO` - proved

A valid commuting lift can move the root quadratic degree into the target projection. Moreover, endpoint univalence and equal total degree do not prevent a shift of the chronological word.

Dependencies: none.

### `STAGEWISE_CRITICAL_WORD_LADDER` - proved

The recurrence (11.1) holds at every intermediate time. Exact chronology is equivalent to univalence of every transverse cylinder projection, not merely the endpoint projection.

Dependencies: `PROPER_SQUARE_DEGREE_CONSERVATION`.

### `QUADRATIC_BASE_CHANGE_DICHOTOMY` - proved

A degree-two proper Jordan-disk map pulled over an embedded Jordan subdisk retains one connected degree-two component exactly when the embedded disk contains the critical value; otherwise it splits into two degree-one components.

Dependencies: none.

### `CRITICAL_SPINE_TELESCOPE_COMPILER` - proved

A finite covering/embedded cycle with one quadratic stage, relative-cover component compatibility, boundary avoidance, and post-quadratic critical-value retention has a unique connected degree-two endpoint telescope.

Dependencies: `QUADRATIC_BASE_CHANGE_DICHOTOMY`, `DEGREE_TWO_FACTORIZATION`.

### `MARKED_FINITE_HORIZON_ASSEMBLY` - proved

Actual marked stages satisfying the telescope hypotheses assemble into one degree-two endpoint pair with exact iterate, critical word, component routing, relative-cover action, prime-end marking, and enlargement naturality.

Dependencies: `CRITICAL_SPINE_TELESCOPE_COMPILER`, `PRIME_END_MARKING_ACTION_CRITERION`, `RELATIVE_COVER_LIFT`, `MARKED_PAIR_ENLARGEMENT_NATURALITY`.

### `END_FIBER_ACTION_EXTENSION` - proved

Parent-compatible finite-cylinder actions of one fixed iterate extend by nested intersection to the corresponding end fibers; surjective compatible inverse branches give equality.

Dependencies: `DIRECT_DECORATION_PULLBACK_COMPACTIFICATION`.

### `LOCALIZED_QL_RESTRICTION` - proved

A connected quadratic-like map can be restricted inside any prescribed Jordan neighborhood of its filled Julia set, preserving degree, filled Julia set, iterate, and critical word.

Dependencies: standard polynomial-like external coordinate.

### `FINITE_CYLINDER_SECOND_PORTRAIT_TRANSFER` - proved

A localized root quadratic-like portrait pulls through every finite univalent direct-decoration cylinder as the exact pseudo-quadratic-like pair \((f^{N_w+r},f^{N_w})\), with pulled carrier and complete finite root marking.

Dependencies: `RETIMED_FINITE_CYLINDER_CORRESPONDENCE`, `LOCALIZED_QL_RESTRICTION`.

### `DIRECT_DECORATION_END_PRIME_END_CODING` - proved

Every infinite direct-decoration address determines a unique external angle; its end fiber is the corresponding prime-end impression, and the angle and impression dynamics commute with the pre-root shift.

Dependencies: source ray/equipotential puzzle coding, `DIRECT_DECORATION_PULLBACK_COMPACTIFICATION`.

### `PLANAR_END_COLLAPSE_NO_GO` - proved

Along every infinite address, the inverse branches converge only to constants on compact subsets of the root puzzle interior; images of every compact interior root carrier have diameter tending to zero. A nondegenerate analytic end component cannot be obtained as an unrescaled planar limit.

Dependencies: `DIRECT_DECORATION_PULLBACK_COMPACTIFICATION`.

### `NORMALIZED_END_GERM_CONSTANCY` - proved

After the cylinder coordinate is used to normalize the retimed finite-word pairs, every pair is identically the root pseudo-quadratic-like portrait. The internal end germ is nondegenerate and constant; only its geometric attachment to an end impression remains open.

Dependencies: `FINITE_CYLINDER_SECOND_PORTRAIT_TRANSFER`.

### `END_BLOWUP_NECESSITY` - proved

Any Hausdorff end compactification that retains the nondegenerate normalized carrier and has a continuous projection to the original plane must place the limiting carrier in a nontrivial projection fiber. Equivalently, a source-faithful end realization must use a rescaling or prime-end blow-up unless a separate planar component theorem is supplied.

Dependencies: `PLANAR_END_COLLAPSE_NO_GO`, `NORMALIZED_END_GERM_CONSTANCY`.

## 29. Status recommendations

### Conservative promotion

`FINITE_HORIZON_ASSEMBLY`: **open to proved**.

Replacement statement:

> Every finite family of compatible proper, core-proper, covering-embedded marked stages with one quadratic stage assembles through the critical-spine telescope into a closed selected degree-two endpoint correspondence retaining all stated finite-horizon data.

The analytic realization of those stages remains in `H1_FINITE_HORIZON_INFLATION` and the virtual marked-correspondence nodes.

### Corrected promotion

`MAPPING_TELESCOPE`: replace the current under-specified statement by the critical-spine mapping-telescope statement after Theorem 16 and promote it to **proved**.

Remove `DEGREE_TWO_FACTORIZATION` as its only dependency. Add:

- `QUADRATIC_BASE_CHANGE_DICHOTOMY`;
- relative-cover component compatibility;
- explicit critical-spine retention.

### Residual scale-two node

Keep `VIRTUAL_DISCONNECTED_MARKING_TRANSFER` open, but split it. Record `FINITE_CYLINDER_SECOND_PORTRAIT_TRANSFER`, `DIRECT_DECORATION_END_PRIME_END_CODING`, and `NORMALIZED_END_GERM_CONSTANCY` as proved. Replace the remaining burden by `VIRTUAL_END_BLOWUP_AND_CRITICAL_SPINE_REALIZATION`: construct an analytic prime-end blow-up/rescaled fiber retaining the normalized germ and construct the protected multi-stage critical spine required by the Wave horizon.

## 30. Revised dependency path

Before this push, the scale-two route was represented schematically as

\[
\text{choose targets}
\to
\text{transfer branches}
\to
\text{assemble a telescope}
\to
\text{act on ends}.
\]

After the present theorems, it is

\[
\boxed{
\text{construct one analytic prime-end blow-up/rescaled fiber and one protected multi-stage critical spine}
}
\]

\[
\Downarrow
\]

\[
\text{critical-spine retention and relative-cover orbit}
\]

\[
\Downarrow
\]

\[
\text{telescope assembly is formal}
\]

\[
\Downarrow
\]

\[
\text{all finite-word portraits, canonical end prime ends, normalized germs, and telescope assembly are formal}.
\]

This is a much smaller and more falsifiable source-facing theorem.

---

# Part XII. Mandatory attacks

## 31. Attacks passed

### A. Criticality can move to the target

Passed by Proposition 7. The theorem does not infer target univalence from commutation.

### B. Total degree can hide chronology shift

Passed by Proposition 8 and Theorem 9. The full intermediate projection ladder is retained.

### C. Degree-two factorization can split under base change

Passed by Proposition 13. The telescope theorem explicitly requires critical-value retention.

### D. Univalent branches may target new components

Handled by Theorem 5: the target is the actual image, and the finite atlas is closed under forced images. No claim is made that the original binary target list was already exhaustive.

### E. Immersion monodromy

The relative-cover version separates subgroup-orbit connectedness from critical-value retention. Neither is inferred from labels.

### F. Boundary branching

The telescope requires every embedded boundary to avoid the current critical value and uses proper Jordan-disk restrictions.

### G. Prime-end chronology

Prime-end maps compose only after the stagewise analytic squares are present. Endpoint conjugacy alone is not used to infer the one-step critical word.

### H. Infinite addresses

The fixed-iterate extension theorem requires one fixed iterate on a neighborhood and compatible finite target prefixes. It does not construct those data by compactness alone.

### I. False planar end limit

Passed by Theorem 18. Every unrescaled inverse-branch limit on the puzzle interior is constant, so no end portrait is inferred from a nondegenerate planar normal-family limit.

### J. Hidden normalized degeneration

Passed by Theorem 20. In cylinder coordinates the retimed portrait is exactly constant; the unresolved issue is geometric attachment, not internal analytic compactness.

### K. False planar attachment

Passed by Theorem 21. Any limit retaining the nondegenerate carrier must have a nontrivial projection fiber or use a rescaling; it cannot remain locally embedded in the original plane.

## 32. Attacks still open

- construction of an actual analytic prime-end blow-up/rescaled fiber and its collapse map to the original plane;
- construction of the actual multi-stage critical-spine bases;
- proof that the required protected accesses lie in those bases;
- proof that post-quadratic critical values remain in every embedded stage after final-root enlargement;
- proof of the relative-cover full-orbit condition in the virtual setting;
- identification of the source-defined end object with the intended virtual small-Julia data, or a proof that the blow-up fiber is the correct replacement;
- period-independent control of access and WAD incidence;
- collision-free attachment support on the complete Wave horizon;
- response/Value realization, MBTT, geometric coercivity, and mixed rigidity.

---

# Part XIII. Next source-facing theorem and attack plan

## 33. End-blow-up and critical-spine realization theorem

The next theorem should be stated at the first nontrivial two-scale configuration, not for arbitrary virtual depth.

### Target theorem

For one directly visible decoration followed by one additional satellite-copy step:

1. for every required infinite address \(\omega\), construct a conformal prime-end blow-up or rescaled marked surface \(\widehat\Sigma_\omega\), a nondegenerate carrier \(\widehat K_{2,\omega}\subset\widehat\Sigma_\omega\), and a continuous collapse map to the original dynamical plane whose image lies in the canonical impression \(E_\omega\); realize the constant normalized root germ on this fiber and preserve the canonical external prime end;
2. for every finite proof-demanded source cylinder and every demanded multi-stage continuation, construct a finite sequence of actual Jordan puzzle or generalized polynomial-like bases

\[
U_{w,0},U_{w,1},\ldots,U_{w,m}
\]

and actual iterate restrictions with the following properties:

   The chain must have one quadratic relative stage and all others univalent; its word must equal the prescribed root word; every post-quadratic embedded base must contain the propagated critical value; every protected access, obstacle, sheet, and localization record must be actual; the selected relative-cover orbit must be full; and the construction must commute with source shift, geometric parent, and authorized root enlargement.

Theorems 14 and 16 then produce the degree-two marked multi-stage correspondence. Theorems 17--21 supply the canonical end prime end, the collapse obstruction, the internal normalized germ, and the necessity of a nontrivial fiber/rescaling; Item 1 is the remaining bridge that turns those data into an actual virtual end object.

## 34. Concrete geometric strategy

The most plausible route uses the manuscript's already proved multi-base terminal chain rather than a single critical base.

1. **Localize the root portrait** inside the direct-decoration gap by Lemma 5A.
2. **Transfer every finite word** by the retimed pair of Theorem 5B; do not search for an equal-depth target cylinder for the quadratic branch.
3. **Use the canonical end prime end** \(\theta_\omega\) and retain the normalized root germ \(F,K\) as separate marked data.
4. **Construct the missing end blow-up** by a prime-end plumbing/localization or source-defined rescaling theorem; reject any argument that retains a nondegenerate germ in an unrescaled locally planar limit, by Theorems 18 and 21.
5. **For a multi-stage Wave chain**, pull each relative stage separately and use critical-value retention, rather than endpoint degree, to keep the telescope connected and degree two.
6. **Freeze protected accesses only after the stage bases and end attachments are actual**. Then use the gap-cell carrier results from Research Push I to route the finite package.
7. **Use fixed-iterate end extension only where its hypotheses hold**; growing retimed exponents are represented by the normalized germ instead.

This procedure is finite and falsifiable. Its first possible failure is no longer “the virtual object is not constructed”; it is one of:

- no actual puzzle component realizes the required retimed stage;
- the propagated critical value leaves the next embedded base;
- the relative-cover subgroup orbit splits;
- a protected access collides with the critical spine;
- a final-root enlargement changes the stage component.

## 35. Why this moves the MLC program

The scale-two gap previously mixed four logically different tasks:

- transfer of univalent branches;
- preservation of the quadratic degree;
- preservation of critical chronology;
- assembly and passage to end fibers.

This note separates and resolves the finite-word and formal parts:

\[
\boxed{\text{all finite-word second-portrait transfer}}
\]

\[
\boxed{\text{canonical end prime ends and constant normalized germs}}
\]

\[
\boxed{\text{formal degree-two telescope assembly}}
\]

\[
\boxed{\text{fixed-iterate end-fiber extension}}
\]

The remaining analytic theorem is no longer “transfer the portrait.” It is to realize the already determined normalized germ on a prime-end blow-up/rescaled end fiber and then preserve one protected critical spine through the complete multi-stage horizon.

---

# Conclusion

The main lesson is that the second-scale problem is not primarily a target-address problem. It is a **critical-time placement problem**.

Commuting iterates preserve the complete orbit word but move the cut between “return dynamics” and “cylinder projection.” As a result, the unique quadratic stage can migrate across the square, or can leave and later re-enter the branch while total degree remains unchanged. Exact chronology is equivalent to a stagewise univalent transverse ladder.

The finite-word portrait is now explicit: the quadratic branch uses the pair \((f^{N_w+r},f^{N_w})\), while univalent branches lift directly. At infinite addresses, the external prime end and the internal normalized germ are also explicit, but the plane chart collapses and any nondegenerate limit must live in a nontrivial blow-up/rescaling fiber. Once an actual analytic end blow-up and a protected multi-stage critical spine are supplied:

- the mapping telescope is canonical;
- the endpoint relative return has degree two;
- all finite-horizon marked data compose;
- every finite-word portrait is already realized;
- fixed-iterate compatible actions extend to end fibers.

The next serious construction is therefore precise:

\[
\boxed{
\text{attach the normalized portrait to actual end components and preserve one protected critical spine}
}.
\]

That is the narrowest current source-facing theorem capable of unlocking the virtual marked correspondence and the later finite Wave-horizon compiler.

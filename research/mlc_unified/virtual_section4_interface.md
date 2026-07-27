# Virtual Section-4 interface

## 1. Status and exact verdict

This note isolates the weakest **source-faithful structural interface** currently
known to reproduce the static trichotomy in Kahn--Kapiamba--Lyubich (KKL),
Proposition 3.7 and Remark 4.14.

There are three distinct statements, and they must not be conflated.

1. **Literal KKL transfer (`IMPORTED`).** If a proposed virtual object has already
   been promoted to a periodically repelling, prime primitively renormalizable
   \(\psi\)-quadratic-like map in the full KKL category, with its complete small-Julia
   cycle, Hubbard tree, canonical WAD, canonical renormalization, and at most \(B\)
   cycle components in each limb, then KKL Proposition 3.7 and Remark 4.14 apply at
   sufficiently large renormalization width.
2. **Abstract static interface (`PROVED HERE`).** A pair of marked virtual
   complements satisfying the explicit axioms in Section 5 obeys the same
   amplification/tame/wave trichotomy. This is a new proof obtained by rerunning only
   KKL Section 4. It is not a citation of KKL Proposition 3.7 outside its category.
3. **Realization for every virtual-Molecule block (`OPEN`).** The present repository
   does not construct the marked complements, access-complete carrier, cycle-width
   comparison, restriction system, or amplification comparison required by the
   abstract interface. Consequently the ledger node
   `H2_VIRTUAL_SECTION4_INTERFACE` remains open.

In particular, this note proves no virtual tame-branch closure, no virtual Wave Lemma,
no Master Transition Lemma, and no MLC.

The word “weakest” below means *proof-minimal at the structural level*: every listed
axiom is used by the KKL Section-4 calculation, while the translation-region,
full-return Value, Wanderers, and long-iterate wave hypotheses from KKL Sections 5 and
6 are omitted. It is not a claim of logical minimality among all imaginable
reformulations.

## 2. Source lock

Primary sources:

- J. Kahn, A. Kapiamba, and M. Lyubich,
  [*MLC for parabolically bounded primitive renormalization*](https://arxiv.org/html/2606.27272),
  arXiv:2606.27272v1, 25 June 2026;
- D. Dudko,
  [*On the MLC Conjecture and the Renormalization Theory in Complex Dynamics*](https://arxiv.org/html/2512.24171),
  arXiv:2512.24171.

The source archives, not only their abstracts, were checked. The relevant local source
hashes are:

| source file | SHA-256 |
|---|---|
| KKL `waves-with-Misha.tex` | `AD4C774806D9902AA54FA31C56AD6146D8034946F19CC5E9CEC3C51A3F94FDD5` |
| KKL `value1.tex` | `2767F71E57862DA5CF50FF7B96FC08917E24CA8F9BD2D4523C467B2E896AD83A` |
| Dudko `main.tex` | `FD807D65C44852995182D23A4E96BB42717E8E7502F1D7B71636B16AF5D8A454` |

The exact KKL source locations used are:

| item | source location |
|---|---|
| \(\psi\)-ql category and width | `waves-with-Misha.tex`, lines 431--461 |
| canonical renormalization and amplification | lines 476--492 |
| limbs, Hubbard tree, and Hubbard arc diagrams | lines 495--595 |
| parabolically \(B\)-bounded definition | lines 661--667 |
| Proposition 3.7 | lines 722--726 |
| definitions of controllable wave, bounded flux, alignment, and tameness | lines 750--769 |
| flux split | lines 772--795 |
| width/WAD comparison | lines 802--824 |
| restriction-multiplicity lemma | lines 827--836 |
| limb side count | lines 838--867 |
| alignment split | lines 870--905 |
| Remark 4.14 | lines 907--911 |
| ideal markings, waves, canonical WAD | lines 1839--1963 |
| thick--thin theorem | lines 1964--2056 |
| harmonic-sum arithmetic | `value1.tex`, lines 37--52 |

Dudko's source says that virtual Julia sets are proposed connected hulls of Cantor
small Julia sets that retain the critical orbit only through an appropriate number of
first returns (`main.tex`, lines 875--892). It does not define an ideal marking,
construct a Hubbard carrier, state an occupancy theorem, or prove a Section-4
trichotomy for those hulls. Thus Dudko supplies the research target, not a missing
transfer theorem that can be imported.

## 3. What Remark 4.14 does and does not license

### 3.1 Literal source theorem

KKL Proposition 3.7, combined with Remark 4.14, gives:

> For every \(B,M\ge1\), there is \(A_{\mathrm{KKL}}(B,M)<\infty\) such that a
> periodically repelling, prime primitively renormalizable \(\psi\)-ql map already in
> the KKL category, with at most \(B\) small filled Julia components in each limb and
> \(\mathbb W(\mathcal RF)\ge A_{\mathrm{KKL}}(B,M)\), is \(M\)-amplifying,
> \(M\)-tame, or has \(M\)-wide controllable waves.

Only the *special parabolic-boundedness input* in the Section-4 proof is reduced to
per-limb occupancy. Remark 4.14 does not remove the ambient KKL hypotheses or
construct any of the following:

- the full small-Julia cycle \(\mathcal K\);
- the finite Hubbard tree \(\mathcal T\);
- the complete ideal marking of \(\mathcal U\setminus\mathcal T\);
- the canonical WAD on \(\mathcal U\setminus\mathcal K\);
- the canonical renormalization \(\mathcal RF\);
- the comparison of every cycle-component boundary width with
  \(\mathbb W(\mathcal RF)\);
- the restriction of canonical leaves from the small-set complement to the tree
  complement.

Therefore a connected partially invariant virtual hull does not literally satisfy the
premise merely because one can count some selected continua in each putative limb.

### 3.2 Abstract rerun versus literal invocation

There are only two source-honest routes.

1. **Literal route.** Promote the virtual block to an actual KKL \(\psi\)-ql object
   with all the preceding data. Then cite Proposition 3.7 and Remark 4.14.
2. **Static-interface route.** Construct only the marked surfaces and estimates used
   in KKL Section 4, and prove a new abstract trichotomy from them. This is the route
   formalized below.

Calling the second route an “application of Proposition 3.7” would be a category
error. It is a reproduction of its proof under a verified interface.

### 3.3 Two source inconsistencies that must not propagate

The controlling amplification definition in KKL lines 491--492 is
\[
  \mathbb W(F)\ge M\mathbb W(\mathcal RF).
\tag{3.1}
\]
Line 698 reverses that inequality while claiming to recall it. KKL Section 4 itself
uses the direction in (3.1), for example at line 784. This note always uses (3.1).

Also, KKL Lemma 4.6 proves
\[
  p\,\mathbb W(\mathcal RF)
  \le 4\|X\|+O(p),
\tag{3.2}
\]
whereas line 895 prints an \(O(1)\) term when invoking that lemma. The controlling
estimate is (3.2). The Section-4 proof needs only an \(O(p)\) error with a coefficient
independent of \(p\), because division by \(p\) and a large-width threshold absorb it.
No virtual argument may upgrade this to an absolute \(O(1)\) error without a separate
proof.

## 4. Exact dependency extraction from KKL Section 4

The proof has no translation marking and no long dynamical pushforward. Its complete
input ledger is:

| KKL proof step | exact input |
|---|---|
| define tame/wave alternatives | two hyperbolic marked complements, horizontal Hubbard diagram, canonical WAD, and complete tree-side ideal marking |
| high flux \(\Rightarrow\) wave | flux witness within additive \(2\); a horizontal multi-interval of length at most \(2B\); exhaustive restriction into vertical paths or waves over its endpoints |
| compare successor width to WAD | thick--thin on the complete small-set complement; all \(p\) component-boundary widths comparable to the renormalization width |
| many Hubbard intersections \(\Rightarrow\) many restrictions | minimal intersection representative; exact description of bounded complementary regions cut by the horizontal diagram |
| count limb intervals | finite reduced tree spanning the limb anchor and at most \(B\) component vertices |
| nonalignment \(\Rightarrow\) wave | harmonic-sum restriction inequality; complete ideal marking of cardinality at most \(6Bp\); exhaustive endpoint decomposition of a restricted lamination |
| no amplification bounds tree width | monotonic comparison \(\mathbb W(F)\ge\mathbb W(\mathcal U\setminus\mathcal T)\) |
| absorb all additive errors | \(\mathbb W(\mathcal RF)\) exceeds a threshold depending on fixed occupancy and requested factor |

The only dynamical provenance hidden in this static-looking list is the comparison of
all \(p\) cycle-component widths with the successor width. KKL invokes the standard
quadratic-like cycle estimate
\[
  \frac12\mathbb W(\mathcal BJ_0)
  \le \mathbb W(\mathcal BJ_k)
  \le \mathbb W(\mathcal BJ_0).
\tag{4.1}
\]
A virtual proof must either retain the orbit/fiber-product stages needed to establish
(4.1), or assume and prove a replacement affine comparison directly. “Section 4 has
no long wave iterate” does not mean that partial invariance is irrelevant.

## 5. The proof-minimal static interface

This section defines an abstract datum. Existence for arbitrary virtual-Molecule
blocks is not assumed.

### 5.1 Geometric data

Fix \(B,M\ge1\), integers \(p\ge q\ge1\), and a successor width \(D>0\).
A **static virtual Section-4 datum** consists of:

1. a finite union \(\mathcal K^v\) of declared small full continua and a connected
   carrier \(\mathcal T^v\supset\mathcal K^v\) in an ambient conformal disk
   \(\mathcal U^v\);
2. nested hyperbolic finite-type marked surfaces
   \[
     V_{\mathcal T}
     =\mathcal U^v\setminus\mathcal T^v
     \subset
     V_{\mathcal K}
     =\mathcal U^v\setminus\mathcal K^v;
   \tag{5.1}
   \]
3. a finite ideal marking \(\mathcal I^v\) of \(V_{\mathcal T}\), partitioned into
   \(q\) virtual limb multi-intervals \(\mathcal L_j^v\);
4. a horizontal carrier arc diagram \(\mathcal H^{v,\mathrm{hor}}\) on
   \(V_{\mathcal K}\);
5. the horizontal-plus-vertical part \(X\) of a canonical or explicitly
   width-comparable WAD, represented by a lamination \(\mathcal F_X\);
6. an ambient width \(W_0\), a total marked tree-complement width \(W_{\mathcal T}\),
   and a class of **controllable** waves in \(V_{\mathcal T}\).

Assume that the maximal width in the declared controllable-wave class is attained
(as it is for the finite collection of maximal wave families in the KKL use), and
set
\[
  W_*=\max\{\mathbb W(S):S\text{ is a declared controllable wave}\}.
\tag{5.2}
\]
The declared wave class must contain every localized wave and every critical-limb
boundary wave produced by the restrictions below.

The datum is \(M\)-amplifying when
\[
  W_0\ge MD,
\tag{5.3}
\]
and has an \(M\)-wide controllable wave when
\[
  W_*\ge MD.
\tag{5.4}
\]

### 5.2 Interface axioms

All constants and error coefficients below must be independent of \(p,q\), the
rotation number, and the virtual transition depth. Dependence on the stated occupancy
parameter \(B\) is displayed or absorbed into \(E_X(B)\).

#### `S4-AC`: access completeness

Every endpoint class of every leaf produced by restricting either
\(\mathcal F_X\) or a flux witness from \(V_{\mathcal K}\) to
\(V_{\mathcal T}\) occurs in \(\mathcal I^v\). Every restricted leaf is classified as
one of:

- a path counted by \(W_{\mathcal T}\);
- a localized wave;
- a declared critical-limb controllable wave.

No leaf may disappear into an undeclared fjord, dam side, omitted Cantor component,
filled complementary component, or unmarked prime-end access.

#### `S4-AMP`: amplification comparison

\[
  0\le W_{\mathcal T}\le W_0.
\tag{5.5}
\]

This is the only implication used from the ambient width: absence of
\(M\)-amplification gives \(W_{\mathcal T}<MD\).

#### `S4-MARK`: complete marking and horizontal-side bounds

\[
  |\mathcal I^v|\le6Bp,
\tag{5.6}
\]
and for every \(\alpha\in\mathcal H^{v,\mathrm{hor}}\), the corresponding
multi-interval \(I_\alpha\) satisfies
\[
  \ell(I_\alpha)\le2B.
\tag{5.7}
\]

The coefficient \(B\) here bounds access-complete marked atoms, not merely selected
small Julia components. A bounded-fiber conversion from component count to marked
atoms is allowed if it has been proved.

#### `S4-WX`: successor-width/WAD comparison

There is \(E_X(B)<\infty\) such that
\[
  pD\le4\|X\|+E_X(B)p.
\tag{5.8}
\]

It is enough to assume directly that \(\|X\|\ge pD/5\) above a stated threshold.
Equation (5.8) is retained because it is the exact affine form produced by the KKL
cycle-width and thick--thin calculation.

#### `S4-FLUX`: flux witness and exhaustive flux restriction

For every horizontal carrier arc \(\alpha\), there is a lamination
\(\mathcal F_\alpha\) such that every leaf intersects \(\alpha\) and
\[
  \operatorname{flux}(\alpha)
  \le\mathbb W(\mathcal F_\alpha)+2.
\tag{5.9}
\]
Its restriction obeys
\[
  \mathbb W(\mathcal F_\alpha)
  \le2\ell(I_\alpha)W_*+W_{\mathcal T}.
\tag{5.10}
\]

By (5.7), the wave coefficient in (5.10) is at most \(4B\).

#### `S4-INT`: canonical support and intersection filtration

For \(n\ge0\), let \(\mathcal F_n\subset\mathcal F_X\) be the sublamination whose
leaves have geometric intersection at least \(n\) with
\(\mathcal H^{v,\mathrm{hor}}\). For every WAD support set \(\mathcal A\) with
\[
  \min_{\gamma\in\mathcal A}
  \langle\gamma,\mathcal H^{v,\mathrm{hor}}\rangle\ge n,
\]
one has
\[
  \|X|_{\mathcal A}\|\le\mathbb W(\mathcal F_n).
\tag{5.11}
\]

#### `S4-RES`: restriction multiplicity and harmonic aggregation

Let \(\mathcal G\) be the full restriction of \(\mathcal F_X\) to
\(V_{\mathcal T}\). For every \(n\ge0\),
\[
  n^2\mathbb W(\mathcal F_n)\le4\mathbb W(\mathcal G).
\tag{5.12}
\]

Section 6 gives a proof-minimal topological certificate for the multiplicity behind
(5.12). The final width inequality also uses the harmonic-sum law and must be verified
for the actually realized restriction.

#### `S4-END`: endpoint pigeonhole and wave decomposition

For each \(\mathcal I\in\mathcal I^v\), let \(\mathcal G(\mathcal I)\) be the
restricted leaves with a chosen endpoint in \(\mathcal I\). The choices cover
\(\mathcal G\), so
\[
  \mathbb W(\mathcal G)
  \le\sum_{\mathcal I\in\mathcal I^v}
  \mathbb W(\mathcal G(\mathcal I)).
\tag{5.13}
\]
For every \(\mathcal I\),
\[
  \mathbb W(\mathcal G(\mathcal I))
  \le2W_*+W_{\mathcal T}.
\tag{5.14}
\]

Access completeness is what makes (5.13)--(5.14) exhaustive.

### 5.3 Precise tame normalization

The datum has **\(M\)-bounded flux in the Section-4 normalization** if
\[
  \operatorname{flux}(\alpha)
  \le(4B+3)MD
  \quad
  \text{for every }\alpha\in\mathcal H^{v,\mathrm{hor}}.
\tag{5.15}
\]

It is **\(M\)-aligned in the Section-4 normalization** if, for all \(n\) and all
\(\mathcal A\) as in (5.11),
\[
  n^2\|X|_{\mathcal A}\|
  <360BM\|X\|.
\tag{5.16}
\]

It is **\(M\)-tame in the Section-4 normalization** if it has bounded flux, is
aligned, and has no \(M\)-wide controllable wave.

The numbers \(4B+3\) and \(360B\) expose constants hidden by KKL's fixed-\(B\)
\(O(M)\) convention. They are sufficient rather than canonically optimal.

The symbol \(M\) is one **single declared control parameter** for all three
alternatives. It must not be changed after the static split. In a later branch
assembly, first choose the wave-input parameter required for the desired output
amplification, then invoke this static lemma at that same value and feed the same
value into the tame closure. The quantifier-correct composition, including the
maximum of all branch thresholds, is proved in `virtual_branch_assembly.md`.

## 6. Two formal lemmas

### Lemma 6.1 (access-complete limb count; already proved in the repository)

Suppose one virtual limb has a reduced finite tree spanning its anchor and \(m\)
non-anchor access-complete marked atoms, every unmarked vertex has valence at least
three, and every prescribed atom has at most two local ideal decorations. Then its
complete ideal multi-interval has cardinality at most
\[
  6m.
\tag{6.1}
\]

**Justification.** This is Theorem 3.2 of
`virtual_limb_marking_bound.md`. The tree has at most \(2m-1\) edges, hence at most
\(4m-2\) oriented sides, and local decorations add at most \(2(m+1)\). \(\square\)

This proves the finite-tree arithmetic behind `S4-MARK`. It does not construct the
tree or prove that its atoms are access complete.

### Lemma 6.2 (restriction-multiplicity certificate)

Let \(\gamma\) be a path in \(V_{\mathcal K}\) represented with minimal intersection
\[
  n=\langle[\gamma],\mathcal H^{v,\mathrm{hor}}\rangle
\]
with a representative \(H\) of the horizontal carrier. Let \(D_H\) be the union of
the components of
\[
  \mathcal U^v\setminus(\mathcal K^v\cup H)
\]
that do not touch the outer boundary. Cutting \(\gamma\) at its \(n\) intersections
with \(H\) gives consecutive segments
\(\gamma_0,\ldots,\gamma_n\). Assume:

1. every \(\gamma_i\not\subset D_H\) determines a restriction path in
   \(V_{\mathcal T}\);
2. different such segments determine different restriction paths;
3. no two adjacent segments are both contained in \(D_H\).

Then \(\gamma\) has at least
\[
  \left\lfloor\frac{n+1}{2}\right\rfloor\ge\frac n2
\tag{6.2}
\]
distinct restrictions in \(V_{\mathcal T}\).

**Proof.** Among \(n+1\) linearly ordered segments, a subset containing no two
adjacent positions has cardinality at most
\(\lceil(n+1)/2\rceil\). Applying this to the segments contained in \(D_H\), at least
\(\lfloor(n+1)/2\rfloor\) segments lie outside \(D_H\). Items 1 and 2 turn them into
distinct restrictions. \(\square\)

This is the exact abstract content of KKL Lemma 4.7. Minimal intersection proves
Item 3 in the KKL Hubbard-tree geometry. No result in the repository proves Items
1--3 for every virtual carrier. If they are realized leafwise, the KKL harmonic-sum
inequality converts (6.2) into (5.12).

## 7. Abstract static trichotomy

### Theorem 7.1 (Virtual Section-4 static lemma; conditional theorem)

Let a static virtual Section-4 datum satisfy `S4-AC` through `S4-END`. If
\[
  D\ge A_0(B,M)
  :=
  \max\{1,5E_X(B)\},
\tag{7.1}
\]
then at least one of the following holds:

1. \(W_0\ge MD\);
2. the datum is \(M\)-tame in the Section-4 normalization;
3. \(W_*\ge MD\).

**Proof.**
Assume that Alternatives 1 and 3 both fail. Then
\[
  W_{\mathcal T}\le W_0<MD,
  \qquad
  W_*<MD.
\tag{7.2}
\]

First consider flux. If some horizontal \(\alpha\) violated (5.15), then
`S4-FLUX`, (5.7), and (7.2) would give
\[
\begin{aligned}
  (4B+3)MD
  &<\operatorname{flux}(\alpha)\\
  &\le\mathbb W(\mathcal F_\alpha)+2\\
  &\le4BW_*+W_{\mathcal T}+2\\
  &<(4B+1)MD+2\\
  &\le(4B+3)MD,
\end{aligned}
\]
where the last inequality uses \(M,D\ge1\). This is impossible. Hence the datum has
\(M\)-bounded flux.

Next suppose alignment failed. By (5.11), for some \(n\),
\[
  n^2\mathbb W(\mathcal F_n)
  \ge360BM\|X\|.
\tag{7.3}
\]
Equation (5.12) gives
\[
  \mathbb W(\mathcal G)
  \ge90BM\|X\|.
\tag{7.4}
\]
By (5.6) and (5.13), some interval \(\mathcal I\in\mathcal I^v\) satisfies
\[
  \mathbb W(\mathcal G(\mathcal I))
  \ge
  \frac{\mathbb W(\mathcal G)}{6Bp}
  \ge
  \frac{15M\|X\|}{p}.
\tag{7.5}
\]
From (5.8) and \(D\ge5E_X(B)\),
\[
  4\|X\|
  \ge p(D-E_X(B))
  \ge\frac45pD,
\]
so
\[
  \|X\|\ge\frac15pD.
\tag{7.6}
\]
Combining (7.5) and (7.6) yields
\[
  \mathbb W(\mathcal G(\mathcal I))\ge3MD.
\tag{7.7}
\]
But (5.14) and (7.2) give
\[
  \mathbb W(\mathcal G(\mathcal I))
  \le2W_*+W_{\mathcal T}<3MD,
\]
a contradiction. Thus the datum is aligned. Together with bounded flux and the
failure of Alternative 3, it is tame. \(\square\)

### Corollary 7.2 (literal KKL recovery)

For an actual KKL object with at most \(B\) small filled Julia components per limb,
the KKL constructions verify the interface axioms after its fixed-\(B\) constants are
normalized, and Theorem 7.1 reproduces the Section-4 proof of Proposition 3.7.

**Qualification.** This corollary is a consistency check, not a new proof that a
virtual hull is an actual KKL object. The source's threshold is still recorded as
\(A_{\mathrm{KKL}}(B,M)\), since its asymptotic notation can hide additional
fixed-\(B,M\) normalization constants.

### Remark 7.3 (parameter synchronization)

Theorem 7.1 is quantified as
\[
  \forall B,M\ge1\ \exists A_0(B,M)<\infty:
  \quad
  D\ge A_0(B,M)
  \Longrightarrow
  \operatorname{Amp}_M
  \vee\operatorname{Tame}_M
  \vee\operatorname{Wave}_M.
\tag{7.8}
\]
Under the exact numerical interface above, the displayed sufficient formula for
\(A_0\) happens not to grow with \(M\). This does not authorize changing \(M\) between
branches, nor does it improve the source threshold in a literal KKL invocation.
`virtual_branch_assembly.md` gives a countermodel showing that unrelated tame and
wave input parameters do not compose.

## 8. Mapping KKL objects to a virtual block

The following table records the strongest mapping currently justified.

| KKL object or hypothesis | required virtual object | current repository result | status |
|---|---|---|---|
| ambient periodically repelling prime primitive \(\psi\)-ql map | selected analytic correspondence or a direct static marked-pair replacement | stagewise full-hull factorization is proved only after an endpoint hull and itinerary are supplied; arbitrary analytic inflation is open | `OPEN` |
| full cycle \(\mathcal K=\{K_i\}_{i=0}^{p-1}\) | every small continuum used by the width sum and every needed orbit label | an admissible hull datum requires this coverage but does not construct it | `OPEN` |
| Hubbard tree \(\mathcal T\) | access-faithful full ribbon/tree carrier \(\mathcal T^v\) | recursive tree-nerve fullness is proved conditionally; cell-tree extraction is open | `OPEN` |
| tree-side ideal marking \(\mathcal I\) | complete prime-end marking induced by the same carrier used by restriction | prime-end circles exist for proper maps between full-hull complements; finite access realization is open | `OPEN` |
| at most \(B\) components per limb | at most \(B_*\) access-complete marked atoms per limb, or a bounded-fiber assignment to components | the conditional \(6B_*\) tree count is proved in `virtual_limb_marking_bound.md`; the bounded atom load is open | `PARTIAL` |
| horizontal multi-interval length \(\le2B\) | uniformly bounded sides associated to each horizontal carrier arc | no general virtual side-assignment theorem | `OPEN` |
| canonical WAD \(X\) | canonical WAD on the realized small-set complement, with the same support used by restriction | KKL thick--thin is imported for an actual finite-type marked surface; realizing the surface and identifying the relevant support are open | `OPEN` |
| \(pD\le4\|X\|+O(p)\) | `S4-WX` with error coefficient independent of \(p\) and virtual depth | no virtual all-cycle width comparison; conditional corridor calibration concerns a different, richer state | `OPEN` |
| KKL Lemma 4.7 | the certificate in Lemma 6.2 on the realized carrier | the abstract certificate is proved; realization is open | `PARTIAL` |
| flux and endpoint wave decompositions | `S4-AC`, `S4-FLUX`, and `S4-END` on the same marked surface | no theorem excludes lost leaves at omitted accesses or filled virtual regions | `OPEN` |
| \(\mathbb W(F)\ge\mathbb W(\mathcal U\setminus\mathcal T)\) | `S4-AMP` comparing the virtual ambient functional with tree-complement marked width | ordinary annular monotonicity does not compare the required marked families | `OPEN` |
| large \(\mathbb W(\mathcal RF)\) | \(D\ge A_0(B,M)\) after every affine error is quantified | no universal virtual error coefficient \(E_X(B)\) is proved | `OPEN` |

Thus none of the open rows may be discharged by citing Remark 4.14.

## 9. What the repository actually proves

The existing results give useful prerequisites, but not the realization theorem.

### 9.1 Fullness and prime ends

`virtual_hull_realization.md` proves fullness for a recursive union of full branch
continua attached along connected intersections. `virtual_block_quotient.md` proves
that proper maps between complements of nondegenerate full continua act on their
prime-end circles.

These results do not provide:

- a canonical finite tree carrier for Dudko's virtual hull;
- a finite complete ideal marking;
- virtual limbs or their anchors;
- the correspondence between tree sides and canonical WAD endpoints.

A prime-end circle can carry arbitrarily many dynamically distinct intervals.

### 9.2 Selected stagewise degree

`virtual_block_quotient.md` proves that, after a terminal full hull and an inverse
itinerary have been supplied, selected pullback continua admit a stagewise
factorization with exactly one quadratic stage. This removes the elementary
degree-\(2^p\) obstruction at the topological level.

It does not prove:

- that those stages coincide with the desired virtual hulls;
- uniform collars or moduli;
- a fiber-product \(\psi\)-ql correspondence;
- admissibility of every canonical leaf used by Section 4.

### 9.3 Finite-horizon partial invariance

`finite_horizon_inflation.md` proves the exact complement-inclusion criterion
\[
  f(\Upsilon_j)\subset\Upsilon_{j+1}
\tag{9.1}
\]
and the standard relative-cover lifting criterion. `regime_and_hulls.md` proves that
later postcritical points are irrelevant to a *specified* finite pullback chain once
every traversed branch and critical value has been marked.

Neither result constructs the required chain. For Section 4, the finite-horizon
certificate must cover:

1. every stage used to compare the \(p\) component widths in `S4-WX`;
2. every component and access used to construct the carrier;
3. every restriction used in `S4-FLUX`, `S4-RES`, and `S4-END`.

If `S4-WX` is proved independently, no other long iterate is used by Theorem 7.1.
Otherwise the safe horizon is at least the complete selected component cycle, not
merely an unspecified “first return.”

### 9.4 Finite-tree arithmetic

`virtual_limb_marking_bound.md` now proves the finite-tree side count, including a
bounded-fiber conversion from selected components to access-complete atoms.

This closes only the implication
\[
  \text{access-complete reduced carrier with bounded atom load}
  \Longrightarrow
  |\mathcal L_j^v|\le6B_*.
\tag{9.2}
\]
The antecedent is the difficult virtual realization statement.

## 10. Exact unresolved realization obligations

The virtual interface is established only after all of the following are proved.

### `VSI-R1`: canonical two-level carrier

For every routed virtual-Molecule block, construct
\[
  \mathcal K^v\subset\mathcal T^v\Subset\mathcal U^v
\]
so that \(\mathcal K^v\) contains every selected small continuum used by the width
sum, \(\mathcal T^v\) is full and connected, and the two complements in (5.1) are the
actual surfaces used by all later restrictions.

**Current obstruction.** Dudko proposes the connected hull but gives no canonical
finite carrier or analytic complement.

### `VSI-R2`: virtual limb and anchor construction

Construct a cyclic limb decomposition with \(q\le p\), distinguished anchors, and a
reduced tree in each limb. Prove that the decomposition is compatible with the
selected return and with changes of virtual scale.

**Current obstruction.** A prime-end circle and a finite list of selected continua do
not determine KKL's \(\alpha\)-limb structure.

### `VSI-R3`: access-complete bounded atom load

Prove that every proof-used prime end, fjord side, dam endpoint, postcritical access,
and carrier side is represented by a marked atom, with
\[
  m_j\le B_*
\]
or \(m_j\le c_{\mathrm{acc}}B\), uniformly in period, rotation number, and virtual
depth. Then apply `virtual_limb_marking_bound.md`.

**Current obstruction.** Selected-component occupancy alone has no such consequence.

### `VSI-R4`: horizontal-side bound

For every virtual horizontal carrier arc, construct its associated multi-interval and
prove (5.7), or prove (5.10) directly with a uniform coefficient.

**Current obstruction.** The per-limb \(6B_*\) bound does not automatically give the
sharper flux-side coefficient used by KKL.

### `VSI-R5`: all-cycle width/WAD calibration

Prove (5.8) with \(E_X(B)\) independent of \(p\) and virtual depth. A source-faithful
derivation must:

1. compare the boundary width of every selected cycle component with \(D\);
2. apply thick--thin on the actual complete small-set complement;
3. show that Euler and marking errors are \(O_B(p)\), not \(O(p^2)\) or
   \(O(p\,h_{\mathrm{virtual}})\).

**Current obstruction.** Partial invariance has not been verified through the cycle,
and the unified virtual functional has not been compared to this canonical WAD.

### `VSI-R6`: restriction-multiplicity realization

Realize the three hypotheses of Lemma 6.2 for every canonical leaf and verify that the
resulting restrictions satisfy the harmonic aggregation (5.12).

**Current obstruction.** Filling, omitted continua, or collapsed carrier fibers can
merge nominally distinct restrictions or hide them in bounded complementary regions.

### `VSI-R7`: faithful flux and endpoint decomposition

Prove `S4-FLUX` and `S4-END` on the same access-complete marked surface. Every
restricted leaf must be counted as vertical or as one of the declared controllable
waves, with no unmarked residual class.

**Current obstruction.** Fullness alone does not control prime-end incidence or leaf
itineraries.

### `VSI-R8`: amplification and chart comparison

Prove `S4-AMP` and identify \(D\) with the successor coordinate used by the unified
transition state, with a period-independent affine or relative error budget.

**Current obstruction.** Marked arc width, ordinary annular inverse modulus, and the
proposed unified functional are not interchangeable without a chart theorem.

### `VSI-R9`: threshold audit

Collect every additive coefficient into \(E_X(B)\) and the flux error, and verify the
large-width condition before invoking Theorem 7.1. If the coefficient depends on
period or virtual depth, regrouping or a different invariant is required.

**Current obstruction.** No period-independent virtual coefficient has been proved.

Any one unresolved item blocks `H2_VIRTUAL_SECTION4_INTERFACE`.

## 11. Adversarial tests and counterexample schemas

These are obstruction schemas. Unless explicitly stated, they are not claimed to be
realized by a quadratic polynomial; they show that the proposed hypotheses do not
logically imply the needed conclusion.

### 11.1 One component, arbitrarily many accesses

Fix one selected small continuum in a limb and attach \(N\) distinguishable fjord or
dam-access terminals to a connected star carrier. The selected-component count is
one, while the complete tree-side marking has order \(N\). A restricted lamination
can distribute its width among all \(N\) endpoints, so the pigeonhole denominator is
\(N\), not \(O(B)\).

This is Proposition 4.1 of `virtual_limb_marking_bound.md`. It defeats any attempt to
replace `S4-MARK` by selected-component occupancy alone.

### 11.2 Omitted Cantor components

Select at most one visible continuum in each limb but leave infinitely or increasingly
many Cantor small Julia components between the connector and the outer boundary. If
some omitted component separates two proof-used accesses, then either:

- the ideal marking is incomplete; or
- filling merges nominally distinct accesses; or
- a restricted leaf ends at an undeclared boundary component.

All three outcomes violate `S4-AC`. Declaring the omitted components “inactive” is
not a proof that they are irrelevant to separation.

### 11.3 Restriction collapse

Let a path cross a drawn carrier \(n\) times, but arrange for most cut segments to lie
in one filled bounded complementary component, or let a quotient identify their
prime-end endpoints. The raw intersection count is \(n\), while the number of
distinct restrictions in the realized tree complement is \(O(1)\).

This violates Items 1 or 2 of Lemma 6.2. A picture of \(n\) crossings is not a
restriction-multiplicity proof.

### 11.4 Alternating hidden regions

Even if distinct restrictions are retained, two consecutive cut segments may both lie
in undeclared bounded regions when the representative is not minimal relative to the
actual carrier. Then the \(n/2\) lower bound fails. The exact repair is Item 3 of
Lemma 6.2, not a generic claim of “transversality.”

### 11.5 Large-width threshold removed

The affine estimate
\[
  pD\le4\|X\|+E_Xp
\]
allows \(\|X\|\) to be negligible whenever \(D\) is on the scale of \(E_X\). The
alignment proof then cannot convert a large restricted family into a definite
multiple of \(D\). Thus the threshold \(D\gg E_X\) is logically essential to this
mechanism.

If \(E_X=E_X(p)\to\infty\), no period-independent threshold exists.

### 11.6 Superlinear marking error

Suppose the realized virtual marking has \(p^2\) intervals even though there are only
\(O(p)\) selected continua. The thick--thin error is then at least of the allowed
topological order \(O(|\mathcal I^v|)=O(p^2)\). After division by \(p\), the error
coefficient in (5.8) is \(O(p)\), and Theorem 7.1 has no uniform threshold.

This is why bounded incidence per cycle cell is substantive, not bookkeeping.

### 11.7 Partial-return undercoverage

Retain only the endpoint hull and a critical orbit through a first return, but omit an
intermediate cycle component used by (4.1). Its boundary collar can degenerate
independently in the unverified model. Then the sum of all component widths need not
be comparable to \(pD\), so `S4-WX` is unavailable.

The finite-orbit sufficiency lemma does not apply because the omitted stage is used by
the proof.

### 11.8 Global degree substitution

Putting the entire critical-value segment into one full hull makes the global
complement return proper of degree \(2^p\). It does not produce a degree-two KKL
\(\psi\)-ql map. Prime-end compactification preserves this degree.

The static theorem does not itself use return degree, but the global map cannot be
used to justify the cycle-width or later tame/wave hypotheses without selected
factorization.

### 11.9 Prime-end circle without a finite carrier

A full continuum always has a simply connected complement and hence a prime-end
circle, but that circle may have arbitrarily many declared access intervals. Prime-end
existence proves neither `S4-MARK` nor the limb decomposition.

### 11.10 Unbounded occupancy parameter

KKL fixes \(B\); its constants and threshold may depend on \(B\). If the virtual
access-complete atom count \(B_*\) grows along a tower, Theorem 7.1 is only a
blockwise statement with a growing threshold. A universal MLC induction would need:

1. a universal bound on \(B_*\);
2. regrouping into blocks on which the effective \(B_*\) is uniformly controlled; or
3. a new normalized state that absorbs the growth.

It is invalid simply to call \(A(B_*,M)\) universal.

### 11.11 Category substitution

A full connected virtual hull, a topological circle map on its prime ends, and a
finite list of orbit labels do not imply periodic repulsion, prime primitive
renormalizability, a canonical KKL renormalization, or a Hubbard transition. Such an
object may satisfy none of the literal premises of Proposition 3.7.

The only valid response is to prove the literal promotion or verify the abstract
interface axiom by axiom.

## 12. Period-independence audit

For Theorem 7.1, period independence reduces to the following exact list.

1. The access-complete atom bound \(B_*\) is independent of \(p,q\), rotation number,
   and virtual depth.
2. The marking satisfies \(|\mathcal I^v|=O(B_*p)\).
3. The coefficient \(E_X(B_*)\) in (5.8) is independent of \(p\).
4. The flux witness error \(2\), or its virtual replacement, is independent of \(p\).
5. The restriction constants \(1/2\), \(4\), and endpoint coefficient \(2\), or their
   replacements, are independent of \(p\).
6. The ambient-to-tree width comparison has no multiplicity growing with \(p\).
7. The same marked surface and carrier are used in the WAD, flux, restriction, and
   wave definitions.

Under these conditions, the only appearances of \(p\) cancel:
\[
  pD
  \longleftrightarrow
  \|X\|
  \longrightarrow
  \mathbb W(\mathcal G)
  \longrightarrow
  \frac{\mathbb W(\mathcal G)}{|\mathcal I^v|}
  \asymp
  \frac{pD}{Bp}.
\tag{12.1}
\]
If any denominator contains an additional depth, access-density, or period factor,
the source proof no longer gives a uniform wave.

## 13. Proposed ledger changes

No shared ledger file is modified by this report. The following changes are proposed
for the root audit.

### 13.1 Add one proved formal node

`ABSTRACT_SECTION4_STATIC_TRICHOTOMY`

> Any static virtual Section-4 datum satisfying `S4-AC` through `S4-END` and the
> explicit large-width threshold obeys the amplification/tame/controllable-wave
> trichotomy.

Status: `proved`.

Evidence:
`virtual_section4_interface.md#7-abstract-static-trichotomy`.

Dependencies should include the imported KKL harmonic-width calculus only if the
ledger treats (5.12) as derived rather than as an interface hypothesis. The theorem
as stated is otherwise a direct consequence of its axioms.

### 13.2 Keep the realization node open

Keep `H2_VIRTUAL_SECTION4_INTERFACE` as `open`, change or supplement its evidence with:

`virtual_section4_interface.md#10-exact-unresolved-realization-obligations`.

Its statement should make clear that it asserts realization of the static datum for
every routed virtual-Molecule block, not the already-proved conditional theorem.

### 13.3 Optional open subnodes

For a finer dependency graph, split the realization into:

1. `H2_VIRTUAL_LIMB_ACCESS_REALIZATION` for `VSI-R1`--`VSI-R4`;
2. `H2_VIRTUAL_CYCLE_WIDTH_CALIBRATION` for `VSI-R5`, `VSI-R8`, and `VSI-R9`;
3. `H2_VIRTUAL_STATIC_RESTRICTION_REALIZATION` for `VSI-R6`--`VSI-R7`.

Then
`H2_VIRTUAL_SECTION4_INTERFACE` depends on these three nodes and
`ABSTRACT_SECTION4_STATIC_TRICHOTOMY`.

The finite-tree implication in `virtual_limb_marking_bound.md` should remain a
separate proved node; it must not be used as evidence that access completeness itself
has been constructed.

## 14. Final assessment

The static KKL mechanism is now completely exposed:

\[
\boxed{
\begin{gathered}
\text{access-complete bounded marking}\\
+\ \text{all-cycle WAD calibration}\\
+\ \text{faithful restriction and wave decomposition}\\
+\ \text{large successor width}
\end{gathered}
}
\Longrightarrow
\boxed{
\text{amplification}\ \lor\ \text{tameness}\ \lor\ \text{wide wave}
}.
\]

The implication is proved by Theorem 7.1. What remains open is not another algebraic
manipulation of Proposition 3.7. It is the analytic-dynamical realization of the
boxed hypotheses for Dudko's partially invariant virtual Julia hulls, uniformly in
period, rotation number, and virtual depth.

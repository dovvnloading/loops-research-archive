# Canonical resolution versus the actual KL tile: whole-tile correspondence no-go

## 1. Result, scope, and status

This pass audits the first map-level gate isolated by
`RESOLVED_INTERMEDIATE_RELATIVE_IDEAL_BOUNDARY`.

The result is negative but exact:

> **Whole-tile correspondence no-go.**  
> A canonical resolved factorization with nontrivial deck kernel cannot
> be conjugated, by a based universal-cover isomorphism preserving the
> annular deck generator, to the whole actual Kahn--Lyubich tile map
> while retaining an injective target comparison and KL's continuous
> values at the two wrapping vertices.

For the ordinary primitive canonical resolution, the deck kernel is
infinite.  Consequently the former whole-tile comparison square does not
exist.  The first unsupported operation is the identification of the
propagated canonical \(q/e\) factorization with a covering/embedding
factorization of the complete actual KL tile map.

This theorem does **not** prove that the actual KL immersion is injective.
An arbitrary noninjective holomorphic immersion need not be a covering
onto its image and need not carry a global deck-invariance relation.  It
can therefore extend continuously to its boundary.  The theorem also does
not construct any of the four admissible replacement interfaces:

1. a proper interior or collar restriction;
2. a non-covering immersion or relation-valued comparison;
3. a retimed stage with trivial deck kernel; or
4. a localization with synchronized obstacle packets.

The next positive gate is to construct one such replacement and prove its
component, access, ideal-boundary, properness, and final-root clauses.
`DIRECT_DECORATION_OUTER_CAP_FOOTPRINT`, all Wave certificates, VAAPC-I,
UPTCR, and MLC remain open.

## 2. Source locks and imported scope

No new external theorem is imported.  The source facts are the already
locked statements used in
[`resolved_intermediate_relative_ideal_boundary.md`](resolved_intermediate_relative_ideal_boundary.md):

```text
Kahn I, arXiv:math/0609045
  .tmp_kl06_source/wad.tex
  SHA-256 B5DF40A5D33B6B590B430D47693514088AF6FC287BAA5D87B4D11015B990E580

Kahn--Lyubich II, arXiv:math/0609046
  .tmp_kl08_source/psiql.tex
  SHA-256 6CC9726461473812A5FBA93377F2DC0B088DB6CAC4B9DE90C7B2AE625DFB49AF

  .tmp_kl08_source/moduli.tex
  SHA-256 CBDB9EF7D6AC94C33FDB0AB7167E19C39EB23D27373C266A296CF6031E0CAF7E
```

The exact source uses are:

1. Kahn I, `wad.tex`, lines 169--175, removes the Fuchsian limit set
   from the point-valued ideal boundary.
2. KL II, `psiql.tex`, lines 118--123, defines every tile
   \(\widehat A_i\) as a copy of the universal cover of the ambient
   annulus.
3. KL II, `psiql.tex`, lines 231--244, identifies the two endpoints at
   which the outer \(\lambda_i\)-arc meets the \(J\)-arcs with paths that
   wrap around the filled Julia set infinitely many times.
4. KL II, `psiql.tex`, lines 248--253, extends the actual
   inclusion-induced pseudo-piece immersion continuously to its named
   boundary.
5. KL II, `moduli.tex`, lines 389--392, gives the horizontal-strip
   uniformization, deck translation \(z\mapsto z+1\), and upper side
   covering the \(O\)-boundary.

Items 2--5 identify the two named wrapping vertices with the two fixed
points of the annular deck generator and give actual continuous values of
the KL composite there.  They do not extend an independently invented
resolved factor.

## 3. The two typed systems

### 3.1 Canonical resolved system

Let \(\mathcal E\cong\mathbb D\), and suppose that

\[
 \mathcal E
 \mathop{\longrightarrow}^{q}
 \mathcal R
 \mathop{\longrightarrow}^{e}
 T
 \tag{3.1}
\]

is a holomorphic factorization with:

1. \(q\) a universal covering;
2. \(e\) a holomorphic embedding;
3. \(L=e q:\mathcal E\to T\) nonconstant; and
4. \(N=\operatorname{Deck}(q)\ne\{1\}\).

Suppose this factorization arises from the degree-one annular tower of
the preceding pass.  Thus one fixed based disk action contains

\[
 G=N\rtimes H,\qquad H=\langle h\rangle\cong\mathbb Z,
 \tag{3.2}
\]

where \(h\) is hyperbolic and has the two source-annular wrapping fixed
points

\[
 \zeta_-,\zeta_+\in\partial\mathbb D.
 \tag{3.3}
\]

The normal-kernel wrapping lemma gives

\[
 \zeta_-,\zeta_+\in\Lambda(N).
 \tag{3.4}
\]

At the ordinary primitive canonical seed, the winding theorem in
`KL_LOCALIZATION_SHEET_RESOLUTION_FACTORIZATION` proves that the original
covering fiber is infinite.  Exact tilewise base change preserves that
fiber, so in any proposed whole-tile realization of (3.1), \(N\) would
be infinite and in particular nontrivial.

### 3.2 Actual KL tile system

Let

\[
 L_{\rm KL}:\widehat A_s\longrightarrow\widehat A_t
 \tag{3.5}
\]

be one source-indexed actual KL inclusion tile map.  Both tiles are
universal covers of their ambient annuli.  Let \(t_s\) be the positive
source annular deck generator and let

\[
 \omega_-,\omega_+\in\partial\widehat A_s
 \tag{3.6}
\]

be its two fixed prime ends.  The locked source identifies these with
the named infinitely wrapping \(\lambda/J\) vertices and supplies
continuous values

\[
 \overline L_{\rm KL}(\omega_-),\qquad
 \overline L_{\rm KL}(\omega_+)
 \tag{3.7}
\]

in the Hausdorff conformal ideal closure of the target pseudo-piece.

No injectivity of \(L_{\rm KL}\) is assumed.

## 4. Definition of a whole-tile end-compatible comparison

A **whole-tile end-compatible comparison** from (3.1) to (3.5) is a
pair

\[
 \Phi:\mathcal E\longrightarrow\widehat A_s,
 \qquad
 B:T\longrightarrow\widehat A_t
 \tag{4.1}
\]

satisfying all of the following.

1. **Based universal-cover identification.**  \(\Phi\) is a
   biholomorphism and is a based isomorphism of universal covers over the
   same oriented source annulus.
2. **Deck-generator compatibility.**
   \[
    \Phi h=t_s\Phi.
    \tag{4.2}
   \]
3. **Target separation.**  \(B\) is continuous and injective on
   \(L(\mathcal E)\).  A whole-target-tile isomorphism or embedding is a
   special case.
4. **Composite square.**
   \[
   \begin{array}{ccc}
   \mathcal E&\mathop{\longrightarrow}^{L=e q}&T\\
   {\scriptstyle\Phi}\downarrow&&\downarrow{\scriptstyle B}\\
   \widehat A_s&\mathop{\longrightarrow}^{L_{\rm KL}}&\widehat A_t
   \end{array}
   \qquad
   L_{\rm KL}\Phi=B L.
   \tag{4.3}
   \]
5. **Named-end compatibility.**  In the conformal ideal closures,
   \[
    \overline\Phi(\zeta_-)=\omega_-,
    \qquad
    \overline\Phi(\zeta_+)=\omega_+.
    \tag{4.4}
   \]

Clause 5 follows from clauses 1--2 **with the biholomorphic typing in
clause 1**: after disk uniformization, \(\Phi\) is a disk automorphism,
extends homeomorphically to the conformal ideal circles, and conjugates
the two hyperbolic transformations.  It therefore sends their repelling
and attracting fixed points to the corresponding fixed points.  It is
listed separately because it is the exact endpoint datum used by the
proof and must survive every proposed root enlargement.  Algebraic
generator conjugacy by an arbitrary interior homeomorphism would not
suffice.

This definition does not require a boundary extension of \(q\) or \(e\).
It requires only the actual KL composite extension already supplied by
the source.

## 5. Whole-tile comparison no-go

### Theorem 5.1 -- no end-compatible square with nontrivial kernel

Under Sections 3--4, a whole-tile end-compatible comparison implies

\[
 N=\{1\}.
 \tag{5.1}
\]

Equivalently, if \(N\ne\{1\}\), no pair \((\Phi,B)\) satisfies
clauses 1--5 of Section 4.

#### Proof

Assume \(N\ne\{1\}\).  By (3.4),

\[
 \zeta_+\in\Lambda(N).
 \tag{5.2}
\]

Choose \(z_0\in\mathcal E\).  By the definition of the limit set, there
are distinct \(\gamma_n\in N\) such that

\[
 \gamma_nz_0\longrightarrow\zeta_+.
 \tag{5.3}
\]

For arbitrary \(z\in\mathcal E\), every \(\gamma_n\) is a hyperbolic
isometry, so

\[
 d_{\mathcal E}(\gamma_nz,\gamma_nz_0)
 =
 d_{\mathcal E}(z,z_0).
 \tag{5.4}
\]

Bounded hyperbolic distance and (5.3) imply

\[
 \gamma_nz\longrightarrow\zeta_+
 \quad\text{for every }z\in\mathcal E.
 \tag{5.5}
\]

Because \(N=\operatorname{Deck}(q)\),

\[
 L(\gamma_nz)
 =
 e q(\gamma_nz)
 =
 e q(z)
 =
 L(z).
 \tag{5.6}
\]

Apply the square (4.3):

\[
 L_{\rm KL}\bigl(\Phi(\gamma_nz)\bigr)
 =
 B L(\gamma_nz)
 =
 B L(z).
 \tag{5.7}
\]

The boundary extension of \(\Phi\) and (4.4)--(5.5) give

\[
 \Phi(\gamma_nz)\longrightarrow\omega_+.
 \tag{5.8}
\]

The source-locked continuity of \(L_{\rm KL}\) at \(\omega_+\) now gives

\[
 \overline L_{\rm KL}(\omega_+)
 =
 \lim_{n\to\infty}
 L_{\rm KL}\bigl(\Phi(\gamma_nz)\bigr)
 =
 B L(z).
 \tag{5.9}
\]

Equation (5.9) holds for every \(z\in\mathcal E\).  The map \(L\) is
nonconstant and \(B\) is injective on \(L(\mathcal E)\), so \(BL\) is
nonconstant.  It cannot equal the one fixed value
\(\overline L_{\rm KL}(\omega_+)\) for every \(z\).  This contradiction
proves (5.1). \(\square\)

The same proof works at \(\zeta_-\).  One wrapping vertex is sufficient;
the second is an independent symmetric certificate.

### Corollary 5.2 -- canonical infinite resolution is not a whole KL tile

For the ordinary primitive canonical resolution,

\[
 [K:H_s]=\infty.
 \]

Therefore no whole-tile end-compatible comparison identifies its
covering/embedding factorization with an actual KL tile map.

#### Proof

The canonical winding theorem gives an infinite fiber before tilewise
base change, and the exact fiber bijection preserves it.  Hence
\(N\ne1\).  Apply Theorem 5.1. \(\square\)

### Corollary 5.3 -- exact optional input that fails

The ambient same-seed identity of the Kahn iterate tower does not imply
the whole-tile comparison of Section 4.  If the canonical infinite
factorization and an actual KL tile are both present, the optional
identification

\[
 \mathcal J_{\rm whole}:
 \quad
 L_{\rm KL}\Phi=B(e q)
 \quad\text{with clauses 1--5}
 \tag{5.10}
\]

is false.

This locates the first unsupported operation.  It does not decide, without
an independent realization theorem, whether a proposed same-seed
subclass is empty, whether the canonical factorization corresponds only
to a proper subdomain, or whether the correct comparison changes the
localization data.

## 6. Exact obstruction certificate

The failed square has the finite certificate

\[
 \mathfrak C_{\rm whole}
 =
 \left(
 \begin{array}{l}
 N\ne1,\ \zeta_\pm\in\Lambda(N),\
 \Phi h=t_s\Phi,\
 \overline\Phi(\zeta_\pm)=\omega_\pm,\\
 L_{\rm KL}\Phi=B e q,\
 B|_{L(\mathcal E)}\text{ injective},\
 \overline L_{\rm KL}(\omega_\pm)\text{ defined}
 \end{array}
 \right).
 \tag{6.1}
\]

The complete collision itinerary is any deck sequence

\[
 \gamma_nz\longrightarrow\zeta_+,
 \qquad
 q(\gamma_nz)=q(z),
 \qquad
 L_{\rm KL}(\Phi(\gamma_nz))=B L(z).
 \tag{6.2}
\]

The collision type is

\[
 \chi_{\rm corr}
 =
 \text{nontrivial deck-limit orbit transported to a source-locked
continuous wrapping end}.
 \tag{6.3}
\]

No numerical experiment, local-connectivity assumption, or parameter
shrinking enters the certificate.

## 7. What remains admissible

Theorem 5.1 forbids only the conjunction of the five whole-tile clauses.
It leaves the following sharply different interfaces open.

### 7.1 Proper interior or collar restriction

Let \(C\Subset\mathcal E\) or let \(C\) be a proved end-collar on which
no two points in one \(N\)-orbit are retained.  A comparison

\[
 \Phi_C:C\longrightarrow\widehat A_s
 \]

is not contradicted by Theorem 5.1 because the sequences
\(\gamma_nz\) need not remain in \(C\), and the restricted map need not
be \(N\)-invariant.  To use this repair one must prove:

1. every proof-used Wave path is contained in the retained domain or
   charged to a uniformly bounded defect window;
2. the restriction is an embedding with complete access markings;
3. all omitted sheets and limit-set ends are entered in the defect
   ledger; and
4. the restriction is stable under final-root enlargement.

None of these conclusions follows from the no-go.

### 7.2 Non-covering immersion or relation-valued comparison

The actual KL map can remain a noninjective immersion.  A relation

\[
 \mathscr C\subset
 \mathcal E\times\widehat A_s
 \]

may retain canonical sheets and actual KL accesses without conjugating
the deck action.  It must record every fiber, target footprint, and
proper-path branch; quotienting the relation to one coarse label is
forbidden unless every future observable is constant on its fibers.

### 7.3 Retiming

At a retimed stage with \(N=1\), the obstruction vanishes.  The
one-sheet branch transports the source conformal ideal closure through
\(q\), but the existence of a universal bounded retiming rule is open.

### 7.4 Localization revision

Synchronizing the source and target obstacle packets can change
\[
 H_s,\quad H_t,\quad
 K=a_*^{-1}(H_t),\quad K/H_s,
\]
and may restore subgroup reflection.  Every component, access, and
root-enlargement clause must then be reproved for the revised packet.

## 8. Adversarial controls

### 8.1 Dropping named-end compatibility

An arbitrary interior comparison is insufficient if it is not proved to
extend at the selected end.  On the horizontal strip
\(\mathbb R\times(0,1)\), the homeomorphism
\[
 u(x,y)=(x-1/y,y)
\]
commutes with the deck translation
\[
 h(x,y)=(x+1,y).
\]
Nevertheless
\[
 (n,1/(2n))\longrightarrow+\infty,
\qquad
 u(n,1/(2n))=(-n,1/(2n))\longrightarrow-\infty.
\]
Thus algebraic generator conjugacy alone does not supply wrapping-end
compatibility.  Theorem 5.1 uses the biholomorphic based-cover
identification and the explicit convergence
\(\Phi(\gamma_nz)\to\omega_+\).

### 8.2 Dropping target separation

If \(B\) collapses the entire set \(L(\mathcal E)\) to one point, (5.9)
is no contradiction.  Therefore the no-go requires only the minimal
separation used in the proof: \(B\) must be injective on
\(L(\mathcal E)\).  No global target homeomorphism is needed.

### 8.3 Restricting the source

The theorem cannot be applied to a collar merely because that collar lies
inside \(\mathcal E\).  The deck-limit sequence may leave it.  Any
collar no-go must prove invariance or recurrence inside that collar
separately.

### 8.4 Trivial-kernel positive control

If \(N=1\), the deck-limit obstruction is absent.  A one-sheeted
factorization can be transported to the actual KL tile whenever the
based map-identification and target embedding are independently supplied.
This is consistent with Theorem 5.1.

### 8.5 Non-covering immersion positive control

Define

\[
 F(z)=\exp(4(z-1)),\qquad z\in\mathbb D.
 \tag{8.1}
\]

Then \(|F(z)|<1\), \(F'(z)=4F(z)\ne0\), and \(F\) extends continuously
to \(\overline{\mathbb D}\).  It is noninjective because

\[
 F(\pi i/4)=F(-\pi i/4)=-e^{-4}.
 \tag{8.2}
\]

It is not a covering onto its image.  If it were, the simply connected
domain would make it the universal cover, whose deck group acts
transitively on every fiber.  A deck transformation \(\delta\) carrying
\(\pi i/4\) to \(-\pi i/4\) would satisfy
\[
 \exp(4(\delta(z)-1))=\exp(4(z-1)).
\]
The continuous function
\[
 \frac{4(\delta(z)-z)}{2\pi i}
\]
would be integer-valued on the connected disk, hence constant.  Its
value at \(\pi i/4\) is \(-1\), so
\(\delta(z)=z-\pi i/2\), which is not an automorphism of
\(\mathbb D\).  Thus noninjectivity plus continuous boundary extension is
compatible when the noninjectivity is not a global covering-deck
invariance.  This is exactly why Theorem 5.1 must not be weakened to
"the actual KL tile is injective."

### 8.6 Same-seed existence

The conditional phrase "if the same seed carries the KL
direct-decoration data" does not prove that such a stage exists in the
specific canonical infinite-resolution comparison class.  Theorem 5.1
shows that any realization theorem must specify which map or restriction
is identified.  It cannot supply the forbidden five-clause square.

### 8.7 Final-root enlargement

An enlargement may change \(N\), its limit set, and the selected end
correspondence.  Based-coset bijectivity alone does not transport
(4.2)--(4.4).  A valid enlargement theorem must give a Cartesian map
square and an equivariant map of relative boundary components while
preserving every excluded limit-set defect.

### 8.8 Normality and the correct acting group

The wrapping generator \(h\in H\) is not asserted to lie in
\(N=\operatorname{Deck}(q)\), and the proof never writes
\(q(hz)=q(z)\).  Normality \(N\triangleleft G\), the split
\(G=N\rtimes H\), and non-elementarity are what put the fixed points of
\(h\) in \(\Lambda(N)\).  Without normality or an independent proof of
that limit-set incidence, a cyclic group \(N\) may have two entirely
different fixed points and the wrapping conclusion fails.

### 8.9 Domain-of-discontinuity positive control

A nontrivial cover can extend at points outside its limit set.  In the
strip model \(z\mapsto e^{2\pi iz}\), finite points on either horizontal
edge have ordinary one-sided limits; only the two wrapping ends are the
deck-limit obstruction.  Theorem 5.1 therefore does not invalidate the
relative ideal bordification on
\(\partial\mathbb D\setminus\Lambda(N)\).

### 8.10 Universal-cover typing is essential

Infinite sheet number alone does not provide a nontrivial group acting
transitively on a fiber: a nonregular infinite cover can have trivial
deck group.  The proof uses the separately established fact that the
tilewise \(q_a\) is the **universal** cover of its resolved intermediate.
Only then is \(N=\operatorname{Deck}(q_a)\) the acting group used in
(5.3)--(5.6).

### 8.11 Hausdorff and nonconstant hypotheses

A constant invariant map has a continuous value at every end, and a
non-Hausdorff target can have nonunique limits.  The theorem explicitly
uses both nonconstancy of \(L\) and the Hausdorff KL ideal closure.  Neither
hypothesis may be deleted.

### 8.12 Quantifier audit

The theorem proves
\[
 \forall s\,
 \bigl[
 \operatorname{Canonical}(s)\wedge
 \operatorname{KL}(s)\wedge
 N_s\ne1\wedge
 \operatorname{EndComparison}(s)
 \ \Longrightarrow\ \bot
 \bigr].
\]
It does not prove that the independently defined class
\[
 \{s:\operatorname{Canonical}(s)\wedge\operatorname{KL}(s)\}
\]
is empty or nonempty.  Inferring either would require an independent
realization theorem.  What is empty is only the stronger class whose
definition includes the forbidden whole-tile end-compatible comparison.

## 9. Promotion and immediate next construction

The internally proved node is:

`CANONICAL_KL_WHOLE_TILE_CORRESPONDENCE_NO_GO`.

Its exact content is Theorem 5.1 and Corollaries 5.2--5.3.  It closes the
whole-tile option negatively; this document itself does not construct a
replacement interface.  The subsequent
`CANONICAL_KL_RESTRICTED_INTERFACE_CLASSIFICATION` constructs the
non-covering relation span and tagged maximal interior restrictions for
each supplied fixed labeled same-source datum.

The immediate positive task is now:

> **Canonical/KL relation proper-end response.**
> Realize the proved relation span throughout the complete Wave horizon,
> freeze every proof-used path, and classify every tagged restriction as
> proper, end-proper, or nonproper with actual
> \(\lambda,\xi,\eta\) endpoint incidence.  Prove complete exhaustion or
> a universal Value-observable response for every omitted component, then
> prove cyclic-order and Cartesian final-root naturality.  The relation
> theorem's two wrapping clusters do not supply these claims.

Until that construction is complete,
`DIRECT_DECORATION_OUTER_CAP_FOOTPRINT`,
`DIRECT_DECORATION_PSEUDO_PIECE_PATH_LIFT_EXHAUSTION`,
`VIRTUAL_WAVE_MARKED_CORRESPONDENCE`,
`VIRTUAL_WAVE_HORIZON_CERTIFICATE`, VAAPC-I, UPTCR, and MLC remain open.

# Resolved intermediate: full-boundary obstruction and relative ideal descent

## 1. Verdict and exact scope

The proposed **full** ideal-boundary factorization

\[
 \overline q_a:
 \overline{\mathcal E}_a\longrightarrow
 \overline{\mathcal R}_a,
 \qquad
 \overline e_a:
 \overline{\mathcal R}_a\longrightarrow
 \overline{\widetilde A}_{t,j_\iota(a)}
\]

cannot hold when \(\overline{\mathcal E}_a\) is the full prime-end
closure of the simply connected source tile and

\[
 q_a:\mathcal E_a\longrightarrow\mathcal R_a
\]

is a nontrivial universal covering.  This is not a missing estimate.  It
is a point-set obstruction forced by the deck action.

The exact replacement is a **cover-relative ideal bordification**.  If

\[
 \Gamma_a=\operatorname{Deck}(q_a),\qquad
 \Lambda_a=\Lambda(\Gamma_a)\subset\partial\mathbb D,\qquad
 \Omega_a=\partial\mathbb D\setminus\Lambda_a,
\]

then factorwise boundary descent can be attempted only on

\[
 \mathbb D\cup\Omega_a,
\]

or on a proved \(\Gamma_a\)-invariant subset of that space.  Every point
of \(\Lambda_a\) must be omitted from the point-valued boundary map and
retained as an explicit limit-set/cluster defect.

This note proves:

1. the universal-cover full-boundary no-go;
2. the exact group and pullback identities for an annular \(q/e\)
   factorization;
3. preservation of the obstruction under the tilewise base change;
4. the strongest valid relative-boundary descent theorem;
5. a conditional wrapping-end collision theorem; and
6. the replacement invariant and the first exact failure certificate.

For an actual KL tile, the source does identify the named wrapping
vertices with the two ends of the standalone universal-cover strip.
Combined with the no-go, this proves that any global
covering/embedding factorization of the actual boundary-extended KL tile
map must be one-sheeted.  Consequently the canonical infinite
sheet-resolution cover cannot be silently identified with that whole KL
tile.  What remains open is a correctly typed correspondence between the
canonical resolved carrier boundary and the actual KL marking.  This
note does not prove that any complete proof-used interval of that
canonical carrier avoids its limit set, that \(\mathcal R_a\) has finite
topology, that \(e_a\) is end-proper, or that any proper lift is unique.

Accordingly `DIRECT_DECORATION_OUTER_CAP_FOOTPRINT`,
`VIRTUAL_AUGMENTED_ATOM_PORT_CERTIFICATE`, UPTCR, and MLC remain open.

## 2. Locked source statements

The source use in this note is deliberately narrow.

### 2.1 Kahn's ideal boundary excludes the limit set

Jeremy Kahn, *A priori bounds for some infinitely renormalizable
quadratics: I. Bounded primitive combinatorics*,
arXiv:math/0609045, source-locked file

```text
.tmp_kl06_source/wad.tex
SHA-256 B5DF40A5D33B6B590B430D47693514088AF6FC287BAA5D87B4D11015B990E580
```

uses finite topology as a standing hypothesis in lines 9--21.  In lines
169--175, for a disk uniformization

\[
 \pi:\mathbb D\longrightarrow S
\]

with deck group \(\Gamma\) and limit set \(\Lambda\), Kahn defines

\[
 \widehat S=\overline{\mathbb D}\setminus\Lambda,
 \qquad
 \partial\widehat S=\partial\mathbb D\setminus\Lambda.
\tag{2.1}
\]

Thus Kahn does not extend the universal covering through its deck limit
set.

The finite-topology hypothesis cannot silently be transferred to the
resolved intermediate \(\mathcal R_a\).  No existing project theorem
proves that \(\mathcal R_a\) has finite topology.

### 2.2 KL extends the composite, not the factors

Jeremy Kahn and Mikhail Lyubich,
*A priori bounds for some infinitely renormalizable quadratics:
II. Decorations*, arXiv:math/0609046, source-locked file

```text
.tmp_kl08_source/psiql.tex
SHA-256 6CC9726461473812A5FBA93377F2DC0B088DB6CAC4B9DE90C7B2AE625DFB49AF

.tmp_kl08_source/moduli.tex
SHA-256 CBDB9EF7D6AC94C33FDB0AB7167E19C39EB23D27373C266A296CF6031E0CAF7E
```

constructs the actual pseudo-piece in lines 95--161, its dynamical and
inclusion maps in lines 169--207, and its named ideal-boundary tiling in
lines 231--253.  Lines 248--253 state continuous boundary extension for
the **composite pseudo-piece immersion** and explicitly warn that the
source boundary need not map into the target boundary.

In `moduli.tex`, lines 389--392, the tile universal cover is a horizontal
strip, its deck generator is \(z\mapsto z+1\), and its upper side covers
the \(O\)-boundary.  Together with `psiql.tex`, lines 231--244, this
identifies the two infinitely wrapping named vertices with the two
standalone strip prime ends.

The source does not construct the resolved intermediate
\(\mathcal R_a\), and it does not extend \(q_a\) or \(e_a\) separately.

### 2.3 KKL's covering boundary is only partial

The source-locked KKL file

```text
.tmp_wave_audit/waves-with-Misha.tex
SHA-256 AD4C774806D9902AA54FA31C56AD6146D8034946F19CC5E9CEC3C51A3F94FDD5
```

defines the ideal boundary through
\((\partial\mathbb D\setminus\Lambda)/\Gamma\) in lines 1844--1868.
Lines 2062--2067 extend a covering from an open dense subset of the
source ideal boundary, not from the complete prime-end circle.  Lines
2081--2094 define properness of an immersion on a selected ideal set only
after the corresponding extension is available.

No KKL statement supplies whole-boundary properness for \(e_a\).

## 3. Typed tilewise data

Fix a source tile index \(a\).  Retain the index even when another source
tile has the same target index.  Write

\[
 A_s=\mathbf U^m\setminus K^m,\qquad
 A_t=\mathbf U^n\setminus K^n
\]

for the source and target annuli, and let

\[
 \iota:A_s\longrightarrow A_t
\tag{3.1}
\]

be the inclusion-induced annular immersion.  Kahn's annular argument
gives oriented degree \(+1\), so after oriented generators are fixed,

\[
 \iota_*:\pi_1(A_s)\longrightarrow\pi_1(A_t)
\]

is the identity map \(\mathbb Z\to\mathbb Z\).

Assume that the interior leg has the already constructed factorization

\[
 A_s\xrightarrow{q}P\xrightarrow{e}A_t,
 \qquad
 \iota=e q,
\tag{3.2}
\]

where \(q\) is a surjective connected holomorphic covering and \(e\) is
a holomorphic embedding.  The pullback construction supplies these
Riemann structures: \(P\) inherits the structure of the open embedded
subsurface \(e(P)\subset A_t\), the projection \(e\) is holomorphic, and
\(q=e^{-1}\iota\) is holomorphic.  This assumption is exactly the input of
`KAHN_ITERATE_COMPLEMENTARY_COMPONENT_ALIGNMENT`, Theorem 6.2; no
boundary extension is included in it.

Let

\[
 \pi_t:\widetilde A_{t,j_\iota(a)}\longrightarrow A_t
\]

be the declared target universal-cover tile.  Define the labelled
pullbacks

\[
 \mathcal E_a
 =
 \{a\}\times
 \left(A_s\times_{A_t}\widetilde A_{t,j_\iota(a)}\right),
\tag{3.3}
\]

\[
 \mathcal R_a
 =
 \{a\}\times
 \left(P\times_{A_t}\widetilde A_{t,j_\iota(a)}\right).
\tag{3.4}
\]

The maps are

\[
 q_a(a,x,\widetilde t)
 =
 (a,q(x),\widetilde t),
\tag{3.5}
\]

\[
 e_a(a,p,\widetilde t)=\widetilde t.
\tag{3.6}
\]

After the based KL lift fixes the deck phase, the proved based
isomorphism

\[
 \Phi_a:\widetilde A_{s,a}\xrightarrow{\cong}\mathcal E_a
\]

satisfies

\[
 e_aq_a\Phi_a=L_a,
\tag{3.7}
\]

where \(L_a\) is the interior KL tile lift.  Equation (3.7) is an interior
identity.  It does not identify the standalone prime-end topology of
\(\widetilde A_{s,a}\) with the boundary topology induced by the glued
source pseudo-piece.

There is a necessary typing distinction which will be retained below.
Let \(t_a\) be the positive deck generator on
\(\widetilde A_{s,a}\), and let \(h\in H\) be the corresponding deck
generator on \(\mathcal E_a\).  Based covering uniqueness gives

\[
 \Phi_a t_a=h\Phi_a.
\tag{3.8}
\]

Both domains are conformal disks, so \(\Phi_a\) extends to a
homeomorphism \(\overline\Phi_a\) of their conformal prime-end closed
disks.  In particular it carries the repelling and attracting fixed
points of \(t_a\) to those of \(h\).  Define the transported composite

\[
 K_a
 :=
 L_a\Phi_a^{-1}:\mathcal E_a\longrightarrow
 \widetilde A_{t,j_\iota(a)}.
\tag{3.9}
\]

Equation (3.7), with its domains now respected, is exactly

\[
 K_a=e_aq_a.
\tag{3.10}
\]

KL's boundary theorem will be used only at boundary points where the
actual \(L_a\) is source-locked to have a continuous value.  At such a
point \(\omega\), the transported map \(K_a\) has the continuous value
\(\overline L_a(\omega)\) at
\(\overline\Phi_a(\omega)\).  No full standalone-tile boundary extension
is inferred from (3.7)--(3.10).

## 4. Fundamental-group decomposition

Choose compatible basepoints and put

\[
 G=\pi_1(P),\qquad
 H=q_*\pi_1(A_s)\leq G,\qquad
 N=\ker(e_*:G\to\pi_1(A_t)).
\tag{4.1}
\]

All groups in (4.1) are based groups.  Since \(q\) is a covering,
\(q_*\) is injective.  Since

\[
 e_*q_*=\iota_*=\operatorname{id}_{\mathbb Z},
\tag{4.2}
\]

the following conclusions are forced.

### Lemma 4.1 -- split exact sequence

The map \(e_*:G\to\mathbb Z\) is surjective,
\(H\cong\mathbb Z\), the restriction

\[
 e_*|_H:H\longrightarrow\mathbb Z
\]

is an isomorphism, and

\[
 1\longrightarrow N\longrightarrow G
 \mathop{\longrightarrow}^{e_*}\mathbb Z
 \longrightarrow1
\tag{4.3}
\]

splits through \(q_*\).  In particular,

\[
 G=N\rtimes H.
\tag{4.4}
\]

#### Proof

Surjectivity follows immediately from (4.2): every
\(k\in\mathbb Z\) is \(e_*(q_*(k))\).  Injectivity of \(q_*\) identifies
\(\pi_1(A_s)\) with \(H\), and (4.2) says that \(e_*|_H\) is its inverse.

For \(g\in G\), put

\[
 h=q_*(e_*(g))\in H,\qquad n=gh^{-1}.
\]

Then

\[
 e_*(n)=e_*(g)-e_*(h)=e_*(g)-e_*(g)=0,
\]

so \(n\in N\) and \(g=nh\).  If \(n_1h_1=n_2h_2\), then

\[
 n_2^{-1}n_1=h_2h_1^{-1}\in N\cap H.
\]

The restriction \(e_*|_H\) is injective, so \(N\cap H=\{1\}\).  Hence
\(n_1=n_2\) and \(h_1=h_2\).  Normality of \(N\) follows because it is a
kernel.  This proves (4.4). \(\square\)

### Corollary 4.2 -- one-sheet criterion

The following are equivalent:

1. \(N=\{1\}\);
2. \(G=H\);
3. \(q\) has one sheet; and
4. \(q\) is a homeomorphism.

#### Proof

Lemma 4.1 gives \(G=N\rtimes H\), so (1) and (2) are equivalent.  A
connected covering has one sheet exactly when its subgroup is the full
base group, so (2) and (3) are equivalent.  A one-sheeted covering is a
homeomorphism, giving (3) and (4).  The converse is immediate.
\(\square\)

No normality of \(H\) is used or asserted.

## 5. Exact pullback groups and fiber preservation

### Lemma 5.1 -- source pullback

The pullback \(\mathcal E_a\) is connected and simply connected.  Under
\(\Phi_a\), it is the universal cover of \(A_s\).

#### Proof

The pullback of the universal cover of \(A_t\) along \(\iota\) is
classified by

\[
 \iota_*^{-1}(\{0\})\leq\pi_1(A_s).
\]

Since \(\iota_*:\mathbb Z\to\mathbb Z\) is the identity, the subgroup is
\(\{0\}\).  The number of components is

\[
 [\,\pi_1(A_t):\iota_*\pi_1(A_s)\,]
 =
 [\mathbb Z:\mathbb Z]=1.
\]

Thus the pullback is connected and is the cover classified by the
trivial subgroup.  It is the universal cover. \(\square\)

### Lemma 5.2 -- resolved pullback

The pullback \(\mathcal R_a\) is connected, the projection
\(\mathcal R_a\to P\) is the covering classified by \(N\), and

\[
 \pi_1(\mathcal R_a)\cong N.
\tag{5.1}
\]

#### Proof

Pulling the universal cover of \(A_t\) back along \(e\) gives the cover
of \(P\) classified by

\[
 e_*^{-1}(\{0\})=N.
\]

Its number of components is

\[
 [\,\pi_1(A_t):e_*(G)\,].
\]

Lemma 4.1 gives \(e_*(G)=\mathbb Z\), so this index is one.  Hence the
pullback is connected and its subgroup is \(N\), proving (5.1).
\(\square\)

### Proposition 5.3 -- universal resolved cover

The map

\[
 q_a:\mathcal E_a\longrightarrow\mathcal R_a
\]

is the universal covering of \(\mathcal R_a\), and

\[
 \operatorname{Deck}(q_a)\cong N.
\tag{5.2}
\]

For every \((a,p,\widetilde t)\in\mathcal R_a\), projection to the first
coordinate gives a canonical bijection

\[
 q_a^{-1}(a,p,\widetilde t)
 \longleftrightarrow
 q^{-1}(p).
\tag{5.3}
\]

#### Proof

The map \(q_a\) is the base change of \(q\), hence is a surjective
covering.  Lemma 5.1 makes its domain simply connected, so it is the
universal cover of its connected target.  Its deck group is therefore
isomorphic to the fundamental group of the target, which is \(N\) by
Lemma 5.2.

More precisely, the composite covering

\[
 \mathcal E_a\xrightarrow{q_a}\mathcal R_a
 \longrightarrow P
\tag{5.4}
\]

has simply connected source and is therefore the universal cover of
\(P\).  After the based universal cover is fixed, its full deck group is
identified with \(G=\pi_1(P)\).  The intermediate cover
\(\mathcal R_a\to P\) is classified by the normal subgroup \(N\), so
under this same identification the deck group of
\(q_a:\mathcal E_a\to\mathcal R_a\) is literally the subgroup
\(N\leq G\), not merely an abstract isomorphic copy.
The complete based covering tower is therefore

\[
 \mathcal E_a/H\cong A_s,\qquad
 \mathcal E_a/N\cong\mathcal R_a,\qquad
 \mathcal E_a/G\cong P.
\tag{5.5}
\]

A point of the left side of (5.3) is exactly a point
\((a,x,\widetilde t)\) with \(q(x)=p\).  The target pullback identity
\(e(p)=\pi_t(\widetilde t)\) ensures that every \(x\in q^{-1}(p)\)
defines such a point because

\[
 \iota(x)=e(q(x))=e(p)=\pi_t(\widetilde t).
\]

This proves the bijection. \(\square\)

Consequently a nontrivial or infinite fiber of \(q\) remains nontrivial
or infinite after the tilewise base change.  Connectedness of the
resolved intermediate does not remove this fiber.

## 6. The full-boundary extension obstruction

We first isolate the analytic-topological lemma independently of any
dynamical notation.

### Lemma 6.1 -- bounded hyperbolic distance has one boundary limit

Let \(z_n,w_n\in\mathbb D\), suppose \(z_n\to\zeta\in\partial\mathbb D\),
and suppose

\[
 d_{\mathbb D}(z_n,w_n)\leq C<\infty.
\]

Then \(w_n\to\zeta\).

#### Proof

The pseudohyperbolic distance satisfies

\[
 \rho(z_n,w_n)
 =
 \left|
   \frac{z_n-w_n}{1-\overline{z_n}w_n}
 \right|
 =
 \tanh\!\left(\frac{d_{\mathbb D}(z_n,w_n)}2\right)
 \leq r<1,
\]

where \(r=\tanh(C/2)\).  If a subsequence of \(w_n\) converged to an
interior point, its hyperbolic distance from \(z_n\to\partial\mathbb D\)
would diverge.  If a subsequence converged to
\(\eta\in\partial\mathbb D\) with \(\eta\ne\zeta\), direct substitution
in the displayed cross-ratio would give
\(\rho(z_n,w_n)\to1\), contradicting \(\rho\leq r<1\).  Every convergent
subsequence therefore has limit \(\zeta\), and compactness of
\(\overline{\mathbb D}\) gives \(w_n\to\zeta\). \(\square\)

### Theorem 6.2 -- no extension through a deck-limit point

Let

\[
 \pi:\mathbb D\longrightarrow R
\]

be a nonconstant universal covering of a hyperbolic Riemann surface, let
\(\Gamma=\operatorname{Deck}(\pi)\), and let
\(\zeta\in\Lambda(\Gamma)\).  There is no continuous extension of
\(\pi\) at \(\zeta\) into any Hausdorff space \(Y\) in which distinct
points of \(R\) remain distinct.

#### Proof

Fix \(z_0\in\mathbb D\).  By the definition of the limit set, choose
distinct \(\gamma_n\in\Gamma\) such that

\[
 \gamma_n z_0\longrightarrow\zeta.
\tag{6.1}
\]

For arbitrary \(z\in\mathbb D\), deck transformations are hyperbolic
isometries, so

\[
 d_{\mathbb D}(\gamma_n z,\gamma_n z_0)
 =
 d_{\mathbb D}(z,z_0).
\]

Lemma 6.1 and (6.1) give

\[
 \gamma_n z\longrightarrow\zeta
\quad\text{for every }z\in\mathbb D.
\tag{6.2}
\]

Assume that a continuous extension \(\overline\pi\) at \(\zeta\)
exists.  Since every \(\gamma_n\) is a deck transformation,

\[
 \pi(\gamma_n z)=\pi(z).
\]

Using (6.2) and continuity,

\[
 \overline\pi(\zeta)
 =
 \lim_{n\to\infty}\pi(\gamma_n z)
 =
 \pi(z).
\tag{6.3}
\]

Equation (6.3) holds for every \(z\in\mathbb D\).  Choose
\(z,w\) with \(\pi(z)\ne\pi(w)\).  Then (6.3) makes both distinct points
equal to \(\overline\pi(\zeta)\), contradicting the Hausdorff uniqueness
of limits. \(\square\)

### Corollary 6.3 -- no full prime-end extension

If \(\Gamma\ne\{1\}\), then \(\Lambda(\Gamma)\ne\varnothing\), and
\(\pi\) has no continuous extension from the complete closed disk
\(\overline{\mathbb D}\).

#### Proof

A nonidentity deck transformation has no fixed point in
\(\mathbb D\).  It is hyperbolic or parabolic and has a boundary
attracting point belonging to \(\Lambda(\Gamma)\).  Apply Theorem 6.2.
\(\square\)

### Corollary 6.4 -- no extension of a nonconstant invariant composite

Let \(Y\) be Hausdorff and let

\[
 L:\mathbb D\longrightarrow Y
\]

be nonconstant and \(\Gamma\)-invariant.  For every
\(\zeta\in\Lambda(\Gamma)\), \(L\) has no continuous point-valued
extension at \(\zeta\).

#### Proof

Use the sequence \(\gamma_n\) from Theorem 6.2.  Equation (6.2) still
holds, while invariance gives

\[
 L(\gamma_n z)=L(z).
\]

Continuity at \(\zeta\) would imply

\[
 \overline L(\zeta)=L(z)
\]

for every \(z\in\mathbb D\), contradicting nonconstancy. \(\square\)

This proves more than failure of injectivity: the point-valued continuous
map itself does not exist.

### Model check 6.4 -- annular wrapping point

Let

\[
 S=\{z:0<\operatorname{Im}z<1\},
\qquad
 \pi(z)=e^{2\pi i z}.
\]

Then \(\pi:S\to\{e^{-2\pi}<|w|<1\}\) is a universal cover and

\[
 \pi(z+n)=\pi(z).
\]

In the prime-end closure of \(S\), \(z+n\) tends to the positive wrapping
point as \(n\to+\infty\).  If \(\pi\) extended there, then for
\(0<y_1<y_2<1\),

\[
 e^{-2\pi y_1}
 =
 \lim_{n\to\infty}\pi(n+i y_1)
 =
 \overline\pi(+\infty)
 =
 \lim_{n\to\infty}\pi(n+i y_2)
 =
 e^{-2\pi y_2},
\]

a contradiction.  The negative wrapping point is identical.

The model is diagnostic only; Theorem 6.2 is the proof.

## 7. Application to the resolved tile

Uniformize \(\mathcal E_a\cong\mathbb D\) and put

\[
 \Gamma_a=\operatorname{Deck}(q_a),\qquad
 \Lambda_a=\Lambda(\Gamma_a).
\tag{7.1}
\]

### Theorem 7.1 -- resolved full-boundary dichotomy

Exactly one of the following holds.

1. **One-sheet branch.**  \(N=\{1\}\), \(q\) and \(q_a\) are
   one-sheeted, and the source conformal ideal closure transports
   homeomorphically across \(q_a\).  Whenever the transported composite
   \(K_a\) has a
   continuous extension on a selected source boundary set, \(e_a\)
   extends uniquely on its transported image by
   \[
     \overline e_a
     =
     \overline K_a\,\overline q_a^{-1}.
    \tag{7.2}
   \]
2. **Nontrivial-cover branch.**  \(N\ne\{1\}\), and no continuous
   extension of \(q_a\) exists from the full prime-end closure of
   \(\mathcal E_a\) to any Hausdorff completion of
   \(\mathcal R_a\).

#### Proof

Corollary 4.2 makes \(N=\{1\}\) equivalent to \(q\) being one-sheeted.
Proposition 5.3 makes \(q_a\) a universal cover with deck group \(N\).

If \(N=\{1\}\), then \(q_a\) is a biholomorphism.  Transporting the
source conformal closure through this biholomorphism defines
\(\overline{\mathcal R}_a\) and a homeomorphism
\(\overline q_a\).  Formula (7.2) is continuous, agrees with \(e_a\) in
the interior because \(K_a=e_aq_a\), and is unique because
\(\overline q_a\) is onto.

If \(N\ne\{1\}\), Corollary 6.3 applies to \(q_a\). \(\square\)

### Corollary 7.2 -- exact outer-set formula in the one-sheet branch

In branch 1, for every selected actual-KL source arc
\(\lambda_a^Q\) on which \(\overline L_a\) is defined, put

\[
 \lambda_a^E=\overline\Phi_a(\lambda_a^Q),
 \qquad
 \lambda_a^R=\overline q_a(\lambda_a^E).
\]

Then

\[
 \overline q_a(\lambda_a^E)=\lambda_a^R,
\qquad
\overline e_a\overline q_a|_{\lambda_a^E}
 =
 \overline K_a|_{\lambda_a^E}
 =
 \overline L_a\overline\Phi_a^{-1}|_{\lambda_a^E}.
\]

The cyclic order and multiplicity are transported without loss because
both \(\overline\Phi_a\) and \(\overline q_a\) are homeomorphisms.

This positive branch recovers the native embedded control.  It does not
apply to an infinite-sheeted resolved collision.

### Corollary 7.3 -- fiber propagation makes the no-go test exact

If the annular cover \(q\) in (3.2) is nontrivial, then the full-boundary
resolved factorization is impossible at that tile.  If \(q\) is
infinite-sheeted, then \(q_a\) is infinite-sheeted.

#### Proof

Use the fiber bijection (5.3) and Theorem 7.1. \(\square\)

### Corollary 7.4 -- the former infinite-fiber KL-tile application is quarantined

One may not combine:

1. infinite-fiber propagation of the canonical primitive resolution;
2. identification of that propagated cover with a whole actual KL tile
   factorization (3.2)--(3.7); and
3. KL's continuous extension at the named wrapping vertices.

Section 8 proves that items 2--3 force \(N=\{1\}\), while item 1 would
force \(N\ne\{1\}\).  Thus the previous claimed whole-tile application
must be audited at the map-identification step.  The exact equalizer
base-change theorem on the unfilled canonical cover remains valid, but it
does not by itself identify that cover with the actual KL tile
factorization.

## 8. Wrapping endpoints and actual KL compatibility

Let \(h\in H\) be the image under \(q_*\) of the positive oriented
generator of \(\pi_1(A_s)\).  In the universal cover
\(\mathcal E_a\cong\mathbb D\), \(h\) is hyperbolic: the annulus
\(A_s=\mathbf U^m\setminus K^m\) has positive finite modulus because
\(K^m\Subset\mathbf U^m\).  Let
\(\zeta_-,\zeta_+\in\partial\mathbb D\) be its repelling and attracting
fixed points.  They are the two wrapping points in the standalone
prime-end closure of the universal cover of the annulus.

### Lemma 8.1 -- normal-kernel wrapping collision

If \(N\ne\{1\}\), then

\[
 \zeta_-,\zeta_+\in\Lambda(N)=\Lambda(\Gamma_a).
\tag{8.1}
\]

#### Proof

The group \(G\) acts as the deck group of the composite universal cover
\(\mathcal E_a\to P\).  Suppose first that \(G\) were elementary.
It is torsion-free and contains the hyperbolic element \(h\), so it is
cyclic.  Write \(G=\langle g\rangle\) and \(h=g^m\).  Since
\(e_*(h)=1\),

\[
 m\,e_*(g)=1
\]

in \(\mathbb Z\).  Therefore \(m=\pm1\), \(H=G\), and
\(N=\ker e_*=\{1\}\), contrary to the hypothesis.  Hence \(G\) is
non-elementary.

The subgroup \(N\) is nontrivial and normal in \(G\).  Its limit set is
nonempty, closed, and \(G\)-invariant: normality gives

\[
 g\Lambda(N)=\Lambda(gNg^{-1})=\Lambda(N)
\]

for every \(g\in G\).  If \(\Lambda(N)\) were finite, its one- or
two-point set would be preserved by \(G\), making \(G\) elementary.
Thus \(\Lambda(N)\) is infinite.  Choose

\[
 \alpha\in\Lambda(N)\setminus\{\zeta_-,\zeta_+\}.
\]

Because \(h\) normalizes \(N\), every \(h^k\alpha\) belongs to
\(\Lambda(N)\).  Hyperbolic dynamics gives

\[
 h^k\alpha\to\zeta_+\quad(k\to+\infty),
\qquad
 h^k\alpha\to\zeta_-\quad(k\to-\infty).
\]

Closedness of \(\Lambda(N)\) proves (8.1). \(\square\)

### Lemma 8.2 -- source-locked KL wrapping identification and transport

For an actual KL universal-cover tile, let
\(\omega_-,\omega_+\in\partial\widetilde A_{s,a}\) be the repelling and
attracting fixed points of \(t_a\).  They are the named wrapping vertices
where the outer
\(\lambda_a\)-arc meets the two \(J\)-side arcs, and the actual
inclusion-induced tile map \(L_a\) has continuous limits there.  Moreover,

\[
 \overline\Phi_a(\omega_-)=\zeta_-,
 \qquad
 \overline\Phi_a(\omega_+)=\zeta_+,
\tag{8.2}
\]

and the transported composite \(K_a=L_a\Phi_a^{-1}\) has the
corresponding continuous values at \(\zeta_-\) and \(\zeta_+\).

#### Proof

KL II, `moduli.tex`, lines 389--392, uniformizes the universal-cover tile
by a horizontal strip whose deck generator is \(z\mapsto z+1\) and whose
upper boundary covers the \(O\)-boundary.  The two prime ends
\(\pm\infty\) are exactly the fixed points of that generator.
`psiql.tex`, lines 231--244, puts the
\(\lambda,\xi,\eta\) arcs on this tile boundary and identifies the two
\(\lambda\)-to-\(J\) meeting points with paths wrapping around the filled
Julia set infinitely many times.  Thus these meeting points are
\(\omega_-,\omega_+\).  Lines 248--253 state continuous extension of the
actual inclusion-induced pseudo-piece immersion to the named boundary;
restriction gives the two asserted limits of \(L_a\).

Equation (3.8) conjugates the two hyperbolic generators.
\(\overline\Phi_a\) therefore carries their repelling and attracting
fixed points as asserted in (8.2).  Composing the two source-locked
limits with \(\overline\Phi_a^{-1}\) gives the asserted limits of
\(K_a\). \(\square\)

### Theorem 8.3 -- actual KL whole-tile factorization is one-sheeted

Assume the typed data (3.1)--(3.10) give a covering/embedding
factorization of the **actual** KL tile lift, with the source-locked
boundary identification and endpoint transport of Lemma 8.2.  Then

\[
 N=\{1\}.
\tag{8.3}
\]

Equivalently, \(q\) and \(q_a\) are one-sheeted.

#### Proof

Suppose \(N\ne\{1\}\).  Lemma 8.1 gives

\[
 \zeta_-,\zeta_+\in\Lambda(N).
\]

Because \(K_a=e_aq_a\), every element of
\(N=\operatorname{Deck}(q_a)\) leaves \(K_a\) invariant.  The map \(K_a\)
is nonconstant because it is a holomorphic immersion.  Corollary 6.4
therefore says that \(K_a\) cannot extend continuously at either
\(\zeta_-\) or \(\zeta_+\).  This contradicts Lemma 8.2.  Hence
\(N=\{1\}\).  Corollary 4.2 and Proposition 5.3 give the equivalent
one-sheet statements. \(\square\)

### Corollary 8.4 -- exact incompatibility certificate

The infinite canonical sheet-resolution cover cannot be transported to
an actual full KL tile as the same global covering/embedding
factorization.  The first incompatible datum is:

\[
 \left(
   N\ne1,\ \zeta_\pm\in\Lambda(N),\
   K_a=L_a\Phi_a^{-1}=e_aq_a,\
   K_a\text{ continuous at }\zeta_\pm
 \right).
\tag{8.4}
\]

At least one of the following map-level identifications must therefore
fail:

1. the canonical resolved cover is the whole actual KL tile cover;
2. the propagated intermediate is the image factor \(P\) in (3.2);
3. the selected equalizer component is the complete KL tile rather than
   a proper interior/collar locus; or
4. the same-seed realization supplies the asserted map identification.

This does not refute the abstract equalizer base change or KL boundary
extension.  It refutes their unsupported simultaneous identification.

## 9. Relative ideal descent

The obstruction is exact, but it does not forbid boundary work on the
domain of discontinuity.

Let \(\Gamma\) be a torsion-free Fuchsian group acting on
\(\mathbb D\), let

\[
 \Lambda=\Lambda(\Gamma),\qquad
 \Omega=\partial\mathbb D\setminus\Lambda,
\]

and let \(J\subset\Omega\) be a \(\Gamma\)-invariant open set.  Put

\[
 X_J=\mathbb D\cup J.
\tag{9.1}
\]

The action on \(X_J\) is properly discontinuous.  Define

\[
 R_J=X_J/\Gamma
\tag{9.2}
\]

with the quotient topology.

### Theorem 9.1 -- cover-relative boundary descent

The quotient \(R_J\) is Hausdorff and the quotient map

\[
 \overline q_J:X_J\longrightarrow R_J
\tag{9.3}
\]

extends the universal covering \(q:\mathbb D\to\mathbb D/\Gamma\).

Let \(T^\partial\) be Hausdorff.  Suppose a continuous map

\[
 \overline L_J:X_J\longrightarrow T^\partial
\]

extends a map \(L=e q\) on \(\mathbb D\).  Then
\(\overline L_J\) is automatically constant on every
\(\Gamma\)-orbit in \(J\), and it descends to a unique continuous

\[
 \overline e_J:R_J\longrightarrow T^\partial
\tag{9.4}
\]

\[
 \overline e_J\,\overline q_J=\overline L_J.
\tag{9.5}
\]

If \(\lambda^Q\subset J\), then defining

\[
 \lambda^R=\overline q_J(\lambda^Q)
\tag{9.6}
\]

gives

\[
 \overline q_J(\lambda^Q)=\lambda^R,
\qquad
 \overline e_J\overline q_J|_{\lambda^Q}
 =
 \overline L_J|_{\lambda^Q}.
\tag{9.7}
\]

#### Proof

By definition of the domain of discontinuity, \(\Gamma\) acts properly
discontinuously on \(\mathbb D\cup\Omega\), hence on \(X_J\).  A properly
discontinuous action by homeomorphisms on this locally compact Hausdorff
space has Hausdorff orbit space, proving the first assertion.

Fix \(x\in J\), \(\gamma\in\Gamma\), and choose \(z_n\in\mathbb D\) with
\(z_n\to x\).  Then \(\gamma z_n\to\gamma x\), while interior deck
invariance gives

\[
 \overline L_J(\gamma z_n)
 =
 L(\gamma z_n)
 =
 L(z_n)
 =
 \overline L_J(z_n).
\]

Continuity and the Hausdorff hypothesis imply

\[
 \overline L_J(\gamma x)=\overline L_J(x).
\]

Thus the boundary map is constant on quotient fibers.  Define

\[
 \overline e_J([x])=\overline L_J(x).
\]

Orbit constancy makes this well-defined.  A map from a quotient is
continuous exactly when its composite with the quotient map is
continuous, so the quotient property makes it continuous; surjectivity
of \(\overline q_J\) makes it unique.
Equations (9.6)--(9.7) are then substitutions. \(\square\)

### Corollary 9.2 -- interior invariance is insufficient by itself

Although continuous extension makes orbit constancy automatic, a
boundary descent on a proposed marked interval still requires:

1. a continuous extension in the **same** topology \(X_J\);
2. proof that the proposed interval is contained in \(J\subset\Omega\);
   and
3. an independent identification of \(\lambda^R\) as the actual resolved
   outer side if that geometric meaning is needed.

Defining \(\lambda^R\) only by (9.6) proves an image identity, not the
physical \(O\)-side interpretation.

## 10. The required replacement invariant

For every source tile \(a\), the boundary state must retain at least

\[
 \mathfrak B_a
 =
 \left(
   \Gamma_a,\Lambda_a,\Omega_a,
   \mathscr I_a^{\rm KL},
   \operatorname{inc}_a,
   \operatorname{Stab}_a,
   \operatorname{phase}^{\rm int}_a,
   \mathscr D_a
 \right).
\tag{10.1}
\]

Here:

- \(\Gamma_a=\operatorname{Deck}(q_a)\);
- \(\Lambda_a\) is its limit set;
- \(\Omega_a=\partial\mathbb D\setminus\Lambda_a\);
- \(\mathscr I_a^{\rm KL}\) is the complete named KL
  \(\lambda,\xi,\eta\) marking, retained separately for each source tile;
- \(\operatorname{inc}_a\) is the still-to-be-proved incidence relation
  between the named KL boundary and
  \(\Lambda_a\sqcup\Omega_a\);
- \(\operatorname{Stab}_a\) records stabilizers and orbit multiplicities
  of all surviving ideal intervals;
- \(\operatorname{phase}^{\rm int}_a\) is the interior based deck-phase
  normalization fixed by \(\Phi_a\); a boundary phase is not declared
  until the incidence/correspondence map is constructed; and
- \(\mathscr D_a\) records every limit-set point used or approached by a
  proof path, together with its cluster/impression status under the
  composite \(L_a\).

Once an incidence realization

\[
 \operatorname{inc}_a:
 \mathscr I_a^{\rm KL}\longrightarrow
 \mathcal P(\partial\mathbb D)
\]

has actually been constructed, define two different flags for a named
marked set \(I\):

\[
 \chi_{\rm hit}(I;\operatorname{inc}_a)
 =
 \begin{cases}
 0,&\operatorname{inc}_a(I)\cap\Lambda_a=\varnothing,\\
 1,&\operatorname{inc}_a(I)\cap\Lambda_a\ne\varnothing,
 \end{cases}
\tag{10.2}
\]

and

\[
 \chi_{\rm edge}(I;\operatorname{inc}_a)
 =
 \begin{cases}
 0,&\overline{\operatorname{inc}_a(I)}\cap\Lambda_a=\varnothing,\\
 1,&\overline{\operatorname{inc}_a(I)}\cap\Lambda_a\ne\varnothing.
 \end{cases}
\tag{10.3}
\]

No point-valued factorwise statement is permitted on a marked set with
\(\chi_{\rm hit}(I;\operatorname{inc}_a)=1\).  The flag
\(\chi_{\rm edge}(I;\operatorname{inc}_a)=1\) is weaker:
an open component of \(\Omega_a\) can have both endpoints in
\(\Lambda_a\), and its quotient can still be a complete component of the
relative ideal boundary.  In that case the endpoints are omitted rather
than assigned boundary values, and the quotient topology and stabilizer
must be recorded explicitly.

The available replacement operations are:

1. retime to a stage at which the resolved cover is one-sheeted;
2. choose one lifted interval in \(\Omega_a\), retain it separately,
   form its complete \(\Gamma_a\)-orbit saturation inside an invariant
   domain \(J\), and charge every excluded endpoint or component;
3. retain the composite KL boundary map while recording the complete
   limit-set cluster groupoid; or
4. revise the localization/obstacle packet and recompute
   \(\Gamma_a,\Lambda_a,\Omega_a\).

None of these operations has yet been proved uniformly through the Wave
horizon.

## 11. Exact failure certificate

The first failure of the original full-boundary theorem is not an
unlocated prime-end ambiguity.  It has the following exact certificate:

\[
 \mathfrak C_a
 =
 \left(
  a,\Gamma_a,\gamma,\zeta_+,
  \{\,\gamma^n z:n\ge0\,\},
  q_a(\gamma^n z)=q_a(z),
  \text{full-prime-end extension}
 \right),
\tag{11.1}
\]

where \(1\ne\gamma\in\Gamma_a\) and \(\zeta_+\) is its attracting
boundary fixed point.  The complete itinerary is the deck word
\(\gamma^n\); its image itinerary is constant; the collision type is a
**deck-limit missing end**.  For the standalone annular wrapping points,
Lemma 8.1 gives the stronger certificates obtained from sequences in
\(N\) converging to \(\zeta_-\) and \(\zeta_+\).

For an actual KL tile, Lemma 8.2 transports the two actual wrapping
vertices through \(\overline\Phi_a\), so (11.1) becomes an actual
marked-access contradiction whenever the same \(q_a\) is asserted
nontrivial.  The first missing datum is therefore not those two endpoint
labels.  It is the map-level correspondence that was claimed to transport
the canonical infinite resolved cover to the whole actual KL tile despite
Theorem 8.3.

## 12. Adversarial audit

### 12.1 Connected intermediate

Connectedness of \(\mathcal R_a\) does not help.  Proposition 5.3 shows
that the connected surface can have a nontrivial universal cover, and
Theorem 6.2 uses precisely that deck group.

### 12.2 Deck phase

Changing the based identification by a deck translate changes which
lifted interval is selected.  It does not change \(\Lambda_a\) or remove
the no-go.  The based phase is necessary for markings but cannot create a
missing boundary value.

### 12.3 Composite extension

Continuity of the glued KL composite does not extend \(q_a\) and \(e_a\)
separately.  At the two wrapping vertices, however, KL does identify the
standalone strip ends and proves continuity.  The based cover
biholomorphism \(\Phi_a\) must be inserted before comparing domains:
\(K_a=L_a\Phi_a^{-1}=e_aq_a\), and
\(\overline\Phi_a(\omega_\pm)=\zeta_\pm\).  Theorem 8.3 therefore forces
any whole-tile covering/embedding factorization of that actual KL map to
be one-sheeted.  Omitting \(\Phi_a^{-1}\) would be a domain error, even
though the repaired argument has the same conclusion.  The canonical
infinite resolved cover must be compared to the KL tile by a different,
explicitly constructed correspondence.

### 12.4 Non-locally-connected image

Even on a relative interval in \(\Omega_a\), a conformal embedding
\(e_a(\mathcal R_a)\subset\widetilde A_t\) can have a prime end with a
nondegenerate target impression.  Theorem 9.1 descends a supplied
continuous composite; it does not prove singleton impressions.

### 12.5 Slit access merger

The inclusion

\[
 \mathbb D\setminus[0,1)\hookrightarrow\mathbb D
\]

has two distinct prime ends on opposite sides of the slit with the same
target landing point.  Thus continuous descent alone does not prove
access injectivity or cyclic-order fidelity.

### 12.6 Nonproper embedded disk

The embedding \(z\mapsto z/2\) from \(\mathbb D\) into \(\mathbb D\)
extends continuously but maps its ideal circle into the target interior.
Boundary continuity alone does not prove end-properness.

### 12.7 Finite quotient

Replacing \(\Gamma_a\) or its orbit relation by a finite label set does
not repair Theorem 6.2.  Such a replacement is admissible only after it
is proved future-faithful for every proof-used interval, cluster set, and
proper-path predicate.

### 12.8 Open versus closed intervals

An open subinterval of \(\Omega_a\) may support relative descent.  Its
closed endpoints cannot be reinserted if they lie in \(\Lambda_a\).
Nevertheless, an entire component of \(\Omega_a\), quotiented by its
stabilizer, can be a complete relative ideal-boundary circle.  Thus a
limit-set endpoint warning does not invalidate that quotient component;
it only forbids treating the omitted standalone endpoints as
point-valued boundary elements.

### 12.9 Final-root enlargement

An enlargement can change the deck group and hence its limit set.  It
must transport

\[
 (\Gamma_a,\Lambda_a,\Omega_a,\operatorname{inc}_a)
\]

equivariantly.  Based-coset bijectivity alone does not prove limit-set
or boundary-incidence stability.

## 13. Promotion decision and next gate

The internally proved result is:

`RESOLVED_INTERMEDIATE_RELATIVE_IDEAL_BOUNDARY`

with exactly the content of Theorems 6.2, 7.1, 8.3, and 9.1:

- no full prime-end extension of a nontrivial resolved universal cover;
- a one-sheet/full-boundary versus nontrivial-cover/no-go dichotomy; and
- the fact that any whole-tile covering/embedding factorization of the
  actual boundary-extended KL tile map must be one-sheeted, which
  quarantines the former infinite-cover whole-tile identification; and
- exact descent on a \(\Gamma_a\)-invariant subset of the domain of
  discontinuity.

The intended full
`DIRECT_DECORATION_OUTER_CAP_FOOTPRINT` obligation remains open and must
use \(\mathfrak B_a\).

The immediately following audit is now completed in
[`canonical_resolution_kl_tile_correspondence_no_go.md`](canonical_resolution_kl_tile_correspondence_no_go.md).
It proves that no based, end-compatible, target-separating whole-tile
comparison can identify the canonical infinite factorization with the
actual KL tile.

The subsequent
[`canonical_kl_restricted_interface_classification.md`](canonical_kl_restricted_interface_classification.md)
constructs, for every supplied fixed labeled same-source datum, the
non-covering relation span and tagged maximal interior restrictions.  It
also proves non-descent, the two wrapping cluster incidences, the
unscaled collar-width source-hypothesis no-go, unchanged-tower retiming
persistence, and the subgroup-reflection criterion with its lift
hypothesis.

The immediate positive gate is:

> **Canonical/KL relation proper-end response.**
> Realize the proved relation span at every complete Wave stage, freeze
> the proof-use path ledger, classify every tagged component and its
> actual \(\lambda,\xi,\eta\) incidence as proper, end-proper, or
> nonproper, and prove exhaustion or a universal Value-observable response.
> Then prove equivariance under Cartesian final-root enlargement.

No \(O,\xi,\eta\) footprint, Wave certificate, VAAPC-I, UPTCR, or MLC
status changes in this pass.

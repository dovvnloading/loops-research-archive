# Direct-decoration outer-port footprint: corrected scope and obstruction

## 1. Verdict

Fix one of the two one-step direct-decoration pullbacks

\[
 Q=Q_a\subset P=Y^{(n-1)q+1},
 \qquad
 g=f^q|_Q:Q\longrightarrow P,
 \qquad a\in\{L,R\},
\]

and the induced pseudo-piece pair

\[
 \mathbf Q
 \overset{\mathbf g}{\underset{\boldsymbol\iota}{\rightrightarrows}}
 \mathbf P.
\]

KL construct a fixed-branch holomorphic immersion
\(\boldsymbol\iota:\mathbf Q\to\mathbf P\).  A hostile source audit found
two linked invalid inferences in the earlier project state: the induced
tile immersions were first treated as globally injective and then as
literal inclusions of nested round annuli.  Neither conclusion follows
from degree one.

The corrected result has three layers.

1. The KL pseudo-pieces \(\mathbf P,\mathbf Q_a\) are hyperbolic conformal
   disks, their named boundary is their conformal ideal circle, and the
   inclusion immersion has the required continuous ideal extension.
2. The abstract accessible-footprint theorem applies to a separately
   embedded retained collar or revised localization.  It does not apply to
   the full canonical immersion, which is noninjective.
3. The horizontal lower-strip, isolated cap, closed-\(O\)-footprint, and
   three-atom tile-star conclusions are proved only for the additional
   **common-coordinate nested-annulus model** `(CI)` defined below.  They
   are not proved for a general KL \(\psi\)-ql annulus immersion.

An explicit \(\mathbb Z\)-equivariant univalent strip perturbation shows
why the deleted inference is false.  Thus
`DIRECT_DECORATION_OUTER_CAP_FOOTPRINT` is open in its intended KL scope.
The correct replacement invariant is the actual complement-access
footprint of the immersed tile boundary, not its nominal \(O\)-label or
an assumed Green-height cap.

The subsequent exact finite-Blaschke-quotient certificate strengthens the
abstract injectivity obstruction: even Kahn's analytic degree-one
inner-boundary and exact annular-modulus hypotheses do not imply global
annulus injectivity.  More decisively,
`kl_canonical_localization_forced_collision.md` gives an actual KL
canonical-stage collision.

Throughout this note, “the full canonical map” at a direct-decoration
stage means the exact stage obtained by Kahn's pullback propagation from
that canonical primitive seed.  No assertion is made about a
direct-decoration pair lacking that alignment.

The abstract positive assertion uses two proved facts: KL's named ideal
boundary is the conformal ideal boundary of the simply connected
pseudo-piece, and a holomorphic disk embedding with continuous ideal
extension has light boundary fibers.  For an embedding, consequently,
every parameter component of a target-path intersection has two genuine
source prime-end limits, and the KKL pullback is exactly the set of source
prime ends whose complete complement-access footprint lies in the
selected target set.  Application to the actual KL immersion remains
conditional on global tile injectivity and therefore is unavailable for
the full canonical map.  It remains valid for a separately proved
collision-free retained collar.

For the full canonical localization, the first remaining object is not
global univalence: that route is closed negatively.  The replacement
object is the sheet-resolved access footprint of the immersed source
\(O\)-side, indexed by the pointed coset set

\[
 \mathscr S_{\rm loc}=a_*^{-1}(H_t)/H_s.
\tag{1.1}
\]

This is a pointed coset set, not an asserted quotient group.

The subsequent canonical sheet-resolution theorem now constructs the
precise interior object represented by (1.1).  On the physical canonical
seed, if \(A\) is the localized inclusion and
\(K=a_*^{-1}(H_t)\), then

\[
 \widehat X_s\xrightarrow{q}P_K\xrightarrow{e}\widehat X_t,
 \qquad A=e\circ q,                                \tag{1.2}
\]

where \(q\) is the \(H_s\)-to-\(K\) covering, \(e\) is embedded, and
\(A\) and \(q\) have identical kernel pairs.  Winding of the powers of
the forced peripheral class proves

\[
 [K:H_s]=\infty.                                   \tag{1.3}
\]

Thus every resolved collision fiber is infinite: raw finite sheet
enumeration is impossible.  The category of elements of the monodromy
functor of \(q\), not a quotient-group structure on (1.1), is the canonical
sheet groupoid.  Base change propagates (1.2) through each full, unselected
exact Kahn equalizer on the complementary-cover locus.  It supplies no
filled or prime-end extension.  Identifying the selected proof-used
direct-decoration component and its \(O\)-side, with the same-seed
alignment, remains open.

After that, the nonproper source
\(\xi\)- and \(\eta\)-segments whose images enter the central seam
\(K_P\setminus K_Q\) must also be computed.  Without all of those
sheet-resolved footprints, the full family of pullbacks cannot be proved
pairwise disjoint, covering-refined, proper, or end-proper.  A retained
collar may still use the conditional embedding theorems, but its discarded
cosets and sheets must remain explicit defect data.

Accordingly,
the universal full-canonical interpretation of
`DIRECT_DECORATION_DEGREE_ONE_PSEUDO_EMBEDDING` is unavailable as a proof
route.
`DIRECT_DECORATION_PSEUDO_PIECE_PATH_LIFT_EXHAUSTION`, VAAPC-I, UPTCR,
and MLC remain open.

## 2. Source lock

### 2.1 Kahn--Lyubich decorations source

The primary construction source is:

- Jeremy Kahn and Mikhail Lyubich, *A priori bounds for some infinitely
  renormalizable quadratics. II. Decorations*, arXiv:math/0609046.

The official arXiv source archive and audited files have SHA-256 hashes:

```text
.tmp_kl08_source.tar
  DA8FCF924793267421F80BE3E17CD7EB2B72CD4F5B08E3F5A38E2161EC608234

.tmp_kl08_source/kingdom.tex
  5DC04FEFF6B6A1D73040FFD50519C35D62EFF03C1049686DA71D595758E38FA7

.tmp_kl08_source/psiql.tex
  6CC9726461473812A5FBA93377F2DC0B088DB6CAC4B9DE90C7B2AE625DFB49AF

.tmp_kl08_source/moduli.tex
  CBDB9EF7D6AC94C33FDB0AB7167E19C39EB23D27373C266A296CF6031E0CAF7E
```

Only the following live, compiled source assertions are used.

1. `kingdom.tex`, lines 17--18 and 45--62: the nested
   equipotentials \(U^m\), the depth-\(m\) puzzle pieces, their vertices,
   and the connected sets \(K_Y=Y\cap K(f)\).
2. `kingdom.tex`, lines 116--137: the definition of
   \(P=Y^{(n-1)q+1}\), the exclusion \(f^q(0)\notin P\), and the two
   univalent pullbacks \(Q_L,Q_R\subset P\) of depth \(nq+1\).
3. `psiql.tex`, lines 95--161: the path-space and glued-tile definitions
   of
   \[
      \mathbf Y=Y\sqcup_{e_i}\widehat A_i,
   \]
   the fact that different tile images are disjoint, the identity
   \(\widehat A_i\cap Y=Y_i\), and exhaustion of the pseudo-piece by the
   central copy and the tiles.
4. `psiql.tex`, lines 169--207: naturality under a puzzle branch and a
   puzzle inclusion; in particular, the covering and immersion maps on
   pseudo-pieces.
5. `psiql.tex`, lines 231--253: the boundary arcs
   \(\lambda_i,\xi_i,\eta_i\), the two wrapping endpoints at which
   \(\lambda_i\) meets \(\xi_i\) and \(\eta_i\), and continuous boundary
   extension of an inclusion immersion.
6. `moduli.tex`, lines 361--371 and 389--394: round-annulus and
   horizontal-strip uniformizations for the individual domains, with deck
   generator \(z\mapsto z+1\), and the identification of the upper strip
   boundary with the \(O\)-boundary.  These lines do **not** say that the
   immersion between two such strips is their common-coordinate
   inclusion.
7. `moduli.tex`, lines 420--443: the natural immersion from a deeper
   truncation to a shallower tile and the fact that a maximal lift can
   terminate on the deeper \(O\)-boundary.  This is used only as a
   consistency check; it is not treated as a footprint theorem.
8. Kahn I, `psiql2.tex`, lines 87--98: a general degree-one annulus
   immersion is proved embedded only on a sufficiently thin inner collar.
   This source result is incompatible with silently treating every such
   immersion as a global round-annulus inclusion.

### 2.2 Kahn's ideal-boundary and itinerary source

The conformal ideal-boundary identification and the itinerary convention
are source-checked against:

- Jeremy Kahn, *A priori bounds for some infinitely renormalizable
  quadratics. I. Bounded primitive combinatorics*,
  arXiv:math/0609045.

The official source records are:

```text
.tmp_kl06_source.tar
  3A63FC9773DB8B60ED4A0EB9A1C551E6F66C08E66AB92C36F4E2B482570AB817

.tmp_kl06_source/wad.tex
  B5DF40A5D33B6B590B430D47693514088AF6FC287BAA5D87B4D11015B990E580
```

In `wad.tex`, lines 169--175, Kahn defines the ideal closure from the
universal uniformization
\(\pi:\mathbb D\to S\), the deck group \(\Gamma\), and its limit set
\(\Lambda\).  For a simply connected hyperbolic pseudo-piece,
\(\Gamma\) is trivial and \(\Lambda=\varnothing\), so this closure is
literally \(\overline{\mathbb D}\).  KL II refers to Kahn I for the
detailed pseudo-quadratic-like framework, calls
\(\lambda,\xi,\eta\) a tiling of this ideal boundary, and states that
the inclusion immersion extends continuously to it.  Section 9 below
records the complete deduction and explains why it assumes no local
connectivity of a physical Julia boundary.

In `wad.tex`, lines 363--382, a target path restricted to a subdomain is
represented by the finite sequence of its nontrivial source components.
Consecutive components are connected through a complementary component,
and the corresponding source end can be nonproper in the target.  This is
evidence for retaining a complement itinerary.  It is not imported as a
theorem that the direct-decoration itinerary has uniformly bounded length
or that its central-seam footprints are finite marking intervals.

### 2.3 KKL path-pullback source

The exact pullback definition is taken from the source-locked file

```text
.tmp_wave_audit/waves-with-Misha.tex
  AD4C774806D9902AA54FA31C56AD6146D8034946F19CC5E9CEC3C51A3F94FDD5
```

at:

- line 406: a KKL proper path extends continuously to two ideal-boundary
  endpoints;
- lines 2081--2097: restriction under an immersion and the universal
  definition of \(\iota^*X\);
- lines 2128--2129: the refinement condition for an action marking; and
- lines 2157--2159: properness on complete end-intervals.

The continuous two-end extension in line 406 is essential.  Mere
topological properness of a path in the interior is not a substitute.

## 3. Fixed notation and hypotheses

Write

\[
 m=\operatorname{depth}P=(n-1)q+1,
 \qquad
 \operatorname{depth}Q=m+q=nq+1.
\]

Let

\[
 K_P=P\cap K(f),\qquad K_Q=Q\cap K(f).
\]

Let \(P_j\) be a component of \(P\setminus K_P\), and let \(Q_i\) be the
unique source component carried into \(P_j\).  Uniqueness here is already
proved in Step 1 of the conditional tile-gluing criterion: the dynamical
homeomorphism \(g:Q\to P\) shows that the source and target component sets
have the same finite cardinality, while KL's inclusion component map is
surjective, hence bijective.  This component bijection does not prove
same-tile injectivity or global pseudo-piece embedding.

Denote the associated tiles by

\[
 \widehat A_{s,i}\subset\mathbf Q,\qquad
 \widehat A_{t,j}\subset\mathbf P.
\]

Let

\[
 \Omega=\boldsymbol\iota(\mathbf Q)\subset\mathbf P.
\]

The analysis uses three facts that must not be conflated.

1. \(\boldsymbol\iota\) is an interior immersion.  In a general abstract
   \(\psi\)-ql scope, injectivity requires separate proof; for the full
   canonical primitive localization it is proved false.
2. Its extension to the named KL boundary is continuous.
3. The extension is not asserted to map the entire source ideal boundary
   into the target ideal boundary.

The third fact allows the source \(O\)-side to map into the target
interior.  It does not prove that its actual image is an embedded
crosscut.  The crosscut \(\sigma_i\) is obtained only in the `(CI)` model
below.  For the full canonical image, the required access geometry must be
computed with the coset/sheet state (1.1), not by assuming embeddedness.

## 4. Conditional lower-strip normal form and the general no-go

The positive strip computation uses the following extra hypothesis.

> **`(CI)` Common-coordinate inclusion.**  The source and target tile
> annuli are literal nested annuli
> \[
> A_s=U^{m+q}\setminus K(f)\subset
> A_t=U^m\setminus K(f)
> \]
> in one external coordinate, and the tile map is the lift of this set
> inclusion.  The round-annulus coordinates on \(A_s,A_t\) are
> restrictions of that one coordinate.  In addition, the lifted inclusion
> reflects the declared central overlap:
> \[
> L_i^{-1}\!\left(\widetilde e_{j(i)}(P_{j(i)})\right)=e_i(Q_i)
> \]
> for every tile.

This is a valid model hypothesis and a positive control.  It is stronger
than the source-locked KL statement that the tile map is a degree-one
holomorphic immersion whose declared overlap square commutes.

### Theorem 4.1: common-coordinate model

Assume `(CI)`.

For every source tile \(i\) and its target tile \(j=j(i)\), there are
compatible strip coordinates

\[
 \widehat A_{s,i}\cong
 \Pi(h_s)=\{z:0<\operatorname{Im}z<h_s\},
\]

\[
 \widehat A_{t,j}\cong
 \Pi(h_t)=\{z:0<\operatorname{Im}z<h_t\},
\]

with

\[
 0<h_s<h_t,\qquad
 h_s=2^{-q}h_t,
\]

in which the lift of the inclusion is

\[
 L_i(z)=z+\theta_i,\qquad \theta_i\in\mathbb R.
\]

Consequently,

\[
 L_i\bigl(\Pi(h_s)\bigr)
 =
 \{z:0<\operatorname{Im}z<h_s\}
+\theta_i.
\tag{4.1}
\]

The source \(O\)-side is the upper ideal side
\(\mathbb R+ih_s\); its immersed image is the horizontal internal
crosscut

\[
 \sigma_i
 =
 \mathbb R+\theta_i+ih_s
 \subset \widehat A_{t,j}.
\tag{4.2}
\]

The two ends of \(\sigma_i\) are the two distinct wrapping prime ends
\(p_i^-,p_i^+\) at which the target \(O\)-arc
\(\lambda_{t,j}\) meets the two target \(J\)-arcs.

### Proof

By `(CI)`, the annuli underlying the two tiles are

\[
 A_t=U^m\setminus K(f),\qquad
 A_s=U^{m+q}\setminus K(f)\subset A_t.
\]

The external coordinate used to define rays and equipotentials
uniformizes these nested annuli compatibly by round annuli.  With the
normalization of `moduli.tex`, their universal covers are horizontal
strips whose heights are proportional to

\[
 2^{-m}\mu
 \quad\text{and}\quad
 2^{-(m+q)}\mu,
\]

respectively.  Therefore

\[
 h_s=2^{-q}h_t<h_t.
\]

Both deck groups are generated by \(T(z)=z+1\).  The physical inclusion
\(A_s\hookrightarrow A_t\) induces \(+1\) on the positively oriented
winding generator.  A compatible lift consequently commutes with \(T\).
In the common logarithmic coordinate the physical map is the identity,
so two lifts differ only by a real deck phase.  This gives
\(L_i(z)=z+\theta_i\) and proves (4.1).

The top boundary of \(\Pi(h_s)\) is the lift of the deeper
equipotential, hence is the source \(O\)-side.  Since \(h_s<h_t\), its
image is the internal line (4.2).  A sequence on that line with
\(\operatorname{Re}z\to\pm\infty\) leaves every compact subset of the
target tile.  In the KL ideal compactification these are exactly the two
wrapping ends at which \(\lambda_{t,j}\) meets its adjacent
\(\xi\)- and \(\eta\)-arcs.  They are distinct ends of the universal
covering strip.  Thus (4.2) is a proper internal crosscut with endpoints
\(p_i^-,p_i^+\).  \(\square\)

### Audit

The proof does not infer the strip form from the word “immersion.”  It
uses the additional hypothesis `(CI)`, namely:

- the common external coordinate;
- the exact depth difference \(q\);
- the induced degree \(+1\) on the annular fundamental group; and
- the based deck phase \(\theta_i\).

Changing the phase translates the picture horizontally and changes none
of the conclusions.

### Proposition 4.2: degree-one immersion does not imply a lower strip

Fix \(0<h_s<h_t\).  For all sufficiently small nonzero real
\(\varepsilon\), the map

\[
 L_\varepsilon(z)=z+\varepsilon\sin(2\pi z)
\tag{4.3}
\]

is a \(\mathbb Z\)-equivariant holomorphic embedding
\(\Pi(h_s)\to\Pi(h_t)\), carries the lower boundary to the lower boundary,
and descends to a degree-one annulus embedding.  Nevertheless its upper
boundary is not horizontal and its image is not the lower substrip.

### Proof

The identity

\[
 L_\varepsilon(z+1)=L_\varepsilon(z)+1
\]

gives \(\mathbb Z\)-equivariance and degree one on the annular quotient.
On the closed strip,

\[
 |L_\varepsilon'(z)-1|
 \le 2\pi|\varepsilon|\cosh(2\pi h_s).
\]

Choose \(\varepsilon\ne0\) so that the right-hand side is \(<1\).  Since
the strip is convex, integration along the straight segment from \(w\)
to \(z\) gives

\[
 |L_\varepsilon(z)-L_\varepsilon(w)|
 \ge
 \bigl(1-2\pi|\varepsilon|\cosh(2\pi h_s)\bigr)|z-w|,
\]

so \(L_\varepsilon\) is injective and locally univalent.  Moreover
\(\mathbb Z\)-equivariance and lift injectivity give quotient
injectivity: if
\([L_\varepsilon(z)]=[L_\varepsilon(w)]\), then for some
\(k\in\mathbb Z\),
\[
 L_\varepsilon(z)=L_\varepsilon(w)+k=L_\varepsilon(w+k),
\]
so \(z=w+k\) and \([z]=[w]\).  Thus the descended degree-one annulus map
is an embedding.  Moreover

\[
 \operatorname{Im}L_\varepsilon(x+iy)
 =
 y+\varepsilon\cos(2\pi x)\sinh(2\pi y).
\tag{4.4}
\]

Choose \(|\varepsilon|\) still smaller so that

\[
 |\varepsilon|<
 \min\left\{
 \frac{h_s}{\sinh(2\pi h_s)},
 \frac{h_t-h_s}{\sinh(2\pi h_s)}
 \right\}.
\]

Because \(y/\sinh(2\pi y)\) decreases on \(0<y\le h_s\), (4.4) lies
strictly between \(0\) and \(h_t\) for \(0<y<h_s\).  On \(y=0\),
\(L_\varepsilon(x)\in\mathbb R\).  On \(y=h_s\), however,

\[
 \operatorname{Im}L_\varepsilon(x+ih_s)
 =
 h_s+\varepsilon\cos(2\pi x)\sinh(2\pi h_s),
\]

which is nonconstant.  Thus the image is not a horizontal lower strip.
\(\square\)

This counterexample satisfies more than the general source hypotheses:
it is globally univalent.  Hence injectivity of the fixed pseudo-piece
immersion does not repair the missing common-coordinate premise.

## 5. Conditional cap isolation in the common-coordinate model

Sections 5--8 assume `(CI)`.  Under `(CI)`, every tile map is a literal
lift of an inclusion and is therefore injective.  The stronger full
overlap-reflection condition is also an explicit part of `(CI)` because
the cap and footprint calculation uses exact target-overlap saturation,
not because interior gluing injectivity requires it.  Together with the
source-locked central injectivity and component bijection, corrected Proposition 4.1
of `direct_decoration_path_lifted_collar_certificate.md` makes the glued
pseudo-piece map an embedding.  None of these geometric conclusions is
asserted for the general KL tile immersion.

Define the closed-on-the-lower-side cap

\[
 C_i^O
 =
 \left\{
   z\in\widehat A_{t,j}:
   h_s\leq\operatorname{Im}z<h_t
 \right\}.
\tag{5.1}
\]

The lower boundary of this set in the target surface is
\(\sigma_i\).  Its upper side is ideal and corresponds to the target
\(O\)-arc.

### Lemma 5.1

The tile images \(\widehat A_{t,j}\) are exactly the connected components
of

\[
 \mathbf P\setminus K_P.
\tag{5.2}
\]

### Proof

The glued presentation gives

\[
 \mathbf P
 =
 P\sqcup_{e_j}\widehat A_{t,j}.
\]

The central complement decomposes as

\[
 P\setminus K_P=\bigsqcup_j P_j,
\]

and the \(j\)-th tile overlaps the central copy exactly in \(P_j\).
Hence, after removing \(K_P\), every central point already lies in one
tile.  KL prove that distinct tile images are disjoint.  Each tile is
connected.  This proves (5.2).  \(\square\)

### Lemma 5.2

For every target tile \(j\), the intersection of \(\Omega\) with that
tile contains the complete lower strip

\[
 \{0<\operatorname{Im}z<h_s\}.
\tag{5.3}
\]

For the fixed degree-one pair it is exactly the image of the unique source
tile assigned to \(j\), away from \(K_Q\).

### Proof

The fixed-pair component map is bijective, so there is exactly one source
tile \(i\) over \(j\).  Theorem 4.1 identifies its image with the complete
lower strip.  Any point of the central copy \(Q\setminus K_Q\) is already
identified with a point of its source tile, so it creates no additional
sheet.  \(\square\)

### Theorem 5.3

\(C_i^O\) is the connected component of
\(\mathbf P\setminus\Omega\) adjacent to the immersed source
\(O\)-side \(\sigma_i\).

### Proof

The set (5.1) is connected and is disjoint from the open lower strip
(5.3).  The line \(\sigma_i\) is not in \(\Omega\), because it is the
image of the source ideal side under the continuous ideal extension of
an embedding.  Explicitly, if
\(\overline{\boldsymbol\iota}(p)=\boldsymbol\iota(u)\in\Omega\) for a
source prime end \(p\), choose interior \(z_n\to p\).  Then
\(\boldsymbol\iota(z_n)\to\boldsymbol\iota(u)\), and continuity of the
inverse on \(\Omega\) gives \(z_n\to u\), contradicting uniqueness of
limits in the Hausdorff source ideal closure.  Thus

\[
 C_i^O\subset\mathbf P\setminus\Omega.
\]

The Green/equipotential height defines a continuous function

\[
 G:\mathbf P\longrightarrow[0,\infty)
\]

which is positive on
\(\mathbf P\setminus K_P\), is proportional to
\(\operatorname{Im}z\) in every strip tile, and vanishes on \(K_P\).
By Lemma 5.2,

\[
 (\mathbf P\setminus\Omega)\cap G^{-1}((0,h_s))=\varnothing.
\tag{5.4}
\]

Let \(D\) be a connected subset of
\(\mathbf P\setminus\Omega\) that meets \(C_i^O\).  If \(D\) contains a
point of \(K_P\), then the connected set \(G(D)\subset\mathbb R\)
contains \(0\) and a value at least \(h_s\).  It must therefore meet
\((0,h_s)\), contradicting (5.4).

Hence \(D\subset\mathbf P\setminus K_P\).  Lemma 5.1 says that the target
tiles are the connected components of this open set, so \(D\) lies in
the single target tile \(j\).  Inside that tile, Lemma 5.2 and the strip
normal form show that the complement is exactly
\(\{\operatorname{Im}z\ge h_s\}=C_i^O\).  Thus \(D\subset C_i^O\).

Every connected subset of the complement meeting \(C_i^O\) is contained
in \(C_i^O\), while \(C_i^O\) itself is connected.  Therefore it is the
complete connected component, not merely the path component.
\(\square\)

### Central-overlap adversarial check

The proof explicitly addresses the apparent bypass through the central
overlap \(P_j\).  The overlap is not a second copy or a new sheet: it is
already a subset of the target tile.  More importantly, the argument uses
connected images under \(G\), not path-connectedness of a possibly wild
closed complement.  Any connected attachment to another tile must reach
\(G=0\) and hence would force forbidden intermediate height.  Tile
bijection is needed; without it, a target tile lacking its source lower
strip could provide a genuine bypass.

## 6. Conditional accessible footprint

Let \(\overline{\lambda}_{t,j}\) denote the target \(O\)-arc together
with its two wrapping endpoints \(p_i^-,p_i^+\).

For
\(p\in\operatorname{relint}\lambda_{s,i}\), let
\(\sigma(p)=\overline{\boldsymbol\iota}(p)\in\sigma_i\).  Define the
pointwise full complement-access footprint

\[
 \Phi_O(p)
 =
 \left\{
 x\in\partial_i\mathbf P:
 \begin{array}{l}
 \text{there is \(a:[0,1]\to\widehat{\mathbf P}\) with}\\
 \text{\(a(0)=x,\ a(1)=\sigma(p)\), and
       \(a((0,1))\subset\mathbf P\setminus\Omega\)}
 \end{array}
 \right\}.
\tag{6.1}
\]

This is the same pointwise footprint used in the abstract embedded-disk
theorem; it is not defined by first restricting paths to the cap.  Define
also the aggregate footprint

\[
 \Phi_O(i)
 =
 \bigcup_{p\in\operatorname{relint}\lambda_{s,i}}\Phi_O(p).
\tag{6.2}
\]

### Theorem 6.1

\[
 \boxed{
 \Phi_O(p)=\overline{\lambda}_{t,j}
 \quad\text{for every }
 p\in\operatorname{relint}\lambda_{s,i},
 \qquad
 \Phi_O(i)=\overline{\lambda}_{t,j}.
 }
\tag{6.3}
\]

### Proof

Fix \(p\) and its finite lower-side coordinate
\(\sigma(p)=x_p+ih_s\).  For any finite point \(y+ih_t\) of the top
ideal side, a polygonal arc that first enters
\(h_s<\operatorname{Im}z<h_t\) and then tends to \(y+ih_t\) stays in
the cap.  Curves that first enter the cap and then satisfy
\(\operatorname{Re}z\to-\infty\) or
\(\operatorname{Re}z\to+\infty\) reach the two wrapping corners.
Thus every point of the closed target \(O\)-port is accessible from this
fixed \(\sigma(p)\), and

\[
 \overline{\lambda}_{t,j}\subset\Phi_O(p).
\]

Conversely, let \(a\) be any path in the definition of \(\Phi_O(p)\).
Its connected open image lies in one component of
\(\mathbf P\setminus\Omega\).  Near the endpoint \(\sigma(p)\), the strip
normal form and occupation of the lower strip force that image to meet
\(C_i^O\).  Theorem 5.3 therefore confines it to \(C_i^O\).  The closure
\(\overline{C_i^O}^{\,\widehat{\mathbf P}}\) meets the target ideal
boundary only in the upper target \(O\)-side and the two strip ends.
Therefore

\[
 \Phi_O(p)\subset\overline{\lambda}_{t,j}.
\]

This proves the pointwise equality.  Taking the union over \(p\) proves
the aggregate equality.  \(\square\)

The closure bars in (6.3) are not cosmetic.  They determine the KKL
endpoint obstruction below.

## 7. Conditional open-\(O\)-interval pullback obstruction

Let

\[
 E\Subset\operatorname{relint}\lambda_{s,i}
\]

be a nondegenerate open source subarc.  Under the boundary extension of
\(\boldsymbol\iota\), it is represented by an open finite subinterval of
\(\sigma_i\).

### Theorem 7.1

No connected candidate for the KKL pullback of the **open** target
interval \(\lambda_{t,j}\) can contain \(E\).  Equivalently,

\[
 E\not\subset\boldsymbol\iota^*(\lambda_{t,j})
\tag{7.1}
\]

whenever the maximal KKL pullback is defined.

### Proof

Choose two finite strip coordinates \(x_1<x_2\) in \(E\).  In the source
lower strip choose a simple crosscut \(\delta\) with ideal endpoints

\[
 x_1+ih_s,\qquad x_2+ih_s,
\]

lying in an arbitrarily thin collar below
\(\operatorname{Im}z=h_s\).  Its source proper-homotopy class is
subordinate to \(E\).

In the target cap, attach two disjoint tails:

1. a tail from \(x_1+\theta_i+ih_s\) tending to the wrapping corner
   \(p_i^-\); and
2. a tail from \(x_2+\theta_i+ih_s\) tending to a point
   \(y\in\operatorname{relint}\lambda_{t,j}\).

The tails can be chosen simple and disjoint in the horizontal strip cap.
Together with \(\boldsymbol\iota(\delta)\), they form a simple target
proper crosscut

\[
 \gamma:(0,1)\longrightarrow\mathbf P
\]

with target ideal endpoints \(p_i^-\) and \(y\).

The two tails lie in \(C_i^O\), and the middle crosscut lies in
\(\Omega\).  Therefore

\[
 \gamma\cap\Omega=\boldsymbol\iota(\delta).
\tag{7.2}
\]

Because \(\boldsymbol\iota\) is an embedding, (7.2) gives exactly one
source proper path in
\(\boldsymbol\iota^*\gamma\), namely \(\delta\).  It is subordinate to
\(E\).

On the other hand, \(\gamma\) is not subordinate to the open target
interval \(\lambda_{t,j}\).  Its endpoint \(p_i^-\) is not in that open
interval.  There is a neighborhood of \(\lambda_{t,j}\) in the ideal
compactification that omits \(p_i^-\), and a homotopy relative to ideal
endpoints cannot move that endpoint.

Thus \(\gamma\) violates the defining KKL implication for every candidate
source subset containing \(E\).  This proves (7.1).  \(\square\)

### Corollary 7.2: necessary footprint containment

Let \(X\subset\partial_i\mathbf P\) be a connected target ideal set.  If
one nondegenerate source \(O\)-subarc \(E\) is admissible for \(X\)
(equivalently, \(E\subset\boldsymbol\iota^*X\) whenever that maximum
exists), then necessarily

\[
 \overline{\lambda}_{t,j}\subset X.
\tag{7.3}
\]

### Proof

For any
\(\zeta\in\overline{\lambda}_{t,j}\), repeat the construction in
Theorem 7.1 with one cap tail ending at \(\zeta\).  If
\(\zeta\notin X\), choose an ideal neighborhood of \(X\) omitting
\(\zeta\).  The resulting target crosscut has one source proper lift
subordinate to the chosen source \(O\)-subarc but is not subordinate to
\(X\).  Hence admissibility forces every
\(\zeta\in\overline{\lambda}_{t,j}\) into \(X\).  \(\square\)

Corollary 7.2 by itself proves necessity only.  Sufficiency is established
later, in Theorem 9.3, using the conformal ideal-boundary identification
and the all-component properness theorem.

## 8. Conditional forced local marking enlargement

In the native KL tiling, the open \(O\)-arc
\(\lambda_{t,j}\) is adjacent at its two endpoints to one
\(\xi\)-arc and one \(\eta\)-arc.  A KKL multi-interval is a connected
open ideal set assembled from whole marking intervals and permitted
endpoints.  In this section the symbols
\(\lambda_{t,j},\xi_{t,j},\eta_{t,j}\) denote the relative interiors of
the corresponding named arcs; their endpoints are written separately.

### Proposition 8.1

Any native-KL multi-interval containing
\(\overline{\lambda}_{t,j}\) contains:

1. \(\lambda_{t,j}\);
2. both endpoints of \(\lambda_{t,j}\); and
3. both adjacent \(J\)-intervals.

Thus its native combinatorial length is at least three, apart from a
degenerate whole-boundary identification.

Equivalently, if \(v_{j-1},v_j\) are the two neighboring Julia vertices,
the unique local three-atom candidate is the open circular interval

\[
 I^\star_{t,j}
 =
 (v_{j-1},v_j)_{\lambda_{t,j}}
 =
 \xi_{t,j}\cup\{p_j^-\}\cup\lambda_{t,j}
 \cup\{p_j^+\}\cup\eta_{t,j}.
\tag{8.1}
\]

The notation \((v_{j-1},v_j)_{\lambda_{t,j}}\) specifies the component
containing \(\lambda_{t,j}\) and excludes the two far vertices.  Hence
\(I^\star_{t,j}\) is open.

### Proof

Containment of the closed port gives the first two assertions.  At either
endpoint, openness in the ideal boundary requires a two-sided
neighborhood.  One side lies in the \(O\)-arc and the other in the
adjacent \(J\)-arc.  Since a multi-interval is assembled from complete
marking intervals rather than arbitrary proper subarcs, it must contain
the entire adjacent \(J\)-interval at each endpoint.  \(\square\)

This is a period-independent local forcing statement.  It does not bound
how much farther a valid action marking may have to enlarge after the
central seam is audited.

## 9. Conformal ideal boundary and the conditional outer-port pullback

### Theorem 9.1: conformal ideal-boundary identification

Each of the two audited direct-decoration pseudo-pieces
\(\mathbf P,\mathbf Q_a\) is a hyperbolic conformal disk.  Its named
\(\lambda,\xi,\eta\) ideal boundary is its conformal ideal circle.  For
their puzzle inclusion, the KL boundary extension is a continuous
extension between the two conformal ideal closures.

### Proof

The physical puzzle pieces are closed Jordan domains
(`kingdom.tex`, lines 28, 32, and 273--278), so the closed central copy
cannot simply be called an open member of a van Kampen cover.  Put
\(U_0=\operatorname{int}Y\) and let \(T_i\) be the open image of the
\(i\)-th universal-cover tile.  These sets cover \(\mathbf Y\):
`kingdom.tex`, lines 56--62, says that \(K_Y\) meets
\(\partial Y\) only at the vertices, and `psiql.tex`, lines 139--144,
puts every vertex in \(S_Y\), hence outside the path surface; every other
central-boundary point lies in some \(Y_i\) and therefore in \(T_i\) by
lines 146--160.

Distinct \(T_i\) are disjoint, and
\(U_0\cap T_i=\operatorname{int}Y\cap Y_i\) is path-connected.  Indeed,
join two of its points by a path in the source-locked simply connected
set \(Y_i\).  Because \(Y_i\) is relatively open in \(Y\), the compact
path image has positive distance from \(Y\setminus Y_i\).  A sufficiently
small Schoenflies-collar isotopy, fixed at the two interior endpoints,
pushes every boundary contact into \(\operatorname{int}Y\) while staying
in \(Y_i\).  Thus
\(\{U_0,T_i\}\) is a finite open cover with star nerve, simply connected
vertex spaces, and path-connected nonempty intersections.  Repeated
van Kampen gives

\[
 \pi_1(\mathbf Y)=0.
\tag{9.1}
\]

The surface is noncompact: if it were compact, the nonconstant open
projection \(\pi_Y\) would have compact, hence closed, image in the
connected target; its image would then be the whole target, contradicting
the omitted nonempty set \(S_Y\).  The bold domain \(\mathbf U^m\) is a
noncompact simply connected disk, hence uniformizes as \(\mathbb D\) or
\(\mathbb C\).  The pseudo-piece projection
\(\pi_Y:\mathbf Y\to\mathbf U^m\) is a nonconstant holomorphic immersion
(`psiql.tex`, lines 107--112), and its image omits \(S_Y\) by the path
definition in lines 97--107.

If \(\mathbf U^m\cong\mathbb D\), a hypothetical
\(\mathbf Y\cong\mathbb C\) would give a bounded nonconstant entire map,
contradicting Liouville.  If
\(\mathbf U^m\cong\mathbb C\), the same hypothetical entire map omits at
least two values.  Indeed, `psiql.tex`, lines 139--144, puts every point
of \(\partial Y\cap K(f)\) in \(S_Y\);
`kingdom.tex`, lines 116--118, gives \(P\) exactly \(2^n\ge2\) distinct
vertices; and the fixed univalent branch carries the corresponding
distinct vertex set to \(Q_a\).  Little Picard is then a contradiction.
The sphere is excluded by noncompactness.  Hence, for
\(\mathbf Y\in\{\mathbf P,\mathbf Q_a\}\),

\[
 \mathbf Y\cong\mathbb D.
\tag{9.2}
\]

Kahn I, `wad.tex`, lines 169--175, defines the ideal closure of a
hyperbolic surface by its disk uniformization, deck group, and limit set.
In (9.2) the deck group is trivial and the limit set is empty, so Kahn's
ideal closure is \(\overline{\mathbb D}\).  KL II explicitly refers to
Kahn I for the detailed framework; `psiql.tex`, lines 231--244, calls the
named arcs a tiling of *the ideal boundary*, not of a second
compactification.  Lines 248--253 state that the inclusion immersion
extends continuously to that boundary.  This proves the assertion.
\(\square\)

No physical Julia boundary is identified with a locally connected curve
in this proof.  The \(\xi,\eta\) sides are abstract conformal accesses.

### Theorem 9.2: component properness conditional on embedding

Assume that \(\boldsymbol\iota\) is globally injective.

Let \(\gamma:(0,1)\to\mathbf P\) be a target proper path and let
\(A\) be a component of \(\gamma^{-1}(\Omega)\).  Then

\[
 \beta=\boldsymbol\iota^{-1}\circ\gamma|_A
\]

extends continuously to two points of
\(\partial_i\mathbf Q\).  Thus every nontrivial parameter component of
the target-path intersection is a KKL proper source path.

### Proof

For compact \(K\Subset\mathbf Q\),

\[
 \beta^{-1}(K)
 =
 A\cap\gamma^{-1}(\boldsymbol\iota(K))
\]

is compact in \(A\).  Indeed,
\(\boldsymbol\iota(K)\Subset\mathbf P\), target properness keeps its
preimage away from \(0,1\), and a finite endpoint of \(A\) mapping into
\(\boldsymbol\iota(K)\subset\Omega\) would lie in the same open parameter
component as nearby points of \(A\).  Hence \(\beta\) is topologically
proper.

At either end of \(A\), the intersection of the nested closures of the
source tail images is a nonempty compact connected subset of
\(\partial_i\mathbf Q\).  Theorem 9.1 and continuity of \(\gamma\) place
it in one boundary fiber of the closed-disk extension of
\(\boldsymbol\iota\).

Every connected subset of such a fiber is a point.  To verify this, use
disk uniformizations and write the embedding as a bounded nonconstant
holomorphic map \(F:\mathbb D\to\mathbb D\), continuous on the closed
disk.  If a boundary fiber contained a nondegenerate connected set, it
would contain a circular arc \(J\), and \(H=F-w\) would vanish
continuously on \(J\).  After a disk automorphism assume \(H(0)\ne0\).
With \(M=\max(1,\|H\|_\infty)\) and
\(u_r=\log M-\log|H(re^{it})|\), Jensen's formula uniformly bounds
\(\int u_r\), while \(u_r\to+\infty\) on the positive-measure arc
\(J\).  Fatou's lemma is a contradiction.  Hence the endpoint cluster
set is a singleton.  Compactness upgrades the unique cluster point to a
limit.  Apply the argument at both ends.  \(\square\)

Theorem 9.2 is the missing implication that topological properness alone
did not provide.  It remains valid for an independently embedded retained
collar or revised localization.  It cannot be applied to the full
canonical KL pair, whose tile maps are noninjective.

### Theorem 9.3: conditional exact outer-port criterion

Assume `(CI)`.

Let \(I\subset\partial_i\mathbf P\) be connected.  Then

\[
 \boxed{
 \operatorname{relint}\lambda_{s,i}
 \subset\boldsymbol\iota^*I
 \quad\Longleftrightarrow\quad
 \overline{\lambda}_{t,j(i)}\subset I.
 }
\tag{9.3}
\]

In particular,

\[
 \operatorname{relint}\lambda_{s,i}
 \cap\boldsymbol\iota^*(\lambda_{t,j(i)})=\varnothing
\tag{9.4}
\]

for the open target \(O\)-atom, while

\[
 \operatorname{relint}\lambda_{s,i}
 \subset\boldsymbol\iota^*I^\star_{t,j(i)}
\tag{9.5}
\]

for the three-atom open tile-star of Proposition 8.1.

### Proof

For a source prime end \(p\), let \(\Phi(p)\) be the set of target ideal
ends accessible from \(\overline{\boldsymbol\iota}(p)\) through
\(\mathbf P\setminus\Omega\); if the boundary image of \(p\) is already
ideal, set \(\Phi(p)\) equal to that singleton.  The embedded-disk
accessible-footprint theorem, whose component-properness input is
Theorem 9.2, proves

\[
 \boldsymbol\iota^*I
 =
 \{p\in\partial_i\mathbf Q:\Phi(p)\subset I\}.
\tag{9.6}
\]

The proof of (9.6) audits repeated target traversals: if a target proper
path has a unique source restriction, all its intersection components
are proper by Theorem 9.2; infinitely many copies of the same source path
would accumulate at an interior target point, contradicting openness of
\(\Omega\).  The first and last complement tails therefore put the two
target endpoints in the footprints of the source endpoints.  Conversely,
any \(\xi\in\Phi(p)\) is realized by a source hairpin at \(p\), joined to
\(\xi\) by one complement access traversed in both directions.  KKL paths
need not be simple, so no local perturbability of the complement is
assumed.

For every
\(p\in\operatorname{relint}\lambda_{s,i}\), the pointwise statement of
Theorem 6.1 gives

\[
 \Phi(p)=\overline{\lambda}_{t,j(i)}.
\]

Substitution in (9.6) proves (9.3).  Equations (9.4) and (9.5) follow
because the open \(O\)-atom omits both wrapping corners while the
tile-star contains the full closed port.  \(\square\)

## 10. Remaining actual-immersion footprint record

The named/conformal ideal-boundary identification and continuous boundary
extension are closed.  The embedded-disk route cannot be applied to the
full canonical map: the forced-collision theorem supplies a non-base class
in \(a_*^{-1}(H_t)/H_s\) and an actual point collision.  The corrected
relative-cartesian gluing theorem remains true conditionally, but its full
tile-injectivity premise is false here.  The stronger
`DIRECT_DECORATION_TILE_CENTRAL_OVERLAP_REFLECTION` question may still
arise inside a retained-collar footprint computation if exact
central-image saturation is used; it cannot repair the full canonical
collision.

The later
`KAHN_ITERATE_COMPLEMENTARY_COMPONENT_ALIGNMENT` theorem removes one
interior ambiguity.  The full complementary equalizer is connected, its
surjective \(q/e\) base change has a connected resolved intermediate, and
the same fixed seed supplies KL's \(\mathbf U^m\)-tower.  Moreover, the
annular degree-\(+1\) inclusion pulls, for every source index \(i\), its
target universal-cover tile \(j_\iota(i)\) back to the connected source
tile.  Given a whole-annulus \(q/e\) factorization of that base map,
compatible lifted basepoints fix the interior deck phase and base change
constructs a connected resolved intermediate.  This last statement is
conditional on the factorization being the actual KL base map; it does
not identify the canonical infinite sheet-resolution factor with that
whole KL tile.  Distinct source indices over one target remain distinct;
the dynamical and inclusion component maps are not identified.

The subsequent
`RESOLVED_INTERMEDIATE_RELATIVE_IDEAL_BOUNDARY` theorem now proves that a
full factorwise prime-end compactification is generally the wrong object.
The tile map
\[
q_{r,i}:\mathcal E_{r,i}\to\mathcal R_{r,i}
\]
is a universal cover.  If its deck group is nontrivial, the map cannot
extend through a deck-limit point to any Hausdorff completion.  Kahn's and
KKL's ideal boundaries accordingly remove the deck limit set.

KL's source makes the application sharper: the two wrapping points
\(\omega_\pm\) of an actual tile are named boundary vertices, and the
actual composite tile map \(L_a\) extends continuously there.  The based
source-cover biholomorphism transports them to resolved-source points
\(\zeta_\pm\), and
\(K_a=L_a\Phi_a^{-1}=e_aq_a\).  Therefore every whole-tile
covering/embedding factorization of that actual map is one-sheeted.  The
canonical infinite resolved cover and the actual KL tile cannot be the
same factorization.

The subsequent
`CANONICAL_KL_WHOLE_TILE_CORRESPONDENCE_NO_GO` theorem closes the complete
map-level option: no based source-cover biholomorphism preserving the
annular deck generator, injective target comparison, composite square,
and named wrapping-end transport can identify the canonical infinite
factorization with the whole actual tile.  A deck orbit converging to a
wrapping end would make the source-locked KL boundary value equal to every
interior composite value.

For every supplied fixed labeled same-source datum,
`CANONICAL_KL_RESTRICTED_INTERFACE_CLASSIFICATION` now constructs the
non-covering relation span and the tagged étale family of all maximal
parameter-compatible interior lifts.  It retains source labels, resolved traces,
sheets, and deck phases, and it proves that the two transported wrapping
values are common fiber-orbit clusters.  It does not construct such
alignment at every Wave stage or classify a restriction at an actual
ideal endpoint.

The later geometric-trace audit proves that every maximal parametrized
lift on a supplied full KL pseudo-piece is a proper source path with exact
endpoint naturality.  It also proves that parametrized lifts do not
exhaust KKL's geometric inverse-trace restrictions and that a single
immersion can have infinitely many competing proper restrictions.

What remains first is therefore the **Wave proof-use ledger**, followed
by actual glued stage alignment and geometric inverse-trace proper-path
and whole-end-interval classification.  Only then can one construct the
uniform relation response and augment the canonical side by the relative boundary
state
\[
(\Gamma_{r,i},\Lambda_{r,i},\Omega_{r,i},
  \operatorname{corr}_{r,i},\operatorname{phase}^{\rm int}_{r,i}),
\]
where \(\operatorname{corr}_{r,i}\) is the constructed parametrized
interior relation for a supplied aligned datum.  Its full geometric
restriction space, proper source paths, pulled marking, and map
properness on complete end-intervals remain open on the actual Wave
horizon.  Factorwise descent
on the canonical side may be
constructed only on proved invariant subsets of
\(\Omega_{r,i}=\partial\mathbb D\setminus\Lambda_{r,i}\).  Every actual
limit-set contact must be retained as a cluster/defect record.  KL's
boundary extension does not supply the canonical-to-KL comparison map.
Therefore the records below are post-correspondence data, not objects
already constructed on the resolved interior.

The full-map replacement must therefore be a sheet-sensitive immersion
theorem.  For
\(\mathfrak s\in\mathscr S_{\rm loc}\), the first footprint record is

\[
 \mathfrak F_O(p,\mathfrak s)
 =
 \left(
   \mathfrak s,
   \overline{\boldsymbol\iota}(p),
   \{(C,\mathfrak s):C\text{ is a component of }
          \mathbf P\setminus\Omega
          \text{ landing at }\overline{\boldsymbol\iota}(p)\},
   \Phi(p,\mathfrak s)
 \right),
 \qquad
 p\in\operatorname{relint}\lambda_{s,i}.
\tag{10.1}
\]

For a separately embedded retained collar, pointwise equality
\(\Phi(p)=\overline{\lambda}_{t,j(i)}\) allows one to invoke the abstract
embedded-disk safe-set formula directly.  Theorem 9.3 itself may be
invoked only if the full `(CI)` hypothesis is independently established.
Neither statement applies to the full canonical map without the
sheet-sensitive replacement.  The analogous source \(J\)-side record, for

\[
 p\in\operatorname{relint}\xi_{s,i}
 \ \cup\
 \operatorname{relint}\eta_{s,i},
\]

the required record is

\[
 \mathfrak F_J(p,\mathfrak s)
 =
 \left(
   \mathfrak s,
   \overline{\boldsymbol\iota}(p),
   \{(C,\mathfrak s):C\text{ is a component of }
          \mathbf P\setminus\Omega
          \text{ landing at }\overline{\boldsymbol\iota}(p)\},
   \Phi(p,\mathfrak s)
 \right).
\tag{10.2}
\]

Each component entry must retain

\[
 (\text{central component},\text{tile side},\text{wrapping or vertex
 access},\text{target ideal footprint},\text{sheet},
 \text{localization coset},\text{return word}).
\tag{10.3}
\]

Here \(\mathfrak s\) is a label in the based fiber of the canonical
covering \(q:\widehat X_s\to P_K\); transport away from the basepoint is
given by the full monodromy groupoid.  It is not a global group element.
Because the based fiber is infinite, any finite state used later must be
a proved future-faithful compactification or sufficient quotient,
preserving every proof-used proper-path, access, and Value observable.

The exact next source-specific task is:

> **Restricted canonical-resolution/KL-tile correspondence and sheet-sensitive actual
> \(O\)-/\(J\)-footprint exhaustion.**
> Construct an authorized restricted comparison between the canonical
> equalizer resolution and the KL tile.  Locate whether the valid
> comparison is a proper interior/collar restriction, a non-covering
> immersion comparison, a different selected component, or a
> retimed/localization-revised interface.  It cannot be a nontrivial
> whole-tile covering/embedding factorization.
> On the canonical side, compute
> \(\Gamma_{r,i}=\operatorname{Deck}(q_{r,i})\), its limit set
> \(\Lambda_{r,i}\), and its domain of discontinuity
> \(\Omega_{r,i}\).  Prove the exact correspondence from its relative
> quotient to the named KL \(\lambda,\xi,\eta\) marking.
> On each proved invariant subset of \(\Omega_{r,i}\), construct the
> relative quotient, \(\overline q_{r,i}\),
> \(\overline e_{r,i}\), and the independently identified
> \(\lambda^R_{r,i}\), with exact deck-phase normalization and
> \[
>   \overline q_{r,i}(\lambda^Q_{r,i})=\lambda^R_{r,i},
>   \qquad
>   \overline e_{r,i}\overline q_{r,i}|_{\lambda^Q_{r,i}}
>   =
>   \overline L_{r,i}|_{\lambda^Q_{r,i}}.
> \]
> Every named point lying in \(\Lambda_{r,i}\) must instead be recorded as
> a complete deck-orbit/cluster defect; it cannot receive a point-valued
> factor map.
> Then start from the proved canonical collision and retain every class in
> \(\mathscr S_{\rm loc}=a_*^{-1}(H_t)/H_s\).  Enumerate the actual
> complement components landing on every source \(O\)-side on every sheet,
> and
> determine whether their full target footprints are the closed
> \(O\)-ports or larger sets.  Then enumerate the actual
> components of
> \(\mathbf P\setminus\boldsymbol\iota(\mathbf Q_a)\) landing on every
> nonproper source \(\xi_i,\eta_i\) portion on every coset; compute every
> complete target ideal footprint in (10.1)--(10.2); derive and prove a
> sheet-sensitive replacement for the embedded formula (9.6);
> and prove that the proof-used family of maximal pullbacks is pairwise
> disjoint, covering-refined, and proper or end-proper on every complete
> end-interval.  If instead a retained collar is used, record and charge
> every discarded coset and sheet.

The exact pullback formula also requires **sheet-isolated witnesses**.
For each proposed footprint access, construct a target proper hairpin
whose complete groupoid of KKL-proper source restrictions has exactly one
member on the declared sheet, or list every competing proper lift with
its coset and deck phase.  Conversely, prove that every target proper path
with one proper resolved restriction has target endpoints in the two
resolved endpoint footprints.  In addition, prove on the authorized ideal
compactifications that source subordination implies endpoint containment,
same-endpoint source hairpins are subordinate when that endpoint is
retained, and target subordination is equivalent to both target endpoints
lying in the target interval.  Only under these three hypothesis packages
is the safe-set proof valid sheetwise; without them, pointwise footprints
do not determine the KKL unique-lift predicate.

Finally, the subgroup equalities

\[
 K\cap\varphi^{-1}(H_s^+)=H_s,
 \qquad
 K^+=\varphi(K)H_s^+
\]

are necessary and sufficient only for bijectivity of the based coset map
under enlargement.  Even with trivial groups, a simply connected new
lobe can add a proof-used component or access.  Full final-root no-birth
therefore still requires a Cartesian cover square, component/path-fiber
bijection, obstacle and nonproper-bridge audit, and prime-end or direct
proper-path endpoint compatibility.

The finite label hull cannot discharge this task: equal
proper/nonproper labels need not have equal access footprints.  Nor may
one assume that a curve approaching a shared ideal vertex eventually
remains in one tile; it can alternate through adjacent sectors.

## 11. Adversarial audit

### 11.1 Hidden central bypass

Rejected by Theorem 5.3 **under `(CI)`**.  A route between tiles must
cross \(K_P\), and a route from the cap to \(K_P\) crosses the occupied
lower strip.  This is not an argument for a wavy or otherwise general
immersed tile boundary.

### 11.2 Shared wrapping endpoints

The two strip ends are ideal points, not points of the target surface.
They do not join two complement components through the interior.

### 11.3 Confusing an open port with its closure

Rejected by Theorem 7.1 and again by (9.6).  The explicit crosscut ending
at a wrapping corner distinguishes the two.

### 11.4 Treating footprint containment as merely necessary

Corrected.  Corollary 7.2 alone was only necessary.  Theorem 9.2 supplies
the missing all-component prime-end limits, and the full
accessible-footprint theorem makes containment necessary and sufficient.

### 11.5 Replacing KKL properness by escape from compacta

Not done.  Topological properness is only the first half of Theorem 9.2;
light boundary fibers force the two actual source prime-end limits
required by KKL.

### 11.6 Assuming a simple test path solves every path

The simple crosscut proves the negative open-port result.  The positive
universal implication instead uses Theorem 9.2, the finite
first/last-traversal argument, and the converse hairpin construction.

### 11.7 Using the finite label hull

Rejected.  The footprint contains endpoint information not present in a
proper/nonproper atom label.  Central-seam footprints must still be
computed geometrically.

### 11.8 Claiming a universal upper marking bound

Not made.  Under `(CI)`, Proposition 8.1 and (9.5) give a
period-independent local three-atom absorption.  They do not establish
that `(CI)` holds at a general KL stage or bound how far the final action
marking may enlarge after all \(J\)-seam footprints are included.

### 11.9 Eventual residence in one tile

Rejected.  Compactness of \(K_P\) does not prevent a proper curve from
approaching a shared ideal vertex through alternating central and tile
sectors.  Theorem 9.1 uses Kahn's conformal ideal-boundary definition,
not such an eventual-residence claim.

### 11.10 Replacing an annulus immersion by an inclusion

Rejected by Proposition 4.2.  The map
\(z+\varepsilon\sin(2\pi z)\) is already a globally univalent,
\(\mathbb Z\)-equivariant degree-one strip map, but its upper boundary is
wavy.  General KL naturality supplies an immersion, not `(CI)`.  Therefore
exact height, cap, and closed-port conclusions cannot be promoted without
an additional source theorem or a direct footprint computation.

### 11.11 Collapsing canonical localization sheets

Rejected.  The full canonical primitive stage has a proved non-base class
in \(a_*^{-1}(H_t)/H_s\).  Two distinct source sheets share a target point,
so a footprint indexed only by the target image or nominal boundary label
is incomplete even when the finite component labels agree.

### 11.12 Full prime-end extension of the resolved cover

Rejected by
`RESOLVED_INTERMEDIATE_RELATIVE_IDEAL_BOUNDARY`.  If
\(\gamma\ne1\) is a deck transformation and
\(\gamma^n z\to\zeta\) on the standalone prime-end circle, then
\[
 q_{r,i}(\gamma^n z)=q_{r,i}(z).
\]
Continuity at \(\zeta\) would make \(q_{r,i}\) constant.  An open
domain-of-discontinuity interval may still descend even when its omitted
endpoints lie in the limit set; actual incidence and quotient topology
must be proved.

### 11.13 Identifying the canonical infinite cover with the actual KL tile

Rejected by
`RESOLVED_INTERMEDIATE_RELATIVE_IDEAL_BOUNDARY`, Theorem 8.3.  KL
identifies and continuously extends the actual tile map at the two
annular wrapping points.  A nontrivial canonical deck kernel puts those
same standalone points in its limit set, where a nonconstant invariant
map cannot extend.  Hence the two objects require an explicit
correspondence or restricted interface; they are not one whole-tile
factorization.

### 11.14 Treating the no-go as actual KL injectivity

Rejected.  The theorem uses a global covering-deck invariance, not bare
noninjectivity.  The exact map
\[
 z\longmapsto e^{4(z-1)}
\]
is a noninjective holomorphic immersion of \(\mathbb D\) into itself and
extends continuously to the closed disk, but it is not a covering onto
its image.  The actual KL map may therefore remain a non-covering
immersion.  A valid replacement must retain its relation-valued sheet and
access data rather than infer injectivity.

## 12. Promotion boundary

The unconditional results proved here justify promotion of:

- `KL_PSEUDOPIECE_CONFORMAL_IDEAL_BOUNDARY`;
- `EMBEDDED_DISK_ACCESSIBLE_FOOTPRINT_THEOREM`;
- `GENERAL_ANNULUS_IMMERSION_LOWER_STRIP_NO_GO`; and
- `COMMON_COORDINATE_NESTED_ANNULUS_OUTER_CAP`.

The last obligation is explicitly conditional on `(CI)` and contains:

- the exact lower-strip normal form;
- isolation of every source-\(O\)-adjacent cap;
- the footprint
  \(\Phi(p)=\overline{\lambda}_{t,j(i)}\) on every open source \(O\)-side;
- explicit exclusion from the open target \(O\)-atom;
- the exact footprint criterion (9.3); and
- positive absorption by the native three-atom tile-star.

They do not justify promotion of:

- `DIRECT_DECORATION_DEGREE_ONE_PSEUDO_EMBEDDING`;
- `DIRECT_DECORATION_OUTER_CAP_FOOTPRINT`;
- `DIRECT_DECORATION_PSEUDO_PIECE_PATH_LIFT_EXHAUSTION`;
- `DIRECT_DECORATION_ALL_DEPTH_CONTACT_CLOSURE`;
- `DIRECT_DECORATION_TRACE_COLLAR_REALIZATION`;
- `VIRTUAL_WAVE_MARKED_CORRESPONDENCE`;
- VAAPC-I;
- UPTCR; or
- MLC.

The unresolved chain now begins with
`DIRECT_DECORATION_WAVE_PROOF_USE_LEDGER`, then actual canonical/KL stage
alignment, geometric inverse-trace proper-path and whole-end-interval
classification, and the uniform relation response.  The physical
relative-boundary incidence state and sheet-sensitive footprint system
(10.1)--(10.3) must then be constructed; the alternative is a separately
embedded retained-collar system with complete charges for discarded
cosets, sheets, and limit-set contacts.
Cartesian final-root no-birth is an independent geometric successor of
the classification.
The old universal full-canonical univalence and full-prime-end
factorization routes are unavailable.  The complete source \(O\)-side
footprint, the \(\xi/\eta\) central-seam footprints, and induced
family-level marking compatibility remain open.

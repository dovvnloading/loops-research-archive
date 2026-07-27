# Terminal Wave crest to KL skipping-over bridge

Date: 2026-07-26

Status: the source-level type obstruction, the adjacent-access
extremal-length warning, and the conditional width comparisons in this
note are proved.  The dynamical binder that would apply those comparisons
to every actual terminal Wave occurrence is open.  In particular, this
note does not prove `TERMINAL_WAVE_KL_CONNECTING_SUBFAMILY`,
`TERMINAL_KL_SUBMULTICURVE_BINDER_SELECTOR`, VAAPC-I, UPTCR, or MLC.

## 1. Purpose and exact conclusion

The terminal native Hubbard-tree construction selects an ideal side
\(I_{1\to0}\), and the puzzle-component analysis selects a unique KL
puzzle vertex \(v_*\) with
\[
 C_1=S_{Y_B}^{v_*},
 \qquad
 K_1\subset S_{Y_B}^{v_*}.
\tag{1.1}
\]
The remaining question addressed here is whether a KKL Wave which
**crests over** \(I_{1\to0}\) automatically contains, without an appended
connector,

1. a crossing of one KL universal-cover tile; or
2. a KL horizontal multicurve which skips over a separating puzzle
   piece.

The answer supplied by the locked sources is negative.  There are two
independent reasons.

First, a KKL Wave's crest is not one of its ends.  The Wave definition
does not produce a physical curve joining two prescribed exterior Julia
components.  The DL cap formulation supplies accessibility of the
crested side, but no KL tile, deck sheet, horizontal lift, or
skipping-over predicate.

Second, the two KL half-accesses at \(v_*\) lie in two adjacent tiles,
whereas KL's tile-crossing family lies in one tile and joins that tile's
two \(J\)-boundary components.  The two families have different
source and endpoint types.

There is nevertheless a sharp conditional result.  If a binder produces
a complete proper restriction family and literal ordered subcurves which
lift to a fixed KL tile-crossing family, then
\[
 \mathcal W(S_0)\le \operatorname{Bd}_A^{-1}.
\tag{1.2}
\]
If instead it produces KL horizontal multicurves which skip a fixed
depth-\(m\) separating piece, then
\[
 \mathcal W(S_0)
 \le
 \frac{2^{2m+q+2}}{\mu}.
\tag{1.3}
\]
Every restriction, lifting, and family-inclusion comparison in these
statements has coefficient exactly one.  The last depth estimates are
KL's published estimates; they are not asserted to be sharp or uniform
when \(m\) or \(q\) grows.

## 2. Locked sources and notation

The line numbers below refer to the following local source snapshots.

| key | local source | SHA-256 | proof-used lines |
|---|---|---|---|
| KKL-W | `.tmp_wave_audit/waves-with-Misha.tex` | `AD4C774806D9902AA54FA31C56AD6146D8034946F19CC5E9CEC3C51A3F94FDD5` | 1844--1875, 2081--2090 |
| DL-W | `.tmp_wave_audit/dl23/Feigen.tex` | `EB8C50CC51039A82317CF1951B1E333F23DF100773F8AD0DF0586AC7CD465DDF` | 2797--2817 |
| KL-\(\psi\) | `.tmp_kl08_source/psiql.tex` | `6CC9726461473812A5FBA93377F2DC0B088DB6CAC4B9DE90C7B2AE625DFB49AF` | 95--123, 231--285 |
| KL-M | `.tmp_kl08_source/moduli.tex` | `CBDB9EF7D6AC94C33FDB0AB7167E19C39EB23D27373C266A296CF6031E0CAF7E` | 289--345, 348--505 |
| KL-E | `.tmp_kl08_source/appendix.tex` | `05A13ED2D46CB9E2D188E6D96F4A2B639626F99657723118B4DE3479CD980916` | 10--45 |

These are source locks, not claims that later versions of the cited
papers use identical line numbers.

For a curve family \(\Gamma\), write
\[
 \mathcal L(\Gamma)
 =
 \sup_{\rho}
 \frac{\ell_\rho(\Gamma)^2}{\operatorname{area}_\rho},
 \qquad
 \mathcal W(\Gamma)=\mathcal L(\Gamma)^{-1},
\tag{2.1}
\]
with the usual extended-value conventions.  KL-E, lines 10--15, uses
this reciprocal convention.  If
\(\Gamma_1\subseteq\Gamma_2\), then
\[
 \mathcal L(\Gamma_1)\ge\mathcal L(\Gamma_2),
 \qquad
 \mathcal W(\Gamma_1)\le\mathcal W(\Gamma_2).
\tag{2.2}
\]
Indeed, for every conformal metric,
\(\ell_\rho(\Gamma_1)\ge\ell_\rho(\Gamma_2)\); take the supremum and
then invert.

### 2.1 KKL Waves

KKL-W, lines 1844--1869, defines the ideal boundary and ideal marking of
a hyperbolic surface.  Lines 1874--1875 define a Wave \(S\) subordinate
to a multi-interval \(B\).  If \(I,J\) are the smallest multi-intervals
at which its leaves end, then
\[
 C=B\setminus(I\cup J)
\tag{2.3}
\]
is its crest.  Saying that \(S\) is a Wave over \(X\) means
\[
 X\subseteq C.
\tag{2.4}
\]
Consequently, (2.4) does not say that a leaf endpoint belongs to \(X\).

KKL-W, lines 2081--2084, defines restriction by a holomorphic immersion
\(\iota:V'\to V\).  Its domination lemma, lines 2086--2090, implies:
if \(S\) is a lamination in \(V\), \(\mathcal H\) is a lamination in
\(V'\), and every leaf of \(S\) has a restriction containing a leaf of
\(\mathcal H\), then
\[
 \mathcal W(S)\le\mathcal W(\mathcal H).
\tag{2.5}
\]

### 2.2 DL Waves above a side

DL-W, lines 2798--2807, defines a side by the Carathéodory boundary of a
filled carrier.  Line 2813 says that a Wave above a side consists of
proper curves whose two ends lie outside that side and whose bounded cap
has the side accessible on its Carathéodory boundary.  This is a
two-sided cap condition, not an endpoint condition.  The Wave Lemma,
lines 2815--2817, compares the ambient width to the Wave width.  It does
not identify the cap with a KL tile or state the reverse estimate needed
in (1.2).

### 2.3 KL pseudo-piece boundary

Let \(Y\) be a geometric puzzle piece and
\[
 K_Y=Y\cap K(f).
\]
KL-\(\psi\), lines 95--123, constructs the pseudo-piece
\(\Psi(Y)\) by taking the components \(A_i\) of \(Y\setminus K_Y\),
embedding each \(A_i\) into a copy \(\widehat A_i\) of the universal
cover of the ambient annulus, and gluing these tile copies to \(Y\).

KL-\(\psi\), lines 231--244, gives the boundary incidence.  The tile
\(\widehat A_i\) has one outer arc \(\lambda_i\) and two
\(J\)-boundary arcs \(\xi_i,\eta_i\), and
\[
 \eta_i\cap\xi_{i+1}=\{v_i\},
 \qquad
 \partial^{v_i}\Psi(Y)=\eta_i\cup\xi_{i+1}.
\tag{2.6}
\]
The tile tags in (2.6) must be retained before the physical gluing at
\(v_i\).

KL-\(\psi\), lines 256--267, defines an ordered horizontal multicurve.
Lines 270--275 prove that a physical curve joining
\(S_Y^v\) to \(S_Y^w\) contains a submulticurve which lifts to a
horizontal multicurve joining
\(\partial^v\Psi(Y)\) to \(\partial^w\Psi(Y)\).  The result is a
contained submulticurve; it is not equality of the original physical
curve with its lift.  Lines 279--285 define
\[
 \Gamma_Y(v,w)
 =
 \{\text{horizontal multicurves from }\partial^v\Psi(Y)
       \text{ to }\partial^w\Psi(Y)\},
\qquad
 \operatorname{Bd}_Y(v,w)=\mathcal L(\Gamma_Y(v,w)).
\tag{2.7}
\]

### 2.4 KL tile crossings and skipping over

KL-M, lines 351--358, fixes a component \(A\) of
\(Y\setminus K_Y\), notes that the exposed \(J\)-boundary of
\(\widehat A\) has two components, and defines
\[
 \mathcal C_A
 =
 \{\gamma\subset\widehat A:
   \gamma\text{ joins the two components of }
   \partial_J\widehat A\},
\qquad
 \operatorname{Bd}_A=\mathcal L(\mathcal C_A).
\tag{2.8}
\]

KL-M, lines 375--408, proves that for
\(Y\in\mathcal Y^m(m+q)\),
\[
 \operatorname{Bd}_A\ge\frac1\mu.
\tag{2.9}
\]
Lines 410--477 prove that for
\(Y\in\mathcal Y^m(0)\),
\[
 \operatorname{Bd}_A
 \ge
 \frac{\mu}{2^{m+q+2}}.
\tag{2.10}
\]
Here \(\mu>0\) is the normalized modulus parameter used in KL-M,
including the normalization at line 291.

Finally, let \(v,w\) be vertices of \(Y\), and let \(Z\subset Y\) be a
depth-\(m\) puzzle piece separating \(v\) from \(w\).  KL-M, lines
479--482, says that a horizontal multicurve from
\(\partial^v\Psi(Y)\) to \(\partial^w\Psi(Y)\) **skips over**
\(K_Z\) if at least one of its ordered components does not cross
\(K_Z\).  If \(\mathcal T_{Y,Z}(v,w)\) denotes the family of all such
multicurves, Corollary `separating pieces`, lines 484--505, proves
\[
 \mathcal L(\mathcal T_{Y,Z}(v,w))
 \ge
 \frac{\mu}{2^{2m+q+2}}.
\tag{2.11}
\]

There are two notation slips in the locked KL-M text which must not be
silently promoted into new assertions.  Line 471 writes
\(\mathcal C_Y^\epsilon\) in a proof whose defined family is
\(\mathcal C_A\), and line 498 writes \(\mathcal G_{A_j}\) where the
preceding tile family is denoted \(\mathcal C_{A_j}\).  The statements
(2.10) and (2.11) are the displayed conclusions of the corresponding
lemma and corollary; nothing here relies on a new identification beyond
their proofs' stated contexts.

## 3. Adjacent-tile type obstruction

### Proposition 3.1

Let \(v_i\) be a tile-tagged vertex occurrence of a KL pseudo-piece.
The two tagged half-accesses flanking \(v_i\) are
\[
 (i,\eta_i)
 \quad\text{and}\quad
 (i+1,\xi_{i+1}).
\tag{3.1}
\]
The tile-crossing family \(\mathcal C_{A_i}\) does not join the two
occurrences in (3.1).  It joins
\[
 (i,\xi_i)
 \quad\text{to}\quad
 (i,\eta_i).
\tag{3.2}
\]
Likewise, \(\mathcal C_{A_{i+1}}\) joins
\[
 (i+1,\xi_{i+1})
 \quad\text{to}\quad
 (i+1,\eta_{i+1}).
\tag{3.3}
\]
Thus no fixed adjacent tile-crossing is the two-flank family at \(v_i\),
except in the exceptional one-tile cyclic presentation where the two
tile occurrences coincide.

#### Proof

Equation (3.1) is exactly (2.6).  By (2.8), a crossing of
\(\widehat A_i\) joins the two components of that tile's exposed
\(J\)-boundary.  Those components are \(\xi_i,\eta_i\), which gives
(3.2).  Replacing \(i\) by \(i+1\) gives (3.3).

The first member of (3.1) occurs in \(\widehat A_i\), while the second
occurs in \(\widehat A_{i+1}\).  A member of \(\mathcal C_{A_j}\) is
contained in the single surface \(\widehat A_j\).  It therefore cannot
have both tile-tagged occurrences in (3.1) as its two boundary sides
unless \(i\) and \(i+1\) denote the same unique tile occurrence.
\(\square\)

### Corollary 3.2

The vertex anchor
\[
 I_{1\to0}\longmapsto v_*
\tag{3.4}
\]
does not select a KL tile-crossing family.

#### Proof

The assignment (3.4) forgets which of the two occurrences in (3.1) is
the left or right lateral access.  Even after both occurrences are
restored, Proposition 3.1 shows that they are not the boundary pair of a
single KL tile. \(\square\)

Concatenating two independently chosen tile curves does not repair this
failure.  Such a concatenation would use a boundary vertex as an
auxiliary connector, would not be a curve in one \(\widehat A_j\), and
is not asserted to be a literal ordered subcurve of the original Wave
leaf.

## 4. Adjacent access does not provide a width bound

The following elementary calculation is a warning against replacing the
missing binder by the bare statement “the curve joins the two tagged
halves at \(v_*\).”

### Lemma 4.1 (punctured-half-disk warning)

Let
\[
 D_\epsilon^+
 =
 \{z:0<|z|<\epsilon,\ 0<\arg z<\pi\},
\]
and let \(\Gamma_\epsilon\) be the family of all curves in
\(D_\epsilon^+\) joining its two radial boundary intervals
\[
 (0,\epsilon)
 \quad\text{and}\quad
 (-\epsilon,0).
\]
Then
\[
 \mathcal L(\Gamma_\epsilon)=0,
 \qquad
 \mathcal W(\Gamma_\epsilon)=+\infty.
\tag{4.1}
\]

#### Proof

Choose the branch
\[
 \log z=\log|z|+i\arg z
\]
on \(D_\epsilon^+\).  It maps \(D_\epsilon^+\) conformally onto
\[
 \Pi_\epsilon
 =
 (-\infty,\log\epsilon)\times(0,\pi).
\tag{4.2}
\]
The two radial boundary intervals map to the two horizontal sides
\(y=0\) and \(y=\pi\).

For \(R>0\), let
\[
 Q_R
 =
 (\log\epsilon-R,\log\epsilon)\times(0,\pi)
\]
and let \(\Gamma_R\) be the full family of curves in \(Q_R\) joining its
horizontal sides.  Every member of \(\Gamma_R\) belongs to the image of
\(\Gamma_\epsilon\), so by (2.2),
\[
 \mathcal L(\Gamma_\epsilon)
 \le
 \mathcal L(\Gamma_R).
\tag{4.3}
\]
The extremal length of the horizontal-side crossing family of a
rectangle of width \(R\) and height \(\pi\) is
\[
 \mathcal L(\Gamma_R)=\frac{\pi}{R}.
\tag{4.4}
\]
Equations (4.3)--(4.4) hold for every \(R>0\).  Letting
\(R\to\infty\) gives
\(\mathcal L(\Gamma_\epsilon)=0\).  The reciprocal convention in (2.1)
then gives infinite width. \(\square\)

### Consequence 4.2

Two boundary arcs with a common endpoint do not, merely by being
distinguished and cyclically ordered, carry a finite universal
two-terminal width.  One must additionally prove a nondegenerate
separation condition, such as:

1. compact truncation away from the common endpoint with a controlled
   scale;
2. crossing of a fixed tile \(\widehat A\); or
3. skipping over a fixed separating piece \(Z\).

Lemma 4.1 is not a claim that every dynamically selected Wave subfamily
has infinite width.  It proves that the half-access labels alone do not
exclude that degeneration and therefore cannot imply a finite bound.

## 5. Why the Wave hypothesis does not fill the gap

### Proposition 5.1 (source-level non-implication)

From the following data alone,

1. \(S\) is a KKL Wave;
2. \(I_{1\to0}\) lies in the crest of \(S\);
3. \(C_1=S_{Y_B}^{v_*}\);

one cannot invoke either the tile estimates (2.9)--(2.10) or the
skipping-over estimate (2.11).

#### Proof

The KKL Wave definition supplies the ideal-boundary datum
\[
 I_{1\to0}
 \subset
 \partial_{\rm id}(\mathbb U\setminus\mathcal T).
\tag{5.1}
\]
The KL crossing and skipping families live instead in
\[
 \widehat A_i
 \subset
 \Psi(Y_B),
\qquad
 \partial^{v}\Psi(Y_B)
 \subset
 \partial_{\rm PE}\Psi(Y_B).
\tag{5.2}
\]
None of the cited Wave definitions constructs a map
\[
 \partial_{\rm id}(\mathbb U\setminus\mathcal T)
 \longrightarrow
 \partial_{\rm PE}\Psi(Y_B),
\tag{5.3}
\]
let alone a map preserving both lateral germs, tile tags, deck sheets,
and cyclic order.

Moreover, the crest relation says that leaf endpoints lie at the Wave
ends, outside the crest.  It supplies no physical subcurve joining fixed
sets \(S_Y^v,S_Y^w\).  The DL formulation adds only that the side is
accessible from the bounded cap.  Accessibility does not declare:

1. two distinct endpoint vertices \(v,w\);
2. a puzzle piece \(Z\) separating them;
3. an ordered KL lift;
4. a component which does not cross \(K_Z\); or
5. one fixed tile \(A\) crossed by every retained leaf.

The component identity \(C_1=S_{Y_B}^{v_*}\) selects the physical
vertex, but Proposition 3.1 shows that it does not select a single tile
crossing.  Consequently none of the hypotheses of (2.9)--(2.11) has
been instantiated. \(\square\)

This is a proof-theoretic obstruction, not a dynamical counterexample to
the possibility of constructing the missing binder.

### Proposition 5.2 (stationary pass-through does not yet fill B1--B2)

The project theorem
`KKL_STATIONARY_TWO_PULLBACK_PASS_THROUGH` improves the raw crest datum
in one native stationary branch: for \(N=b+3\), every retained
occurrence in \(A_{N-1}\) passes through \(K_0^b\) and
\(K_0^{b+1}\) in KKL's successive-pullback sense.  This does not
instantiate the literal-restriction or fixed-puzzle clauses B1--B2 below.

#### Proof

The complete proof, including the repair of the undefined \(A_N\) at KKL
line 1605, is in `kkl_stationary_wave_component_incidence.md`.  The
proved source statement remains in KKL's pass-through language.
Subsequent filled-set graph naturality names the two distinct final
components and proves their projection formulas, but it does not prove
common-occurrence incidence or order.  It also shows that both proposed
graph restrictions have degree two, not one.  Final proper-path
extraction, incidence refinement, order, a connected or ordered proper
restriction, and one authorized KL puzzle realization are exactly the
additional assertions required by B1 and B2. \(\square\)

## 6. Ordered overflow

For completeness, the inequality direction used below is recorded
explicitly.

### Lemma 6.1 (ordered-submulticurve overflow)

Let \(p:U\to V\) be a holomorphic immersion.  Let
\(\widehat{\mathcal H}\) be a family of finite ordered multicurves in
\(U\), where the length of a multicurve is the sum of its component
lengths.  Let \(\mathcal H\) be a curve family in \(V\).  Suppose that
for every \(h\in\mathcal H\), pairwise parameter-disjoint ordered
subarcs of \(h\) are the images of the ordered components of some
\(\widehat h\in\widehat{\mathcal H}\).  Then
\[
 \mathcal L(\mathcal H)
 \ge
 \mathcal L(\widehat{\mathcal H}),
\qquad
 \mathcal W(\mathcal H)
 \le
 \mathcal W(\widehat{\mathcal H}).
\tag{6.1}
\]

#### Proof

This is the ordered-multicurve extension proved as Lemma 5.0 of
`terminal_dense_obstacle_and_submulticurve_replacement.md`; KL-E
Corollary `two families`, lines 38--43, is its curve-family antecedent.
For a self-contained verification, fix a conformal metric
\(\rho\) on \(U\) and define the pushforward metric
\[
 \sigma(w)^2
 =
 \sum_{z\in p^{-1}(w)}
 \frac{\rho(z)^2}{|p'(z)|^2}.
\tag{6.2}
\]
The area formula gives
\[
 \operatorname{area}_\sigma(V)
 =
 \operatorname{area}_\rho(U);
\tag{6.3}
\]
the sum in (6.2) already ranges over every source preimage, and
Tonelli's theorem plus change of variables gives equality.  Along an
image subarc,
\[
 \sigma(p(z))\,|p'(z)|\ge\rho(z).
\tag{6.4}
\]
Because the chosen subarcs are pairwise parameter-disjoint, their
lengths add inside the length of \(h\).  Thus
\[
 \ell_\sigma(h)
 \ge
 \ell_\rho(\widehat h),
\qquad
 \ell_\sigma(\mathcal H)
 \ge
 \ell_\rho(\widehat{\mathcal H}).
\tag{6.5}
\]
Use (6.3)--(6.5) in (2.1) and take the supremum over \(\rho\).  This
gives the first inequality in (6.1); inversion gives the second.
\(\square\)

The disjoint ordered-subarc condition is essential.  If two source
components are represented by the same target parameter interval, their
summed source length cannot be charged twice to the target curve.

## 7. Sharp conditional tile-crossing theorem

### Theorem 7.1

Let \(\iota:V'\to V\) be a holomorphic immersion.  Let \(S_0\) be a
lamination in \(V\), and let \(\mathcal H\) be an admissible lamination
in \(V'\).  Assume:

1. for every leaf \(\alpha\in S_0\), the restriction
   \(\iota^*\alpha\) contains a leaf of \(\mathcal H\);
2. \(Y\) is one fixed KL geometric puzzle piece and
   \(A\) is one fixed component of \(Y\setminus K_Y\), with a declared
   holomorphic KL tile map
   \[
    p_A:\widehat A\longrightarrow V';
   \]
3. the relevant physical localization of every
   \(h\in\mathcal H\) contains an ordered subarc of the form
   \(p_A(c_h)\), where \(c_h\in\mathcal C_A\);
4. no connector has been appended to \(h\), and all retained
   occurrences and multiplicities are those of the literal
   restrictions.

Then
\[
 \mathcal W(S_0)
 \le
 \mathcal W(\mathcal H)
 \le
 \mathcal W(\mathcal C_A)
 =
 \operatorname{Bd}_A^{-1}.
\tag{7.1}
\]

#### Proof

Hypothesis 1 and KKL domination (2.5) give
\[
 \mathcal W(S_0)\le\mathcal W(\mathcal H).
\tag{7.2}
\]
Hypothesis 3, together with the declared holomorphic map \(p_A\), is
exactly the hypothesis of Lemma 6.1 with source family
\(\mathcal C_A\).  Therefore
\[
 \mathcal L(\mathcal H)\ge\mathcal L(\mathcal C_A).
\tag{7.3}
\]
Invert (7.3) and use (2.8):
\[
 \mathcal W(\mathcal H)
 \le
 \mathcal W(\mathcal C_A)
 =
 \operatorname{Bd}_A^{-1}.
\tag{7.4}
\]
Combining (7.2) and (7.4) proves (7.1). \(\square\)

### Corollary 7.2 (KL depth estimates)

Under Theorem 7.1:

1. if \(Y\in\mathcal Y^m(m+q)\), then
   \[
    \mathcal W(S_0)\le\mu;
   \tag{7.5}
   \]
2. if \(Y\in\mathcal Y^m(0)\), then
   \[
    \mathcal W(S_0)
    \le
    \frac{2^{m+q+2}}{\mu}.
   \tag{7.6}
   \]

#### Proof

Invert (2.9) and (2.10), respectively, and apply (7.1).
\(\square\)

## 8. Sharp conditional skipping-over theorem

### Theorem 8.1

Retain \(\iota,S_0,\mathcal H\) and Hypothesis 1 of Theorem 7.1.
Suppose instead that there are fixed data
\[
 (Y,Z,v,w,p_Y),
\tag{8.1}
\]
where:

1. \(v\ne w\) are vertices of \(Y\);
2. \(Z\subset Y\) is a depth-\(m\) puzzle piece separating \(v\)
   from \(w\), and
   \[
    p_Y:\Psi(Y)\longrightarrow V'
   \]
   is the declared holomorphic KL projection/comparison map;
3. for every \(h\in\mathcal H\), pairwise parameter-disjoint ordered
   subarcs of \(h\) are the \(p_Y\)-images of the components of an
   ordered horizontal multicurve
   \(\widehat h\in\Psi(Y)\) from
   \(\partial^v\Psi(Y)\) to \(\partial^w\Psi(Y)\);
4. one declared component of every \(\widehat h\) does not cross
   \(K_Z\);
5. the resulting family \(\widehat{\mathcal H}\) retains every
   occurrence and multiplicity and is contained in the single fixed
   family \(\mathcal T_{Y,Z}(v,w)\).

Then
\[
\begin{aligned}
 \mathcal W(S_0)
 &\le
 \mathcal W(\mathcal H)\\
 &\le
 \mathcal W(\widehat{\mathcal H})\\
 &\le
 \mathcal W(\mathcal T_{Y,Z}(v,w))\\
 &\le
 \frac{2^{2m+q+2}}{\mu}.
\end{aligned}
\tag{8.2}
\]

#### Proof

KKL domination gives the first inequality exactly as in (7.2).
Lemma 6.1 gives
\[
 \mathcal W(\mathcal H)
 \le
 \mathcal W(\widehat{\mathcal H}).
\tag{8.3}
\]
Hypotheses 3--5 and the definition at KL-M lines 479--487 give
\[
 \widehat{\mathcal H}
 \subseteq
 \mathcal T_{Y,Z}(v,w).
\tag{8.4}
\]
Family monotonicity (2.2) gives
\[
 \mathcal W(\widehat{\mathcal H})
 \le
 \mathcal W(\mathcal T_{Y,Z}(v,w)).
\tag{8.5}
\]
Finally, invert the positive lower bound (2.11):
\[
 \mathcal W(\mathcal T_{Y,Z}(v,w))
 \le
 \frac{2^{2m+q+2}}{\mu}.
\tag{8.6}
\]
Equations (8.3), (8.5), and (8.6), together with KKL domination,
prove (8.2). \(\square\)

### Proposition 8.2 (sharp comparison coefficient)

The coefficient one in every comparison preceding the final KL depth
estimate in (7.1) and (8.2) cannot be decreased in the abstract
category of the stated hypotheses.

#### Proof

Take the restriction immersion and KL comparison map to be conformal
isomorphisms, take no discarded restriction components, and take the
source, restriction, lifted, and ambient families to be conformal copies
of the same family.  Every inequality preceding the numerical KL bound
is then equality. \(\square\)

Proposition 8.2 does not assert that the estimates (2.9)--(2.11) are
sharp, nor that the required equality model occurs in every terminal
dynamical block.

## 9. Why KL's skipping proof does not select a terminal tile

KL-M, lines 494--504, proves (2.11) by considering the at most
\(2^m\) components \(A_j\) of \(Z\setminus K_Z\).  A skipping
multicurve contains an arc lifting to a crossing in **some**
\(\widehat A_j\), and the proof partitions by \(j\) before applying the
parallel law.

Consequently:

1. the tile \(A_j\) may vary with the multicurve;
2. the selected tile need not be either tile adjacent to \(v_*\);
3. the proof supplies a width bound after summing the response classes,
   not a canonical terminal tile; and
4. the factor \(2^{2m+q+2}\) records the depth-dependent partition.

Thus Theorem 8.1 is potentially useful for the width-only branch, but it
does not by itself prove exact carrier-pair or terminal prime-end
naturality.

## 10. Exact open binder certificate

The next analytic obligation is:

```text
TERMINAL_WAVE_CREST_TO_KL_SKIPPING_BINDER
```

It should be recorded as a child of the already open
`TERMINAL_WAVE_KL_CONNECTING_SUBFAMILY`, rather than as a replacement
for that obligation.

For a retained proof-use Wave \(S\), it must first select a subwave
\(S_0\) and constants \(\theta>0,E\ge0\) satisfying
\[
 \mathcal W(S_0)
 \ge
 \theta\mathcal W(S)-E.
\tag{10.1}
\]
For every actual retained leaf occurrence \(\delta\), the certificate
must then construct
\[
\begin{aligned}
 \mathfrak B_{\rm skip}(\delta)
 =(&h_\delta,\,
    Y,Z,v^-,v^+,\,\beta_\delta,\widehat\beta_\delta,\,
    k_\delta,\\
   &\mathbf a^-_*,\mathbf a^+_*,\,
    \operatorname{tile}_\delta,\operatorname{deck}_\delta,\,
    \operatorname{ord}_\delta,\operatorname{mult}_\delta,\,
    \operatorname{loc}_\delta,\operatorname{obs}_\delta,\,
    \operatorname{root}_\delta).
\end{aligned}
\tag{10.2}
\]
The entries must satisfy all of the following clauses.

### B1. Literal complete restriction

\(h_\delta\) is a leaf of one admissible proper-restriction lamination
\(\mathcal H\), and
\[
 h_\delta\subset\iota^*\delta.
\tag{10.3}
\]
No path segment may be appended.  Every proof-used restriction
occurrence is either retained with its multiplicity or explicitly
charged by the proved loss estimate (10.1).

### B2. Fixed response class

The data \(Y,Z,v^-,v^+\) are fixed across the response class to which
\(\delta\) belongs,
\[
 v^-\ne v^+,
\tag{10.4}
\]
and \(Z\) separates \(v^-\) from \(v^+\).  If several classes are used,
their number and parallel-width charge must be proved uniformly bounded;
one may not apply Theorem 8.1 to leaf-dependent unrecorded data.

### B3. Ordered contained subcurve

\(\beta_\delta\) is an ordered union of pairwise
parameter-disjoint subarcs of \(h_\delta\).  It is not an independently
chosen curve with the same endpoint labels.

### B4. Actual KL lift

The declared tile, deck, and relative-cover data lift
\(\beta_\delta\) to the ordered horizontal multicurve
\[
 \widehat\beta_\delta:
 \partial^{v^-}\Psi(Y)
 \longrightarrow
 \partial^{v^+}\Psi(Y).
\tag{10.5}
\]
All central/tile seam crossings and ordered components are retained.

### B5. Componentwise skip witness

\(k_\delta\) names one actual ordered component of
\(\widehat\beta_\delta\) and proves
\[
 \widehat\beta_{\delta,k_\delta}
 \text{ does not cross }K_Z.
\tag{10.6}
\]
It is insufficient to say that the whole multicurve “goes around” the
terminal component.

### B6. Tagged terminal flanks

Writing \(v_*=v_{i_*}\), the two terminal lateral occurrences are
recorded before gluing as
\[
 \mathbf a^-_*
 =
 (i_*,\eta_{i_*}),
 \qquad
 \mathbf a^+_*
 =
 (i_*+1,\xi_{i_*+1}),
\tag{10.7}
\]
up to the one explicitly declared orientation reversal.  The
certificate proves where these occurrences appear in the ordered lift
itinerary.  Equality of their physical images at \(v_*\) is not a
substitute for their tile-tagged occurrence data.

### B7. Localization and obstacle audit

Every component of \(\beta_\delta\) and
\(\widehat\beta_\delta\) lies in the authorized localization.
The obstacle ledger proves avoidance, absorption, or separation for
every proof-used obstacle.  No hidden crossing may be removed by
passing to the ribbon quotient.

### B8. Family admissibility

The selected \(h_\delta\) form a lamination to which KKL domination
applies.  The selected lifts form the family
\(\widehat{\mathcal H}\) with the occurrence order and multiplicities
required by Lemma 6.1.

### B9. Final-root stability

The record \(\operatorname{root}_\delta\) proves that final-root
enlargement preserves:

1. the literal-subcurve relation;
2. the two tagged flank occurrences;
3. the separating piece and skip witness;
4. the relative-cover sheet;
5. occurrence multiplicity; and
6. the obstacle/localization verdict.

A late root enlargement which changes any of these data invalidates the
binder occurrence.

### B10. Uniform response charge

If (8.2) is to contribute to a universal tower estimate, the resulting
factor
\[
 \frac{2^{2m+q+2}}{\mu}
\tag{10.8}
\]
must be uniformly controlled, absorbed into a separately proved
calibrated potential, or replaced by a stronger estimate.  The
published skipping-over bound alone is not period independent.

## 11. Failure certificate

If the binder fails, the first failure must be recorded as
\[
\begin{aligned}
 \mathfrak F_{\rm skip}(\delta)
 =(&\delta,\text{stage},\text{first failed clause},Y,Z,
    v^-,v^+,\\
   &\text{physical component},\text{ordered parameter interval},
    \text{tile tag},\text{deck phase},\\
   &\text{crossing/skip verdict},\text{obstacle},
    \text{full itinerary},\text{final-root image}).
\end{aligned}
\tag{11.1}
\]

The failure classes are:

1. `F_END`: no distinct physical endpoint components;
2. `F_SUB`: the proposed curve requires an appended segment;
3. `F_LIFT`: no ordered KL lift in the declared relative cover;
4. `F_TAG`: wrong or merged \(\eta/\xi\) occurrence;
5. `F_SEP`: no fixed separating \(Z\);
6. `F_SKIP`: every lifted component crosses \(K_Z\);
7. `F_OBS`: obstacle or localization collision;
8. `F_MULT`: occurrence or ordered-component multiplicity is lost;
9. `F_ROOT`: final-root enlargement changes the certificate; and
10. `F_UNIF`: the response-class or depth charge is not uniform.

An `F_TAG` failure does not refute the width-only skipping route if
B1--B5 and B7--B10 can be proved independently.  Conversely, a
width-only skipping theorem does not repair `F_TAG` for exact
carrier-pair naturality.

## 12. Dependency and promotion record

The open binder should depend on:

1. `DIRECT_DECORATION_WAVE_PROOF_USE_LEDGER`;
2. `TERMINAL_K1_UNIQUE_PUZZLE_VERTEX_ANCHOR`;
3. `TERMINAL_WAVE_KL_CONNECTING_SUBFAMILY`;
4. the terminal relative-cover, seam, tile-tag, and final-root records;
5. KKL-W's Wave and domination statements;
6. KL-\(\psi\)'s pseudo-piece boundary and lifting lemma; and
7. KL-M's tile and skipping-over estimates.

Theorems 7.1 and 8.1 may be recorded as the proved conditional node

```text
TERMINAL_WAVE_CREST_TO_KL_WIDTH_CONDITIONAL
```

with `TERMINAL_WAVE_CREST_TO_KL_SKIPPING_BINDER` as a hypothesis, not as
a proved dependency.

Only after B1--B10 hold for the complete terminal proof-use family may
the result feed
`TERMINAL_KL_SUBMULTICURVE_BINDER_SELECTOR`.  Exact terminal
carrier-pair naturality additionally requires the original endpoint and
prime-end matching obligations; Theorem 8.1 alone does not supply them.

## 13. Skeptic audit

1. **Crest was not relabeled as an end.**  The distinction is explicit
   in (2.3)--(2.4).
2. **A vertex was not relabeled as a tile side.**  Proposition 3.1
   retains both tile tags.
3. **Two adjacent half-accesses were not assigned a positive modulus
   for free.**  Lemma 4.1 exhibits the exact degeneration.
4. **No connector was appended.**  Literal containment is required in
   B1 and B3.
5. **KL's submulticurve was not upgraded to equality.**  Lemma 6.1 uses
   only ordered contained subarcs.
6. **All inequality directions were checked in extremal length before
   inversion.**
7. **The extracted tile in KL's skipping proof was not declared
   canonical.**  Section 9 records its leaf-dependent partition.
8. **The KL depth constants were not declared universal.**  B10 remains
   a separate global obligation.
9. **Width-only transfer was not promoted to prime-end naturality.**
10. **No numerical model proves an analytic clause.**

The immediate constructive target is therefore not another endpoint
label.  It is the literal, ordered, occurrence-complete certificate
(10.2), beginning with an actual Wave restriction and ending with a
componentwise KL skip witness.

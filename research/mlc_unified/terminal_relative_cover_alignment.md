# Terminal carrier fullness and relative-cover alignment

## 1. Result and promotion boundary

This note proves two terminal-interface facts that were previously left
conservative:

```text
TERMINAL_NATIVE_HUBBARD_CARRIER_FULLNESS
TERMINAL_RELATIVE_COVER_SUBGROUP_ALIGNMENT
```

For a periodically repelling terminal primitive map, the native Hubbard
carrier \(\mathcal T\) is a full continuum.  In any common simply
connected plane localization
\[
 \mathcal T\subset K\Subset\Omega,
\]
the inclusion
\[
 j:\Omega\setminus K\hookrightarrow\Omega\setminus\mathcal T
\]
induces an isomorphism on fundamental groups.  Pulling the universal
cover of the carrier complement back along \(j\) therefore gives one
connected universal cover of \(\Omega\setminus K\).  After a basepoint is
fixed, this cover is canonically isomorphic to a KL universal-cover tile
only when the tile has this exact base annulus, or after an explicit
base-domain identification.  The terminal constructor in Section 9
specializes to the exact KL base \(\mathbf U^m\setminus K\).

This closes the **relative-cover subgroup and connected-cover**
coordinate at the terminal anchor.  It does not:

- construct the common KL/KKL stage localization;
- enumerate KKL proper restrictions of a Wave trace;
- identify a carrier side with a KL ideal-boundary arc;
- prove properness or end-properness of an inclusion immersion;
- control obstacles or collar flanks;
- prove final-root no-birth; or
- close `WAVE_TO_KL_ADDRESS_ACCESS_SELECTOR`, VAAPC-I, UPTCR, or MLC.

Sections 11--12 add three further local results without changing that
promotion boundary.  The first canonically normalizes the integer deck
coordinate after an oriented outer seam has been marked.  The second
proves finite prime-end landing, with no deck escape, for every KKL
proper path in that normalized annular cover.  The third is a planar
countermodel showing that fullness, empty interior, and one-gate
attachment of every individual enlargement component do not by
themselves preserve any nonempty protected interval on a carrier side.

## 2. Source lock

The proof uses the following exact source statements.

1. Dudko--Lyubich, `Feigen.tex`, SHA-256
   `EB8C50CC51039A82317CF1951B1E333F23DF100773F8AD0DF0586AC7CD465DDF`,
   lines 953--970:

   > in the periodically repelling case,
   > \(\operatorname{int}K=\varnothing\), hence \(J=K\);
   > the general Hubbard continuum is the lift of the combinatorial
   > Hubbard dendrite.

2. KKL, `waves-with-Misha.tex`, SHA-256
   `AD4C774806D9902AA54FA31C56AD6146D8034946F19CC5E9CEC3C51A3F94FDD5`,
   the Hubbard-tree section:
   the native terminal carrier is compact, connected, contained in the
   filled Julia continuum, and contains the complete primitive
   small-Julia cycle.

   The same source, lines 451--457, states Kahn's induced
   quadratic-like restriction theorem: every \(\psi\)-quadratic-like
   map of finite width restricts, in neighborhoods of the same filled
   continuum \(\FK\), to a quadratic-like map.  The periodic points in
   \(\FK\), their multipliers, and the filled continuum are unchanged
   by this restriction.  Consequently the Dudko--Lyubich
   quadratic-like statement about
   \(\operatorname{int}\FK=\varnothing\) applies to KKL's periodically
   repelling \(\psi\)-quadratic-like terminal map.  This
   \(\psi\)-quadratic-like-to-quadratic-like step is part of the source
   interface; it is not being inferred merely from matching notation.

3. KL, `psiql.tex`, SHA-256
   `6CC9726461473812A5FBA93377F2DC0B088DB6CAC4B9DE90C7B2AE625DFB49AF`,
   lines 117--147:
   for a geometric puzzle piece, every tile \(\widehat A_i\) is a copy
   of the universal cover of the annulus \(A=\mathbf U^m\setminus K\),
   with a selected overlap embedding \(e_i:Y_i\to\widehat A_i\).

The filled Julia set \(K\) is full by the definition of a
quadratic-like or \(\psi\)-quadratic-like filled continuum.  No local
connectivity is assumed.

## 3. A connected subcontinuum of an empty-interior full continuum is full

### Theorem 3.1
(`TERMINAL_NATIVE_HUBBARD_CARRIER_FULLNESS`)

Let \(K\subset\mathbb C\) be a full continuum with
\(\operatorname{int}K=\varnothing\).  Every nonempty compact connected
set \(T\subset K\) is full.

In particular, the native terminal Hubbard carrier
\(\mathcal T\subset K\) is full.

#### Proof

Because \(K\) is full,
\[
 \mathbb C\setminus K
\tag{3.1}
\]
is connected and contains a neighborhood of infinity.  Since
\(T\subset K\),
\[
 \mathbb C\setminus K
 \subset
 \mathbb C\setminus T.
\tag{3.2}
\]
The connected set in (3.1) therefore lies in the unbounded component
of \(\mathbb C\setminus T\).

Suppose \(T\) were not full.  Then
\(\mathbb C\setminus T\) would have a bounded component \(O\).  By
(3.2), \(O\) is disjoint from \(\mathbb C\setminus K\), so
\[
 O\subset K.
\tag{3.3}
\]
But \(O\) is a nonempty open subset of \(\mathbb C\).  Equation (3.3)
would give \(\operatorname{int}K\ne\varnothing\), contradicting the
hypothesis.  Hence \(\mathbb C\setminus T\) is connected and \(T\) is
full. \(\square\)

For completeness, the terminal \(\psi\)-quadratic-like application has
one source-interface step.  Its annular width is finite, so Kahn's
theorem, recalled by KKL at source lines 451--457, supplies a
quadratic-like restriction on neighborhoods of the **same physical**
filled continuum \(K\).  The restriction agrees with the
\(\psi\)-quadratic-like germ on \(K\), hence has the same periodic
orbits and the same repelling multipliers there.  If
\(\operatorname{int}K\ne\varnothing\), the polynomial-like
no-wandering theorem (equivalently, straightening followed by the
polynomial Fatou classification) makes some component of
\(\operatorname{int}K\) eventually periodic.  The corresponding
periodic Fatou component is attracting, parabolic, or Siegel and
therefore supplies a nonrepelling periodic cycle in \(K\), contrary to
periodic repulsion.  Thus \(\operatorname{int}K=\varnothing\), in exact
agreement with the Dudko--Lyubich statement locked in Section 2.

The imported KKL theorem supplies compactness, connectedness, and
\(\mathcal T\subset K\).  The terminal primitive cycle contains at
least two disjoint nonempty small Julia continua, so \(\mathcal T\) is
nondegenerate.

## 4. The annular inclusion is a fundamental-group isomorphism

Fix a simply connected plane domain \(\Omega\) satisfying
\[
 \mathcal T\subset K\Subset\Omega.
\tag{4.1}
\]
Put
\[
 A=\Omega\setminus K,
 \qquad
 M=\Omega\setminus\mathcal T,
 \qquad
 j:A\hookrightarrow M.
\tag{4.2}
\]

### Lemma 4.1

Both \(A\) and \(M\) are doubly connected plane domains, and
\[
 \pi_1(A)\cong\mathbb Z,
 \qquad
 \pi_1(M)\cong\mathbb Z.
\tag{4.3}
\]

#### Proof

The complement of \(A\) in the sphere has exactly the two connected
components \(K\) and
\(\widehat{\mathbb C}\setminus\Omega\); the second is connected because
\(\Omega\) is simply connected.  Theorem 3.1 gives the identical
statement for \(M\), with \(K\) replaced by \(\mathcal T\).  Thus both
complements have the required two components.

We also verify that \(A\) and \(M\) are connected.  Choose a connected
Jordan collar inside \(\Omega\) surrounding \(K\).  If
\(\Omega\setminus K\) had a component missing that collar, a path in the
connected open set \(\mathbb C\setminus K\) from a point of that
component to infinity would have to meet the collar before leaving
\(\Omega\), while still remaining in \(\Omega\setminus K\).  This joins
the component to the collar component, a contradiction.  The same
argument applies to \(\mathcal T\).  Hence \(A\) and \(M\) are doubly
connected domains.  A doubly connected plane domain with
nondegenerate inner complementary continuum has fundamental group
\(\mathbb Z\); equivalently, its universal covering is a strip and a
once-winding outer collar loop is a generator. \(\square\)

### Theorem 4.2

The homomorphism
\[
 j_*:\pi_1(A)\longrightarrow\pi_1(M)
\tag{4.4}
\]
is an isomorphism.

#### Proof

Choose a smooth Jordan subdomain \(D\) with
\[
 K\Subset D\Subset\Omega.
\]
The positively oriented loop \(\ell=\partial D\) lies in both \(A\)
and \(M\).  Its winding number about every
\(t\in\mathcal T\) and every \(k\in K\) is \(+1\).  Since each
fundamental group is \(\mathbb Z\), this makes the loop a primitive
generator in both domains.  Thus by
Lemma 4.1
\[
 [\ell]_A\text{ generates }\pi_1(A),
 \qquad
 [\ell]_M\text{ generates }\pi_1(M).
\tag{4.5}
\]
The inclusion takes the first class in (4.5) to the second.  Under the
identifications with \(\mathbb Z\), \(j_*\) is multiplication by
\(+1\).  Hence it is an isomorphism. \(\square\)

The sign is \(+1\), rather than \(-1\), because the same positively
oriented physical collar loop is used in both domains.

## 5. Connected pullback of the universal cover

### Theorem 5.1
(`TERMINAL_RELATIVE_COVER_SUBGROUP_ALIGNMENT`)

Let
\[
 p_{\mathcal T}:\widetilde M\longrightarrow M
\tag{5.1}
\]
be the universal cover.  Then
\[
 \widetilde A
 =
 p_{\mathcal T}^{-1}(A)
\tag{5.2}
\]
is connected, and
\[
 p_{\mathcal T}|_{\widetilde A}:
 \widetilde A\longrightarrow A
\tag{5.3}
\]
is the universal cover of \(A\).

If \(\widehat A_i\to A_{\rm KL}\) is a KL tile and an explicit
orientation-preserving conformal base-domain identification
\[
 \beta:A\xrightarrow{\cong}A_{\rm KL}
\tag{5.4}
\]
is supplied, then basepoints
\(\widetilde a\in\widetilde A\) and
\(\widehat a_i\in\widehat A_i\) projecting to \(a\) and \(\beta(a)\)
determine a unique covering isomorphism
\[
 \Phi_i:
 (\widetilde A,\widetilde a)
 \xrightarrow{\ \cong\ }
 (\widehat A_i,\widehat a_i)
\tag{5.5}
\]
covering \(\beta\).  In the terminal specialization
\(\Omega=\mathbf U^m\), one has \(A=A_{\rm KL}\) and
\(\beta=\operatorname{id}\).

#### Proof

For a connected subspace \(A\subset M\), the components of the inverse
image of \(A\) in the universal cover of \(M\) are indexed by the cosets
\[
 \pi_1(M)/j_*\pi_1(A).
\tag{5.6}
\]
Theorem 4.2 makes the denominator equal to \(\pi_1(M)\), so (5.6) has
one element.  Thus \(\widetilde A\) is connected.

The subgroup of \(\pi_1(A)\) represented by the covering (5.3) is
\[
 j_*^{-1}(\{1\}).
\tag{5.7}
\]
Since \(j_*\) is injective, (5.7) is trivial.  Hence (5.3) is the
universal cover.

After the explicit conformal base identification \(\beta\), the KL tile and
\(\widetilde A\) are universal covers of the same base.  The based
uniqueness theorem for universal covers gives the unique isomorphism
(5.5).  Because \(\beta\) and both covering maps are conformal local
isomorphisms, this lift and its inverse are holomorphic; hence
\(\Phi_i\) is conformal. \(\square\)

### Corollary 5.2

At the terminal anchor there is no unresolved **cover-component** or
relative-subgroup multiplicity:
\[
 \#\pi_0\bigl(p_{\mathcal T}^{-1}(A)\bigr)=1,
 \qquad
 (j_*)^{-1}(\{1\})=\{1\}.
\tag{5.8}
\]

Different KL tile labels or unbased deck translates are not extra
components of the pulled-back cover.  A selected basepoint fixes the
covering isomorphism.  This does not collapse different KKL proper paths
or different ideal channels inside the one connected cover.

## 6. Proper-access channel atlas in the one connected cover

Use the based identification from Theorem 5.1 and regard
\[
 e:\widetilde A\hookrightarrow\widetilde M
\tag{6.1}
\]
as the physical inclusion of the connected pulled-back cover.  Both
surfaces are conformal disks, but \(e\) need not extend to their whole
ideal circles.

Fix a lifted native ideal interval
\[
 \widetilde I\subset\partial_{\rm id}\widetilde M.
\]
Fix also a closed, or locally finite closed, lifted ambient obstacle
ledger
\[
 \widetilde{\mathscr F}\subset\widetilde M,
 \qquad
 \widetilde M\setminus\widetilde A
 \subset\widetilde{\mathscr F}.
\tag{6.2}
\]
The relative obstacle \(\widetilde M\setminus\widetilde A\) is included
because a collar may avoid it in its interior while either flank or
its ideal end still accumulates on it.

### Definition 6.1

An open arc \(J\subset\partial_{\rm id}\widetilde A\) is a **certified
local proper-access arc over \(\widetilde I\)** if there is a one-sided
closed Jordan quadrilateral \(Q_J\) in the prime-end closure of
\(\widetilde A\), whose base-side relative interior is \(J\), and a
map
\[
 E_J:Q_J\longrightarrow
 \overline{\widetilde M}^{\,\operatorname{PE}}
\]
such that:

1. \(E_J\) is continuous and
   \(E_J|_{Q_J\cap\widetilde A}=e\);
2. \(E_J\) is a topological embedding of \(Q_J\) into the
   prime-end closure of \(\widetilde M\), and its boundary restriction
   maps \(J\) homeomorphically into
   \(\widetilde I\);
3. the two flank crosscuts of \(Q_J\) have distinct images and retain
   their cyclic order; and
4. in the prime-end closure of \(\widetilde M\), the ambient closure of
   the image collar avoids the ambient closure of the complete lifted
   obstacle ledger:
   \[
   E_J(Q_J)
   \cap
   \overline{\widetilde{\mathscr F}}^{\,\operatorname{PE}(\widetilde M)}
   =\varnothing .
   \tag{6.3}
   \]

Let
\[
 \mathcal E_{\rm pr}(\widetilde I)
 =
 \bigcup\{J:J\text{ is a certified local proper-access arc over }
              \widetilde I\}.
\tag{6.4}
\]

### Theorem 6.2
(`TERMINAL_PROPER_ACCESS_CHANNEL_ATLAS`)

The set \(\mathcal E_{\rm pr}(\widetilde I)\) is open in the source
ideal circle.  Its connected components are pairwise-disjoint open
intervals, except that the whole ideal circle is allowed when
\(\mathcal E_{\rm pr}(\widetilde I)\) is the whole circle.  In either
case they form an at-most-countable channel set.

Every point of a channel has a two-flank ambient-compatible collar.
Every compact subarc of a channel admits a finite subdivision into
subarcs carrying such collars.  Conversely, every two-flank collar
satisfying Definition 6.1 has its base arc in exactly one channel.

The theorem does not assert that the boundary extension is globally
injective on an entire channel, that there is one channel, or that all
proper KKL paths with ends in one channel are equivalent.

#### Proof

Equation (6.4) is a union of open arcs, so it is open.  A proper open
subset of a second-countable circle is a disjoint union of at most
countably many open intervals: assign to each component a distinct
member of a fixed countable basis contained in it.  If it is the whole
circle, it has one component.

The local collar assertion is the definition.  A compact subarc of one
component is covered by finitely many defining arcs \(J\); subdividing
at finitely many endpoints gives the asserted finite collar atlas.  A
certified collar base is contained in (6.4), and connectedness places it
in one component. \(\square\)

Thus the terminal end multiplicity has a canonical coarse coordinate
\[
 \nu_*(\widetilde I)
 =
 \#\pi_0\mathcal E_{\rm pr}(\widetilde I)
 \in
 \{0,1,2,\ldots,\aleph_0\}.
\tag{6.5}
\]
This count is neither the number of connected inverse-trace components
nor the number of arbitrary proper paths.  Lollipop-type path
multiplicity can remain inside one channel and must still be retained
by the full restriction response.

### Theorem 6.3
(`TERMINAL_LOCAL_CHANNEL_TO_KL_WELDING`)

Work in one fixed terminal alignment record and retain the notation
\[
 e:\widetilde A\hookrightarrow\widetilde M,
 \qquad
 \Phi_i:\widetilde A\xrightarrow{\cong}\widehat A_i
\tag{6.6}
\]
from Theorem 5.1.  Let bars denote intrinsic prime-end
compactifications.  The conformal isomorphism \(\Phi_i\) has a canonical
orientation-preserving prime-end extension
\[
 \overline\Phi_i:
 \overline{\widetilde A}^{\,\operatorname{PE}}
 \xrightarrow{\cong}
 \overline{\widehat A_i}^{\,\operatorname{PE}}.
\tag{6.7}
\]

Let \(J\) be one certified local proper-access arc from Definition 6.1,
let
\[
 h_J=E_J|_J:
 J\xrightarrow{\cong}I_J\subset\widetilde I,
\tag{6.8}
\]
and suppose the fixed KL marking verifies
\[
 L_J:=\overline\Phi_i(J)\subset L_i,
\tag{6.9}
\]
where \(L_i\) is the relative interior of one declared KL
\(\eta\)- or \(\xi\)-side contained in
\(\partial^{v_*}\Psi(Y_B)\).  In particular, \(J\) crosses no KL ideal
vertex or central/tile seam.  Assume also that the declared native
orientation on \(\widetilde I\) agrees with the boundary orientation
induced by
\(\overline{\widetilde M}^{\,\operatorname{PE}}\), and that the declared
orientation on \(L_i\) agrees with the boundary orientation induced by
\(\overline{\widehat A_i}^{\,\operatorname{PE}}\).  Then
\[
 W_{i,J}:I_J\longrightarrow L_J,
 \qquad
 W_{i,J}
 =
 \overline\Phi_i|_J\circ h_J^{-1},
\tag{6.10}
\]
is an orientation-preserving homeomorphism.

For every nondegenerate compact interval \(I_0\Subset I_J\), there is an
ambient-ledger-free closed Jordan subquadrilateral \(Q_0\) based on
\(J_0=h_J^{-1}(I_0)\) such that
\[
\begin{aligned}
 C_M&=e(Q_0^\circ)\subset\widetilde M,\\
 C_{\rm KL}&=\Phi_i(Q_0^\circ)\subset\widehat A_i,\\
 \mathcal W_{I_0}
 &=
 \Phi_i\circ(e|_{Q_0^\circ})^{-1}:
 C_M\xrightarrow{\cong}C_{\rm KL}
\end{aligned}
\tag{6.11}
\]
is a conformal collar welding.  More precisely,
\[
 \overline{\mathcal W}_{I_0}
 =
 \overline\Phi_i|_{Q_0}
 \circ
 (E_J|_{Q_0})^{-1}:
 E_J(Q_0)\xrightarrow{\cong}\overline\Phi_i(Q_0)
\tag{6.12}
\]
is a homeomorphism of marked compactified quadrilaterals.  It equals
\(W_{i,J}\) on \(I_0\), carries the two flanks to distinct flanks in
the same cyclic order, and preserves the modulus for the marked
base/opposite-side pair.

More precisely, let \(J_1,J_2\) be certified arcs in the same fixed
alignment and tile.  If \(J_{12}\) is a nonempty source subarc of
\(J_1\cap J_2\) and
\[
 E_{J_1}(J_{12})=E_{J_2}(J_{12})=:I_{12},
\tag{6.13}
\]
then their welding maps agree on \(I_{12}\).

#### Proof

Both \(\widetilde A\) and \(\widehat A_i\) are conformal disks.
Conjugating \(\Phi_i\) by disk uniformizations gives a disk
automorphism, which extends uniquely to an orientation-preserving
homeomorphism of the unit circle.  Conjugating back proves (6.7)
without any local-connectivity assumption on \(K\) or \(\mathcal T\).

Definition 6.1 makes \(h_J\) a homeomorphism and makes \(E_J\) a
topological embedding on its one-sided
quadrilateral.  Thus (6.10) is a homeomorphism.  Holomorphic maps
preserve the interior orientation.  On the declared interior side,
\(E_J\) therefore preserves the induced boundary-arc orientation; so
does (6.7).  The two explicit orientation agreements in the statement
show that (6.10) preserves the declared interval orientation and every
finite cyclically ordered marking on it.

For \(I_0\Subset I_J\), compactness gives
\(J_0=h_J^{-1}(I_0)\Subset J\).  Choose a smaller closed Jordan
subquadrilateral \(Q_0\) inside the certificate quadrilateral and based
on \(J_0\).  Clause 4 of Definition 6.1 gives the precise
ambient-ledger-free condition
\[
 E_J(Q_0)\cap
 \overline{\widetilde{\mathscr F}}^{\,\operatorname{PE}(\widetilde M)}
 =\varnothing.
\]
The maps
\[
 e|_{Q_0^\circ}
 \quad\text{and}\quad
 \Phi_i|_{Q_0^\circ}
\]
are conformal embeddings.  Hence (6.11) is conformal.  Because both
\(E_J|_{Q_0}\) and \(\overline\Phi_i|_{Q_0}\) are topological
embeddings, their composition in (6.12) is a homeomorphism of the
marked compactified quadrilaterals.  Its base restriction is (6.10),
and its flank restrictions prove distinctness and order without
inferring an ambient extension from the interior map alone.  Mark
\(Q_0\) by the ordered sides
\[
 (\text{base},\text{right flank},\text{opposite side},\text{left flank})
\]
and define its modulus using curves joining the base to the opposite
side.  Conformal invariance of extremal length then gives equality of
the correspondingly marked moduli; no reciprocal convention is left
ambiguous.

For (6.13), take a compact subarc of \(J_{12}\).  Interior points in the
overlap of the two one-sided source collars tend to every prime end of
that subarc.  Both certificate extensions equal the physical inclusion
\(e\) on those interior points.  Continuity into the Hausdorff
prime-end disk gives
\(E_{J_1}=E_{J_2}\) on \(J_{12}\).  Both welding formulas are therefore
\(\overline\Phi_i\circ(E_{J_r}|_{J_{12}})^{-1}\), so they agree on
\(I_{12}\). \(\square\)

The locality is essential.  The theorem does not prove that
\(\mathcal E_{\rm pr}(\widetilde I)\) covers all of
\(\widetilde I\), that distinct channels have disjoint native images,
or that local maps continue across a KL vertex or central/tile seam.
It gives no positive lower modulus at channel endpoints and no
whole-side or uncertified-channel end-proper factorization through a
final-root enlargement.  Theorem 7.2 below proves the local
certified-channel factorization; the whole-side assertions remain.

### Theorem 6.4
(`TERMINAL_KL_FINITE_SIDE_REFINEMENT`)

Let \(J\) be any certified local proper-access arc in a fixed terminal
alignment.  In the strip normalization of Theorem 11.4, let
\[
 \mathscr V_i=\{a_i,b_i,c_-,c_+\}
 \subset\partial_{\rm PE}\widehat A_i
\]
be the (possibly coincident) finite central endpoints and the two
deck-limit endpoints.  Then
\[
 \mathscr Z_{i,J}
 =
 J\cap\overline\Phi_i^{-1}(\mathscr V_i)
\tag{6.14}
\]
is finite.  Every connected component \(J_\alpha\) of
\(J\setminus\mathscr Z_{i,J}\) is again a certified local
proper-access arc after restricting its quadrilateral, and
\[
 \overline\Phi_i(J_\alpha)
\tag{6.15}
\]
lies in exactly one of
\[
 \lambda_i^\circ,\qquad
 \rho_i^-,\qquad
 \rho_i^+,\qquad
 \omega_i^\circ.
\tag{6.15a}
\]
There are
at most
\[
 1+\#\mathscr Z_{i,J}
\tag{6.16}
\]
such components.

Consequently:

1. a component on the tile-tagged \(\eta/\xi\) occurrence belonging to
   \(\partial^{v_*}\Psi(Y_B)\) has the local welding of Theorem 6.3;
2. a component on \(\lambda_i^\circ\), or on the wrong tagged
   \(\rho_i^\pm\), is an explicit exposed-side obstruction; and
3. a component on \(\omega_i^\circ\) is the explicit
   \(O_{\rm cent}\) central/buried obstruction.

The cut points in \(\mathscr Z_{i,J}\) retain their finite-incidence or
infinite-wrapping labels and are not discarded.

#### Proof

The prime-end extension \(\overline\Phi_i\) is a homeomorphism by
(6.7).  Therefore the preimage of the finite set
\(\mathscr V_i\) is finite, proving the first assertion.  Removing
\(\#\mathscr Z_{i,J}\) points from an interval produces at most one
more connected component than the number removed, proving (6.16).

The exact intrinsic ideal-circle decomposition (11.21) says that
removing \(\mathscr V_i\) leaves precisely the four sets in (6.15a).
The connected set \(\overline\Phi_i(J_\alpha)\) avoids every cut point,
so it lies in one such component, and in no second one.  This is where
the central interval \(\omega_i^\circ\) is retained rather than hidden
inside a false named-side exhaustion.

Restrict the certificate quadrilateral \(Q_J\) between the vertical
crosscuts over the endpoints of \(J_\alpha\).  The resulting one-sided
subquadrilateral has base-side relative interior \(J_\alpha\).
Restriction preserves the topological embedding, the two-flank order,
and the ambient-ledger avoidance in Definition 6.1.  Thus
\(J_\alpha\) is certified.  The final assertion is exactly
Theorem 6.3 on the components with the required tagged KL side label;
the other cases are the displayed source-locked obstructions.
\(\square\)

## 7. Exact final-root cover decomposition

Let
\[
 \mathcal T\subset\mathcal T^+\subset K
 \tag{7.1}
\]
be an authorized connected compact terminal-carrier enlargement in the
same disk \(\Omega\).  Put
\[
 M^+=\Omega\setminus\mathcal T^+.
\]

### Theorem 7.1
(`TERMINAL_FINAL_ROOT_COVER_OBSTACLE_DECOMPOSITION`)

All three continua in (7.1) are full.  In the universal cover
\(p_{\mathcal T}:\widetilde M\to M\), the set
\[
 \widetilde M^+
 =
 p_{\mathcal T}^{-1}(M^+)
\tag{7.2}
\]
is connected and is the universal cover of \(M^+\).  Moreover
\[
 \widetilde A
 \subset
 \widetilde M^+
 \subset
 \widetilde M
\tag{7.3}
\]
and
\[
\begin{aligned}
 \widetilde M\setminus\widetilde A
 &=
 p_{\mathcal T}^{-1}(K\setminus\mathcal T),\\
 \widetilde M\setminus\widetilde M^+
 &=
 p_{\mathcal T}^{-1}(\mathcal T^+\setminus\mathcal T),\\
 \widetilde M^+\setminus\widetilde A
 &=
 p_{\mathcal T}^{-1}(K\setminus\mathcal T^+),
\end{aligned}
\tag{7.4}
\]
with the disjoint decomposition
\[
 p_{\mathcal T}^{-1}(K\setminus\mathcal T)
 =
 p_{\mathcal T}^{-1}(\mathcal T^+\setminus\mathcal T)
 \sqcup
 p_{\mathcal T}^{-1}(K\setminus\mathcal T^+).
\tag{7.5}
\]

Consequently no unrecorded **interior cover obstacle** is born by the
enlargement.  Ideal-channel survival, ambient prime-end injectivity, and
end-proper factorization through \(\widetilde M^+\) remain separate.

#### Proof

Theorem 3.1 applies to \(\mathcal T^+\subset K\), so all continua in
(7.1) are full.  The inclusion
\[
 M^+\hookrightarrow M
\]
induces an isomorphism on \(\pi_1\) by the common outer-generator proof
of Theorem 4.2.  The covering-space argument of Theorem 5.1 therefore
shows that (7.2) is connected and universal.

The inclusions in (7.3) follow by reversing the inclusions of the
removed continua.  Each equality in (7.4) is the inverse-image identity
\[
 p^{-1}(X\setminus Z)=p^{-1}(X)\setminus p^{-1}(Z)
\]
inside the relevant domain.  Finally,
\[
 K\setminus\mathcal T
 =
 (\mathcal T^+\setminus\mathcal T)
 \sqcup
 (K\setminus\mathcal T^+)
\]
is a disjoint set decomposition; applying \(p_{\mathcal T}^{-1}\)
gives (7.5). \(\square\)

### Theorem 7.2
(`TERMINAL_CERTIFIED_CHANNEL_FINAL_ROOT_STABILITY`)

Let \(J\) be a certified local proper-access arc for
\(\widetilde A\hookrightarrow\widetilde M\), with certificate
quadrilateral \(Q_J\) satisfying Definition 6.1, and let
\(\mathcal T^+\) be any authorized enlargement in (7.1).  Then the
same physical collar factors through the intermediate cover:
\[
 \widetilde A
 \xhookrightarrow{\ e^+\ }
 \widetilde M^+
 \xhookrightarrow{\ r^+\ }
 \widetilde M.
\tag{7.6}
\]
More precisely, there is an ideal arc \(I_J^+\) of
\(\widetilde M^+\) and local prime-end extensions on \(Q_J\) such that
\[
 J\xrightarrow[\cong]{\ \overline e^{+}\ } I_J^+
 \xrightarrow[\cong]{\ \overline r^{+}\ } I_J,
 \qquad
 E_J|_J
 =
 \overline r^{+}|_{I_J^+}\circ\overline e^{+}|_J.
\tag{7.7}
\]
Both maps preserve the two distinct flanks and their cyclic order.
Consequently the local KL welding from Theorem 6.3 is unchanged after
factorization through \(\widetilde M^+\), and its quadrilateral modulus
is unchanged.

#### Proof

By Definition 6.1, the ambient prime-end closure of the image collar is
disjoint from the complete lifted obstacle ledger, which contains
\[
 \widetilde M\setminus\widetilde A
 =
 p_{\mathcal T}^{-1}(K\setminus\mathcal T).
\tag{7.8}
\]
The component removed in passing from \(\widetilde M\) to
\(\widetilde M^+\) is, by (7.4),
\[
 \widetilde M\setminus\widetilde M^+
 =
 p_{\mathcal T}^{-1}(\mathcal T^+\setminus\mathcal T)
 \subset
 p_{\mathcal T}^{-1}(K\setminus\mathcal T).
\tag{7.9}
\]
Hence a prime-end neighborhood of the closed image quadrilateral is
disjoint from (7.9).  On that neighborhood the two physical domains
\(\widetilde M^+\) and \(\widetilde M\) coincide.

The crosscut chains in this common Jordan neighborhood therefore
define the same local prime ends in both domains.  Regard the embedded
image of \(Q_J^\circ\) first as a collar in \(\widetilde M^+\); its base
defines \(I_J^+\).  Regard it next as a collar in \(\widetilde M\); its
base is \(I_J\).  The identity on the common neighborhood gives both
homeomorphisms in (7.7), including the factorization.  Because the
physical quadrilateral and its oriented flanks were not changed,
distinctness and cyclic order persist.

The KL side is still \(\Phi_i(Q_J^\circ)\).  Thus the two formulas for
the welding, before and after enlargement, are the same conformal map
\[
 \Phi_i\circ(e|_{Q_J^\circ})^{-1}.
\]
The physical quadrilateral is identical, so its modulus is identical.
\(\square\)

The scope is deliberately local.  The theorem proves final-root
stability for every **already certified** obstacle-separated channel.
It does not prove that such a channel exists at every point of the
whole native interval, nor that an uncertified proper composite factors
properly.  Properness of a composite alone still does not prove
properness of both factors.

## 8. Adversarial boundary

1. **Connected called full without empty interior.**  Invalid in
   general.  Theorem 3.1 uses periodic repulsion exactly through
   \(\operatorname{int}K=\varnothing\).
2. **A cover component called a proper-path class.**  Rejected.
   Theorem 5.1 proves connectedness of one pulled-back cover; the
   lollipop and exponential examples still permit multiple proper
   restrictions or end channels inside it.
3. **An unbased cover called canonical.**  Rejected.  Equation (5.4)
   is canonical only after the two lifted basepoints are supplied.
4. **Subgroup alignment called end-properness.**  Rejected.  No
   prime-end or proper-path assertion occurs in the proof.
5. **Terminal theorem globalized through the Wave horizon.**  Rejected.
   Every later stage still needs its own common localization, carrier
   fullness or replacement hypothesis, and compatibility square.

## 9. Fixed terminal base-record constructor

### Theorem 9.1
(`TERMINAL_LOCAL_KL_KKL_ALIGNMENT_RECORD`, conditional constructor)

Let \(Y_B\) have KL depth \(m\).  Suppose a frozen terminal proof-use
binder supplies:

1. one actual oriented proper target path
   \[
   \gamma_*^{\mathcal T}
   \subset \mathbf U^m\setminus\mathcal T
   \]
   with its carrier-side/fiber endpoint data; and
2. a complete closed, or locally finite closed, obstacle ledger
   \(\mathscr F_*\).

Then the terminal stage has a fixed marked alignment record consisting
of:

- the common disk \(\mathbf U^m\), the continua
  \(\mathcal T\subset K\), and the physical inclusion
  \[
  \mathbf U^m\setminus K
  \hookrightarrow
  \mathbf U^m\setminus\mathcal T;
  \]
- the target path and endpoint data from the binder;
- every KL central complementary component \(Y_i\), its already
  selected overlap embedding \(e_i\), and the corresponding tile
  \(\widehat A_i\);
- for every proof-used tile, a paired choice
  \[
    \widetilde a_i\in\widetilde A,
    \qquad
    \widehat a_i\in\widehat A_i
  \]
  over one physical central basepoint \(a_i\), with
  \(\widehat a_i=e_i(a_i)\) on the retained central/tile seam;
- KL's marked external ray of angle \(0\), its orientation from the
  outer equipotential to the inner prime end, and its two flank labels,
  retained as the terminal outer seam;
- the identity relative-subgroup comparison and the based universal
  cover isomorphism of Theorem 5.1; and
- the actual central/tile seam equalizers and the supplied obstacle
  ledger.

The record is fixed marked data.  The theorem does not assert
independence from changing KL's selected \(e_i\), changing a lifted
basepoint by a deck transformation, or replacing the binder path.

#### Proof

The geometric puzzle \(Y_B\) and the terminal native carrier are built
for the same quadratic-like restriction: KL place \(Y_B\) and \(K\) in
\(\mathbf U^m\), while
\(\mathcal T\subset K\).  Hence the displayed inclusion is an actual
map in one common disk.

The frozen binder supplies the target path, its orientation and endpoint
record, and \(\mathscr F_*\); none is reconstructed from a label.  KL's
glued definition of \(\Psi(Y_B)\) supplies the finite central components
\(Y_i\), the selected embeddings \(e_i:Y_i\to\widehat A_i\), and the
central/tile seam identifications.  Retain those choices exactly.  In
every proof-used tile choose one physical central basepoint and retain
both its lift in the pulled cover and its seam-matched image in the KL
tile.  Retain KL's marked ray of angle \(0\) and its two oriented banks;
Theorem 11.2 proves that this field normalizes the source cut-and-stack
deck coordinate once the paired target lift is retained.

Theorems 4.2 and 5.1 identify the inclusion subgroups and give the unique
covering isomorphism after the paired basepoints are fixed.  Collecting these
source-supplied and retained fields gives the stated marked record.
\(\square\)

This theorem is conditional on the **actual** frozen binder and complete
closed obstacle ledger.  It constructs no binder and proves no proper
restriction.  Its role is to remove a separate terminal stage-typing
ambiguity once those upstream inputs are present.

## 10. Exact next interface

The terminal local alignment record may now set
\[
 H_s=H_t=\mathbb Z
\quad\text{under }j_*,
 \qquad
 \chi_{\rm cover\ component}=0.
\tag{10.1}
\]
The remaining response is internal to the one connected aligned cover:
for each actual bound Wave path, retain every KKL proper restriction,
its two ideal ends, based tile/deck presentation, obstacle record, and
ambient prime-end survival.  Proving a unique positive protected collar,
or charging all additional channels by a universal response, is the
next analytic task.

## 11. Terminal outer-seam deck normalization

The based uniqueness in Theorem 5.1 still leaves a practical question:
how should the integer deck coordinate be normalized without making an
unrecorded choice of a lift?  At the terminal polynomial puzzle there is
a natural answer once one of the marked external rays is retained as an
oriented seam.  The construction below is topological and applies to any
doubly connected plane domain with such a seam.

The terminal specialization uses KL `kingdom.tex`, lines 21--28: the
external rays form the marked foliation of the complement of \(K\), and
the ray of angle \(0\) lands at the nondividing fixed point \(\beta\).
It uses KL `psiql.tex`, lines 117--147, only for the fact that each
\(\widehat A_i\) is a selected copy of the universal cover of the same
base annulus.

### Definition 11.1 -- oriented outer seam

Let \(A\) be an oriented doubly connected plane domain whose two
complementary continua are nondegenerate.  Assume its prime-end
compactification \(\overline A^{\,\mathrm{pe}}\) is a closed annulus.
An **oriented outer seam** is an embedding
\[
 \sigma:[0,1]\longrightarrow\overline A^{\,\mathrm{pe}}
\tag{11.1}
\]
such that

1. \(\sigma((0,1))\subset A\);
2. \(\sigma(0)\) belongs to the outer prime-end circle and
   \(\sigma(1)\) belongs to the inner prime-end circle; and
3. no other point of \(\sigma\) belongs to the prime-end boundary.

The seam is oriented from the outer end to the inner end.  The
orientation of \(A\), together with this direction, labels the two
flanks of the cut seam as \(\sigma^L\) and \(\sigma^R\).  With the
standard oriented-intersection convention, a transverse path has
positive intersection with \(\sigma\) precisely when it crosses from
\(\sigma^L\) to \(\sigma^R\).

Cut \(\overline A^{\,\mathrm{pe}}\) open along \(\sigma\), and denote the
resulting closed topological disk by \(D_\sigma\).  Its boundary contains
the two copies \(\sigma^L,\sigma^R\).

### Theorem 11.2
(`TERMINAL_OUTER_SEAM_DECK_NORMALIZATION`)

Under Definition 11.1, take copies \(D_k\), \(k\in\mathbb Z\), of the
interior of \(D_\sigma\), with the appropriate open seam flanks retained,
and glue
\[
 \sigma^L_k\sim\sigma^R_{k+1}
 \qquad(k\in\mathbb Z).
\tag{11.2}
\]
Let \(\widetilde A_\sigma\) be the resulting surface and let
\[
 p_\sigma:\widetilde A_\sigma\longrightarrow A
\tag{11.3}
\]
be the map induced by regluing the cut.  Then:

1. \(p_\sigma\) is the universal covering of \(A\).
   With the complex structure pulled back from \(A\), it is the universal
   holomorphic covering.
2. The copy \(D_0\) is a distinguished zero sheet, and
   \[
    T(D_k)=D_{k+1}
   \tag{11.4}
   \]
   defines the positive generator of its deck group.
3. If a path \(\gamma\) in \(A\), with endpoints off \(\sigma\), is
   transverse to \(\sigma\) and has finitely many crossings, then its
   lift beginning in \(D_0\) ends in \(D_{N(\gamma)}\), where
   \[
    N(\gamma)
    =
    \sum_{x\in\gamma\cap\sigma}\epsilon_x,
    \qquad
    \epsilon_x=
    \begin{cases}
      +1,&\gamma\text{ crosses from the \(L\)-flank to the \(R\)-flank},\\
      -1,&\gamma\text{ crosses from the \(R\)-flank to the \(L\)-flank}.
    \end{cases}
   \tag{11.5}
   \]
   Thus the deck phase is the signed seam-crossing number.
4. Let \(\widehat A_i\to A\) be a KL universal-cover tile.  Suppose a
   connected nonempty open set \(Y_i^\circ\subset A\setminus\sigma\) and
   one of its KL lifts
   \[
    e_i^\circ:Y_i^\circ\longrightarrow\widehat A_i
   \tag{11.6}
   \]
   are retained.  There is a unique covering isomorphism
   \[
    \Phi_i:\widetilde A_\sigma\longrightarrow\widehat A_i
   \tag{11.7}
   \]
   that carries the copy of \(Y_i^\circ\) in \(D_0\) to
   \(e_i^\circ(Y_i^\circ)\) with the stated lift.  In particular, no
   nontrivial deck translate also satisfies this normalization.

For the terminal KL base
\[
 A=\mathbf U^m\setminus K,
\tag{11.8}
\]
the external ray of angle \(0\), truncated between the outer
equipotential and its landing prime end at \(\beta\), is an oriented
outer seam.  Retaining this ray and its two flank labels fixes the
integer deck coordinate in the source cut-and-stack model.  For each
proof-used terminal tile, the additional retained KL lift
\(e_i^\circ\) fixes the comparison with that tile by (11.6)--(11.7).

#### Proof

By the proper-arc classification in an annulus, there is an
orientation-preserving homeomorphism of pairs
\[
 h:
 \bigl(\overline A^{\,\mathrm{pe}},\sigma\bigr)
 \longrightarrow
 \bigl(S^1\times[0,1],\{1\}\times[0,1]\bigr)
\tag{11.9}
\]
that carries the oriented seam to the displayed radial spanning arc
with the corresponding left/right banks.  In particular, cutting along
\(\sigma\) gives a closed disk, as asserted in Definition 11.1.

Lift \(h\) to the cut copies before performing (11.2).  It identifies
the resulting cut-and-stack surface, including its two finite lifted
boundary lines but omitting the two deck-limit prime ends, with
\[
 \mathbb R\times[0,1],
\qquad
 (s,t)\longmapsto(e^{2\pi i s},t),
\tag{11.10}
\]
and identifies \(D_k\) with the strip cell
\([k,k+1]\times[0,1]\), with the usual convention that a common seam
bank is counted only once.  After deleting the two prime-end boundary
lines, (11.3) is therefore conjugate to the standard covering
\[
 \mathbb R\times(0,1)\longrightarrow S^1\times(0,1).
\tag{11.11}
\]
This simultaneously proves local finiteness of the gluing, the covering
property, and simple connectivity of \(\widetilde A_\sigma\).  Hence
\(p_\sigma\) is the universal cover.
There is a unique complex structure on \(\widetilde A_\sigma\) for which
the covering charts pulled back from \(A\) are holomorphic.  With this
structure, \(p_\sigma\) is holomorphic and every covering isomorphism in
Item 4 is conformal.

Translation of the sheet labels preserves the gluing, giving the deck
map \(T\).  A generator of \(\pi_1(A)\) crosses the seam once with
positive sign, so \(T\) is primitive and positive.  This proves Items
1--2.

Away from its finitely many transverse crossings, a lift of \(\gamma\)
stays in one cut sheet.  At a positive crossing it passes through
\(\sigma_k^L=\sigma_{k+1}^R\), increasing the sheet label by one; at a
negative crossing it decreases the label by one.  Induction over the
ordered crossings proves (11.5).  The same formula is invariant under a
homotopy through paths transverse to the seam except for creation or
annihilation of oppositely signed crossing pairs.

The copy of \(Y_i^\circ\) in \(D_0\) and the retained lift
\(e_i^\circ\) specify the image of one point, hence a based isomorphism
between two universal covers of \(A\).  Based uniqueness of universal
covers gives (11.7).  Any two covering isomorphisms differ by a deck
transformation.  A nonzero deck transformation moves \(D_0\) to
\(D_k\), so it cannot retain the stated lift of the open set
\(Y_i^\circ\).  This proves Item 4.

Finally, KL's marked external ray of angle \(0\) lands at the
nondividing fixed point \(\beta\).  Its segment in
\(\mathbf U^m\setminus K\) is simple and runs from the outer
equipotential to the inner prime-end circle.  It therefore satisfies
Definition 11.1 and gives the terminal specialization. \(\square\)

### Theorem 11.3
(`TERMINAL_SEAM_LIFT_END_PROPERNESS`)

KKL `waves-with-Misha.tex`, lines 394--406, fixes the convention used
here: a proper path in a Riemann surface \(V\) is a map
\(\delta:(0,1)\to V\) that extends continuously to the KKL ideal
closure, with both endpoints in the ideal boundary.  For the annulus
\(A\) of Definition 11.1, the KKL ideal closure is canonically
identified with the prime-end closed annulus by the natural,
identity-extending homeomorphism
\[
 \Theta_A:
 A\cup\partial_{\mathrm i}^{\mathrm{KKL}}A
 \xrightarrow{\ \cong\ }
 \overline A^{\,\mathrm{pe}},
\]
with the marked outer and inner boundary components preserved.

Let
\[
 \delta:(0,1)\longrightarrow A
\tag{11.12}
\]
be KKL proper.  Fix \(t_0\in(0,1)\) and a seam-normalized lift
\(\widetilde x_0\in p_\sigma^{-1}(\delta(t_0))\), and let
\(\widetilde\delta\) be the unique lift satisfying
\(\widetilde\delta(t_0)=\widetilde x_0\).  Under the strip
identification in (11.10)--(11.11), the following hold.

1. The base path has a continuous prime-end extension
   \[
    \overline\delta:
    [0,1]\longrightarrow\overline A^{\,\mathrm{pe}},
    \qquad
    \overline\delta(\{0,1\})
    \subset\partial_{\mathrm{pe}}A.
   \tag{11.13}
   \]
2. The lifted path has a unique continuous extension
   \[
    \overline{\widetilde\delta}:
    [0,1]\longrightarrow\mathbb R\times[0,1]
   \tag{11.14}
   \]
   through the closed-annulus covering
   \[
    \overline p_\sigma:
    \mathbb R\times[0,1]\longrightarrow S^1\times[0,1],
    \qquad
    (s,t)\longmapsto(e^{2\pi i s},t).
   \tag{11.15}
   \]
   Its endpoint values have the form
   \[
    \overline{\widetilde\delta}(j)=(s_j,b_j),
    \qquad
    s_j\in\mathbb R,\quad b_j\in\{0,1\},
    \quad j=0,1.
   \tag{11.16}
   \]
   In particular, both real deck coordinates are finite.
   Here \(\mathbb R\times[0,1]\) is the finite-boundary partial
   compactification of the open strip; its full prime-end disk has the
   two additional deck-limit points used in Item 3.
3. The map
   \(\widetilde\delta:(0,1)\to\mathbb R\times(0,1)\)
   is proper.  In the two-ended prime-end compactification of the strip,
   neither tail lands at either deck-limit point \(c_-\) or \(c_+\)
   represented by \(s\to-\infty\) or \(s\to+\infty\).
4. If the frozen KL lift \(e_i^\circ\) supplies the comparison
   \(\Phi_i:\widetilde A_\sigma\to\widehat A_i\) from Theorem 11.2,
   then the prime-end extension of \(\Phi_i\) carries both finite
   endpoints in (11.16) to well-defined endpoint prime ends of the KL
   tile.  The only remaining endpoint assertion is the separate marked
   statement that those endpoint prime ends belong to the declared KL
   access labels.

#### Proof

A doubly connected plane domain with two nondegenerate complementary
continua is conformally equivalent to a round annulus
\[
 A_r=\{z:r<|z|<1\},
 \qquad 0<r<1.
\tag{11.17}
\]
The conformal equivalence extends, by the definition of prime ends, to a
homeomorphism from \(\overline A^{\,\mathrm{pe}}\) to the closed round
annulus.  On the other hand, the KKL ideal boundary is defined from the
universal disk cover as
\((\partial\mathbb D\setminus\Lambda)/\Delta\).  For a finite-modulus
annulus, the deck group is infinite cyclic hyperbolic; its complement of
the two limit points has two invariant intervals, and their quotients
are the two boundary circles of the same closed round annulus.
Consequently the KKL ideal closure and the prime-end compactification
are identified by the identity-on-\(A\), outer/inner-label-preserving
map \(\Theta_A\) obtained through a round-annulus uniformization.  If two
uniformizations are used, the resulting maps agree on the dense interior
\(A\); continuity and the Hausdorff property of the target
compactification make them agree on the boundary as well.  Thus
\(\Theta_A\) is independent of the presentation.
The defining KKL properness extension is therefore exactly (11.13).

The map in (11.15) is a covering of topological manifolds with boundary.
Apply the path-lifting theorem to \(\overline\delta|_{[t_0,1]}\) with
initial value \(\widetilde x_0\), and apply it to the reversed path
\overline\delta|_{[0,t_0]}\) with the same initial value.  Uniqueness
makes the two lifts agree at \(t_0\), and their union gives (11.14).
On \((0,1)\) it agrees with \(\widetilde\delta\) by uniqueness of the
ordinary path lift.  Since the base endpoints in (11.13) lie on the
boundary circles, their lift endpoints lie on the boundary lines of the
closed strip.  Every point of the closed strip has finite first
coordinate.  This proves (11.16).

Let \(C\Subset\mathbb R\times(0,1)\).  The set
\(\overline{\widetilde\delta}^{-1}(C)\) is closed in \([0,1]\), and it
misses \(0\) and \(1\) by (11.16).  Hence it is a compact subset of
\((0,1)\).  Thus \(\widetilde\delta\) is proper.  More strongly, the
continuous image of the compact interval \([0,1]\) under
\(\overline{\widetilde\delta}\) is a compact subset of
\(\mathbb R\times[0,1]\), so its first coordinate is bounded.  It cannot
accumulate at either of the two points \(c_\pm\) added in the
two-ended prime-end compactification of the strip.  This proves Item 3.

Finally, \(\Phi_i\) is a conformal isomorphism between simply connected
covering surfaces.  Its canonical prime-end extension is a
homeomorphism, so it maps each finite endpoint in (11.16) to one
well-defined KL endpoint prime end.  Neither covering theory nor the
seam crossing coordinate identifies that endpoint with a particular KL
\(\eta\)-side, \(\xi\)-side, or vertex-access interval.  That membership
is precisely the declared access-label check retained in Item 4.
\(\square\)

### Theorem 11.4
(`TERMINAL_KL_FINITE_ENDPOINT_FIVE_WAY_CLASSIFICATION`)

Fix a tagged terminal tile \(\widehat A_i\).  Use KL's strip
uniformization
\[
 \Pi_i=\{z:0<\operatorname{Im}z<h_i\}
\tag{11.18}
\]
so that the finite-coordinate upper boundary is the \(O\)-boundary and
a compact interval
\[
 \omega_i=[a_i,b_i]\subset\mathbb R,
 \qquad a_i\le b_i,
\tag{11.19}
\]
on the lower boundary represents \(K_{Y_B}\cap\partial A_i\).  Let
\[
\begin{aligned}
 \lambda_i^\circ&=\mathbb R+i h_i,\\
 \rho_i^-&=(-\infty,a_i),\\
 \rho_i^+&=(b_i,\infty),\\
 \omega_i^\circ&=(a_i,b_i).
\end{aligned}
\tag{11.20}
\]
The retained KL seam/incidence marking labels
\(\rho_i^-\) and \(\rho_i^+\) as the two exposed
\(\xi/\eta\) occurrences; the theorem does not guess which sign has
which name if that marking is omitted.  The central interior
\(\omega_i^\circ\) is empty when \(a_i=b_i\).  Write \(c_-,c_+\) for
the two deck-limit prime ends of the strip.

The intrinsic tile ideal circle has the disjoint decomposition
\[
 \partial_{\rm PE}\widehat A_i
 =
 \lambda_i^\circ
 \sqcup\rho_i^-
 \sqcup\rho_i^+
 \sqcup\omega_i^\circ
 \sqcup\{a_i,b_i,c_-,c_+\}.
\tag{11.21}
\]
Let \((i,\widehat a)\) be either endpoint supplied by Theorem 11.3.
Since \(\widehat a\notin\{c_-,c_+\}\), exactly one of five finite cases
holds:

1. \(P_O\): \(\widehat a\in\lambda_i^\circ\);
2. \(P_J^-\): \(\widehat a\in\rho_i^-\);
3. \(P_J^+\): \(\widehat a\in\rho_i^+\);
4. \(O_{\rm cent}\): \(\widehat a\in\omega_i^\circ\);
5. \(P_{\rm inc}\): \(\widehat a\in\{a_i,b_i\}\), with every tagged
   finite vertex incidence retained.

For the selected terminal vertex \(v_*=v_{i_*}\), the desired access
predicate is the tagged test
\[
 (i,\widehat a)\in
 \bigl(\{i_*\}\times\eta_{i_*}\bigr)
 \sqcup
 \bigl(\{i_*+1\}\times\xi_{i_*+1}\bigr).
\tag{11.22}
\]
The two occurrences are retained before gluing, even if their physical
images meet at \(v_*\).  The \(\eta/\xi\) arcs in (11.22) are the
closed marked arcs, including their retained finite endpoint
incidences.

Define \(\operatorname{Inc}_{\rm KL}(i,\widehat a)\) as follows.  On a
relative-interior named side it is the singleton containing that
tile-tagged side occurrence; on \(\omega_i^\circ\) it is empty; and at
\(a_i\) or \(b_i\) it is the finite set of tagged
\(\lambda/\xi/\eta\) endpoint germs identified with that occurrence by
the frozen full-pseudo-piece gluing record.  Thus a failure certificate
records
\[
 (i,\widehat a,(s_j,b_j),
   \operatorname{case}_{11.4}(\widehat a),
   \operatorname{Inc}_{\rm KL}(i,\widehat a)).
\tag{11.23}
\]
The theorem classifies every finite endpoint, but it does not prove
that the actual binder endpoint avoids \(\omega_i^\circ\), lies on a
particular exposed side, or has the desired tile tag.

#### Proof

KL `psiql.tex`, lines 118--123, identifies every tile
\(\widehat A_i\) with a copy of the universal cover of the same
annulus, without a bidepth restriction.  Hence it has a horizontal
strip uniformization.  KL `psiql.tex`, lines 231--244, supplies the
outer arc \(\lambda_i\), the two \(J\)-arcs \(\xi_i,\eta_i\), their
infinite-end incidences, and their finite vertex incidences.  General
KL `moduli.tex`, lines 351--355, states that the exposed \(J\)-boundary
of a tile has exactly two components.

In a strip, the outer arc joining the two deck ends occupies one
finite-coordinate boundary line.  The two connected \(J\)-arcs occupy
the two rays of the other line, each joining a deck end to a finite
endpoint.  The strip order therefore leaves one compact interval
\(\omega_i=[a_i,b_i]\), possibly degenerate, between those finite
endpoints.  The special coordinate calculations in KL `moduli.tex`,
SHA-256
`CBDB9EF7D6AC94C33FDB0AB7167E19C39EB23D27373C266A296CF6031E0CAF7E`,
lines 389--396 and 424--428, confirm explicitly that this remaining
lower interval represents \(K_Y\); they are coordinate confirmations,
not a bidepth hypothesis on \(Y_B\).

The prime-end compactification of an open horizontal strip is a closed
disk.  Its boundary consists of the two finite-coordinate boundary
lines plus the two common end points \(c_-,c_+\).  Splitting the lower
line at \(a_i,b_i\) gives (11.21).  Theorem 11.3 proves that the lifted
endpoint has finite strip coordinate and therefore is not
\(c_-\) or \(c_+\).  The five remaining pieces are disjoint and
exhaustive.

KL `psiql.tex`, lines 231--244, gives the tagged \(\lambda,\xi,\eta\)
names and defines
\(\partial^{v_{i_*}}\Psi(Y_B)
=\eta_{i_*}\cup\xi_{i_*+1}\).
Keeping the tile tags yields (11.22).  No local connectivity is used.
\(\square\)

### Scope of Theorems 11.2--11.4

The normalization is relative to the marked seam.  Forgetting the seam
restores the \(\mathbb Z\)-deck ambiguity.  These theorems do not:

- identify \(I_{1\to0}\) with a KL \(J\)-boundary arc;
- construct a protected parallel carrier access;
- prove two-flank prime-end survival or end-properness of the ambient
  inclusion on an interval;
- remove any obstacle; or
- compare widths.

It only converts a supplied terminal path into an exact, reproducible
integer deck phase and removes presentation drift caused by changing an
unbased source lift.  More precisely, the invariant phase is read in the
cut-and-stack model \(\widetilde A_\sigma\).  If \(\tau\) is a target
deck generator and KL's selected embedding is replaced by
\(e_i^{\circ\prime}=\tau^k\circ e_i^\circ\), based uniqueness gives
\(\Phi_i'=\tau^k\circ\Phi_i\).  Thus the seam alone does not select
\(e_i^\circ\): a frozen target lift (or an equivalent target basepoint)
is part of the comparison data.  The source seam-crossing integer
\(N(\gamma)\) is unchanged.  Formula (11.5) is asserted only for the
finite, transverse paths stated in Item 3.  For a proper path with
infinitely accumulating seam crossings, expressing the endpoint deck
phase as an infinite signed crossing sum would require an additional
convergence theorem and is not asserted.  The finite endpoint landing
itself is instead supplied by Theorem 11.3.

Theorem 11.3 applies only because KKL properness already includes a
continuous ideal-boundary extension.  Ordinary topological properness of
a map \((0,1)\to A\) would not suffice: an infinitely winding spiral can
be proper while having no prime-end limit and while its strip lift
escapes to \(c_+\) or \(c_-\).  Within the uniquely seam-normalized path
phase, Theorem 11.3 removes this deck-escape alternative.  It does not
prove membership of the finite endpoint in the declared KL access
label, and it does not furnish the two-flank collar required for ambient
prime-end survival.

## 12. Dense one-gate hairs destroy every upper protected interval

Theorem 7.1 proves that the interior obstacle set after enlargement is
known exactly.  It deliberately does not say that an ideal channel
survives.  The following planar example proves that this caveat cannot
be removed using only fullness, empty interior, and one-gate attachment.

Let
\[
 B_0=[-1,1]\times\{0\}\subset\mathbb R^2
\tag{12.1}
\]
and enumerate the rational points of \((-1,1)\), without repetition, as
\[
 \{q_1,q_2,\ldots\}.
\tag{12.2}
\]
For \(n\ge1\), put
\[
 H_n=\{q_n\}\times[0,2^{-n}]
\tag{12.3}
\]
and define
\[
 H=B_0\cup\bigcup_{n\ge1}H_n.
\tag{12.4}
\]
Take, for example, the common simply connected localization
\[
 \Omega=(-2,2)\times(-2,2).
\tag{12.5}
\]

For a nonempty open interval \(J\subset(-1,1)\), call the upper side
\[
 J^+=J\times\{0^+\}
\tag{12.6}
\]
**ambient protected relative to \(H\)** if there is an open neighborhood
\(N\subset\Omega\) of \(J\times\{0\}\) such that
\[
 N\cap\{y>0\}\cap(H\setminus B_0)=\varnothing.
\tag{12.7}
\]
For the collar consequence below, a **strong ambient upper collar** on
\(J\) means an embedding
\[
 c:J\times[0,1)\longrightarrow\Omega
\]
with \(c(x,0)=(x,0)\), whose interior lies on the physical upper local
side at every base point, and whose image away from its base is disjoint
from \(H\setminus B_0\).  The following
elementary implication fixes the strength of the notion being ruled
out:
\[
 \text{strong ambient upper collar on }J
 \quad\Longrightarrow\quad
 J^+\text{ is ambient protected in the sense of (12.7)}.
\tag{12.7a}
\]
Indeed, the local Schoenflies theorem at each interior base point gives
a Euclidean upper half-neighborhood contained in the collar image.
The union of these half-neighborhoods, together with sufficiently small
lower half-neighborhoods, is an open neighborhood \(N\) of
\(J\times\{0\}\) satisfying (12.7).  This implication is not asserted
for mere prime-end labels, a collar that changes physical side, or a
snaking access curve.

### Theorem 12.1
(`DENSE_ONE_GATE_HAIR_ACCESS_NO_GO`)

The continuum \(H\) has all of the following properties:

1. \(H\) is compact and connected.
2. \(H\) is full.
3. \(\operatorname{int}H=\varnothing\).
4. Every hair is a one-gate attachment:
   \[
    H_n\cap
    \left(B_0\cup\bigcup_{k<n}H_k\right)
    =
    \{(q_n,0)\}.
   \tag{12.8}
   \]
5. The attachment gates \(\{(q_n,0)\}\) are dense in the upper side of
   \(B_0\).
6. No nonempty open \(J\subset(-1,1)\) is ambient protected relative to
   \(H\).  Consequently the old upper prime-end side of
   \(\Omega\setminus B_0\) contains no nonempty subinterval carrying an
   obstacle-free strong ambient upper collar after enlargement from
   \(B_0\) to \(H\).

#### Proof

**Compactness.**
The set is bounded.  Let \(z_j\in H\) be a convergent sequence.  If the
hair indices containing a subsequence of the \(z_j\) are bounded, pass
to a further subsequence in one of the finitely many closed segments
\[
 B_0,H_1,\ldots,H_N.
\]
Its limit belongs to \(H\).  Otherwise pass to a subsequence whose hair
indices \(n_j\) tend to infinity.  Its vertical coordinates satisfy
\[
 0\le y_j\le2^{-n_j}\longrightarrow0,
\]
so its limit belongs to \(B_0\).  Thus \(H\) is closed and bounded,
hence compact.

**Connectedness and one-gate attachment.**
Each \(H_n\) is connected and meets the connected base \(B_0\) at
exactly \((q_n,0)\).  Distinct hairs are disjoint away from the base
because the \(q_n\) are distinct.  Hence (12.8) holds, and the union is
path connected.  Density of the gates is exactly (12.2).

**Empty interior.**
The set \(H\) is a countable union of line segments, so it has
two-dimensional Lebesgue measure zero.  A nonempty planar open set has
positive measure.  Therefore \(\operatorname{int}H=\varnothing\).

**Fullness.**
The homotopy
\[
 R_t(x,y)=(x,(1-t)y),
 \qquad 0\le t\le1,
\tag{12.9}
\]
is a strong deformation retraction of \(H\) onto \(B_0\).  Thus \(H\)
is contractible and
\[
 \check H^1(H;\mathbb Z)=0.
\tag{12.10}
\]
Alexander duality for compact subsets of the sphere gives
\[
 \widetilde H_0
 \left(\widehat{\mathbb C}\setminus H;\mathbb Z\right)
 \cong
 \check H^1(H;\mathbb Z)
=0.
\tag{12.11}
\]
The complement is an open surface and is therefore locally path
connected, so vanishing reduced singular \(H_0\) says that it is
connected.  Since \(H\) is compact, this rules out every bounded
complementary component.  Equivalently, \(H\) is full.

There is also a direct planar check.  Above any fixed height \(y>0\),
only finitely many hairs meet the horizontal line at height \(y\),
because \(2^{-n}\ge y\) holds for only finitely many \(n\).  A point
above the base can be moved vertically upward--its vertical line either
misses every hair or begins above the unique hair with that
\(x\)-coordinate--and then joined to the region \(y>1/2\), detouring
around only finitely many segments.  A point below the base can first be
joined around an endpoint of \(B_0\) to the upper half-plane.  Thus every
complement point joins the same outer region.

**Failure of every protected interval.**
Let \(J\subset(-1,1)\) be nonempty and open, and let \(N\) be any open
neighborhood of \(J\times\{0\}\).  Choose \(x\in J\).  There is \(r>0\)
such that
\[
 \overline{\mathbb D((x,0),r)}\subset N,
 \qquad
 (x-r,x+r)\subset J.
\tag{12.12}
\]
By density choose \(q_n\) with
\[
 |q_n-x|<r/2.
\tag{12.13}
\]
Choose
\[
 0<y<\min\{2^{-n},r/2\}.
\tag{12.14}
\]
Then
\[
 (q_n,y)\in H_n\setminus B_0
\]
and, by (12.13)--(12.14),
\[
 \|(q_n,y)-(x,0)\|<r.
\]
Thus \((q_n,y)\in N\cap\{y>0\}\), contradicting (12.7).  Since \(N\)
was arbitrary, no nonempty \(J^+\) is ambient protected.  The final
collar statement follows from implication (12.7a). \(\square\)

### Exact interpretation of the countermodel

The decay \(2^{-n}\to0\) is essential to the chosen compact
empty-interior model.  Equal-height hairs over a dense gate set would
have a rectangular closure and would not satisfy the theorem's
hypotheses.

The example is not asserted to be a polynomial Julia carrier.  It is a
logical countermodel to the inference
\[
 \begin{gathered}
 \text{full carrier}+\text{empty interior}
 +\text{one gate per attachment}\\
 \Longrightarrow
 \text{a nonempty protected side interval survives}.
 \end{gathered}
\tag{12.15}
\]
An actual dynamical theorem can exclude the example only by adding
effective local finiteness, a protected-collar separation estimate,
uniform attachment-height control in a collar coordinate, or an
equivalent no-dense-incidence hypothesis.  The set identities in
Theorem 7.1 do not supply any of these.

The theorem rules out the strong physical-side collar defined above.
It does not rule out a weaker proper prime-end channel, a snaking access
curve, or a collar for which physical-side compatibility has not been
proved.

None of Theorems 11.2, 11.3, and 12.1 changes the status of
`WAVE_TO_KL_ADDRESS_ACCESS_SELECTOR`, `VIRTUAL_WAVE_MARKED_CORRESPONDENCE`,
VAAPC-I, UPTCR, or MLC.

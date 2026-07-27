# Canonical/KL restricted interfaces: exact relation span and branch classification

## 1. Verdict, scope, and status

This pass addresses the first positive gate left by
`CANONICAL_KL_WHOLE_TILE_CORRESPONDENCE_NO_GO`.

The result has one constructive part and two exact negative parts.

> **Restricted-interface classification.**
>
> 1. For every supplied fixed same-source labeled canonical/Kahn--Lyubich
>    tile datum with chosen lifted basepoints, the unchanged canonical
>    resolution and the actual tile admit a canonical
>    **relation-valued** comparison: a based analytic
>    span
>    \[
>      \mathcal R
>      \mathop{\longleftarrow}^{q}
>      \mathcal E
>      \mathop{\longrightarrow}^{K}
>      \widehat A_t^{\rm KL}.
>    \]
>    The pullback of every target path by \(K\) is an exact, multiplicity-
>    preserving étale family of all maximal actual KL source restrictions.
> 2. If the canonical deck kernel \(N=\operatorname{Deck}(q)\) is
>    nontrivial, this span cannot descend to a single-valued map on
>    \(\mathcal R\).  At every point where the source-locked KL extension
>    domain meets the deck limit set, every resolved fiber has the same
>    transported KL value in its target-cluster closure.  In particular
>    this holds at both wrapping points.
> 3. Kahn's annulus hypotheses, even with \(d=2\) and a globally embedded
>    base map, cannot give the unscaled universal additive comparison
>    between a retained inner-collar crossing width and the full
>    target-annulus crossing width.
> 4. Retiming within the unchanged exact Kahn equalizer tower cannot make
>    the canonical factorization one-sheeted: the infinite \(q\)-fiber is
>    preserved by every finite base change.
> 5. Provided the physical embedding lifts between the revised covers, a
>    revised localization is one-sheeted exactly when it restores the
>    subgroup-reflection equality
>    \(a_*^{-1}(H_t)=H_s\).  No checked source proves that such a revision
>    preserves the required dynamical package, obstacles, accesses, and
>    final-root data.

Thus one map-level branch is no longer unspecified: the full
relation-valued span is canonically constructible from the fixed
same-source data without assuming a false descent, the unscaled collar
charge ruled out below, or a one-sheet retiming.  This does **not** prove
that the four nominated branches exhaust all possible interfaces.  It
also does **not** construct the aligned datum at every Wave stage or prove
parameter realization.  Finally, it does **not** prove the proper/end-proper
classification of its path restrictions, a uniform bad-family width
bound, prime-end naturality, or final-root functoriality.

The internally proved ledger node is

`CANONICAL_KL_RESTRICTED_INTERFACE_CLASSIFICATION`.

The following remain open:

- `DIRECT_DECORATION_OUTER_CAP_FOOTPRINT`;
- `DIRECT_DECORATION_PSEUDO_PIECE_PATH_LIFT_EXHAUSTION`;
- `DIRECT_DECORATION_ALL_DEPTH_CONTACT_CLOSURE`;
- `VIRTUAL_WAVE_MARKED_CORRESPONDENCE`;
- `VIRTUAL_WAVE_HORIZON_CERTIFICATE`;
- VAAPC-I;
- UPTCR; and
- MLC.

## 2. Source locks and imported scope

No new external theorem is imported.  The locked primary source files are:

```text
Kahn I, arXiv:math/0609045
  .tmp_kl06_source/psiql2.tex
  SHA-256 E4EFCCEC65D8C9C2BDFE2AF8203B3D4D63ECF992B40D302F56FBA78259547228

Kahn--Lyubich II, arXiv:math/0609046
  .tmp_kl08_source/psiql.tex
  SHA-256 6CC9726461473812A5FBA93377F2DC0B088DB6CAC4B9DE90C7B2AE625DFB49AF

  .tmp_kl08_source/appendix.tex
  SHA-256 05A13ED2D46CB9E2D188E6D96F4A2B639626F99657723118B4DE3479CD980916

  .tmp_kl08_source/moduli.tex
  SHA-256 CBDB9EF7D6AC94C33FDB0AB7167E19C39EB23D27373C266A296CF6031E0CAF7E
```

The exact source uses are:

1. Kahn I, `psiql2.tex`, lines 87--98, states the annulus-immersion
   hypotheses.  Lines 118--130 prove injectivity only on a sufficiently
   thin inner collar.  Lines 133--137 make the collar uniform only when
   the target annulus is bounded away from modulus zero.
2. KL II, `psiql.tex`, lines 117--147, constructs a pseudo-piece by gluing
   universal-cover tiles to the central piece.
3. KL II, `psiql.tex`, lines 169--207, constructs the actual inclusion-
   induced tile immersions and keeps them distinct from the dynamical
   covering maps.
4. KL II, `psiql.tex`, lines 231--253, identifies the complete ideal
   marking, the two infinitely wrapping vertices, and the continuous
   extension of the actual pseudo-piece immersion.
5. KL II, `appendix.tex`, lines 10--17, fixes
   \[
      \mathcal W(\Gamma)=\mathcal L(\Gamma)^{-1}
   \]
   for extremal width and records the parallel and series laws.
6. KL II, `moduli.tex`, lines 351--400, explicitly uses curve families in
   a universal-cover tile and the horizontal-strip model adjoining the
   \(O\)-boundary.

The already proved internal inputs are:

- `KL_LOCALIZATION_SHEET_RESOLUTION_FACTORIZATION`;
- `KAHN_ITERATE_COMPLEMENTARY_COMPONENT_ALIGNMENT`;
- `RESOLVED_INTERMEDIATE_RELATIVE_IDEAL_BOUNDARY`;
- `CANONICAL_KL_WHOLE_TILE_CORRESPONDENCE_NO_GO`; and
- `FINITE_HORIZON_KAHN_COLLAR_EMBEDDING`.

None of these sources or internal inputs supplies a uniform omitted-width
charge, singleton proper-restriction selection, or geometric final-root
no-birth.

## 3. The typed systems

### 3.1 Canonical resolution

Fix one source-indexed tile of the canonical annular resolution.  In the
common based disk action, write

\[
 \mathcal E
 \mathop{\longrightarrow}^{q}
 \mathcal R
 \mathop{\longrightarrow}^{e}
 T,
 \qquad
 L=e q,
 \qquad
 N=\operatorname{Deck}(q).
\tag{3.1}
\]

The proved covering-tower theorem gives

\[
 G=N\rtimes H,\qquad
 \mathcal E/H=A_s,\qquad
 \mathcal E/N=\mathcal R,\qquad
 \mathcal E/G=P,
\tag{3.2}
\]

where \(H=\langle h\rangle\cong\mathbb Z\) is the positive source-annular
deck group.  In the ordinary primitive canonical case, \(N\) is infinite.

### 3.2 Actual KL tile

Let

\[
 L_{\rm KL}:
 \widehat A_s^{\rm KL}
 \longrightarrow
 \widehat A_t^{\rm KL}
\tag{3.3}
\]

be the actual source-indexed KL tile immersion.  Both
\(\mathcal E\) and \(\widehat A_s^{\rm KL}\) are universal covers of the
same based oriented source annulus \(A_s\).  Hence there is a unique based
biholomorphism

\[
 \Phi:\mathcal E\longrightarrow\widehat A_s^{\rm KL}
\tag{3.4}
\]

over \(A_s\), and it satisfies

\[
 \Phi h=t_s\Phi
\tag{3.5}
\]

for the positive annular generators.

Define the actual composite on the common source disk by

\[
 K=L_{\rm KL}\Phi:
 \mathcal E\longrightarrow\widehat A_t^{\rm KL}.
\tag{3.6}
\]

The map \(K\) is a nonconstant holomorphic immersion.  Its boundary
domain must be stated more narrowly.  Let
\(\omega_-,\omega_+\in\partial_i\widehat A_s^{\rm KL}\) be the two
source-locked KL wrapping vertices.  The biholomorphism \(\Phi\) extends
homeomorphically between the standalone conformal ideal circles and
conjugates their positive annular generators.  Put

\[
 \zeta_\pm=\overline\Phi^{-1}(\omega_\pm),
 \qquad
 D_{\rm ext}=\{\zeta_-,\zeta_+\}.
\tag{3.7}
\]

KL extends the **glued pseudo-piece immersion** on the pseudo-piece ideal
boundary, and these two vertices lie on that boundary.  Therefore the
source-locked result gives the partial continuous extension

\[
 \overline K:
 \mathcal E\cup D_{\rm ext}
 \longrightarrow
 \overline{\boldsymbol Y_t^{\rm KL}}{}^{\,i},
\tag{3.8}
\]

where the target is the Hausdorff conformal ideal compactification of the
target pseudo-piece.  KL explicitly allow a source boundary point to map
to target interior, so (3.8) is not typed as a map into the target
boundary alone.

No checked source identifies the entire standalone source-tile ideal
circle with the glued pseudo-piece boundary topology.  In particular,
this pass does not assert an extension on all of
\(\partial_i\mathcal E\), or that
\(\Lambda(N)\subset D_{\rm ext}\).  Any enlargement of \(D_{\rm ext}\)
requires a separate compatibility proof.

No target comparison \(B:T\to\widehat A_t^{\rm KL}\) is assumed.

## 4. Construction of the relation-valued interface

### Definition 4.1 -- based comparison span

The **canonical/KL comparison span** is

\[
 \mathfrak S_{\rm KL}
 =
 \left(
 \mathcal R
 \mathop{\longleftarrow}^{q}
 \mathcal E
 \mathop{\longrightarrow}^{K}
 \widehat A_t^{\rm KL}
 \right).
\tag{4.1}
\]

Its set-valued realization is

\[
 \mathscr C_{\rm KL}
 =
 \{(q(z),K(z)):z\in\mathcal E\}
 \subset
 \mathcal R\times\widehat A_t^{\rm KL}.
\tag{4.2}
\]

For \(r\in\mathcal R\), define the target orbit trace

\[
 \mathcal O_K(r)
 =
 \{K(z):q(z)=r\}.
\tag{4.3}
\]

If \(q(z)=r\), regularity of the universal cover gives

\[
 q^{-1}(r)=N z,
 \qquad
 \mathcal O_K(r)=\{K(\gamma z):\gamma\in N\}.
\tag{4.4}
\]

### Proposition 4.2 -- existence and based uniqueness

The span (4.1) exists for every fixed same-source canonical/KL tile datum
and is unique after the source basepoint and positive annular generator
are fixed.

#### Proof

The two source disks in (3.4) are based universal covers of the same
annulus.  Based lifting uniqueness gives one and only one biholomorphism
\(\Phi\) over the identity of \(A_s\).  The chosen orientation forces
(3.5).  Equations (3.6), (4.1), and (4.2) then determine every remaining
map and relation.  No intermediate or target quotient is chosen.
\(\square\)

### Proposition 4.3 -- non-descent for a nontrivial kernel

Assume \(N\ne1\).  There is no continuous map

\[
 \kappa:\mathcal R\longrightarrow\widehat A_t^{\rm KL}
\tag{4.5}
\]

such that

\[
 K=\kappa q.
\tag{4.6}
\]

Consequently the relation (4.2) cannot be replaced by a single-valued map
on the unchanged resolved intermediate.

#### Proof

If (4.6) held, then for every \(\gamma\in N\),

\[
 K(\gamma z)
 =
 \kappa q(\gamma z)
 =
 \kappa q(z)
 =
 K(z).
\tag{4.7}
\]

Thus \(K\) would be a nonconstant \(N\)-invariant map.  The proved
normal-kernel wrapping theorem gives
\(\zeta_-,\zeta_+\in\Lambda(N)\), while (3.8) gives a continuous value of
\(K\) at each of these two points.  The proved invariant-composite
deck-limit theorem forbids a nonconstant \(N\)-invariant map from
extending at either one.  This is a contradiction. \(\square\)

This proof does not assert that \(L_{\rm KL}\) is injective.  It asserts
that the actual KL values cannot be constant on every canonical
\(q\)-fiber.

## 5. Complete compact-path restriction family

### Definition 5.1 -- pullback of one target path

Let \(J\subset\mathbb R\) be an interval and let

\[
 \alpha:J\longrightarrow\widehat A_t^{\rm KL}
\tag{5.1}
\]

be a path.  Form the topological fiber product

\[
 \mathscr P_K(\alpha)
 =
 J\times_{\widehat A_t^{\rm KL}}\mathcal E
 =
 \{(t,z):\alpha(t)=K(z)\}.
\tag{5.2}
\]

The projection

\[
 \operatorname{pr}_J:
 \mathscr P_K(\alpha)\longrightarrow J
\tag{5.3}
\]

is a local homeomorphism because \(K\) is a holomorphic immersion.

For a fixed pseudo-piece let \(\mathcal I_s\) be its finite set of
source-tile indices.  Repeat (3.3)--(3.6) with the label retained to
obtain \(K_i:\mathcal E_i\to\widehat A_{t,j(i)}^{\rm KL}\).  If a target
path \(\alpha\) lies in the tile with target index \(j\), define the
tagged total pullback

\[
 \mathscr P^{\rm tag}(\alpha)
 =
 \bigsqcup_{\substack{i\in\mathcal I_s\\j(i)=j}}
 \{i\}\times\mathscr P_{K_i}(\alpha).
\tag{5.4}
\]

This disjoint union is necessary because KL's component map \(j(i)\) is
surjective but need not be injective.

A **maximal KL restriction** of \(\alpha\) is a maximal path
\(\widetilde\alpha:J'\to\mathcal E\), for an interval \(J'\subset J\),
satisfying

\[
 K\widetilde\alpha=\alpha|_{J'}.
\tag{5.5}
\]

It is a **full restriction** when \(J'=J\).

### Theorem 5.2 -- exact restriction enumeration

For each fixed source label \(i\), the path components of
\(\mathscr P_{K_i}(\alpha)\) are exactly the graphs of the maximal
restrictions of \(\alpha\) in that tile.  The path components of
\(\mathscr P^{\rm tag}(\alpha)\) therefore enumerate all maximal
restrictions across the declared source labels with \(j(i)=j\).  In
particular:

1. every actual source restriction of \(\alpha\) appears;
2. no restriction is identified with another restriction;
3. every restriction carries the resolved trace
   \[
     q_i\widetilde\alpha:J'\longrightarrow\mathcal R_i;
   \tag{5.6}
   \]
4. the starting point in \(q_i^{-1}(r)=N_i z\) retains the complete
   canonical sheet and deck phase; and
5. distinct source labels \(i_1\ne i_2\) with
   \(j(i_1)=j(i_2)\) remain separate tagged objects.

#### Proof

Fix a source label \(i\), abbreviate \(K_i\) by \(K\), and take
\((t_0,z_0)\in\mathscr P_K(\alpha)\).  Since \(K\) is a local
homeomorphism at \(z_0\), there are neighborhoods \(U\ni z_0\) and
\(V\ni\alpha(t_0)\) for which

\[
 K|_U:U\xrightarrow{\cong}V.
\tag{5.7}
\]

On a sufficiently small interval \(J_0\ni t_0\) with
\(\alpha(J_0)\subset V\), the unique local lift is

\[
 \widetilde\alpha(t)=(K|_U)^{-1}\alpha(t).
\tag{5.8}
\]

If \(J\) is a singleton, every component of (5.2) is already a singleton
graph and the assertion is immediate.  Assume henceforth that \(J\) is
nondegenerate.

Local uniqueness lets these germs continue uniquely until the first time
at which continuation leaves every compact subset of the current inverse
charts.  Their union is one maximal lift on an interval \(J'\subset J\).
Its graph lies in one path component of (5.2).

For the converse and the global assertion, use the topology of the fiber
product rather than the parametrization of an arbitrary path.
\(\mathscr P_K(\alpha)\) is a subspace of the Hausdorff,
second-countable space \(J\times\mathcal E\).  Base change of the local
homeomorphism \(K\) makes \(\operatorname{pr}_J\) a local homeomorphism.
Thus every path component \(C\) is a connected second-countable
one-manifold, possibly with boundary over an endpoint of \(J\), and
\(\operatorname{pr}_J|_C\) is locally monotone.

The component \(C\) cannot be a circle.  A local homeomorphism from a
circle cannot meet an endpoint of \(J\), while its image would otherwise
be a nonempty compact open subset of the interior of an interval.  Hence
\(C\) is an interval.  After orienting it, the local monotonicity sign of
\(\operatorname{pr}_J|_C\) is locally constant and therefore constant.
The projection is consequently strictly monotone and injective on \(C\).
Write \(J_C=\operatorname{pr}_J(C)\).  Its inverse has the form

\[
 t\longmapsto (t,\widetilde\alpha_C(t)),
 \qquad t\in J_C,
\tag{5.9}
\]

and \(K\widetilde\alpha_C=\alpha|_{J_C}\).  If this lift extended past an
endpoint of \(J_C\), its graph would join the same path component,
contradicting the definition of \(J_C\).  It is therefore maximal.
Conversely, local uniqueness (5.8) prevents the graph of a maximal lift
from being a proper path-connected subset of a component.  Path
components and maximal restrictions are in bijection.

Applying \(q_i\) gives (5.6).  No quotient is taken in (5.2), and the
disjoint union (5.4) is label-preserving, so distinct components, source
labels, initial sheets, and phases remain distinct. \(\square\)

### Scope

Theorem 5.2 proves **interior restriction completeness**.  The word
"family" is deliberate: no composition or inversion law has been added,
so this theorem does not by itself construct a groupoid.  It also does
not prove:

- that a maximal parameter-compatible restriction has point-valued
  source ideal endpoints on the standalone tile relation;
- that the parametrized restriction exhausts every KKL proper path in the
  geometric inverse trace;
- map properness on a source ideal subset or end-properness on the complete
  end-intervals of a pulled multi-interval;
- that it has a point-valued endpoint in the relative ideal boundary;
- that exactly one proper restriction is subordinate to a marked target
  interval;
- that the family of nonproper or omitted restrictions has bounded
  extremal width; or
- that the restriction family is functorial under final-root
  enlargement.

These are separate analytic obligations.

## 6. Boundary orbit traces

### Theorem 6.1 -- common cluster on the source-locked extension domain

Assume \(N\ne1\).  For every \(r\in\mathcal R\),

\[
 \overline K\bigl(\Lambda(N)\cap D_{\rm ext}\bigr)
 \subset
 \overline{\mathcal O_K(r)}
 \subset
 \overline{\boldsymbol Y_t^{\rm KL}}{}^{\,i}.
\tag{6.1}
\]

In particular, the source-locked KL values at both annular wrapping points
\(\zeta_\pm\in\Lambda(N)\) lie in the closure of every target orbit trace.

#### Proof

Fix \(\zeta\in\Lambda(N)\cap D_{\rm ext}\), \(r\in\mathcal R\), and
\(z\in q^{-1}(r)\).  Choose \(z_0\in\mathcal E\).  By the definition of
the limit set, there are distinct \(\gamma_n\in N\) such that

\[
 \gamma_nz_0\longrightarrow\zeta.
\tag{6.2}
\]

Every \(\gamma_n\) is a hyperbolic isometry, hence

\[
 d_{\mathcal E}(\gamma_nz,\gamma_nz_0)
 =
 d_{\mathcal E}(z,z_0).
\tag{6.3}
\]

Bounded hyperbolic distance and (6.2) give

\[
 \gamma_nz\longrightarrow\zeta.
\tag{6.4}
\]

By (3.8),

\[
 K(\gamma_nz)\longrightarrow\overline K(\zeta).
\tag{6.5}
\]

Every \(K(\gamma_nz)\) lies in \(\mathcal O_K(r)\) by (4.4), proving
(6.1).  The wrapping assertion follows from the proved normal-kernel
wrapping lemma. \(\square\)

### Consequence 6.2

A conservative, uncompressed candidate state for the next gate is:

\[
 \left(
 N,\Lambda(N),\Omega(N),
 D_{\rm ext},
 \overline K|_{\Lambda(N)\cap D_{\rm ext}},
 \{\mathcal O_K(r)\}_{r\in\mathcal R}
 \right).
\tag{6.6}
\]

Equation (6.1) is a cluster statement on the explicitly certified partial
extension domain, not a point-valued descent of \(q\).  It does not
reinsert \(\Lambda(N)\) into Kahn's relative ideal boundary, and it does
not assert a KL value at an uncertified point of
\(\Lambda(N)\setminus D_{\rm ext}\).  It proves the incidence recorded in
(6.6), but it proves neither minimality of that state nor impossibility of
a finite future-faithful quotient.

## 7. Kahn's hypotheses do not give the unscaled collar-width charge

### 7.1 Exact source scope

Kahn's annulus lemma starts with

\[
 I:\mathbb A(1,r^{1/d})\longrightarrow\mathbb A(1,r),
\qquad d>1,
\tag{7.1}
\]

a holomorphic immersion with continuous degree-one inner-circle map.
It proves an embedded inner collar.  A collar radius uniform away from
one is obtained only when \(r\) is bounded away from one.

The global gate cannot assume such a lower modulus bound: that would be
an a-priori bound at the point where the project is trying to prove one.

### Proposition 7.1 -- quadratic zero-modulus collar no-go

There is no universal constant \(D<\infty\) with the following property:
for every degree-two datum satisfying Kahn's annulus hypotheses, one can
choose an essential embedded retained source inner collar
\(C\subset A_s\) so that

\[
 \left|
 \mathcal W(\Gamma_C)
 -
 \mathcal W(\Gamma_t)
 \right|
 \le D,
\tag{7.2}
\]

where \(\Gamma_C\) and \(\Gamma_t\) are the complete curve families
joining the two boundary components of \(C\) and of the full target
annulus.

This remains false when the base immersion is the identity inclusion and
is globally injective.

#### Proof

For \(\varepsilon>0\), set

\[
 r=e^\varepsilon,\qquad
 A_s=\mathbb A(1,e^{\varepsilon/2}),\qquad
 A_t=\mathbb A(1,e^\varepsilon),
\tag{7.3}
\]

and define

\[
 I_\varepsilon:A_s\hookrightarrow A_t,
\qquad
 I_\varepsilon(z)=z.
\tag{7.4}
\]

This is a holomorphic embedding, extends by the identity to the inner
circle, has degree one there, and has exactly the \(d=2\) radii required
by (7.1).

The logarithm identifies \(A_t\) with the Euclidean cylinder

\[
 (0,\varepsilon)\times\mathbb R/(2\pi\mathbb Z).
\tag{7.5}
\]

For curves joining its two boundary components,

\[
 \mathcal L(\Gamma_t)
 =
 \operatorname{mod}(A_t)
 =
 \frac{\varepsilon}{2\pi},
\qquad
 \mathcal W(\Gamma_t)
 =
 \frac{2\pi}{\varepsilon}.
\tag{7.6}
\]

Every essential annular collar \(C\subset A_s\) has

\[
 \operatorname{mod}(C)
 \le
 \operatorname{mod}(A_s)
 =
 \frac{\varepsilon}{4\pi}
\tag{7.7}
\]

by monotonicity of the modulus of nested essential annuli.  Therefore

\[
 \mathcal W(\Gamma_C)
 =
 \frac{1}{\operatorname{mod}(C)}
 \ge
 \frac{4\pi}{\varepsilon}.
\tag{7.8}
\]

Combining (7.6)--(7.8),

\[
 \left|
 \mathcal W(\Gamma_C)-\mathcal W(\Gamma_t)
 \right|
 \ge
 \frac{2\pi}{\varepsilon}
 \longrightarrow\infty
 \qquad(\varepsilon\downarrow0).
\tag{7.9}
\]

No universal \(D\) can satisfy (7.2). \(\square\)

### Exact interpretation

Proposition 7.1 proves only a **source-hypothesis no-go**:

- Kahn's degree, local-univalence, boundary-degree, and collar conclusions
  do not imply a uniform full-versus-collar width comparison;
- topology and degree two do not repair the missing estimate; and
- choosing an even thinner collar cannot help, because (7.8) only
  increases its crossing width.

It does not prove that every actual quadratic KL block realizes the model
(7.3).  A positive quadratic theorem must add a source-specific
degeneration estimate, absorb the outer family into another controlled
module, or retain its full response in the state.  It also does not rule
out a separately justified degree-calibrated comparison or a comparison
for a smaller proof-used curve family; neither follows from Kahn's
annulus lemma alone.

## 8. Retiming inside the unchanged Kahn tower

### Proposition 8.1 -- finite equalizer retiming preserves the defect

Let

\[
 X_r\xrightarrow{q_r}P_r\xrightarrow{e_r}Z_r
\tag{8.1}
\]

be the canonical covering/embedding factorization propagated through the
full, unselected exact Kahn equalizers on the complementary-cover locus.
If one fiber of \(q_0\) is infinite, then every corresponding fiber of
every finite \(q_r\) is infinite.  Consequently, selecting any later
finite Kahn iterate as a retimed stage cannot make the unchanged
factorization one-sheeted.

#### Proof

At one exact base change,

\[
 E=X\times_ZY,\qquad
 R=P\times_ZY,\qquad
 q'(x,y)=(q(x),y).
\tag{8.2}
\]

For every \((p,y)\in R\),

\[
 (q')^{-1}(p,y)
 =
 \{(x,y):q(x)=p\}
 \cong
 q^{-1}(p).
\tag{8.3}
\]

Thus one base change preserves the fiber exactly.  Induction over any
finite number of Kahn equalizers proves the first assertion.  A
one-sheeted covering has singleton fibers, so no such finite retiming is
one-sheeted. \(\square\)

This theorem does not exclude a genuinely different return map, a changed
localization, or a quotient that is separately proved future-faithful.
Those are not retimings inside the unchanged exact equalizer tower.

## 9. Revised localization

Fix a based physical embedding

\[
 a:X_s\hookrightarrow X_t
\tag{9.1}
\]

and connected localization covers classified by

\[
 H_s\le\pi_1(X_s),
\qquad
 H_t\le\pi_1(X_t).
\tag{9.2}
\]

Assume the based embedding lifts between these two covers, equivalently

\[
 a_*(H_s)\le H_t.
\tag{9.3}
\]

The canonical intermediate subgroup is

\[
 K_a=a_*^{-1}(H_t).
\tag{9.4}
\]

The lift condition is exactly \(H_s\le K_a\).

The based fiber of the first factor is the pointed coset set

\[
 K_a/H_s,
\tag{9.5}
\]

so the revised factor is one-sheeted exactly when

\[
 a_*^{-1}(H_t)=H_s.
\tag{9.6}
\]

Equation (9.6) is necessary and sufficient algebraically, conditional on
the lift hypothesis (9.3).  The cosets in (9.5) are a pointed set; no
normality of \(H_s\) in \(K_a\) is asserted.  The criterion is not an
analytic carrier theorem.  A revised obstacle packet must still prove:

1. containment of every required small Julia component and orbit segment;
2. preservation of all proof-used accesses and their cyclic order;
3. absence of a new critical value in every declared degree-one corridor;
4. compatibility with the actual KL tile and its central gluing;
5. complete path-restriction and properness data; and
6. Cartesian final-root no-birth.

No checked source constructs such a revision for every admissible virtual
Wave block.

## 10. Audit of the four nominated branches

The four replacement types nominated after the whole-tile no-go now have
the following exact status.

| Branch | What is proved | First unresolved datum |
|---|---|---|
| Proper interior/collar | An abstract coherent embedded collar exists on every fixed finite horizon under explicit overlap-reflection hypotheses.  Those hypotheses are not proved for the actual KL pseudo-piece. | Proposition 7.1 forbids deriving the unscaled full-versus-collar crossing-width charge from Kahn's hypotheses, even for \(d=2\); it does not rule out a separately proved calibrated response. |
| Non-covering relation | The span (4.1), orbit traces (4.3), and tagged parametrized-path restriction family (5.4) are canonical for the fixed same-source datum. | Full geometric inverse-trace paths, proper source endpoints, ideal-subset and whole-end-interval map properness, uniform bad-family response, and final-root functoriality. |
| Retimed one-sheet | Nothing changes if retiming only selects a later full Kahn equalizer. | Proposition 8.1 preserves the infinite fiber; a genuinely new return/localization must be constructed. |
| Revised localization | Subject to the lift condition (9.3), one-sheetedness is exactly subgroup reflection (9.6). | Dynamical-package and obstacle authorization, analytic realization, marking fidelity, and root naturality. |

Therefore the relation-valued span is one canonical branch constructed on
the fixed unchanged same-source datum.  This audit neither proves that
the four branches are logically exhaustive nor excludes a fifth
construction.  The span is deliberately not compressed to a map
\(\mathcal R\to\widehat A_t^{\rm KL}\).

## 11. Candidate replacement state

A conservative label-complete candidate retained state is

\[
 \mathfrak C_{\rm rel}^{\rm cand}
 =
 \left(
 \left\{
 \begin{aligned}
 (&\mathcal E_i,\mathcal R_i,q_i,K_i,N_i,H_i,D_{{\rm ext},i},\\
  &\overline K_i|_{\Lambda(N_i)\cap D_{{\rm ext},i}},
    \{\mathcal O_{K_i}(r_i)\}_{r_i\in\mathcal R_i})
 \end{aligned}
 \right\}_{i\in\mathcal I_s},
 \{\mathscr P^{\rm tag}(\alpha)\}_{\alpha\in\mathscr A_{\rm use}},
 \mathscr D_{\rm prop},
 \mathscr D_{\rm width}
 \right),
\tag{11.1}
\]

where:

- \(\mathscr A_{\rm use}\) is the complete frozen proof-use path ledger;
- \(\mathscr D_{\rm prop}\) must separately record proper source paths,
  map properness on ideal subsets, and map properness on every complete
  end-interval used to define end-properness; these predicates have
  different types;
- \(\mathscr D_{\rm width}\) must retain the response of every bad or
  omitted family rather than replacing it by a constant not supplied by
  Proposition 7.1.

For every supplied fixed same-source datum, the label-indexed interior
spans, tagged pullbacks, and two-point extension/cluster records in
(11.1) are constructed in this pass.  The proof-use ledger
\(\mathscr A_{\rm use}\) must still be frozen for an actual complete Wave
horizon.  The two defect modules are named obligations, not proved
bounds.  Thus (11.1) is not asserted minimal, finite, Value-observable, or
future-faithful.

Subsequent cross-validation proves that this candidate was still too
small.  KKL restrict by all proper source paths contained in the
**geometric inverse trace**, whereas (5.4) records only maximal
parameter-compatible lifts.  The identity-disk lollipop gives strict
containment, and one exponential disk immersion gives infinitely many
proper restrictions plus unbounded raw interior branchwise crossing
width.  See
`canonical_kl_geometric_trace_proper_end_response.md`.

That pass also proves the strongest safe positive statement: on a supplied
full KL pseudo-piece immersion with its full continuous ideal extension,
every maximal parametrized lift of a KKL proper target path is a KKL
proper source path with exact endpoint naturality.  This does not exhaust
the geometric restriction or prove map/end-properness.

The corrected target is split into five nodes:

1. freeze the complete Wave proof-use ledger;
2. construct the glued canonical/KL datum at every ledger stage;
3. build the full geometric inverse-trace path space, pulled marking, and
   whole-end-interval properness classification;
4. prove the uniform WAD/Value response; and
5. independently prove Cartesian final-root no-birth.

At each node the first missing path, endpoint, interval, response row, or
born/merged component is the required obstruction certificate.

## 12. Adversarial audit

### 12.1 A span is not a descent

The middle disk \(\mathcal E\) is retained.  Writing only the set
\(\mathscr C_{\rm KL}\) and then treating it as the graph of a map on
\(\mathcal R\) would contradict Proposition 4.3.

### 12.2 The actual KL immersion is not declared injective

All path restrictions are pulled back by the local homeomorphisms \(K_i\).
Different path components may have the same target image.  The tagged
étale family retains them rather than identifying them.

### 12.3 Compact paths are not proper ends

Theorem 5.2 is an interior theorem.  It does not assign point endpoints at
\(\Lambda(N)\), where the resolved cover has no point-valued extension.

### 12.4 Cluster values are not quotient values

Equation (6.1) applies only to
\(\zeta\in\Lambda(N)\cap D_{\rm ext}\) and places
\(\overline K(\zeta)\) in every closed orbit trace.  It does not define
\(q(\zeta)\), and it does not make the relative boundary Hausdorff after
reinserting \(\zeta\).  Applying it to all of \(\Lambda(N)\) would require
a new full standalone-tile boundary theorem.

### 12.5 The collar model does not assume the desired quadratic theorem

The family (7.3) lies exactly in Kahn's annulus category and uses \(d=2\).
It proves that those hypotheses alone are insufficient.  It is not
presented as an actual quadratic parameter sequence.

### 12.6 Retiming is narrowly typed

Proposition 8.1 excludes only finite selection inside the unchanged exact
base-change tower.  It does not exclude a newly constructed return map.

### 12.7 Algebraic subgroup reflection is not geometric authorization

After the lift condition (9.3) is checked, equation (9.6) says when the
covering factor is one-sheeted.  It says nothing about whether the revised
cover contains the required carrier or respects the actual KL gluing.

### 12.8 No finite-state conclusion

The ordinary primitive canonical \(N\) is infinite.  Neither (4.3) nor
(5.2) is proved to admit a finite future-faithful quotient.  Raw finite
sheet enumeration remains invalid.

### 12.9 No global promotion

The relation span and the two no-go statements do not imply a width
transition, compactness, rigidity, parameter shrinking, or MLC.

### 12.10 Parametrized lifts are not KKL trace exhaustion

KKL's definition starts from the geometric set
\(\iota^{-1}(|\gamma|)\) and retains every proper source path contained in
it.  Equation (5.2) instead fixes the parameter \(t\).  The later
identity-lollipop counterexample proves that a proper loop-omitting path
can belong to the former and not the latter.  Theorem 5.2 therefore keeps
its exact parametrized-interior scope.

### 12.11 End-properness is not a component flag

A path may be proper while one of its source ideal endpoints maps to target
interior.  KKL end-properness is properness of the immersion on every
complete end-interval of an already constructed pulled multi-interval.
It cannot be assigned to a path component before that marking exists.

## 13. Promotion and exact next gate

Promote only:

`CANONICAL_KL_RESTRICTED_INTERFACE_CLASSIFICATION`.

Its proved content is:

1. the based analytic relation span;
2. exact tagged compact-path restriction enumeration as an étale family;
3. non-descent and common target clusters on the source-locked portion of
   the deck limit set, including both wrapping points;
4. the degree-two unscaled collar-width source-hypothesis no-go;
5. unchanged-tower retiming persistence; and
6. the revised-localization subgroup criterion conditional on its lift
   hypothesis.

Do not promote:

```text
DIRECT_DECORATION_OUTER_CAP_FOOTPRINT
DIRECT_DECORATION_PSEUDO_PIECE_PATH_LIFT_EXHAUSTION
DIRECT_DECORATION_ALL_DEPTH_CONTACT_CLOSURE
VIRTUAL_WAVE_MARKED_CORRESPONDENCE
VIRTUAL_WAVE_HORIZON_CERTIFICATE
VIRTUAL_AUGMENTED_ATOM_PORT_CERTIFICATE
UNIVERSAL_PROTECTED_TOWER_CLOSURE
MLC
```

The next gate is
`DIRECT_DECORATION_WAVE_PROOF_USE_LEDGER`, followed by the four typed
geometric-trace nodes listed after (11.1).  It is not another attempt to
identify the canonical resolution with the whole actual KL tile.

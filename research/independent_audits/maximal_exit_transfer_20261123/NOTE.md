# Countable restriction assembly and exact cyclic-end width transfer

**2026-11-23. Written proofs; not Lean formalizations.**

This note addresses the actual stationary exit interface in
`KKL_STATIONARY_FINAL_FIXED_COMPONENT_EXIT`, using the same surfaces and
local-width definition as Kahn–Kapiamba–Lyubich (KKL). It combines and
sharpens the archive's existing repair template as follows:

1. A Borel family of embedded paths under a holomorphic immersion has a
   countably coded Borel family of **all** maximal proper restrictions.
   Borel endpoint and marking filters can be imposed on this family. Thus,
   once an eligible fixed-component exit exists for each input leaf, a
   measurable exit lamination exists without an independently supplied
   continuous access seed or a product foliation. The rational-seed
   construction is already in BOWR §7.2; the proof below generalizes its
   endpoint test to the actual final punctured surface.
2. For a lamination from one entire ideal boundary circle to other ideal
   boundary components, its width is at most the **cyclic-cover local
   width** of that circle. Under a finite covering that local width scales
   exactly by the degree on the circle. Applied to the archive's already
   constructed stationary degree-two end, this gives

   \[
   \boxed{\mathcal W(A_m)\leq2\mathcal W(\mathcal RF)}.
   \tag{0.1}
   \]

3. For the terminal estimate one may select one restriction per parent
   and transport densities directly. The restrictions need only be
   proper in the final surface; they need not survive the separate
   marking filters used to define the next dynamical Wave. This weakens
   the remaining exit premise to the unfiltered condition E0(Q) in §5.
4. In the actual Kahn disk category, two physical downstairs hits already
   give the weaker exit condition E1(Q): either an inner-to-inner exit or
   an inner-to-outer exit. A bounded holomorphic function and boundary
   uniqueness force any failed finite-time lift to land at one outer
   ideal point. Consequently the bound follows from the actual N2
   pass-through conclusion at the two valid indices, without a separate
   common-lift, retained-exit, or target-lamination premise; see §6.

The native application remains **conditional on the actual N2 physical
pass-through conclusion** at the two indices specified in Corollary 6.5.
It does not prove that conclusion, the two-path-break argument that is
supposed to supply it, the stationary theorem in full, a universal
protected tower, or MLC.
The earlier degree-two graph/collar realization is an input already proved
in the archive, not a new contribution here. No historical ledger status
is changed.

## 1. Sources, objects, and the precise advance

The primary source is J. Kahn, A. Kapiamba, M. Lyubich,
[*MLC for parabolically bounded primitive renormalization*,
arXiv:2606.27272v1](https://arxiv.org/html/2606.27272v1):

| Source location | Role in this note |
|---|---|
| §1.4 | Proper paths extend to the ideal boundary; paths are considered up to reparameterization. |
| §2.2 and Appendix A.2.4 | Localization and the local width of an entire ideal boundary circle are defined by its peripheral cyclic cover. |
| Lemma 4.3, equation (4.6) | For the actual small-Julia cycle, \(\mathcal W(J_k)\leq\mathcal W(J_0)=\mathcal W(\mathcal RF)\). |
| Lemma 6.31 and equations (6.32)–(6.34) | The stationary final-exit argument being repaired. |
| Appendix A.1 | Ideal marking, subordination, and the short-path filter. |
| Appendix A.3.2, Lemma A.11 | Immersion restriction and width domination. |

Relevant previous archive proofs are:

- [Borel ordered Wave realization, Theorem BOWR and §§4–5, 7.2](../../mlc_unified/kkl_stationary_n1_borel_ordered_wave_realization_20260726.md): a standard-Borel leaf space, jointly Borel evaluation, Borel ideal endpoints, and countably coded filtered maximal restrictions. Section 2 below reproves that construction and allows endpoint tests in a different, explicitly specified ambient ideal surface.
- [Access-seeded maximal lifts, Theorem 3.1](../../mlc_unified/kkl_access_seeded_maximal_lift_measurability.md): simultaneous continuity when a continuous product family and an access seed have already been provided.
- [Filled graph naturality, Lemma 3.4 and Theorems 4.1, 5.2](../../mlc_unified/pql_iterate_filled_graph_naturality.md): the actual final components, isolating holomorphic neighborhoods, and degree two on their whole ideal boundary circles; its Corollary 5.3 gives the previous conditional bound \(4\mathcal W(\mathcal RF)+4\).
- [Stationary occurrence obstruction, equations (10.4)–(10.6)](../../mlc_unified/stationary_occurrence_collision_obstruction.md): the retained fixed-component exit predicate. The statement that a leaf passes through a continuum is weaker than this predicate.

The descriptive-set input is the Lusin–Souslin theorem: an injective Borel
map between standard-Borel spaces has Borel image and a Borel inverse onto
that image; see A. S. Kechris, *Classical Descriptive Set Theory* (1995),
Theorem 15.1 and Corollary 15.2,
[DOI 10.1007/978-1-4612-4190-4](https://doi.org/10.1007/978-1-4612-4190-4).
This is used to identify the geometric support as Borel. The countable
enumeration below is constructed explicitly; no uncountable selection
theorem is invoked.

The cover and modulus facts are classical. The contribution is their
fully typed combination at this archive's exit interface, the extension
of the existing Borel construction to final-surface endpoint tests, and
the removal of unnecessary marked-retention and pushforward-extraction
premises from the terminal bound. No external priority claim is made.

## 2. Borel enumeration of all maximal lifted components

### 2.1 Setting

Let \(X,Y\) be second-countable Riemann surfaces and let
\(i:X\to Y\) be a holomorphic immersion. For this section only the local
homeomorphism property is used; \(i\) need not be a covering or be globally
injective.

Let \(\Lambda\) be a standard-Borel space. Suppose

\[
e:\Lambda\times(0,1)\longrightarrow Y
\]

is jointly Borel, each \(e_\lambda\) is a topological embedding, and
different leaves have disjoint images. Assume the ideal closure
\(X^i=X\cup\partial^iX\) is a second-countable Hausdorff bordered surface.
It is locally compact and admits a compatible complete metric. In
particular this applies to the cusp-free ideal surfaces used below. The
metric used to test convergence is a complete metric on **this ideal
closure**, not the Euclidean metric of an ambient planar drawing.

In the application the embedding hypothesis follows from the proper
ideal-path presentation: an injective interior path with continuous
extension to ideal endpoints cannot accumulate at an interior image
point when its parameter tends to an endpoint. Continuous injectivity
alone, without this embedding or properness condition, would not justify
the component identification in §2.2.

For each \(\lambda\), a maximal lift is an embedded curve

\[
\ell:(a,b)\longrightarrow X,\qquad
0\leq a<b\leq1,\qquad i\ell(t)=e_\lambda(t),
\tag{2.1}
\]

maximal among extensions of that same lift. It is called ideal-proper
when both limits at \(a,b\) exist in \(X^i\) and belong to
\(\partial^iX\). These are actual ideal limits. Escape from compact sets
alone is not substituted for them.

### Theorem 2.1 — countable Borel restriction atlas

There is a Borel subset \(Z\subset\Lambda\times\mathbb N\) whose fiber
over \(\lambda\) indexes every distinct maximal lift of \(e_\lambda\)
exactly once. Its endpoint times \(a(z),b(z)\) are Borel, and

\[
E(z,u)=\ell_z\bigl(a(z)+(b(z)-a(z))u\bigr),\quad 0<u<1,
\tag{2.2}
\]

is jointly Borel and continuous in \(u\). The ideal-proper locus
\(Z_{\rm pr}\) is Borel. Both ideal endpoint maps on \(Z_{\rm pr}\) are
Borel. The evaluation map on any Borel subset of \(Z_{\rm pr}\), times
\((0,1)\), is injective, and its image in \(X\) is Borel.

#### Proof

**Step 1: a countable set of all possible seeds.** Choose a countable
cover \(U_j\) of \(X\) such that
\(i|_{U_j}:U_j\to V_j\) is a homeomorphism onto an open subset of \(Y\).
Enumerate pairs \((q,j)\) with \(q\in\mathbb Q\cap(0,1)\). Whenever
\(e_\lambda(q)\in V_j\), use the Borel seed

\[
s_{q,j}(\lambda)=(i|_{U_j})^{-1}(e_\lambda(q)).
\tag{2.3}
\]

Local inverse charts give a unique maximal lift through each seed.
Every maximal lift contains a rational time and at that time a point in
some \(U_j\), so this list finds every lift. This argument also proves
countability per leaf. It does not assume a finite sheet alphabet.

**Step 2: Borel maximal continuation.** Give
\(C((0,1),Y)\) its compact-open Polish topology. The map
\(\lambda\mapsto e_\lambda\) is Borel: on continuous paths the Borel
structure is generated by evaluation at a countable dense set of times.
For a fixed seed time \(q\), consider the universal input space

\[
\mathscr P_q=\{(\gamma,x):i(x)=\gamma(q)\}.
\]

For a fixed compact interval \([r,s]\subset(0,1)\) containing \(q\),
the set of inputs whose lift exists throughout \([r,s]\) is open in
\(\mathscr P_q\). To see this, cover the lifted compact segment of one
such input by finitely many inverse charts and subdivide \([r,s]\) so
successive segments and transition points lie inside these charts and
their overlaps. A sufficiently small compact-open perturbation of the
path and of its starting point preserves all these finitely many open
conditions. The inverse formulas then give its lift continuously.

Consequently the maximal continuation domain, with time retained, is
open, and the universal lifted evaluation is continuous there. Its
left and right lifetime endpoints are respectively upper and lower
semicontinuous. Composing with the Borel data (2.3) gives Borel lifetime
endpoints and a Borel lift field. Substituting the Borel affine change of
time in (2.2) preserves Borelness. The endpoint times may be 0 or 1;
the open interval remains nonempty because it contains the seed time.

**Step 3: remove duplicates without an uncountable quotient.** Two
seed codes define the same lift exactly when the time of the second
seed lies in the first lift's lifetime and the first lifted evaluation
at that time equals the second seed. This is a Borel test. Equality at
one time implies equality on the common interval by local uniqueness;
maximality then makes the intervals identical. Keep a seed only if no
smaller seed code gives the same lift. There are only finitely many
smaller natural-number codes at each test. This gives a Borel
\(Z\subset\Lambda\times\mathbb N\) with no repeated component.

**Step 4: test actual ideal limits.** Fix a compatible complete metric
\(d_i\) on \(X^i\). The left endpoint exists if and only if

\[
\forall k\ \exists n\ \forall r,s\in\mathbb Q\cap(0,1/n):
d_i(E(z,r),E(z,s))<2^{-k}.
\tag{2.4}
\]

Continuity in the path variable extends this rational Cauchy criterion
to all times, with an inessential adjustment of \(k\). Completeness
gives its limit. The same test with \(1-r,1-s\) handles the right end.
These are countable Borel tests. On their intersection, the endpoint
maps are limits of the Borel sequences \(E(z,1/(n+2))\) and
\(E(z,1-1/(n+2))\); hence they are Borel. Requiring both limits to
belong to the closed boundary \(\partial^iX\) gives \(Z_{\rm pr}\).
In particular an oscillating nonlanding lift is not admitted.

**Step 5: geometric Borel support.** Each lift is injective since its
projection is injective. Two maximal lifts of the same parent leaf
that meet coincide, by uniqueness; Step 3 removed that duplication.
Lifts of different parent leaves cannot meet because their projections
are disjoint. Thus (2.2) is injective on \(Z\times(0,1)\).
Its restriction to any Borel set of codes is an injective Borel map
between standard-Borel spaces. Lusin–Souslin makes its geometric image
Borel and provides its Borel inverse. This proves every assertion. ∎

### 2.2 Why these are the full proper restriction components

For a fixed embedded parent, \(i^{-1}(|e_\lambda|)\) is locally a
one-dimensional manifold, with the parent parameter serving as a local
coordinate. Each connected component maps locally homeomorphically to
an interval. Continuing its parameter coordinate shows that it is one
of (2.1), and conversely each maximal lift is a component. A closed
circle component cannot map locally homeomorphically to an interval.

A proper subpath of such a component cannot acquire an ideal endpoint
at an interior lifetime: continuity gives an interior point there.
Accordingly the ideal-proper maximal lifts are exactly the proper
components in KKL's immersion restriction, up to reparameterization.

### Lemma 2.2 — endpoint and native marking filters are Borel

On \(Z_{\rm pr}\), impose any of the following conditions:

- the two endpoints lie in specified Borel parts of the ideal boundary;
- the endpoints belong to intervals of a countable ideal marking;
- the path is not subordinate to any multi-interval of combinatorial
  length at most two in that marking;
- the path is not subordinate to a single interval of the immersion's
  pulled marking.

The remaining code set is Borel.

#### Proof

Endpoint conditions follow from Theorem 2.1. For subordination, cover
the boundary marking intervals by countably many relatively compact
boundary arcs and treat a pair of such endpoint charts at a time.
Continuous paths in the bordered surface with endpoints in these
charts have discrete relative homotopy types, where endpoints are
allowed to slide inside their respective charts. Each type is open
in that path space: a finite chain of simply connected charts covering
a compact path gives a homotopy for sufficiently close paths, including
the two short boundary endpoint adjustments. There are countably many
types, since a second-countable surface has a countable triangulation.

For charts contained in a specified connected boundary set \(B\), being
subordinate to \(B\) is constant on each such type. It means that the
type is representable in an arbitrarily small inward collar of \(B\).
Endpoint sliding within \(B\) does not change this property, so this
mobile-endpoint test is equivalent to the original fixed-endpoint
subordination after adding the short boundary paths. If \(B\) is an
entire circle, all its allowed peripheral winding classes are retained;
they are not collapsed to one class. The set of subordinate types is
therefore Borel. The properly compactified path code is Borel into
\(C([0,1],X^i)\), as follows again from its rational evaluations.

There are only countably many intervals and multi-intervals of length
at most two in a countable ideal marking. Take the countable union of
their subordinate loci and then its complement. Apply the same
argument to the coarse pulled intervals. ∎

### Corollary 2.3 — pointwise exits assemble measurably

Let \(J\) be one fixed ideal circle of \(X\), and let \(B_\partial\)
be a Borel union of other ideal boundary components. Apply the filters
of Lemma 2.2 and require one end in \(J\), the other in
\(B_\partial\). If every input leaf has at least one surviving code,
the union of **all** surviving lifts is a Borel lamination that supplies
a proper restriction for every input leaf.

One may instead retain the least surviving seed code over each
\(\lambda\). Its locus is Borel, by testing all smaller codes, and it
also gives a Borel lamination dominating every parent leaf. Retaining
all codes is preferable when later arguments need occurrence data.

This corollary constructs neither the nonempty sections nor the
endpoints. It proves that their assembly needs no further measurable
selection hypothesis once their pointwise geometric existence is
proved in the indicated path presentation.

### 2.4 Endpoint tests in the full final surface

There is an ambient-surface version of Theorem 2.1 that is needed below.
Suppose \(X_0\) is an open subset of a Riemann surface \(X_f\), and the
immersion is defined on \(X_0\). Enumerate maximal lifts there, but test
the two endpoint limits in the specified bordered surface \(X_f^i\),
requiring them to lie in \(\partial^iX_f\). The proof of Step 4 works
verbatim with a complete metric on \(X_f^i\); all other steps are
unchanged. Thus this final-surface proper locus and its endpoint labels
are Borel. Landing on an artificial interior boundary of \(X_0\) is
not accepted by this test.

In the application \(I:X_f\to\mathcal U\) is globally defined and
\(X_0=X_f\cap I^{-1}(Y)\), where the parent paths lie in \(Y\).
The preimage of each parent support is exactly the same set whether
computed in \(X_0\) or in \(X_f\), with the same subspace topology.
Its components therefore agree. If a lifted path had an interior-time
continuation point \(x\in X_f\), continuity would give
\(I(x)=e_\lambda(t)\in Y\), hence \(x\in X_0\). Restricting to
this exact inverse image causes no artificial interior-time stopping.
An interior \(X_f\) limit at a parent endpoint fails the final-surface
properness test, as it should.

If a separate argument needs native marking filters on \(X_0^i\),
run a second ideal endpoint test there and apply Lemma 2.2 on that
surface. Final-surface landing does not by itself identify a native
\(X_0\) ideal end or a native homotopy class. The terminal estimate
below does not need those additional filters.

### Proposition 2.5 — one selected restriction dominates its parents

In the setting of §2.4, suppose each parent leaf has at least one
maximal lift which is proper in \(X_f^i\) and satisfies a specified
Borel endpoint condition. Keep the least qualifying seed code for each
parent and let \(\mathscr B\) be the resulting family. Then

\[
\mathcal W_Y(\{e_\lambda\})
\leq\mathcal W_{X_f}(\mathscr B).
\tag{2.5}
\]

#### Proof

The least-code selection and evaluation are Borel by Theorem 2.1 and
§2.4. Distinct selected lifts are disjoint. The immersion \(I\) is
injective on their entire union: only one lift was selected per parent,
its projection is an embedded subpath, and different parents are
disjoint. Lusin–Souslin makes the projected support and its inverse
Borel.

Let \(\rho\) be any Borel density admissible for \(\mathscr B\).
Restrict it to this Borel support and push it to \(Y\) using the
conformal change of length under \(I\); put zero elsewhere. Every
parent contains the image of its selected lift, so its length in the
pushed density is at least one. The change-of-area formula and
injectivity on the support give a pushed area no larger than
\(\int_{X_f}\rho^2\). Taking the infimum over admissible densities
proves (2.5). This is the modulus definition of extremal width. ∎

This proof is the needed unmarked domination calculation. It avoids
any assumption that the selected path survives a dynamical Wave filter
or that the immersion maps all of \(X_f\) into the parent surface.

## 3. Direct domination by a cyclic-end width

Let \(X=\mathbb D/\Gamma\) be a hyperbolic Riemann surface and let
\(J\) be an entire ideal boundary circle with hyperbolic peripheral
stabilizer. Other ends may include cusps; no path endpoint in this
theorem is assigned to a cusp. A lift
\(\widetilde J\subset\partial\mathbb D\) has stabilizer
\(H=\langle\tau\rangle\), with \(\tau\) hyperbolic. Write

\[
\mathbb A_J=\mathbb D/H,\qquad
\pi_J:\mathbb A_J\longrightarrow X.
\tag{3.1}
\]

The interval \(\widetilde J\) is one of the two intervals between the
fixed points of \(\tau\). It descends to one whole ideal boundary
circle \(J_*\) of \(\mathbb A_J\); \(\pi_J:J_*\to J\) is a
homeomorphism. The other interval descends to the other boundary circle.
KKL Appendix A.2.4 defines

\[
\mathcal W_X(J)=\mathcal W(\mathbb A_J)
=\frac1{\operatorname{mod}(\mathbb A_J)}.
\tag{3.2}
\]

### Theorem 3.1 — a lamination with one fixed end

Let \(\mathscr B\) be a lamination of simple proper paths in
\(X\), supplied with a standard-Borel leaf space and jointly Borel
evaluation and ideal endpoint maps, as in Theorem 2.1. Suppose every
leaf has exactly one endpoint on \(J\) and its
other endpoint on an ideal boundary component different from \(J\).
Then

\[
\boxed{\mathcal W_X(\mathscr B)\leq\mathcal W_X(J).}
\tag{3.3}
\]

The result requires neither local connectivity of the planar boundary
impressions nor a claim that \(\pi_J\) is globally injective.

#### Proof

Orient each leaf from \(J\). Since \(J_*\to J\) is a homeomorphism,
its initial ideal endpoint and a small one-sided collar give one
specified lift to \(\mathbb A_J\). Continue it by the covering property.
Near its other endpoint the original proper path lies in an ideal
boundary chart, so the lifted tail also converges in an ideal boundary
chart. This endpoint cannot lie on \(J_*\): that circle projects to
\(J\), whereas the stipulated endpoint lies on a different component.
Equivalently, in the universal disk the terminal lift belongs to the
complementary interval between the fixed points of \(\tau\). Thus the
lift joins the two boundary circles of \(\mathbb A_J\).

The lifts form a lamination \(\widetilde{\mathscr B}\). Each leaf is
simple, and lifts of distinct leaves cannot meet. Moreover
\(\pi_J\) is injective on their **whole union of interiors**: two
points projecting to the same point would belong to the same original
embedded leaf and the same parameter value. Their lifts agree by the
chosen initial end. This support assertion, not global injectivity of
the localization, is the fact needed for width transport.

The support and the inverse on it are Borel. For example, enumerate
lifts by Theorem 2.1, select the unique one with initial endpoint on
\(J_*\), and apply Lusin–Souslin to evaluation. Transport a Borel
admissible conformal density on the lifted support downstairs by this
one-to-one conformal map, and put zero off the support. The length of
each leaf is unchanged. The conformal change-of-area formula shows
that the resulting area is at most the original area. Reversing the
same operation gives

\[
\mathcal W_X(\mathscr B)
=\mathcal W_{\mathbb A_J}(\widetilde{\mathscr B}).
\tag{3.4}
\]

This is a metric calculation on a measurable support; it does not
replace width by an arbitrary transverse measure. The lifted family
is contained in the full family joining the two annulus boundaries.
Monotonicity of extremal width and (3.2) give (3.3). ∎

**Why the endpoint qualifier matters.** A family of short
boundary-parallel arcs with both endpoints on \(J\) can have arbitrarily
large width. Its distinguished lifts return to \(J_*\), so they do not
cross the annulus. Equation (3.3) does not cover such families. This
also explains why a bare statement that a lamination ends at \(J\)
cannot replace the precise hypothesis.

**Why this is not a false embedding inference.** The annular
localization may have many collisions away from the selected leaf
support. No inverse map on the whole surface is constructed or used.
The argument concerns the unique lift of each disjoint proper leaf
from the distinguished circle, with its full winding information.

## 4. Exact transfer under a finite covering

### Theorem 4.1 — local widths scale by the whole end degree

Let \(p:X'\to X\) be an unbranched finite holomorphic covering of
the indicated punctured surfaces. Let \(J'\) and \(J\) be entire ideal
boundary circles such that \(p:J'\to J\) has degree \(d\). Then

\[
\boxed{\mathcal W_{X'}(J')=d\,\mathcal W_X(J).}
\tag{4.1}
\]

Consequently every lamination \(\mathscr B\) in \(X'\) with the
Borel path presentation in Theorem 3.1 and
one end on \(J'\) and the other on a different ideal boundary component
satisfies

\[
\boxed{\mathcal W_{X'}(\mathscr B)\leq d\,\mathcal W_X(J).}
\tag{4.2}
\]

#### Proof

Use the same universal disk for both surfaces, identifying their
groups as \(\Gamma'\leq\Gamma\). Choose the lifts of \(J',J\)
compatibly. If the target stabilizer is \(\langle\tau\rangle\), the
source stabilizer is

\[
\Gamma'\cap\langle\tau\rangle=\langle\tau^d\rangle.
\tag{4.3}
\]

Indeed the index of these peripheral groups is exactly the degree of
the circle covering, or equivalently the monodromy cycle length at this
end. The induced map between the cyclic annuli is therefore a
holomorphic degree-\(d\) annulus covering. In round coordinates it is
\(z\mapsto z^d\), up to conformal coordinate choices, so

\[
\operatorname{mod}(\mathbb A_{J'})
=\operatorname{mod}(\mathbb A_J)/d.
\]

Taking reciprocal moduli proves (4.1). Apply Theorem 3.1 on \(X'\)
to obtain (4.2). ∎

It is the degree on the **whole source ideal circle**, not a single
access or an independently assigned vertex degree, that enters (4.3).
For a proper map on isolating Jordan neighborhoods of full nondegenerate
continua, whose critical values lie in the deleted target continuum,
the restriction between their annular collars is unbranched. Annulus
uniformization then identifies this degree with the ideal-circle degree,
even when the embedded continuum is not locally connected. The archive's
filled-graph Lemma 3.4 already proves this transfer for the actual final
components used here.

No target lamination needs to be extracted from \(p_*\mathscr B\).
Images may intersect or coincide. Such collisions do not affect the
source local width or the stabilizer calculation. In particular the
other source endpoint is allowed to project to the same target component
\(J\); no false distinct-image assumption is imposed.

## 5. Application to the native stationary exit

Fix the archive's source-defined primitive stationary setting, put

\[
m=b+2,\quad
X'=\mathcal U^m\setminus\mathcal K^m,\quad
X=\mathcal U\setminus\mathcal K,\quad p=P_m=f^m,
\]

and choose one of the canonical final graph components
\(Q=\widehat K_b\) or \(Q=\widehat K_{b+1}\). Write
\(J'=\partial^iQ\). Filled-graph Theorems 4.1 and 5.2, including their
isolating neighborhoods, establish:

1. \(Q\) is an actual component of \(\mathcal K^m\).
2. \(p:X'\to X\) is a finite unbranched covering.
3. \(J'\) covers the whole ideal circle \(J_k=\partial_CK_k\)
   with degree two, with \(k=2\) or \(k=1\), respectively.

Let \(A_m\) be the stationary Wave supplied by the existing N1
construction, with its BOWR standard-Borel proper-path presentation.
Define the exact additional geometric condition:

> **E0(Q).** For every leaf \(\alpha\in A_m\), its preimage under the
> final immersion contains a maximal component that is ideal-proper
> in the final surface \(X'\), has one endpoint on \(J'\),
> and has its other endpoint on an ideal boundary component belonging
> to \(\mathcal K^m\setminus Q\).

Let \(I_m:\mathcal U^m\to\mathcal U\) be the final immersion and
\(Y=\mathcal U\setminus\mathcal T\) the parent path surface.
Apply §2.4 on the exact open domain
\(X_0=X'\cap I_m^{-1}(Y)\), testing endpoints in **\(X'^i\)**.
Thus neither an artificial boundary of \(X_0\) nor an ideal endpoint
of a different surface can count as an exit.

The older retained-exit predicate additionally requires native marking
and subordination filters. It implies E0(Q), but that stronger predicate
is unnecessary for this terminal bound. The selected exit family is not
asserted to be a dynamical successor Wave. KKL's unmarked domination
lemma A.11 precedes those filters; Proposition 2.5 provides the direct
calculation with the exact two surfaces used here.

### Theorem 5.1 — exact stationary bound from pointwise final exits

Under E0(Q),

\[
\boxed{\mathcal W(A_m)\leq2\mathcal W(\mathcal RF).}
\tag{5.1}
\]

#### Proof

Theorem 2.1 and §2.4 enumerate the final proper restrictions and their
ideal endpoints as Borel data. Require one endpoint on \(J'\) and
the other on the union of the other small-Julia-component circles.
E0(Q) makes every parent section nonempty. Keep its least qualifying
code. Proposition 2.5 gives a Borel lamination \(\mathscr B\) of
one selected restriction per parent, each joining \(J'\) to a
different component, with

\[
\mathcal W(A_m)\leq\mathcal W_{X'}(\mathscr B).
\tag{5.2}
\]

Theorems 3.1 and 4.1 apply on the actual final punctured surface and give

\[
\mathcal W_{X'}(\mathscr B)
\leq\mathcal W_{X'}(J')
=2\mathcal W_X(J_k)
\leq2\mathcal W(\mathcal RF).
\tag{5.3}
\]

The last inequality is the same source cycle-width comparison used in
the older repair, KKL Lemma 4.3, equation (4.6). Combining (5.2) and
(5.3) proves (5.1). ∎

The proof uses no coefficient-one Wave pushforward theorem, no choice
of a target sublamination, no assertion of distinct projected terminal
paths, and no large-width absorption of an additive constant. The
constant two comes from the actual single critical encounter in the
canonical final component. It is not a numerical fitted coefficient.

### 5.2 Exact effect on the existing obligations

| Existing question | What this note establishes |
|---|---|
| Does arbitrary pointwise choice automatically give a Borel support? | Not in general. Here the local-homeomorphism restriction relation is explicitly countably coded, so it does. |
| Is a continuous product foliation and a chosen access seed needed for this assembly? | No; the existing BOWR Borel path presentation is enough. |
| Is the whole-end degree two known? | Yes, from the earlier filled-graph/collar proof, retained as an input. |
| Is a pushforward-lamination extraction needed to estimate the final exit family? | No; cyclic-end local width gives (5.3) directly. |
| Must the terminal exit survive the native marking filters? | No. E0(Q) and one selected lift per parent suffice for direct density domination. |
| Does pass-through of two continua prove E0(Q)? | The prescribed inner-to-inner conclusion requires a continued lift. Section 6 instead proves the sufficient E1(Q), allowing an outer endpoint if continuation fails. |
| Does this close N2 or global MLC? | No. Section 6 supplies the terminal estimate from actual physical pass-through; the upstream pass-through/two-path-break argument remains open. |

Within the stated native surfaces and existing BOWR presentation, the
stronger inner-to-inner N3 statement retains its geometric predicate
E0(Q). It is no longer necessary for the terminal quantitative route:
§6 obtains the sufficient E1(Q) directly from two physical hits, and
then obtains the same exact width bound. The remaining native premise
for that route is the upstream N2 physical pass-through implication.

## 6. From physical hits to proper final exits

There are two distinct extraction statements. A common compact lift with
two continuum hits gives the inner-to-inner exit E0(Q). For the terminal
width bound, allowing the other endpoint to lie on the **outer** ideal
circle removes the common-lift premise in the actual Kahn disk setting.
Neither assertion proves that the stationary Wave has the required
physical hits; that is an upstream dynamical question.

### 6.1 End-cuts at isolated full continua

Let \(S\) be a conformal disk, let
\(\mathscr H=\{H_1,\ldots,H_r\}\) be a finite family of pairwise
disjoint nondegenerate full continua compactly contained in \(S\), and
put \(X_f=S\setminus\bigcup\mathscr H\). Each \(H_j\) determines
one whole ideal boundary circle of \(X_f\).

We use the classical Koebe end-cut theorem in precisely this form: a
conformal map from a simply connected planar domain onto the unit disk
has a limit along every Jordan end-cut of the domain. An end-cut here
is an embedded arc whose interior lies in the domain and whose one
terminal point lies on its physical boundary. The limit lies on the
unit circle, by continuity of the inverse map at interior disk points.
This does not say that every physical boundary point has a unique
prime end, or that every escaping curve lands.

The theorem is stated explicitly in T. Adamowicz,
[*Prime ends in metric spaces and quasiconformal-type mappings*,
§6.1](https://doi.org/10.1007/s13324-019-00292-z),
*Analysis and Mathematical Physics* **9** (2019), 1941–1975.
Its reference [28] is P. Koebe, *Abhandlungen zur Theorie der konformen
Abbildung. I. Die Kreisabbildung des allgemeinsten einfach und zweifach
zusammenhängenden schlichten Bereichs und die Ränderzuordnung bei
konformer Abbildung*, *J. Reine Angew. Math.* **145** (1915), 177–223.
Only the classical simply connected conformal statement is imported;
the extra hypotheses of Adamowicz's later metric-space generalization
are not asserted for Julia continua.

To apply it to \(H_j\), choose a planar coordinate on \(S\), and
choose a Jordan disk \(E_j\Subset S\) containing \(H_j\) and
disjoint from all other \(H_k\). Such disks exist because the continua
are full, compact, and pairwise disjoint. The domain
\(\widehat{\mathbb C}\setminus H_j\) is simply connected. A Möbius
coordinate with its pole at a point of \(H_j\) different from the
end-cut's landing point puts the situation in the planar version of
Koebe's theorem. Consequently a Jordan arc in \(E_j\setminus H_j\)
landing at a point of \(H_j\) has one prime-end limit.

The inner end of the annulus \(E_j\setminus H_j\) is the same
conformal ideal circle whether viewed in
\(\widehat{\mathbb C}\setminus H_j\) or in \(X_f\): both
surfaces agree on this whole annular neighborhood of the isolated
continuum. Thus the end-cut has a genuine ideal limit on the
\(H_j\)-circle of \(X_f^i\). Local connectivity of \(H_j\) is
not used. The end-cut, not its physical landing point alone, supplies
the access.

### Lemma 6.1 — extraction from one compact unpunctured lift

Let \(i:S\to U\) be a holomorphic immersion and let
\(\alpha:(0,1)\to U\) be an embedded path. Suppose some compact
subinterval \([u,v]\subset(0,1)\) has a continuous lift
\(\sigma:[u,v]\to S\), with

\[
i\sigma(t)=\alpha(t),\qquad
\sigma(u)\in Q\in\mathscr H,\qquad
\sigma(v)\in H_j\ne Q.
\tag{6.1}
\]

Then \(i^{-1}(|\alpha|)\cap X_f\) has a maximal component
which is ideal-proper in \(X_f\), with one endpoint on the
\(Q\)-circle and the other on a different \(\mathscr H\)-circle.

#### Proof

Let \(b\) be the first time in \([u,v]\) at which \(\sigma\)
hits \(\bigcup(\mathscr H\setminus\{Q\})\), and let \(a\)
be its last hit of \(Q\) in \([u,b]\). These times exist by
compactness and continuity. Pairwise disjointness and compactness give
\(u\leq a<b\leq v\). By their definitions,

\[
\sigma((a,b))\subset X_f,
\quad \sigma(a)\in Q,
\quad \sigma(b)\in H_k\ne Q.
\tag{6.2}
\]

The lift is injective, because its projection \(\alpha\) is
injective. Thus its tails, including the physical endpoints in (6.2),
are Jordan end-cuts at the two isolated full continua. Section 6.1
gives actual ideal limits on their two different ideal circles.
No extension across \(a\) or \(b\) is possible inside \(X_f\),
because the existing continuous limits belong to the deleted continua.
Hence \(\sigma|(a,b)\) is a maximal lifted component, by §2.2.
It is ideal-proper as claimed. ∎

In the native graph notation, a sufficient condition for (6.1) is
that the parent segment \(\alpha([u,v])\) lie in the analytic
graph neighborhood \(V_m\) of filled-graph Lemma 3.4 and hit the
two downstairs graph continua there. Then
\(\sigma=\Gamma_m\circ\alpha\) is the required compact lift.
Without this condition, two local graph germs alone do not establish
a common compact lift. The next two lemmas handle a failure of
continuation by accepting an outer exit instead.

### Lemma 6.2 — a bounded holomorphic function detects one boundary point

Let \(h:\mathbb D\to\mathbb C\) be bounded, holomorphic, and
nonconstant. Let \(z:[0,1)\to\mathbb D\) be continuous with
\(|z(t)|\to1\). If \(h(z(t))\to w\in\mathbb C\), then
\(z(t)\) converges to one point of \(\partial\mathbb D\).

#### Proof

On a sufficiently late tail \(z(t)\ne0\), so choose a continuous
real argument \(\theta(t)\) with
\(z(t)=|z(t)|e^{i\theta(t)}\). Suppose first that this real
argument is bounded on a tail but does not converge. Its finite
liminf \(l\) and limsup \(L\) satisfy \(l<L\). Choose a
nonempty interval \(B\Subset(l,L)\) of length less than \(2\pi\).
For every \(\theta\in B\), the intermediate value theorem gives
times \(t_n\to1\) such that \(\theta(t_n)=\theta\).

If instead \(\theta(t)\) is unbounded above or below on every
tail, its continuity and boundedness on each compact time interval
give arbitrarily late crossings of \(\theta+2\pi k\) for every
angle \(\theta\), along an appropriate unbounded sequence of
integers \(k\). These two alternatives cover every failure of
convergence of \(z(t)\) on the unit circle: convergence of the real
argument would already give convergence of \(z(t)\).

Accordingly, failure of the asserted conclusion gives a positive-length
arc \(B_*\subset\partial\mathbb D\) such that, at every
\(e^{i\theta}\in B_*\), there are radii \(r_n\to1\) with

\[
h(r_ne^{i\theta})\longrightarrow w.
\tag{6.3}
\]

Fatou's theorem gives a radial limit for \(h\) at almost every
point of \(B_*\). At each such point (6.3) forces that radial
limit to equal \(w\). The boundary uniqueness theorem for bounded
holomorphic functions then forces \(h-w\equiv0\), a contradiction.
Thus the boundary cluster set is a singleton, and compactness of
\(\overline{\mathbb D}\) gives convergence to it. ∎

The analytic inputs in the last paragraph are precisely Theorems A
(Fatou) and B (F. and M. Riesz), stated on p. 1147 of A. Danielyan,
[*The radial limits and boundary uniqueness*,
*Comptes Rendus Mathématique* **362** (2024), 1147–1153](https://doi.org/10.5802/crmath.609).
The angular-crossing argument is included above to specify why these
theorems apply to the possibly nonlanding curve under consideration.

### Lemma 6.3 — finite-time escape of an immersion lift lands at the outer end

Let \(S,U\) be hyperbolic conformal disks, let \(i:S\to U\)
be a holomorphic immersion, and let \(\alpha\) be continuous on an
open interval containing \([u,v]\). Suppose a lift \(\sigma\)
through time \(u\) has a finite maximal right lifetime \(b\leq v\).
Then \(\sigma(t)\), as \(t\uparrow b\), escapes every compact
subset of \(S\) and converges to one point of the outer ideal
boundary of \(S\). The same point is on the outer ideal circle of
\(S\setminus\bigcup\mathscr H\).

#### Proof

Suppose \(t_n\uparrow b\) and \(\sigma(t_n)\to x\in S\).
Continuity gives \(i(x)=\alpha(b)\). Choose an inverse chart
\(i:O\to V\) at \(x\) and a smaller target neighborhood of
\(\alpha(b)\) whose closure lies in \(V\). A sufficiently late
parent segment, continuing slightly beyond \(b\), lies in \(V\).
Starting at \(\sigma(t_n)\in O\), its inverse-chart lift agrees
with \(\sigma\) by uniqueness and extends it beyond \(b\), a
contradiction. Thus there is no compact accumulation in \(S\).

Choose Riemann maps \(\phi:S\to\mathbb D\) and
\(\psi:U\to\mathbb D\). Then

\[
z(t)=\phi(\sigma(t)),\qquad
h=\psi\circ i\circ\phi^{-1}
\tag{6.4}
\]

satisfy \(|z(t)|\to1\) and
\(h(z(t))=\psi(\alpha(t))\to\psi(\alpha(b))\).
The holomorphic function \(h\) is bounded and nonconstant, so
Lemma 6.2 gives one unit-circle limit. This is the outer ideal endpoint
in the disk coordinate. Since \(\bigcup\mathscr H\Subset S\),
the original and punctured surfaces coincide on a whole outer annular
collar. Their outer ideal circles agree there. ∎

This argument uses the **unpunctured** immersion and a failure at a
finite interior parent time. It makes no assertion that a lift ending
at a parent ideal endpoint is automatically proper in the final
surface. In particular it never replaces the full filled set by the
small-Julia cycle, nor assumes that the Hubbard carrier has no edges
outside that cycle.

### Theorem 6.4 — two downstairs filled-set hits give an inner or outer exit

In addition to the setting of §6.1, suppose \(S,U\) are hyperbolic
conformal disks, \(C\Subset S\) and \(K\Subset U\) satisfy

\[
i^{-1}(K)=C,\qquad i|_C:C\longrightarrow K
\text{ is a homeomorphism},\qquad
\bigcup\mathscr H\subset C.
\tag{6.5}
\]

Fix \(Q\in\mathscr H\). Suppose an embedded parent path
\(\alpha:(0,1)\to U\) has two distinct interior times \(u,v\)
with

\[
\alpha(u)\in i(Q),\qquad
\alpha(v)\in i(H_j),\qquad H_j\ne Q.
\tag{6.6}
\]

Then \(i^{-1}(|\alpha|)\cap X_f\) contains a maximal
ideal-proper component with one endpoint on the \(Q\)-circle and
the other on **any different ideal boundary component** of \(X_f\):
either another \(\mathscr H\)-circle or the outer circle. The
second component need not be the one named in (6.6).

#### Proof

Reverse the parent parameter if necessary so that \(u<v\). Start
the unique local lift at
\(x=(i|_C)^{-1}(\alpha(u))\in Q\) and continue it maximally
in the unpunctured disk \(S\).

If it continues through time \(v\), (6.5) forces
\(\sigma(v)=(i|_C)^{-1}(\alpha(v))\in H_j\).
Lemma 6.1 supplies the asserted inner-to-inner component.

Otherwise its right lifetime \(b\leq v\) is finite. Lemma 6.3
gives escape and a unique outer ideal endpoint. If the lifted segment
\([u,b)\) hits any \(H_k\ne Q\), take such a hit at some
time \(v'<b\) and apply Lemma 6.1 on \([u,v']\).

In the remaining case it hits no other deleted continuum. Compactness
of \(Q\) and escape from every compact set show that its \(Q\)-hit
times in \([u,b)\) are nonempty and bounded away from \(b\).
Their supremum \(a<b\) is attained, by continuity. The open tail
\(\sigma((a,b))\) avoids every deleted continuum. At \(a\) it
is a Jordan end-cut landing on \(Q\), so §6.1 gives its inner ideal
limit. At \(b\) Lemma 6.3 gives its outer ideal limit. Neither end
can be extended inside \(X_f\); hence this tail is a maximal
ideal-proper component. Its two ideal boundary components are
different. ∎

### 6.5 Native application and the exact remaining premise

The topology in Lemma 6.3 is supplied by the original Kahn construction.
In J. Kahn,
[*A priori bounds for some infinitely renormalizable quadratics:
I. Bounded primitive combinatorics*, arXiv:math/0609045v3,
Definition 7.1 and §7.3](https://arxiv.org/html/math/0609045v3),
the domains of a pseudo-polynomial-like map are disks. The paragraph
immediately preceding Lemma 7.11 proves that the pullback domain is
again a connected disk, and that lemma iterates the construction.
The archive's locked source locators are `psiql2.tex` lines 16–41,
350–399, and 410–416; see
[Kahn iterate alignment, §§2–3](../../mlc_unified/kahn_iterate_complementary_component_alignment.md).

There is a conformal-type qualification, handled explicitly by Kahn's
Remark 7.2. A topological disk can have conformal type \(\mathbb C\).
If the target \(U\) is hyperbolic, each \(U^m\) is hyperbolic:
otherwise its nonconstant holomorphic map \(P_m\) to \(U\cong
\mathbb D\) would contradict Liouville's theorem. If \(U\cong
\mathbb C\), Remark 7.2 says that the source is also a plane and
the immersion is an isomorphism; iterating gives the same for \(I_m\).
In that case every compact parent segment has a compact common lift,
so Lemma 6.1 applies directly and the escape alternative is unnecessary.

For the actual final immersion, filled-graph Lemma 3.1 gives exactly

\[
I_m^{-1}(K^0)=K^m,\qquad
I_m|_{K^m}:K^m\xrightarrow{\cong}K^0.
\tag{6.7}
\]

Here \(K^0,K^m\) are the **full filled sets**. They must not be
confused with the finite unions \(\mathcal K,\mathcal K^m\) of
small Julia sets. Filled-graph Theorem 4.1 identifies the canonical
final components inside \(\mathcal K^m\subset K^m\).
Thus Theorem 6.4 applies to their actual downstairs graph images;
it does not require a globally injective immersion or a chosen
common-lift corridor.

Define the weaker endpoint predicate:

> **E1(Q).** Each parent leaf has a maximal restriction proper in
> \(X'^i\), with one endpoint on the fixed \(Q\)-circle and the
> other on any different ideal boundary component of \(X'\),
> including its outer circle.

Theorem 5.1 remains valid with E1(Q) in place of E0(Q). Indeed the
endpoint set consisting of all the other circles is Borel, so the
same least-code selection and Proposition 2.5 apply, and Theorem 3.1
already permits the outer endpoint. Consequently Theorem 6.4 proves
the following genuine reduction:

\[
\begin{gathered}
\text{every }\alpha\in A_m\text{ physically hits }I_m(Q)
\text{ and }I_m(H_\alpha),\\
H_\alpha\in\pi_0(\mathcal K^m),\quad H_\alpha\ne Q,
\quad\text{at interior parent times}
\end{gathered}
\quad\Longrightarrow\quad
\boxed{\mathcal W(A_m)\leq2\mathcal W(\mathcal RF)}.
\tag{6.8}
\]

The second hit may occur before or after the fixed-component hit, and
its component may depend on the leaf. The fixed \(Q\) and its degree
two cannot depend on the leaf. Neither the hit times nor the temporary
unpunctured lifts must be selected measurably: the countable atlas
selects the final proper components after their pointwise existence
has been proved.

The residual in (6.8) is a **two-hit statement about the actual parent
curves and actual filled graph components**. Homotopy incidence, two
separately retained stage occurrences, or equality of projected curve
names does not establish those hits. In the native stationary sequence,
however, the claimed physical pass-through implication at two valid
indices is enough; no additional binder is required after those hits.

### Corollary 6.5 — the terminal bound conditional only on the physical pass-through step

Assume the physical pass-through implication asserted in the proof of
KKL Lemma 6.31 at \(n=b\) and \(n=b+1\):

\[
\alpha\in A_{n+1}\quad\Longrightarrow\quad
|\alpha|\cap K_0^n\ne\varnothing.
\tag{6.9}
\]

Then the terminal stationary family \(A_{b+2}\) satisfies
\(\mathcal W(A_{b+2})\leq2\mathcal W(\mathcal RF)\).

#### Proof

The definition immediately before KKL Lemma 6.24 gives
\(A_n\subset A_{n-1}\) for every \(0<n<N=b+3\).
Therefore every \(\alpha\in A_m=A_{b+2}\) belongs also to
\(A_{b+1}\). Applying (6.9) at \(n=b\) and \(n=b+1\)
gives physical hits of both \(K_0^b\) and \(K_0^{b+1}\) at
interior times of that same parent curve. Both families used here are
defined; \(A_N\) is never invoked.

Filled-graph Theorem 4.1, equations (4.8)–(4.10), identifies their
unique final graph lifts as distinct components
\(\widehat K_b,\widehat K_{b+1}\subset\mathcal K^m\), with
images \(K_2\) and \(K_1\) under \(P_m\). Choose either of
these two fixed components as \(Q\), and use the other for the
second hit in Theorem 6.4. It gives E1(Q); (6.8) proves the bound. ∎

The implication (6.9) is precisely where the source asserts that
avoidance would produce two Waves and hence a break. The archive's N2
work has not proved this avoidance-to-two-Waves implication, and this
note does not prove it. Corollary 6.5 removes the **additional terminal
exit and assembly obligation after actual physical pass-through**;
it does not validate the upstream dynamical argument. It also repairs
the undefined \(A_N\) invocation by using nestedness at the two valid
indices, while retaining the already proved degree-two correction.

For the stronger inner-to-inner predicate E0(Q), a common compact lift
as in Lemma 6.1 is still a sufficient extra condition. For the actual
terminal width estimate, it is unnecessary: finite-time nonproper
escape contributes a valid outer exit under Theorem 6.4.

### Corollary 6.6 — the same terminal bound at the longer noncollision horizon

Let the primitive little-Julia cycle have period \(p\). Fix an integer
\(r\) with \(2\le r<p\), put \(m=b+r\) and \(N=m+1\), and use the
actual nested stationary families \(A_0,\ldots,A_m\) at that horizon.
If the same two physical pass-through implications (6.9) hold at
\(n=b,b+1\), then

\[
 \mathcal W(A_{b+r})\le2\mathcal W(\mathcal RF).
 \tag{6.10}
\]

In particular the longer collision argument's choice
\(N=b+5\), \(m=b+4\), \(q>b+4\), and \(p\ge q\) is covered by
\(r=4\). This statement does not assert the two pass-through implications.

#### Proof

The filled-graph identities apply to every finite \(m\). For
\(n\in\{b,b+1\}\) let \(Q_n=K_0^n\), set \(\ell=m-n\), and let
\(\widehat Q_n=\Gamma_m(Q_n)\). The actual map on the filled graph is

\[
 P_m|_{\widehat Q_n}=F^m|_{Q_n}\circ I_m|_{\widehat Q_n},
 \qquad P_m(\widehat Q_n)=K_\ell.
 \tag{6.11}
\]

We verify the component and whole-end degree rather than inferring them
from (6.11). The first \(n\) selected inverse arrows have univalent
Jordan restrictions by filled-graph Lemma 5.1. The next arrow
\(K_0\to K_1\) has its actual degree-two Jordan restriction by Lemma 4.A.
For each remaining arrow \(K_j\to K_{j+1}\), where
\(1\le j<\ell<p\), the target \(K_{j+1}\) is disjoint from the only
critical value, which belongs to \(K_1\). A small simply connected
neighborhood of that target avoids the critical value. Its selected
inverse component is therefore a univalent disk containing \(K_j\).

Shrinking backwards along this finite sequence makes the restrictions
composable. The disks can all be chosen in the finite-iterate holomorphic
graph neighborhood supplied by the predecessor's §3: only finitely many
compact subsets of the filled set are involved. Their composite is a proper degree-two restriction of
\(F^m\), whose inverse image of \(K_\ell\) is exactly \(Q_n\).
The equality follows successively from the selected inverse components,
the full central inverse equality \(F^{-1}(K_1)=K_0\), and the univalent
cycle arrows. Its source boundary maps to the terminal Jordan boundary,
which is disjoint from \(K_\ell\). Thus \(Q_n\) is an entire component
of \(F^{-m}(K_\ell)\), not merely a connected subset of one.
All critical values of this composite lie in \(K_\ell\). A connected
preimage cannot join different members of the disjoint finite cycle.
The filled-graph component and collar results (Theorem 3.2 and Lemma 3.4
of the cited predecessor) therefore give an entire component
\(\widehat Q_n\) of \(\mathcal K^m\) and degree two on its whole ideal circle.

The two terminal indices are \(\ell=r,r-1\). They are different
members of the disjoint primitive cycle, so the two graph components
are distinct. Nestedness and (6.9) give both actual hits on every
\(\alpha\in A_m\). Theorem 6.4 supplies one inner or outer exit from
either fixed graph component. Theorems 3.1 and 4.1, together with the
source comparison \(\mathcal W(K_\ell)\le\mathcal W(\mathcal RF)\),
give (6.10) exactly as before. ∎

This explicitly supplies the terminal component, degree, and width
typing for the longer horizon in
[the collision note, §6](../maximal_global_closure_20261123/MONODROMY_COLLISION.md).
It does not manufacture the canonically anchored retained occurrences or
native contour correspondence used in that note or its
[connected-carrier strengthening](../maximal_global_closure_20261123/CONNECTED_CARRIER_NONCOLLISION.md).

## 7. Adversarial boundaries and review record

The following conditions are essential:

1. **One fixed entire source end.** Choosing a different end for each
   leaf would require partitioning and accounting for all the resulting
   local widths. A single maximum would not bound their sum.
2. **Different source terminal components.** Same-circle peripheral
   arcs do not cross the cyclic annulus and defeat the unrestricted
   version of Theorem 3.1.
3. **A genuine covering of the punctured surfaces.** A degree assigned
   only to a compact continuum is insufficient until the annular
   collar/ideal-boundary argument has been supplied.
4. **Disjoint simple leaves.** These ensure injectivity on the lifted
   support in (3.4). An arbitrary intersecting family cannot use that
   argument without a separate multiplicity bound.
5. **A Borel path presentation.** This is supplied here by the earlier
   BOWR theorem; it is not inferred from an arbitrary unstructured set
   of curve names.
6. **Actual ideal convergence.** The countable limit test excludes
   nonlanding maximal lifts. It does not prove that any specified lift
   passes it.
7. **Occurrence-correct final exits.** Neither a finite incidence
   matrix, a coarser pass-through event, nor equal physical impressions
   proves E(Q).

The cyclic-cover argument was separately examined in this research
session by an independent agent, including support injectivity, terminal
boundary location, degree scaling, and the possible confusion between
condenser capacity and extremal length of a single separating loop class.
This is AI-assisted adversarial review, not specialist human review.

Prepared with OpenAI GPT-6 Astra Pro assistance in proof search, source
comparison, and writing. The standard cover/modulus and descriptive-set
theorems retain their original attribution. The mathematical arguments
above are written; no Python run or Lean theorem is represented as a
formal verification of them. Independent specialist review remains
outstanding.

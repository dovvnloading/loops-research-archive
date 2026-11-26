# Canonical rational-cut carrier and actual primitive little-Julia compatibility

Date: 2026-11-26. Base: 6ba50a4b452f7703c17200dd3b3bab4b117ee413.

## 1. Target, status and claim

Primary ledger ID: **TERMINAL_NONLC_HUBBARD_CARRIER_PROPER** (open).
Secondary IDs: KKL_STATIONARY_NONLC_SELECTED_GEOMETRIC_CONTINUUM_LIFT and
KKL_STATIONARY_SELECTED_PREDECESSOR_MARKED_COMPONENT_INCIDENCE (open).
The target is a physical continuum, not a finite graph or an ideal-side marking.

**Result (b), proved for an explicitly specified class of actual cycles.**
For every connected, periodically repelling ordinary degree-two polynomial or
quadratic-like map with an actual primitive degree-two renormalization of period
\(P>1\), the canonical rational-lamination projection identifies each physical
little Julia set with its own internal combinatorial model (as a quotient,
not as a point), the projected little Julia sets are pairwise disjoint,
and the full lift of their dendrite hull is a compact forward-invariant
physical continuum. It omits the full fiber of the nondividing fixed point
\(\beta\), hence is proper. An intrinsic formula in terms of actual
finite-orbit cuts determines this lift independently of the straightening.
The statement does not assume local connectivity. No a priori bounds are
imported. The precise source-marked identification needed for a separately
chosen KKL pseudo-quadratic-like marked object is not asserted.

The scope includes the canonical set construction on the ordinary same-filled
terminal representative, provided its given primitive return is represented
by an actual degree-two restriction on that germ. The proof uses neither a
uniform modulus nor any infinite tower compactness. Excluded: disconnected
filled sets; attracting, parabolic and irrationally indifferent cycles;
satellite cycles with touching little Julia sets; degree greater than two;
formal cycles without a physical return. The stationary addendum has the
additional finite limb and count hypotheses stated there.

The November 23
[cutpoint-pruning theorem](../maximal_global_closure_20261123/CUTPOINT_PRUNING.md)
already supplies the abstract one-cut hull theorem, the actual Kiwi
full-hull construction and its forward invariance, and a stationary count
conditional on identifying the native carrier. We **use**, not re-claim,
those results. Its §7 explicitly leaves the rational-lamination versus
full-fiber identification and the source lift convention open. The new
ingredients here are (i) removal of the rational-extension ambiguity in
the periodically repelling case, (ii) the ambient/internal fiber identity
on an actual primitive return, (iii) disjointness of the geometric cycle
images, (iv) an intrinsic all-finite-cut formula, and (v) application to
the nondividing fixed point and the whole selected predecessor sheet.

## 2. Hypotheses and source interfaces

Write \(F\) for the ordinary quadratic-like germ, \(K=K(F)\) for its
connected filled Julia continuum, \(J=\partial K\), and
\[
 S=\bigcup_{i=0}^{P-1}K_i,\quad K_i=F^i(K_0),\quad
 F(K_i)=K_{i+1\bmod P}.
\]
Here \(K_0\) is the connected filled set of an actual proper degree-two
restriction \(F^P:V'\to V\), \(V'\Subset V\); the critical point of \(F\)
is in \(K_0\), all intermediate maps on the return domain exist, and
the \(K_i\) are pairwise disjoint. All cycles of \(F\) in \(K\) are
repelling. The fixed point \(\beta\) is the nondividing one, with
\(K\setminus\{\beta\}\) connected (KKL §2.4, p. 12).

For a quadratic polynomial this is its actual dynamical plane. For an ordinary
quadratic-like map use Douady–Hubbard straightening (Theorem 1, *On the dynamics
of polynomial-like mappings*, Ann. Sci. ENS 18 (1985), 287–343, §I.1,
pp. 296–298; [article](https://www.numdam.org/item/ASENS_1985_4_18_2_287_0/)).
Straightening gives a homeomorphism conjugating the actual filled-set
dynamics, preserves the periodic dynamical type, and transports all of
the finite-orbit cut relations used below. We do not straighten individual
pieces independently and then assume their embeddings agree. In the
periodically repelling category the filled set equals the Julia set and
has empty interior (Fatou classification and Sullivan no wandering domains;
also explicitly Dudko–Lyubich §2.2.1, p. 9, cited below). Fullness of a
connected polynomial-like filled set is standard. The same statements hold
for the inner return: a nonrepelling periodic orbit of that return would
be nonrepelling for an iterate of \(F\). No a priori bounds are needed for
any straightening here, just an existing compactly contained proper
degree-two restriction.

The source map and marks must be distinguished. KKL,
[*MLC for parabolically bounded primitive renormalization*,
arXiv:2606.27272v1](https://arxiv.org/pdf/2606.27272v1), §2.4 pp. 12–13
and §2.5 p. 13, define the LC hull by connected minimality and specify
a rational-lamination quotient and its natural projection in the non-LC
case. They subsequently use ideal sides in §2.6. The same-filled
ordinary representative is the restriction interface in the archive's
[terminal Hubbard anchor](../../mlc_unified/terminal_hubbard_anchor.md).
The paper's paragraph in §2.5 does not give a separate formula for lifting
an independently specified ideal-side marking. Dudko–Lyubich,
[*MLC at Feigenbaum points*, arXiv:2309.02107v3](https://arxiv.org/pdf/2309.02107v3),
§2.2.1 p. 9 explicitly defines the natural projection by the finite
preperiodic separation classes. §2.2.2 pp. 9–10 and equation (2.2) use
the full inverse image of the unique model arc as the geodesic continuum.
We take this explicit unmarked convention, with the KKL complete
little-set cycle rather than the postcritical set as the marks.

## 3. The canonical projection really is the rational-lamination projection

Primary input: J. Kiwi, *Real laminations and the topological dynamics
of complex polynomials*, Advances in Math. **184** (2004), 207–267,
[DOI](https://doi.org/10.1016/S0001-8708(03)00144-0),
[readable full text](https://www.academia.edu/91433960/Real_laminations_and_the_topological_dynamics_of_complex_polynomials).
In the no-irrationally-neutral-cycle case use Definition 2.5 p. 214,
Theorem 2 pp. 209–210, Proposition 3.15 pp. 232–233, Proposition 4.2
pp. 233–234, Lemma 4.4 pp. 234–235, Proposition 4.7 and Corollary 4.8
pp. 235–236, and Theorems 5.12–5.13 pp. 243–245.

Let \(E_F\) be the set of points of \(K=J\) with finite forward orbit.
For \(x,y\in K\), use the following exact relation, transported from
the straightened polynomial:
\[
 x\sim_F y\quad\Longleftrightarrow\quad
 \text{for every finite }Z\subset E_F\setminus\{x,y\},
 \ x,y\text{ belong to the same component of }K\setminus Z.
\tag{1}
\]
Kiwi's results assert that these fibers partition \(K\) into compact
connected classes and give a continuous monotone quotient \(h:K\to D\),
semiconjugating \(F\) to \(Q:D\to D\). Each point of \(E_F\) has a
singleton full fiber. On the straightened plane the quotient is a plane
and is the identity on singleton classes outside \(K\); the induced
map is a topological polynomial of degree two.

Here is why the plane model is a dendrite and why there is no hidden
rational-extension ambiguity. Off \(K\) the plane quotient restricts to
a homeomorphism onto the complement of its image (open saturated set
and one-to-one quotient). The complement is therefore connected. The
image has empty interior: an open subset in the image would have
nonempty open preimage in \(K\). The image is locally connected by
Kiwi's model theorem. A Jordan curve in it would enclose a bounded
complementary component unless it contained the enclosed open disk.
Both possibilities are excluded. Thus \(D\) is a dendrite. This
repeats the already established argument in the November 23 note §3
to fix the exact setting.

Let \(\lambda\) be the real circle lamination of the straightened
polynomial, and \(\lambda_{\mathbb Q}\) its rational restriction.
Proposition 4.7 and Corollary 4.8 identify the quotient landing map
with the model circle parametrization; Theorems 5.12–5.13 identify the
pinched-disk realization with the topological model. In particular the
model contains **no bounded topological Fatou component**: its
complement is exactly the connected outside component, and the filled
model has empty interior. The warning in Kiwi pp. 257–258 about the
rational restriction is relevant but its exception is absent here.
Specifically Kiwi there recalls Lemma 4.17 of his *Rational laminations
of complex polynomials*, Contemp. Math. 269 (2001), 111–154: for the
topological realization, the smallest closed equivalence relation
extending the rational restriction is the real lamination unless an
infinite-orbit critical point lies on the boundary of a bounded Fatou
component. We invoke the criterion **as stated by Kiwi in the 2004
paper**, not an independently verified page of the 2001 article.
It applies to the topological realization of \(\lambda\) just
identified, not to an arbitrarily chosen polynomial with neutral cycles.
There are no bounded Fatou components of that realization, so
\[
 \lambda=\operatorname{EqCl}(\lambda_{\mathbb Q}).
\tag{2}
\]
Here EqCl means the least **closed equivalence relation**, not merely
the closure of a subset of the product circle. The pinched-disk
quotient is obtained by collapsing convex hulls of these classes;
there is no remaining filled gap representing a bounded Fatou
component. Thus it yields the same dendrite as Kiwi's model.

There is also uniqueness of the projection with the rational labels:
every rational ray of the polynomial lands at a finite-orbit point in
this category, and the natural projection sends its landing point to
the rational class of its angle (Proposition 4.7). These landing points
are dense in \(J=K\) (repelling periodic points are dense and are
landed by periodic rays). Any continuous map to the identified model
with these rational labels must agree with \(h\) on a dense set,
hence everywhere. Equivalently Dudko–Lyubich's finite-cut definition
of the projection is exactly (1). In an ordinary quadratic-like germ
the cut relation (1) is intrinsic to \(K\) and the actual finite-orbit
set, so this identification does not depend on which hybrid
straightening was used. This argument removes the generic rational
non-density concern for the **unmarked** rational-lamination model.

Two further consequences will be used.

**Lemma 3.1 (singleton model finite-orbit fibers).** If \(u\in D\) is
periodic, its fiber is a singleton periodic physical point by Kiwi's
Lemma 4.4. If \(Q^m(u)\) is periodic, semiconjugacy puts
\(h^{-1}(u)\) in \(F^{-m}\) of that singleton, a finite set in \(K\)
because \(F\) has degree two. A connected fiber contained in a
finite set is a singleton. Thus the model has no extra finite-orbit
points with nontrivial fibers.

**Lemma 3.2 (arc-density of the actual finite-orbit cuts).**
If \(u\ne v\) in \(D\), the open arc \((u,v)_D\) contains a point
\(h(a)\), \(a\in E_F\). Choose physical lifts \(x,y\). Their fibers are
distinct, so by (1) there is a finite \(Z\subset E_F\) avoiding \(x,y\)
which separates them in \(K\). Every \(z\in Z\) has a singleton fiber,
so \(h(Z)\) avoids \(u,v\). If \([u,v]_D\) avoided \(h(Z)\), its
monotone full inverse image would be a connected subset of
\(K\setminus Z\) containing \(x,y\), impossible. This proves the
assertion even on arcs of empty relative interior in the dendrite.
Ordinary density alone would not suffice.

## 4. New compatibility theorem: the ambient quotient restricts to the actual inner quotient

**Theorem 4.1.** Let \(C=K_0\) and \(G=F^P|_C\) be the actual
primitive return. For all \(x,y\in C\),
\[
 x\sim_F y \quad\Longleftrightarrow\quad x\sim_G y,
\tag{3}
\]
where the right side is the finite-cut relation in the actual filled
set \(C\), with the finite-orbit points for its own degree-two return.
Consequently \(h(C)\subset D\) is naturally homeomorphic to the
internal rational-lamination dendrite of \(G\), with the homeomorphism
conjugating the induced return maps.

**Proof.** First prove a physical planar fact. Every compact subset
\(A\subset K\) has connected complement: any bounded component of
\(\mathbb C\setminus A\) is open, cannot meet the connected unbounded
set \(\mathbb C\setminus K\), and would therefore be contained in \(K\),
contrary to empty interior. There is only one unbounded component.
It follows that \(K\) is hereditarily unicoherent: if two subcontinua
have nonempty disconnected intersection, the second Janiszewski
separation theorem implies their union separates the sphere. That
union is a compact subset of \(K\), which we just proved impossible.
For the separation theorem see K. Kuratowski, *Topology*, vol. II
(Academic Press, 1968), §61.I, Theorem 2, p. 506 (the sphere is a
Janiszewski space), and property (J) p. 505.

The set of finite-orbit points for \(G\) on \(C\) is exactly \(E_F\cap C\):
one direction follows by taking the subsequence of multiples of \(P\),
and for the other direction the full orbit is a union of \(P\) images
of that finite subsequence.

Suppose \(x\sim_F y\). The continuum \(h^{-1}(h(x))\) intersects \(C\)
in a connected compact set by hereditary unicoherence. For any finite
internal cut set \(Z\) avoiding \(x,y\) this intersection avoids \(Z\):
a point of \(Z\) has singleton ambient fiber, and cannot belong to the
fiber of \(x\) unless it equals \(x\). Thus the connected intersection
contains \(x,y\) in one component of \(C\setminus Z\); (1) for the
return proves \(x\sim_G y\).

Conversely, if \(x\not\sim_F y\), choose a finite ambient separating
set \(Z\) as in (1). Its intersection with \(C\) is a finite set of
internal finite-orbit points, avoiding the endpoints. A connected
subset of \(C\setminus(Z\cap C)\) containing \(x,y\) would also be a
connected subset of \(K\setminus Z\), contradiction. Thus
\(x\not\sim_G y\). This proves (3).

Let \(h_G:C\to D_G\) be the internal quotient, from §3 applied to the
ordinary quadratic-like return. The equality of equivalence
relations gives a unique continuous bijection
\(e:D_G\to h(C)\) with \(e h_G=h|_C\). Compactness and Hausdorffness
make \(e\) a homeomorphism. The diagram with \(G\) and \(Q^P\)
commutes by semiconjugacy and surjectivity of \(h_G\). This is an
embedding of the **geometric** internal dendrite in the ambient
dendrite; it is not an equality of prime-end circles or a claim
that \(h^{-1}(h(C))=C\). QED.

The same result holds for every actual phase \(K_i\). To justify
the transport, put \(V_j=F^j(V')\), \(0\le j\le P\), with \(V_P=V\).
Each map \(F:V_j\to V_{j+1}\) is proper and onto: for a sequence
in \(V_j\) whose images remain in a compact subset of \(V_{j+1}\),
choose preimages in \(V'\); their \(F^P\) images lie in the compact
image of that subset under the remaining composition, so properness
of the return supplies a convergent subsequence inside \(V'\).
Applying \(F^j\) gives the required compactness in \(V_j\).
The degrees multiply to two. The first factor contains the critical
point and has degree at least two, so all subsequent factors have
degree one and are biholomorphisms. Therefore \(F^{P-i}\) on \(K_i\)
for \(i>0\) is a homeomorphism to \(K_0\) conjugating the two
\(P\)-step dynamics. Transport the finite-orbit cut relation by this
homeomorphism. The ambient/internal comparison proof itself uses
only the equality of the finite-orbit sets and hereditary
unicoherence, and applies on \(K_i\) without further analytic
hypotheses. This is why independently chosen straightenings do not
create an extra arbitrary continuum label.

**Theorem 4.2 (disjointness in the geometric model).** Put
\(C_i=h(K_i)\). These are pairwise disjoint nondegenerate subdendrites
and \(Q(C_i)=C_{i+1\bmod P}\).

Proof: compact connectedness and cyclic covariance are immediate.
Each return has an infinite Julia set and dense repelling periodic
points, hence at least two distinct finite-orbit points whose ambient
fibers are singleton; their images are distinct. In a dendrite any
connected subset contains the unique arc between any two of its
points. If \(C_i\cap C_j\) contained two different points, it would
contain their connecting arc and by Lemma 3.2 a model point
\(h(a)\) on that arc with singleton physical fiber. Since it lies
in both images, \(a\in K_i\cap K_j\), impossible. If
\(C_i\cap C_j=\{u\}\), then \(Q^P(u)\in C_i\cap C_j\) and \(u\)
is periodic. Lemma 3.1 again gives a singleton fiber meeting both
physical sets, impossible. This rules out both possible nonempty
intersections, not just overlap with interior. QED.

## 5. The physical lift, an intrinsic cut formula, and properness

Let
\[
 H=\operatorname{Hull}_D\left(\bigcup_i C_i\right),\qquad
 T=h^{-1}(H).
\tag{4}
\]
Here Hull means the smallest connected subset of a dendrite. This
hull is the union of all unique arcs with endpoints in the given
finite union of subcontinua; it is compact (equivalently, add the
finitely many connecting arcs between chosen points of the pieces).
The monotone full preimage is compact connected and contains \(S\).
This is exactly the union of the full geodesic continua (Dudko–Lyubich
equation (2.2)) between endpoints in \(S\).

Forward invariance is the result already proved in November 23
CUTPOINT_PRUNING.md §5: the induced degree-two topological
polynomial has its unique critical point at \(h(\operatorname{crit}F)\)
in \(C_0\), and the image of an arc, split at that critical point
if necessary, lies in the hull of its endpoints and the image
of the critical point. All these images are in the cyclic marked
union when the original endpoints are in that union. To see the
arc assertion, a locally injective path on a dendrite cannot
backtrack without a locally noninjective point (a minimal closed
subpath would be a simple closed curve). Off the critical point
the plane map is locally a homeomorphism. Thus \(Q(H)\subset H\)
and \(F(T)\subset T\). No new forward-invariance proof is claimed.

The following identifies the **physical set** without making a
choice of model or of marked prime-end lifts:
\[
 T=K\setminus\!\!\bigcup_{\substack{a\in E_F,\ 
       \Omega\in\pi_0(K\setminus\{a\})\\
       \Omega\cap S=\varnothing}}\Omega.
\tag{5}
\]
For clarity \(\pi_0\) here denotes connected components, not
the combinatorial projection.

**Proof of (5).** Fix \(a\in E_F\). The singleton fiber at \(a\)
makes the components of \(K\setminus\{a\}\) exactly the inverse
images of components of \(D\setminus\{h(a)\}\). Indeed such
inverse images are connected: each is a union of inverse images
of compact arcs with a common endpoint in the component, and
monotone compact maps have connected full inverse images of
continua. Conversely a connected subset avoiding \(a\) has
connected image avoiding \(h(a)\). If \(\Omega\) misses \(S\),
its image component misses all \(C_i\). The complement of that
component is connected and contains the marked union, hence
contains \(H\). Thus \(T\) avoids \(\Omega\).

Conversely let \(x\notin T\) and \(u=h(x)\). Choose \(y\in H\)
and the first point \(v\) of the arc from \(u\) to \(y\) belonging
to the closed set \(H\). Then \(u\ne v\) and the open arc
\((u,v)\) misses \(H\). Lemma 3.2 supplies \(h(a)\in(u,v)\)
with \(a\in E_F\). The component of \(D\setminus\{h(a)\}\)
containing \(u\) misses \(H\): if it contained \(z\in H\),
the unique arc from \(u\) to \(z\) would avoid \(h(a)\), so
the arc from \(z\) to \(y\) would contain \(h(a)\) (the unique
arc property). But \([z,y]\subset H\). Taking the full component
inverse image yields an \(\Omega\) appearing in the union in
(5) and containing \(x\). This proves the reverse inclusion.
QED.

In particular (5) is intrinsic to the actual cycle and the
actual dynamics even if the filled set is not locally connected.
It identifies a specific physical continuum rather than an abstract
tree vertex. It need not be the minimal connected subset of \(K\)
in a different, nonsaturated convention. If \(K\) is locally connected, Carathéodory's theorem makes
each external impression a singleton. Kiwi's Theorem 3 (Finiteness
Theorem, p. 210, proof pp. 237–238) represents every fiber in this
nondegenerate connected Julia set as a finite union of impressions.
Since the fibers are connected, each is a singleton. Thus the
finite-cut model is homeomorphic to the actual dendrite and (4)
is the ordinary connected hull.

**Corollary 5.1 (properness).** The actual nondividing fixed point
\(\beta\) belongs to no \(K_i\): fixedness and the cycle permutation
would put it in all the disjoint pieces. Its fiber is singleton.
As \(K\setminus\{\beta\}\) is connected, its image equals
\(D\setminus\{h(\beta)\}\) and is connected; it contains all the
\(C_i\). By connected minimality \(H\) is contained in that
punctured dendrite. Consequently
\[
 h^{-1}(h(\beta))=\{\beta\},\qquad
 T\cap h^{-1}(h(\beta))=\varnothing,\qquad T\subsetneq K.
\tag{6}
\]
Every possible set lift projecting **into this same hull** also
omits that fiber, even without equality to the full lift. Compactness,
connectedness and the exact identity (5) have been proved for the
full lift. The geometric complement \(K\setminus T\) is therefore
nonempty in this canonical category; no LC or density of open
external accesses was assumed.

## 6. Stationary selected predecessors (set level only)

Use the existing
[selected-predecessor endpoint proof](../../mlc_unified/kkl_stationary_n2_selected_predecessor_endpoint.md),
Theorem 4.3, steps 1–2: the actual terminal inverse sheet
\(\Omega_n=\phi_0^n(\mathfrak L_0)\) is a component of
\(K\setminus\{\alpha^n\}\), with \(F^n:\Omega_n\to\mathfrak L_0\)
a homeomorphism. Its single root \(\alpha^n\) is preperiodic to
the dividing fixed point and lies outside the primitive cycle.
This is a hypothesis of this application, not an assertion that all
primitive combinatorics have this stationary inverse branch.

By the component correspondence in §5 and dendrite convexity,
\(T\cap\Omega_n=h^{-1}(H\cap h(\Omega_n))\) is connected if nonempty.
Formula (5) gives the exact criterion
\[
 T\cap\Omega_n\ne\varnothing\quad\Longleftrightarrow\quad
 \exists i\ (K_i\subset\Omega_n).
\tag{7}
\]
For the reverse implication use \(S\subset T\); for the forward
one a connected \(K_i\) avoiding the root belongs to one component.

Suppose at most \(b\) distinct physical cycle members meet the
critical limb \(\mathfrak L_0\), and \(P>b\) (in the high-type
source case \(P\ge q>b\)). If \(n\ge b\) and
\(K_i\subset\Omega_n\), its first \(b+1\) images, including
\(K_i\) itself, are contained in the critical limb by
\(F^j(\Omega_n)=\Omega_{n-j}\subset\mathfrak L_0\). These are
\(b+1\) distinct cycle members, contradiction. Therefore
\[
 T\cap\Omega_n=\varnothing\quad(n\ge b)
\tag{8}
\]
whenever the indicated sheet exists. This is exclusion of the
**whole open physical sheet**, not merely the connected selected
predecessor inside it; its root is not asserted to be excluded.

For the canonical set-level model define
\(\overline\Omega_n=h(\Omega_n)\), the corresponding component,
\[
 L_n=F^{-n}(T)\cap\Omega_n,\qquad
 \overline L_n=Q^{-n}(H)\cap\overline\Omega_n.
\]
The restriction \(Q^n:\overline\Omega_n\to\overline\Omega_0\)
is a homeomorphism. Here is the inverse-fiber check, which is
needed to match the selected model branch rather than just its
image. A fiber over \(\overline\Omega_0\) is contained in
\(\Omega_0\) by singleton-root component correspondence. If it
is nontrivial, it contains no physical finite-orbit point.
Its inverse under the homeomorphism \(F^n|_{\Omega_n}\) is
a connected compact set, also without finite-orbit points.
By (1) such a continuum is contained in a single ambient fiber.
For a singleton fiber the inverse is a single point.
Thus the physical inverse branch descends to an inverse on the
quotient. It is continuous since the restriction of \(h\) to
the open saturated component \(\Omega_0\) is a quotient map
onto \(\overline\Omega_0\) (components of a punctured dendrite
are open). This proves the asserted homeomorphism. Therefore
\(\overline L_n\) is the connected selected inverse of
\(H\cap\overline\Omega_0\), not an arbitrary relabeling of a
model component.

Because \(T\cap\mathfrak L_0\) is connected, \(L_n\) is its
connected inverse via the homeomorphism \(F^n\), i.e. the actual
selected component in this construction. Semiconjugacy and the
singleton-root component correspondence give the exact equality
\[
 h^{-1}(\overline L_n)=L_n,\qquad h(L_n)=\overline L_n.
\tag{9}
\]
The geometric small Julia model continua are exactly the \(C_i\)
of Theorem 4.1; \(h(K_i)=C_i\), not an abstract finite-tree vertex.
Thus in this model the two clauses of the selected set lift are
separate and both have a proof. Formula (8) immediately implies
the disjointness used in the stationary count. None of (7)–(9)
identifies occurrences, incident ideal sides, proper paths,
subordination, endpoint disks, immersion injectivity, measurable
exits or width transfer. In particular one cannot infer a
two-path-breaking inequality from set disjointness alone.

## 7. Exact arithmetic regression on an actual polynomial

The nonattracting real 3/9 Misiurewicz tip already certified in the
archive provides a physical test of the fixed-point and cut exclusion.
Let \(x_0(c)=0,\ x_{j+1}(c)=x_j(c)^2+c\). Define \(c_*\) to be
the root of \(x_{18}(c)+x_9(c)=0\) in
\[
 [k/2^{128},(k+1)/2^{128}],\qquad
 k=-607918036626757496169199575185708826140.
\]
The accompanying independent integer-interval checker proves
opposite endpoint signs, derivative in \((-71,-70)\), pairwise
distinct \(x_0,\ldots,x_{18}\) and the period-nine multiplier
in \((3,4)\). The root identity gives
\(x_{19}=x_{10}\), so the critical point has exact preperiod 10
and period 9. This is an actual strictly preperiodic quadratic,
not a symbolic model. Standard Misiurewicz/subhyperbolicity theory
gives a locally connected Julia dendrite, all cycles repelling.
The actual connected primitive 3/9 proper degree-two domains are
proved in
[nonattracting_tip_complex_two_scale_20261106.md](../nonattracting_tip_complex_two_scale_20261106.md)
(the stated complex-domain theorem and its cited Rouché/Riemann–Hurwitz inputs); in
particular the period-three critical return has \(V_3\subset
U_3=B(0,1/4)\). See also
[period27_misiurewicz_tip_ray_access_20261106.md](../period27_misiurewicz_tip_ray_access_20261106.md).
We do not replace these physical domain theorems by a numerical
disk test.

Write
\[
 \alpha=(1-\sqrt{1-4c_*})/2,\quad
 \beta=(1+\sqrt{1-4c_*})/2,\quad
 a_1=-\alpha,\quad a_2=\sqrt{a_1-c_*}.
\]
Then \(F(a_1)=\alpha,\ F(a_2)=a_1\). The checker gives
\(\alpha<0<a_1<a_2<\beta\) and strictly disjoint complex phase
disk enclosures, using
\(r_0=1/4,\ r_{j+1}=2|x_j|r_j+r_j^2\).
All of \(K_i\) for the period-three cycle lies in the respective
\(F^i(U_3)\) enclosures, whose real-part bands lie strictly left of
\(a_2\) and \(\beta\); phase 1 is left of \(\alpha\) and phases 0
and 2 right of \(\alpha\). Each \(K_i\) contains its real orbit
point \(x_i\). The real invariant interval \([-\beta,\beta]\)
lies in \(K\) since \(c_*\in(-2,-1)\), \(c_*=\beta-\beta^2>-\beta\),
and \(F([-\beta,\beta])=[c_*,\beta]\).
Thus the component containing \(\beta\) of \(K\setminus\{a_2\}\)
cannot contain any \(x_i\): the unique real arc between \(x_i\)
and \(\beta\) passes through \(a_2\). Connectedness of each \(K_i\)
and the strict band inequalities imply this component misses the
entire actual primitive cycle. Formula (5) excludes it from \(T\).
As a negative control, \(a_1<x_2\); the weaker cut at \(a_1\)
does not put the entire cycle on the opposite side from \(\beta\).
The checker tests these strict inequalities, not the continuum
theorem or the imported physical-return domains.

Run from the repository root:
~~~sh
python -B research/independent_audits/nonlc-terminal-carrier_20261126/verify.py
~~~
Python 3.12, standard library only, deterministic, no sampling or
floating-point decisions. Signed interval endpoints are rounded
outwards to multiples of \(2^{-256}\); products enclose all four
corners and square roots use integer square root with upper
rounding. Assertions fail on an uncertified sign, multiplier,
separation or ordering. PASS means exact finite arithmetic only.
This is an LC calibration, **not** a constructed example of a
non-LC periodically repelling quadratic. The theorem above does not
require existence of a non-LC example. No inference from a finite
orbit to general non-LC fiber structure is made.

## 8. Dependency and status disposition; first unproved identification

Consumed archive dependencies (no edits or status promotions here):
KKL_NATIVE_TERMINAL_HUBBARD_TREE (imported, KKL §2.4–2.5, pp.12–13);
TERMINAL_LC_NATIVE_HUBBARD_CARRIER_PROPER (proved,
[terminal dense obstacle, Proposition 2.1](../../mlc_unified/terminal_dense_obstacle_and_submulticurve_replacement.md));
the same-filled terminal restriction interface in
[terminal_hubbard_anchor.md](../../mlc_unified/terminal_hubbard_anchor.md);
the [Kiwi-model identification audit](../../mlc_unified/kkl_stationary_n2_kiwi_model_identification_audit_20260727.md),
the selected endpoint Theorem 4.3 and Proposition 4.5,
and the November 23 CUTPOINT_PRUNING.md §§3–6 as cited above.
For the stationary conditional application only, consume
KKL_STATIONARY_SELECTED_PREDECESSOR_CHAIN and the actual
inverse-sheet hypotheses in that endpoint note. No source claim is
imported that already says that the ambient quotient restricts to
the little-set internal quotient: (3) is the proof of that bridge.
The July source-locked status counts are not modified.

Proposed integration: add a **proved scoped statement** for the
canonical ordinary same-filled geometric construction (3)–(6).
If the reviewed integration explicitly takes the full geodesic
lift convention as the unmarked meaning of KKL §2.5, (6) is a
proof of TERMINAL_NONLC_HUBBARD_CARRIER_PROPER in that meaning.
We conservatively report (b) rather than silently assert that
KKL's independently selected pseudo-ql marked carriers, edges,
and sheets are this precise realization. No canonical ledger entry
is requested to switch status unconditionally in this PR. For
KKL_STATIONARY_NONLC_SELECTED_GEOMETRIC_CONTINUUM_LIFT record
(3), (4), (9) as proved in the explicit canonical realization;
for KKL_STATIONARY_SELECTED_PREDECESSOR_MARKED_COMPONENT_INCIDENCE
record (7)–(8) in the stated stationary class. The precise first
remaining source step, if a different named model/lift or marked
carrier is used, is equality of that independently selected
geometric cycle/side realization with the canonical construction
in (3)–(4), followed separately by the marked path/occurrence
identifications. We have not proved the latter from the unmarked
fiber equality. In particular a homeomorphism of internal
dendrites need not identify their prime-end circles, accesses
or localization-sheet cosets. Full saturation of each individual
ambient \(C_i\) back to \(K_i\) is also not claimed; (3) establishes
precisely the restricted equivalence needed for the geometric
embedding. The projected \(C_i\) are pairwise disjoint by §4 even
without that stronger saturation assertion.

These results narrow a terminal carrier obstruction relevant to
marked construction and stationary transfer, but do not prove
H1_MARKED_CONSTRUCTION, MBTT, H3_COERCIVITY, H4_RIGIDITY, VAAPC-I,
UPTCR, or MLC. No quantitative width estimate, full Marked-Wave
bridge, all-scale realization, or new parameter-locus local
connectivity claim follows. CI checks only the executable regression,
not the written topological argument.

## 9. Attribution and AI disclosure

The quotient and lamination theory belongs to Jan Kiwi, the
straightening theorem to Adrien Douady and John Hubbard, the
separation theorem to Zygmunt Janiszewski, and the respective
renormalization and geodesic-continuum conventions to Kahn,
Kapiamba, Lyubich and Dudko. Credit the archive's November 23
cutpoint-pruning authors for the already proved monotone
full-hull and count argument, and its November 6 authors for the
actual tip and proper-return certificates. The new contribution
is the written combination and proofs explicitly distinguished
in §1. OpenAI GPT-6.2 performed proof search, source comparison,
exact-arithmetic implementation, adversarial checks and drafting.
No independent human specialist verification has been performed
for this submission; it is offered for review, not as a
refereed result or a claim of an MLC proof.

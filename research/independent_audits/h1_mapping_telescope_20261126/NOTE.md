# Saturated cyclic pullbacks and peripheral-cover telescopes

**Target:** MAPPING_TELESCOPE (H1_MARKED_CONSTRUCTION), especially
critical_chronology_and_retimed_telescope.md, Definition 10.1, Theorem 10.2,
§15.3, and finite_horizon_inflation.md §§4–6.

**Current status:** OPEN. **Proposed result:** PROVED written physical subcase
(subject to the stated imported theorem); PARTIAL for the ledger obligation.
No change to any canonical ledger status is requested.

**Claim:** For a finite cycle of actual saturated full inverse continua of
a quadratic polynomial, with one quadratic step, the basin condition of
BOPT Theorem B, separated forward-closed markings and peripheral relative
covers, one can construct cyclic relatively compact Jordan cores, their
based embedded relative-cover lifts, a proper degree-two selected return
and its actual critical-value and component/phase route. This is not an
assertion that every source-facing virtual block supplies those inputs.

## 1. Physical inputs and precise scope

All statements refer to the same polynomial \(f(z)=z^2+c\). Put
\(P_j=f^{s_j}\), \(s_j\ge1\), for \(0\le j<m\); stage indices are cyclic.
The following is a class defined by actual continua and their images,
not by the existence of a planar telescope:

* (S1) Nondegenerate full plane continua \(H_j\), \(H_m=H_0\), with
  \(P_j(H_j)=H_{j+1}\) and \(H_j\) the connected component of
  \(P_j^{-1}(H_{j+1})\) containing the chosen physical anchor.
  Multiplicities of preimages in that component are \(d_j\in\{1,2\}\),
  constant on \(H_{j+1}\), with \(\prod d_j=2\).
* (S2) For \(P=P_{m-1}\circ\cdots\circ P_0=f^S\),
  \(S=\sum s_j\), each attracting or parabolic periodic point of \(P\) in
  \(H_0\) has its immediate attracting basin or all its incident
  parabolic domains in \(H_0\), respectively. In particular this is
  vacuous if \(f\) has no finite attracting or parabolic cycles. The
  intended Julia-only version uses \(H_j\subset J(f)\).
* (S3) The specified closed marking is
  \(\Upsilon_j=H_j\cup E_j\) in the sphere, where \(E_j\) is compact,
  disjoint from \(H_j\), contains infinity, and
  \(P_j(\Upsilon_j)\subset\Upsilon_{j+1}\).
  Every critical value of \(P_j\), including infinity, is in
  \(\Upsilon_{j+1}\). A prescribed open authorized plane neighborhood
  \(N_j\) of \(H_j\) is given (the collar must lie there). One may also
  prescribe finitely many disjoint compact obstacles in \(E_j\).
* (S4) The selected relative covers are the peripheral cyclic covers of
  the component of the marked complement incident to \(H_j\), and of the
  corresponding preimage complement. The marked component is the one
  specified by the anchor in (S1). The selected sheet/phase is the
  distinguished physical peripheral collar, or a based isomorphic copy
  thereof. We do not substitute these covers for arbitrary preassigned
  nonperipheral covers or externally fixed incompatible coset routes.

These conditions permit arbitrary finite stage lengths, and do not
require a uniform modulus lower bound, local connectivity of the
continua, disjointness of different stages, or a Jordan boundary for
\(H_j\). They exclude unsaturated/only forward-coherent virtual
connectors, nonclosed itineraries, omitted obstacles accumulating on a
selected hull, unabsorbed attracting/parabolic domains, and prescribed
nonperipheral or incompatible sheets. Actual virtual hulls satisfying
(S1)–(S4) are covered; their existence with the source's full marking
for a nonordinary virtual block is not established here.

A useful check on (S1): if a proposed stage has a connected full target
carrier \(H_j\) and a selected full pullback component \(H'_j\subset H_j\)
mapping onto \(H_{j+1}\), then (S3) already forces \(H'_j=H_j\).
Indeed \(P_j(H_j)\) is connected, is contained in
\(H_{j+1}\cup E_{j+1}\), and meets \(H_{j+1}\) (in fact contains it).
Compact separation forces \(P_j(H_j)\subset H_{j+1}\). Hence \(H_j\)
lies in the component \(H'_j\) of the full preimage. This observation
does not prove (S3) for a proposed virtual hull, nor justify replacing
a merely immersed carrier by a planar inclusion.

## 2. Cyclic closure is a consequence of saturation, not of a finite fan

### Lemma 2.1 (return recognition)

Under (S1), \(H_0\) is a component of \(P^{-1}(H_0)\),
\(P(H_0)=H_0\), and the multiplicity of the selected return over every
point of \(H_0\) is two.

Proof. If \(C\) is the component of \(P^{-1}(H_0)\) containing \(H_0\),
then each intermediate image of \(C\) under the successive prefixes
\(P_{j-1}\circ\cdots\circ P_0\) is connected and contains \(H_j\).
Starting at the last image in \(H_0\), work backward: each preceding
image lies in the selected component of \(P_j^{-1}(H_{j+1})\),
which is \(H_j\). Thus \(C\subset H_0\). The reverse inclusion and
surjectivity follow from the given equalities. For a point of the
target, sum the multiplicities along the selected inverse fibers;
each step multiplies by \(d_j\), giving exactly two, including at
critical values. QED.

Apply Blokh–Oversteegen–Ptacek–Timorin (BOPT), *Quadratic-like dynamics
of cubic polynomials*, [arXiv:1305.5799v3](https://arxiv.org/pdf/1305.5799),
Theorem B, printed pp. 17–18 (Lemma 4.1, p. 15). Despite the title this
theorem is for an arbitrary polynomial. Its sufficient hypotheses
are fullness, forward invariance, being a component of the inverse
image of the image, and inclusion of the indicated immediate
attracting/parabolic domains. Lemma 2.1 and (S2) verify all of them for
\(P=f^S\). Thus \(H_0\) is the filled Julia set of a polynomial-like
restriction \(P:U\to V\), \(U\Subset V\). Its degree is two: the full
preimage of each point of its filled set within \(U\) lies in that
filled set, so Lemma 2.1 computes its degree, not just a local degree.
In particular, one has obtained the closing analytic collar from the
physical itinerary, not assumed Definition 10.1.

### Lemma 2.2 (cyclic collar refinement)

Under (S1)–(S3) there exist bounded Jordan disks \(B_j,A_j\) with
\(B_m=B_0\), and
\[
 H_j\Subset A_j\Subset B_j\Subset N_j,\qquad
 \overline B_j\cap E_j=\varnothing,\qquad
 A_j=\operatorname{Comp}_{H_j}(P_j^{-1}(B_{j+1})),
 \quad P_j^{-1}(H_{j+1})\cap A_j=H_j.
 \tag{2.1}
\]
Each \(P_j:A_j\to B_{j+1}\) is proper of degree \(d_j\).
Here compact containment of a disk always refers to its closure.

Proof. We give the compact-margin step, which the finite-horizon
inflation theorem §10 by itself does not provide around a cycle.

We use elementary polynomial pullback facts. A component of the
preimage of a Jordan disk maps properly onto the disk (polynomial
properness and open/closed image). When the boundary misses the finite
critical values, its inverse boundary is a finite union of Jordan
curves, by the unbranched covering of a boundary collar. The inverse
image of the closed disk is full: a point over the exterior can be
joined to infinity by lifting a path in the exterior avoiding the
finite critical values (if initially critical, first move a little
in the open exterior preimage). Thus each disk component is Jordan,
and its closure is the corresponding closed pullback component.
For a full continuum, pull back nested decreasing Jordan
neighborhoods and take intersections. At each level there are at most
\(\deg P_j\) components, each surjecting onto its target. The nested
selected components intersect in a connected compact set mapping
onto the limiting continuum (theorem 14.1 below); it is the entire
selected component, since every connected subset of the limiting
preimage containing the anchor is contained in each selected
component. Distinct limiting components are finite in number:
otherwise one could choose more than \(\deg P_j\) distinct components,
which are separated at some finite level of the nested pullbacks.
Equivalently, each component surjects and the fiber over any one
point is finite. These observations give the following shrinking
rule: for any neighborhood of a selected closed preimage component,
all sufficiently small Jordan neighborhoods of its target have the
corresponding closed preimage component inside that neighborhood.
For a general neighborhood choose an intermediate open set with
boundary disjoint from the entire preimage of the compact target;
compactness of its boundary image proves the same rule. This is the
argument of finite_horizon_inflation.md Lemma 10.1, with finitely many
components for a polynomial iterate.

Choose a nested basis of Jordan neighborhoods of \(H_0\) from the
quadratic-like restriction in Lemma 2.1: successive pullbacks of a
Jordan target \(V\) within \(U\) are connected, because the unique
critical value belongs to \(H_0\); the closed disks are nested with
strict compact containment and intersect in \(H_0\), by the definition
of the filled set. The BOPT proof allows a Jordan target; alternatively
first take a sufficiently deep smooth target in the polynomial-like
collar. Boundaries of sufficiently deep chosen targets avoid every
critical value of \(P\) not in \(H_0\) (a finite set). Denote such a
target by \(B_0\) and put \(C_m=B_0\). Let \(C_j\) be the component
of \((P_{m-1}\circ\cdots\circ P_j)^{-1}(B_0)\) containing \(H_j\).
For all sufficiently deep choices these are Jordan disks and
\[
 P_j(C_j)=C_{j+1},\quad C_j=\operatorname{Comp}_{H_j}
 (P_j^{-1}(C_{j+1})),\quad \overline C_0\subset B_0 .
 \tag{2.2}
\]
The component of the suffix preimage of \(H_0\) containing \(H_j\)
is exactly \(H_j\), by the same backward connected-image argument
as Lemma 2.1. Consequently the shrinking rule makes every
\(\overline C_j\) lie inside the given \(N_j\), away from \(E_j\).
The initial strict inclusion in (2.2) is from the quadratic-like
return. It is the only cyclic closing margin needed.

Now set \(L_0=B_0\). In forward index order choose open neighborhoods
\(L_j\) of \(\overline C_j\) for \(1\le j<m\), with closures inside
\(N_j\setminus E_j\), sufficiently small that the closed selected
pullback of \(\overline L_j\) (or of any Jordan disk compactly inside
\(L_j\) containing \(\overline C_j\)) lies in \(L_{j-1}\).
This is the shrinking rule applied to the compact Jordan disk
\(\overline C_j\), whose selected preimage is \(\overline C_{j-1}\)
by (2.2). Take \(B_m=B_0\), then go backward: take \(A_{m-1}=C_{m-1}\)
and choose a Jordan \(B_{m-1}\) strictly between
\(\overline A_{m-1}\) and \(L_{m-1}\). Continue defining \(A_j\) as
the selected pullback of \(B_{j+1}\) and choosing \(B_j\) strictly
between \(\overline A_j\) and \(L_j\). At \(j=0\) no new choice of
\(B_0\) is made: \(\overline A_0\subset L_0=B_0\).
At each choice the available open neighborhood of a compact full
disk contains an outer Jordan collar (use exterior Riemann
equipotentials). At every stage the target boundary avoids the
critical values, by (S3) and the strict containments. The restriction
is proper; its preimage of \(H_{j+1}\) is exactly the chosen
component \(H_j\), since any other component would have to map onto
the target and would contradict the selected-component shrinking
rule (shrink the initial permitted neighborhoods to exclude all
other components before starting). Thus the fiber degree is \(d_j\).
For \(m=1\) use the initial closing collar directly. QED.

## 3. Actual relative-cover construction

The following proves more than subgroup inclusion for this class;
no claim about a full native KKL access marking is made.

Fix the data of Lemma 2.2. Let \(X_j\) be the component of
\(\widehat{\mathbb C}\setminus\Upsilon_j\) containing
\(B_j\setminus H_j\). Let \(X'_j\) be the component of
\(P_j^{-1}(X_{j+1})\) containing \(A_j\setminus H_j\).
These collars are connected annuli. By (S3) and
finite_horizon_inflation.md Lemma 4.1, \(X'_j\subset X_j\).
The map \(P_j:X'_j\to X_{j+1}\) is a finite unbranched cover:
all critical values were deleted, and each component of a finite
polynomial preimage of a domain maps onto it.

Take a positive meridian \(t_j\) in \(B_j\setminus H_j\), and \(t'_j\)
in \(A_j\setminus H_j\). Use collar basepoints and, where necessary,
change basepoint along a path within the physical collar. Their
images in the fundamental groups of \(X_j,X'_j\) have infinite
order: the planar winding about a point of \(H_j\) is one.
Write \(L_j=\langle t_j\rangle\), \(L'_j=\langle t'_j\rangle\).
For \(i_j:X'_j\hookrightarrow X_j\), inclusion of the actual annuli
and the proper annular covering induced by \(P_j\) give, with these
basepoint connectors,
\[
 (i_j)_*(L'_j)=L_j,\qquad
 (P_j)_*(L'_j)=\langle t_{j+1}^{d_j}\rangle\subset L_{j+1}.
 \tag{3.1}
\]
The second equality uses the full preimage identity (2.1): the
restriction \(A_j\setminus H_j\to B_{j+1}\setminus H_{j+1}\) has
degree \(d_j\), no branch point and orientation-preserving
peripheral winding. No abelianization of a nonperipheral loop is
being used.

Let \(p_j:\widetilde X_j\to X_j\) and
\(p'_j:\widetilde X'_j\to X'_j\) be the connected based covers with
the subgroups \(L_j,L'_j\). The selected lifts of the annuli are
one-sheeted: their whole fundamental groups are in the respective
subgroups, so path lifting gives inverse sections on them.
By Lemma 5.1 of finite_horizon_inflation.md, (3.1) gives the based
holomorphic lift \(\widetilde i_j\) and the lift
\(\widetilde P_j:\widetilde X'_j\to\widetilde X_{j+1}\).
The inclusion lift is holomorphic and locally biholomorphic, since both projections and the inclusion are local biholomorphisms.
The latter polynomial lift is itself a degree-\(d_j\) cover: the composite
\(P_jp'_j\) corresponds to the subgroup
\(\langle t_{j+1}^{d_j}\rangle\), of index \(d_j\) in the subgroup
of \(p_{j+1}\). This index is computed in the cyclic subgroup,
not in an assumed abelian fundamental group of the entire base.

Fill in the selected lifted collars with the actual physical
disks \(A_j,B_j\) using the inverse sections. More precisely glue
\(A_j\) to \(\widetilde X'_j\) along the distinguished copy of
\(A_j\setminus H_j\), and \(B_j\) to \(\widetilde X_j\) in the same
way. There is no non-Hausdorff pair at the inner end: all old
cover points project off the deleted \(H_j\), so a point over
\(H_j\) and any old point can be separated using their physical
projections. Along the overlap the sections are open embeddings.
The gluing therefore gives Riemann surfaces with the indicated
physical charts. Van Kampen kills the cyclic subgroup upon filling
its generator by the disk; the surfaces are simply connected.
We need only the physical Jordan charts, not a uniformization of
the whole filled surfaces as hyperbolic disks.

On the distinguished annuli, uniqueness of based lifting gives
\[
 \widetilde i_j\big((p'_j|_{\rm collar})^{-1}(z)\big)
       =(p_j|_{\rm collar})^{-1}(z),\qquad
 \widetilde P_j\big((p'_j|_{\rm collar})^{-1}(z)\big)
       =(p_{j+1}|_{\rm collar})^{-1}(P_j(z)).
 \tag{3.2}
\]
Thus both maps extend holomorphically to the filled charts by the
identity and the actual polynomial, respectively. The identity
extends on \(\overline A_j\) as an embedding: the boundary is
inside \(B_j\), and a slightly larger Jordan neighborhood of
\(\overline A_j\) in \(B_j\) meets neither any other preimage
component of \(H_{j+1}\) nor \(P_j^{-1}(E_{j+1})\). This follows
from compactness, the proper boundary relation
\(P_j(\overline A_j)=\overline B_{j+1}\), and (2.1).
The one-sheeted section extends across this extra collar by
(3.1). This is an ordinary closure embedding, not just a
Carathéodory prime-end extension, addressing adversarial correction
10.4.

The lifted inclusion is core-proper in the literal sense that
the inverse image of the selected filled target \(H_j\) is
exactly the filled source \(H_j\), mapped identically; outside
the filled source all points project to the complement of
\(\Upsilon_j\). Its restriction to the compact closed Jordan
core is proper, and its open restriction is proper onto its
image (not proper as a map into the whole larger open disk;
no relatively compact open embedding has that property).
On the filled surfaces the extended \(\widetilde P_j\) is proper
of degree \(d_j\). Indeed the distinguished source collar already
provides all \(d_j\) preimages over the distinguished target
collar, so there is no other sheet accumulating on the added
core from its neighborhood. Over the complement use properness
of a finite covering; over a compact neighborhood of \(H_{j+1}\)
inside the target chart use properness of
\(P_j:A_j\to B_{j+1}\). These two local compactness tests imply
global properness. The inverse image of the selected filled
target is exactly \(H_j\), by (2.1).

### 3.1. Based component and phase around the cycle

Choose the same target cover and the same collar section at
stages \(m\) and 0, not independent identifications. Pick a point
\(b_0\) of the physical exterior collar sufficiently close to \(H_0\)
so that its successive physical images \(b_j=P_{j-1}\cdots P_0(b_0)\)
are in \(A_j\setminus H_j\) for \(0<j<m\), and \(b_m\) is in
\(A_0\setminus H_0\). Such a point exists: the finite inverse
images of the open chart neighborhoods contain \(H_0\), and their
intersection is an open neighborhood; near a boundary point
choose outside \(H_0\), using the exact inverse-core identities
to rule out an earlier hit of \(H_j\). Choose \(b_0\) also in \(A_0\).
Lift these points using the distinguished sections. For the final
change of basepoint, choose a path from \(b_m\) to \(b_0\) inside
\(A_0\setminus H_0\), which exists because the annulus is connected.
Its lift stays in the same distinguished section. We are not
asserting that there is a periodic point in the exterior collar.

For any path in the selected local itinerary, its successive
lifts agree with the physical paths via (3.2), including all
intermediate components. For general complement paths, in the
based path-class description of these covers a point is a path
from the basepoint modulo its subgroup. The two lifted maps
send the class of a path to the class of its inclusion or its
polynomial image with the indicated basepoint connector.
Equation (3.1) makes this well-defined; concatenating paths
gives the actual successive coset labels, rather than just
their winding numbers. The final connector is in the
distinguished section and returns to the prescribed initial
lift; different choices inside that section differ by its
peripheral subgroup. Thus the selected physical collar has
no phase drift. This proves compatibility for the *specified
peripheral phase*, not that arbitrary external loops return to
their starting sheet. If an externally fixed sheet itinerary
is specified, its equality to these based path classes is an
additional check; the proof cannot replace those labels.

## 4. The critical lift, the compiler and fixed-iterate limits

Use as the planar stage system of Definition 10.1 the actual
physical charts \(X_j^{\rm core}=A_j,\ Y_j^{\rm core}=B_j\),
\(g_j=P_j|_{A_j}\), \(\iota_j\) the inclusion furnished by
(3.2). In particular \(Y_m^{\rm core}=Y_0^{\rm core}\).
Here the symbols \(X_j^{\rm core}\) distinguish the filled
Jordan chart from the punctured complement \(X_j\) in §3.

Let \(a\) be the unique degree-two stage. It has one simple
critical point in \(H_a\): Riemann–Hurwitz gives exactly one
simple critical point in its Jordan source, and degree two
on the full inverse continuum forces it to be there (if all
points over the core were regular, a small simply connected
Jordan neighborhood of the full target core avoiding the critical
value would have two disjoint degree-one pullback disks, contrary
to connectedness and degree two on \(H_a\)). Its critical value
lies in \(H_{a+1}\). Before that stage, the successive proper
base changes are univalent and contain the full inverse copy
of \(H_a\). Hence that critical point has precisely one lift
in the selected partial return. After it, induction gives
\[
 v_k=P_{k-1}\circ\cdots\circ P_{a+1}(v_{a+1})\in H_k
      \subset A_k\quad (a+1\le k<m).
 \tag{4.1}
\]
The recurrence is exactly (10.7), since the immersion on the
core is the physical identity. This is the missing critical
retention assertion (10.5), not an inference from total degree.
No critical value lies on a base-change boundary. Theorem 10.2
now gives connected Jordan base changes, uniqueness of the
selected route, and a proper degree-two endpoint map with
compact embedded source in \(B_0\). By Proposition 11.1 its
relative endpoint is the actual restriction of \(f^S\);
its physical time word is the concatenation of the stage
words, and the nested domains retain every intervening
selected component. For stage exponents greater than one the
only critical encounter along the selected route is the one
counted by the degree-two factor (local degrees multiply).
This does not convert a physical-time word into a word of
arbitrary virtual address deletions.

The fixed-iterate issue in Theorem 14.1 can also be checked
without assuming local connectivity. Use the nested closed
suffix pullbacks from the first part of Lemma 2.2 at successively
deeper root targets \(V_n\) of the *fixed* return \(P=f^S\).
For each \(j\), the closed selected components \(C_{j,n}\)
are nested, compact, and \(P_j(C_{j,n})=C_{j+1,n}\).
Their intersections are \(H_j\) by the component shrinking
argument. Theorem 14.1 therefore applies to each fixed \(P_j\)
and proves equality on the limiting continua, not merely
inclusion. The physical peripheral subgroup/section is unchanged
by restricting to these nested annuli. This says nothing about
limits with increasing retimed exponent \(N_w+r\) or about
source-defined infinite-address end blow-ups.

## 5. Dependencies, actual coverage, and the exact first failure

The principal external recognition input is BOPT Theorem B,
pp. 17–18, and Lemma 4.1, p. 15, cited above. Classical inputs:
Riemann mapping/exterior equipotentials of full continua,
finite covering classification and based lifting, van Kampen,
and Riemann–Hurwitz for proper Jordan maps (already used in
chronology §9). No uniform-modulus or straightening distortion
estimate is consumed.

For comparison, published ordinary a priori bounds supply
closing quadratic-like collars on their own renormalization
cycles: Kahn, *A priori bounds ... I. Bounded primitive combinatorics*,
[arXiv:math/0609045v3](https://arxiv.org/pdf/math/0609045),
§§1.1–1.2, printed pp. 3–4 (Main Theorem, bounded successive
primitive-period ratios); Kahn–Lyubich, *A priori bounds ... III.
Molecules*, [IMS07-04](https://commack.math.stonybrook.edu/preprints/ims07-04.pdf),
Main Theorem, p. 1 and §2.2 (primitive molecule condition).
Our construction does not need a quantitative bound and includes
any genuine saturated cycle meeting (S1)–(S4), whether or not
these a priori theorems apply. These bounds cannot be invoked
to identify a Cantor-hull virtual carrier with the filled set
of an ordinary return or to separate its omitted obstacles.
Even for a parameter covered by either bound, an unauthorized
virtual hull or a specified incompatible phase is excluded.
There is no asserted uniform modulus for the arbitrarily thin
stage collars chosen here.

Sections 6–7 give concrete actual satellite and primitive cycles;
§8 supplies a strict actual-polynomial first-failure record.
These are not an assertion that the source's virtual-Cantor
block has already been identified.

**Exact ledger/interface accounting.**
* STAGE_FORWARD_CLOSURE (proved): consumed, with its premise
  explicitly checked as (S3); the initial inclusion is in §3.
* RELATIVE_COVER_LIFT (proved): consumed in (3.1); new exact
  peripheral subgroup equality, index, ordinary closure embedding
  and core-properness are in §3.
* PLANAR_CRITICAL_SPINE_TELESCOPE_COMPILER and
  QUADRATIC_JORDAN_BASE_CHANGE_DICHOTOMY (proved): consumed
  only after Lemma 2.2 and (4.1).
* Chronology Definition 10.1 items: actual compact Jordan
  inclusions (2.1), properness and degree, closing equality §4.
  Theorem 10.2 items 1–4: degree from (S1), univalent
  precritical pullbacks, critical containment (4.1), and
  compact authorization in the prescribed \(N_j\).
  Failure certificate 10.3/Adversarial correction 10.4:
  excluded by (4.1) and the extra ordinary closure collar.
  Proposition 11.1 and Theorem 14.1: applied in §4, with
  fixed physical clocks. §15.3: embeddedness, core-properness,
  component and compatible based phase, critical lift and
  degree retention all proved on the stated class.
* §16.1 items 1–3,5: an independently specified physical
  saturated root yields the return and collars within
  any given authorized neighborhoods, the full core identities,
  and actual selected phase maps. We do not construct/source-identify
  the required virtual second-scale hull or show that its
  prescribed safe gap contains it; nor establish item 4
  (full protected access action), item 6 (final enlargement
  and Wave completeness) or any of §16.2.
* finite_horizon_inflation.md §6 items 6–8: connected
  selected Jordan components and proper base-change degrees
  on these cores, with selected collar/component labels.
  Not the entire depth-q covering-embedding/prime-end/Wave
  datum on all enlarged or immersed sheets.

**First unresolved physical implication.** A finite source
virtual block must yield the entire forward-closed marking
and an actual cyclic saturated inverse-component itinerary
(S1), (S3) with a compatible peripheral phase (S4). The
source's finite connected hull and finite critical visits do
not establish equality of the *whole* connector images or
that the last selected inverse component equals the first.
Finite seed-forest saturation cannot close a cyclic root
by itself. It can absorb omitted obstacles, which destroys
the separated marking used in (3.1); even a relative-cover
lift of a different subgroup need not select the distinguished
collar. This is the first point where the present argument
does not apply to the general ledger quantifier. It is a
physical hypothesis about the hull, not an assumption that
the desired Jordan core or degree-two return exists.

**Ledger statuses that would change:** none. The subcase
requires review and a source-authorization theorem for the
virtual cycles before any promotion of MAPPING_TELESCOPE;
H1_FINITE_HORIZON_INFLATION, FINITE_HORIZON_ASSEMBLY,
H1_ANALYTIC_ACCESS_REALIZATION, H1_MARKED_CONSTRUCTION and
all downstream gates remain open.

**Attribution:** BOPT and the classical results listed above;
the archive's finite-horizon inflation, saturated seed
forest and chronology compiler; Kahn and Lyubich for the
ordinary a priori bounds. The cyclic compact-margin and
peripheral-lift construction is the present deduction.

**AI disclosure:** GPT-6.2 (OpenAI) performed proof search,
source comparison, mathematical writing and checker
generation. No independent human specialist verification
or kernel formalization of the analytic proof is represented.

## 6. Actual nonattracting satellite witness (two stages)

This is a physical period-two satellite return, with contacting little
Julia sets, not a model disk map or a primitive cycle mislabeled as
satellite. The algebraic parameter is the unique real zero \(c\) of
\[
 p(c)=c^3+2c^2+2c+2=0.
\]
The existing
[period-two satellite tip certificate](../../native_wave_transfer/RESULTS.md#real-period-two-satellite-misiurewicz-tip-exact-return-semantic-v1-refusal)
and [satellite v2 specification](../../native_wave_transfer/SPECIFICATION_v2_satellite.md)
identify this same polynomial. We only need the coarser exact isolator
\(-31/20<c<-77/50\): the signs of \(p\) at the endpoints are opposite,
and \(p'(c)=3(c+2/3)^2+2/3>0\). Write \(a=c^2+c\).
Then \(2079/2500<a<341/400<9/10\), and
\[
 f(0)=c,\quad f(c)=a,\quad f(a)=f(-a)=-a,\quad
 a^2=-a-c,\quad c^2=a-c .
 \tag{6.1}
\]
Indeed \(a^2+a+c=c\,p(c)\). The four orbit values are distinct
except for the final fixed value, and \(|f'(-a)|=2a>1\).
This is strictly preperiodic critical dynamics, so there is no finite
attracting/parabolic orbit (each such basin must attract the orbit of
a finite critical point). In particular it is a Misiurewicz quadratic,
with connected Julia set equal to its filled Julia set. For this
classical fact see the same physical satellite tip certificate,
and Douady–Hubbard, *On the dynamics of polynomial-like mappings*,
Ch. I §1 Proposition 2 for the nonescaping-critical connectedness
criterion; absence of attracting, parabolic or other bounded Fatou
components in the strictly preperiodic repelling case is the standard
subhyperbolic theorem.

Define the actual full intervals
\[
 H_0=[-a,a],\qquad H_1=[c,-a],\qquad H_2=H_0 .
\]
These lie in the filled Julia set by the bounded forward itinerary
(6.1), hence in the Julia set. They intersect at the repelling point
\(-a\). Directly over the complex plane, the real interval
\(H_1-c=[0,a^2]\) has full square-root preimage \(H_0\), whereas
\(H_0-c=[a^2,c^2]\) has exactly two components
\([c,-a]\) and \([a,-c]\) in its square-root preimage. In particular
\(f(H_0)=H_1,\ f(H_1)=H_0\) with degrees 2 and 1 respectively.
This verifies (S1) as an exact complex preimage identity, not just
an interval map. (S2) follows from the repelling preperiodic orbit
above. Take
\[
 E_0=\{c,\infty\},\qquad E_1=\{a,\infty\}.
\]
Both are separated from the selected stage continuum. Forward
closure is exact as an inclusion:
\(f(E_0)=\{a,\infty\}\subset E_1\) and
\(f(E_1)=\{-a,\infty\}\subset H_0\cup E_0\).
The two sphere critical values \(c,\infty\) are in each stage
marking. Choose the peripheral covers of §3, with the actual
interval component and physical collar as the specified phase.

For this witness one can construct the cyclic Jordan cores by
direct strict inequalities, independently of BOPT. Put
\[
 B_0=\mathbb D(0,1),\quad B_1=\mathbb D(c,7/8),\quad
 A_0=\mathbb D(0,\sqrt{7/8}),\quad
 A_1=\{-\sqrt{w-c}:w\in B_0\},
 \tag{6.2}
\]
using the positive-real-part square root on the right half-plane.
On the closed \(w\)-disk, \(\operatorname{Re}(w-c)>27/50\).
If \(z=-\sqrt{w-c}\), then
\(-\operatorname{Re}z\ge\sqrt{\operatorname{Re}(w-c)}>7/10\).
Using \(z^2=w-c\) and \(a=c^2+c\),
\[
 |z-c|=\frac{|w-a|}{|z+c|}
 < \frac{1+9/10}{77/50+7/10}
 =\frac{95}{112}<\frac78 .
\]
Thus \(\overline A_1\Subset B_1\) and
\(\overline A_0\Subset B_0\). Both are Jordan disks, and the two
boundary restrictions are proper of degrees 2 and 1.
The marking obstacles miss the respective closed target disks:
\(|c|>1\) and \(a-c=c^2>7/8\). The root \(H_0\) is contained
in \(A_0\) by \(a^2<(9/10)^2<7/8\), and \(H_1\Subset A_1\)
by its exact inverse branch and \(H_0\Subset B_0\).
The critical value of \(G_1=f|_{A_0}\) is \(c\in A_1\)
because \(f(c)=a\in B_0\) and \(c<0\).
Hence the selected base change \(D_1=f^{-1}(A_1)\cap A_0\)
is connected and Jordan, with degree two by Theorem 9.1;
\(f^2:D_1\to B_0\) is proper of degree two, with critical
value \(a\in H_0\), and the route closes. §3 constructs the
actual peripheral lifts and their closure embeddings, including
the returning basepoint connector. This verifies every clause
listed in §15.3 for these prescribed physical stages.

For comparison, on this very parameter the common marking
\(\Upsilon=H_0\cup H_1\cup\{\infty\}\) does *not* give
independent peripheral meridians of the two touching intervals:
the winding of a loop avoiding the union is constant on the
connected union. The individual collar encircling one interval
and missing the other cannot exist. This does not rule out a
bouquet marking or a different source-defined virtual cover.
It explains why the above choice is genuinely stage-dependent;
it does not silently change a prescribed common marking.

## 7. A primitive two-scale physical family of examples

The archive's independently certified nonattracting
period-3/period-9 Misiurewicz tip is defined by
\(P_{18}(c)+P_9(c)=0,\ P_{k+1}=P_k^2+c\), with
\(P_0=0\) and the adjacent dyadic bracket in
[Two actual complex quadratic-like returns](../nonattracting_tip_complex_two_scale_20261106.md),
sections "Exact parameter and real return data" and "The complex
theorem with its imported analytic ingredients." Use that written
analytic theorem and its exact Rouché and phase-gap certificates
as inputs (not merely the samples): the actual return restrictions
\(f^p,\ p=3,9\), have connected filled sets \(K_p\), contain
\(0\), have exactly one quadratic encounter and have pairwise
disjoint physical phase neighborhoods. The same source gives the
repelling critical orbit and \(K(f)=J(f)\).
These are separately source-identified ordinary terminal KL
returns by
[Both modified nests terminate at their first children](../tip_kl_terminal_first_child_20261106.md),
§§2–6, using KL *Decorations* Lemma 2.3 and §2.2.

For each \(p\) set \(H_j=f^j(K_p)\), \(0\le j<p\).
The suffix-component argument gives saturation without
assuming fullness of polynomial images: \(K_p\) is a component
of \((f^p)^{-1}(K_p)\) by the proper filled-set identity and
its compact isolation. For the component \(C\) of the suffix
preimage \((f^{p-j})^{-1}(K_p)\) containing \(f^j(K_p)\),
take the component of \((f^j)^{-1}(C)\) containing \(K_p\).
It maps onto \(C\) and lies in the selected full-return
component, so equals \(K_p\); hence \(C=f^j(K_p)\).
Components of polynomial pullbacks of full continua are full
by the nested Jordan-neighborhood argument of Lemma 2.2.
The same argument with one step proves (S1) on all phases.
Multiplicities are 2 on stage zero, 1 otherwise by the
disjoint physical phases and the unique quadratic critical
point of \(f\). With
\[
 E_j=\{\infty\}\cup\bigcup_{\ell\ne j} H_\ell
\]
one has separation, common forward-invariant marking, and
the critical values in every target marking. Thus (S3)
holds for these actual cycles. The peripheral cover choice
(S4) then gives the result at each of the two physical scales.
This does **not** give an interscale comparison between their
different prescribed native KL coset/prime-end atlases or
solve the virtual second-scale authorization of §16.1.

The same proof works for any actual primitive quadratic-like
return with connected Julia set and pairwise disjoint physical
phases, including ordinary primitive levels to which the
published Kahn/Kahn–Lyubich bounds apply. Neither primitive
disjointness nor the ordinary quadratic-like hypothesis is
needed in the general theorem of §§1–4.

## 8. An exact actual-polynomial degree-loss certificate

The critical retention conclusion is not a consequence of
proper stage maps, cyclic target labels, and compact ordinary
closure embeddings alone, even for a quadratic with \(K=J\).
Let \(f(z)=z^2-2\), the Chebyshev quadratic. Its filled Julia
set is \([-2,2]\), as follows also from
\(f(u+u^{-1})=u^2+u^{-2}\); points off the interval have a
representative \(|u|>1\) and escape. Use the two actual stages
\[
 \begin{split}
 Y_0&=\mathbb D(0,3/2),&
 A_0&=\mathbb D(0,7/5),\\
 Y_1&=\mathbb D(-2,49/25),&
 A_1&=\{-\sqrt{w+2}:w\in Y_0\},\qquad Y_2=Y_0.
 \end{split}
\]
Both \(\iota_j\) are literal closure inclusions.
Here \(\operatorname{Re}(w+2)\ge1/2\) for the closed target
disk, so the negative square root is holomorphic across that
disk and injective there. For \(z=-\sqrt{w+2}\),
\[
 |z+2|=\frac{|w-2|}{|z-2|}
 \le\frac{7/2}{2}=\frac74<\frac{49}{25}.
\]
Thus \(\overline A_1\Subset Y_1\), and
\(\overline A_0\Subset Y_0\). The stage \(g_0=f:A_0\to Y_1\)
is quadratic, \(g_1=f:A_1\to Y_0\) conformal. The critical
value of \(g_0\) is \(v=-2\notin\overline A_1\), since
\(f(-2)=2\notin\overline Y_0\).
The exact Failure certificate 10.3 is
\[
 (1,g_0,-2,A_1,D^+,D^-,D^+),\qquad
 D^\pm=\{\pm\sqrt{w+2}: w\in A_1\}.
\]
In this expression the square root is the analytic branch on
the simply connected \(A_1+2\) avoiding zero, positive over
\(w=-\sqrt2\); its two choices are exchanged by negation.
The compact separation of \(A_1\) from \(-2\) gives disjoint
closed inverse disks. Each lies in \(A_0\) because
\(|w+2|<49/25\), and each is mapped biholomorphically by \(g_0\)
onto \(A_1\). No connected selected continuation has degree
two; choosing the negative component instead does not help.

This verifies Definition 10.1 and Theorem 10.2(1),(2),(4)
on actual iterates with authorized local charts taken to be
the indicated plane neighborhoods, but fails (3). It is
**not** claimed as a counterexample to the ledger's
source-facing universal quantifier: it is not a source-identified
virtual stage cycle with saturated closed carriers. In fact
the second critical iterate \(f^2(0)=2\) is outside the
first target disk, so it cannot satisfy the saturated
cyclic critical itinerary of §1. It is an actual-dynamics
counterexample to dropping critical containment from the
planar criterion.

## 9. Exact peripheral-degree test for a prescribed cover

For an actual stage collar as in §2, replace the two chosen
based cyclic subgroups by arbitrary prescribed subgroups of
the corresponding marked complement fundamental groups.
Suppose the lift of inclusion exists (Lemma 5.1). The connected
restriction of each cover to the physical annulus is classified
by its intersection with the peripheral cyclic subgroup at
the selected basepoint. If these intersections are
\(\langle (t'_j)^{n'_j}\rangle\) and
\(\langle t_j^{n_j}\rangle\) with positive integers \(n'_j,n_j\),
then their annular covering degrees are precisely \(n'_j,n_j\).
The inclusion lift on the selected annuli has degree
\(n'_j/n_j\) (an integer by the lift condition), since projections
and inclusion commute. Thus it is injective on these entire
annuli iff \(n'_j=n_j\); to fill both by *one-sheeted physical
core charts* as in §3 requires \(n'_j=n_j=1\).
Likewise the polynomial lift to the selected next target
annulus has degree \(d_j n'_j/n_{j+1}\) when it exists, and
preserves the original physical annular degree iff
\(n'_j=n_{j+1}\). These equalities are in the actual
covering components, not in the abelianized ambient group.
If the intersection is trivial, the lifted annulus is
its infinite cyclic universal cover (a strip), and no
one-sheeted inverse section of the whole physical collar
exists. These tests are necessary for this specific whole-collar
filling and provide explicit first rejection tests for
externally prescribed phase choices. They do not imply
that every possible different core construction is impossible.

## 10. Reproduction and review boundary

Run from the repository root with Python 3.12:
\[
\texttt{python -B research/independent\_audits/h1\_mapping\_telescope\_20261126/verify.py}
\]
The checker uses only the standard library, exact rational
arithmetic and integer polynomial reduction. It reports the
satellite root isolator, identity and strict containment checks,
and the strict Chebyshev degree-loss margins as JSON.
No tolerances, sampling, random seeds, or network are used;
a failed assertion exits nonzero. It is registered as METADATA
because it checks arithmetic inputs, not the analytic theorem
or a model-to-physical implication. The analytic deductions
and their hypotheses are in this note. The associated workflow
only reads repository contents, runs the checker, and does
not commit or alter generated files.

The classification remains **partial**: a proved physical
subclass and concrete ordinary (including satellite) cycles,
plus an actual degree-loss diagnostic, but no verified
source-authorized nonordinary virtual cycle, no counterexample
to the original universal claim, and no ledger-status changes.

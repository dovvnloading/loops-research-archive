# Exact ideal boundaries and proper path classes for the selected real slit pair

Research investigation, 2026-11-23 (America/New_York). Base repository: `dovvnloading/loops-research-archive`, main `ed64c7ad839dcc8b799d53379434f892fdc92a2c`. Prepared with OpenAI GPT-6 Astra Pro; no human specialist review has occurred. Sections 2–4 give a written proof of the intrinsic ideal-boundary and A.1 class identification. The full immersion-marking obligation remains open for the reasons in §§5–6. This is not a Lean theorem or a global MLC result.

## Result and exact scope

The finite-type annulus setting is strong enough to prove the intrinsic ideal-boundary/class part of the selected-tip hypothesis H2 without assuming the conclusion as a new marking hypothesis. The necessary input is the actual dynamical geometry already isolated in [the family bridge](../../tip_family_theorem/PHYSICAL_BRIDGES.md), §§1–3: the central degree-two map, its actual interval Hubbard tree and pullback tree, the vertex intervals, and the strict real cut orders. The proof below constructs the comparison with the hyperbolic ideal boundary, retains every deck translate, proves preservation **and reflection** of A.1 subordination for all proper paths, and derives the source covering marking from the actual branch maps. It does not infer a path class from the shortest distance between endpoint labels. It does not identify a complete immersion restriction with a list of temporal excursions.

This addresses a selected locally connected embedded slit pair at one period, and hence every period for which those same input geometry assertions have been proved. It supplies the intrinsic classes needed by the [independent-width comparison](WIDTH_TRANSFER.md). It does not establish the complete A.3.2 immersion-pulled marking, issue #40's general non-locally-connected exceptional-interface theorem, uniform iterative crest transport, an identification with a four-hole canonical WAD, or MLC. Its elementary topology is classical; the contribution is the complete application to the archive's physical objects and the explicit retention of winding.

## 1. Inputs stated without the desired marking conclusion

Write `g=G_p=f_c^p` and `y_j=g^j(0)=x_{jp}`. Work with the actual embedded plane domains

\[
U=D(0,R),\qquad V=\operatorname{Comp}_0 g^{-1}(U)\Subset U,
\qquad g:V\longrightarrow U
\]

where the last map is proper holomorphic of degree two and its sole critical point is 0. The restriction is even and real-symmetric. Its filled set is a dendrite, its period-three renormalization is prime and primitive, and its three actual little filled sets are

\[
K_0=[y_3,y_6],\qquad K_1=[y_4,y_1],\qquad
K_2=[y_2,y_5],\qquad y_6=-y_3>0.
\]

Let \(a\) be the dividing fixed point. Assume the already proved orders

\[
y_2<y_5<y_3<0<y_6<a<y_4<y_1,
\tag{O1}
\]
\[
-y_1<-y_4<y_2<y_5<-a<y_3<y_6<a<-y_5<-y_2<y_4<y_1.
\tag{O2}
\]

The map is increasing on the negative half of \([-y_1,y_1]\) and decreasing on the positive half. The actual tree and its entire central preimage are

\[
T=[y_2,y_1],\qquad T'=[-y_1,y_1]=g^{-1}(T)\cap V.
\tag{1}
\]

The newest `PHYSICAL_BRIDGES.md` supplies direct written arguments for the little interval, shrinking the three phase neighborhoods, and exclusion of period two using the second critical point of \(g^2\). One should use those arguments, not revive the older unverified McMullen/nesting inference. The finite and all-period analytic arithmetic remain their stated upstream inputs.

Define the physical surfaces and maps

\[
\Omega=U\setminus T,\qquad \Omega'=V\setminus T',\qquad
f=g|_{\Omega'}:\Omega'\longrightarrow\Omega,
\qquad \iota:\Omega'\hookrightarrow\Omega.
\]

There is no assumption here identifying either ideal boundary with a table or identifying any admissible path class. Those are the conclusions to prove.

## 2. The ideal circle of a real slit: an explicit comparison

### Lemma 1 (analytic collar and all inner accesses)

Let \(D\subset\mathbb C\) be a bounded simply connected domain and let \(L=[u,v]\Subset D\), \(u<v\). Put \(m=(u+v)/2\), \(h=(v-u)/2\), and

\[
J(w)=m+\frac h2(w+w^{-1}),\qquad |w|>1.
\tag{2}
\]

Then \(J\) is a conformal bijection from \(\{|w|>1\}\) to \(\mathbb C\setminus L\). Its inverse is the branch

\[
w=\frac{z-m}{h}+\sqrt{\left(\frac{z-m}{h}\right)^2-1}
\]

selected by \(|w|>1\), or equivalently its behavior at infinity. The preimage \(J^{-1}(D\setminus L)\) contains a complete collar \(1<|w|<1+\epsilon\) for some \(\epsilon>0\). Its inner prime-end boundary is exactly \(|w|=1\).

**Proof.** The only zeros of \(J'(w)=(h/2)(1-w^{-2})\) are \(w=\pm1\), outside the open domain. Solving the quadratic for \(w\) yields reciprocal roots, exactly one of modulus greater than one off the slit; this proves bijection and the inverse formula. The continuous map \(J\) sends the compact unit circle to \(L\Subset D\); uniform continuity therefore puts an entire thin closed collar outside that circle inside \(D\). In the \(w\)-plane the boundary is an actual analytic circle, so small circular crosscuts in this collar provide one prime end at each point, and every approach in this end of the annulus is one of these prime ends. One can also prove the last assertion using the annulus uniformization in Lemma 2 below, followed by Schwarz reflection at this analytic circle.

On the boundary,

\[
J(e^{i\theta})=m+h\cos\theta,
\qquad
\operatorname{Im}J(re^{i\theta})
=\frac h2(r-r^{-1})\sin\theta.
\tag{3}
\]

Consequently every point of \((u,v)\) has exactly two distinct accesses, with \(0<\theta<\pi\) the upper bank and \(\pi<\theta<2\pi\) the lower bank. The endpoints \(v,u\) correspond to the single points \(1,-1\). This proves completeness and sidedness of the access list, rather than counting only chosen crosscuts. No external polynomial ray angle is used. ∎

### Lemma 2 (agreement with the KKL hyperbolic ideal boundary)

The surface \(D\setminus L\) has two hyperbolic ideal boundary circles as defined in KKL A.1. Its inner ideal circle is canonically identified with the circle in Lemma 1; the identification extends the identity on the open surface and agrees with its prime-end topology. No Jordan assertion about \(\partial D\) is required.

**Proof.** The complement on the sphere has exactly two components, the slit and the complement of the simply connected domain. Both are nondegenerate. Thus the doubly connected uniformization theorem gives a conformal annulus of finite positive modulus. Finiteness at the slit can also be seen directly: in the \(w\)-coordinate the domain contains \(1<|w|<1+\epsilon\) and is contained in \(1<|w|<M\) for some finite \(M\). The other end is represented by the other annular boundary, independently of whether its Euclidean landing map is one-to-one.

Write its universal cover as a strip \(\Sigma_h=\{0<\operatorname{Im}\zeta<h\}\), with deck generator \(\zeta\mapsto\zeta+2\pi\). The map \(\zeta\mapsto\exp(\pi\zeta/h)\) identifies the strip with a half-plane. The deck generator becomes multiplication by \(\exp(2\pi^2/h)\). Its limit set is exactly the two fixed ideal points \(0,\infty\). Removing them from the ideal circle leaves two open lines; quotienting by the deck generator gives exactly the two circles

\[
(\partial\mathbb D\setminus\Lambda)/\Delta
\cong (\mathbb R/2\pi\mathbb Z)\sqcup
(\mathbb R/2\pi\mathbb Z).
\tag{4}
\]

This is KKL's definition, not a substitute boundary.

Choose the annular uniformization so that the slit end corresponds to the lower strip rail. Composing with (2), the annular map has an analytic source boundary circle at this end. Properness of the conformal equivalence maps this end to the chosen circular end; Schwarz reflection, applied also to the inverse, extends it to a homeomorphism of those boundary circles. Equivalently the crosscut chains in the full collar (2) are exactly the chains approaching the corresponding rail. Hence the KKL and slit-access compactifications agree at every inner boundary point. At the other end retain the annular ideal circle itself; no Euclidean outer-boundary parametrization or pointwise extension of \(\iota\) there is being asserted. ∎

**Source inputs for these lemmas.** The doubly connected uniformization and Schwarz reflection principles are standard conformal mapping theorems. KKL explicitly uses the annulus/strip model, deck translation and two lifted ideal intervals in Appendix A.2.3. The explicit Joukowski map, its inverse, its derivative and the bank formula are proved above. This use does not depend on local connectivity of an unknown Julia continuum: the removed continuum in this lemma is the already identified nondegenerate real segment.

## 3. Exhaustive path classes, including all winding numbers

### Lemma 3 (exact subordination criterion)

Let \(B\) be a proper connected open arc of the inner ideal circle, and let \(\gamma\) be any proper path with both endpoints on that circle. Fix a lift of the initial endpoint to the lower rail of \(\Sigma_h\), and lift \(\gamma\) continuously. Then

\[
\gamma\text{ is subordinate to }B
\iff
\text{the two endpoints of its lift lie in one and the same lift of }B.
\tag{5}
\]

The endpoint of the lift exists. If the endpoint positions modulo \(2\pi\) are \(s,t\), its possible lifted terminal positions are \(t+2\pi k\), \(k\in\mathbb Z\), and (5) uses the **actual** integer \(k\) determined by the path. It does not choose the smallest angular distance.

**Proof.** Because \(\gamma\) is proper in KKL's sense, it extends continuously at its ideal endpoints. A sufficiently small terminal collar rectangle about the endpoint is evenly covered, and an eventual tail of \(\gamma\) lies in it. That tail stays in one component of its preimage, so its lifted endpoint converges on one fixed rail interval. Infinite winding without a convergent lifted rail endpoint is not hidden here: it would leave every such evenly covered collar rectangle infinitely often and would violate properness.

Suppose first that \(\gamma\) is subordinate to \(B\). Choose a thin neighborhood of \(B\) in the ideal closure whose lifts are disjoint simply connected collar strips, one for each lift of \(B\). A representative homotopic to \(\gamma\) rel endpoints lying in this neighborhood lifts into one such strip. Homotopy lifting fixes both lifted endpoints. They therefore lie in the same lift of \(B\).

Conversely, suppose its lifted endpoints lie in one lift \(\widetilde B\). The compact rail segment between the two endpoints is contained in \(\widetilde B\). In every neighborhood of \(B\) there is a collar path joining those endpoints in that same lift, with interior in the strip. The universal strip is convex; the given lifted path and that collar path are homotopic rel endpoints, with all interior path points remaining in the strip (straight-line homotopy after parametrization suffices). Projection gives the required rel-endpoint homotopy into every prescribed neighborhood. This is precisely KKL A.1 subordination. ∎

For the whole inner circle, every path with both endpoints on that circle is subordinate to it: retain its actual endpoint displacement and draw a collar path with that displacement. A path with an endpoint on the outer ideal circle cannot be subordinate to an inner boundary arc. These assertions account for both ideal circles.

### Corollary (the actual Joukowski logarithmic lift)

The map

\[
\mathcal P(\zeta)=J(e^\zeta),\qquad
\widetilde\Omega_D=\{\operatorname{Re}\zeta>0:
\mathcal P(\zeta)\in D\},
\]

is the universal cover of \(D\setminus L\), with deck group
\(\zeta\mapsto\zeta+2\pi i k\). In particular the same-lift criterion (5)
holds in the explicit angular windows on \(\operatorname{Re}\zeta=0\)
used by the archive's conformal estimates.

Indeed, \(J^{-1}(D\setminus L)\) is an annulus containing a complete collar of
the unit circle. Its inclusion into \(\{|w|>1\}\) induces an isomorphism on
fundamental groups: the positively oriented collar circle is a generator
on both sides. Pulling back the exponential universal cover therefore
gives one connected cover with trivial fundamental group. The lifted
physical domain is invariant under every deck translate, although its
outer boundary generally is not a straight line. The comparison with the
uniformizing strip is an equivariant lift of the same conformal map and
extends at the inner rail by Lemma 2. Consequently (5) selects the same
deck integer in either model. No replacement of the physical domain by a
round annulus is made in this corollary.

### Consequence for every marked path and Wave

The comparison in Lemmas 1–2 fixes the open domain, takes the explicit access cuts to their genuine KKL ideal points, and identifies all collar neighborhoods. By (5), it preserves **and reflects** every relative-endpoint path class, all integer windings, the exclusions for a multi-interval of length at most two, and subordination to each larger multi-interval. Simplicity and disjointness concern the same open curves, so they too are preserved. Therefore it identifies every admissible lamination and Wave; taking the smallest allowed base and end multi-intervals on either side gives the same base, ends and closed crest.

This is an exhaustive class argument. It is stronger than verifying a table of selected arc representatives. It also means that H3 may use (5) to select its fixed electrode windows: a parent subordinate to \((I_9,I_0,I_1)\) lifts to the left-tip windows in one lift of that base, and a child subordinate to \((S_1,S_2,S_3)\) lifts to its designated source windows. An extra full-slit winding cannot also belong to that same proper base lift.

### Necessary correction to a tempting finite test

The shortest cyclic distance between endpoint atom labels is **not** the full A.1 admissibility test. In a ten-atom annulus choose endpoints at angular coordinates \(1/2\) and \(3/2\), where angles are measured in units with period 10. The short representative has lifted displacement 1, is subordinate to two adjacent atoms, and is excluded. The other simple representative has terminal lift \(-17/2\), displacement \(-9\), and is subordinate to the long arc containing ten atoms but omitting the common endpoint of the two adjacent end atoms. It is not subordinate to the short two-atom arc. For example, the explicit curve

\[
\theta(t)=\tfrac12-9t,\qquad r(t)=\exp(\epsilon\sin\pi t),
\quad 0<t<1,
\]

in a round annulus (with angular coordinate \(2\pi\theta/10\)) is simple and proper for sufficiently small \(\epsilon>0\). Its total angular variation is less than one full turn. Thus identical endpoint atom labels can have different A.1 decisions. The archive's 3/3/7 and 3/3/5 calculations are valid only after their particular boundary-parallel classes are fixed; they are not a general path-class classifier.

## 4. The physical target marking and complete source covering marking

By the actual dendrite geometry in §1, KKL's smallest connected hull of the three little filled sets is \(T\). The real interval has no additional branch point; KKL §2.5 adds its dividing fixed point \(a\) to the three vertex sets. The five interior cut locations are therefore exactly

\[
(y_5,y_3,y_6,a,y_4).
\tag{6}
\]

Lemma 1 gives two distinct prime ends above each of these five locations. With the terminal left atom numbered 0 and the upper bank ordered from left to right, the ten atoms have types

\[
[K_2,E_{20},K_0,E_{0a},E_{a1},K_1,E_{a1},E_{0a},K_0,E_{20}],
\tag{7}
\]

where \(E_{20}=(y_5,y_3)\), \(E_{0a}=(y_6,a)\), \(E_{a1}=(a,y_4)\). The left and right tips lie **inside** terminal atoms; they are not extra cut endpoints. The outer ideal circle is one whole-component atom.

Removing the sole critical point with \(T'\) makes \(f:\Omega'\to\Omega\) a proper unbranched two-fold cover. Thus its ideal boundary map is an actual two-fold covering by KKL A.3.1, or directly by the annular strip model. Each target cut has exactly two source preimages, and the orbit/fixed identities give them without choosing a symbolic automaton:

| Target cut | Its two real preimages in \(T'\) |
|---|---|
| \(y_5\) | \(-y_4,y_4\) |
| \(y_3\) | \(y_2,-y_2\) |
| \(y_6\) | \(y_5,-y_5\) |
| \(a\) | \(-a,a\) |
| \(y_4\) | \(y_3,y_6\) |

The proper degree-two count excludes any additional off-real source cut. Sorting these ten actual locations by (O2) gives

\[
(-y_4,y_2,y_5,-a,y_3,y_6,a,-y_5,-y_2,y_4).
\tag{8}
\]

Their two banks yield exactly twenty source atoms \(S_0,\ldots,S_{19}\), with \(S_0\) the left terminal atom. The source right terminal atom is \(S_{10}\). Every point, including slit tips and the source access over the critical value, is accounted for by the covering of ideal circles.

To identify the labeling of this cover, use \(g(-y_1)=y_2\): the source left tip maps to the target left tip. On negative real inputs the positive derivative preserves upper/lower banks and on positive inputs the negative derivative exchanges them. The source upper passage through 0, which is interior to the removed slit, passes continuously around the target right tip. Reading (8) and the five exact endpoint images therefore gives

\[
f_*(S_s)=I_{s\bmod10},\qquad 0\leq s<20.
\tag{9}
\]

This identifies all intervals, not just their cardinalities. As a check on the nontrivial turn, \(S_5\), lying over \((y_3,y_6)\), maps to the terminal target atom \(I_5\): its negative half maps to the upper bank of \(K_1\), its positive half to the lower bank, and the one source access over 0 maps to the one tip access at \(y_1\). This uses the analytic two-fold covering, so there is no additional hidden access at the critical point.

## 5. Attachment blocks and the unresolved full immersion marking

Equation (1) gives one and only one added tree component

\[
A=T'\setminus T=[-y_1,y_2),
\]

whose closure attaches at the target left endpoint \(y_2\). The source has two distinct accesses at \(y_2\), but the target has one tip access there. The complete new attachment boundary is the source arc through \(S_{19},S_0,S_1\), including its internal joints. The source access at \(-y_1\) is inside \(S_0\).

This is the geometric configuration for the proposed specialization of KKL Proposition 6.5: the immersion is the inclusion, injective near the entire filled set; \(T'\) is its actual tree preimage in that neighborhood; and every component attached to \(T\) has been listed. The proposition's attachment formula applies to both open multi-intervals and their closures and includes the **whole** Carathéodory boundary of an attachment. Reading that formula gives the following geometric source blocks, with their internal joints included. Their identification with the maximal native pullbacks, in the archive's retained geometric-trace category, is not asserted independently of the unresolved interpretation below.

| Target atom | Source block | Boundary description |
|---|---|---|
| \(I_0\) | \(S_{18},S_{19},S_0,S_1,S_2\) | from lower \(y_5\) around the source left tip to upper \(y_5\) |
| \(I_1\) | \(S_3,S_4\) | upper \(y_5\) to upper \(y_3\) |
| \(I_2\) | \(S_5\) | upper \(y_3\) to upper \(y_6\) |
| \(I_3\) | \(S_6\) | upper \(y_6\) to upper \(a\) |
| \(I_4\) | \(S_7,S_8,S_9\) | upper \(a\) to upper \(y_4\) |
| \(I_5\) | \(S_{10}\) | upper \(y_4\) around the common right tip to lower \(y_4\) |
| \(I_6\) | \(S_{11},S_{12},S_{13}\) | lower \(y_4\) to lower \(a\) |
| \(I_7\) | \(S_{14}\) | lower \(a\) to lower \(y_6\) |
| \(I_8\) | \(S_{15}\) | lower \(y_6\) to lower \(y_3\) |
| \(I_9\) | \(S_{16},S_{17}\) | lower \(y_3\) to lower \(y_5\) |

In particular the added component is not counted once as a graph edge: its two banks and its terminal passage all occur. The open blocks omit only their two listed external endpoint accesses; taking the source access closure adjoins those two endpoints. The attachment root \(y_2\) is inside \(I_0\), not a target marking endpoint. Thus this specific attachment does not create an unrecorded additional block at one of the ten marking endpoints. One should nevertheless continue to treat images of closed crests and closures of images as different operations; no general commuting-of-closure rule follows.

The blocks are pairwise disjoint and cover the inner source circle except for their external endpoints. Each is a union of consecutive covering atoms and their internal joints. The outer component also needs a proof; merely retaining it in the picture would not prove the global refinement condition.

### Why the outer pullback proof is not accepted here

Let O and O′ denote the complete outer ideal circles. The covering has
one full-circle atom on O′, but proving the immersion assertion
\(\iota^*O=O'\) requires the exact maximal-subordination definition in
KKL A.3.2. The inclusion is not proper on O′, so this is not a
pointwise boundary inverse image.

A tempting argument says that every target path with an inner endpoint
has an inner-ended source excursion, and then proves maximality using a
tiny proper loop at each source inner point. This only settles the
intended implication after the full meaning of *unique proper
restriction* has been verified. Counting temporal entrance/exit
components alone is insufficient: the archive's
[geometric-trace audit](../../mlc_unified/canonical_kl_geometric_trace_proper_end_response.md),
§§1 and 4, explicitly retains other proper paths in the inverse trace,
including paths that omit a loop or backtrack. The
[restricted-interface audit](../../mlc_unified/canonical_kl_restricted_interface_classification.md),
§11, keeps this exhaustion problem open.

There is also a definition issue to resolve before using the uniqueness
criterion. If “proper paths contained in the inverse trace” means every
continuous map into that trace, an embedded boundary-to-boundary arc
contains a proper hairpin obtained by following an initial subarc and
returning along it. Such paths can defeat the unique-member assertion
even when there is only one temporal excursion. One cannot silently
replace the source category by reduced arcs or parameterized subpaths
to make uniqueness automatic. The statement of KKL A.3.2 and the
archive's retained geometric-path category must be reconciled explicitly.

Accordingly, **no outer maximality theorem or complete refinement theorem
is claimed here**. The attachment table above records the actual geometry
and the specialization proposed using Proposition 6.5; it is not a proof
that every geometric-trace restriction has been enumerated. The full
MARK row remains open. In particular, Proposition A.12 is not activated
by this table alone.

The monotone quotient that collapses the closed attachment arc to the
target tip remains a useful record of the table. It is not a continuous
extension of the physical inclusion: an attachment interior maps to a
target interior point. It cannot substitute for the actual proper-path
operation.

## 6. Exact dependency boundary

The proved intrinsic statement uses the very same open subsets
\(\Omega,\Omega'\subset\mathbb C\), the complete ideal compactifications
of Lemmas 1–2, and the actual winding-sensitive class criterion of
Lemma 3. Thus it identifies all A.1 path and Wave classes on each
surface separately, with the target marking and source covering marking
of §4. No assertion about how an arbitrary target trace restricts to the
source is needed for this identification.

The independent parent and child suprema in the companion width proof
are defined by their own three-atom bases on these two surfaces. Their
lower foliations and upper metrics use only those intrinsic classes.
The square-sum metric is pushed down by the universal cover of one
surface; it is not pushed through the immersion. Therefore the open
immersion-marking and geometric-trace exhaustion problems do not enter
that proof.

For a specifically drawn crossing representative, one can still follow
its two temporal pieces and compute source spans 3,3 and an avoiding
span 7, with the selected covering images of spans 3,3,5. Those are
statements about the represented relative classes. They do not exhaust
all proper paths in the geometric inverse trace and do not imply that
a common parent realizes the independently optimized child suprema.

## 7. Adversarial checks and retained gap

1. **No circular H2 assumption:** the inputs of §1 are sets, maps, branch degree and actual dynamical vertex geometry. The ideal/access/class identification is constructed later.
2. **All ideal boundary points:** finite modulus gives exactly two rail quotients; Joukowski identifies every point on the inner circle. There are no leftover deck-indexed ideal circles.
3. **All windings retained:** equation (5) keeps the actual endpoint lift integer. It never substitutes a winding vector or the shortest cyclic distance.
4. **Both directions of subordination:** the proof supplies necessity by homotopy lifting and sufficiency by a representative in every collar. Matching endpoint positions alone does not provide this without the lift condition.
5. **Outer boundary:** it remains its genuine annular ideal circle. Its Euclidean boundary need not be Jordan; its inclusion is not asserted proper.
6. **All source cuts:** the five exact two-point fibers and the degree-two count exclude extra off-real cuts. The source critical point belongs to the removed slit; its ideal access behavior is that of an unramified annulus cover.
7. **Whole attachment:** both source banks, the source tip and all joints appear. Inclusion properness fails there exactly as it should.
8. **Immersion gap retained:** matching the compactifications does not enumerate the complete geometric inverse trace or prove the unique-restriction premise of a maximal pullback. The outer marking and full refinement remain open.
9. **No class-to-geometry promotion:** knowing that a relative class admits a two-component representative does not force every representative to have exactly two intersection components. The proof states the actual-component requirement explicitly.
10. **Scope:** fixed selected finite-type slit geometry. No non-LC model lift, arbitrary virtual immersion, depth-uniform estimate, native global Wave amplification or MLC is established.

## 8. Sources inspected

The original KKL source was inspected directly. The exact primary-source locators are:

- Kahn–Kapiamba–Lyubich, *MLC for parabolically bounded primitive renormalization*, arXiv:2606.27272v1: [§2.5, physical Hubbard tree and vertices](https://arxiv.org/html/2606.27272v1#S2.SS5).
- [Appendix A.1, hyperbolic ideal boundary, subordination, paths and Waves](https://arxiv.org/html/2606.27272v1#A1.SS1).
- Appendix A.2.3, annular universal strip and canonical ideal marking.
- [Proposition 6.5, whole attached-component boundaries, open and closed intervals](https://arxiv.org/html/2606.27272v1#S6.E5), and Proposition 6.6, actual covering/pulled-marking refinement.
- Appendix A.3.1–A.3.2, ideal cover and actual proper restriction; [Proposition A.12](https://arxiv.org/html/2606.27272v1#A1.E12), with its refinement hypothesis retained.
- Repository `research/tip_family_theorem/PHYSICAL_BRIDGES.md`, §§1–3: current actual interval and nesting proofs; `papers/tip_family_preprint_v2_20261116/sections/referee_scope.tex`, H2; `REFEREE_REPORT.md`, F2.
- `research/independent_audits/issue40_native_attachment_edge_incidence_20261115/NOTE.md` and its verifier: actual p=3 order, attachment and edge data, with its precise existing limitations.

The basic conformal uniformization/reflection theorems and covering homotopy lifting are imported classical mathematics. They have not been formally proved here. The new work is the explicit proof that they apply to these surfaces and preserve the precise intrinsic A.1 path predicates used by the independent-width theorem. The separate A.3.2 immersion comparison retains its stated gap.

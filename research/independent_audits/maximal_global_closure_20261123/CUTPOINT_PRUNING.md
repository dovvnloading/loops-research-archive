# Physical marked incidence from singleton cut fibers

Date: 2026-11-23  
Base revision: `ed64c7ad839dcc8b799d53379434f892fdc92a2c`  
Status: written topological theorem and a physical carrier construction;
application to the named native KKL carrier remains conditional on its
identification. No MLC, UPTCR, stationary exit, or width claim is made.

AI disclosure: GPT-6 Astra Pro was used for proof search, source comparison,
drafting, and verifier construction. The independent checks described here
are AI-assisted; no new human mathematical verification is represented.

## 1. The exact change

The July Gate-N2 audit proves that the selected inverse sheet
`Omega_n` is an entire component of the physical filled continuum with
one preperiodic boundary point `alpha^n`. It leaves the non-locally-connected
marked-incidence implication open behind a model-identification package.
That package asks for a global marked comparison of models, selected-sheet
correspondence, and geometric small-Julia correspondence.

For the **set-theoretic incidence implication alone**, those last three
identifications can be dispensed with. A full hull lift under any monotone
dendrite quotient with a singleton fiber at the cut point has exactly the
required terminal-side property. Its truth is independent of which such
quotient is used. This does not identify the whole lifted carriers or any
proper-path relation.

There is also a concrete improvement in the existential input: in the
periodically repelling case, the plane quotient in Kiwi's theorem has a
dendrite Julia set. This follows from that plane quotient and empty interior;
it need not be retained as an additional unproved assumption.

The result below constructs an actual physical continuum `T_Kw`, proves
its marked terminal-side incidence without local connectivity of the
physical Julia set, and gives the resulting conditional stationary count.
The separate question whether the exact carrier and markings used by KKL's
Wave argument agree with this construction remains explicit.

## 2. Source inputs and notation

The archive inputs are:

* [Selected predecessor endpoint, Theorem 4.3 and Proposition 4.5](../../mlc_unified/kkl_stationary_n2_selected_predecessor_endpoint.md):
  the physical critical-limb inverse `phi_0`, the terminal sheets `Omega_n`,
  and the existing conditional full-lift route.
* [Kiwi model audit, Sections 2 and 6](../../mlc_unified/kkl_stationary_n2_kiwi_model_identification_audit_20260727.md):
  the same-filled quadratic-like restriction, straightening, singleton
  finite-orbit fibers, and the unresolved identification with KKL's model.
* [Frontier audit, Sections 4--8](../../mlc_unified/kkl_stationary_n2_frontier_audit_20260727.md):
  the currently retained N2 boundary.

Primary references are:

1. J. Kiwi, *Real laminations and the topological dynamics of complex
   polynomials*, Adv. Math. **184** (2004), 207--267,
   [DOI](https://doi.org/10.1016/S0001-8708(03)00144-0),
   [readable article](https://www.academia.edu/91433960/Real_laminations_and_the_topological_dynamics_of_complex_polynomials).
   Theorem 2, pp. 209--210; Proposition 3.15(2), p. 232;
   Proposition 4.2, pp. 233--234;
   Proposition 4.7 and Corollary 4.8, pp. 235--236;
   Theorems 5.12--5.13, pp. 243--245.
2. J. Kahn, A. Kapiamba, M. Lyubich,
   [*MLC for parabolically bounded primitive renormalization*, v1](https://arxiv.org/html/2606.27272v1),
   Section 2.5, p. 13, for the Hubbard hull and its lifted version;
   the stationary critical-end argument in Section 6 for the intended count.

The Kiwi inputs used here are the monotone plane quotient by fibers,
singleton complete fibers at periodic and preperiodic Julia points, the
locally connected quotient Julia set, and the induced topological polynomial.
They are used on a periodically repelling polynomial with connected Julia
set. Transport through a fixed straightening gives the corresponding
statements for the same-filled quadratic-like restriction. No identification
with an independently named quotient is included in these imports.

A **dendrite** is a locally connected continuum containing no simple closed
curve. Any two points of a dendrite are joined by a unique arc, and every
connected subset contains that arc. A monotone map has connected point
fibers. All continua in this note are compact metric spaces.

## 3. The quotient target is a dendrite

### Proposition 3.1

Let `K` be a full planar continuum with empty interior. Let
`q : C -> Y`, where `Y` is a plane, be a continuous monotone quotient such
that every non-singleton fiber is contained in `K`, and every fiber meeting
`K` is wholly contained in `K`. Suppose `D = q(K)` is locally connected.
Then `D` is a dendrite.

#### Proof

The restriction of `q` to `C \ K` is a homeomorphism onto `Y \ D`.
Indeed its fibers are singletons; it is the restriction of the quotient to
the saturated open complement, and is therefore an open continuous
bijection. Thus `Y \ D` is connected, because `C \ K` is connected.

The set `D` has empty interior. If a nonempty open set `V` in `Y` were
contained in `D`, the nonempty open set `q^{-1}(V)` would be contained in
`q^{-1}(D) = K`, contradicting empty interior of `K`.

If `D` contained a Jordan curve, its bounded complementary Jordan domain
would contain a point outside `D`, since `D` has empty interior. That point
could not be connected to infinity in `Y \ D`: the Jordan curve is a
subset of `D`. This contradicts connectedness of the complement. Hence
`D` contains no simple closed curve. It is a locally connected continuum,
so it is a dendrite. QED.

### Corollary 3.2: actual periodically repelling polynomial

For a connected periodically repelling polynomial, `K = J` has empty
interior, using the usual classification of periodic Fatou components and
the no-wandering-domain theorem. Kiwi's plane fiber quotient has precisely
the saturation properties in Proposition 3.1, and its quotient Julia set
is locally connected. Therefore its target is a dendrite. Kiwi's complete
fibers at every finite-orbit point are singletons.

This conclusion improves the existential input in the July model audit.
It does not assert that a symbol `pi` in another construction already
denotes this quotient.

## 4. One-cut hull theorem

### Lemma 4.1: component correspondence

Let `q : X -> D` be a continuous monotone surjection from a continuum onto
a dendrite. Suppose `q^{-1}(b) = {a}`. Then inverse image gives a bijection

```
components of D \ {b}  <->  components of X \ {a}.
```

More precisely, if `C` is a component of `D \ {b}`, then `q^{-1}(C)` is
one entire component of `X \ {a}`.

#### Proof

First, the inverse image of a compact connected set under a monotone map
of compact Hausdorff spaces is connected. For if its inverse image had a
separation into two compact sets, connected fibers would place each fiber
in one side, and the two compact images would separate the target set.

For a component `C` of `D \ {b}` and any two points `x,y` of its inverse
image, the compact arc `[q(x),q(y)]` lies in `C`. Its inverse image is
connected by the preceding paragraph and contains both `x` and `y`.
Consequently `q^{-1}(C)` is connected, even though `C` need not be closed.

Conversely any connected subset of `X \ {a}` has connected image avoiding
`b`, and hence lies over a single component of `D \ {b}`. The sets
`q^{-1}(C)` are therefore exactly the components. This also proves both
directions of the asserted correspondence. QED.

### Theorem 4.2: physical terminal-side incidence

In Lemma 4.1 let `M_1,...,M_s` be nonempty subcontinua of `X` avoiding
`a`. Put

\[
 A=\bigcup_{i=1}^{s}q(M_i),\qquad
 S=\operatorname{Hull}_D(A),\qquad
 T=q^{-1}(S).
\]

For every component `Omega` of `X \ {a}`:

1. `T intersect Omega` is connected or empty;
2. the following are equivalent:

\[
 T\cap\Omega\ne\varnothing
 \quad\Longleftrightarrow\quad
 \exists i\;(M_i\subset\Omega).
\tag{4.1}
\]

The hull `S` is compact, and `T` is a physical subcontinuum of `X`
containing every `M_i`.

#### Proof

Choose `z_i` in `q(M_i)`. The finite union of the continua `q(M_i)` and
the arcs `[z_1,z_i]` for `i > 1` is compact and connected. Any connected
set containing `A` must contain those arcs, so that finite union is
exactly `S`. Monotonicity makes `T` a continuum, and its definition
includes all the marks `M_i`.

Write `Omega = q^{-1}(C)` by Lemma 4.1. Both `S` and `C` are arc-convex
in the dendrite. Their intersection is therefore connected when nonempty.
Applying the compact-arc argument of Lemma 4.1 to `S intersect C` proves
that

\[
 T\cap\Omega=q^{-1}(S\cap C)
\]

is connected or empty.

The singleton-fiber assumption and `a notin M_i` imply that `q(M_i)`
avoids `b`. Each connected `q(M_i)` is therefore wholly contained in
one component of `D \ {b}`. If no such image is in `C`, all of `A`
lies in `D \ C`. The latter is a connected subtree containing `b`.
The least connected hull `S` must then lie in `D \ C`. This proves the
forward implication of (4.1) by contraposition.

If `M_i subset Omega`, its nonempty image lies in `S intersect C`, and
`M_i subset T intersect Omega`. This proves the reverse implication. QED.

### Corollary 4.3: independence from the whole model

Suppose two monotone dendrite quotients of the same physical continuum
have singleton fibers at the same physical point `a`. Form both full hull
lifts from the **images of the same physical marks** `M_i`. Then, for
every component `Omega` of `X \ {a}`, one lifted hull meets `Omega` if
and only if the other does.

The proof is (4.1) for each map. There need be no homeomorphism between
the two quotient dendrites, and the lifted hulls need not be equal as
subsets. This is an equality of one-cut incidence data, not an equality
of access, edge, or width data.

### Why the singleton condition is real

Take a triod with two marked endpoints on its horizontal arms, and collapse
its unmarked vertical arm to the central point of an interval. This is a
monotone quotient to a dendrite. The full lift of the hull of the two
marked images is the whole triod. Cutting the physical triod at its
central point leaves an unmarked vertical component that meets the full
lift. Its quotient fiber is non-singleton, so Theorem 4.2 does not apply.

This example shows exactly why monotonicity and a model hull alone do not
justify terminal pruning at a physical point.

## 5. Constructing a physical full-hull carrier

Fix the transported Kiwi plane quotient `q` of a periodically repelling
quadratic-like filled continuum `K`. Let `K_0,...,K_{P-1}` be its physical
primitive small-Julia cycle. Define

\[
 S_{\rm Kw}=\operatorname{Hull}_{q(K)}
     \left(\bigcup_i q(K_i)\right),\qquad
 T_{\rm Kw}=q^{-1}(S_{\rm Kw}).
\tag{5.1}
\]

This definition uses actual continuum images, never a point collapse of
a small Julia set. Section 3 proves the dendrite hypothesis; Section 4
proves that `T_Kw` is a physical continuum containing the entire cycle.
At every finite-orbit point `a` outside that cycle it has property (4.1).

For completeness, the critical-point correspondence needed for forward
invariance is proved next. It is not silently added to the statement of
Kiwi's Proposition 4.2.

### Lemma 5.1: the critical fiber in the quadratic quotient

Let `f` be the straightened quadratic, let `c_*` be its critical point,
and let `v=f(c_*)`. Let `q` be Kiwi's plane fiber quotient and `Q` its
induced degree-two branched cover. Then `q(c_*)` is the unique finite
critical point of `Q`, with local degree two.

#### Proof

The fiber `E=q^{-1}(q(v))` is a full compact continuum by Kiwi,
Proposition 3.15(2), p. 232. Choose nested closed Jordan disks `V_n`
with `E` in their interiors and intersection exactly `E`. Such disks
are obtained from an exterior Riemann-map exhaustion of a full
continuum; if `E` is a singleton, ordinary shrinking disks suffice.

Every `V_n` contains `v`. The full inverse of its punctured interior
under the quadratic is a connected two-sheeted cover: a loop around
the only critical value has the transposition monodromy of the local
quadratic map, so it joins the two sheets. Adding the critical point
and taking the closure shows that `f^{-1}(V_n)` is connected. These
sets are nested nonempty compacta. Consequently

\[
 f^{-1}(E)=\bigcap_n f^{-1}(V_n)
\]

is connected.

Kiwi's Proposition 4.2, pp. 233--234, supplies `q f=Q q` and that
`Q` is a branched cover of degree two. Surjectivity of `q` therefore
gives

\[
 q(f^{-1}(E))=Q^{-1}(q(v)).
\]

The left side is connected; the right side is finite and contains
`q(c_*)`. Thus it is the singleton `{q(c_*)}`. The sum of the local
degrees over this fiber is two, so the local degree at `q(c_*)` is
two.

Finally the proof of Proposition 4.2 constructs disjoint one-sheeted
Jordan preimages whenever the target fiber contains no critical
value of `f`. It follows that every finite critical value of `Q`
is `q(v)`. Its unique inverse just found is `q(c_*)`, so there is
no other finite critical point. QED.

The same statement transports through the fixed straightening. Thus
the induced degree-two topological polynomial `Fbar` on the physical
quotient has its only finite critical point in `q(K_0)`. The marked
union `A` is forward invariant. The arc assertion needed here has the
following elementary proof, so no local-to-global injectivity is assumed.

**Arc lemma.** A continuous path in a dendrite which is locally injective
at every interior parameter is injective on the entire parameter interval.
First suppose local injectivity also holds at its endpoints. Compactness
gives an `epsilon > 0` such that every parameter interval of length less
than `epsilon` lies in an interval on which the path is injective. If
there is a repeated value, the compact set of equal-value parameter pairs
at distance at least `epsilon` has a pair of minimum distance. On the
subinterval between that pair, no other value repeats, by minimality.
Identifying the two endpoints therefore gives an embedded circle in the
dendrite, a contradiction. For local injectivity only in the interior,
apply this result on every compact interior interval to get injectivity
there. If either endpoint repeats an interior value, the subinterval
between them again gives an embedded circle; if the two endpoints agree,
the whole interval does so. All repetitions are excluded. QED.

The restriction of `Fbar` to an arc avoiding its critical point in the
interior satisfies the arc lemma, because the plane branched cover is a
local homeomorphism at every noncritical point. Its image is therefore
the unique arc joining the image endpoints.

For any arc joining two points of `A`, split it at the critical point if
necessary. The image of each resulting subarc is the unique arc between
its image endpoints, which are in `A`. It therefore lies in `S_Kw`.
Since `S_Kw` is the union of arcs connecting `A`,

\[
 \overline F(S_{\rm Kw})\subseteq S_{\rm Kw},
 \qquad F(T_{\rm Kw})\subseteq T_{\rm Kw}.
\tag{5.2}
\]

The critical-point correspondence used here is Lemma 5.1, not a claim
about a separately chosen finite tree.

Thus (5.1) is an actual non-LC physical carrier with the incidence and
forward-invariance properties used in the next section. It is not yet
an identification of the exact native marked carrier.

## 6. Consequence for the stationary predecessor count

Retain the physical inverse-sheet construction in the archived endpoint
note. Its hypotheses and conclusions include

\[
 \Omega_0=\mathfrak L_0,\quad
 \Omega_n=\phi_0^n(\mathfrak L_0),\quad
 F^n:\Omega_n\longrightarrow\Omega_0
 \text{ is a homeomorphism},
\]

and `Omega_n` is a component of `K \ {alpha^n}` with boundary
`{alpha^n}`. Each `alpha^n` has finite orbit and avoids every `K_i`.

Let `T` be any forward-invariant full-hull carrier covered by
Theorem 4.2 simultaneously at `alpha^0,...,alpha^H`. In particular one
may use the physical `T_Kw` of Section 5. Put

\[
 L_0=T\cap\Omega_0,\qquad
 L_n=\phi_0^n(L_0).
\tag{6.1}
\]

Theorem 4.2 proves connectedness of `L_0`; it contains the critical
small Julia set. Thus the first selected inverse component is no longer
ambiguous: it is the entire `phi_0(L_0)`, and it contains the archived
selected predecessor `Q_1`. Inductively these are exactly the
`Q_0`-selected components. Furthermore,

\[
 L_n=F^{-n}(T)\cap\Omega_n.
\tag{6.2}
\]

Indeed `F^n` is a homeomorphism from `Omega_n` to `Omega_0`, so both
sides of (6.2) are its inverse image of `L_0`.

Suppose `L_n intersect T` is nonempty. It is contained in `T intersect
Omega_n`, so Theorem 4.2 yields an entire `K_i subset Omega_n`.
Forward invariance gives `K_i subset T subset F^{-n}(T)`. Equation
(6.2) then gives

\[
 L_n\cap T\ne\varnothing
 \quad\Longrightarrow\quad
 \exists i\;(K_i\subset L_n).
\tag{6.3}
\]

This is the physical marked-incidence implication. It was proved without
matching a selected model sheet, without knowing an independently named
model small Julia continuum, and without local connectivity of `K`.

Now suppose at most `b` cycle components lie in the critical limb and
the cycle period satisfies `P >= q > b`, as in the archived stationary
high-type count. If `L_b` met `T`, (6.3) and
`F(L_j) = L_{j-1}` would place

\[
 K_i,F(K_i),\ldots,F^b(K_i)
\]

inside the critical limb. These are `b+1` distinct cycle components
because `P > b`, a contradiction. Hence

\[
 L_b\cap T=\varnothing.
\tag{6.4}
\]

For `n > b`, a point in `L_n intersect T` would map under `F^{n-b}`
to a point in `L_b intersect T`, again impossible. Thus all the later
selected predecessors through the declared finite horizon also miss `T`.

## 7. Exact native residue and acceptance test

The native source in Section 2.5 says that the non-LC objects are obtained
by lifting the analogous model Hubbard tree. To apply (6.3) to **that
particular carrier**, it is sufficient to establish the following:

1. its projection is monotone onto a dendrite;
2. its complete fibers at the finitely many selected `alpha^n` are
   singletons; and
3. its physical Hubbard carrier is the full inverse image of the hull
   of the images of the actual physical `K_i`.

No global marked homeomorphism with the Kiwi model is necessary for this
incidence conclusion. Nor are model labels for the `Q_n`, the `Omega_n`,
or the individual geometric model `K_i` necessary: the proof works on
the actual images of the physical objects.

If the source projection and lift are explicitly defined using Kiwi's
fiber quotient and (5.1), these items are supplied by Sections 3--5,
and the set-theoretic count is proved on that definition. If an already
fixed source construction uses a different projection or notion of
lift, these items must be verified for it. The phrase “natural
projection” is not a verification.

There is a concrete reason not to infer a global identification solely
from the phrase “rational lamination”: Kiwi notes on pp. 257--258 that
the rational part need not be dense in the full real lamination. The
present one-cut theorem deliberately avoids requiring that unproved
global comparison.

Even after (6.4) holds for the native carrier, the following remain
separate: full-carrier separator geometry, actual incoming proper host,
the selected Wave occurrences, two-sided retained routes, pointwise final
component exit, measurable sublamination realization, and quantitative
pushforward of the exact source widths. In particular (6.4) alone is not
a proof that an arbitrary Wave leaf exits the deepest component.

## 8. Verification and attribution

`verify_cutpoint_pruning.py` checks the discrete tree analog on every
labelled tree with up to six vertices, every nonempty marked subset, and
every unmarked cut vertex. It also checks the triod counterexample when
the singleton-fiber premise is dropped. These checks test the direction
and scope of the combinatorial assertions; the continuum and dynamical
arguments are the written proofs above.

The ingredients from continuum theory and Kiwi are classical. The
contribution claimed here is their explicit application to this archive's
selected physical inverse sheets, the projection-independent one-cut
formulation, and the removal of unnecessary model-label premises from
the N2 incidence route. No novelty claim is made for abstract monotone-map
or dendrite facts.

Prepared with GPT-6 Astra Pro assistance for proof search, source
comparison, and verification code. No independent human specialist review
has been performed in this session.

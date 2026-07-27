# Virtual blocks: quotient obstruction and translation compression

## 1. Result of the proof attempt

The initial Virtual Block Quotient Lemma required a quotient with:

1. universally bounded WAD topology;
2. preservation of every marked access and critical return;
3. uniformly bounded total width distortion.

Requirements 1 and 2 are incompatible when a block has arbitrarily many dynamically
distinct accesses. This is already visible in KKL's source-locked translation model.

The correct replacement is not a bounded marked surface. It is:

- a bounded **active core**;
- arbitrarily long translation corridors retaining all their markings;
- a finite set of interaction types modulo the translation action;
- a relative/amortized error estimate paid for by degeneration or entropy.

The new open target is the Virtual Translation-Compression Lemma in Section 6.

## 2. Marking-cardinality obstruction

Let \((\mathbb D,{\cal I}_N)\) be a disk with \(N\) pairwise disjoint labeled ideal
intervals
\[
{\cal I}_N=(I_0,\ldots,I_{N-1})
\]
in cyclic order.

### Definition 2.1

A map
\[
q:(\mathbb D,{\cal I}_N)\longrightarrow(S,{\cal J})
\]
is **marking-faithful** if:

1. each \(I_j\) maps into one ideal interval \(J(j)\in{\cal J}\);
2. the label \(j\) can be recovered from \(J(j)\);
3. for every \(j\ne k\), the proper-arc classes from \(I_0\) to \(I_j\) and from
   \(I_0\) to \(I_k\) remain distinguishable after applying \(q\).

The recoverability clause is exactly what is needed if different accesses have
different return itineraries.

### Theorem 2.2 (no faithful bounded-marking quotient)

Every marking-faithful quotient satisfies
\[
|{\cal J}|\ge N.
\]
In particular, no universal bound on the number of ideal intervals is possible as
\(N\to\infty\).

**Proof.** If \(J(j)=J(k)\) for \(j\ne k\), then the target marking does not recover
which of \(I_j,I_k\) was used. Moreover the two target proper arcs have the same marked
endpoint \(J(j)\), so the quotient has discarded the distinction required in
Definition 2.1. Thus \(j\mapsto J(j)\) is injective and
\(|{\cal J}|\ge N\). \(\square\)

### Corollary 2.3

If a virtual block retains \(N\) distinct return accesses, connectedness of its hull
does not reduce its marking cardinality. Any bounded-topology claim must either:

- prove that only \(O(1)\) accesses are dynamically distinguishable for the argument;
- encode the remaining accesses equivariantly rather than as individual quotient
  vertices; or
- accept topology-dependent errors and show that they are dominated or amortized.

## 3. The obstruction occurs in the source model

KKL defines an \((n,p)\)-translation marking with
\[
N=2(n+1)p
\]
ideal intervals. The return acts as an index shift by \(2p\) away from the terminal
defect region. Here \(n\) can grow with the length of the near-translation region.

KKL also records that the support of a WAD on \((V,{\cal I})\) can contain as many as
\[
3|\chi(V)|+|{\cal I}|
\]
arcs. Therefore bounded Euler characteristic alone does not make the WAD combinatorics
uniform when the ideal marking is unbounded.

This does not break the KKL proof. Their strategy keeps the long translation marking
and controls it dynamically. The bounded object is the part with non-translation
interaction, not the entire marked surface.

## 4. Translation-orbit compression

Consider a linear translation corridor with interval indices
\[
0,1,\ldots,N-1
\]
and a partial shift
\[
T(i)=i+s
\]
where it is defined. An oriented short interaction is a pair \((i,j)\) with
\(|j-i|\le R\), away from the two defect ends.

### Definition 4.1

Two interactions are translation equivalent if
\[
(i',j')=(i+ks,j+ks)
\]
for some integer \(k\), with all intermediate translates in the corridor.

### Lemma 4.2 (bounded short interaction types)

The number of translation-equivalence classes of oriented interactions with
\(|j-i|\le R\) is at most
\[
s(2R+1).
\]
This bound is independent of \(N\).

**Proof.** Translate the first index until it lies in a fixed residue window
\(\{0,\ldots,s-1\}\), except possibly at a defect end, which is excluded by hypothesis.
The class is then determined by the residue of \(i\) modulo \(s\) and the displacement
\(\delta=j-i\in[-R,R]\). There are at most \(s(2R+1)\) such pairs. \(\square\)

### Corollary 4.3

For at most \(r\) translation corridors with shifts \(s\le s_0\), the number of
interior short-interaction types is at most
\[
r s_0(2R+1),
\]
independent of the lengths of the corridors. The finitely many defect-end interactions
must be added to the active core.

The quotient is thus a quotient of the **interaction groupoid**, not a quotient that
identifies the actual ideal intervals.

## 5. Width of interactions that cannot be compressed

KKL's Translation Marking Theorem states that for an \((n,p)\)-translation marking,
the canonical weight of long arcs obeys
\[
\|W^{\mathrm{long}}\|
\le 2W_{\mathrm{std}}+6N,
\qquad N=2(n+1)p.
\tag{5.1}
\]
The displayed constants are those obtained at the end of the source proof.

### Proposition 5.1 (relative tail control)

Let \(X>0\) be the total degeneration assigned to a transition. If
\[
W_{\mathrm{std}}\le\varepsilon X
\quad\text{and}\quad
N\le\varepsilon X,
\]
then
\[
\|W^{\mathrm{long}}\|\le 8\varepsilon X.
\]

**Proof.** Substitute the two hypotheses into (5.1):
\[
\|W^{\mathrm{long}}\|
\le2\varepsilon X+6\varepsilon X
=8\varepsilon X.
\quad\square
\]

This is the correct form of “the unbounded topology is harmless” in a highly
degenerate transition. The error is not universally \(O(1)\); it is small relative to
the width being amplified.

### Proposition 5.2 (absolute summability is too strong for this mechanism)

The Translation Marking Theorem alone does not give an error bound independent of
\(N\).

**Proof.** Its right side contains \(6N\), and the theorem permits
\(N=2(n+1)p\) with unbounded \(n\). No \(N\)-independent estimate follows without an
additional hypothesis relating \(N\) to the total degeneration or canceling errors
between adjacent scales. \(\square\)

Consequently the earlier requirement
\[
\sum e_j\le E_0
\]
must not be imposed as the only admissible error mechanism. The sufficient alternatives
are:

\[
\sum e_j\le\delta D_n+C,
\qquad 0<\delta<\lambda-1,
\tag{5.2}
\]

or an entropy-amortized inequality
\[
\sum e_j\le cE(B)D_n+C
\tag{5.3}
\]
whose coefficient is smaller than the Value-contraction gain.

## 6. Corrected open lemma

### Virtual Translation-Compression Lemma (`OPEN`)

There exist universal
\[
r_0,\ s_0,\ A_0<\infty
\]
and a canonical accelerated checkpoint rule such that the marked complement of every
virtual-molecule block decomposes into:

\[
X_B=X_B^{\mathrm{act}}\cup
\bigcup_{\nu=1}^{r_B}T_{B,\nu},
\qquad r_B\le r_0,
\]

with the following properties.

1. **Bounded active core.**
   \(X_B^{\mathrm{act}}\) has at most \(A_0\) ideal vertices, degree-\(>1\) branches,
   base-cycle defects, and critical-return accesses.
2. **Faithful corridors.**
   Every \(T_{B,\nu}\) retains all of its ideal intervals and all return labels; none are
   identified merely to force bounded topology.
3. **Accelerated translation.**
   Away from the active core, the first-return correspondence acts on each corridor as
   a partial shift of size at most \(s_0\). Continued-fraction or molecule sublevels are
   accelerated until this bounded-step form holds.
4. **Bounded interaction complexity.**
   For every fixed localization radius \(R\), the short interactions modulo translation
   have at most
   \[
   r_0s_0(2R+1)+O(A_0R)
   \]
   types.
5. **Long-tail estimate.**
   The total weight of nonlocalizable or long interactions satisfies a relative or
   entropy-amortized estimate of the form (5.2) or (5.3), uniformly in block length,
   periods, and rotation numbers.
6. **Orbit completeness.**
   Every branch used by Wave, Wanderers, covering, or Value either lies in the active
   core or is represented by its full labeled translation orbit in a corridor.
7. **Interface functoriality.**
   The active/corridor decomposition transports through the adjacent pseudo-Siegel and
   puzzle charts without creating more than \(O(1)\) new active defects.

## 7. Fullification and prime-end realization

### Lemma 7.1 (fullification preserves genuine polynomial invariance)

Let \(K\subset\mathbb C\) be a compact connected set and let
\(\operatorname{Fill}(K)\) be \(K\) together with all bounded components of
\(\mathbb C\setminus K\). Then \(\operatorname{Fill}(K)\) is a full continuum.
If \(P\) is a polynomial and \(P(K)\subset K\), then
\[
P(\operatorname{Fill}(K))\subset\operatorname{Fill}(K).
\]

**Proof.** In one complex dimension, \(\operatorname{Fill}(K)\) is the polynomially
convex hull
\[
\widehat K=\{z:|q(z)|\le\sup_K|q|\text{ for every polynomial }q\}.
\]
It is compact, connected, and full. If \(z\in\widehat K\), then for every polynomial
\(q\),
\[
|q(P(z))|
\le\sup_{w\in K}|q(P(w))|
\le\sup_{u\in K}|q(u)|,
\]
where the first inequality applies the definition of \(\widehat K\) to the polynomial
\(q\circ P\), and the second uses \(P(K)\subset K\). Hence
\(P(z)\in\widehat K\). \(\square\)

The lemma gives a canonical full hull whenever the proposed connected hull is genuinely
forward invariant. It does not automatically apply to a partially invariant hull:
the inclusion \(P(K)\subset K\) must hold for the entire set being filled, not only for
selected return pieces.

### Lemma 7.2 (critical-value pullback)

Let \(P\) be a polynomial of degree \(d\ge2\), and let \(H\subset\mathbb C\) be a full
continuum containing every finite critical value of \(P\). Then

\[
H'=P^{-1}(H)
\]

is a full continuum and

\[
P:\widehat{\mathbb C}\setminus H'
\longrightarrow
\widehat{\mathbb C}\setminus H
\]

is a proper holomorphic map of degree \(d\).

**Proof.** Put \(\Omega=\widehat{\mathbb C}\setminus H\). Since \(H\) is full and
connected, \(\Omega\) is simply connected and contains \(\infty\). The restriction
\[
P:P^{-1}(\Omega)\to\Omega
\]
has no finite critical values. Let \(U\) be the component of \(P^{-1}(\Omega)\)
containing \(\infty\). The local degree at \(\infty\) is \(d\), so the restriction
\(P:U\to\Omega\) already has the full degree \(d\). Hence there can be no other
component of \(P^{-1}(\Omega)\).

Remove \(\infty\) from both domains. The resulting map is a connected degree-\(d\)
unbranched covering of the punctured simply connected domain
\(\Omega\setminus\{\infty\}\). Such a cover is a punctured disk; restoring \(\infty\)
shows that \(U=P^{-1}(\Omega)\) is simply connected. Therefore its complement
\(H'\) is connected and full. Properness and degree \(d\) follow from the corresponding
properties of the polynomial. \(\square\)

### Corollary 7.3 (quadratic return criterion)

For \(f_c(z)=z^2+c\), all finite critical values of \(f_c^q\) belong to
\[
\{f_c^j(0):1\le j\le q\}.
\]
Consequently, if a full virtual hull \(H\) contains this orbit segment, then
\((f_c^q)^{-1}(H)\) is a full continuum and \(f_c^q\) acts as a proper degree-\(2^q\)
map between the two hull complements.

**Proof.** A finite critical point of \(f_c^q\) reaches \(0\) after some
\(0\le k<q\) iterates. Its image under \(f_c^q\) is \(f_c^{q-k}(0)\), which is in the
displayed orbit segment. Apply Lemma 7.2 to \(P=f_c^q\). \(\square\)

The virtual hull need not be locally connected, so its Euclidean boundary is not a
legitimate substitute for an ideal marking. For a nondegenerate full hull—equivalently
here, one whose complement is hyperbolic—the complement nevertheless has a canonical
prime-end circle.

### Lemma 7.4 (prime-end return model)

Let \(H',H\subset\mathbb C\) be full continua such that
\[
\Omega'=\widehat{\mathbb C}\setminus H',
\qquad
\Omega=\widehat{\mathbb C}\setminus H
\]
are hyperbolic domains containing infinity. Suppose
\[
g:\Omega'\longrightarrow\Omega
\]
is a proper holomorphic map of degree \(d<\infty\). Then:

1. \(\Omega'\) and \(\Omega\) have prime-end compactifications homeomorphic to closed
   disks;
2. \(g\) extends continuously to their prime-end compactifications;
3. on the prime-end circles, the extension is an orientation-preserving covering of
   degree \(d\);
4. if \(d=1\), it is a circle homeomorphism and transports every labeled ideal interval
   without identifying it.

**Proof.** A full planar continuum has connected complement, so its complement on the
Riemann sphere is simply connected. Choose Riemann maps
\[
\phi':\Omega'\to\mathbb D,\qquad \phi:\Omega\to\mathbb D.
\]
Prime-end compactification is defined so that these maps extend to homeomorphisms with
\(\overline{\mathbb D}\). The conjugate
\[
B=\phi\circ g\circ(\phi')^{-1}:\mathbb D\to\mathbb D
\]
is a proper holomorphic map of degree \(d\), hence a finite Blaschke product of degree
\(d\). A finite Blaschke product extends across the unit circle and restricts there to
an orientation-preserving degree-\(d\) covering. Conjugating back proves the claims.
\(\square\)

### Corollary 7.5

If each declared virtual return restricts to a proper map between complements of
nondegenerate full pullback hulls and those complements are hyperbolic, then all return
accesses and their cyclic order can be represented by ideal intervals on prime-end
circles without assuming local connectivity of the virtual hulls.

### Proposition 7.6 (global-return degree obstruction)

The global complement return in Corollary 7.3 cannot itself serve as a uniformly
bounded-degree virtual ql return when \(q\) is unbounded. If the hulls are additionally
nondegenerate and their complements hyperbolic, the same obstruction is visible on
their prime-end circles.

**Proof.** Corollary 7.3 gives an ordinary proper map of degree \(2^q\). Degree is
invariant under conjugacy of proper maps, so it cannot be reduced to \(2\) or another
universal bound by changing coordinates. Under the additional hyperbolic-complement
hypotheses, Lemma 7.4 identifies the same \(2^q\) as the degree of the prime-end circle
covering. \(\square\)

Therefore the correct object is a componentwise factorization
\[
\Omega_0
\xleftarrow{\,f_0\,}\Omega_1
\xleftarrow{\,f_1\,}\cdots
\xleftarrow{\,f_{q-1}\,}\Omega_q
\]
along the prescribed return itinerary, where:

- exactly one selected step has degree \(2\);
- every other selected step is a conformal isomorphism onto its image;
- intermediate critical values and access labels are retained;
- the composition represents the quadratic-like first return, while discarded global
  preimage components never enter its Wave/Wanderers chains.

Constructing this factorization with full hulls and uniform corridor geometry is the
**Selected Pullback Factorization Gap**. It is stronger than merely proving that the
global polynomial iterate is proper.

### Lemma 7.7 (degree-two factorization)

Suppose a quadratic-like return \(G\) of degree \(2\) has already been represented as a
composition of proper holomorphic maps between connected domains,
\[
G=g_{q-1}\circ\cdots\circ g_0.
\]
Then exactly one factor has degree \(2\), every other factor has degree \(1\), and every
degree-one factor is a conformal isomorphism.

**Proof.** Degrees of proper holomorphic maps are positive integers and multiply under
composition:
\[
2=\deg G=\prod_{j=0}^{q-1}\deg g_j.
\]
The only factorization of the prime integer \(2\) into positive integers has one factor
equal to \(2\) and all others equal to \(1\). A proper degree-one holomorphic map is
biholomorphic. \(\square\)

Thus the missing content is the existence and geometric control of the connected
intermediate domains, not an additional degree estimate.

### Lemma 7.8 (quadratic pullback dichotomy)

Let \(f_c(z)=z^2+c\), and let \(H\subset\mathbb C\) be a nondegenerate full continuum.

1. If \(c\notin H\), then
   \[
   f_c^{-1}(H)=H^+\sqcup H^-
   \]
   is the disjoint union of two full continua. Each restriction
   \(f_c:H^\pm\to H\) extends to a conformal isomorphism between neighborhoods.
2. If \(c\in H\), then \(f_c^{-1}(H)\) is a full continuum and the pullback has degree
   \(2\).

**Proof.** A nondegenerate full continuum has a nested basis of simply connected Jordan
neighborhoods. If \(c\notin H\), choose such a basis \(V_m\searrow H\) with
\(c\notin\overline V_m\). Since \(V_m\) is simply connected and contains no critical
value, \(f_c^{-1}(V_m)\) has two Jordan components, each mapped conformally onto
\(V_m\). Label the nested components consistently. Their intersections are disjoint
full continua \(H^\pm\), and together they equal \(f_c^{-1}(H)\). The conformal
extensions are supplied by any sufficiently deep \(V_m\).

If \(c\in H\), apply Lemma 7.2 to the quadratic polynomial. \(\square\)

### Corollary 7.9 (selected full-hull factorization)

Let \(H_q\) be a nondegenerate full continuum and fix a length-\(q\) inverse itinerary.
Define
\(H_j\) inductively backward: if \(c\notin H_{j+1}\), take the component of
\(f_c^{-1}(H_{j+1})\) selected by the itinerary; if \(c\in H_{j+1}\), take the full
preimage. If exactly one of the target hulls \(H_{j+1}\) contains \(c\), then suitable
neighborhood restrictions give a proper factorization of total degree \(2\), with one
quadratic factor and all other factors conformal.

**Proof.** Lemma 7.8 supplies the selected full pullback continua and the local degree
at each step. We adapt the control-neighborhood construction of Lemma 10.1 in
`finite_horizon_inflation.md`.

Choose a Jordan control neighborhood \(C_0\) of \(H_0\). Inductively choose a Jordan
neighborhood \(C_{j+1}\) of \(H_{j+1}\) so small that its selected pullback component
has closure in \(C_j\); when \(c\notin H_{j+1}\), also require
\(\overline C_{j+1}\cap\{c\}=\varnothing\). Now choose one terminal Jordan disk
\(V_q\Subset C_q\) containing \(H_q\), with boundary avoiding \(c\), and define
\(V_j\) recursively as the selected component of \(f_c^{-1}(V_{j+1})\).
The control-neighborhood choices give \(H_j\Subset V_j\Subset C_j\) at every stage.
Each map
\[
  f_c:V_j\longrightarrow V_{j+1}
\]
is proper, and these maps are genuinely composable. Exactly the declared critical
target disk contains \(c\), giving one degree-two stage; every other target disk
avoids \(c\), giving a conformal stage. Their degrees multiply to two. \(\square\)

This closes the topological degree/fullness part of the Selected Pullback Factorization
Gap, provided one can choose an endpoint hull and itinerary for which the resulting
\(H_j\) coincide with, or uniformly control, the prescribed virtual Julia sets. It does
not give uniform moduli, corridor geometry, or local saturation.

The stagewise construction is sufficient but not logically necessary. The alternative
used by \(\psi\)-ql renormalization is to retain a larger global filled set and recover
the degree-two return by fiber products and subsurface localization. Proposition 7.6
rules out only using the unlocalized global complement map itself.

Lemmas 7.2--7.4 close the pullback fullness, properness, and ideal-boundary realization
whenever the target hull contains the entire critical-value segment of the declared
return. They do not prove:

- that the connected hull proposed by D25 is full;
- that the prescribed “appropriate number” of returns always contains every critical
  value of each iterate used later in Wave/Wanderers;
- that the dynamically relevant restricted branches coincide with the global pullback
  components supplied by Lemma 7.2;
- that the global degree \(2^q\) can be replaced by the selected one-critical-step
  factorization above;
- that noncritical inverse branches persist as conformal isomorphisms for the whole
  declared corridor;
- that their prime-end action is geometrically near a translation rather than merely
  topologically conjugate to a circle homeomorphism.

## 8. The pseudo-quadratic-like inflation blueprint

KKL's \(\psi\)-ql category is designed to separate a bounded-degree branched covering
from the immersion that records how its domain sits in the ambient dynamics. A
\(\psi\)-ql map
\[
F=(f,\iota):(\mathcal U',K')\rightrightarrows(\mathcal U,K)
\]
has:

- a degree-two branched covering \(f:\mathcal U'\to\mathcal U\);
- a holomorphic immersion \(\iota:\mathcal U'\to\mathcal U\);
- compact connected full sets satisfying
  \[
  f^{-1}(K)=\iota^{-1}(K)=K'.
  \]

Its iterates are formed by fiber products rather than by using the global
degree-\(2^q\) polynomial iterate directly. This is exactly the categorical repair
required by Proposition 7.6.

DL25 supplies a parallel inflation blueprint. Starting with a forward-invariant set
\(\Upsilon\) containing the postcritical set, it uses the partial self-covering
\[
(f,\hookrightarrow):
\widehat{\mathbb C}\setminus f^{-1}(\Upsilon)
\rightrightarrows
\widehat{\mathbb C}\setminus\Upsilon
\]
and a local-saturation hypothesis to inflate a local degree-two prerenormalization into
a \(\psi^\bullet\)-ql correspondence. DL25 also notes that multiple-component
correspondences are natural when a first return creates many critical points.

### Proposition 8.1 (source-locked categorical reduction)

If a virtual block can be promoted to a genuine \(\psi\)-ql map satisfying the
preceding full-set identities, then:

1. its fiber-product iterations give canonical bounded-degree return surfaces;
2. a prime primitive small filled Julia set has a canonical \(\psi\)-ql
   renormalization by localization;
3. when its \(\psi\)-ql width is bounded, Kahn's induced-map theorem supplies a genuine
   quadratic-like restriction with a positive modulus bound depending only on that
   width.

**Justification.** These are the \(\psi\)-ql iteration, canonical renormalization, and
induced quadratic-like-map theorems recalled in KKL26. \(\square\)

### Selected fiber-product telescope problem (`OPEN`)

Suppose that, for indices \(j\in\mathbb Z/q\mathbb Z\), one has connected conformal
surfaces and maps
\[
F_j=(f_j,\iota_j):
(\mathcal U_j,K'_j)
\rightrightarrows
(\mathcal V_{j+1},K_{j+1})
\quad\text{and}\quad
\iota_j:\mathcal U_j\to\mathcal V_j,
\]
with the required full-set identities and compatible labels. Assume each \(f_j\) is
proper, exactly one has degree \(2\), and all others have degree \(1\). Then the
disjoint unions formally define componentwise maps
\[
\mathcal U=\bigsqcup_j\mathcal U_j,
\qquad
\mathcal V=\bigsqcup_j\mathcal V_j
\]
and the componentwise maps \(f=\bigsqcup f_j\),
\(\iota=\bigsqcup\iota_j\). This formal disjoint-union correspondence does **not**
yet have a proved degree-two fiber-product return.

The missing theorem must:

1. specify a connected component of every successive fiber product
   \(f_j(z)=\iota_{j+1}(w)\);
2. prove component routing closes after \(q\) stages and excludes extra sheets;
3. prove the relevant base changes and projections are proper and preserve the stated
   stage degrees;
4. verify every selected iterated component is in the declared conformal category;
5. preserve all core and marking labels under the selected projections.

Only after these properties are proved may one identify the selected fiber-product
return with an ordinary composition and multiply degrees. Properness of the \(f_j\)
and vague label compatibility alone do not suffice: fiber products can split, and
their projections can acquire multiplicity. The multiple-component framework remains
a source-guided blueprint, not a proved assembly theorem.

### Lemma 8.3 (canonical factorization of a genuine ql return)

Let
\[
G=f_c^q:U_0\longrightarrow V_q
\]
be a quadratic-like restriction of degree \(2\). For \(0\le j\le q\), let \(V_j\) be
the component of
\[
f_c^{-(q-j)}(V_q)
\]
containing \(f_c^j(U_0)\). Then:

1. \(V_0=U_0\);
2. every restriction
   \[
   f_c:V_j\to V_{j+1}
   \]
   is proper;
3. exactly one restriction has degree \(2\), and all others are conformal
   isomorphisms;
4. the composition of the restrictions is \(G\).

**Proof.** Properness of \(G:U_0\to V_q\) implies that \(U_0\) is a component of
\(f_c^{-q}(V_q)\). Indeed, if the containing component extended across a point of
\(\partial U_0\), a sequence in \(U_0\) approaching that point would have images in a
compact subset of \(V_q\), contradicting properness. Hence \(V_0=U_0\).

Inductively, \(V_j\) is the component of \(f_c^{-1}(V_{j+1})\) containing
\(f_c^j(U_0)\). Since a polynomial is proper, its restriction to a preimage component
is proper and maps that component onto \(V_{j+1}\). The degrees of these restrictions
multiply to \(\deg G=2\), so Lemma 7.7 gives one degree-two factor and conformal
degree-one factors. Their composition is the original restriction by construction.
\(\square\)

Thus selected finite-horizon domains already exist at every genuine ql checkpoint.
The virtual problem is to enlarge/localize this factorization so that the intermediate
virtual hulls and all required markings lie in controlled \(\psi\)-ql surfaces, with
relative width loss independent of \(q\).

The virtual setting does not yet meet the premise. D25 retains only a finite part of the
postcritical set and asks only for partial invariance. A finite-horizon set need not
extend to the globally forward-invariant \(\Upsilon\) used by DL25 without swallowing
the geometric scale one is trying to study.

### Finite-Horizon Analytic Inflation Theorem (`OPEN`)

Given a virtual block with stopping time \(q\), construct correspondences
\[
F_j=(f_j,\iota_j):
(\mathcal U_{j+1},H_{j+1})
\rightrightarrows
(\mathcal U_j,H_j),
\qquad 0\le j<q,
\]
such that:

1. \(H_j\) is a full continuum carrying the required virtual Julia sets and orbit data;
   the construction either distributes this data stagewise or retains it globally and
   supplies a subsurface localization that selects the quadratic return;
2. the full-set identities
   \[
   f_j^{-1}(H_j)=\iota_j^{-1}(H_j)=H_{j+1}
   \]
   hold on the selected components;
3. the fiber-product composition has degree \(2\), hence one quadratic factor and all
   other factors conformal by Lemma 7.7;
4. every pullback used by Wave/Wanderers is defined before the finite horizon;
5. no global forward-invariant enlargement is assumed;
6. the immersion and localization losses obey the relative/amortized width budget.

This lemma is the construction-theoretic core of the Virtual
Translation-Compression Lemma. It replaces both the unsafe global degree-\(2^q\) return
and an unjustified assumption of a globally invariant virtual postcritical set.

The finite-horizon audit in `finite_horizon_inflation.md` refines this statement in
three ways.

1. The stage markings must satisfy
   \[
     f(\Upsilon_j)\subset\Upsilon_{j+1}
   \]
   even for the complement inclusion to exist.
2. Relative-cover lifting, core properness, and admissibility of every curve pullback
   are separate conditions; none follows from fullness alone.
3. Topological inflation cannot imply Item 6. The rescaled family
   \(z^2:\mathbb D_R\to\mathbb D_{R^2}\) has constant topological data and arbitrarily
   varying inverse modulus.

Accordingly, the open lemma is now named the **Finite-Horizon Analytic Inflation
Theorem**. Its exact current statement and the proved formal prerequisites are in
`finite_horizon_inflation.md`, Sections 3–9.

## 9. KKL trichotomy transfer gate

### Proposition 9.1 (source-locked occupancy trichotomy)

For every \(B,M\ge1\), there is \(A(B,M)<\infty\) with the following property.
Let \(F\) already satisfy KKL's definitions of a periodically repelling, prime
primitively renormalizable \(\psi\)-ql map, with its full cycle \({\cal K}\) of small
filled Julia sets, Hubbard tree \({\cal T}\), canonical WAD, and canonical
renormalization. If every limb contains at most \(B\) components of \({\cal K}\) and
\[
  \mathbb W({\cal R}F)\ge A(B,M),
\]
then KKL Proposition 3.7 gives at least one of:

1. \(F\) has \(M\)-amplification;
2. \(\mathcal U\setminus{\cal K}\) is \(M\)-tame in KKL's sense;
3. \(\mathcal U\setminus{\cal T}\) has \(M\)-wide controllable waves in KKL's sense.

**Justification.** KKL Remark 4.14 says that the only part of parabolic boundedness
used in Proposition 3.7 is the per-limb component bound. The large-width premise and
the requested factor \(M\) remain part of that proposition. The remark does not
license KKL Propositions 3.8 or 3.9 under occupancy alone. \(\square\)

This is not yet a virtual-block theorem. A connected virtual hull is only partially
invariant and need not be the filled Julia set of a periodically repelling
\(\psi\)-ql map. To invoke Proposition 9.1, one must construct a partial-cover analogue
of the canonical lamination and verify that the proof uses no iterate beyond the marked
return time.

The source audit `kkl_virtual_occupancy_source_audit.md` shows that a selected
component count is not the direct virtual interface. KKL first uses its finite
Hubbard tree to convert component occupancy into
\[
  |{\cal L}_j|\le6B
\]
for the complete ideal multi-interval of each limb. Fjords, dams, omitted Cantor
components, or additional prime-end accesses can violate that marking bound even
when the selected component count is small.

The transfer gate therefore splits into three independent problems:

1. **Virtual Section-4 Interface:** construct access-complete marked complements and
   prove the limb-interval, WAD/width, restriction-multiplicity, flux, and wave
   estimates needed for the static Proposition 3.7 split.
2. **Virtual Tame Full-Return Lemma:** on the tame branch, construct the full-period
   selected return, localized cover, bounded selected degree, literal or controlled
   corridor transition, WAD domination, Wanderers tail, and Value contraction.
3. **Virtual Long-Iterate Wave Lemma:** on the wave branch, construct the compatible
   pulled markings, proper/end-proper interval dynamics, controlled selected degree,
   and itinerary-complete transport through the \(O_B(q)\) stopping horizon.

Only the first problem is the content suggested by Remark 4.14. The second and third
use the additional parabolic translation and critical-defect hypotheses throughout
KKL Sections 5 and 6; they may not be inferred from occupancy.

## 10. What is proved and what remains open

Proved here:

- a faithful quotient cannot have bounded marking cardinality;
- short translation interactions have bounded orbit-type complexity;
- KKL's long-arc estimate yields relative tail control when degeneration dominates
  marking complexity;
- the source theorem alone cannot yield absolute \(O(1)\) error for unbounded markings.
- proper returns between complements of nondegenerate full hulls act canonically on
  prime-end circles when those complements are hyperbolic.

Still open:

- constructing the active/corridor decomposition for Dudko's virtual Julia sets;
- proving fullness and properness for the declared virtual pullback hulls;
- proving the Finite-Horizon Analytic Inflation Theorem, including local saturation,
  orbit admissibility, and a separate quantitative localization estimate;
- proving a universal bound on the number of corridors and accelerated shift sizes;
- showing that critical returns outside the active core really are translation
  equivalent;
- proving the relative/amortized error across virtual, neutral, and puzzle interfaces.

## 11. Consequence for the unified functional

The state must be enlarged from one scalar \(D^\#\) to

\[
\mathscr D_B=
\left(
D_B^{\mathrm{act}},
W_{B,1}^{\mathrm{std}},\ldots,W_{B,r_B}^{\mathrm{std}},
{\cal O}_B,
{\cal E}_B
\right),
\]

where \({\cal O}_B\) is the finite orbit-type WAD and \({\cal E}_B\) is the accumulated
error budget. A scalar Lyapunov quantity must be recovered by a positive homogeneous
calibration. After a verified balance/bottleneck-chamber reduction, it may take the
linear form

\[
L_B=D_B^{\mathrm{act}}
+a\sum_\nu W_{B,\nu}^{\mathrm{std}}
+b\,\operatorname{val}({\cal O}_B)
-{\cal E}_B,
\]

The constants \(a,b\), positivity of \(L_B\), and the balance reduction are part of the
future transition proof. Without balance, harmonic series transport requires a
nonlinear bottleneck/min calibration as shown in `corridor_network_calibration.md`.
The vector state is the invariant required before a valid scalar can be defined.

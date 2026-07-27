# Gate N2: selected-predecessor endpoint reduction

Date: 2026-07-27  
Status: canonical finite-horizon predecessor selection, terminal
inverse-sheet geometry without local connectivity, finite-tree
pruning, dynamic continuum saturation, locally connected physical
marked incidence, model marked incidence, the monotone full-lift
conditional criterion, critical-limb orbit distinctness, and the
conditional line-1598 count are proved; the actual non-locally-
connected full-lift identification, separator/access realization, and
proof-used occurrence compatibility remain open

## 1. Purpose and nonclaim

This note isolates the first source-facing geometric predicate needed
before the incoming occurrence-window anchor can be constructed.  It
audits the inference at KKL line 1598

\[
  \bigl(\text{at most \(b\) small-Julia components in }\mathfrak L_0\bigr)
  \quad\Longrightarrow\quad
  L_0^b\cap T=\varnothing .
\tag{1.1}
\]

Three parts of the intended argument are valid:

1. a terminal component of a finite tree that is the hull of marked
   vertices must contain a marked vertex;
2. in the rotation-\(1/q\) primitive cycle, the component period is at
   least \(q\), so the first \(b+1\) iterates are distinct when \(q>b\);
3. once a full small-Julia component is known to lie in \(L_0^b\),
   the selected predecessor relation produces \(b+1\) distinct cycle
   components in \(\mathfrak L_0\), a contradiction.

What is not supplied by the locked source is the minimal implication

\[
 \mathrm{MCI}_b:\qquad
 L_0^b\cap T\ne\varnothing
 \Longrightarrow
 \exists K\in\operatorname{Comp}\mathcal K
 \text{ with }K\cap L_0^b\ne\varnothing.
\tag{1.2}
\]

A nonempty edge-only intersection does not provide that bridge.  The
terminal-side construction below is one sufficient route to
\(\mathrm{MCI}_b\), while the selected-preimage dynamics upgrades
contact with \(K\) to containment of all of \(K\).  The terminal route
is not a logically necessary form of every possible repair.

Accordingly this note does not promote Gate N2, the stationary repair,
VAAPC-I, UPTCR, or MLC.

## 2. Source lock

The source is

```text
.tmp_wave_audit/waves-with-Misha.tex
SHA-256 AD4C774806D9902AA54FA31C56AD6146D8034946F19CC5E9CEC3C51A3F94FDD5
```

For the non-locally-connected lift wording, the secondary locked
primary manuscript is

```text
.tmp_wave_audit/dl23/Feigen.tex
SHA-256 EB8C50CC51039A82317CF1951B1E333F23DF100773F8AD0DF0586AC7CD465DDF
```

The exact clauses used are:

- lines 478--487: the primitive period-\(P\) cycle
  \(\mathcal K=\bigcup_{j=0}^{P-1}K_j\), with pairwise-disjoint
  components;
- lines 497--504: the rotation-\(1/q\) limb dynamics, the critical limb,
  and the critical value in \(\mathfrak L_1\);
- lines 514--529: \(T\) is the least connected carrier of
  \(\mathcal K\), and its components and edges define a finite
  combinatorial tree;
- lines 661--667: every limb contains at most \(b\) components of
  \(\mathcal K\);
- lines 698--715: the proof is in the high-type regime, so its
  threshold may and must include the explicit inequality \(q>b\);
- lines 1597--1598: the printed argument intends predecessor sets
  \(L_0^n\) in \(\mathfrak L_0\), with
  \[
     K\subset L_0^n,\ K\in\operatorname{Comp}\mathcal K
     \quad\Longrightarrow\quad
     F(K)\subset L_0^{n-1}.
  \tag{2.1}
  \]

The paragraph does not separately define its initial \(K_0\), justify
the definite article "the" for every inverse component, or keep the
\(\alpha^n/\alpha_n\) convention stable.  Put

\[
 H=b+2.
\tag{2.2}
\]

We reserve the notation below for the canonical complete-horizon
selection certificate

\[
 \mathrm{SC}_H=
 \left(
 L_0^0,L_0^1,\ldots,L_0^H;\
 w_0,w_1,\ldots,w_H
 \right),
\tag{2.3}
\]

where \(L_0^0=T\cap\mathfrak L_0\), and, for \(1\le n\le H\),
\(L_0^n\) is one recorded connected component of the full set
\(F^{-1}(L_0^{n-1})\), contained in \(\mathfrak L_0\), with
\(F(L_0^n)\subset L_0^{n-1}\).
The first component is the \(Q_0\)-selected component constructed in
Lemma 2.2 below.  Lemma 2.1 first constructs only a preliminary chain,
denoted \(\mathrm{PSC}_H\), of the same tuple type; it is not yet
\(\mathrm{SC}_H\).
Here

\[
 w_0=(),\qquad
 w_n=(L_0^1,\ldots,L_0^n),\qquad
 \operatorname{par}(w_n)=w_{n-1},
\tag{2.4}
\]

for \(1\le n\le H\), is an actual-component address, not a symbolic label: two addresses
are equal exactly when their ordered actual connected subsets agree.
Separately, write

\[
 \mathrm{APC}_H=
 \left(
 \alpha^0=\alpha_F,\alpha^1,\ldots,\alpha^H;\
 v_0,v_1,\ldots,v_H
 \right)
\tag{2.5}
\]

for a selected fixed-point predecessor chain satisfying
\(F(\alpha^n)=\alpha^{n-1}\), where
\(v_0=()\), \(v_n=(\alpha^1,\ldots,\alpha^n)\), and, for
\(1\le n\le H\),
\(\operatorname{par}(v_n)=v_{n-1}\).  All inverse sets here are taken inside
\(K(F)\) for the induced map \(F=f\circ\iota^{-1}\) of source line
457, matching the use at line 1597.

### Lemma 2.1 (critical-limb inverse branch and horizon selection)

For a rotation-\(1/q\) map with \(q\ge2\), put

\[
 D_0=F^{-1}(\mathfrak L_0)\cap\mathfrak L_0.
\tag{2.6}
\]

Then \(F:D_0\to\mathfrak L_0\) is a homeomorphism.  Consequently a
preliminary component chain \(\mathrm{PSC}_H\), and the point chain
\(\mathrm{APC}_H\), exist through every prescribed finite horizon
\(H\).  No canonical first component is asserted for
\(\mathrm{PSC}_H\) if
\(F^{-1}(L_0^0)\cap\mathfrak L_0\) is disconnected.

#### Proof

The source states that
\(F:\mathfrak L_{q-1}\to\mathfrak L_0\) is a homeomorphism, that the
critical value lies in \(\mathfrak L_1\), that
\(F(\mathfrak L_0)=K(F)\), and that \(F:K(F)\to K(F)\) is a
degree-two branched cover.  Thus each
\(y\in\mathfrak L_0\) has one preimage in
\(\mathfrak L_{q-1}\), is not the critical value, and has at least one
preimage in \(\mathfrak L_0\).  Degree two leaves exactly one
preimage in \(\mathfrak L_0\).  That preimage is noncritical.
Because there are finitely many limbs, \(\mathfrak L_0\) is open in
\(K(F)\setminus\{\alpha_F\}\); \(D_0\) is its relative inverse in the
noncritical locus.  Thus the ambient local homeomorphism restricts to
a local homeomorphism \(F:D_0\to\mathfrak L_0\).  It is bijective by
the preimage count, hence open, and therefore a homeomorphism.  Denote
its inverse by \(\phi_0\).

The set \(L_0^0\) is nonempty because it contains the critical point
in the critical small-Julia component.  Choose one connected
component of \(\phi_0(L_0^0)\) and call it \(L_0^1\).  The full
inverse \(F^{-1}(L_0^0)\) omits \(\alpha_F\), so a connected component
cannot cross between two limbs; hence \(L_0^1\) is a component of the
full inverse set.  Once \(L_0^{n-1}\) is connected, put

\[
 L_0^n=\phi_0(L_0^{n-1}).
\tag{2.7}
\]

It is the unique full inverse component contained in
\(\mathfrak L_0\), and \(F(L_0^n)=L_0^{n-1}\) for \(n\ge2\).
At the first step, \(F(L_0^1)\) is the selected connected component
of \(L_0^0\), so only \(F(L_0^1)\subset L_0^0\) is asserted unless
connectedness of \(L_0^0\) is separately proved.  Iteration constructs
\(\mathrm{PSC}_H\), and the successive actual components give the
address \(w_n\).

For the point chain, \(F(\mathfrak L_0)=K(F)\) supplies a preimage
\(\alpha^1\in\mathfrak L_0\) of \(\alpha_F\).  It is unique: the
fixed point \(\alpha_F\) is the other preimage, and \(\alpha_F\) is
not the critical value.  For \(n\ge2\), define
\(\alpha^n=\phi_0(\alpha^{n-1})\).  This constructs
\(\mathrm{APC}_H\) and the address \(v_n\). \(\square\)

### Lemma 2.2 (canonical small-Julia predecessor selection)

Let \(Q_0\) be the critical member of the primitive small-Julia cycle
and define

\[
 Q_n=\phi_0(Q_{n-1}),\qquad 1\le n\le H.
\tag{2.8}
\]

Then every \(Q_n\) is a whole connected component of
\(F^{-1}(Q_{n-1})\), the restriction
\(F:Q_n\to Q_{n-1}\) is a homeomorphism, and there is a unique
\(Q_0\)-selected certificate \(\mathrm{SC}_H\) satisfying

\[
 Q_n\subset L_0^n,\qquad 0\le n\le H.
\tag{2.9}
\]

#### Proof

The continuum \(Q_0\) contains the critical point, avoids
\(\alpha_F\), and belongs to the cycle contained in \(T\).  Hence

\[
 Q_0\subset T\cap\mathfrak L_0=L_0^0.
\tag{2.10}
\]

Assume \(Q_{n-1}\subset\mathfrak L_0\).  The inverse-branch
homeomorphism makes \(Q_n=\phi_0(Q_{n-1})\) compact and connected,
places it in \(\mathfrak L_0\), and maps it homeomorphically onto
\(Q_{n-1}\).  Since the target omits \(\alpha_F\), its full inverse
omits \(\alpha_F\); a connected full-inverse component cannot cross
between distinct limbs.  Inside \(\mathfrak L_0\), uniqueness of
\(\phi_0\) shows that the component containing \(Q_n\) is exactly
\(Q_n\).  This proves the first assertion by induction.

Now \(Q_1\subset\phi_0(L_0^0)\).  The connected set \(Q_1\) lies in a
unique connected component of that inverse; select this component as
\(L_0^1\).  Having selected it, set
\(L_0^n=\phi_0(L_0^{n-1})\) for \(n\ge2\).  Induction gives
\(Q_n\subset L_0^n\), and uniqueness at the first component containing
\(Q_1\), followed by uniqueness of the critical inverse branch, gives
the unique \(Q_0\)-selected certificate.  From this point onward,
\(\mathrm{SC}_H\) means only this canonical chain; the arbitrary
preliminary object remains \(\mathrm{PSC}_H\). \(\square\)

This lemma defines a corrected canonical predecessor package; it does
not claim that the undefined \(K_0^0\) in printed line 1597 was already
source-identified with \(Q_0\).

The two lemmas prove finite selection and routing.  They do not prove
that \(\alpha^n\) belongs to \(\overline{L_0^n}\), that it is the
unique attachment of \(L_0^n\), or that a proof-used prime-end access
lands there.  The conditional proof-used compatibility predicate
\(\mathrm{PUS}_H\) says only that every independently supplied
depth-\(n\) proper restriction following the declared \(Q\)-parent
itinerary lands in this \(Q_0\)-selected \(L_0^n\); it does not
construct such a restriction or occurrence.

The remaining separator predicate \(\mathrm{KSEP}_H\) must prove that
\(Q_0\) separates \(\alpha^0\) from the jointly selected \(L_0^1\)
and that the inverse branch propagates this to separation of
\(\alpha^n\) from \(L_0^{n+1}\) by \(Q_n\), with the proof-used collar
and occurrence compatibility asserted at line 1602.  No use is made
of line 1600 or line 1603.

## 3. Finite marked-tree pruning

In the locally connected case, let \(G\) be the finite combinatorial
Hubbard tree obtained by collapsing each vertex continuum of the
physical \(T\) to its vertex.  In the non-locally-connected case, let
\(G=T_{\rm com}\) be the finite combinatorial Hubbard tree in the
rational-lamination model at source lines 542--543.  In either case,
let \(M\subset V(G)\) be the vertices corresponding to the components
of \(\mathcal K\), or to their model images.

In the locally connected case, the source defines \(T\) as the least
connected set containing \(\mathcal K\).  In the combinatorial case,
the phrase "analogously defined Hubbard tree" applies the same
connected-hull construction in the locally connected model.  Hence,
in either finite combinatorial tree,

\[
 |G|=\operatorname{Hull}_{|G|}(M).
\tag{3.1}
\]

If a proper connected subgraph of \(G\) contained \(M\), then in the
physical locally connected case it would
lift to a proper connected subset of \(T\) containing \(\mathcal K\).
In the model case it directly contradicts the model's connected-hull
definition.  We do **not** infer that the physical lift of
\(T_{\rm com}\) is inclusion-minimal in the non-locally-connected
case; its fibers are handled separately in the contact predicate.

### Lemma 3.1 (terminal-component pruning)

Let \(G\) be a finite tree satisfying (3.1).  For every point
\(x\in |G|\), every connected component \(C\) of
\(|G|\setminus\{x\}\) contains a vertex of \(M\).

#### Proof

Assume that one component \(C\) contains no marked vertex.  In a tree,

\[
 H:=|G|\setminus C
\tag{3.2}
\]

is a closed connected subtree: it contains \(x\), and the unique arc
between any two of its points cannot enter \(C\), because entering and
leaving the component \(C\) would pass through \(x\) twice.  The
subtree \(H\) contains every marked vertex and is proper because
\(C\ne\varnothing\).  This contradicts (3.1). \(\square\)

### Corollary 3.2 (terminal-side criterion)

Let \(S\subset |G|\).  If there is an \(x\in|G|\) and a component
\(C\) of \(|G|\setminus\{x\}\) with

\[
 C\subset S,
\tag{3.3}
\]

then \(S\) contains a marked vertex.

This is the exact finite-tree fact that the source's component count
can use.  Mere nonemptiness or connectedness of \(S\) is insufficient.

### Sharpness witness

Let

\[
 |G|=[0,3],\qquad M=\{0,3\},\qquad S=[1,2].
\tag{3.4}
\]

Then \(G=\operatorname{Hull}(M)\), and \(S\) is nonempty, compact, and
connected, but \(S\cap M=\varnothing\).  Thus neither minimality of the
Hubbard carrier nor connectedness of \(L_0^b\cap T\) can exclude an
edge-only intersection.

Even being one inverse-image component does not repair this.  Take

\[
 T=[0,1]=\operatorname{Hull}\{0,1\},\qquad
 g(x)=4x(1-x),\qquad L=(0,1].
\tag{3.5}
\]

Then

\[
 g^{-1}(L)=(0,1)
\tag{3.6}
\]

is one connected inverse component, but its closure has two attachment
points \(0,1\), both mapping to the single endpoint \(0\), and it
contains neither marked endpoint.  This is not a KKL analytic
counterexample: it is a finite-tree countermodel to inferring a
one-attachment terminal side merely from the phrase "component of an
inverse image."  The selected analytic route must prove that the
closure of the pulled component has exactly one recorded attachment
fiber and that its original-tree intersection is saturated over the
resulting terminal side.

Even a proved one-point attachment does not force marked contact.
Take the original tree \(T=[-1,1]\), mark only \(-1,1\), and attach a
new edge \(e=[0,1]_e\) by identifying \(0_e\) with the unmarked
interior point \(0\in T\).  Define a continuous graph map by

\[
 g(x)=-\frac12+\frac{x^2}{2}\quad(x\in T),\qquad
 g(t_e)=-\frac12-\frac{t}{2}\quad(t_e\in e).
\tag{3.7}
\]

For \(J=[-1,-1/2]\subset T\), the component
\(g^{-1}(J)=e\cup\{0\}\) meets the original \(T\) at the single point
\(0\) and meets no mark.  This is again only an abstract logical
countermodel, not a \(\psi\)-quadratic-like realization.  It proves
that the one-gate statement at source line 1304 cannot by itself
discharge \(\mathrm{MCI}_b\); the gate must also be classified.

## 4. Marked-core contact and dynamic continuum saturation

The quotient statement in Corollary 3.2 does not by itself identify an
actual point of a small-Julia continuum in a non-locally-connected
lift.  The minimal open predicate is therefore the marked-core contact
\(\mathrm{MCI}_b\) from (1.2).

Once actual contact is supplied, however, whole-continuum containment
is not an additional hypothesis.

### Theorem 4.1 (selected-predecessor continuum saturation)

Assume \(\mathrm{SC}_H\).  For every cycle component \(K_i\) and every
\(0\le n\le H\),

\[
 K_i\cap L_0^n\ne\varnothing
 \quad\Longrightarrow\quad
 K_i\subset L_0^n.
\tag{4.1}
\]

#### Proof

For \(n=0\), the component \(K_i\) lies in \(T\), is connected, and
does not contain \(\alpha_F\): otherwise fixedness of \(\alpha_F\)
and \(F(K_i)=K_{i+1}\) would put \(\alpha_F\) in two distinct members
of the primitive cycle.  If \(K_i\) meets
\(L_0^0=T\cap\mathfrak L_0\), it lies wholly in the one component
\(\mathfrak L_0\) of \(K(F)\setminus\{\alpha_F\}\).  Hence
\(K_i\subset L_0^0\).

Assume the result at depth \(n-1\), and suppose
\(K_i\cap L_0^n\ne\varnothing\).  Since
\(F(L_0^n)\subset L_0^{n-1}\),

\[
 F(K_i)\cap L_0^{n-1}\ne\varnothing.
\tag{4.2}
\]

The induction hypothesis gives
\(F(K_i)\subset L_0^{n-1}\), and therefore

\[
 K_i\subset F^{-1}(L_0^{n-1}).
\tag{4.3}
\]

The continuum \(K_i\) is connected and meets the selected connected
component \(L_0^n\) of that inverse image.  It is consequently
contained in the same component, namely \(L_0^n\). \(\square\)

The connected-component clause in \(\mathrm{SC}_H\) is essential in
the last sentence.  The arbitrary-set example
\[
 T=[-1,2],\qquad K_0=[-1,1],\qquad S=\{0\}
\tag{4.4}
\]
meets \(K_0\) but does not contain it; Theorem 4.1 does not apply to
such an unrelated \(S\).

### Corollary 4.2

Under \(\mathrm{SC}_H\), \(\mathrm{MCI}_b\) is equivalent to

\[
 L_0^b\cap T\ne\varnothing
 \Longrightarrow
 \exists K\in\operatorname{Comp}\mathcal K
 \text{ with }K\subset L_0^b.
\tag{4.5}
\]

Only the forward implication needs proof, and it is Theorem 4.1.

One selected sufficient certificate for \(\mathrm{MCI}_b\) is:

> **Terminal marked-core predicate \(\mathrm{TMC}_b\).**  If
> \(L_0^b\cap T\ne\varnothing\), then:
>
> 1. for some recorded point \(x_b\), there is one component
>    \(C_b\in\pi_0(|G|\setminus\{x_b\})\) with
>    \(C_b\subset\pi_T(L_0^b\cap T)\);
> 2. choosing \(v_K\in C_b\cap M\) by Lemma 3.1, this same vertex is
>    realized by an actual contact \(K\cap L_0^b\ne\varnothing\).

Here \(\pi_T:T\to|G|\) is the finite vertex-edge quotient.  In the
locally connected physical Hubbard-tree model used at source lines
514--520, the fiber over the marked vertex \(v_K\) is exactly the
vertex continuum \(K\), so marked-vertex incidence gives Clause 2.
In a non-locally-connected rational-lamination or prime-end lift, the
corresponding collapsed marked fiber can be larger than \(K\);
there Clause 2 is a separate analytic lift assertion.  Theorem 4.1
then upgrades actual contact to full containment.  Thus

\[
 \mathrm{TMC}_b\Longrightarrow\mathrm{MCI}_b
 \Longrightarrow\text{the containment in (4.5)}.
\tag{4.6}
\]

More precisely, Clause 1 and Lemma 3.1 locate the marked vertex;
exact physical fiber identification supplies Clause 2 in the locally
connected case, while Clause 2 must be proved independently in the
non-locally-connected lift.  Pruning alone does not prove the latter
contact.

The converse is not asserted: a different dynamical argument could
establish \(\mathrm{MCI}_b\) without producing a complete terminal side.

### Theorem 4.3 (terminal inverse sheets and locally connected incidence)

For \(n\ge0\), put

\[
 \Omega_0=\mathfrak L_0,\qquad
 \Omega_n=\phi_0^n(\mathfrak L_0)\quad(n\ge1).
\tag{4.7}
\]

Without assuming local connectivity, for every \(n\ge1\),

\[
 \overline{\Omega_n}
   =\Omega_n\cup\{\alpha^n\},\qquad
 \Omega_n\in
 \pi_0\!\left(K(F)\setminus\{\alpha^n\}\right).
\tag{4.7a}
\]

If, in addition, the physical filled continuum \(K(F)\) is locally
connected, put \(T_n=F^{-n}(T)\).  This is the base-dynamical inverse
inside \(K(F)\); no identification with the ambient fiber-product tree
\(f^{-n}(T)\) is made here.  That graph lift belongs to the later
pseudo-quadratic-like naturality gate.  For the \(Q_0\)-selected chain
of Lemma 2.2,

\[
 L_0^n=T_n\cap\Omega_n,
\tag{4.8}
\]

and

\[
 L_0^n\cap T\ne\varnothing
 \Longrightarrow
 \exists K_i\in\operatorname{Comp}\mathcal K
 \text{ with }K_i\subset L_0^n.
\tag{4.9}
\]

Consequently \(\mathrm{MCI}_b\) holds in the locally connected
physical category.

#### Proof

**Step 1: the first inverse sheet has one root.**  The domain
\(D_0=\phi_0(\mathfrak L_0)\) is open and connected.  We claim

\[
 \partial_{K(F)}D_0=\{\alpha^1\}.
\tag{4.11}
\]

The fixed point \(\alpha_F\) is noncritical, because the unique
critical point belongs to the limb \(\mathfrak L_0\), which does not
contain \(\alpha_F\).  We first prove
\(\alpha_F\notin\overline{D_0}\), without making any local-arm
connectivity assumption.  Otherwise choose \(x_k\in D_0\) with
\(x_k\to\alpha_F\) and set
\(y_k=F(x_k)\in\mathfrak L_0\).  Then \(y_k\to\alpha_F\).
The source homeomorphism
\[
 F:\mathfrak L_{q-1}\longrightarrow\mathfrak L_0
\]
supplies a unique \(z_k\in\mathfrak L_{q-1}\) with
\(F(z_k)=y_k\).  Source line 501 gives
\(\overline{\mathfrak L_{q-1}}
 =\mathfrak L_{q-1}\cup\{\alpha_F\}\).
Every accumulation point \(z\) of \((z_k)\) therefore belongs to this
closure and satisfies \(F(z)=\alpha_F\).  The two preimages of
\(\alpha_F\) are \(\alpha_F\) and
\(\alpha^1\in\mathfrak L_0\); the latter is not in
\(\overline{\mathfrak L_{q-1}}\).  Hence \(z_k\to\alpha_F\).
For all sufficiently large \(k\), both \(x_k\) and \(z_k\) lie in a
neighborhood on which \(F\) is injective, while
\[
 x_k\ne z_k,\qquad F(x_k)=F(z_k),
\]
a contradiction.

Let \(x\in\partial D_0\).  Choose \(x_k\in D_0\) with \(x_k\to x\).
Continuity first gives
\(F(x)\in\overline{\mathfrak L_0}\).  If
\(F(x)\in\mathfrak L_0\), then
\[
 x_k=\phi_0(F(x_k))\longrightarrow \phi_0(F(x)).
\]
The left side tends to \(x\), so uniqueness of limits gives
\(x=\phi_0(F(x))\in D_0\).  This is impossible because \(D_0\) is open
and therefore disjoint from its boundary.  Consequently
\(F(x)\in\partial\mathfrak L_0=\{\alpha_F\}\).  The two preimages of
\(\alpha_F\) are \(\alpha_F\) and \(\alpha^1\), and the preceding
two-preimage argument excludes \(\alpha_F\) from
\(\overline{D_0}\).
Also \(\alpha^1\notin D_0\), because
\(F(\alpha^1)=\alpha_F\notin\mathfrak L_0\).
Conversely, for \(y_k\in\mathfrak L_0\) tending to \(\alpha_F\), any
limit of \(\phi_0(y_k)\) is a preimage of \(\alpha_F\); it cannot be
\(\alpha_F\), so it is \(\alpha^1\).  This proves (4.11).  It used
only the finite limb decomposition, the limb-closure formula, the
degree-two dynamics, and local injectivity at \(\alpha_F\), not local
connectivity of \(K(F)\).

Since \(D_0\) is connected and open and is closed in
\(K(F)\setminus\{\alpha^1\}\), it is a component of that punctured
continuum.

**Step 2: every iterated inverse sheet is terminal.**  Inductively,

\[
 \overline{\Omega_n}
   =\Omega_n\cup\{\alpha^n\},\qquad
 \Omega_n\in
 \pi_0\!\left(K(F)\setminus\{\alpha^n\}\right).
\tag{4.12}
\]

The case \(n=1\) is (4.11).  For \(n\ge2\),
\(\overline{\Omega_{n-1}}\) is compact and lies in
\(\mathfrak L_0\), including its endpoint
\(\alpha^{n-1}\).  The homeomorphism \(\phi_0\) is defined there, so

\[
 \overline{\Omega_n}
 =\phi_0(\overline{\Omega_{n-1}})
 =\Omega_n\cup\{\phi_0(\alpha^{n-1})\}
 =\Omega_n\cup\{\alpha^n\}.
\tag{4.13}
\]

For completeness, continuity and density give
\(\phi_0(\overline{\Omega_{n-1}})
\subset\overline{\phi_0(\Omega_{n-1})}\), while compactness makes
\(\phi_0(\overline{\Omega_{n-1}})\) closed and containing
\(\phi_0(\Omega_{n-1})\), which gives the reverse inclusion in
(4.13).
Moreover,
\[
 F^n(\alpha^n)=\alpha^0=\alpha_F\notin\mathfrak L_0,
 \qquad
 F^n(\Omega_n)=\mathfrak L_0,
\]
so \(\alpha^n\notin\Omega_n\).  The set \(\Omega_n\) is open and
connected and, by (4.13), is closed in
\(K(F)\setminus\{\alpha^n\}\).  It is therefore exactly one connected
component of that punctured continuum.  This proves (4.12), and hence
the unconditional assertion (4.7a).

**Step 3: local connectivity supplies the physical tree
identification.**  Assume from now on that \(K(F)\) is locally
connected.  The project already source-locks the standard fact that a
periodically repelling \(\psi\)-quadratic-like map has empty-interior
filled continuum: use the same-filled-continuum quadratic-like
restriction, no wandering Fatou components, and the exclusion of
nonrepelling periodic cycles.  The set \(K(F)\) is full.  If it
contained a Jordan curve, fullness would force the bounded Jordan
domain into \(K(F)\), contradicting empty interior.  A locally
connected continuum containing no simple closed curve is a dendrite.

Every subcontinuum of a dendrite contains the unique arc between each
two of its points.  Also \(\alpha_F\in T\): the carrier contains
\(Q_0\subset\mathfrak L_0\) and
\(F(Q_0)\subset\mathfrak L_1\), and a connected subset meeting two
components of \(K(F)\setminus\{\alpha_F\}\) contains their common
cutpoint.  It follows that

\[
 L_0^0=T\cap\mathfrak L_0
\tag{4.10}
\]

is connected: the unique arc in \(K(F)\) between two of its points
lies in the component \(\mathfrak L_0\) of
\(K(F)\setminus\{\alpha_F\}\), and, because both endpoints lie in the
subcontinuum \(T\), that arc lies in \(T\).

**Step 4: identify the selected tree predecessor.**  Because
\(L_0^0\) is connected, Lemma 2.2 selects the whole critical inverse
at the first step and hence

\[
 L_0^n=\phi_0^n(L_0^0).
\tag{4.14}
\]

The restriction \(F^n:\Omega_n\to\mathfrak L_0\) is a
homeomorphism.  Therefore

\[
\begin{aligned}
 T_n\cap\Omega_n
 &=\{x\in\Omega_n:F^n(x)\in T\}\\
 &=(F^n|_{\Omega_n})^{-1}(T\cap\mathfrak L_0)\\
 &=\phi_0^n(L_0^0)=L_0^n,
\end{aligned}
\tag{4.15}
\]

which is (4.8).  Notice that this is an actual set equality, not a
coarse address comparison.

The equality \(F^n(\alpha^n)=\alpha_F\in T\) also gives
\(\alpha^n\in T_n\).  This fact is recorded for endpoint bookkeeping;
the incidence argument below does not require \(T_n\) itself to be
connected.

**Step 5: prune the original terminal side.**  Forward invariance of
\(T\) gives \(T\subset T_n\).  Suppose
\(x\in L_0^n\cap T\).

If \(\alpha^n\notin T\), connectedness of \(T\) places all of \(T\)
in one component of \(K(F)\setminus\{\alpha^n\}\).  Since it meets
\(\Omega_n\), (4.12) gives \(T\subset\Omega_n\), and then (4.8) gives
\(T\subset L_0^n\).

If \(\alpha^n\in T\), let \(C\) be the component of
\(T\setminus\{\alpha^n\}\) containing \(x\).  Equation (4.12) gives
\(C\subset\Omega_n\), while \(C\subset T\subset T_n\); hence
\(C\subset L_0^n\) by (4.8).  Lemma 5.1 gives
\(\alpha^n\notin K_i\) for every component \(K_i\) of \(\mathcal K\).
If no \(K_i\) were contained in \(C\), then no \(K_i\) could meet
\(C\): a connected \(K_i\subset T\setminus\{\alpha^n\}\) meeting \(C\)
lies wholly in the component \(C\).  Since \(T\) is a dendrite, \(C\)
is open in \(T\), so \(T\setminus C\) is compact.  It is connected
because, for every \(y\in T\setminus C\), the unique arc
\([\alpha^n,y]_T\) avoids \(C\); thus all its points join to the common
point \(\alpha^n\) inside \(T\setminus C\).  This compact subtree
contains every component of \(\mathcal K\) and is proper because
\(x\in C\).  This contradicts the source definition of \(T\) as the
least connected set containing \(\mathcal K\).  Hence some actual
small-Julia continuum \(K_i\) lies in \(C\), and

\[
 K_i\subset C\subset L_0^n.
\tag{4.16}
\]

Both cases prove (4.9). \(\square\)

### Corollary 4.4 (model incidence and exact non-LC residue)

Let \(\bar{\mathcal K}=\{\bar K_i\}\) denote the geometric model
small-Julia continua.  These are continua in \(K(F)_{\rm com}\), not
points.  Only the subsequent finite-tree quotient collapses
\(\bar K_i\) to an abstract marked vertex \(\bar v_i\).  The same proof
in KKL's locally connected degree-two rational-lamination model proves
the stronger, correctly typed statement

\[
 L_{0,\mathrm{com}}^n\cap T_{\rm com}\ne\varnothing
 \Longrightarrow
 \exists i,\quad \bar K_i\subset L_{0,\mathrm{com}}^n.
\tag{4.17}
\]

Equivalently, the finite-tree image of
\(L_{0,\mathrm{com}}^n\) contains the marked abstract vertex
\(\bar v_i\), but this quotient statement must not be substituted for
the geometric containment in (4.17).

To recover physical \(\mathrm{MCI}_b\) in the
non-locally-connected case by this model-lift route, it is sufficient
to prove, for the selected component and corresponding geometric
model continuum \(\bar K_i\),

\[
\pi^{-1}(L_{0,\mathrm{com}}^b)=L_0^b,
\qquad
\pi(K_i)\subset\bar K_i.
\tag{4.18}
\]

Indeed, (4.17)--(4.18) give
\[
 K_i\subset\pi^{-1}(\bar K_i)
      \subset\pi^{-1}(L_{0,\mathrm{com}}^b)=L_0^b.
\]
Source lines 542--543 say only that the combinatorial objects can be
lifted; they do not state the selected full-preimage equality or the
geometric marked-continuum correspondence in (4.18).
Therefore the locally connected and model conclusions are proved,
while physical non-locally-connected \(\mathrm{MCI}_b\) remains open
for this chosen sufficient route at the package (4.18).  This is not a
minimality claim: after selected full-preimage equality, a separately
proved nonempty intersection
\(\pi(K_i)\cap\bar K_i\ne\varnothing\), together with the continuum
saturation theorem, could also suffice.

### Proposition 4.5 (monotone full-lift criterion)

Let barred symbols denote KKL's locally connected combinatorial model.
Assume, through the finite horizon \(H=b+2\), the following package
\(\mathrm{MFL}_H\):

1. \(K(F)_{\rm com}\) is a dendrite and
   \(\pi:K(F)\to K(F)_{\rm com}\) is a continuous monotone
   surjection satisfying
   \(\pi\circ F=F_{\rm com}\circ\pi\);
2. the selected fixed-point predecessor labels agree and the fixed
   fiber is a singleton:
   \[
     \pi(\alpha^n)=\bar\alpha^n\quad(0\le n\le H),
     \qquad
     \pi^{-1}(\bar\alpha^0)=\{\alpha^0\};
   \tag{4.19}
   \]
3. the physical carrier is the full lift
   \[
     T=\pi^{-1}(T_{\rm com});
   \tag{4.20}
   \]
4. the physical critical point maps to the model critical point,
   \(\pi(Q_n)\subset\bar\Omega_n\) for \(0\le n\le H\), and each
   physical small-Julia continuum maps into its corresponding
   geometric model small-Julia continuum:
   \[
     \pi(c_F)=\bar c_F,\qquad
     \pi(K_i)\subset\bar K_i.
   \tag{4.21}
   \]

Clause 4 deliberately does **not** say
\(\pi(K_i)=\{\bar v_i\}\).  The latter conflates the geometric
rational-lamination projection with the separate finite-tree quotient
and is incompatible with finite-orbit injectivity for the canonical
monotone model.

Then, for the physical and model \(Q_0\)-selected chains,

\[
 \pi^{-1}(L_{0,\rm com}^n)=L_0^n,
 \qquad 0\le n\le H.
\tag{4.22}
\]

Consequently model continuum incidence (4.17) implies physical marked
incidence, in the stronger form

\[
 \bar K_i\subset L_{0,\rm com}^n
 \Longrightarrow K_i\subset L_0^n.
\tag{4.23}
\]

#### Proof

First, (4.19) already forces all selected predecessor fibers to be
singletons.  Monotonicity makes
\(E_n:=\pi^{-1}(\bar\alpha^n)\) connected, while semiconjugacy gives
\[
 F^n(E_n)\subset
 \pi^{-1}(\bar\alpha^0)=\{\alpha^0\}.
\]
The degree-two quadratic-like map \(F\) is finite-to-one, so
\(F^{-n}(\alpha^0)\) is finite (of cardinality at most \(2^n\)).
Thus \(E_n\) is a connected subset of a finite set.  It contains
\(\alpha^n\), and therefore
\[
 \pi^{-1}(\bar\alpha^n)=\{\alpha^n\},
 \qquad 0\le n\le H.
\tag{4.19a}
\]

We first record the topological component lemma used below.  Let
\(\rho:X\to Y\) be a continuous monotone surjection from a compact
continuum onto a dendrite, and suppose
\(\rho^{-1}(y)=\{x\}\).  Then \(\rho\) gives a
bijection

\[
 \pi_0(X\setminus\{x\})
 \longleftrightarrow
 \pi_0(Y\setminus\{y\}),
 \qquad
 C\longmapsto\rho(C),
\tag{4.24}
\]

whose inverse sends a component \(D\) to \(\rho^{-1}(D)\).

For a compact subcontinuum \(A\subset Y\),
\(\rho^{-1}(A)\) is connected.  Otherwise a separation
\(\rho^{-1}(A)=U\sqcup V\) has compact sides.  Monotonicity places
every point fiber wholly in one side, so the disjoint compact sets
\(\rho(U)\) and \(\rho(V)\) separate \(A\), a contradiction.

The same conclusion holds for a nonempty connected subset
\(A\subset Y\), even when \(A\) is not closed.  Fix \(a_0\in A\).
For every \(a\in A\), the unique dendrite arc \([a_0,a]_Y\) lies in
\(A\): omission of a point of that arc would place \(a_0\) and \(a\)
in two distinct components of its complement and would separate
\(A\).  Hence
\[
 A=\bigcup_{a\in A}[a_0,a]_Y.
\]
Each inverse arc is connected by the compact-subcontinuum case, and
all inverse arcs contain the common fiber \(\rho^{-1}(a_0)\).
Their union, which is exactly \(\rho^{-1}(A)\), is connected.

Now let \(D\) be a component of \(Y\setminus\{y\}\) and fix
\(d_0\in D\).  Since \(Y\) is a dendrite,
\[
 D=\bigcup_{d\in D}[d_0,d]_Y .
\]
The inverse images of these compact arcs are connected and all contain
\(\rho^{-1}(d_0)\); their union \(\rho^{-1}(D)\) is therefore
connected and avoids \(x\).  Conversely, the image of a component of
\(X\setminus\{x\}\) is connected and avoids \(y\), hence lies in one
component of \(Y\setminus\{y\}\).  Maximality and surjectivity now give
(4.24).

Apply (4.24) to \(\pi\) at
\(\alpha^n\mapsto\bar\alpha^n\).  By construction of the selected
chain,
\[
 Q_n\subset L_0^n\subset\Omega_n,
 \qquad
 \pi(Q_n)\subset\bar\Omega_n.
\]
Thus the component bijection (4.24) sends the physical component
\(\Omega_n\) to the model component \(\bar\Omega_n\).  Theorem 4.3 and
its model counterpart therefore give

\[
 \pi^{-1}(\bar\Omega_n)=\Omega_n,
 \qquad 0\le n\le H.
\tag{4.25}
\]

At \(n=0\), (4.20), (4.25), and distributivity of inverse images give

\[
 L_0^0
 =T\cap\mathfrak L_0
 =\pi^{-1}(T_{\rm com}\cap\bar{\mathfrak L}_0)
 =\pi^{-1}(L_{0,\rm com}^0).
\tag{4.26}
\]

The model set \(L_{0,\rm com}^0\) is connected but need not be compact,
because it omits the root.  The arbitrary-connected-set argument
following (4.24), not merely the compact-subcontinuum case, therefore
shows that its inverse \(L_0^0\) is connected.  Hence the set identity
in Step 4 of Theorem 4.3, whose derivation uses only connectedness of
\(L_0^0\), applies:

\[
 L_0^n=F^{-n}(T)\cap\Omega_n.
\tag{4.27}
\]

The same identity holds in the locally connected model.  Using
semiconjugacy, (4.20), and (4.25), we obtain

\[
\begin{aligned}
 \pi^{-1}(L_{0,\rm com}^n)
 &=\pi^{-1}\!\left(
     F_{\rm com}^{-n}(T_{\rm com})\cap\bar\Omega_n
   \right)\\
 &=F^{-n}\!\left(\pi^{-1}(T_{\rm com})\right)
   \cap\pi^{-1}(\bar\Omega_n)\\
 &=F^{-n}(T)\cap\Omega_n=L_0^n.
\end{aligned}
\tag{4.28}
\]

This proves (4.22).  Finally, if
\(\bar K_i\subset L_{0,\rm com}^n\), then (4.21) and (4.22) give
\[
 K_i\subset\pi^{-1}(\bar K_i)
       \subset\pi^{-1}(L_{0,\rm com}^n)=L_0^n,
\]
which is (4.23). \(\square\)

### Proposition 4.6 (small-Julia point-collapse obstruction)

Let \(\pi_{\rm Kw}\) be the monotone semiconjugacy obtained by
transporting Kiwi's canonical model through KKL's same-filled
quadratic-like restriction and a straightening.  For every member
\(K_i\) of the nondegenerate primitive small-Julia cycle,
\[
 \#\pi_{\rm Kw}(K_i)\ge2.
\tag{4.29}
\]
In particular, \(\pi_{\rm Kw}(K_i)\) cannot be identified with the
abstract finite-tree vertex \(\bar v_i\) at the geometric quotient
level.  Only a later carrier-tree quotient may collapse this
nondegenerate image to that vertex.

#### Proof

Let \(P\) be the primitive return period and
\(G=F^P:V'\to V\) the quadratic-like renormalization with filled Julia
set \(K_0\).  Straighten \(G\) to \(P_c(z)=z^2+c\).  Its two finite
fixed points lie in \(K(P_c)\).  They are distinct: a repeated root of
\[
 z^2-z+c=0
\]
forces \(c=1/4\).  But \(P_{1/4}\) has an open parabolic basin in its
filled Julia set.  A global quasiconformal straightening carries
\(K_0\) onto \(K(P_c)\) and preserves ambient interior.  The active KKL
map is periodically repelling, so its same-filled quadratic-like
restriction and the no-wandering-domain theorem give
\(\operatorname{int}K(F)=\varnothing\).  Since \(K_0\subset K(F)\),
the parabolic case is impossible.

The straightening conjugacy gives distinct \(G\)-fixed points
\(x_0,y_0\in K_0\).  Put
\[
 x_i=F^i(x_0),\qquad y_i=F^i(y_0),\qquad 0\le i<P.
\]
Both points lie in \(K_i\) and have finite \(F\)-orbits.  If
\(x_i=y_i\), applying \(F^{P-i}\) gives \(x_0=y_0\), a contradiction.
Moreover \(\operatorname{int}K(F)=\varnothing\) gives
\(K(F)=J(F)\), so these periodic points belong to the finite-orbit
Julia set on which Kiwi's theorem applies.
Kiwi's Theorem 5.12 is injective on finite-orbit points, so
\(\pi_{\rm Kw}(x_i)\ne\pi_{\rm Kw}(y_i)\).  This proves (4.29).
\(\square\)

The complete clause audit and source locations are recorded in
`kkl_stationary_n2_kiwi_model_identification_audit_20260727.md`.
This proposition concerns the transported Kiwi map.  Identifying that
map with KKL's particular \(\pi\) remains open.

The source-lock boundary is now exact.  KKL lines 542--543 state the
locally connected model, a natural projection, descent of \(F\), and
an unspecified lift of corresponding objects.  They do not state
monotonicity, the selected labels and singleton fixed fiber in (4.19),
the full-lift equality (4.20), or the component/marked-continuum
identifications in (4.21).
The corresponding Dudko--Lyubich source says at lines 956--958 that
the induced model map is semiconjugate by a natural projection, and
at lines 968--970 that lifting the model Hubbard tree produces a
Hubbard continuum.  Lines 973--978 explicitly use a full-preimage
convention for individual geodesic continua, but do not identify the
entire Hubbard continuum with \(\pi^{-1}(T_{\rm com})\), identify its
projection with KKL's selected limb labels, or establish the
physical/model marked-continuum correspondences.

Kiwi's Theorem 5.12, after the same-filled restriction and
straightening, supplies an existential monotone semiconjugacy that is
injective on the finite-orbit subset.  More strongly, Kiwi's Theorem 2
proves trivial dynamical fibers at periodic and preperiodic points,
Proposition 4.2 forms the quotient \(q\) by those fibers, and the proof
of Theorem 5.12 writes the semiconjugacy as
\(h=\widehat w^{-1}\circ q\).  Thus the transported Kiwi map has
singleton complete fibers at every periodic and preperiodic point.
This proves Proposition 4.6 and discharges the abstract singleton-fiber
subclause for that transported map.  The dendrite target and a marked
dynamical homeomorphism intertwining the transported Kiwi projection
with KKL's particular rational-lamination projection, carrier, sheet,
\(Q_n\), \(K_i\), and access markings all remain unproved.
Thus Proposition 4.5 proves only that the corrected
\(\mathrm{MFL}_H\) is a sufficient package.

The locked paragraph defines \(L_0^b\) as a selected component of an
iterated inverse image.  It does not state that its intersection with
the original \(T\) contains a terminal side or contacts a marked core.
Those properties do not follow from the word "component": the
component is taken in the inverse-image tree, whereas the intersection
in (1.1) is with the original tree.

## 5. Endpoint avoidance and distinctness of the predecessor cycle

The second hidden issue is whether the \(b+1\) components obtained by
iteration are distinct.  In the source's high-type branch this part
can be proved.

### Lemma 5.1 (a selected fixed-point predecessor avoids the cycle)

Assume \(\mathrm{APC}_H\).  For every \(0\le n\le H\),

\[
 \alpha^n\notin\mathcal K.
\tag{5.1}
\]

#### Proof

The selection gives \(F^n(\alpha^n)=\alpha_F\).  If
\(\alpha^n\in K_i\), then
\(\alpha_F\in K_{i+n}\).  Since \(F(\alpha_F)=\alpha_F\) and
\(F(K_j)=K_{j+1}\), the fixed point would belong successively to every
member of the primitive cycle.  This contradicts pairwise
disjointness and the cycle period \(P>1\). \(\square\)

This proves only that the selected fixed-point predecessor avoids the
cycle.  It does not identify \(\alpha^n\) with the attachment of
\(L_0^n\).  Without endpoint coherence, the actual gate could still
lie inside a cycle continuum, in an edge interior, or at an unmarked
branch point.

### Lemma 5.2 (period at least the rotation denominator)

Let \(K_0\) be the critical member of a primitive small-Julia cycle

\[
 \mathcal K=\bigcup_{j=0}^{P-1}K_j,\qquad F(K_j)=K_{j+1\bmod P},
\tag{5.2}
\]

for a map with limb rotation number \(1/q\).  Then

\[
 P\ge q.
\tag{5.3}
\]

#### Proof

The critical point belongs to \(K_0\).  The set \(K_0\) is connected,
contains a point of \(\mathfrak L_0\), and avoids \(\alpha_F\), so
\(K_0\subset\mathfrak L_0\).  The critical value belongs to
\(K_1=F(K_0)\), and the source places it in \(\mathfrak L_1\).
No \(K_j\) contains the fixed point \(\alpha_F\):
if one did, forward invariance of \(\alpha_F\) would put it in every
\(K_j\), contrary to primitivity and \(P>1\).  Since \(K_1\) is
connected and avoids \(\alpha_F\), it lies in the single component
\(\mathfrak L_1\) of
\(K(F)\setminus\{\alpha_F\}\).

For \(1\le j<q-1\), the source map carries
\(\mathfrak L_j\) homeomorphically to \(\mathfrak L_{j+1}\).
Induction gives

\[
 K_j\subset\mathfrak L_j,\qquad 1\le j<q.
\tag{5.4}
\]

The \(q\) sets \(K_0,K_1,\ldots,K_{q-1}\) lie in pairwise-disjoint
limbs and are therefore distinct.  Hence their cycle period satisfies
\(P\ge q\). \(\square\)

### Corollary 5.3

If \(q>b\), then for every component \(K\) of \(\mathcal K\),

\[
 K,F(K),\ldots,F^b(K)
\tag{5.5}
\]

are \(b+1\) distinct components.

#### Proof

Every component has period \(P\) under the cyclic permutation (5.2).
Lemma 5.2 gives \(P\ge q>b\). \(\square\)

The inequality \(q>b\) must be written into the high-type threshold;
the asymptotic notation \(q\largegiven{b}\) cannot be used without
making this elementary numerical consequence explicit.

## 6. Conditional completion of line 1598

### Proposition 6.1 (selected-predecessor count)

Assume \(F\) has parabolically \(b\)-bounded primitive renormalization
with rotation number \(1/q\), assume \(q>b\), assume an explicit chain
\(\mathrm{SC}_H\), and assume that it satisfies \(\mathrm{MCI}_b\).
The construction in Lemma 2.1 gives

\[
 L_0^n\subset\mathfrak L_0,\qquad
 F(L_0^n)\subset L_0^{n-1}.
\tag{6.1}
\]

Then

\[
 L_0^b\cap T=\varnothing.
\tag{6.2}
\]

#### Proof

Suppose \(L_0^b\cap T\ne\varnothing\).  Predicate
\(\mathrm{MCI}_b\) supplies a component \(K_b\) of \(\mathcal K\)
contacting \(L_0^b\), and Theorem 4.1 supplies

\[
 K_b\subset L_0^b.
\tag{6.3}
\]

Applying (6.1) repeatedly gives

\[
 F^j(K_b)\subset L_0^{b-j}\subset\mathfrak L_0,
 \qquad 0\le j\le b.
\tag{6.4}
\]

Corollary 5.3 says that the \(b+1\) components in (6.4) are distinct.
This contradicts the stated parabolic \(b\)-boundedness, which allows at most
\(b\) components of \(\mathcal K\) in \(\mathfrak L_0\).  Therefore
(6.2) holds. \(\square\)

### Corollary 6.2 (deeper set disjointness)

Assume Proposition 6.1 and \(\mathrm{SC}_H\).  For
\(h=b+1,b+2\), iteration of (6.1) gives

\[
 F^{h-b}(L_0^h)\subset L_0^b.
\tag{6.5}
\]

Then

\[
 L_0^h\cap T=\varnothing.
\tag{6.6}
\]

#### Proof

If \(z\in L_0^h\cap T\), forward invariance of \(T\) and (6.5) give
\[
 F^{h-b}(z)\in L_0^b\cap T,
\]
contradicting (6.2). \(\square\)

### Corollary 6.3 (unconditional LC line-1598 repair)

If \(K(F)\) is locally connected, and \(F\) has parabolically \(b\)-bounded
primitive renormalization of rotation \(1/q\), and \(q>b\), then

\[
 L_0^h\cap T=\varnothing,\qquad h=b,b+1,b+2.
\tag{6.7}
\]

#### Proof

Theorem 4.3 supplies \(\mathrm{MCI}_b\); apply Proposition 6.1 and
Corollary 6.2. \(\square\)

These are set-level statements.  They still do not construct a
proper retained path, select a contact occurrence, prove that the
contact is an interior parameter of that path, choose its incoming
side, or identify the lifted \(B L_0\) access.

## 7. Minimal gate, sufficient certificate, and endpoint coherence

Lemmas 2.1--2.2 construct the canonical complete-horizon component,
small-Julia, and point chains.  Theorem 4.3 proves
\(\mathrm{MCI}_b\) in the locally connected physical category, and
Corollary 4.4 proves its finite-model counterpart.  The remaining
set-theoretic line-1598 gate is now the non-locally-connected
geometric model-continuum lift (4.18), not an unspecified terminal-side
theorem and not a collapse to an abstract graph vertex.

The proof-used Wave issue is separate.  Predicate
\(\mathrm{PUS}_H\) is the conditional compatibility statement that
every independently supplied depth-\(n\) proper restriction following
the declared \(Q\)-parent itinerary lands in the canonical
\(Q_0\)-selected component \(L_0^n\).  It does not construct the
restriction, endpoint occurrence, or host; those existential clauses
remain in the incoming-window anchor.

The stronger \(\mathrm{TMC}_b\) remains an optional geometric
certificate.  It is already realized by Theorem 4.3 in the locally
connected category.  In the non-locally-connected category its second
clause is precisely the physical/model continuum-correspondence issue
in (4.18).

Failure of \(\mathrm{TMC}_b\) is not automatically a counterexample to
\(\mathrm{MCI}_b\): a different dynamical argument could establish
actual contact without producing a complete terminal side.  The first
failure record for the selected terminal-side route is

\[
 \mathfrak e_b=
 \left(
 n,\ L_0^{n-1},L_0^n;\
 w_n;\
 L_0^n\cap T;\
 \operatorname{Att}_n;\
 \text{first missing terminal side};\
 \text{first marked vertex without actual \(K\)-contact}
 \right),
\tag{7.1}
\]

where \(\operatorname{Att}_n\) is the complete set of attachment points of the
selected pulled component to the original carrier at the first failed
depth.  Every point of \(\operatorname{Att}_n\) is classified as lying in a
small-Julia continuum, at an unmarked branch point, or in an edge
interior.  A middle-edge segment as in (3.4), or a one-gate attachment
at an unmarked point, is a genuine failure of this selected
certificate and cannot be relabelled as a small-Julia contact.

For the now-isolated non-locally-connected residue, the first failure
certificate is sharper:

\[
 \mathfrak f_b=
 \left(
 w_b,\ \bar K_i,\
 K_i,\
 \pi(K_i),\
 \pi^{-1}(L_{0,\mathrm{com}}^b)\mathbin{\triangle}L_0^b,\
 \text{first failed full-lift or continuum-correspondence clause in (4.18)}
 \right).
\tag{7.2}
\]

It must distinguish failure of the selected full-preimage equality
from failure of \(\pi(K_i)\subset\bar K_i\).  The abstract vertex
\(\bar v_i\) may be recorded only after applying the separate
finite-tree quotient.

The fixed-point predecessor record is separate.  One selected
sufficient architecture for the later incoming access is
\(\mathrm{EGC}_H\), endpoint-gate coherence.  For
\(0\le n\le H\), let \(\widehat T_n\) denote the selected pulled
carrier named by the actual-component address \(w_n\), and put

\[
 \operatorname{Att}_n=
 \overline{L_0^n}^{\,\widehat T_n}
 \cap
 \overline{\widehat T_n\setminus L_0^n}^{\,\widehat T_n}.
 \tag{7.3}
\]

Predicate \(\mathrm{EGC}_H\) means that these carriers are actually
constructed, that for \(1\le n\le H\) there is a recorded
map \(\eta_n:\widehat T_n\to\widehat T_{n-1}\) equal to the actual
branch-induced carrier homeomorphism and extending to the declared
collar and its prime-end boundary, and that

\[
 \alpha^n\in\overline{L_0^n}^{\,\widehat T_n},\qquad
 \operatorname{Att}_n=\{x_n\},\qquad x_n=\alpha^n,
 \tag{7.4}
\]

and, for \(1\le n\le H\), \(\eta_n\) transports the declared
one-sided prime-end access at \(x_n\) to the declared access at
\(x_{n-1}\).  This is a precisely
typed selected route suggested but not proved by the notation at
source lines 1597 and 1602.  Lemma 5.1 constrains the gate after
coherence is known; it does not prove (7.4).  The actual attachment
set may have several points, or its gate may lie in an edge interior
or at an unmarked branch point.

Thus \(\mathrm{EGC}_H\) is not needed for the set-counting implication
in Proposition 6.1.  It is one sufficient architecture for treating
the selected \(L_0^h\)-end as a canonical marked access in the
incoming-window anchor; another direct marked-access construction
could replace it.

## 8. Skeptic audit

1. The proof distinguishes the original Hubbard tree from its iterated
   inverse-image tree.
2. Finite-horizon existence is proved from the unique critical-limb
   inverse branch, and the critical small-Julia chain selects the first
   set component; no uniqueness is inferred from the definite article
   "the."
3. A connected edge-only intersection is not called a marked vertex.
4. In the locally connected tree, a marked vertex has fiber \(K\);
   in a non-locally-connected lift, actual \(K\)-contact is checked
   separately.
5. Distinctness is proved from \(P\ge q>b\), not assumed from the
   component count.
6. The numerical inequality \(q>b\) is explicit.
7. Whole-continuum containment is derived from actual contact and the
   selected whole-component recursion; it is not left inside
   \(\mathrm{TMC}_b\).
8. Set disjointness is not upgraded to proper path landing.
9. The selected \(\alpha\)-predecessor is not identified with the
   attachment gate without \(\mathrm{EGC}_H\).
10. Model marked-vertex incidence is not lifted to physical
    small-Julia contact without (4.18).
11. Canonical component selection is not identified with a
    proof-used Wave endpoint; \(\mathrm{PUS}_H\) is conditional and
    the anchor retains the existential burden.
12. The small-Julia predecessor chain is not called a separator chain
    without \(\mathrm{KSEP}_H\).
13. The terminal inverse-sheet theorem uses the two-preimage
    contradiction, not an unjustified assertion that an arbitrary
    small neighborhood has exactly \(q\) connected limb germs.
14. A monotone model theorem is not silently identified with KKL's
    underdefined natural projection; all clauses of
    \(\mathrm{MFL}_H\) remain explicit hypotheses.
15. Line 1600, line 1603, Gate N2, the stationary repair, VAAPC-I,
    UPTCR, and MLC remain open.

## 9. Binary status

| assertion | status |
|---|---|
| finite marked-tree terminal-component pruning | **proved** |
| nonempty connected intersection alone forces a marked vertex | **refuted** |
| complete-horizon selected predecessor chain \(\mathrm{SC}_H\) | **proved** |
| complete-horizon selected fixed-point chain \(\mathrm{APC}_H\) | **proved** |
| canonical small-Julia predecessor chain \(Q_0,\ldots,Q_H\) and \(Q_n\subset L_0^n\) | **proved** |
| terminal inverse-sheet geometry \(\overline{\Omega_n}=\Omega_n\cup\{\alpha^n\}\) | **proved without LC** |
| full-carrier separator/access predicate \(\mathrm{KSEP}_H\) | **open** |
| conditional proof-used compatibility \(\mathrm{PUS}_H\) | **open** |
| selected \(\alpha^n\) can lie in a cycle continuum | **refuted** |
| actual contact \(K_i\cap L_0^n\ne\varnothing\) implies \(K_i\subset L_0^n\) | **proved** |
| locally connected physical \(\mathrm{MCI}_b\) | **proved** |
| combinatorial-model marked incidence | **proved** |
| non-LC selected full-preimage and model-continuum lift (4.18) | **open** |
| \(\mathrm{MFL}_H\Rightarrow\) physical non-LC incidence | **proved conditionally** |
| KKL's exact projection/lift satisfies \(\mathrm{MFL}_H\) | **open** |
| primitive rotation-\(1/q\) cycle has \(P\ge q\) | **proved** |
| \(q>b\) gives \(b+1\) distinct predecessor components | **proved** |
| parabolic \(b\)-bound \(+\ q>b+\mathrm{SC}_H+\mathrm{MCI}_b\Rightarrow L_0^b\cap T=\varnothing\) | **proved** |
| \(\mathrm{TMC}_b\Rightarrow\mathrm{MCI}_b\) | **proved** |
| global physical KKL marked-core incidence \(\mathrm{MCI}_b\) | **open only at the non-LC lift** |
| optional global terminal marked-core certificate \(\mathrm{TMC}_b\) | **open only at the non-LC lift** |
| selected endpoint-gate coherence \(\mathrm{EGC}_H\) | **open** |
| actual KKL interior incoming contact | **open** |
| Gate N2 | **open** |

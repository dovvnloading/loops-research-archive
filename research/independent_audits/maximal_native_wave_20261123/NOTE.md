# Selected real slits: a complete access atlas and escape of positive zero-edge subarcs

**Date:** 2026-11-23.  **Nature of contribution:** a written analytic/topological
proof for the selected real primitive-tip family, with exact finite checks of
its endpoint bookkeeping.  This is a proposed research contribution, not an
external referee certification.  GPT-6 Astra Pro assisted the proof search,
derivation and verifier; no new human mathematical verification is represented.

## Result and dependency boundary

The new argument addresses the specific **selected-family H2** in
[the v2 scope](../../../papers/tip_family_preprint_v2_20261116/sections/referee_scope.tex),
and the positive **subatom zero-edge escape** left open in
[the family theorem](../../tip_family_theorem/THEOREM.md) and
[the November 15 attachment audit](../issue40_native_attachment_edge_incidence_20261115/NOTE.md).
It does not assume H2 in its proof.

From the physical degree-two restrictions, actual filled intervals, and
signed real orders specified in §1, we obtain:

1. An identification of the **entire hyperbolic ideal boundary**, including
   all integer deck translates, with the physical slit access circles.
   The identification preserves and reflects proper paths and their
   relative-endpoint subordination classes.  The ten/twenty incidence table
   is derived from these coordinates and the actual two monotone branches.
2. An exact connected-arc formula for the inclusion's boundary restriction.
   Its one nontrivial fiber is the **complete** attachment boundary.  The
   formula distinguishes open, closed and half-open inputs.
3. Every positive original marked interval, and its closure, saturates in at
   most **five iterations of \(G=f^p\)**.  Five is sharp for this marking.
   Original marked inputs commute with closure at every iterate in this
   family, for a geometric reason that fails for arbitrary finer inputs.
4. Every nondegenerate zero-old-edge **subarc**, including subarcs strictly
   inside an original atom, eventually exposes a complete old edge and
   saturates.  A Chebyshev angular length \(\delta>0\) gives the explicit
   saturation bound
   \[
     d+3\left\lceil\log_2(1/\delta)\right\rceil+5,
     \qquad 0\le d\le2.                                      \tag{0.1}
   \]
   There is **no bound independent of the initial subarc**: arbitrarily
   small positive subarcs can avoid all old edges for arbitrarily many
   iterations of this same physical map.

The physical input package is established by the **written** arguments in
[the family bridge proof, §§1–3](../../tip_family_theorem/PHYSICAL_BRIDGES.md),
using the selected finite parameter cells and the separately quantified
large-period chart.  This note supplies a consequence of that package.  It
does not independently re-prove its all-period parameter estimates or the
Douady–Hubbard Straightening Theorem.  In particular the finite program below
does not establish those analytic premises.

### Comparison with the existing packets

The actual tip family, its three filled intervals, the 10/20 proposed marking,
the two operators' tables, the whole-atom 1/2/3-step edge exposures, and the
whole-atom 2/3/4-step saturations are **already in the archive**.  They are not
new numerical or dynamical discoveries here.  In particular the November 16
note called ["M discharge"](../tip_family_hypothesis_M_discharge_20261116/NOTE.md)
already proposed identifying the full marked path classes, and the v2 referee
subsequently required a complete geometric argument for that claim.

| Existing result or open item | Addition in this note |
|---|---|
| Two slit approaches and a proposed H2 identification | An explicit annulus-uniformization/strip calculation of the **hyperbolic ideal quotient**, followed by a criterion retaining every integer relative winding (§2). |
| The already tabulated inclusion blocks | A physical contour code and connected-arc proof, including singleton attachment fibers and all endpoint conventions (§3); the old table is re-derived, not advertised as new (§4). |
| Whole zero-edge atom escape and saturation | A sharp bound for **every original marked interval**, and an all-iterate closure theorem using the singleton fibers and invariant marked cut set (§5). |
| Arbitrary positive fine zero-edge subarcs explicitly left open | A genuine Chebyshev return argument proving escape for every such arc, plus a proof that no initial-size-independent escape time exists (§6). |
| Full-path envelope arguments stated subject to the marking bridge | The complete ideal-lift criterion supplies their class-inclusion part; numerical SC competitors and excluded-energy estimates remain separate (§7). |

The conclusion concerns **the interval action** of the actual inclusion and
covering on these slit surfaces.  It does not assert that the image of a
parent crest is contained in each of its child crests.  It does not identify
arbitrary Wave descendants with those interval images, prove the full H3
extremal comparison, or settle Issue #40 in the general non-locally-connected
category.  The global H1–H4, UPTCR and MLC are not changed.

## 1. The physical input package and fixed notation

Fix one selected \(p\ge3\), its real parameter \(c_p\),

\[
 f(z)=z^2+c_p,\qquad G=f^p,\qquad x_j=f^j(0).
\]

Use the actual central proper degree-two restriction

\[
 G:V\longrightarrow U=D(0,R_p),\qquad V\Subset U,
 \quad R_3=1/4,\quad R_p=2^{-p}\quad(p\ge4).
\]

Here \(V\) is a disk, \(G\) is even and real, and its only critical point in
\(V\) is 0.  The actual source certificates give a **strict, uniform**
Rouché barrier on the complete circle:

\[
             \min_{|z|=R_p}|G(z)|>R_p,                 \tag{1.0}
\]

and exactly two roots, with multiplicity, of \(G(z)-y\) in \(U\) for every
\(|y|\le R_p\).  The strict gap is material for Lemma 1.1 below; an
unquantified proper degree-two restriction alone would not imply its
boundary conclusion.  Write

\[
 r=x_p,\quad \ell=x_{2p},\quad a=x_{5p},\quad
 b=x_{3p}=-t,\quad d=x_{6p}=t,\quad e=\alpha_p,\quad h=x_{4p}.
\]

The required strict orders are

\[
 \ell<a<b<0<d<e<h<r,                                   \tag{1.1}
\]
\[
 -r<-h<\ell<a<-e<b<d<e<-a<-\ell<h<r.                  \tag{1.2}
\]

The real map is increasing on \([-r,0]\) and decreasing on \([0,r]\).
Its exact endpoint values, used below, include

\[
\begin{array}{c|rrrrrrrr}
 z&-r&\ell&a&b&0&d&e&h\\ \hline
 G(z)&\ell&b&d&h&r&h&e&a
\end{array},\qquad G(r)=\ell.                          \tag{1.3}
\]

The three **actual** little filled sets of the primitive period-three
renormalization are

\[
 K_0=[b,d],\qquad K_1=[h,r],\qquad K_2=[\ell,a].        \tag{1.4}
\]

The central \(G^3\)-restriction with filled set \(K_0\) straightens to
\(Q(z)=z^2-2\).  Its critical portrait is
\(0\mapsto b\mapsto d\mapsto d\).  A competing degree-two period-two
restriction is excluded by the direct two-critical-point proof in the
bridge note, §2; no application of McMullen's theorem to a degree-\(2^p\)
polynomial is needed here.

The ambient Misiurewicz filled set is a dendrite.  The minimal connected hull
of the three little sets is consequently the actual KKL Hubbard continuum

\[
 T=[\ell,r],\qquad T'=G^{-1}(T)\cap V=[-r,r].          \tag{1.5}
\]

For the second equality, both real inverse branches already give the entire
degree-two fiber of every point of \(T\), with the critical fiber counted
with multiplicity.  Thus no additional nonreal inverse part can lie in
\(V\).  The one added component is

\[
 X=[-r,\ell),\qquad \overline X=[-r,\ell].             \tag{1.6}
\]

Set

\[
 \Omega=U\setminus T,\qquad \Omega'=V\setminus T',
 \qquad g=G:\Omega'\to\Omega,\qquad
 \iota:\Omega'\hookrightarrow\Omega.
\]

The first map is an unbranched degree-two cover.  The second is the actual
inclusion.  In particular \(X\subset\Omega\) is target **interior**.  No
pointwise extension of \(\iota\) sends the sides of \(X\) to the target
ideal tip.

For \(3\le p\le12\), the associated parameter cells and orders are recorded
in the [finite physical certificate](../real_primitive_tip_family_unconditional_20261116/NOTE.md).
For \(p\ge13\), the input is the [written signed-chart theorem](../real_primitive_tip_family_all_p_20261116/NOTE.md).
The passage from the proper restrictions to (1.4)–(1.5) is the written
Douady–Hubbard/dendrite argument in the bridge note.  These are the exact
prerequisites of the present theorem, rather than an assumed ideal marking.

### Lemma 1.1 — the actual source boundary is regular by the strict barrier

For the specific component \(V\) above, \(\partial V\) is an analytic Jordan
curve, and \(\overline V\) lies inside a slightly larger proper degree-two
source disk on which 0 is the only critical point.

**Proof.** Compactness of \(|z|=R_p\) and (1.0) give
\(\epsilon>0\) such that \(|G(z)|>R_p+\epsilon\) on that circle.  The same
Rouché count is then valid for every \(|y|\le R_p+\epsilon\): no zero can
cross the circle as \(y\) varies, and the count is two at \(y=G(0)\).
Let \(W\) be the component of \(G^{-1}(D(0,R_p+\epsilon))\) containing 0.
The boundary barrier makes \(W\Subset U\).  It is a disk: the maximum
principle fills the interior of every Jordan curve in a component of a
polynomial inverse image of a disk.  Its proper degree is two, since the
double zero at 0 in the fiber of \(G(0)\) already exhausts the two available
zeros in \(U\).  Riemann–Hurwitz therefore says that 0 is its only critical
point, counted with multiplicity.

The central preimage of \(D(0,R_p)\) inside \(W\) is \(V\), and properness
gives \(\overline V\Subset W\).  Its boundary is a level set
\(|G|=R_p\) disjoint from 0; thus \(G'\ne0\) there.  It is consequently a
compact analytic one-dimensional submanifold.  The preimage of a thin
round annulus about \(|y|=R_p\) is a connected annulus: the monodromy around
the single branch value \(G(0)\) interchanges the two sheets.  Hence there
is one boundary component, an analytic Jordan curve.  \(\square\)

In particular, a proper target path has a continuous physical extension
to its two endpoints, and every maximal open component of its intersection
with \(\Omega'\) has ideal endpoints.  At an interior point of \(T'\), a
connected tail must eventually remain in one of the two local slit banks;
at a slit tip there is a single access; at \(\partial V\), use its Jordan
collar.  Thus these maximal components really are the proper source
components used in A.3.2, including for paths with many such components.
This fact will be used in the uniqueness argument in §3.

## 2. The hyperbolic ideal circles and every deck access

### Lemma 2.1 — the actual slit collar is the full inner ideal circle

Let \(D\) be any bounded simply connected plane domain and
\(L=[u,v]\Subset D\), \(u<v\).  Put

\[
 m=(u+v)/2,\qquad s=(v-u)/2,\qquad
 J_L(w)=m+\frac{s}{2}(w+w^{-1}),\quad |w|>1.            \tag{2.1}
\]

Then \(J_L\) maps the exterior disk conformally onto
\(\mathbb C\setminus L\).  The inner hyperbolic ideal circle of
\(D\setminus L\), as defined in KKL Appendix A.1, is identified with
\(|w|=1\) by (2.1).  It has exactly two accesses above every interior point
of \(L\), and one at each terminal point.  This identification accounts for
all deck translates, not just a finite set of chosen crosscuts.

**Proof.** Solving the quadratic equation in \(w\) gives reciprocal roots.
Off the slit exactly one has modulus greater than one.  The derivative
of \(J_L\) is nonzero for \(|w|>1\).  This proves conformal bijectivity.

Let \(A=J_L^{-1}(D\setminus L)\).  Compact containment of \(L\) in \(D\)
gives \(\{1<|w|<1+\epsilon\}\subset A\) for some \(\epsilon>0\); boundedness
of \(D\) bounds \(A\) above in modulus.  It is a doubly connected domain
of finite positive modulus.  The annulus uniformization theorem gives a
conformal equivalence with \(1<|\zeta|<e^H\), \(0<H<\infty\), with the
inner boundary components matched.  On the inner analytic circle this
equivalence and its inverse extend by Schwarz reflection.  Thus their
restrictions are inverse circle homeomorphisms.  This step requires no
Jordan assertion about the other boundary component of \(D\).

The round annulus is covered by the strip \(0<\Re z<H\), with deck
translation \(z\mapsto z+2\pi i\).  A conformal map from this strip to the
disk conjugates that translation to a hyperbolic Möbius transformation.
Its limit set consists of its two fixed points.  The two boundary lines of
the strip map to the two components of the disk boundary minus that limit
set.  Quotienting each line by \(2\pi i\mathbb Z\) gives exactly the two
circles in KKL's \((\partial\mathbb D\setminus\Lambda)/\Delta\).
No further ideal points survive this quotient.  The preceding reflected
identification identifies the inner one with the full Joukowski circle.

On that circle,
\(J_L(e^{i\theta})=m+s\cos\theta\).  For \(0<\theta<\pi\), approaching
radially from \(|w|>1\) gives the upper slit access; for
\(-\pi<\theta<0\), it gives the lower.  At \(w=1,-1\), the two neighboring
banks meet in a single circle point.  These are all points of the circle,
which proves both the access count and completeness.  \(\square\)

The invoked standard analytic inputs are annulus uniformization and Schwarz
reflection across an analytic boundary arc.  The explicit strip computation
is the link to the *hyperbolic* ideal boundary that is missing from a mere
count of local Euclidean sectors.  The outer component is represented by
the other strip boundary line even when no physical Jordan boundary has
been asserted.  It receives one whole-component marking atom here.

### Lemma 2.2 — relative-endpoint classes retain their integer winding

Use the logarithmic Joukowski cover of \(D\setminus L\), and let \(B\) be a
proper connected arc of its inner ideal circle.  A component \(\widetilde B\)
of its lift is an interval on the line \(\Re z=0\), of length at most
\(2\pi\); the equality case is a punctured circle, with its endpoints
omitted.  For a proper path \(\gamma\) with its two endpoints in \(B\), fix
the lift of its first endpoint in \(\widetilde B\).  Then

\[
 \gamma\text{ is subordinate to }B
 \quad\Longleftrightarrow\quad
 \text{its lifted second endpoint belongs to }\widetilde B.   \tag{2.2}
\]

**Proof.** The logarithmic lift of \(A\) is simply connected.  Any two paths
with the same lifted endpoints are homotopic relative to them.  If both
endpoints belong to \(\widetilde B\), a representative can be placed in any
chosen thin collar of the compact boundary interval between those endpoints.
Projecting gives subordination.  Conversely, a path in a sufficiently thin
collar of \(B\) lifts to a collar of one and the same \(\widetilde B\).
Relative-endpoint homotopy preserves the lifted second endpoint.  This proves
necessity.  If \(B\) is the entire boundary circle, all integer winding
classes with both endpoints on that circle are subordinate; this is the
separate whole-component case.  \(\square\)

Consequently the homotopy data are not just two atom labels.  With fixed
endpoint representatives they include an integer deck displacement.  The
criterion (2.2) quantifies over **every** proper path.  It preserves and
reflects the A.1 exclusion of paths subordinate to at most two atoms,
simplicity, laminations, and the minimal base and ends used to define a
Wave.  This proves the complete path-class part of the marking comparison.
The same strip argument handles paths ending on the outer circle; paths
between the two different boundary components are not subordinate to an arc
of one boundary component.

## 3. The actual inclusion restriction, including the full root fiber

Use coordinates increasing from the left tip along the upper bank.  Set

\[
 m=(\ell+r)/2,\qquad s=(r-\ell)/2,
\]
\[
 L(q)=m-s\cos(2\pi q),\qquad L'(q)=-r\cos(2\pi q),
 \qquad q\in\mathbb R/\mathbb Z.                       \tag{3.1}
\]

Here \(L,L'\) are landing projections of the full ideal circles of \(T,T'\)
obtained in §2.  The upper banks have \(0<q<1/2\).  Define

\[
 A(y)=\frac1{2\pi}\arccos\frac{m-y}{s},\qquad
 \eta=\frac1{2\pi}\arccos\frac{-\ell}{r}\in(0,1/4).
\]

There is an explicitly derived monotone degree-one **contour code**

\[
 q_0(u)=
 \begin{cases}
 0\pmod1,&u\in[1-\eta,1]\cup[0,\eta],\\
 A(L'(u)),&\eta\le u\le1/2,\\
 1-A(L'(u)),&1/2\le u\le1-\eta.
 \end{cases}                                             \tag{3.2}
\]

On the common old slit it matches both the physical point and the bank.
Its one non-singleton fiber is

\[
 B_X=q_0^{-1}(0)=[1-\eta,1]\cup[0,\eta].                \tag{3.3}
\]

This is the complete two-bank boundary of the attachment, including the two
distinct source gates at \(\ell\) and its far tip \(-r\).  Formula (3.2)
is **not the boundary extension of the holomorphic inclusion**.  It records
relative path subordination, and will only be used for that purpose.

### Lemma 3.1 — connected-arc pullback in a pair of nested real slits

For an open or closed connected inner ideal arc \(J\), the connected-arc
restriction defined by the proper-path criterion of KKL A.3.2 is

\[
                  \iota^*J=q_0^{-1}(J).                 \tag{3.4}
\]

The same formula holds for a half-open arc and for a singleton.  In
particular the source-root fiber is the **closed** arc \(B_X\).  Maximality
here is among all subsets of the full source ideal boundary, as in A.3.2,
not only among connected arcs on its inner circle.

**Proof.** On either old bank \(T\setminus\{\ell\}\), the actual inclusion
extends to the same ideal point.  Thus its restriction there is the
ordinary bank-preserving inverse correspondence of (3.2).

The only part of \(T'\) absent from \(T\) is the connected interval \(X\),
attached at the single terminal access 0 of \(T\).  A source collar of its
complete boundary has two gates, one on each bank above \(\ell\), joined
around \(-r\).  In the target this collar, with its ends completed along
\(X\) when necessary, can be contracted through the target interior to an
arbitrarily small collar of the old terminal access.  Thus the full block
\(B_X\) is eligible precisely when that access belongs to \(J\).  No proper
sub-block can replace it: completing a collar crosscut on either bank of
\(X\), or around its far end, gives a proper target path subordinate to the
old terminal access.  All of those source collar classes must be retained.

To check the defining implication for an arbitrary path, suppose a target
proper path has one source restriction and that restriction is subordinate
to \(q_0^{-1}(J)\).  By Lemma 1.1, every maximal source intersection is
proper, so there is exactly one such component.  Both of its endpoints
are on the inner source circle.  Each omitted initial or final tail is
connected and lies in the complement of \(\Omega'\) within \(\Omega\).
That complement consists of the outer part \(\Omega\setminus V\) and the
attached interval \(X\), separated by the positive gap \(T'\Subset V\).
At an inner endpoint the tail therefore stays in \(X\), if it is nonempty;
it cannot reach the outer part without creating another proper source
component.  Contract those
portions toward the old root as just described.  The endpoints now lie in
\(J\), and the lifted boundary interval is carried into the chosen lift of
\(J\).  The integer deck displacement is unchanged: this is a contraction
of an attached interval, while the annular generator surrounding \(T'\)
maps to the generator surrounding \(T\).  Lemma 2.2 therefore says that the
target path is subordinate to \(J\).

For maximality, first enlarge the candidate source arc beyond either
endpoint.  If the new part is on an old bank, take a sufficiently thin
source collar path whose corresponding target endpoint lies outside \(J\).
The same path in the target fails subordination to \(J\).  If the enlargement
enters the attachment block while 0 is excluded from \(J\), complete a
source collar crosscut to the old terminal access along \(X\).  The completed
target path has a unique source restriction but has an endpoint at 0, so
again it is not subordinate to \(J\).  Both constructions can be made in a
small collar of the real slits; they have no extra outer excursion.
These are pointwise exclusions, not just exclusions of connected
enlargements: a small source collar loop with both ideal endpoints at any
extra inner access is subordinate to that singleton, and the same
completion gives the forbidden target endpoint.  Finally, an extra outer
source access is excluded by a small collar loop based at that access on
the analytic curve \(\partial V\).  Complete both of its endpoints through
\(U\setminus\overline V\) to \(\partial U\).  The target path has exactly
that one proper source component, subordinate to the added singleton,
but its outer endpoints prevent subordination to the inner \(J\).
Consequently no disconnected inner or outer access can be adjoined.
If an
endpoint of \(J\) is included, its corresponding access (or the whole root
fiber) is included.  If it is excluded, that access or fiber is excluded.
This proves (3.4), including the endpoint conventions.  It is a direct
real-slit proof of the attachment rule in KKL Proposition 6.5; no global
monotone quotient is assumed for a general KKL carrier.  \(\square\)

An equivalent precise endpoint rule is useful.  For a monotone lift
\(\widetilde q_0\), write
\(\widetilde q_0^{-1}(x)=[u^-(x),u^+(x)]\).  Then

\[
 \widetilde q_0^{-1}((a_0,b_0))=(u^+(a_0),u^-(b_0)),\qquad
 \widetilde q_0^{-1}([a_0,b_0])=[u^-(a_0),u^+(b_0)].    \tag{3.5}
\]

The analogous half-open rules choose the indicated endpoint independently.
Thus closing an arbitrary finer arc **can** add an entire attachment block.

The outer target whole-circle atom pulls back to the source outer circle.
For completeness, Lemma 1.1 makes every maximal source component proper.
If there is only one and both its endpoints are outer, its omitted tails
stay in \(\Omega\setminus V\), by the same separation argument.  They
cannot reach an inner target endpoint without passing through an additional
source component.  Thus both target endpoints are outer.  Every such
relative path class is subordinate to that whole circle, by the strip
criterion.  Inner collar paths exclude adjoining any inner access to this
pullback.  The inclusion is not asserted proper on the source outer circle;
that physical curve lies inside \(U\).

## 4. Deriving the native marking, covering, and refinement

KKL §2.5 defines the vertices from the actual small filled sets, branch
points, and dividing fixed point.  Here the tree is an interval and has no
branch point.  Its vertex set is
\(K_0\cup K_1\cup K_2\cup\{e\}\).  In the full access circle of §2, the
induced marking therefore has the five paired cut positions

\[
                       a,b,d,e,h.                       \tag{4.1}
\]

Index the ten target atoms starting with the left terminal vertex side
\(I_0\), then the upper bank, the right terminal side \(I_5\), and the lower
bank in reverse.  Thus the edge-side atoms are
\(I_1,I_3,I_4,I_6,I_7,I_9\); the remaining four are the small-Julia sides.

By (1.2)–(1.3), evenness, and monotonicity, the complete source preimage of
the five paired cuts consists of the ten physical cuts

\[
                -h,\ell,a,-e,b,d,e,-a,-\ell,h.           \tag{4.2}
\]

Index its twenty atoms \(S_0,\ldots,S_{19}\) by the same left-tip/upper-bank
convention.  On the negative real branch the derivative is positive, so
upper accesses map to upper accesses; on the positive branch it is
negative, so they map to lower accesses.  The critical point is on the
removed slit and creates no branch point of the annular cover.  Reading
the complete branch images gives

\[
                         g_*(S_j)=I_{j\bmod10}.          \tag{4.3}
\]

This also follows from a degree-two lift of the explicit boundary map:
on \(0\le u\le1/4\), use \(A(G(L'(u)))\); on
\(1/4\le u\le1/2\), use \(1-A(G(L'(u)))\); then extend by adding 1
when \(u\) increases by \(1/2\).  Its total increase over a source turn is
2.  This formula fixes the sheet order and treats every deck translate.

Using the physical \(q_0\) of (3.2), not (4.3), gives the following
**different** inclusion restrictions:

| Target atom | Full connected inclusion pullback | Cover-pushed atom word |
|---|---|---|
| \(I_0\) | \(S_{18},S_{19},S_0,S_1,S_2\) | \(I_8,I_9,I_0,I_1,I_2\) |
| \(I_1\) | \(S_3,S_4\) | \(I_3,I_4\) |
| \(I_2\) | \(S_5\) | \(I_5\) |
| \(I_3\) | \(S_6\) | \(I_6\) |
| \(I_4\) | \(S_7,S_8,S_9\) | \(I_7,I_8,I_9\) |
| \(I_5\) | \(S_{10}\) | \(I_0\) |
| \(I_6\) | \(S_{11},S_{12},S_{13}\) | \(I_1,I_2,I_3\) |
| \(I_7\) | \(S_{14}\) | \(I_4\) |
| \(I_8\) | \(S_{15}\) | \(I_5\) |
| \(I_9\) | \(S_{16},S_{17}\) | \(I_6,I_7\) |

For example, the upper \(I_1\)-bank is exactly \((a,b)\); the only additional
source cut in it is \(-e\), so its complete source block is \(S_3,S_4\).
The \(I_0\) block consists of the old upper/lower portions over \((\ell,a)\)
and **all** of \(B_X\).  The other rows follow in the same way from (4.2).
Internal source cuts in every row are included, while its two outer cuts
are omitted for an open input.

These ten blocks are consecutive and disjoint.  Their endpoints are
source covering cuts; hence the twenty-atom covering marking refines the
inclusion marking.  Its end-atoms are on the old slit, so the inclusion
is end-proper on every inner block.  Only \(I_0\)'s block contains
nonproper interior sides.  The two outer whole-circle atoms are compatible
with the covering and the outer restriction described in §3.

Thus the hypotheses of KKL A.12 are checked on these actual surfaces,
rather than inferred from table consistency.  Its filtered restrictions
are literally the proper components of the same physical path, with the
A.1 short classes and single-inclusion-block classes removed.  Lemma 2.2
identifies those classes in both directions.  Their number can depend on
the geometric representative, as the archived crossing/avoiding example
already proves; the present result does not replace the operation by a
function on endpoint words.

This completes the selected-slit ideal-marking implication H2 from the
physical input package.  Since the physical and model domains are the
same subsets of the same \(z\)-plane, the identification is also the
conformal identity on their interiors.  No conformal-width invariance is
claimed for the nonconformal code \(q_0\).

## 5. Exact endpoint dynamics and the sharp five-step theorem

Let \(\Phi=g_*\iota^*\) act on connected inner ideal arcs.  Assign integer
labels to the target cuts so that \(I_j=(j,j+1)\) in a lifted indexing
coordinate, modulo 10.  Source atoms have period 20.  The table just derived
gives the target-cut lift

\[
 \begin{split}
 (L(0),L(1),\ldots,L(10))
   &=(-2,3,5,6,7,10,11,14,15,16,18),\\
 L(k+10)&=L(k)+20.                                      \tag{5.1}
 \end{split}
\]

This is a lift on **cuts**, not a claim that the physical map is piecewise
affine in Euclidean angle.  Every target marked cut has one \(q_0\)-preimage:
the attachment root lies strictly *inside* \(I_0\), not at a marked cut.
Moreover (1.3) sends each physical marked cut to another marked cut, with
the bank determined as above.

### Theorem 5.1 — all marked intervals saturate; closures agree

Every nonempty positive-length connected multi-interval \(J\) in the
original ten-atom marking satisfies

\[
 \Phi^5(J)=C_T,\qquad
 \Phi^n(\overline J)=\overline{\Phi^n(J)}\quad(n\ge0). \tag{5.2}
\]

The same five-step bound holds for half-open intervals with original marked
endpoints.  It is sharp: \(I_3\) and \(I_7\) first saturate at step 5.

**Proof.** Because the endpoint fibers are singletons, (3.5) says that an
open lifted interval \((a_0,b_0)\) with original cut endpoints is sent to
\((L(a_0),L(b_0))\) modulo 10, with the same endpoint convention.  If the
lifted span exceeds 10, the image is the full circle.  If it equals 10,
an open image is a **punctured circle**, while an image including either
endpoint is the full circle.  A span below 10 is the corresponding proper
arc.  This is the full endpoint rule, including the possible equality case.

In particular singleton endpoint fibers give
\(\iota^*\overline J=\overline{\iota^*J}\).  The continuous covering map
commutes with closure of these compact arcs.  Images have original marked
endpoints or are full/punctured circles; induction proves the second
identity in (5.2).  This is a special property of this family and marking,
not a contradiction of KKL's general open/closed warning.

The exact saturation times of the ten whole atoms are

\[
             (2,4,4,5,4,3,4,5,4,4).                    \tag{5.3}
\]

Here is a hand-check of the longest orbit.  For \(I_3\), the successive
lifted atom words are

\[
\begin{split}
 I_3&\longmapsto I_6\longmapsto(I_1,I_2,I_3)\\
    &\longmapsto(I_3,I_4,I_5,I_6)\\
    &\longmapsto(I_6,I_7,I_8,I_9,I_0,I_1,I_2,I_3)
      \longmapsto C_T.
\end{split}                                             \tag{5.4}
\]

All the first four are proper open intervals.  The last input pulls back
to a source span of 16, strictly greater than 10; therefore its image is
the whole circle.  Reflection gives \(I_7\).  The remaining times follow
from the same rows: \(I_0\) has a five-atom first image whose next source
span is 11; \(I_5\to I_0\); \(I_2,I_8\to I_5\); and the edge atoms use the
displayed three remaining nontrivial rows.  Every positive marked
multi-interval contains a whole atom, and \(\Phi\) is monotone, proving the
bound.  \(\square\)

The equality case in the covering rule is real.  For example the open
target interval with cut endpoints 2 and 8 has source span
\(L(8)-L(2)=10\); it maps to a punctured circle, while its closure maps to
the entire circle.  Nevertheless their closures agree, exactly as (5.2)
says.

For the **finer unmarked root access**, the fiber is different.  In the
source cut indexing its closed lift is \([19,22]\), with interiors
\(S_{19},S_0,S_1\).  Its covered image has closed cut span \([9,12]\), hence

\[
             \Phi(\{0\})\supset I_9\cup I_0\cup I_1.  \tag{5.5}
\]

Closing a fine arc at that access can therefore add a positive interval,
as (3.5) predicts.  A finite argument that discards this fiber would fail
the subarc theorem below.

## 6. Arbitrary positive zero-edge subarcs: escape and its clock

The old real edges are

\[
 E_0=(a,b),\qquad E_1=(d,e),\qquad E_2=(e,h).
\]

Call an inner ideal arc **zero-edge** if it is contained in one of the four
vertex-side atoms \(I_0,I_2,I_5,I_8\).  This includes arbitrarily small arcs
inside those atoms; it is not a whole-atom convention.

### Theorem 6.1 — every nondegenerate zero-edge subarc saturates

Let \(J\) contain a nonempty open subarc of one of those four atoms.  Then
some \(\Phi^n(J)\) contains a complete side of \(E_0\), and a later iterate
is \(C_T\).  More precisely, select an interior compact nondegenerate
subarc, avoiding terminal tips unless one is already present.  In at most
\(d\le2\) iterations it either exposes the root or becomes a side arc over
a nondegenerate real interval \(A\subset(-t,t)\) of \(K_0\).  Let
\(\chi:K_0\to[-2,2]\) be the real interval conjugacy furnished by the
genuine \(G^3\)-straightening, and set

\[
 \vartheta(x)=\frac1\pi\arccos\frac{\chi(x)}2,\qquad
 \delta=|\vartheta(A)|>0.                               \tag{6.1}
\]

Then a complete old edge occurs by

\[
 d+3\left(\left\lceil\log_2(1/\delta)\right\rceil+1\right),
                                                               \tag{6.2}
\]

and saturation occurs within two more steps, giving (0.1).

**Proof.** First isolate the mechanism at the actual root.  The critical
point \(0\in K_0\) has two slit accesses in \(C_T\).  An open side arc
containing one of them maps under the annular covering to an open arc
containing the single right tip \(r\).  The next image contains the single
left tip \(\ell\).  There has been no attachment loss: the first two
inclusion restrictions are proper at the relevant old-side accesses.
On the next restriction the **entire** block \(B_X\) is inserted by Lemma
3.1.  Its image is the two-sided contour of

\[
                  G(\overline X)=[\ell,b],             \tag{6.3}
\]

which contains all of \(K_2\) and both complete sides of \(E_0=(a,b)\).
Equivalently this is exactly the block in (5.5), including its intervening
cuts.  Thus an open arc containing a critical access exposes the full old
edge in **three** iterations of \(G\).  The exposed block contains \(I_0\),
which saturates in two further steps by Theorem 5.1.

Until this event, a side subarc strictly inside a little interval is
transported by the actual real branch and its corresponding slit bank.
This follows from (3.4), since the only nontrivial inclusion fiber is at
\(\ell\).  If a \(K_1\)-arc contains its terminal access \(r\), it reaches
\(\ell\) in one step and exposes the attachment in the next.  If a
\(K_2\)-arc already contains \(\ell\), it exposes it immediately.
Otherwise a subarc of \(K_1\) reaches a \(K_0\) side in two steps, and a
subarc of \(K_2\) does so in one, by (1.3)–(1.4).  A \(K_0\) side needs
no alignment step.

The hybrid straightening of the actual quadratic-like return restricts
to a homeomorphism of its filled interval with \([-2,2]\).  It sends
\(b\mapsto-2\), \(d\mapsto2\), and \(0\mapsto0\), so it is increasing on
the interval.  Therefore \(\vartheta\) conjugates \(F=G^3|_{K_0}\) to the
tent map

\[
 \tau(s)=\begin{cases}2s,&0\le s\le1/2,\\
                       2-2s,&1/2\le s\le1.
        \end{cases}                                    \tag{6.4}
\]

While the angular interval avoids \(1/2\) in its interior, its length
is doubled at each return.  If all of its first \(N+1\) images avoided
\(1/2\), each would lie in one half-interval and have length at most \(1/2\).
For \(N=\lceil\log_2(1/\delta)\rceil\), however, its putative length at
time \(N\) is \(2^N\delta\ge1\), a contradiction.  Thus for some
\(k\le N\), \(F^k(A)\) contains 0 in its interior.  Before that time the
native arc has stayed in the corresponding little-set sides, unless an
earlier root exposure has already proved the result.  At that time the
three-step critical-access mechanism gives (6.2) and then (0.1).

If the original \(J\) has closed endpoints or crosses a marked endpoint,
work with the chosen open interior subarc.  Monotonicity of the actual
restriction and covering puts all of its images inside the images of
\(J\).  Thus no unjustified interchange of closure and restriction is used
for these finer subarcs.  \(\square\)

This proof uses a genuine return on a named little filled interval and a
complete attachment fiber.  The Perron eigenvalue of the old-edge matrix
does not enter it.

### Theorem 6.2 — a uniform bound over all positive subarcs is false

For this same fixed physical \(G\), and for every integer \(N\ge1\), there
is a positive zero-edge open subarc whose first \(3N\) images contain no
old edge.

**Proof.** In the angular coordinate (6.1), choose

\[
 A_N=(2^{-N-3},2^{-N-2}).                               \tag{6.5}
\]

For \(0\le j\le N\), its \(j\)-th tent image is
\((2^{j-N-3},2^{j-N-2})\subset(0,1/2)\).  Pull it back to a side of \(K_0\).
Every \(G^3\)-block remains on one real branch, and its intermediate phases
stay in the interiors of \(K_1\) and \(K_2\), away from the attachment tip.
There is therefore no added root block and no old edge during those
\(3N\) iterations.  The arc is nondegenerate.  This proves the claimed
absence of a size-independent bound.  \(\square\)

It remains possible to have a periodic **singleton** access with zero edge
mass.  Theorem 6.1 requires a nondegenerate arc; it does not discard that
distinction.  Likewise a positive-width Wave must be connected to these
arc images by an actual descendant/crest theorem before either result can
be used as a Wave estimate.

## 7. What this supplies to the width problem

Lemma 2.2 gives one useful piece of selected-family H3 without an extremal
calculation.  Every A.1 parent with base \((I_9,I_0,I_1)\) lifts, after fixing
one endpoint lift, into exactly the left-tip relative-endpoint class in the
logarithmic Joukowski cover.  It cannot acquire an extra deck turn or use
the right-tip class while remaining subordinate to that base.  The same
statement holds for every source child with base \((S_1,S_2,S_3)\) or its
reflected base.  Thus the endpoint classes in the archived full-path
envelopes contain **every** such physical leaf, including arbitrary
noncircular excursions.

For an admissible nonnegative density \(\widetilde\rho\) on the full
selected lift, its square-periodization defines a density downstairs:

\[
 \rho(\pi z)^2|\pi'(z)|^2=\sum_{n\in\mathbb Z}
                  \widetilde\rho(z+2\pi i n)^2.         \tag{7.1}
\]

The Jacobian explicitly transports the density to the physical complex
coordinate; the derivative of \(\pi\) is periodic and nonzero in the
covering domain. Tonelli identifies its area with the total
lifted area.  Along the selected lift it dominates
\(\widetilde\rho\), so every physical leaf retains its length lower bound.
This proves the direction of the full-path upper comparison.  It does
not prove a Schwarz–Christoffel competitor's minimal base, any particular
omitted-energy subtraction, or the claimed numerical strict defect.
Those remaining statements need their own domain and foliation checks.
The separate [H3_WIDTH.md](H3_WIDTH.md) now supplies those checks, including
both child widths' positivity and the corrected strict independent defect.
It uses the present note as its actual ideal-class input; the interval
results in this note alone do not imply that width conclusion.

In particular, the new interval saturation theorem must not be substituted
for a theorem about restrictions of every leaf or inheritance of a closed
crest by one selected child.  The existing two-child example still rules
out that shortcut.

## 8. Reproduction, adversarial distinctions and source locators

Run from the repository root:

```sh
python3 -B research/independent_audits/maximal_native_wave_20261123/verify.py
```

The checker independently propagates outward 640-bit dyadic intervals from
the ten already isolated \(p=3,\ldots,12\) parameter cells.  It checks the
whole real derivative sign, brackets the dividing fixed point, derives the
covering and inclusion labels from physical interval samples after the
complete-cut argument, and derives (5.1) from those labels.  It checks all
370 nontrivial original marked open/closed/half-open states, the sharp
five-step bound, closure commutation, four exact open-halfturn examples,
and deck-equivariance.  It also checks 2,780 rational tent intervals and
long-avoidance examples through \(N=1000\).  These are finite regressions
of the written proof, not its analytic justification.  Only this new
directory's result manifest is written with `--write`.

The exact analytic inputs and uses are:

| Source | Result used here | Use and checked hypotheses |
|---|---|---|
| Douady–Hubbard, *On the dynamics of polynomial-like mappings* (1985), [Proposition 2 and Theorem 1](https://doi.org/10.24033/asens.1491) | Connectedness and straightening of the actual degree-two return | The return has one trapped critical point; the three-point critical portrait selects \(z^2-2\). The full restricted filled set is the named interval by the bridge proof. |
| Annulus uniformization and Schwarz reflection across analytic arcs | Round-annulus model and inner-boundary extension | The Joukowski image contains a full inner collar and is bounded; its inner circle is analytic. This inner-circle identification uses no outer Jordan regularity; the distinct proper-component argument uses Lemma 1.1. |
| Kahn–Kapiamba–Lyubich, [arXiv:2606.27272v1, §2.5](https://arxiv.org/html/2606.27272v1#S2.SS5) | Definition of the native Hubbard continuum and its vertices | The actual disjoint little filled intervals and dendrite hull give \(T\); there are no extra branch vertices. |
| KKL [§6.1, Propositions 6.5–6.6](https://arxiv.org/html/2606.27272v1#S6.SS1) | Attachment-complete boundary restriction and combinatorial marking | The real-slit proof in §3 explicitly realizes its complete attachment rule; §4 derives the refinement on the physical cuts. |
| KKL [Appendix A.1](https://arxiv.org/html/2606.27272v1#A1.SS1) | Hyperbolic ideal boundary, subordination, marked paths, Waves | The strip computation identifies the exact boundary quotient; Lemma 2.2 treats all deck classes and the short-path exclusion. |
| KKL [Appendix A.3.2, Proposition A.12](https://arxiv.org/html/2606.27272v1#A1.SS3.SSS2) | Proper-component restriction and refined path-chain condition | The source marking refines the derived inclusion blocks; the operation remains representative-dependent and set-valued. |
| KKL [Appendix A.3.4](https://arxiv.org/html/2606.27272v1#A1.SS3.SSS4) | Distinct cover/inclusion composite and open/closed warning | The endpoint-fiber rule (3.5) explains both the original-cut commutation and the finer root-cut failure. |

The primary KKL v1 HTML was retrieved directly from arXiv and checked at
the cited sections.  The imported statements are attributed to their
authors; the new real-slit proof, sharp local clock, and subarc escape/no-
uniform-time claims are the assertions submitted here for review.

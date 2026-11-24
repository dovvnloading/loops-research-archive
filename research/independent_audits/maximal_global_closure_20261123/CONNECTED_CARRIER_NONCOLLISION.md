# Replacing a connected parent contact by the selected carrier

Date: 2026-11-23  
Status: conditional strengthening of the reviewed
[monodromy collision note](MONODROMY_COLLISION.md). The connected contact
subsegment of the parent is no longer required. Actual ordered proper
retained occurrences and their canonical contact endpoints remain
required. No global stationary N2 or MLC conclusion is claimed.

AI disclosure: GPT-6 Astra Pro was used for proof search, source comparison,
and drafting. Independent review is by collaborating AI agents; no new
human mathematical verification is represented.

Target interface: **KKL_STATIONARY_TWO_SIDED_WAVE_NONCOLLISION**.
This addendum preserves the earlier reviewed result and proves a stronger
conditional route by a different argument.

## 1. The improvement

In Theorem 4.1 of MONODROMY_COLLISION.md, the two specified occurrences
were separated by a connected parent subsegment
\(E=\alpha([s,t])\) lying in one selected deep limb. Here the intervening
parent segment may make arbitrary excursions. Instead, the two actual
contact points must lie in a connected selected carrier \(C\), whose
canonical graph maps into the closed critical target limb.

The reason this suffices is analytic:

1. The closed critical target limb is a full continuum, even when it
   is not locally connected.
2. When \(h<q\), it has a Jordan neighborhood avoiding every critical
   value of the actual covering \(P_h\).
3. The connected canonical lift of \(C\) lies in one univalent inverse
   component of that neighborhood.
4. A common pushed path subordinate to the critical contour can be
   homotoped into that neighborhood while fixing its **physical**
   endpoints. The proof keeps actual landing tails and does not assume
   that intermediate ideal homotopy paths physically land.
5. Its lift must then join the two canonical contact points. One
   occurrence would revisit the later contact of the simple parent,
   which is impossible.

Consequently a collision output must use the contour arc outside the
critical limb. The same two further selected Wave stages as in the
earlier note rule out that alternative.

No statement here creates the two proper occurrences or proves their
survival under the sequential restriction filters.

## 2. Fullness without local connectivity

### Lemma 2.1 — every subcontinuum of the physical filled set is full

Let \(K\subset\mathbb C\) be a full continuum with empty interior.
Then every subcontinuum \(H\subset K\) is full.

#### Proof

Suppose a bounded complementary component \(D\) of \(H\) existed.
Since \(K\) has empty interior, the nonempty open set \(D\) contains
a point \(z\notin K\). Fullness of \(K\) says that
\(\mathbb C\setminus K\) is connected. It is open and hence path
connected, so \(z\) can be joined there to a point sufficiently far
away to be outside \(D\). That path is also disjoint from \(H\),
contradicting the choice of \(D\). \(\square\)

A connected periodically repelling quadratic-like filled set has empty
interior: transport to its polynomial straightening and use the
classification of periodic Fatou components and the no-wandering-domain
theorem. Its fullness is part of the polynomial-like filled-set
package. This is the same imported input used in
[CUTPOINT_PRUNING.md, Section 3](CUTPOINT_PRUNING.md).

In particular the closed physical critical filled limb

\[
 H_0=\overline{\mathfrak L_0}
 =\mathfrak L_0\cup\{\alpha_F\}
 \tag{2.1}
\]

is compact, connected, and full: it is the closure of a connected
component of \(K\setminus\{\alpha_F\}\). There is no requirement that
\(H_0\) be an arc or a dendrite, and no Hubbard-carrier identification
is needed for this fact.

One may instead use the smaller closed critical tree limb when its
connectedness has been established. For the constructed full-hull
carrier in CUTPOINT_PRUNING.md that connectedness is proved by
monotone inverse images; identifying that smaller carrier with the
native one remains a separate issue. The preferred choice (2.1)
does not need this extra tree identification.

For that preferred choice there is also a proof requiring no
empty-interior input. If \(K\) is any full continuum, \(a\) a cut
point, and \(C_0\) a component with
\(\overline{C_0}=C_0\cup\{a\}\), then \(\overline{C_0}\) is full.
Indeed, a bounded complementary domain \(D\) of this closure
would lie in \(K\), by fullness of \(K\). Choose
\(p\in\partial D\setminus\{a\}\subset C_0\). The connected set
\(D\cup\{p\}\) lies in \(K\setminus\{a\}\) and meets \(C_0\),
so it lies in that component. This contradicts
\(D\cap\overline{C_0}=\varnothing\).

### Lemma 2.2 — one univalent neighborhood for the connected selected lift

Let \(P:S\to U\) be a finite proper holomorphic map, \(U\) a conformal
disk, and \(H_0\Subset U\) a full continuum containing no critical
value of \(P\). There is a Jordan disk \(V\Subset U\), containing
\(H_0\), that avoids all critical values. Every component of
\(P^{-1}(V)\) maps conformally onto \(V\).

If \(C\) is a connected set and \(\Gamma:C\to S\) is continuous with
\(P\Gamma(C)\subset H_0\), then \(\Gamma(C)\) lies in one of those
univalent components.

#### Proof

A full planar continuum has a basis of Jordan neighborhoods. One
construction is to use level curves in the exterior Riemann map;
their filled interiors decrease to the continuum. A singleton is
handled by ordinary disks. The critical values of a finite proper
holomorphic map are locally finite, so a sufficiently small such
neighborhood is contained in \(U\) and avoids them.

The restriction over \(V\) is a finite unbranched covering. Every
connected covering of a simply connected disk has one sheet, proving
the conformal assertion. The connected set \(\Gamma(C)\) is contained
in \(P^{-1}(V)\), so it lies in one component. \(\square\)

For the actual stationary iterate, Lemma 3.1 of MONODROMY_COLLISION.md
proves

\[
 \operatorname{CV}(P_h)
 \subset\{F(c),\ldots,F^h(c)\}.
 \tag{2.2}
\]

When \(h<q\), the limb rotation places this finite set outside
\(H_0\). Thus the neighborhood in Lemma 2.2 really avoids **all**
critical values of the full iterate, not just those visible in a
selected local collar.

The proved physical selected-component theorem gives the preferred
connector

\[
 C=\overline{\Omega_h},\qquad
 \Gamma=\Gamma_h|_C.
 \tag{2.3}
\]

Indeed \(\Omega_h\) is an actual connected component of
\(K\setminus\{\alpha^h\}\), and
\(F^h:\Omega_h\to\mathfrak L_0\) is a homeomorphism. Its closure
is a compact continuum in the physical filled set. Continuity of
the graph identity therefore gives

\[
 P_h\Gamma_h(C)\subset\overline{\mathfrak L_0}=H_0.
 \tag{2.4}
\]

No assertion that \(\alpha\cap C\) is connected is involved.
Nor is connectedness of any pulled Hubbard-tree limb needed. The
smaller choice \(C=\overline{\mathcal L_0^h}\) also works if its
connectedness is available, but is unnecessary.

## 3. Passing from ideal subordination to a physical-endpoint homotopy

This is the step at which a non-locally-connected boundary needs care.

Let \(T\Subset U\) be a nondegenerate full continuum. The domain
\(\Omega=U\setminus T\) is an annulus, with inner ideal circle \(C_T\).
Let \(B_0\subset C_T\) be a proper open connected arc. Assume the
following precise contour locality:

\[
 \operatorname{Imp}(e)\subset H_0
 \quad\hbox{for every }e\in\overline{B_0}.
 \tag{3.1}
\]

Here the impression is in the physical plane, and \(H_0\Subset U\)
is the closed critical target continuum above. For a native use,
\(B_0=\mathbf L_0\); (3.1) is the full critical-contour premise,
including its dividing endpoints. It is not inferred from finite
atom labels.

### Lemma 3.1 — fixing actual landing tails

Let \(V\) be an open neighborhood of \(H_0\). Let \(\delta\) be a
proper path in \(\Omega\), subordinate to \(B_0\), that has actual
physical endpoint limits \(y_-,y_+\in H_0\). If a set
\(Z\subset T\) is disjoint from \(V\), then the physical extension
of \(\delta\) is homotopic in \(U\setminus Z\), relative to
\(y_-,y_+\), to a path contained in \(V\).

#### Proof

By (3.1) and upper semicontinuity of prime-end impressions, there
is an open ideal neighborhood \(N\) of \(\overline{B_0}\) whose
physical interior satisfies

\[
 N\cap\Omega\subset V.
 \tag{3.2}
\]

For completeness, if no such neighborhood existed, points outside
\(V\) could approach the compact ideal arc \(\overline{B_0}\).
After taking subsequences, their ideal limits would converge to a
point \(e\) of that arc and their physical limits to a point of
its impression outside \(V\), contradicting (3.1).

Subordination supplies a proper representative \(\beta\) in \(N\)
and a homotopy \(H_r\), \(0\le r\le1\), from \(\delta\) to
\(\beta\), fixing the two ideal endpoints. This homotopy can be
taken through proper paths: lift the two representatives to the
universal strip with their compatible endpoint lifts, and use a
straight-line homotopy there. Interior path parameters stay in the
open strip. Thus

\[
 H_r(t)\in\Omega\quad(0<t<1)
 \tag{3.3}
\]

throughout the homotopy.

The homotopy is continuous on the compact parameter square in the
ideal compactification and fixes both ideal endpoints. There is
therefore \(\epsilon>0\) such that, uniformly in \(r\),

\[
 H_r([0,\epsilon])\cup H_r([1-\epsilon,1])
 \subset N.
 \tag{3.4}
\]

Intermediate \(H_r\) need not have the same physical landing
points. We do not use them as physical-endpoint homotopies.
Instead, for each \(r\), concatenate the following five pieces:

1. the fixed actual initial tail of \(\delta\), from
   \(y_-\) to \(\delta(\epsilon)\);
2. the track \(u\mapsto H_u(\epsilon)\), \(0\le u\le r\);
3. the middle path \(H_r|_{[\epsilon,1-\epsilon]}\);
4. the reversed track \(u\mapsto H_u(1-\epsilon)\),
   \(r\ge u\ge0\);
5. the fixed actual terminal tail of \(\delta\), from
   \(\delta(1-\epsilon)\) to \(y_+\).

Using fixed parameter intervals for the five pieces makes this a
continuous physical homotopy. At \(r=0\) it is \(\delta\), up to
inserting constant pieces. The endpoints \(y_\pm\) are fixed,
because the two actual landing tails are fixed. By (3.3), all
middle and track interiors avoid \(T\), hence avoid \(Z\).
The endpoint tails also avoid \(Z\), with their limits in
\(H_0\subset V\).

At \(r=1\), the middle belongs to \(\beta\subset N\); the two
tracks and the fixed tails lie in \(V\) by (3.2)--(3.4).
Consequently the entire final path is in \(V\). This is the desired
homotopy in \(U\setminus Z\). \(\square\)

The proof does not assume local connectivity of \(T\), singleton
impressions of the critical contour, or physical landing of any
intermediate ideal homotopy path.

## 4. Connected-carrier noncollision

### Theorem 4.1

Let \(P:S\to U\), \(I:S\to U\), \(T\), \(\Omega\), \(H_0\), and
\(B_0\) be as above. Assume

\[
 \operatorname{CV}(P)\subset T,\qquad
 \operatorname{CV}(P)\cap H_0=\varnothing,
 \tag{4.1}
\]

and assume \(H_0\) is full and satisfies the contour locality (3.1).

Let \(\alpha\) be a simple proper parent in \(\Omega\). Suppose
two actual proper occurrence paths \(\gamma^-,\gamma^+\) in
\(S\setminus P^{-1}(T)\) lift the ordered parent portions

\[
 \alpha((a,s)),\qquad\alpha((t,b)),\qquad
 0\le a<s\le t<b\le1,\quad 0<s\le t<1.
 \tag{4.2}
\]

Put \(x_-=\alpha(s)\), \(x_+=\alpha(t)\). Suppose a connected
carrier \(C\) containing \(x_-,x_+\) has a continuous canonical
lift \(\Gamma:C\to S\) with

\[
 I\Gamma=\mathrm{id}_C,\qquad P\Gamma(C)\subset H_0.
 \tag{4.3}
\]

The contact ends of \(\gamma^-,\gamma^+\) must converge in the
ambient surface \(S\) to \(\Gamma(x_-),\Gamma(x_+)\).
The intervening parent portion \(\alpha([s,t])\) is unrestricted.

Suppose both occurrences map homeomorphically under \(P\) onto
the same simple proper path \(\delta\). Then

\[
 \delta\text{ is not subordinate to }B_0.
 \tag{4.4}
\]

#### Proof

Apply Lemma 2.2 and let \(V\) be a critical-value-free Jordan
neighborhood of \(H_0\). The connected set \(\Gamma(C)\) lies
in one component \(W\) of \(P^{-1}(V)\), and
\(P|_W:W\to V\) is conformal. In particular it is injective at
both contact points and on the entire connecting lift.

If \(s<t\), simplicity of \(\alpha\) gives \(x_-\ne x_+\).
Since \(I\Gamma=\mathrm{id}\) and \(P|_W\) is injective, the two
contact images \(y_\pm=P\Gamma(x_\pm)\) are distinct and must be
the opposite endpoints of \(\delta\).

If \(s=t\), the two contact lifts are the same point of \(W\).
Were both contact ends to map to the same end germ of \(\delta\),
local injectivity of \(P\) would identify the corresponding source
germs. Their \(I\)-images would overlap on the disjoint parent
portions in (4.2), contradicting simplicity. Thus in this case
also the contact ends map to opposite ends of \(\delta\).

The two physical endpoint limits of \(\delta\) therefore exist
and equal \(y_-\), \(y_+\). Assume for contradiction that
\(\delta\) is subordinate to \(B_0\). Apply Lemma 3.1 with
\(Z=\operatorname{CV}(P)\). It gives a homotopy, relative to
these physical endpoints and inside \(U\setminus Z\), from
\(\delta\) to a path \(\delta_V\subset V\).

The unbranched covering over \(U\setminus Z\) has the usual
homotopy lifting property. Start both path lifts at
\(\Gamma(x_-)\). Since the target endpoints are fixed, their
lifted terminal endpoints agree. The lift of \(\delta_V\) stays
in the univalent component \(W\), so it ends at \(\Gamma(x_+)\).
The actual lift of \(\delta\), namely \(\gamma^-\) with its
contact end taken first, must have that same far endpoint.

Under \(I\), the earlier parent end at parameter \(a\) would
therefore be \(x_+=\alpha(t)\). If \(a>0\), this contradicts
simplicity. If \(a=0\), it makes a proper parent end converge
to an interior point of \(\Omega\), also impossible.
Thus (4.4) holds. \(\square\)

This theorem needs no Jordan-cap argument and no connectedness of
the parent's contact set. The connecting carrier may meet other
parts of the parent or contain points the parent never visits.
It is not substituted for the actual proper occurrences in (4.2).

## 5. The longer stationary horizon still works

Apply Theorem 4.1 to \(P=P_h\), \(I=I_h\),
\(B_0=\mathbf L_0\), and the selected carrier (2.3).
Use the actual critical-value statement (2.2), \(h<q\), and the
full critical-contour locality (3.1). The source occurrences must
still be sequentially retained, with the displayed canonical
contact endpoints.

Suppose their common output \(\delta_h\) is a Wave leaf and its
two marked ends belong to \(\mathbf L_0\). Theorem 4.1 excludes
the relative class subordinate to \(\mathbf L_0\). The other
relative boundary route between two ends in that proper connected
arc contains the entire complementary contour. Hence

\[
 \delta_h\text{ crests over }\mathbf L_{q-1}.
 \tag{5.1}
\]

This last step is an ideal-circle statement: a lifted connected
base containing the two endpoint lifts either lies on the
\(\mathbf L_0\) side or passes through its whole complement.
The marked end intervals lie inside \(\mathbf L_0\), so removing
the ends does not remove \(\mathbf L_{q-1}\). A whole-circle base
has the same conclusion. No physical connectedness assumption on
\(T\setminus\mathcal L_0\) is needed for this route.

If the next two actual selected outputs are Wave leaves and

\[
 F_*\{\delta_h\}=\{\delta_{h+1}\},\qquad
 F_*\{\delta_{h+1}\}=\{\delta_{h+2}\},
 \tag{5.2}
\]

Proposition A.14 gives successive crests over
\(\mathbf L_0\) and \(C_T\). The latter is impossible. This is
exactly the reviewed sequential argument of
MONODROMY_COLLISION.md, Theorem 6.1.

Consequently the choice

\[
 N=b+5,\qquad m=b+4,\qquad q>b+4
 \tag{5.3}
\]

again supplies the two extra selected stages at \(h=b+1,b+2\).
The source's high-type threshold permits the explicit inequality
on \(q\), as checked in the earlier note. It does not supply any
missing occurrence or contact-end premise.

[The exit-transfer note, Corollary 6.6](../maximal_exit_transfer_20261123/NOTE.md)
supplies the final component and whole-end degree-two typing at
this horizon. Conditional on the same two actual physical
pass-through statements, it gives
\(\mathcal W(A_{b+4})\le 2\mathcal W(\mathcal RF)\).
Its upstream canonical-occurrence and contour obligations remain
those stated here.

## 6. Exact dependency change

Relative to MONODROMY_COLLISION.md, the following condition is removed:

> The entire intervening parent subsegment between the two actual
> contact ends is a connected subset of the selected deep limb.

It is replaced by:

> The two actual canonical contact ends lie in one connected selected
> carrier whose graph image belongs to the closed critical target
> limb.

For two contacts in the same physical selected component \(\Omega_h\),
the connector is its closure. Its connectedness and selected
forward image are already proved by the predecessor theorem. Thus
this condition requires neither connected contact along the parent
nor connectedness of a native pulled tree limb. Fullness of the
closed target filled limb follows from Lemma 2.1 and empty interior
of the physical filled set, rather than from local connectivity.

The following remain explicit:

* actual location of both canonical contact ends in the same selected
  physical component \(\Omega_h\);
* the full critical-contour impression locality (3.1);
* actual ordered proper occurrences and convergence of their contact
  ends to the canonical graph points;
* survival through every required sequential filter;
* simple retained Wave projections and the compatible further
  selected outputs (5.2).

[The annular properness note, Corollary 5.2](ANNULAR_RESTRICTION_PROPERNESS.md)
removes a separate proper-landing premise for maximal raw restrictions
when the actual carrier is a full nondegenerate forward-invariant
continuum containing the critical point and the iterate domains are
hyperbolic disks. It proves the finite-annulus topology of the full
pulled carrier and ideal convergence at both ends of every maximal
lift. Actual paired canonical contact germs, their order, physical
endpoint identification, and survival through the native filters
remain required.

This is a further analytic reduction of noncollision. It does not
prove that a bypass supplies those two retained occurrences, and
does not change the open status of stationary N2 or MLC.

## Sources

The primary source labels and URLs are recorded in
[MONODROMY_COLLISION.md, Section 2](MONODROMY_COLLISION.md):
KKL v1 Sections 2.1, 2.4, 3.2, 4.1, and 6.1, and Appendix A.3.4
Proposition A.14. The canonical finite graph and its full inverse-
filled-set identities are proved in
[PQL iterate filled-graph naturality](../../mlc_unified/pql_iterate_filled_graph_naturality.md).
The physical connected selected component and its iterate are proved
in [the selected predecessor endpoint theorem, Theorem 4.3](../../mlc_unified/kkl_stationary_n2_selected_predecessor_endpoint.md).
This addendum does not identify the native Hubbard carrier; the
full critical-contour premise still has to hold for the actual
marking used in the stationary argument.

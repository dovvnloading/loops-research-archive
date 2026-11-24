# Adjacent stationary collisions force a critical cap

Date: 2026-11-23  
Base revision: ed64c7ad839dcc8b799d53379434f892fdc92a2c  
Status: a proved conditional replacement for a separate deck-noncollision
assumption. The actual adjacent retained occurrences and their connected
contact are still required. The stationary N2 gate and MLC are not closed.

AI disclosure: GPT-6 Astra Pro was used for proof search, source comparison,
and drafting. The independent review described in the integration packet
is AI-assisted; no new human mathematical verification is represented.

Target interface: **KKL_STATIONARY_TWO_SIDED_WAVE_NONCOLLISION**.
The two-occurrence binder, retained realization, and full stationary
proof-repair interfaces remain open.

## 1. What changes

The source-reduction note
[stationary two-sided noncollision](../../mlc_unified/kkl_stationary_tsnc_source_reduction.md)
isolates a possible equality of the two geometric path images in KKL's
Lemma 6.31. It proposes proving noncollision inside a selected quadratic
collar, after additionally proving that both complete occurrences stay in
that collar.

There is another route. It uses the **entire actual finite covering**
of the fiber-product iterate. Suppose two proper retained occurrences
are adjacent along one simple parent leaf and are joined by one actual
connected contact in the selected deep limb. If their simple terminal
images coincide, the common path and the image of that contact bound a
Jordan cap containing a critical value. This follows from path lifting:
a critical-value-free cap would lift injectively and make the parent
revisit its contact.

For an iterate shorter than the limb rotation period, all its critical
values lie outside the critical limb. The connected complementary
tree then lies in the cap. Thus the common output crests over the last
noncritical limb. Two further **unique, selected Wave outputs** would
crest first over the critical limb and then over the whole ideal circle,
which is impossible.

This removes the following premises from this particular conditional
route:

* confinement of the two complete portions in a chosen quadratic collar;
* a global degree-two bound on their complete routes;
* independently supplied deck-phase or endpoint-pair noncollision.

It does not produce two retained occurrences from the source's informal
word “passes through.” In particular it does not replace a disconnected
or repeated contact by a connected contact, prove proper maximal
continuation, or bypass the sequential retention filter.

## 2. Source inputs and notation

The primary source is Kahn--Kapiamba--Lyubich,
[*MLC for parabolically bounded primitive renormalization*, v1](https://arxiv.org/html/2606.27272v1):

| Source location | Exact input |
|---|---|
| [Section 2.1](https://arxiv.org/html/2606.27272v1#S2.SS1), definition of a pseudo-quadratic-like map and the finite iterates | \(f\) is a proper degree-two branched cover, \(\iota\) is an immersion, and \(\iota^{-1}(\mathfrak K)=f^{-1}(\mathfrak K)=\mathfrak K'\); the filled-set coordinate is embedded near the filled set |
| [Section 2.4](https://arxiv.org/html/2606.27272v1#S2.SS4) | The \(1/q\) limb rotation: the critical value belongs to \(\mathfrak L_1\), and the noncritical limbs map homeomorphically to their successors |
| [Section 3.2](https://arxiv.org/html/2606.27272v1#S3.SS2), paragraph before Theorem 3.6 and the paragraph after its reduction | The high-type-near-degenerate threshold permits \(q\) to exceed any prescribed constant depending on \(b\) |
| [Section 4.1](https://arxiv.org/html/2606.27272v1#S4.SS1), paragraph before Lemma 4.8 | \(\mathbf L_j\) is the full Caratheodory contour of the physical tree limb \(\mathcal L_j\) |
| [Section 6.1](https://arxiv.org/html/2606.27272v1#S6.SS1), Proposition 6.6 and the following paragraph | Combinatorial action and \(F_*\mathbf L_j=\mathbf L_{j+1}\) for \(j\ne0\), \(F_*\mathbf L_0=C_T\) |
| [Section 6.2](https://arxiv.org/html/2606.27272v1#S6.SS2), Lemmas 6.24 and 6.31 | The selected stationary subwaves, and the two proposed separator-side portions |
| [Appendix A.3.4](https://arxiv.org/html/2606.27272v1#A1.SS3.SSS4), Proposition A.14 | Crest transport for an actual unbreakable Wave and an actual pushed lamination |

The repository's
[filled-set graph naturality](../../mlc_unified/pql_iterate_filled_graph_naturality.md),
Lemma 3.1, proves for the actual finite tower

\[
 I_h=\iota_h:U^h\longrightarrow U,\qquad
 P_h=f^h:U^h\longrightarrow U,
\]
\[
 I_h^{-1}(\mathfrak K)=P_h^{-1}(\mathfrak K)=\mathfrak K^h,\qquad
 I_h|_{\mathfrak K^h}\text{ is a homeomorphism},\qquad
 P_h=F^h\circ I_h\quad\hbox{on }\mathfrak K^h.
 \tag{2.1}
\]

Write \(\Gamma_h\) for its inverse filled-set coordinate. The same note
constructs its holomorphic graph extension near every compact filled
package on which the corresponding physical iterate is defined.

The selected predecessor theorem gives the physical inverse branch
\(\phi_0\), the terminal component \(\Omega_h\), and

\[
 F^h:\Omega_h\longrightarrow\mathfrak L_0
 \quad\hbox{a homeomorphism}.
 \tag{2.2}
\]

Here \(\mathcal L_0^h\subset\Omega_h\) is the selected pulled tree limb.
For the carrier constructed in [CUTPOINT_PRUNING.md](CUTPOINT_PRUNING.md),
the terminal pruning is proved. Identification with the named native
KKL carrier still requires the explicit native-carrier premise stated
there. The present result uses an actual contact in
\(\mathcal L_0^h\setminus T\), so it never infers such a contact from a
quotient label alone.

Throughout, proper paths are actual geometric representatives.
Coincidence of their images means equality of unparametrized traces;
tagging the two source occurrences does not make the outputs distinct.

## 3. The full iterate has no additional critical values

### Lemma 3.1

Let \(c\) be the physical critical point of a pseudo-quadratic-like map
with connected filled set. For every finite \(h\),

\[
 \operatorname{CV}(P_h)
 \subset \{F(c),F^2(c),\ldots,F^h(c)\}.
 \tag{3.1}
\]

In particular, for rotation number \(1/q\) and \(h<q\),

\[
 \operatorname{CV}(P_h)\cap\overline{\mathfrak L_0}
 =\varnothing.
 \tag{3.2}
\]

#### Proof

Write a point of the finite equalizer using successive coordinates
\((z_0,\ldots,z_{h-1})\in(U')^h\), with

\[
 f(z_j)=\iota(z_{j+1}),\qquad
 I_h=\iota(z_0),\qquad P_h=f(z_{h-1}).
 \tag{3.3}
\]

Because \(\iota\) is an immersion, these equations define a smooth
local coordinate chain: each next coordinate is locally a holomorphic
function of the previous one. The chain rule says that a critical
point of \(P_h\) has \(f'(z_j)=0\) at some index \(j\).

The unique critical point of \(f\) lies in \(\mathfrak K'\). Its physical
image under \(\iota\) is \(c\). If \(z_j\) is this point, then
\(f(z_j)=F(c)\in\mathfrak K\). The equality
\(\iota^{-1}(\mathfrak K)=\mathfrak K'\), and injectivity of
\(\iota\) on that filled set, force every later coordinate to be the
unique filled-set continuation. Consequently

\[
 P_h(z_0,\ldots,z_{h-1})=F^{h-j}(c).
 \tag{3.4}
\]

This proves (3.1). It also explains why remote immersion sheets do not
introduce extra critical values here: a continuation whose immersion
image is in the filled set is forced into its unique filled-set copy.
One must use this full inverse-image axiom, not only local injectivity
near the filled set.

For \(1\le j<q\), the limb rotation gives
\(F^j(c)\in\mathfrak L_j\). The closures of different limbs meet only
at the dividing fixed point, and these postcritical points are in the
open limbs. This proves (3.2). \(\square\)

## 4. A geometric collision lemma for actual covers

The next theorem is independent of the quadratic degree and of any
selected collar.

### Theorem 4.1 — a collision forces a critical value in the cap

Let \(P:S\to U\) be a finite proper holomorphic map of Riemann surfaces,
where \(U\) is a conformal disk. Let \(I:S\to U\) be a holomorphic
immersion, and let \(T\Subset U\) be a full continuum. Set
\(X=U\setminus T\) and \(X'=S\setminus P^{-1}(T)\).

Suppose the following actual data are given.

1. A simple proper parent path \(\alpha\) in \(X\).
2. Numbers \(0<s\le t<1\) for which
   \(E=\alpha([s,t])\subset X\) is either an arc or one point, and a
   continuous lift \(\Gamma:E\to S\) with \(I\Gamma=\mathrm{id}\).
3. The map \(P\Gamma\) is injective on \(E\), and
   \(\eta=P\Gamma(E)\subset T\). The map \(P\) is unramified near the
   two endpoints of \(\Gamma(E)\).
4. Two proper occurrence paths \(\gamma^-,\gamma^+\) in \(X'\).
   Their \(I\)-images are respectively the two adjacent open portions
   \(\alpha((a,s))\), \(\alpha((t,b))\), for some
   \(0\le a<s\le t<b\le1\). At their contact ends they converge in
   the ambient surface \(S\) to
   \(\Gamma(\alpha(s))\), \(\Gamma(\alpha(t))\), respectively.
5. The two \(P\)-images coincide with the same simple proper target
   path \(\delta\), and \(P\) maps each occurrence homeomorphically
   onto that path.

Then the contact endpoints correspond to opposite ends of \(\delta\).
The union

\[
 C=\delta\cup\eta
 \tag{4.1}
\]

is a Jordan curve, with \(\eta\) interpreted as a point when \(s=t\).
If \(C\) avoids the critical values of \(P\), its bounded Jordan domain
contains a critical value of \(P\).

#### Proof

Write \(x_-=\alpha(s)\), \(x_+=\alpha(t)\) and
\(y_\pm=P\Gamma(x_\pm)\). If \(s<t\), injectivity of \(P\Gamma\)
gives \(y_-\ne y_+\), so the contact ends necessarily correspond to
the two different ends of \(\delta\).

If \(s=t\), suppose instead that the two contact ends correspond to
the same end germ of \(\delta\). Both source germs then converge to
the same point \(u=\Gamma(x_-)\). On a neighborhood of \(u\), \(P\)
is injective. The two lifts of the same sufficiently short end germ
therefore coincide. Their \(I\)-images overlap on the two disjoint
parameter portions of \(\alpha\), contradicting simplicity.
Thus the two contact ends correspond to opposite ends also in this
case.

The physical endpoints of \(\delta\) are consequently \(y_-\) and
\(y_+\). They exist because its two specified end lifts converge at
the contact. Its interior is disjoint from \(T\), and \(\eta\) is an
arc in \(T\) with just those endpoints. Thus their union is a Jordan
curve. In the point case, the simple open path has both physical
endpoints at that point and no other repetition, which again gives
a Jordan curve.

Let \(D\) be the bounded Jordan domain. Suppose
\(\overline D\) contains no critical value. It is compactly contained
in \(U\): a Jordan curve in a simply connected plane domain encloses
its bounded domain there. Critical values of a finite proper
holomorphic map are locally finite. A slightly enlarged Jordan disk
\(D_+\Subset U\) can therefore contain \(\overline D\) and avoid all
critical values.

Each component of \(P^{-1}(D_+)\) is a one-sheeted unbranched cover
of a disk. Let \(V_+\) be the component containing
\(\Gamma(x_-)\). Since \(\Gamma(E)\) is connected, it lies in
\(V_+\), and \(P|_{V_+}\) is a conformal isomorphism.

The lift of \(\delta\) beginning at \(\Gamma(x_-)\) must therefore
end at \(\Gamma(x_+)\): it is the unique inverse of the target path
in that disk. This is the occurrence \(\gamma^-\), after choosing
its orientation from the contact end. Hence its other \(I\)-endpoint
is \(x_+\).

But the other end of \(\gamma^-\) corresponds to the earlier
parameter \(a<s\) of the parent, while \(x_+=\alpha(t)\) occurs at
\(t\ge s\). If \(a>0\), continuity and injectivity of \(\alpha\)
are contradicted. If \(a=0\), the parent has an endpoint limit at the
interior point \(x_+\in X\), contradicting properness. This argument
also applies when \(s=t\).

Thus \(\overline D\) contains a critical value. Under the stated
avoidance on \(C\), it lies in \(D\). \(\square\)

The theorem does not assume that the two occurrences have distinct
images. It derives a necessary consequence of their equality. It also
does not require their far ends to coincide with the original parent
ends: earlier or later intervening restrictions are allowed, provided
the displayed two occurrences really are adjacent to the stated
connected contact.

## 5. Applying the cap theorem to the stationary limb

Assume \(T\) is the actual physical carrier under discussion. Write
\(\mathcal L_0=T\cap\mathfrak L_0\), and assume the native rooted
contour correspondence: \(\mathbf L_j\) is the full ideal contour
of \(T\cap\mathfrak L_j\). In impression terms, every prime end of
the closure of a noncritical contour \(\mathbf L_j\) has its entire
impression in the closed physical limb
\(\overline{T\cap\mathfrak L_j}\), including its dividing endpoint.
Every access landing in the open critical limb that is used as a
retained path end belongs to \(\mathbf L_0\). These are native
ideal-contour premises, not consequences of finite atom labels.
Also use the physical connectedness of

\[
 R=T\setminus\mathcal L_0.
 \tag{5.1}
\]

For a dendrite carrier this is immediate. For the full-hull carrier
in CUTPOINT_PRUNING.md it follows by pulling back the connected
subtree on the other side of the singleton dividing fiber. It is
not an identification of that constructed carrier with an
independently named native carrier.

### Corollary 5.1 — a stationary collision crests over the last limb

Let \(h<q\). Suppose items 1--4 of Theorem 4.1 are realized with
\(P=P_h\), \(I=I_h\), the canonical \(\Gamma_h\), and

\[
 E\subset\mathcal L_0^h\setminus T,\qquad
 F^h(E)\subset\mathcal L_0.
 \tag{5.2}
\]

Suppose both terminal images are simple retained Wave leaves, with
the native marking, and each occurrence maps homeomorphically to
its image. If the two terminal images coincide as \(\delta\),
then \(\delta\) crests over
every noncritical limb, in particular \(\mathbf L_{q-1}\).

#### Proof

Equation (2.2) makes \(F^h|_E\) injective. Lemma 3.1 places every
critical value of \(P_h\) in \(R\), while \(\eta=F^h(E)\) lies in
the disjoint open critical limb. The interior of \(\delta\) lies
outside \(T\). Thus the Jordan curve \(C=\delta\cup\eta\) avoids
all critical values.

Theorem 4.1 puts some critical value in the bounded domain \(D\).
The connected set \(R\) is disjoint from \(C\). As it contains every
critical value, it follows that

\[
 R\subset D.
 \tag{5.3}
\]

This is a physical Jordan separation argument; no quotient or
sheet-label equality is used.

To translate (5.3) to the ideal boundary, cut the annulus
\(U\setminus T\) along the simple proper path \(\delta\). Its
boundary-parallel side is the component cut off from the outer end.
The inner ideal interval on this side is the relative-boundary
interval to which \(\delta\) is subordinate. Every access belonging
to a noncritical limb lies on this side: its entire physical limb
and its dividing endpoint lie in the open set \(D\), by (5.3).
More precisely, the native contour premise puts every impression
of the closed noncritical contour in the compact set \(R\subset D\).
Upper semicontinuity of prime-end impressions then gives an ideal
collar of that closed contour whose physical interior is contained
in \(D\). This does not require singleton impressions on that limb.

The two ends of \(\delta\) are the images of its contact ends and
land in the open critical limb. Their marked end intervals therefore
belong to \(\mathbf L_0\). Removing those ends from the base leaves
the entire noncritical contour in the crest. In particular
\(\mathbf L_{q-1}\) belongs to that crest. \(\square\)

The rooted contour correspondence in this statement is part of the
native marking that must actually be used. A combinatorial component
label without its ideal-contour meaning is not a substitute for it.

## 6. Two additional selected Wave stages rule out the collision

### Theorem 6.1 — bounded-delay noncollision

Under the hypotheses of Corollary 5.1, suppose the original parent has
unique retained path outputs at stages \(h,h+1,h+2\), and each of
those three paths is a leaf of an actual Wave. These outputs must
be sequentially compatible through the native filters:

\[
 F_*\{\delta_h\}=\{\delta_{h+1}\},\qquad
 F_*\{\delta_{h+1}\}=\{\delta_{h+2}\}.
 \tag{6.0}
\]

Uniqueness of separately computed direct-iterate restrictions is
not substituted for (6.0). Suppose also the KKL
combinatorial action and Proposition A.14 apply at these stages.
Then the two adjacent retained stage-\(h\) occurrences cannot have
the same terminal image.

#### Proof

If their images were equal, the unique stage-\(h\) output
\(\delta_h\) would crest over \(\mathbf L_{q-1}\), by Corollary 5.1.
It is unbreakable for the next step, and its unique output
\(\delta_{h+1}\) is an actual Wave leaf. Apply Proposition A.14 to
the one-leaf lamination \(\{\delta_h\}\) and the one-leaf pushed
lamination \(\{\delta_{h+1}\}\). It gives

\[
 \delta_{h+1}\text{ crests over }
 F_*\mathbf L_{q-1}=\mathbf L_0.
 \tag{6.1}
\]

Apply the same proposition once more. The uniqueness and Wave
assumptions at the next stage give

\[
 \delta_{h+2}\text{ crests over }
 F_*\mathbf L_0=C_T.
 \tag{6.2}
\]

A Wave cannot crest over its entire ideal boundary circle: its
crest is its base minus its nonempty ends. This is a contradiction.
No extraction lemma or additive width error is used. \(\square\)

The “actual Wave” clauses matter. Unbreakability alone says that
the output is one path; it must not silently be strengthened to a
simple path or a Wave. The theorem uses exactly the additional
selected-Wave structure supplied by the stationary subwaves when
those subwaves and their retained images have been constructed.

### Corollary 6.2 — a valid longer horizon for this conditional route

In a prospective repaired stationary argument set

\[
 N=b+5,\qquad m=N-1=b+4,\qquad q>b+4.
 \tag{6.3}
\]

Assume the selected subwaves \(A_0,\ldots,A_m\) are actually
constructed as in the source, and consider a parent in \(A_m\).
At the two separator indices \(n=b,b+1\), put \(h=n+1\).
Then

\[
 h\le b+2,\qquad h+2\le m,\qquad h<q.
 \tag{6.4}
\]

Thus, if a proposed bypass at either index supplies the connected
contact and two actual retained adjacent occurrences of Theorem 4.1,
their coincident-image possibility is excluded by Theorem 6.1.
Distinct images would contradict unbreakability immediately.
Either way that fully realized bypass is impossible.

The numerical inequality on \(q\) is legitimate in the source's
high-type branch: Section 3.2 allows the \(b\)-dependent high-type
threshold to be enlarged. It is stated explicitly here and is not
asserted for every small-\(q\) parameter.

Changing \(N\) does not itself prove the missing bypass realization.
Nor does this note claim that every other use of the terminal
index in the stationary proof has been rewritten. For example, the
two proposed final graph projections would now be

\[
 P_m(\widehat K_b)=F^4(K_0),\qquad
 P_m(\widehat K_{b+1})=F^3(K_0),
 \tag{6.5}
\]

rather than the source's shorter-horizon formulas. The primitive
period is at least \(q>b+4\), so these are distinct cycle members,
and the factorization still contains only one central degree-two
step. Applying any final width theorem requires its own correctly
typed final incidence statement at this new level.

## 7. The exact surviving N2 work

The conditional implication now has the form

\[
\begin{split}
 &\text{actual simple stationary parent}\\
 &+\ \text{one connected selected deep contact}\\
 &+\ \text{two adjacent proper sequentially retained occurrences}\\
 &+\ \text{canonical graph endpoints and native limb contours}\\
 &+\ \text{two further unique selected Wave stages}\\
 &\quad\Longrightarrow\quad
 \text{the two images are distinct}.
\end{split}
\tag{7.1}
\]

The new proof uses no independent deck-noncollision or complete
selected-corridor confinement premise. But the following remain
outside the theorem:

1. The printed phrase “passes through” has to give an actual
   contact component along the proof-used geometric leaf.
2. The contact must be connected in the stated sense, or a new
   argument must replace it when the leaf makes multiple contacts
   or intervening excursions.
3. Both one-sided local germs must extend to proper complete
   occurrences with the named contact endpoints.
4. Both occurrences must survive the fine-marking and single-
   inclusion-block filters at every required sequential stage.
5. The native non-locally-connected carrier and its full ideal
   contours must be identified where the proof uses them.

The first local germs follow if an actual two-sided crossing in the
embedded graph neighborhood is supplied. The existing binder audit
correctly explains why those germs alone do not give items 2--4.
The theorem above does not overwrite that distinction.

No actual source-admissible counterexample to the complete stationary
statement has been constructed here. The result is a new analytic
restriction on possible collisions, and a conditional way to remove
their independent treatment once the earlier occurrence geometry is
proved.

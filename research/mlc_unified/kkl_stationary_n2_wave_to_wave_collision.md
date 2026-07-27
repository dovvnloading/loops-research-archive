# Gate N2 adversarial frontier: a Wave-to-Wave occurrence collision

Date: 2026-07-27  
Status: explicit analytic pseudo-quadratic-like countermodel proved;
not an actual stationary KKL counterexample

## 1. The strengthened obstruction

The model in `stationary_occurrence_collision_obstruction.md` proves
that two distinct proper immersion-restriction components can have one
identical proper image under a degree-two covering.  Its common image
joins different ideal-boundary components, so that image is not a
Wave.

This note removes that geometric qualification.  It proves:

> **Wave-to-Wave collision theorem.**  There is an explicit analytic
> degree-two pseudo-quadratic-like relation \(F=(f,\iota)\), a proper
> simple target path \(\alpha\), and two distinct proper components
> \(\gamma_\downarrow,\gamma_\uparrow\subset\iota^{-1}(\alpha)\) such
> that:
> 1. \(\alpha\) is a Wave for a finite target ideal marking;
> 2. each \(\gamma_\downarrow,\gamma_\uparrow\) is a Wave for the
>    covering-pulled marking \(f^*\mathcal I\);
> 3. \(f(\gamma_\downarrow)=f(\gamma_\uparrow)=\delta\) as one
>    unparametrized proper path;
> 4. \(\delta\) is itself a Wave for the same target marking; and
> 5. neither restriction path contains the critical point.

Thus the literal geometric information

\[
\text{two distinct proper restriction portions, each pushing to a Wave}
\tag{1.1}
\]

does not imply that the untagged pushforward contains two paths.
Path-level deck noncollision is indispensable.

The theorem does **not** prove that the chosen target marking is a
complete acting KKL marking satisfying

\[
 f^*\mathcal I\succcurlyeq\iota^*\mathcal I,
\tag{1.2}
\]

and it does not realize KKL's stationary Hubbard tree, primitive
combinatorics, or the line-1603 endpoint itinerary.  It is therefore
not a counterexample to the intended KKL stationary theorem.  It is a
strict counterexample to any attempted proof of Gate N2 that replaces
the exact terminal path predicate by the assertion that both terminal
objects are Waves.

## 2. The pseudo-quadratic-like relation

Put

\[
 R=75,\qquad P=100,\qquad
 \beta=\frac{2\pi}{P}=\frac{\pi}{50},\qquad
 \Delta=e^{2\beta}-1,
\tag{2.1}
\]

and let

\[
 U'=\mathbb D_R,\qquad U=\mathbb D_{R^2},
\qquad K'=[-1,1],\qquad K=[0,1].
\tag{2.2}
\]

Define

\[
 f(z)=z^2,\qquad
 \iota(z)=\frac{e^{\beta(z+1)}-1}{\Delta}.
\tag{2.3}
\]

Sections 3--4 of
`stationary_occurrence_collision_obstruction.md` prove, by direct
calculation, that:

1. \(f:U'\to U\) is proper of degree two;
2. \(\iota:U'\to U\) is a holomorphic immersion;
3. \(f^{-1}(K)=\iota^{-1}(K)=K'\); and
4. \(f|_{K'}\) and \(\iota|_{K'}\) give the required filled-set
   identification.

These clauses are unchanged here.  Notice also the exact period

\[
 \iota(z+Pi)=\iota(z),
\tag{2.4}
\]

because \(e^{\beta Pi}=e^{2\pi i}=1\).

## 3. Two proper outer-to-outer restriction components

Set

\[
 a=\sqrt{R^2-\left(\frac P2\right)^2}
   =25\sqrt5.
\tag{3.1}
\]

For \(-a<x<a\), define the horizontal chords

\[
 \gamma_\downarrow(x)=x-50i,\qquad
 \gamma_\uparrow(x)=x+50i.
\tag{3.2}
\]

At \(x=\pm a\),

\[
 |\gamma_\downarrow(x)|^2
 =
 |\gamma_\uparrow(x)|^2
 =
 a^2+50^2
 =
 75^2.
\tag{3.3}
\]

For \(-a<x<a\), the strict inequality in (3.3) holds.  Hence both
chords lie in \(U'\), extend to two distinct points of
\(\partial U'\), and are proper paths in \(U'\setminus K'\).  They
avoid \(K'\) because their imaginary parts are \(\pm50\).

By (2.4),

\[
 \iota(\gamma_\downarrow(x))
 =
 \iota(\gamma_\uparrow(x)).
\tag{3.4}
\]

Their common immersion image is

\[
 \eta(x)
 =
 \frac{-e^{\beta(x+1)}-1}{\Delta}.
\tag{3.5}
\]

It is a strictly decreasing negative-real interval.  Write

\[
 u=\eta(-a),\qquad v=\eta(a),
\qquad v<u<0.
\tag{3.6}
\]

## 4. A proper target Wave containing the common trace

Define \(\alpha\) to be the oriented polygonal path obtained by
concatenating, in order,

\[
\begin{split}
0,\quad i,\quad u+1+i,\quad u+1,\quad u,\quad
\eta([-a,a]),\quad v-1,\quad v-1-2i,\quad 1-2i,\quad1.
\end{split}
\tag{4.1}
\]

The four nonreal polygonal legs lie respectively in the upper and
lower half-planes.  The real portion lies in
\((-\infty,0)\).  Therefore \(\alpha\) is simple and

\[
 \alpha((0,1))\cap K=\varnothing.
\tag{4.2}
\]

It extends continuously to \(0,1\in K\), so it is proper in
\(U\setminus K\).  It lies far inside \(U\): from
\(a<56\), \(\beta<22/350\), and \(e^t-1>t\),

\[
 |v|
 =
 \frac{e^{\beta(a+1)}+1}{\Delta}
 <
 \frac{e^{3.6}+1}{3/25}
 <320,
\tag{4.3}
\]

and every vertex in (4.1) has modulus below \(322\ll5625\).

We next prove that the chords in (3.2) are complete connected
components of \(\iota^{-1}(|\alpha|)\), rather than proper subarcs of
larger lifts.

At either chord endpoint \(z=x_0\pm50i\), \(x_0\in\{-a,a\}\),

\[
 \iota'(z)
 =
 -c_{x_0},
\qquad c_{x_0}>0.
\tag{4.4}
\]

Let \(w=X+iY\) be a target tangent and
\(dz=-w/c_{x_0}\) its local inverse tangent.  The tangent points into
\(\mathbb D_R\) precisely when

\[
 \operatorname{Re}(\overline z\,dz)<0,
\quad\text{equivalently}\quad
 \operatorname{Re}(\overline z\,w)>0.
\tag{4.5}
\]

At the \(x_0=-a\) endpoints, the direction of \(\eta\) into the chord
is \(w=-1\), and

\[
 \operatorname{Re}(\overline z(-1))=a>0
\tag{4.6}
\]

for both signs.  The continuation of \(\alpha\) from \(u\) toward
\(u+1\) has \(w=+1\), for which the expression is \(-a<0\); it points
outside both source-disk sheets.

At the \(x_0=a\) endpoints, the direction from \(v\) back into
\(\eta\) is \(w=+1\), for which

\[
 \operatorname{Re}(\overline z(+1))=a>0,
\tag{4.7}
\]

while the continuation from \(v\) toward \(v-1\) has \(w=-1\) and
points outside both sheets.  Thus no lift of either continuation
extends either chord through its source-boundary endpoint.

Since \(\iota\) is a local homeomorphism and \(\alpha\) is simple,
\(\iota^{-1}(|\alpha|)\) is locally a one-manifold.  Equations
(4.6)--(4.7) therefore prove that
\(\gamma_\downarrow\) and \(\gamma_\uparrow\) are two complete,
distinct proper components of that inverse trace.

Finally, \(\alpha\) together with the accessible inner-boundary arc
from \(1\) to \(0\) forms a Jordan curve.  Hence \(\alpha\) is
boundary-parallel to one connected arc of the inner ideal-boundary
component.  Subdivide that arc into at least three marked intervals,
with the two endpoint accesses lying in its end intervals.  Then
\(\{\alpha\}\) is a Wave and \(\alpha\) is a path in the resulting
marked surface.

## 5. The two proper covering images are one Wave

The two chords are deck mates with reversed parameter:

\[
 \gamma_\uparrow(-x)
 =
 -\gamma_\downarrow(x).
\tag{5.1}
\]

Therefore

\[
 f(\gamma_\uparrow)=f(\gamma_\downarrow)
\tag{5.2}
\]

as unparametrized paths.  Their common image is

\[
 \delta(x)
 =
 (x-50i)^2
 =
 x^2-2500-100xi,
\qquad -a<x<a.
\tag{5.3}
\]

The imaginary part \(-100x\) determines \(x\), so \(\delta\) is
injective.  It avoids \(K\): its only real point occurs at \(x=0\),
where

\[
 \delta(0)=-2500.
\tag{5.4}
\]

At the two endpoints,

\[
 |\delta(\pm a)|=|\gamma_\downarrow(\pm a)|^2=75^2,
\tag{5.5}
\]

while \(|\delta(x)|<75^2\) for \(-a<x<a\).  Thus \(\delta\) is a
proper simple path with two distinct accesses on the outer
ideal-boundary component of \(U\setminus K\).

A simple outer-to-outer crosscut is boundary-parallel on one side.
Refine the same target marking used in Section 4 on the outer boundary
component, using at least three intervals along that boundary arc and
putting the two endpoint accesses in the end intervals.  The inner and
outer subdivisions are disjoint, so together they form one finite
ideal marking \(\mathcal I\).  For this one marking,

\[
 \{\alpha\}\quad\text{and}\quad\{\delta\}
\tag{5.6}
\]

are both Waves.

Choose the outer base arc of \(\delta\) to be the image under
\(z\mapsto z^2\) of the lower outer-circle arc joining
\(-a-50i\) to \(a-50i\).  That lower arc has angular length less than
\(\pi\), so the squaring map is injective on it.  Its deck mate is the
corresponding upper arc.  The subdivision of the target base therefore
lifts to two disjoint connected subdivisions in \(f^*\mathcal I\),
and the two chords are boundary-parallel to those lifted bases.
Consequently

\[
 \{\gamma_\downarrow\},\qquad\{\gamma_\uparrow\}
\tag{5.7}
\]

are Waves in the covering-pulled marking \(f^*\mathcal I\).

Combining (3.2), (3.4), and (5.2) gives the collision certificate

\[
\boxed{
\gamma_\downarrow\ne\gamma_\uparrow,\qquad
\iota(\gamma_\downarrow)
=
\iota(\gamma_\uparrow)\subset\alpha,\qquad
f(\gamma_\downarrow)
=
f(\gamma_\uparrow)
=\delta,
}
\tag{5.8}
\]

with both \(\alpha\) and \(\delta\) Waves.  The critical point \(0\)
lies in \(K'\), not on either chord.

## 6. What this proves about Gate N2

The construction rules out each of the following proposed terminal
certificates:

1. two distinct source components;
2. two different immersion sheets;
3. two proper restriction paths;
4. two paths whose covering images are individually Waves; and
5. two paths with different source-boundary accesses.

All five can hold while the untagged covering images are the same
geometric path.

The exact missing terminal predicate is therefore path-level:

\[
 [\lambda^+]\ne[\tau(\lambda^-)],
\tag{6.1}
\]

where \(\tau\) is the nontrivial deck involution and brackets denote
unparametrized geometric paths.  Endpoint-pair separation can prove
(6.1), but endpoint-pair equality is inconclusive without a relative
homotopy or winding record.

The model does not discharge the earlier incoming-anchor theorem in
`kkl_stationary_n2_incoming_window_anchor.md`; nor does it prove or
refute the actual KKL-specific predicate (6.1).

## 7. Acting-marking boundary

The common target marking in Section 5 certifies the geometric Wave
types, and its covering pullback marks each chord as a source Wave.
This note does not assert that its pullbacks satisfy the full
KKL action condition (1.2).  The immersion is nonproper at the outer
source boundary, exactly where both chords end.  Consequently a proof
of (1.2) would require an independent computation of:

1. every ideal pullback \(\iota^*I\);
2. overlap of those pullbacks at the nonproper outer end;
3. refinement by \(f^*\mathcal I\); and
4. survival of both chords under the line-2097
   coarse-single-interval filter.

None of these is inferred from (5.8).  This qualification prevents the
model from being misreported as a formal counterexample to KKL's full
marked action.

The note also does not assert that these are the only raw restrictions
of \(\alpha\).  Additional restriction components, if present, can
produce other terminal paths; the model is not an unbreakable KKL leaf.
Its theorem is the exact pairwise collision (5.8).

## 8. Validation

The diagnostic script

```text
audit_n2_wave_to_wave_collision.py
```

checks:

1. \(a=25\sqrt5\);
2. the periodic immersion equality in (3.4);
3. the deck-image equality in (5.2);
4. strict monotonicity and negativity of \(\eta\);
5. the inner modulus of \(\delta\) and its outer endpoint moduli; and
6. numerical separation of \(\delta\) from \(K\).

These checks are diagnostic only.  The analytic proof is Sections
2--5.

## 9. Skeptic audit

1. Two source sheets are not called two terminal paths.
2. “Both images are Waves” is not called terminal noncollision.
3. The target marking is not called an acting KKL marking.
4. The model is not called a primitive or parabolically bounded block.
5. No numerical check discharges an analytic assertion.
6. No invariant is quotiented by the deck involution.
7. The critical point is removed with \(K'\).
8. Gate N2 and every downstream obligation remain open.

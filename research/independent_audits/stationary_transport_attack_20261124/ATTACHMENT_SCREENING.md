# Exponential attachment screening with bounded vertical width

2026-11-25. Exact obstruction to a general attachment-angle
calibration following [ANGULAR_CALIBRATION.md](ANGULAR_CALIBRATION.md).
It uses a fixed unchanged old side, a family of full finite
trees and a genuine degree-two annular covering. The screening
bound is proved by an explicit harmonic barrier, not sampled
harmonic measure. The construction is not a native periodically
repelling primitive renormalization or a counterexample to MLC.

## 1. The same old access interval, and a genuine quadratic cover

Put S=D(0,5), U=D(0,25), J=[-1,1] in the complex plane,
and f:S→U, f(z)=z². For 0<δ≤1/2 define A_δ by the two
polygonal paths rooted at 1:

    (1,0), (1,1), (δ,1), (δ,3),
    (1,0), (1,-1), (δ,-1), (δ,-3).

Let B_δ=-A_δ and L_δ=J∪A_δ∪B_δ. All their vertices
lie in D(0,4) (their squared norms are at most 9+1/4),
so the same holds for their straight segments. The two
added trees are disjoint, have positive and negative
real coordinates respectively, and attach to J at
its two distinct tips. Their union with J is a full
compact embedded finite tree. Its upper part forms a
room with a narrow open neck, not a closed loop.

Since f is injective on A_δ and f(A_δ) meets [0,1]
only at 1, T_δ=f(L_δ) is also a full compact finite
tree. It is f(J)∪f(A_δ), two trees meeting at one
point. The exact two-root property and deck symmetry
give

\[
 f^{-1}(T_\delta)=L_\delta
\]

inside S. Thus X_δ=S minus L_δ→U minus T_δ is a
genuine unbranched degree-two annular covering.
The old annulus Y=S minus J is fixed. Let

\[
 M_0=\operatorname{mod}Y,\qquad
 M_\delta=\operatorname{mod}X_\delta .
\]

By monotonicity of the ring modulus,

\[
 0<{\log(5/4)\over2\pi}\le M_\delta\le M_0<\infty .
 \tag{1}
\]

In particular the vertical widths of both source and
target annuli stay bounded, and the full fixed
separator J has a fixed finite peripheral width in Y.
The two branches attach at genuine opposite accesses
of that old annulus, interchanged by z↦-z.

Let I be the upper side of the real subsegment
[-1/2,1/2] of J, with its actual ideal accesses,
not its lower bank. For every δ this compact access
interval is on the unchanged old side of L_δ.
The old and enlarged carriers agree in a fixed
physical neighborhood of this subsegment, for example
within radius 1/4 of each of its points. The old
and new ideal coordinates identify this side
bijectively by the local embedded chart.
Let ℓ_0>0 be its fixed normalized angle length in Y,
and ℓ_δ its angle length in X_δ. All continua here
are locally connected, and the ideal interval I
is a literal unchanged physical side, not an
attachment collapsed to a point.

## 2. Explicit harmonic screening estimate

Let v_δ be the annular harmonic height on X_δ,
zero at the inner boundary and one at the outer
boundary. It exists by annular uniformization and
has those physical boundary limits because the
finite slit tree and the outer circle are locally
connected. It takes values in [0,1].

The open room is (-1,1)×(0,1), with its floor on J.
It connects through the open interval (-δ,δ)×{1}
to the rectangular neck

\[
 N_\delta=(-\delta,\delta)\times(1,3).
\]

The two vertical neck walls and the rest of the
room boundary are on L_δ. In the neck use the
harmonic barrier, with a=π/(4δ),

\[
 B(x,y)=\sqrt2\cos(ax)
 \left(e^{-a(y-1)}+e^{-a(3-y)}\right).
\]

Each summand is harmonic. On the vertical sides
B≥0=v_δ; on the horizontal ends y=1 and y=3,
cos(ax)≥1/√2, so B≥1≥v_δ. The maximum principle
on the rectangle gives v_δ≤B there. At y=2,

\[
 v_\delta(x,2)\le \epsilon_\delta
       :=2\sqrt2\,e^{-\pi/(4\delta)} .
 \tag{2}
\]

The room together with the lower half-neck is a
bounded connected polygonal domain whose only
boundary not on L_δ is the horizontal cut at y=2.
A second maximum-principle application gives
0≤v_δ≤ε_δ throughout that room. The same inequality
holds at the floor by continuous landing.

For every x∈[-1/2,1/2], odd reflection across the
horizontal floor gives a harmonic extension to
the disk of radius 1/4 centered at x, with absolute
value bounded by ε_δ. The elementary Poisson
gradient estimate on that disk yields

\[
 0\le \partial_y v_\delta(x,0^+)
       \le 8\epsilon_\delta . \tag{3}
\]

For example the directional derivative at the
center of a radius-r disk is the integral against
sin(θ)/(πr), whose absolute integral is 4/(πr)
and hence is <2/r. Use r=1/4. The nonnegative
sign follows from the floor being the zero boundary.

In the normalized flat conformal cylinder for X_δ
of circumference one and height M_δ, the vertical
coordinate is M_δ v_δ. The inner boundary angle
coordinate on I is its harmonic conjugate, with
derivative in absolute value M_δ ∂_y v_δ by
Cauchy-Riemann. This is a local assertion on a
straight regular slit side; reflection supplies
the required conformal boundary chart. Integrate
(3) across the length-one subsegment and apply
(1)–(2). We obtain

\[
 \boxed{\ell_\delta
 \le 16\sqrt2\,M_0 e^{-\pi/(4\delta)}.} \tag{4}
\]

There is no numerical approximation or implicit
domain comparison in this estimate. Thus

\[
 \log(\ell_0/\ell_\delta)
 \ge {\pi\over4\delta}
       +\log\!\left({\ell_0\over16\sqrt2\,M_0}\right)
       \longrightarrow+\infty . \tag{5}
\]

Even the angle of an entire unchanged protected
physical interval can be exponentially compressed
by adding these two tree branches. Both the
separator's local annular width and the source
and target vertical widths are uniformly bounded.

## 3. A complementary near-contact width on the same screen

There is a corresponding large unrestricted width
between the two branches. For every y∈(1,3) the
horizontal open segment from -δ+iy to δ+iy
lies in X_δ, is proper at both ends, and connects
the two distinct attached branches. These paths
are simple and mutually disjoint. The exact width
is 1/δ: every admissible density satisfies by
Cauchy-Schwarz

    ∫_{-δ}^{δ} ρ(x+iy)^2 dx ≥ 1/(2δ)

for each y, and integration over height two gives
the lower bound. The constant density 1/(2δ) on
the neck attains it. The same computation is a
lower bound for the free Dirichlet response that
sets one branch to zero and the other to one.

Consequently the mechanism causing (5) is a real
positive-width channel between distinct attachments,
not a finite set of singular gates. It also shows
why bounding the number of branches or requiring
antipodal old attachment angles is insufficient.

## 4. Exact scope and implication for the stationary route

The estimate in ANGULAR_CALIBRATION for an actual
degree-one inner-circle immersion does not conflict
with (4). The map from X_δ into Y has pieces of its
inner boundary in the interior of Y, namely the added
trees. It lacks the global inner-end hypothesis of
that distortion theorem. In this example the actual
local old-side chart is the identity on the plane
near I. Even that does not control the change of
its conformal angular measure.

This example supplies the nesting, an actual proper
quadratic cover, an exact full inverse carrier,
opposite attachment hosts and a fixed old separator.
It does NOT supply a compatible pseudo-quadratic-like
immersion identifying J with the independently
prescribed target carrier T_δ, a forward-invariant
primitive small-Julia cycle, or the native rotation
and parabolic occupancy. In particular the fixed
separator width in this example is not asserted to
equal the native renormalization width R(F).
The negative result is a precise no-go for deducing
attachment distortion from the abstract annular,
topological and vertical-width data alone.

A native solution must either exclude or charge the
screening channels by the specific dynamics and
actual marked Wave conditions. The coherent-packet
theorem avoids needing a general angle bound for
the genuine collision subclass; its remaining
single-retained, carrier-edge family still requires
such a source-specific argument. The present proof
neither refutes the native desired estimate nor
declares that remaining family negligible.

All harmonic and conformal arguments above are
written mathematics. The exact polygon and rectangle
energy arithmetic is covered by the companion
finite checks. No proof-obligation ledger status is
changed. Prepared with ChatGPT assistance;
specialist review pending.

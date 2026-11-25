# Logarithmic anchored angular charge and the immersion/attachment split

2026-11-25. Companion to [COLLISION_GAIN.md](COLLISION_GAIN.md), §5.
The long-span charge there works without a common crest, but has
cost 1/(2ε). For stationary families sharing a fixed crest anchor
we can replace this by logarithmic cost. A separate Poisson-kernel
estimate proves exponential distortion control for the actual
unpunctured-carrier immersion. The remaining attachment-induced
distortion is not estimated by that theorem.

## 1. Fixed-anchor long-span estimate

Normalize the actual annular complement X=U minus T to the flat
cylinder (R/Z)×(0,M), M=mod(X). Let D be any family of simple proper
inner-ended paths with disk-side caps and distinct ideal endpoints,
each cap base containing a fixed inner access e. Suppose their
angular spans in the unit-circumference coordinate are at least
ε, where 0<ε≤1.

Lift each cap and path to the universal strip, choosing the lift
of e at the origin on its bottom line. Its two endpoint coordinates
are x_-<0<x_+, with x_+-x_- in [ε,1]. Consequently both endpoint
distances from the origin are ≤1 and at least one is ≥ε/2.
This choice is fixed by the actual cap, not by the shorter
distance between its endpoints.

On the strip take the radial density 1/|z| on the upper
half-annulus ε/4≤|z|≤2, zero off it. Its squared area on the
strip is at most π log(8/ε). Every such lift has length at
least log 2 in this metric. Indeed:

* If it enters |z|<ε/4, the tail from the farther endpoint
  crosses [ε/4,ε/2] in radial distance.
* If it goes outside |z|≤2, a tail from an endpoint of
  distance at most one crosses [1,2].
* Otherwise it stays in the displayed half-annulus and its
  argument varies from π to 0; the 1/|z| metric then gives
  length at least π.

The first two assertions use total radial variation; the third
uses total angular variation, so no monotonicity of the trace
is assumed. Include the radial boundary circles in the support.
All these statements follow by exhaustion for improper
locally rectifiable paths. Nonrectifiable parent curves can be
handled by adding an arbitrarily small positive constant in
the finite-area cylinder coordinate.

Divide the density by log 2 and push it to the cylinder by
the all-sheet square-sum rule. The infinite-sheeted universal
cover does not increase its area, and every parent has at
least the length of its chosen lift. Thus

\[
 \boxed{
 W_X(D)\le {\pi\over(\log 2)^2}\log(8/\varepsilon).
 } \tag{1}
\]

This does not assert a logarithmic bound for the unanchored
family with bases spread around the entire inner circle.
The earlier band estimate is valid for that larger family.

## 2. Exponential separation is sufficient for robust collision gain

Suppose actual simple stationary output paths at each prefix
j=0,...,h have a common crest anchor e_j (allowed to depend on
j and on the block, not on the leaf). A full fixed crest
interval supplies such an anchor. The hypotheses of the
canonical-lift and collision-gain notes are in force, including
actual retained witnesses.

For each j discard the original parents whose j-th output
span is ≥ε. By (1) and the actual degree-2^j all-sheet metric
transport, their total width is at most
2^j π log(8/ε)/(log 2)^2. Sum over the prefixes and add the
single final-horizon incomplete-lift charge. This gives

\[
 E^{\rm anchored}_{\varepsilon,h}
 \le 2^h V(F)
   +{\pi(2^{h+1}-1)\over(\log 2)^2}\log(8/\varepsilon).
 \tag{2}
\]

On the complement every retained one-step source cap has
angular span <ε/2. As in COLLISION_GAIN, §5, two qualified
protected anchors at source circle distance ≥ε/2 force two
retained disjoint windows and hence a double stage.

In particular, if actual native geometry were to produce,
at the requisite majority of stages, two qualified anchors
with separation at least exp(-L), where
L≤C_b(R(F)+V(F)+1), then one may choose ε=exp(-L)
(for L≥0). The entire exceptional cost in (2) would
be O_b(R+V+1), despite the possibly exponentially small
separation. Under the same actual output-controllability
hypothesis, the majority collision gain supplies the
strict terminal response at sufficiently large input
width. It is not necessary to prove an absolute positive
lower bound for the separation of the anchors.

This is a conditional calibration threshold, not a proof
that the required anchors exist. In particular it does not
turn an arbitrary pair of model cut labels into two
qualified anchors or assume a common crest on an
unstructured family.

## 3. Exponential inner-boundary distortion of an immersion

The following is an independent analytic theorem. Let Y and
X be finite conformal annuli of moduli m',m, and let
i:Y→X be holomorphic, taking the inner end to the inner
end, with a degree-one local conformal correspondence on
their inner ideal circles. The map need not be globally
injective or proper at the outer end.

**Theorem.** In normalized flat cylinder coordinates, the
inner-circle map is an orientation-preserving real-analytic
homeomorphism whose derivative a(x) satisfies

\[
 \boxed{
 \exp(-\pi/(2m'))\le a(x)\le\exp(\pi/(2m')) .
 } \tag{3}
\]

In particular angular lengths of either of two complementary
arcs, and hence geodesic circle distances, are changed by a
factor between the two bounds.

Proof. Lift to strips, obtaining a holomorphic map H on
0<Im z<m' into 0<Im H<m with H(z+1)=H(z)+1.
At the inner boundary it has real values by its ideal-end
extension, and extends by reflection. Put v=Im H, a
positive bounded harmonic periodic function, with v(x,0)=0.
The boundary derivative a(x)=∂_y v(x,0)>0 by the local
conformal correspondence (also by the Hopf lemma).
Cauchy-Riemann and degree one imply

\[
 \int_0^1 a(x)\,dx=1.
 \tag{4}
\]

For any 0<s<m', put g(t)=v(t,s), a positive periodic
function. The harmonic solution on the strip 0<y<s
with bottom zero and top g has top-edge Poisson kernel

\[
 v(x,y)=\int_{\mathbb R}
 {1\over2s}
 {\sin(\pi y/s)\over
  \cosh(\pi(x-t)/s)+\cos(\pi y/s)}
 g(t)\,dt.
\]

This follows directly from the upper-half-plane Poisson
formula under exp(π z/s), with the bottom ray positive
and the top ray negative. Boundedness removes a possible
contribution at infinity. Equivalently the unique
periodic solution on the cylinder is given by the
periodization of this kernel. Differentiating at y=0
is justified by bounded g and exponential kernel decay.
It gives

\[
 a(x)=\int_{\mathbb R}K_s(x-t)g(t)\,dt,\qquad
 K_s(u)={\pi\over2s^2(\cosh(\pi u/s)+1)} .
\]

The logarithmic derivative of this strictly positive
kernel has absolute value at most π/s, since
|sinh u|≤cosh u+1. For any x,x' with |x-x'|≤1/2,
pointwise comparison of the kernels and g≥0 give

\[
 e^{-\pi/(2s)} a(x')\le a(x)\le e^{\pi/(2s)} a(x').
\]

By periodicity any two circle points have representatives
at this distance. Integrate in x' using (4) to bound
a(x) above and below by these same constants, and let
s increase to m'. This proves (3). QED.

The coefficient π/2 is the direct strip-kernel estimate;
no claim of optimality is needed.

## 4. Actual application and exact remaining attachment distortion

At one step put Y=U^1 minus Γ_1(T) and
X=U minus T. The full inverse-filled-set property gives
I_1^(-1)(T)=Γ_1(T), so I_1:Y→X is an actual holomorphic
map. Its qualitative embedded neighborhood of K^1
identifies the inner collar of Γ_1(T) with that of T,
including the degree-one ideal-circle map. This follows
also in annular coordinates: inner tails map into the
inner collar uniformly by compactness, reflection gives
analytic extension, and the local embedding near the
filled set gives degree one. No local connectivity of
T or global immersion embedding is necessary.

The actual full pulled carrier T_1 contains Γ_1(T), so
ring monotonicity and degree-two covering of complements
give

\[
 m'=\operatorname{mod}(Y)
 \ge\operatorname{mod}(U^1\setminus T_1)=m/2.
\]

Apply (3). Since V(F)=1/m, every pair of accesses of
the old carrier on the Y inner circle has angular
distance transformed by a factor between
exp(-π V(F)) and exp(π V(F)) under I_1.
In particular a target pair separated by a fixed c>0
has Y-source separation at least c exp(-π V(F)).
This is precisely an exponential-in-width bound
of the scale used by (2).

However the actual raw restriction annulus is
X_1=U^1 minus T_1, not Y. The inclusion X_1→Y
does not map the entire inner ideal circle into
the inner ideal circle: added carrier pieces land
in its interior. Formula (3) cannot be applied to
that inclusion as if it had the stated boundary
hypothesis. Even when both particular accesses
have old local charts, a global inner-end boundary
condition on the rest of the circle is missing.

Thus the old-carrier immersion alone has the needed
exponential distortion control. The remaining
calibration can be isolated to the effect of
adding the actual preimage carrier T_1 minus Γ_1(T),
and to locating the two qualified anchors inside
the parent cap. The symmetric narrow-gap example
in SYMMETRIC_SEPARATOR explains why an arbitrary
added branch can carry independent geometric cost.
No uniform bound for this remaining attachment
distortion is proved here, and the theorem is not
misapplied to a nonproper full inner-circle map.

No new ledger status or kernel claim for the
analytic proof is made. The existing finite
collision-gain and geometric-series modules
check the algebraic portions of the response.
Prepared with ChatGPT assistance; specialist
review pending.

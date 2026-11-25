# Quadratic deck separator, its actual host accesses, and a free-response obstruction

2026-11-25. Continuation of [CANONICAL_LIFT_AND_DIRECTION.md](CANONICAL_LIFT_AND_DIRECTION.md).
The result proves the full-filled-continuum separation portion of
line 1602 under explicit monotone-model hypotheses, and identifies
two attachment hosts in the full preimage carrier. The last section
is a genuine holomorphic double-cover countermodel to deriving
free-condenser calibration from symmetry and separation alone.
No native stationary counterexample or ledger promotion is claimed.

## 1. Full physical separation

Use the actual same-filled-set quadratic-like germ of a periodically
repelling, prime primitive pseudo-quadratic-like map. Write F:K→K,
c for its unique critical point, a=α_F for the dividing fixed point,
and a'=α^1 for its other preimage in the open critical limb Ω_0.
Write Q_0=K_0 for the critical small Julia set. Let C_0 be the closure
of Ω_0 and C_n the closure of Ω_n=φ_0^n(Ω_0), n≥1, for the selected
critical inverse branch. Set a_n=α^n and Q_n=φ_0^n(Q_0).
The [selected predecessor theorem, §4](../../mlc_unified/kkl_stationary_n2_selected_predecessor_endpoint.md)
gives the singleton boundary a_n of Ω_n in K, nested C_n, and
the homeomorphism F^n:C_n→C_0 (identity at n=0).

Assume a monotone semiconjugacy m:K→D onto a dendrite,
with a degree-two model polynomial G on the plane satisfying
mF=Gm and G^(-1)(D)=D. Assume the model critical point m(c)
is the only finite critical point of G, the fibers over m(a)
and m(a') are the respective singletons, and

\[
 m^{-1}(m(c))\subset Q_0. \tag{1}
\]

These are the transported periodically-repelling Kiwi-model inputs
with the canonical saturated primitive little Julia set. The
critical-fiber identification and singleton-cut hypotheses are
treated in [CUTPOINT_PRUNING.md, §5](../maximal_global_closure_20261123/CUTPOINT_PRUNING.md)
and the saturation proof in
[the native marked realization, §1](../issue40_native_marked_realization_local_gates_20261124.md).
In particular (1) does not assert that the critical point is
preperiodic or its physical fiber is singleton. For an independently
designated native little Julia set, verify the saturated-set
identification. In the locally connected dendrite case take m=id.

**Theorem 1.** At every available selected depth n, no connected
subset of K minus Q_n meets both a_n and C_(n+1).
If T is the full-hull carrier satisfying T∩Ω_b=∅, then for n≥b
no connected subset of K minus Q_n meets both T and C_(n+1).
These are separation statements in the entire filled continuum K
and hence in its full carriers, not in the ambient plane minus Q_n.

Proof. The deck involution σ of a degree-two plane branched cover
extends at its simple critical point, its only finite fixed point.
This follows from the connected two-sheeted covering off the critical
value and the local degree-two branch chart. Since G^(-1)(D)=D,
σ preserves D. The distinct points u=m(a), v=m(a') have
G(u)=G(v)=u, so σ swaps them. The unique arc [u,v] is invariant.
In a parameterization by [0,1], the induced continuous function s
satisfies s(0)=1 and s(1)=0. The intermediate value theorem for
s(t)-t gives a fixed point. Hence m(c) belongs to the open arc
(u,v). This is not a metric-midpoint claim about physical K.

The singleton-cut component correspondence of CUTPOINT_PRUNING,
Lemma 4.1, identifies Ω_1 with the inverse image of one component
of D minus v. This component does not contain u since a∉C_1.
Thus the arc from u to m(x) for any x∈C_1 contains v, including
x=a'. Every connected subset E of K containing a and x has
connected image m(E), which contains that arc and therefore
m(c). Consequently E meets m^(-1)(m(c))⊂Q_0. This proves
the base case for connected sets, not merely paths.

For n≥1 define r_n:K→C_n by the identity on C_n and the
constant a_n off C_n. This is continuous by closed pasting on
C_n and K minus Ω_n. The two definitions agree at the
singleton boundary. Since a_n∉Q_n, this retraction sends any
set avoiding Q_n to a set still avoiding Q_n. Thus if E is
connected, avoids Q_n, and meets both K minus Ω_n and
C_(n+1), the connected set F^n(r_n(E)) in C_0 avoids Q_0
and contains a and a point of C_1. Contradiction. At n=0
the same retraction onto C_0 extends the base assertion to
K minus Ω_0. For n≥b, the nested-limb pruning gives
T⊂K minus Ω_n. QED.

The base Q_0 is disjoint from C_1: if it met Ω_1, connectedness
and the singleton boundary a' (which avoids the cycle) would
put Q_0 wholly in Ω_1, contrary to F(Q_0)=K_1 lying in the
next rotational limb. Thus the specified sides really avoid
the separator. The inverse branch transports this disjointness.

This proves the continuum-separation portion of
KKL_STATIONARY_SELECTED_SEPARATOR_REALIZATION in the stated
model setting. It excludes bypasses *within K* even via a
competing route outside the selected sheet. It does not
force an ambient Wave trace to meet Q_n, construct the
named retained occurrences, or verify the full marked action.

## 2. Opposite attachment hosts in the genuine source

For this refinement assume also the full saturated carrier
model with the finite graph of little-Julia vertex bodies,
connecting edges and preperiodic contact-cut hypotheses of
[the native marked realization](../issue40_native_marked_realization_local_gates_20261124.md).
Use the actual one-step source disk S=U^1, immersion I_1
and proper degree-two map f=P_1. Write J=Γ_1(Q_0),
B=f^(-1)(T), K'=f^(-1)(K). The full inverse of K_1 is
the connected critical preimage J by the whole-component
degree-two property. The holomorphic deck involution τ
of f preserves J, B and K', and swaps Γ_1(a), Γ_1(a').
This follows also by disk normalization to z².

By Theorem 1 the two points belong to distinct components
X_-,X_+ of B minus J, and τ swaps these components. Both
points are in B since they map to a∈T. The model B is the
entire preimage carrier, a full saturated lift of the model
preimage of the hull. The unique model arcs from the deep
cut to points of Γ_1(C_1)∩B lie in the model preimage hull
and avoid the model J. Their lifts are connected by
monotonicity and saturation, so the deep-side portion
lies in X_+. The same reasoning at a places the root-side
portion Γ_1(T minus Ω_0) in X_-.

The model branches leaving J_model have unique roots,
by arc-convexity of subdendrites. The two designated
branches attach through connecting edges incident to this
vertex body. Their contact points are among the finite
preimage-edge contacts on J_model. Every such contact is
preperiodic: a sequence along the incident edge tends to
the contact and maps to points of the original model T
outside K_1, tending to its contact on K_1. This uses J
being the entire inverse of K_1. The original finite
edge-contact set is forward invariant by the separated
component argument along the primitive cycle in the
native marked realization, §2. Thus each of these model
contacts has a singleton physical fiber.

The [model exteriorization/unique-host theorem, §1](../issue40_ambient_angle_exactness_20261124.md)
for nested model dendrites identifies one old J-model
attachment access for each branch. The
[monotone impression correspondence, Theorem 1](../issue40_monotone_model_prime_end_bridge_20261124.md)
places the physical limiting circle angles of that branch,
in the exterior coordinate of J, in the fiber of this one
model access. Since the contact fiber is singleton,
Corollary 2 of that note makes the boundary fiber
singleton as well. Hence the two physical branches have
actual unique hosts e_-, e_+ on the inner ideal circle
of S minus J, with singleton physical impressions.

In the actual annular covering f:S minus J→U minus K_1,
the round annulus coordinate makes the map a degree-two
monomial up to scaling and rotations. Its deck involution
acts on the source inner circle by a half-turn. Uniqueness
of the host access and τ(X_-)=X_+ give

\[
 e_+=\tau_*e_-,\qquad e_+\ne e_-. \tag{2}
\]

Their separation in that source annulus coordinate is
exactly half the circumference. Their covering images
are the same target access of K_1, as expected.
This is not a collision theorem about complete paths.

The compatible selected univalent localizations of
[the two-sided noncollision source reduction, Lemma 4.1](../../mlc_unified/kkl_stationary_tsnc_source_reduction.md)
transport these two local host germs to the Q_n root and
deep sides whenever the corresponding branches are pulled
back by the selected inverse. They remain distinct, with
their cyclic order and common two-sheet phase at the
terminal critical arrow. No half-circumference claim is
made for a differently normalized collar at every depth.
This advances the side-existence part of AR(s), not the
construction of a proof-used parent restriction landing
on a designated open fine marking interval. In particular
the hosts used to distinguish sides are not the variable
endpoints of a positive-width family. Landing at a fixed
singleton gate is a zero-width exception.

## 3. Why antipodal hosts do not bound the free energy

Here is an exact genuine degree-two covering example.
It strengthens the earlier planar narrow-gap model in
DOUBLE_CROSSING_CHARGE. It does not satisfy the native
prime primitive filled-dynamics hypotheses.

Take S=D(0,5), U=D(0,25), f(z)=z², τ(z)=-z and
J=[-1,1]. Then f(J)=[0,1]. For 0<δ≤1/2 let A_δ be
the tree in the right half-plane consisting of segments:

- (1,0) to (2,0);
- (2,0) to (2,3) to (δ,3) to (δ,2);
- (2,0) to (2,-3) to (δ,-3) to (δ,-2).

Put B_δ=-A_δ and L_δ=J∪A_δ∪B_δ. Every vertex has
squared norm at most 13<16, so all segments lie in
D(0,4). The trees A_δ and B_δ are disjoint and meet
J only at their respective roots 1 and -1. Thus L_δ
is a full embedded finite tree, and J separates the
two branches in L_δ. Their attachment accesses on
the inner ideal circle of S minus J are opposite.

The image T_δ=f(L_δ) is also a full finite tree:
f is injective on A_δ (all points have positive real
part), and f(A_δ) meets [0,1] only at 1 because
z²∈[0,1] implies z∈[-1,1]. Hence T_δ is two trees
joined at one point. The complete two-root enumeration
gives f^(-1)(T_δ)=L_δ inside S. The actual annular map
S minus L_δ→U minus T_δ is a connected degree-two cover.

The vertical widths satisfy

\[
 W(U\setminus T_\delta)\le 2\pi/\log(25/16),
 \qquad W(S\setminus L_\delta)=2W(U\setminus T_\delta).
\]

The first estimate uses T_δ⊂closed D(0,16) and
ring-modulus monotonicity. The small-continuum annuli
S minus J and U minus [0,1] are fixed, so their
whole cyclic widths are finite constants independent
of δ.

For every y∈[2,3), the open horizontal segment from
-δ+iy to δ+iy joins B_δ to A_δ, avoids J and L_δ
in its interior, and lies in S. For every smooth u
equal to one near A_δ and zero near B_δ, the fundamental
theorem of calculus and Cauchy–Schwarz give

\[
 \int_{-\delta}^{\delta}|\partial_xu(x+iy)|^2\,dx
       \ge 1/(2\delta).
\]

Integrating in y yields

\[
 \boxed{\inf_u\int_S|\nabla u|^2\,dA\ge 1/(2\delta).} \tag{3}
\]

The proper horizontal path family in S minus L_δ has
exactly that modulus: the constant density 1/(2δ)
on the rectangle and zero elsewhere attains the
matching upper bound. This lower bound uses a full
rectangle away from J, not a singular corner.

Thus even exact deck-opposed hosts, full-carrier
separation and a genuine finite annular covering
do not bound free internal energy by the separator's
local width and vertical width. The example is not
a native F with critical rotation 1/q, a forward
invariant primitive carrier, or a native R(F).
It does not refute the native free-response target.
It rules out a derivation using only the separator
and deck data of Sections 1–2. Opposite attachment
angles are not opposite angles of every point in
the two branches.

## 4. Remaining target

The full physical separator under the saturated
model assumptions is now established, and the two
host accesses are actual distinct ideal points under
the additional preperiodic contact-cut hypotheses.
Neither theorem supplies the native retained Wave
portions, or bounds the free internal energy. A
source-specific restriction on actual root/deep
connecting Wave traces, or a dynamic estimate
excluding the near-contact mechanism of §3 in the
relevant subclass, is still needed.

The companion StationaryDeckSeparator.lean isolates
the interval fixed-point argument, the retraction
logic, and the rectangle energy algebra. It does not
formalize the dendrite or prime-end topology, or
the conformal modulus argument. No proof-obligation
ledger status is changed. Prepared with ChatGPT
assistance; independent specialist review pending.

# Stationary stage-endpoint census: a renormalization-width charge without deep-branch calibration

2026-11-25. Written analytic and dynamical proof, with a separate
finite counting kernel. This note continues
[PREFIX_POTENTIAL_CHARGE.md](PREFIX_POTENTIAL_CHARGE.md) and
[VARIABLE_END_EXIT_TRANSFER.md](VARIABLE_END_EXIT_TRANSFER.md).
It gives a uniform terminal estimate for a physically specified
subclass of the stationary family without assuming the selected
deep encounter or its condenser calibration. The complementary
edge/vertex endpoint cases and the native telescope remain open.

## 1. Setup and statement

Let F be a hyperbolic-disk pseudo-quadratic-like map in the primitive
setting of the source Kahn–Kapiamba–Lyubich (KKL), arXiv:2606.27272v1,
with disjoint primitive cycle K_0,...,K_(P-1) and at most b members
in the physical open critical limb Ω_0. Write R=W(RF) and V=W(U minus T).
Use the actual forward-invariant full carrier T⊂K containing the
whole little Julia cycle, and the actual finite Kahn maps I_j,P_j,
filled graphs Γ_j, and degree 2^j from
[filled-graph naturality](../../mlc_unified/pql_iterate_filled_graph_naturality.md).
Take h<P. The finite annuli and covering
P_j:U^j minus P_j^(-1)(T)→U minus T are supplied by
[ANNULAR_RESTRICTION_PROPERNESS.md](../maximal_global_closure_20261123/ANNULAR_RESTRICTION_PROPERNESS.md)
under the stated full-carrier hypotheses.

Suppose a simple proper parent α has an actual sequential retained
chain δ_0=α,δ_1,...,δ_h of simple proper output paths, each with both
ends on the inner ideal circle of U minus T. This is the relevant
stationary Wave type. For an unbreakable parent with singleton
simple-Wave outputs, there is at least one such chain of witnesses:
at each stage choose an actual retained restriction projecting
to the unique next output. No uniqueness of that witness or
survival of its discarded shoulders is assumed.

Call a stage j **Julia-critical** if at least one of its two
physical endpoint limits lies in a member of the original cycle
contained in Ω_0. Count stages, not the number of endpoint labels
or occurrences. For parents of infinite length or with no physical
limit use the zero-width exception described below. A sufficient
ideal formulation is an actual endpoint impression contained in
one of those little Julia sets; a symbolic critical-limb label alone
does not suffice.

**Theorem.** Let A_J be any family of such parents admitting chains
through h with at least b+1 Julia-critical stages among 0,...,h.
Then

\[
 \boxed{W(A_J)\le b(3\cdot2^h-2)R.}
 \tag{1}
\]

At the source horizon h=b+2<P, this charges every parent for which
all but at most two stages have a Julia-critical endpoint. The
coefficient depends only on b, not on the primitive period,
rotation denominator or the individual endpoint components.

No full-hull quotient identification is needed for (1) beyond
the full-carrier hypotheses already displayed. Section 5 obtains
a separate bounded-total-visit theorem using the stronger
full-hull/singleton-cut hypotheses.

## 2. Actual endpoint records from segmented retained chains

By the [segmented reconstruction theorem](../../mlc_unified/kkl_stationary_segmented_occurrence_binder.md),
Theorem 6.1, every prefix has a compatible path Θ_j in the actual
fiber product with

\[
 I_j\Theta_j=\alpha a_{0|j},\qquad P_j\Theta_j=\delta_j,
 \tag{2}
\]

where a_{0|j} is a homeomorphism onto an open interval
(a_j,d_j)⊂(0,1). Choose orientations along the original parent;
the windows are nested, a_j nondecreasing and d_j nonincreasing.
For j=0 use (a_0,d_0)=(0,1). The one-step occurrence maps exist
because the source restriction is simple (its covering image
is simple), the immersion is locally injective, and its image
is contained in the preceding simple path. The induced parameter
map is locally injective on an interval and hence strictly
monotone. Each choice is of a genuine retained restriction.

There is a useful properness consequence not requiring the earlier
coordinates to be full proper stage paths. Since the terminal
projection in (2) is the entire proper δ_j, Θ_j is its lift under
the actual annular covering P_j. A finite annular covering in
round coordinates is a monomial map of degree 2^j, up to conformal
coordinate changes; its ideal extension is a boundary covering.
Thus Θ_j itself has proper ideal endpoints in the full pulled
annulus U^j minus P_j^(-1)(T). This does NOT make its earlier
coordinate segments proper, recover the discarded shoulders, or
identify the selected deep branch. It only proves properness of
the reconstructed prefix trace in its actual full host. Since
I_jΘ_j is an embedded subpath of α, Θ_j is maximal among lifts of
α in that host: any continuation through a window endpoint would
give an interior limit in conflict with the proper ideal endpoint.

Discard the zero-width family of parents of infinite Euclidean
length in unit-disk coordinates, using arbitrarily small positive
constant densities as in [EXCEPTIONAL_WIDTH_REDUCTION.md](EXCEPTIONAL_WIDTH_REDUCTION.md).
Every remaining α extends physically continuously to [0,1],
with endpoints on T or the ambient outer boundary. For the
inner-ended parents here both lie on T.

At an endpoint of Θ_j, let t=a_j or d_j be the limiting original
parent parameter. The corresponding δ_j tail tends in its ideal
annulus to an inner end. Its physical cluster points all lie on
T, and its late tail lies in a compact neighborhood of T inside U.
By properness of P_j, the Θ_j tail lies in a compact subset of U^j.
Every source accumulation point z satisfies

\[
 P_j(z)\in T,\quad I_j(z)=\alpha(t),\quad z\in K^j.
\]

The full filled-set identity forces α(t)∈K, and the unique
filled-graph preimage forces z=Γ_j(α(t)). All accumulation
points therefore coincide. Continuity gives the genuine physical
endpoint formula

\[
 \boxed{\lim \delta_j=F^j(\alpha(t))\in T.}
 \tag{3}
\]

This proves physical landing of every inner output endpoint from
the one parent finite-length condition, even for non-locally-
connected T. No summability of the projected curve lengths
is required. If t is interior, α(t) is an actual point of K
outside T. If t is 0 or 1, it is an original carrier landing
point. Formula (3) does not assert that this point lies in the
specific selected inverse limb.

Thus at each Julia-critical stage choose one endpoint and record
t_j∈[0,1], x_j=α(t_j), k_j with F^j(x_j)∈K_(k_j)⊂Ω_0.
These are actual endpoint values on actual prefixes. Choices
may differ from stage to stage; the proof below needs no Borel
choice of a chain or endpoint.

## 3. Final-component census and degree budget

For each such record at stage j, its final canonical graph lift
Γ_h(x_j) belongs to a component Q of P_h^(-1)(K_(k_j+h-j)).
The latter compacta are the actual deleted continua of the
final little-Julia surface. We show two facts.

**A. No final component accounts for more than b stages.**
Suppose records at times j<l lie in the same final component Q.
Let C=I_h(Q)⊂K. By the graph identity C is an entire component
of F^(-h)(K_k) for its unique final target label k.
Its image F^j(C) is connected, lies in F^(-(h-j))(K_k), and
meets K_(k_j). The latter is an entire inverse component of
K_k: apply the primitive whole-component inverse property
(filled-graph note, Lemma 4.A) successively, using confluence
and component composition (Lemma 3.3). Hence F^j(C)⊂K_(k_j).
The same argument at l gives F^l(C)⊂K_(k_l).
Consequently

\[
 k_l=k_j+l-j\pmod P .
\]

Since 0≤j<l≤h<P, these are different members of the cycle.
All the indices counted for Q are in the critical limb, so
there are at most b. More than b Julia-critical stages force
at least two *distinct* final components. This includes the
case where both records occur at original parent endpoints.

**B. One uniform bank contains all possible recorded components.**
For every j=0,...,h and every critical-limb target K_k, include
the final graph lifts of all components of F^(-j)(K_k) in a bank
B_h, taking the union as a set (duplicate components are not
new charges). For j=0 these are the original cycle components.
The component composition just cited implies that each such
component remains an entire component of F^(-h)(K_(k+h-j)),
and thus lifts to an entire final deleted continuum.

Let d_{j,C} be its whole-end degree at stage j. The per-target
degree census of the variable-end note, Lemma 5.1, gives
sum_C d_{j,C}=2^j. At stage 0 the degree is one.
The subsequent h-j arrows along the primitive cycle meet
the critical small Julia set at most once, because h<P.
Their composed proper degree e_{j,k} is therefore at most
two, and is one for j=h. These are whole peripheral degrees:
choose shrinking Jordan neighborhoods avoiding the other
cycle components and critical values, and compose the
actual degree-one or degree-two restrictions along the cycle.
For the earlier j-step component, a sufficiently small
target Jordan neighborhood pulls back into the graph
embedding neighborhood; this follows by compactness and
the nested full-inverse components from Lemma 5.1.
Thus the prefix and suffix restrictions compose in the
physical graph chart. Their isolating inverse compactum
is the entire final component C. Filled-graph Lemma 3.4
transports the composite degree to its whole final ideal
circle, so d_{h,C}=e_{j,k}d_{j,C}. No multiplication of
unverified local access labels is used.

Summing the union of the bank, overcounting only in the
safe upper-bound direction, gives

\[
 \sum_{Q\in B_h}d_{h,Q}
 \le b\left(2\sum_{j=0}^{h-1}2^j+2^h\right)
 =b(3\cdot2^h-2).
 \tag{4}
\]

Every member's cyclic local width is at most d_{h,Q}R,
by the whole-end covering identity and KKL Lemma 4.3,
equation (4.6), as used in the variable-end note.

## 4. Two physical records including parent endpoints suffice

Here extend the previous two-interior-hit and one-hit-landing
theorems to two records at times in the closed interval [0,1].
The relevant physical point at an original endpoint is its
actual limit, not an arbitrary point in an impression.

Work outside a further zero-width family supplied by the
simultaneous finite-energy metric of
[EXCEPTIONAL_WIDTH_REDUCTION.md](EXCEPTIONAL_WIDTH_REDUCTION.md),
for I_h and the finite final deleted-continuum package.
Every actual lift then has finite disk-coordinate length, and
near a deleted component its annular collar coordinate also
has finite length.

Take the two distinct component records just proved, and
order their times t<s in [0,1]. They are unequal because
I_h on K^h is injective and the two continua are disjoint.
Start the canonical unpunctured lift at Γ_h(α(t)) in Q.
When t=0 the actual physical endpoint is inside U and its
canonical source point inside U^h; a local inverse chart
gives the lift of the initial tail, with that physical limit.
Continue toward s by maximal local inversion.

If there is compact accumulation at an interior stopping
time, the local inverse chart extends the lift, so this
cannot be a maximal failure. If the lift reaches s (including
s=1 by physical continuation at a compact limit), its
limit is the canonical graph point in the second component,
by the full inverse identity and injectivity on K^h.
Otherwise it escapes to the ambient source outer circle
by the finite-length envelope. These are the only alternatives:
at s with no compact accumulation the same outer escape
holds. In the compact case, continuity and the inverse chart
at the unique compact accumulation point also extend the
lift to s if that endpoint time is not interior.

If another deleted component is reached, choose its first
hit and the last preceding Q-hit on that compact interval,
allowing the initial or final closed endpoint times.
If none is reached before escape, take the last Q-hit
before escape (attained and bounded away from the escaping
endpoint by compactness). The open subarc between these
times lies in the final little-Julia complement. Its two
ends are either Q and a different deleted component, or Q
and the ambient outer circle. Finite collar-coordinate
length supplies the inner ideal endpoints, and finite
disk-coordinate length supplies the outer ideal endpoint.
Neither end extends in the final complement, so it is an
actual maximal ideal-proper restriction. This uses only
two physical records; no two retained occurrences,
marking survival of the final restriction, or noncollision
after covering projection is required.

To finish the width bound without a measurable choice of
records or lifts, use a direct metric version of the cyclic
end argument. For any bank member Q take the canonical
cross-annulus density on its peripheral cyclic cover of the
final complement, with length at least one on every
cross-annulus curve and squared area L_Q, the local cyclic
width. Push the density to the final complement by the
all-sheet square-sum construction of the exceptional-width
note. Every actual proper curve from Q to a different ideal
component has a lift crossing that annulus (the ideal
endpoint argument of maximal exit transfer, Theorem 3.1);
the pushed density dominates its length and has area L_Q.
This is an all-path estimate, not an assertion of injective
support for an intersecting curve family.

Combine the finitely many bank metrics by square-sum and
then push through I_h by square-sum again to U, restricting
to U minus T. Area is at most sum_Q L_Q; every good parent
has a literal subarc which is the image of an eligible
exit, so its length is at least one. The exceptional family
has zero modulus by the separate envelope argument. This
proves (1) from (4) even without Borel selection of a
particular chain or exit. In the Borel stationary setting
the earlier countable selection route is also available
once the pointwise existence has been supplied.

The proof does not say that the original two fixed
predecessor components are hit, or that the other endpoint
of the extracted exit belongs to the bank. In particular
no half-bank factor is asserted.

## 5. Bounded *total* critical visits of carrier points and window births

The full-hull/singleton-cut hypotheses of
[CUTPOINT_PRUNING.md](../maximal_global_closure_20261123/CUTPOINT_PRUNING.md)
give another improvement. Here require them at all the
finitely many preimages of the dividing fixed point α_F
through h<q≤P. The transported Kiwi full-hull construction
has singleton fibers at every preperiodic point; an
independently named native carrier still needs the stated
identification.

For every t<q, the entire closed critical limb H_0 avoids
all critical values of P_t (the actual finite-iterate
critical-value lemma in
[MONODROMY_COLLISION.md](../maximal_global_closure_20261123/MONODROMY_COLLISION.md)).
Choose a Jordan disk around H_0 avoiding these critical
values. Its complete inverse has 2^t univalent disk
components. In each, the inverse of Ω_0 is a connected
relatively open subset of K^t, with closure the inverse of
H_0 and exactly one boundary point, the inverse of α_F.
It is clopen in K^t minus that point, hence an entire
component there. By the filled-graph homeomorphism the same
is true for every branch of F^(-t)(Ω_0) inside K. The cut
point is preperiodic and outside the original primitive
cycle (otherwise forward invariance would place α_F in it).
For t=0 use Ω_0 itself.

If x∈T and F^t(x)∈Ω_0, the branch containing x meets T.
The one-cut full-hull theorem supplies a whole original
little Julia component in that branch. For 0≤j≤t, its
image and F^j(x) lie in the same physical limb: the image
of the branch is connected and avoids α_F, since a hit
of the fixed α_F would contradict its final image in Ω_0.
Thus this one little Julia component shadows the complete
finite limb itinerary of x through t. Its cycle members
at distinct times are distinct because t<P.

Choose t to be the last critical visit of a carrier point
within 0,...,h (if none, the count is zero). We obtain

\[
 \boxed{
 \#\{0\le j\le h:F^j(x)\in\Omega_0\}\le b
 \qquad(x\in T,\ h<q).
 }
 \tag{5}
\]

Unlike the earlier consecutive-stay result, (5) allows
arbitrary departures and returns. The same argument says
that any point of K with more than b visits by its last
critical time t lies in a branch of F^(-t)(Ω_0) disjoint
from T. Only the open branch is proved disjoint; its cut
point can meet T. No quantitative separation is asserted.

For a chain as in §2 in which every stage has at least
one endpoint physically in Ω_0, label one such endpoint
by its original parameter t_j. Every distinct endpoint
parameter t has a first birth k: the first prefix window
having it as an endpoint. At k, (3) says F^k(α(t))∈T.
Every later occurrence of that same endpoint in the chain
has the physical value F^j(α(t)). Hence (5) bounds the
number of stages assignable to this one t by b, applied
to the carrier point at its birth and the shorter
remaining horizon. The original endpoints 0 and 1 are
included with birth 0. A parameter born at k>0 is strictly
inside the earlier window (unless it was already an
endpoint, contrary to first birth); at earlier prefixes
its orbit avoids T, since these prefix paths are interior
in U minus T. Thus its birth records an actual first
physical encounter with the pulled carrier, not a new
symbolic access name.

If e counts distinct interior endpoint parameters born
in the chain (not just the chosen critical records), then

\[
 h+1\le b(2+e),\qquad
 e\ge\max(0,\lceil(h+1)/b\rceil-2).
 \tag{6}
\]

In particular a stationary chain through h=2b<q cannot
have all its windows equal to the original full window.
It has at least one actual interior encounter with a
pulled carrier. This inference does not assume the line
1600 selected deep-branch assertion. Using a longer
stationary horizon in the full KKL proof would still
require its independently justified nested-family
telescope at that horizon.

The critical-endpoint premise in (6) is physical. A
contour whose impressions are contained in Ω_0 plus
α_F suffices modulo zero: exclude the finitely many
preimages of α_F at each finite prefix using the
countable physical-gate zero-width lemma (when the
corresponding original point is a parent endpoint).
For interior hits of a specified finite set the same
logarithmic singularity proves zero width, since a
nonconstant curve approaching one of those points from
outside has infinite length in that finite-energy metric.
No width-zero assertion is made for all carrier-edge
landing points. For a saturated model, the contour
locality follows from the monotone impression comparison
cited in the prefix-potential note, without identifying
the disputed unrestricted immersion marking.

## 6. A remaining internal, rather than outer, calibration

For the independent deep-encounter capacity D_b from the
prefix-potential note, let E_free be the infimum of smooth
0≤w≤1 potentials on U equal to one near C_(b+1) and zero
near T, with no outer boundary condition. Let W(F) be the
full exterior width of K. Choose a compactly supported
potential v equal to one near K with energy arbitrarily
close to W(F), using the annular radial cutoff in
U minus K and extension by its constant value near K.
The minimum min(v,w) preserves both specified electrodes
and has compact support. Its a.e. gradient energy is at
most the sum of the two energies (the gradient agrees
with an active branch). Smooth approximation preserves
the plateaus and does not increase the limiting energy.
Consequently

\[
 \max\{E_{\rm free},\,\operatorname{cap}(C_{b+1},\partial U)\}
 \le D_b\le E_{\rm free}+W(F).
 \tag{7}
\]

The lower inequalities are inclusion of admissible classes.
In a branch where M-amplification has not already occurred,
W(F)<M R(F). A uniform internal free-response bound would
therefore suffice for the original grounded calibration,
without a separate outer-collar estimate. No such bound
is derived here; the previous planar countermodels show
why qualitative clearance alone is inadequate.

## 7. Exact remaining native scope

For h=b+2 the Julia-critical census charges any parent with
at least b+1 such stages, with a coefficient depending only
on b. All other parents have at least three stages without
a physical critical little-Julia endpoint. They are the
remaining stage-endpoint residual, not a width-zero family.
Independently, (5)–(6) force actual carrier encounters under
the full-hull hypotheses and a sufficiently long stationary
horizon, but do not put those encounters on a selected deep
limb or little Julia set. They can fall on newly added
carrier edges. The free internal calibration in (7) and
an estimate or terminal response for the edge-only residual
remain open.

The companion StationaryEndpointVisits Lean module checks
the finite occupancy/pigeonhole and geometric-series
accounting; the topological, conformal and source-specific
proofs above are written mathematics. No ledger promotion,
native stationary theorem, H1–H4, UPTCR or MLC claim.
Prepared with ChatGPT assistance; human specialist review pending.

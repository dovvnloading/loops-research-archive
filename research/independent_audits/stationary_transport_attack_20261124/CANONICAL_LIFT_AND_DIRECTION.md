# Full canonical lifts modulo a vertical charge; cap and direction recovery

2026-11-25. Written analytic extension of
[STAGE_ENDPOINT_CENSUS.md](STAGE_ENDPOINT_CENSUS.md) and
[PREFIX_POTENTIAL_CHARGE.md](PREFIX_POTENTIAL_CHARGE.md).
The vertical charge and complete-lift conclusions below require no
corrected marked action. The directional and stationary applications
explicitly require an actual protected contour block and the
geometric coarse/fine marking interpretation. They do not validate
the literal unrestricted maximal-subset definition of KKL A.3.2.

## 1. Automatic vertical charge for incomplete canonical lifts

Let F be a hyperbolic-disk pseudo-quadratic-like map with connected
filled set K and a nondegenerate full compact forward-invariant
carrier T⊂K containing the critical point. Let

\[
 I_h,P_h:U^h\longrightarrow U,\qquad
 T_h=P_h^{-1}(T),\quad X_h=U^h\setminus T_h,\quad X=U\setminus T.
\]

Use the actual finite Kahn tower, the filled-graph inverse Γ_h of
I_h on K^h, and the degree 2^h annular covering P_h:X_h→X from
[filled-graph naturality](../../mlc_unified/pql_iterate_filled_graph_naturality.md)
and [annular properness](../maximal_global_closure_20261123/ANNULAR_RESTRICTION_PROPERNESS.md).
In particular I_h(X_h)⊂X, T_h is a full continuum, and
Γ_h(T)⊂T_h. Put V=1/mod(X)=W(X).

Consider any family of simple proper inner-to-inner parent paths
in X. Discard the family of infinite disk-coordinate Euclidean
length: positive constant densities tending to zero in area prove
that its width is zero. Every remaining parent α has physical
endpoint limits p_0,p_1∈T, because it is proper at the inner circle
and finite-length in the ambient disk.

Start the actual unpunctured inverse lift of α at Γ_h(p_0).
Call α **complete at h** if this lift extends continuously across
the closed parameter interval [0,1]. Its terminal point must be
Γ_h(p_1) by the full inverse-filled-set identity. The property
is independent of reversing α (a complete lift can be reversed).
Write E_h for the noncomplete parents, with the discarded zero-width
family included if desired.

**Theorem 1 (automatic overflow).**

\[
 \boxed{W(E_h)\le 2^h V.}
 \tag{1}
\]

Indeed the canonical lift exists initially by a local inverse
chart at Γ_h(p_0). If its maximal lifetime ends before the last
parent time, any compact source accumulation would give a local
inverse extending the lift, contradiction. If the lifetime reaches
the final parent time and has a compact accumulation point, that
point is Γ_h(p_1), and the same chart gives a continuous terminal
extension. Hence every failure escapes all compact subsets of
U^h toward its outer end. There is a last time at which the lift
meets T_h, allowing time zero: compactness of T_h and escape make
the set of contact times bounded away from the lifetime endpoint,
and the set is closed on a suitable compact time interval.

The subsequent literal lift subarc is in X_h, beginning at its
inner physical boundary and escaping toward the ambient outer
boundary. In round annular coordinates its radial coordinate
tends to the appropriate circle at each end. This follows by
separating the compact inner continuum from the outer end by an
annular collar; no angular landing or LC hypothesis is needed.
The standard radial cross-annulus density on X_h has length
at least one on this subarc, and area 1/mod(X_h)=2^h V by the
actual covering degree. Push this density through I_h using the
all-sheet square-sum metric from the exceptional-width reduction.
Its area is unchanged before restriction to X, and it dominates
the length of the selected literal parent portion. Add a
vanishing positive constant for the infinite-length parents if
necessary. This proves (1) with no measurable route selection,
injective global inverse, marking retention or additive error.

The same argument gives an eligible proper vertical restriction
modulo the finite-energy landing exception of
[EXCEPTIONAL_WIDTH_REDUCTION.md](EXCEPTIONAL_WIDTH_REDUCTION.md);
(1) itself needs only radial limits and does not depend on this
extra proper-landing statement.

A complete lift at h projects under every prefix immersion to
the unique canonical complete lift at each j≤h. This follows
from the actual commuting prefix projections and uniqueness of
a lift based at Γ_j(p_0). Thus one final-horizon charge (1)
handles all shorter prefix continuation failures simultaneously.
No sum over prefix escape families is needed.

## 2. Exact raw component windows and measurability

Assume α is complete at h. Denote its complete lifts at j≤h
by θ_j:[0,1]→U^j. The two filled-set identities imply

\[
 \theta_j(t)\in T_j\quad\Longleftrightarrow\quad
 \alpha(t)\in K,\ F^j(\alpha(t))\in T .
 \tag{2}
\]

In particular define the closed contact sets

\[
 D_j=\alpha^{-1}(F^{-j}(T))\subset[0,1].
\]

Here F^{-j}(T) is the inverse set *inside K*; it is compact.
Forward invariance gives D_j⊂D_{j+1}, D_0={0,1}, and every
D_j contains 0 and 1.

**Theorem 2 (canonical raw-component exhaustion).** All actual
maximal raw I_j-restrictions of α in X_j having at least one
inner ideal endpoint are precisely the restrictions of θ_j
to the components of (0,1) minus D_j. They have two inner
ideal endpoints.

For the forward direction, let an actual raw restriction
have an inner ideal endpoint at original parameter time t.
Its late tail accumulates on the compact T_j. By continuity
of I_j, every source accumulation point z has I_j(z)=α(t).
Since z∈T_j⊂K^j, the full inverse identity makes it the unique
Γ_j(α(t)). The complete lift has that same value by (2).
A local inverse chart at this point identifies the restriction's
tail with θ_j; path-lifting uniqueness then identifies its
entire maximal trace. Conversely, each gap of D_j gives a
maximal lift in X_j with both endpoints physically in T_j,
hence with proper ideal limits by the maximal annular
restriction theorem. Its maximality is in the full actual
inverse trace; neither endpoint can be crossed within X_j.
Remote-sheet components with two outer endpoints may still
exist, and are not declared absent.

This gives an exact literal representation of all inner-ended
retained restrictions of a complete parent, before any marking
filter is imposed. A sequential chain of actual singleton
inner-Wave outputs reconstructs by the segmented prefix
theorem; at each j its terminal covering projection is proper,
so its prefix trace is one of these components. Its windows
are nested gaps of the actual nested contact sets. There is
no inference of one-shot equality of the filtered and sequential
actions. In particular an unretained raw component is not
declared retained merely by its presence in a gap.

### Borel strengthening

In a standard Borel atlas of finite-length parameterized
parents with the uniform path structure on the physical
extensions to [0,1], completeness at h is Borel. In fact it
is relatively open in the space of continuous extended paths
with endpoints in T, and its lift map is continuous there.
To see this, cover the compact image of a complete lift by
finitely many local inverse charts and subdivide the compact
parameter interval so that successive lift pieces use these
charts with overlap. On each closed subinterval the target
path lies a positive distance inside its target chart. A
sufficiently uniform-close parent, started at the nearby
canonical preimage of its first endpoint, has the same finite
chart continuation, and its lift is uniformly close. Shrink
the chart margins at the subdivision times to enforce the
overlaps. This gives openness and continuity, including the
initial and final times. The physical extension of a finite
length path in the original Borel atlas is obtained by
pointwise limits at its endpoint times, hence is Borel as a
continuous path (rational evaluations generate that structure).
The finite length predicate is Borel by rational partitions.

For each j enumerate the gaps of D_j by the first rational
interior time in a fixed enumeration of (0,1)∩Q. The two
endpoints of the gap containing a rational t outside D_j
are the last D_j point before t and first one after t.
These are Borel: contact with any fixed closed time interval
is tested by the zero minimum distance to F^{-j}(T) on that
interval, a continuous function of the extended parent.
Rational cut inequalities determine the gap endpoints.
Discard later rational seeds in the same gap. This gives a
Borel enumeration of the actual inner-ended raw restrictions
on the complete family, with their maximal windows.
Ideal endpoint limits are Borel by rational approaching
times and the annular charts. Native filter identification
remains a separate predicate, not proved by this enumeration.

## 3. A complete lift extends across its filled cap

The following elementary univalence fact is useful here.

**Lemma.** Let S,U be conformal disks and i:S→U a holomorphic
immersion, injective on a compact connected set A⊂S. Then
i is injective on a neighborhood of the planar filled hull
fill(A), and i(fill(A))=fill(i(A)), in disk coordinates.

First i is injective on some neighborhood of A. Otherwise
pairs of distinct points tending to A with the same image
have subsequential limits in A, which must agree by
injectivity on A. Local injectivity at their common limit
is a contradiction. The compact full continuum fill(A)
lies in S (S is simply connected); its boundary lies in A.
Choose a Jordan neighborhood of fill(A) compactly contained
in S whose boundary is sufficiently close to that boundary,
by the exterior Riemann-map exhaustion of a full continuum.
Thus i is injective on its Jordan boundary. The argument
principle counts the preimages of every point not on the
image Jordan curve with multiplicity, giving either zero
or one; the nonempty open image forces winding number +1
on the bounded image component. If there were an interior
collision mapping to the image curve, local openness would
move the common value off that curve and yield a collision
there, impossible. Hence i is univalent on the Jordan
neighborhood. It maps that disk onto the bounded image disk.
The bounded complementary components of A correspond
under this embedding to those of i(A), because both compacta
are inside the respective enclosing Jordan disks. This proves
the fill assertion. QED.

Apply the lemma to

\[
 A_j=\Gamma_j(T)\cup\theta_j([0,1]).
\]

Injectivity on A_j follows from simplicity of α in X,
I_j-bijectivity on Γ_j(T), and the fact that the interior
of the parent avoids T. Repeated physical endpoint points
are harmless: they have the same canonical preimage.
Consequently I_j is univalent across the filled cap of
each complete parent, together with the original carrier.
For an inner-to-inner simple crosscut with distinct ideal
endpoints, its disk-side cap in the annulus is exactly the
bounded complementary component obtained by adding the
physical crosscut to the full carrier. The local embedded
collars of Γ_j(T) and T identify their old inner ideal
circles even if the compacta are not locally connected.
Thus the full lifted crosscut and its disk-side cap have
the same oriented boundary access as the original parent.

The same lemma applied to the union of Γ_j(T) and finitely
many mutually disjoint complete parent lifts proves
simultaneous univalence on their filled hull. In particular
the inverse cap charts agree on overlapping cap interiors;
there is no assertion of a uniform enclosing neighborhood
over the entire infinite lamination, or of global immersion
injectivity. This removes the need to assume a prescribed
embedded cap for each good parent. The analytic dynamics
P_j composed with this inverse is defined on that actual
cap, agreeing with F^j wherever it meets K.

## 4. An oriented-component theorem with one protected block

The next result is a topological repair under explicit
marking hypotheses. It is independent of any asserted
general directionalization of the printed A.3.2 action.

Work at one stage with a complete parent α, its full lift θ
in Y=U^1 minus Γ_1(T), and the larger removed carrier
T_1 containing Γ_1(T), so X_1⊂Y. Let α and θ have
distinct ideal ends on their original inner circles.
Orient them with the disk-side cap on their left (equivalently
the counterclockwise base arc runs from the initial to
the final endpoint). By §3 these orientations agree.

Assume there is an actual connected inner ideal block J of
X_1 with the following **protected crest conditions**:

1. J contains a whole coarse marking atom and a whole fine
   marking atom. There are at least three fine atoms.
2. No inner end of any maximal raw component of θ in X_1
   belongs to the closure of J. All such ends are in fine
   marking atoms rather than at omitted fine cuts.
3. Some e∈J has an actual end-tail in X_1 approaching e,
   disjoint from θ and lying on the disk-cap side of θ in Y.
4. The retained action uses the stated geometric fine
   path condition (not subordinate to at most two fine
   atoms) and the one-coarse-atom exclusion. The untagged
   retained covering output is one simple proper
   inner-to-inner path δ.

A sufficient geometric realization of conditions 1–3 is a
protected old crest block: its ideal chart for the nested
carriers is a homeomorphism onto a subarc of the original
parent crest, with all its impressions in Γ_1(T); it contains
the complete specified fine/coarse atoms and avoids the
parent's endpoint accesses. An interior raw end in this
chart would give a physical encounter with T, impossible.
The original endpoint limits lie outside the chart.
Fine-cut landing exceptions themselves have zero width,
even for arbitrary competing raw lifts, by putting a
finite-area logarithmic point singularity at each cut in
annular coordinates and pushing through the immersion.
This is the same all-sheet construction as in the
exceptional-width note. This explains how to remove those
exceptions, but does not construct the protected chart for
every native crest.

**Theorem 3 (unique directed component and orientation).**
Exactly one maximal raw component γ has e in its disk-side
inner base. Its cap lies on the same local side of γ as the
full parent cap lies along θ. It is retained and maps to δ.

Indeed a component whose base contains e contains all J,
since no endpoint belongs to the closed block. The whole
fine atom in J separates its ends in the base: if the two
ends are in distinct fine atoms the base traverses at least
three, and if in the same fine atom its long base traverses
all other atoms. It is not subordinate to one coarse atom,
since it contains an entire coarse atom and both ends lie
outside the closed J. Hence this raw component satisfies
both geometric filters. Every such component therefore
projects to the unique simple δ. A finite annular covering
lifts the disk-side cap of a simple inner crosscut to
disjoint disk-side caps, each mapped homeomorphically,
with disjoint open ideal base arcs. This is because the
cap is simply connected and the covering extends to
the inner ideal circle. Its crosscut lifts are exactly
the corresponding cap boundaries. At most one of these
lifts can have e in its base.

It remains to prove existence and orientation. Choose a point
z on the tail in condition 3. It is in the cap of θ; it is
inside the disk-side cap of any raw component if and only
if that component's base contains e. This follows because
the tail approaches a nonendpoint and avoids all the
components. Choose w in the outer collar of X_1 disjoint
from the compact physical θ and the two carriers; w is
outside every cap in question. Join z to w by a path in
X_1 meeting θ in finitely many transverse crossings.
For this last topological step, straighten the proper
embedded arc θ in the old annulus Y by an annular
homeomorphism to a polygonal crosscut. The image of X_1
is open and connected, and a polygonal path inside it can
be perturbed to avoid polygon vertices and meet the arc
transversely finitely many times. Pull back this path.
Each crossing belongs to precisely one raw component,
since the joining path is in X_1.

Count signed crossings of θ, with departure from its
disk cap positive. Their sum is 1 because z is inside
and w outside. For each raw component γ, let ε_γ be +1
when its cap is locally on the same side as the full
cap along that arc, and −1 otherwise. The contributions
of that component sum to

\[
 \varepsilon_\gamma\,
 [\mathbf1_{\{z\text{ in its cap}\}}-
   \mathbf1_{\{w\text{ in its cap}\}}]
 =\varepsilon_\gamma\mathbf1_{\{e\text{ in its base}\}}.
 \tag{3}
\]

This is telescoping of the inside/outside indicator at each
transverse crossing, not a sum of homotopy labels. Only
finitely many components intersect this joining path.
Since at most one component can contain e, the sum of
(3) being 1 proves exactly one such component and its
positive orientation. Its retained output is δ. QED.

In particular the directed surviving restriction preserves
the parameter orientation relative to its cap, even if
its parameter window is a strict subinterval. Its covering
projection preserves that orientation because it maps the
corresponding cap conformally onto the target cap. This
proof does not claim that every raw component has the
same orientation, or that every raw component is retained.

## 5. Application to a critical-ending positive directed chain

The following is conditional on the geometric contour action;
it is NOT an inference from the unrestricted subset quantifier
of A.3.2. Use the actual native rotation 1/q with q>2,
the physical open limbs Ω_j, the critical limb Ω_0,
the selected inverse Ω_1^sel=φ_0(Ω_0), and the precritical
physical limb Ω_(q−1). The notation Ω_1^sel is the first
selected deep inverse inside Ω_0, not the next rotational
limb. Its closure is C_1 of the prefix-potential note.

Assume the following source-facing geometric data:

* the geometric degree-one contour collapse r from the
  pulled inner circle to the original circle, and the
  actual degree-two boundary covering p, with
  r^(-1)(BL_j) the connected correctly ordered limb blocks;
  p(r^(-1)(BL_0)) is the full target circle;
* actual precritical-limb locality: an inner access of the
  pulled carrier whose physical graph image belongs to the
  open precritical limb lies in r^(-1)(BL_(q−1));
* a protected crest block satisfying §4 in the pullback
  of some BL_k, 1≤k≤q−2, for each step in use;
* the full geometric retained filters and singleton
  simple inner output in §4.

In the saturated monotone full-hull model, the locality
condition has a topological verification. The model
precritical limb minus the dividing point is one
dendrite component, and its old hull intersection is
nonempty (it contains a cycle member). The unique arc
from any extra point in that component to an old mark
in the same component avoids the dividing point.
Hence the unique old attachment root of any added
component in this limb is also in the open precritical
limb, not at the dividing point. Its host angle belongs
to that limb's contour. Old accesses there remain in
the same contour. The nested model collapse and
monotone impression correspondence of
[ambient-angle exactness](../issue40_ambient_angle_exactness_20261124.md)
and [monotone model prime-end bridge](../issue40_monotone_model_prime_end_bridge_20261124.md)
then give the physical locality for saturated lifts and
the corresponding model-side blocks. One must still
verify that these are the chosen actual coarse marking
blocks of the repaired action. No assertion of equality
with the printed literal maximal-subset action is made
(the [canonical-localization uniqueness failure](../issue40_canonical_localization_uniqueness_failure_20261124.md)
separates these notions).

Assume α and δ each have exactly one physical critical
end, occurring at the initial end in cap orientation,
and the directed component uses the protected BL_k
block. Then its critical source end cannot lie in the
precritical limb. For otherwise its initial inner access
is in r^(-1)(BL_(q−1)), and the positively oriented base
travels from there to e in r^(-1)(BL_k), covering all
of r^(-1)(BL_0) in between. The boundary covering p
would map that base onto the entire circle by critical
saturation. But a lift of a simple proper disk-cap path
has its base mapped homeomorphically onto a proper base,
contradiction.

Every point mapping to the open critical filled limb
has exactly one of the two physical inverse origins:
the precritical limb, or Ω_1^sel inside the critical
limb, by the rotation and unique critical-limb inverse
branch. Thus the initial source end of the unique
directed component lies physically over Ω_1^sel.
The complete lift identification of §2 puts this
point on the closed parent trace. This is an actual
one-step selected critical-limb record. It may be the
original endpoint or a new interior contact.

The positive-end condition itself holds for a simple
inner Wave leaf with a physical critical endpoint,
crest over some positive nonprecritical BL_k, and
no full precritical-limb crest, provided the ideal
limb contours have their physical locality. Its
base cannot run from a noncritical endpoint to
a critical endpoint through BL_k without passing
all of the precritical block; nor can two critical
endpoints bound a base containing BL_k without
including that block. Exclude the finite dividing
accesses modulo zero as in the point-gate argument.
These are circle-order assertions about singleton
bases, not about an aggregate Wave.

Consequently, on a stationary chain satisfying these
hypotheses at every step, the critical end stays on
one fixed oriented side of the original parent
parameter windows. Each step's selected directional
witness can be used because its output is the same
unique δ; no choice of another output is being made.
By §1–2 all these witnesses lie on the common
canonical lift (for a complete lift at the final
horizon). In fact the last-coordinate projection of
that full relation lift supplies the complete
one-step lift of each stage path over its own window,
by uniqueness at an inner endpoint.

Under the total-critical-visit estimate of
STAGE_ENDPOINT_CENSUS.md §5, if e counts distinct
interior parameters born on this initial side then

\[
 h+1\le b(1+e),\qquad e\ge
 \max(0,\lceil(h+1)/b\rceil-1).
 \tag{4}
\]

Indeed each initial-side parameter at its birth
lands on T; the later critical stages assigned to
it are distinct forward visits of that carrier point
and are at most b before q. There is just one original
parameter on this side. At h=b<q, at least one
interior initial-side birth is forced; by the
one-step exclusion just proved such a birth is
an actual encounter with Ω_1^sel in the immediately
preceding physical output path. This is earlier
than the two-sided birth horizon 2b.

Importantly, (4) does not imply that the same late
birth point was in the selected inverse limb through
every earlier interior portion of the chain. Those
earlier path segments may visit other inverse sheets
before landing. Thus a full depth-b selected encounter
is NOT asserted. The theorem removes a last-step
precritical-origin ambiguity and an orientation ambiguity,
not the entire stationary pass-through problem.

## 6. Weaker free internal response; no outer collar

There is also a quantitative improvement that applies without
§4–5's corrected marking assumptions. Use the bounded-stay and
deep-prefix identities (2)–(3) of PREFIX_POTENTIAL_CHARGE.md.
Put

\[
 Z_T=T\setminus\Omega_0,\qquad
 S_T^{free}(F)=\inf_u\int_U|\nabla u|^2\,dA ,
 \tag{5}
\]

where u is smooth with values in [0,1], one near C_1 and
zero near Z_T. There is **no** condition at the ambient
outer boundary, and no zero condition on K minus T.
The electrodes are disjoint compacta, so the class is
nonempty and the infimum finite for each fixed block.

For a family A_deep of inner-ended parents meeting some
C_n, n≥b+1, at an interior time, charge the parents
incomplete at horizon b by (1). On the rest all canonical
prefix lifts are complete. For each parent half choose
j≤b at which the corresponding original carrier endpoint
has left the critical limb. Its physical image F^j(p)
lies in Z_T by forward invariance. At the deep encounter
the same prefix image lies in C_1. Thus u composed with
P_j varies by one on the actual complete prefix lift
of this half. The all-sheet pushed gradient metric
and exact degree energy calculation from the prefix
potential note apply without compact support: the area
identity is Tonelli on a countable inverse-chart partition,
and the potential variation occurs on actual compact
lifted subpaths. Combine the two halves and take the
infimum over u. The result is

\[
 \boxed{
 W(A_{\rm deep})\le
 2^b V+\frac{2^{b+1}-1}{4}S_T^{free}(F).
 }
 \tag{6}
\]

This replaces the previous grounded response on the
entire noncritical filled set by a free response on the
smaller noncritical portion of the actual carrier. The
price is an explicitly bounded vertical term, not a
global full-filled collar cost.

Under the stronger oriented one-step hypotheses of §5,
the complete parent already has a physical encounter
with C_1 on its closed trace, and its other endpoint is
in Z_T. A single ordinary gradient variation from one
to zero gives W≤S_T^free for all such complete parents;
charge incomplete one-step lifts by 2V. Thus

\[
 W(A_{\rm oriented\ step})\le 2V+S_T^{free}(F).
 \tag{7}
\]

No stationary depth-b collar is needed in this stronger
conditional branch. This is a weaker variational target:
a uniform estimate S_T^free(F)≤C_b(R(F)+V(F)+1)
would charge the corresponding edge-end families.
Neither that estimate nor the required protected-block
and corrected-marking realization for all native
stationary leaves follows from qualitative separation.
The earlier positive-width carrier-edge countermodels
remain relevant. All conformal analysis here is written
mathematics, not kernel formalization. The finite
orientation sum, one-sided visit budget and vertical/
potential accounting are isolated in
StationaryCanonicalLift.lean. No source-ledger status
or global MLC gate is changed.

Prepared with ChatGPT assistance; human specialist review pending.

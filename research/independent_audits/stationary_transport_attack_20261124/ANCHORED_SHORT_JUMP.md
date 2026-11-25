# Anchored short-crest growth and a localized long-jump theorem

Continuation of [ANCHORED_PHASE_FREE_RESPONSE](ANCHORED_PHASE_FREE_RESPONSE.md).
This supplies two further pieces of the phase-free route: (i) short
crest growth/saturation by bounded signed probes, without singleton
hypotheses; (ii) a long-iterate **localized lifting** bound which does
not pay the full covering degree for incomplete canonical lifts.
Under the actual proper middle-corridor chart, the cost of a long
jump depends on a logarithmic angular guard involving only six
terminal limbs, not on the length of the jump or arbitrary pulled
attachment angles.

Combining the results gives a conditional vertical-width estimate
in terms of two explicitly isolated quantities: the difference
between the global and near-critical anchored suprema, and the
terminal angular guard. Neither quantity is proved uniformly bounded
by the native hypotheses in this note. This is a new route toward
amplification, not a claim that the old ambient phase deficit has
been eliminated or that the source's full terminality theorem is
proved.

## 1. Width convention and common-interval propagation

Use C_* and M_*=sup W(C_*), the fixed-map comparison class and
its finite supremum from ANCHORED_PHASE_FREE_RESPONSE. In
particular a member is an actual Borel simple marked lamination
with a whole original crest atom shared by every leaf. It may
have additional common crest atoms and may consist entirely of
breakable paths. The cap M_* is available for every such actual
packet, regardless of its location or source controllability.
Keep all stated geometric, Borel, and filled-graph hypotheses of
that note. Let C=C_2, V=W(X), and R=W(RF).

Let A in C_* have width w and every leaf crest over a common
nonempty connected **open marked interval** I, consisting of
whole open atoms and their intervening cuts. Use the corrected
complete geometric interval action

    Phi(I)=p(r^(-1)(I)),

with r the actual contour collapse, p the actual degree-two
boundary covering. On a proper marked input the coarse interval
J=r^(-1)(I) is a connected union of whole fine atoms with the
stated old-proper first/last fine atoms. The open convention
does not silently include the fibers of excluded endpoint cuts.

First charge incomplete canonical one-step lifts by 2V and
all bad raw gaps over the first old-proper end fine probe by C.
The signed sum one produces a positive good primary gap for
each remaining parent. Select one by the Borel occurrence
enumeration. Its simple covering image shares the whole target
fine image atom in its strict crest, and the fixed chart is
injective on the actual selected source supports. Put
E_0=2V+C. The primary-good family G has width >=w-E_0, and
its actual image D belongs to C_* and has width >=W(G).
The original comparison allowance is

    d=M_*-w+E_0.

For any fixed n additional old-proper end-fine probes, which
are either entirely strict crest or entirely outside the
marked old base on the corresponding subfamilies, the
signed-probe rule of ANCHORED_PHASE_FREE_RESPONSE gives
total bad-probe/disagreement width

    <= n C + sqrt(n M_* d).                     (1)

In particular, every additional gap witnessing disagreement
has a literal time window different from the chosen primary.
Its simple image is in C_*. Its target support need not be
different from, or disjoint from, the primary support.
The proof uses series on the two windows and the actual
disjoint primary addition on G; no singleton identity is used.

### Proper-image propagation

Suppose Phi(I) is a proper interval. The boundary covering
is injective on the connected open J, whose normalized
angular span is <=1/2 (including the punctured-circle
borderline). Test also the last fine probe of J. After (1)
with n=1, the first and last probes are both in the selected
positive primary's base, and no raw endpoint is inside
their respective fine atoms. The source primary cap span is
<1/4 by fixed-anchor confinement. It cannot connect these
two probes by going around the complement of J, whose
length is >=1/2. It therefore contains all of J between
its whole end fine atoms. Its proper covering cap contains
all of Phi(I) in its strict crest, including all its
constituent atoms. If J consists of one fine atom the
conclusion is immediate. This proves an actual packet A'
with

    W(A') >= w-2V-2C-sqrt(M_*(M_*-w+E_0)),      (2)
    all leaves crest Phi(I).

The old atom count cannot decrease on a proper image:
each old atom contributes at least one fine atom, and
the covering is injective on the connected proper pull.
No expansion assertion is made after saturation.

### Saturation guard

Suppose instead Phi(I) is the whole circle and there is
one original atom O outside every old leaf's marked base.
Use the same first primary and test the last inside and
one outside probe over O. A good primary agreeing with
both tests would contain the two entire end fine atoms
of J, and would avoid the outside probe. The outside
probe lies in the complementary arc between the last
and first probes, so the base must take the route through
J rather than the complementary route. It would therefore
contain all J, whose covering image is the whole circle.
This contradicts the primary's proper injective cap chart.
Consequently every primary-good parent has a bad probe
or a disagreement at these two additional tests. By (1),

    w <= 2V+3C+sqrt(2 M_*(M_*-w+E_0)).          (3)

This is a saturation response against the anchored maximum.
In particular it does not assume that every large pulled
crest contains two old-proper deck-related accesses. It
works even if most of the pulled interval consists of
attached components. The outside probe is essential in
this argument: first/last probes alone do not rule out
the opposite route when the pulled interval is very long.

For q>=4, such an outside whole atom exists whenever
all old leaves are short and share a nonempty common
crest atom. A short leaf's actual marked base meets at
most two consecutive limbs: otherwise an entire
intermediate limb is strictly between its ending atoms.
If the common crest lies in one limb, the union of
possible short bases is in that limb and its two
neighbors; if the common crest meets two limbs, their
short bases are in those two. Choose a limb outside
this union and any one of its atoms for O. This is a
finite marked-order argument, not the false assertion
that a general short disconnected Wave has proper
aggregate base. It needs the actual common crest.
We work below in the high-q regime, so do not use
this guard for the q=2 borderline.

## 2. A localized long-lift bound independent of the covering degree

Let X have flat normalized cylinder height M_X>0 and
V=1/M_X. Let Y be an actual annulus with a degree-d
proper annular covering p:Y→X. Normalize its height
M_Y=M_X/d. Let i:Y→X be the actual immersion, not
assumed proper or globally injective. Use the Borel
maximal raw restriction atlas of
[the exit-transfer theorem](../maximal_exit_transfer_20261123/NOTE.md)
section 2, which does not require canonical full
parent completion. All metrics are 2-modulus metrics.

Suppose in the universal source strip there is an
open bottom interval J=(l,u), a=u-l<=1/d, on which
i has continuous proper old-boundary limits inducing
an orientation-preserving homeomorphism onto a proper
open old interval J_old. The covering on J is
injective; it is also injective on the open vertical
slab over J. Require the actual old cap bases of the
parents to lie inside J_old, and one fixed old common
marked crest I with its entire proper inverse interval
inside J. Suppose its boundary covering image is a
nonempty marked interval (a whole atom suffices).

Choose two distinct fixed bottom probes e,f in J:
the old image of e is in the strict actual crest of
every parent, and the old image of f is outside every
actual parent cap base. They need not be endpoints of
fine atoms; the good lift constructed below will
transport the whole parent, not merely an arbitrary
raw gap over a point. Put

    g=min(e-l,u-e,f-l,u-f)>0,
    Gamma=log(a/(2g))>=0.

**Localized long-lift theorem.** Modulo a Borel parent
discard of width at most

    L_jump = 200(1+Gamma)+4V,                    (4)

every parent admits a full lift contained in the open
slab over J. These lifts may be selected Borel with
one lift per parent; their actual p-images form one
disjoint Borel lamination with coefficient-one width
transfer on every surviving subfamily. The output
crests over the entire p-image of the proper inverse
of I. In particular it is in C_*. The cost does not
involve d except through the scale-invariant guard
ratio a/g.

### Local escape metric

For x in J define

    r(x)=max(g,min(x-l,u-x)).

It is positive and 1-Lipschitz, and r(x)<=a/2.
Use on the slab the densities

    rho_side=10/r(x)  for 0<y<=min(M_Y,r(x)),
    rho_vert=2/M_Y   for 0<y<M_Y,

zero elsewhere, with the ordinary support boundary
conventions. The first area is at most

    100 integral_l^u dx/r(x)
      =200(1+log(a/(2g))).

The second is 4a/M_Y<=4V because a<=1/d.
Use the square-sum of these densities, project from
the strip and push through the immersion by the
all-sheet square-sum rule. The total energy does not
increase.

Consider any actual maximal raw lift of a parent
whose strip lift meets the central low rectangle

    min(e,f)<=x<=max(e,f),
    0<y<=min(g/8,M_Y/4).

If in either direction it reaches a vertical side of
the slab (also allowing a limiting endpoint there),
its horizontal displacement from the test point
(x_0,y_0) is at least r_0=min(x_0-l,u-x_0)>=g.
Before doing so, take the first occurrence of
|x-x_0|=r_0/4 or y=r_0/4. If this is horizontal,
the Euclidean length from the test point is >=r_0/4.
If vertical, it is >=r_0/8 since y_0<=g/8<=r_0/8.
Until the first such occurrence we have
3r_0/4<=r(x)<=5r_0/4 and y<=r_0/4.
Thus the whole segment lies in the side metric band
and has rho_side-length at least
(10/(5r_0/4))*(r_0/8)=1.
This argument applies in either parameter direction
and does not assume monotone horizontal coordinates.

If a lift escapes to the outer end without leaving
the slab, its vertical variation from y_0<=M_Y/4
to M_Y gives rho_vert-length at least 3/2.
This includes escape before reaching the side
metric's height threshold when the annulus is thin.
Every parent with any such bad raw lift therefore
has length at least one in the pushed density,
by the literal immersion path-lift identity.
This single metric charges all competing sheets
and both parameter directions at once. It yields
(4), not one factor d per potential preimage.

Remove the zero-width exceptional parents for which
some actual raw lift has infinite cylinder length:
push the constant one density on the finite-area
source cylinder through the immersion and use
vanishing multiples of its finite-energy norm, as
in EXCEPTIONAL_WIDTH_REDUCTION. Nonrectifiable
parents may also be removed by positive constant
densities in the finite-area target. Every remaining
raw lift has a single ideal limit at each maximal
endpoint by finite cylinder length; a compact
interior endpoint would extend in a local inverse
chart or contradict parent properness. The countable
Borel raw occurrence atlas makes the badness tests
Borel: lift coordinates seeded in the central
rectangle and their extremal side/top values and
endpoint limits are tested by compact exhaustion
and rational-time evaluations. Thus the discard
can be used in the actual width measure on
disjoint parent supports.

### Existence of a good full lift

For a remaining parent alpha, take a sufficiently
small positive height y<=min(g/8,M_Y/4). The i-images
of (e,y) and (f,y) lie on opposite sides of the old
crosscut alpha, by their actual proper ideal limits
in the strict crest and outside the cap base.
The horizontal path between them in the central
rectangle maps into X and must meet alpha. At that
point choose the actual maximal raw lift by local
inverse continuation. It meets the rectangle and
is not bad, so it stays inside the slab in both
directions, with neither outer nor side limit.
Its two ideal limits must be on the inner interval
J. There i has proper old-boundary limits. If a
maximal lift endpoint time were an interior parent
time, its i-limit would be an old inner ideal
point, whereas the parent has an interior value
at that time. This is impossible. Both endpoints
are therefore at the original parent endpoint
times, and the lift is of the entire parent.
The limiting source ideal endpoints are distinct
by the old-boundary homeomorphism and the parent's
distinct ideal ends.

Choose the first qualifying full lift in the
Borel raw atlas. There is no need for measurable
selection of the height or the crossing point.
The selected full lifts for different parents have
disjoint interiors by the immersion projection.
The covering is injective on the whole slab, so
their simple actual p-images are disjoint, with
Borel paths and supports. Because the source
strip cap arc and the old cap arc both lie in
the specified proper intervals, the homeomorphic
old-limit order identifies their endpoint order
and the whole crest I between them. Its proper
p-image is the output crest interval. Finally,
pulling an admissible output density back on the
injective slab and pushing it through i gives
coefficient-one energy and parent length transport
for every subfamily. QED.

No global completeness of I_h-lifts at degree d
has been used. In the native case d=2^r the old
full-completion bound would cost 2^r V.
The guard ratio is the exact remaining analytic
quantity in this local lifting theorem. Small
angular padding cannot be discarded as a point
exception, and the theorem does not assert a
uniform bound on it.

## 3. A proper-middle full-tower chart from the covering squares

For application require the actual one-step proper
middle corridor of KKL Proposition 6.7 in the corrected
geometric action: on a band of whole noncritical
limbs in BL_[b,q-b-2] the pulled contour has no
inserted material, the old-boundary identification is
a homeomorphism including its internal cuts, and the
covering maps it homeomorphically onto the band
translated by one. This is a source-specific geometric
input, not inferred from mere labels or from the
literal A.3.2 quantifier. The exact old-carrier
equality and actual proper access realization are
still to be verified on the native saturated
carrier if they are not taken as hypotheses.

Here is a finite-tower consequence. Suppose an
open marked band J_0, its translates J_1,...,J_r,
and the actual one-step old-proper source intervals
E_0,...,E_(r-1) have these properties: on E_j the
immersion has proper homeomorphic old limit onto
J_j and the one-step covering maps E_j homeomorphically
onto J_(j+1). Then there is a single interval on the
full r-th source ideal circle on which the full I_r
has proper homeomorphic old limit onto J_0 and P_r
is a homeomorphism onto J_r.

The proof is the same real-strip covering-square
argument as SUFFIX_ANCHOR_RESPONSE Lemma 1, now
applied to entire open intervals. Set B_r=J_r.
Working backwards, suppose B_(j+1) is the selected
interval on the (r-j-1)-th suffix, with I_(r-j-1)
old limit homeomorphic onto J_(j+1). Write
J_s for the immersion-factor projection U^s→U^1
in that lemma, s=r-j (this projection is not one
of the boundary bands J_j). The commuting square is

    P_1 J_s = I_(s-1) f_(s-1).

On the two inverse intervals of B_(j+1) under
f_(s-1), the right-hand side has a continuous
homeomorphic old limit into J_(j+1).
The proper degree-two P_1 covering lifts those
limits to the two respective inverse intervals
of J_(j+1); the two are distinguished because
J_s and I_(s-1) have degree one on the essential
loop, so on the real strips a half-turn in the
source changes their lifted relation by exactly
one covering sheet. Hence one inverse interval
has J_s limit homeomorphic onto E_j. Compose
with I_1 to get the I_s limit homeomorphic onto
J_j, and use the actual covering composition
for its P_s image. Induct back to j=0.
This proof uses the actual tower squares and
proper end limits, not an equality between
sequential and one-shot filtered restrictions.
On this interval the full P_r is injective, and
its normalized length is the final angular band
length divided by d=2^r.

The local long-lift theorem therefore transports
a whole parent cap contained in J_0 whenever its
common inside and outside probes have the
guarded positions in this single full chart.
The resulting image contains the entire
successively translated common interval Phi^r(I).
It does not require intermediate stage
singleton paths, or any completion cost
proportional to 2^r.

## 4. Only six terminal limbs enter the angular guard

Now take q>=2b+20, in the source high-type regime.
Suppose the actual input consists of short leaves
sharing a positive short marked interval I that
meets one or two consecutive noncritical limbs,
with first limb k in the linear order 1,...,q-1.
If k>=b+2 and k<k_*=q-b-5, take

    r=k_*-k,
    J_0=BL_[k-2,k+3].

The entire marked base of every short parent is
inside J_0: if the common I lies in BL_k, their
bases meet at most one of its neighbors; if I
meets BL_k,BL_(k+1), their bases lie in those two.
Choose a fixed interior old probe in a crest
atom of I and a fixed outside probe in BL_(k+2).
Both are inside the internal portion BL_[k,k+2].
No leaf of this short class has its base in
BL_(k+2).

For each one-step input time j<r the whole
band BL_[k-2+j,k+3+j] lies in the proper
middle corridor BL_[b,q-b-2]. Indeed its
lowest index is >=b and its highest before
the final step is <=q-b-3. The actual chart
of section 3 is therefore available under
that proper-middle hypothesis. The final
band is always

    B_T=BL_[q-b-7,q-b-2].

This has six consecutive near-precritical
limbs, regardless of k and r. Write |B| for
normalized **angular length in the original
target cylinder X**, not combinatorial length.
Put

    A_T=|B_T|,
    L_T=|BL_[q-b-7,q-b-6]|,
    R_T=|BL_(q-b-2)|,
    G_T(F)=log(A_T/(2 min(L_T,R_T))).

The positive lengths L_T,R_T are the left
two and right one whole terminal padding
limbs. In the full proper inverse chart
of degree d=2^r the whole angular interval
has length a=A_T/d. Both probes lie above
the internal three translated limbs, so
their distance to either end is at least
min(L_T,R_T)/d. Thus Gamma<=G_T(F), with no
estimate on angular sizes of individual
interior fine atoms. In particular the
uniform-in-r jump bound is

    W(A') >= W(A)-200(1+G_T(F))-4V,             (5)
    all leaves crest Phi^r(I).

The same final six-limb angular quantity
works for every jump from the middle.
This is a replacement for the part of
the fast-forward that transports a short
common-crest packet through a fully proper
band. It does not establish the parabolic
terminal fan outside that band, nor claim
that G_T(F) is O_b(1) or O_b(R+V+1).
The guard is measured on the original
terminal target circle, so a qualitative
properness theorem alone is not a bound
on its ratio. This guard is a precise
new remaining native estimate.

## 5. Bounded critical visits on the exact geometric action

Use the nested-contour and ambient-angle exactness theorem
of [the corrected interval-action note](../issue40_ambient_angle_exactness_20261124.md)
section 3, with its stated actual model/physical and corrected
geometric marking hypotheses. In particular every positive
open marked interval eventually saturates under Phi, so
a proper interval cannot repeat on its deterministic orbit.
Retain its exact marked interval and positive fine-atom
typing. This is not asserted for the literal unrestricted
maximal-subset action.

A common short interval contains no complete limb, so it
meets at most two consecutive limbs. Its number of atoms
is <=L=12b. The number of connected cyclic intervals of
fixed length ell that meet BL_0 in a whole atom is at most
6b+ell-1: there are at most 6b starts inside the critical
block and at most ell-1 starts immediately before it.
For a proper short orbit, length never decreases, and no
state repeats. Therefore the total number of critical
visits before the interval becomes saturated or contains
a whole limb is bounded by

    D_b = L(6b+L-1).

No use of a Perron spectral gap is needed on this
corrected contour action.

For a noncritical interval, the geometric pulled block
covers the translated proper interval injectively, and
a proper subinterval of a limb maps to a proper
subinterval of its next limb (a missing open old atom
has a nonempty disjoint fine pull). Thus a common short
interval that avoids BL_0 stays short as it translates
one step; its first noncritical limb advances by one
until it reaches the critical block. If the common
interval contains a complete limb after a critical
step, its output also contains a genuine near-critical
atom: a selected old-proper probe on an old critical
atom has its whole target atom in BL_(-b)..BL_b
by CRITICAL_PHASE_LOCALIZATION section 1, and that
atom lies in Phi(I). If the output remains short the
same near-critical atom certifies its anchor.

Fix c=b+8 and the bank B_c=BL_(-c)..BL_c. The
anchored nonshort estimate generalizes to inputs with
an anchor in this bank by replacing its K with

    K_c=6b(2c+h+1)+1,

and keeping its other proof unchanged: during the
bounded H=h+2 raw primary sequence the anchor moves
one noncritical limb at a time, or resets inside
BL_(-b)..BL_b at a critical old-proper step.
The expanded bank BL_(-c)..BL_(c+h) therefore
supplies the away endpoint module count. No
localization of remote auxiliary output packets
is required because M_* caps all C_*.

Starting from a common short interval with a
near-critical atom in B_c, use the following
macro-stage schedule:
* if the common interval meets BL_0, use the
  one-step signed-probe propagation or saturation
  guard of section 1;
* otherwise, if its first noncritical limb k
  satisfies b+2<=k<q-b-5, perform the single
  proper middle jump of section 4;
* otherwise take one ordinary step.

Before a long jump or a saturation test remove
the nonshort subfamily; we can conservatively
remove it before every macro-stage. The
remaining short leaves satisfy the required
actual base and outside-probe conditions.
The common interval is preserved on subfamilies.
A jump lands with first limb q-b-5, near the
precritical bank. Between critical visits at
most b+1 ordinary forward steps are needed to
reach the jump range, at most one jump, and
at most b+5 forward steps after that to reach
BL_0. A critical step contributes one more.
Thus

    L_macro=(D_b+2)(2b+10)

is a safe bound on macro-stages through the
first saturation or full-limb crest. Every
actual packet at a macro-stage start has a
near-critical atom: on ordinary stages its
short interval translates within B_c (until
the next jump); at a jump's end it lies near
q-b-5; at a critical step the old-proper
critical probe has its actual image in the
near bank as above. The intermediate conceptual
short intervals in a long jump need not be
realized by actual Wave sequences. The proper
full-tower chart realizes the final interval
directly. The length/nonreturn count is on
the exact deterministic geometric orbit, not
on invented intermediate physical path choices.

## 6. A conditional vertical-width reduction with two explicit gaps

Let M_near be the supremum over the same class C_*
restricted to packets with a common atom in B_c.
Use zero if this subclass is empty. Define the exact
nonnegative supremum gap

    D_remote(F)=M_*(F)-M_near(F).

This records a different remaining issue from phase
selection: an unrelated-crest Wave never needs to be
assembled, but the global anchored maximum need not
be approximately attained near the critical bank.
We do not assume D_remote is small.

We prove a finite quantitative implication for the
new comparison class:

    M_* <= C_b' (R+V+1+G_T(F)+D_remote(F)).      (6)

Here C_b' is finite and depends only on b.
The estimate is conditional on all the exact
geometric inputs stated above (including the
proper middle chart, ambient-angle exactness,
and the previous anchored nonshort geometry).
It is not a uniform native theorem without
bounds on G_T and D_remote. Its utility is
to separate those two tasks from arbitrary
phase-deficit and small-breaking assembly.

For precision we give an explicit finite
scale argument. Use the generalized constants
of ANCHORED_PHASE_FREE_RESPONSE with
K_c=6b(2c+h+1)+1,
J_c=max(12K_c,N,2), h=b+2, H=h+2,
N=h+12b*2^h, C=C_2:

    E=1+2^H V+H C,
    E_a=sum_(r=1)^h C_(2^r)+12b*2^h*C_(2^h),
    B=E+8K_c+(48K_c+12+2h)C+E_a+4R,
    A_step=2V+3C,
    A_jump=200(1+G_T(F))+4V,
    A_abs=max(E,B,A_step,A_jump,2D_remote(F),1),
    a_0=max(2,(h+11)*sqrt(J_c)).

If M_*=0 the conclusion is immediate. Otherwise
normalize the current packet's deficit by

    u=(M_*-w)/M_*>=0, eta=A_abs/M_*.

All comparisons in the anchored nonshort proof
are against the fixed M_*, so its equation (7)
gives the general bound

    W(nonshort)/M_* <= eta+a_0 sqrt(u+eta)

for a packet with near-critical anchor.
No relative cap parameter needs to be fixed
in advance. Discarding its nonshort part
increases the normalized deficit by at most
that amount, unless it was the entire packet.
Equation (2) increases the deficit by at most
eta+sqrt(u+eta) at an ordinary proper-image
step. The long jump (5) increases it by at
most eta. Thus each elementary filtering
or movement operation satisfies the single
envelope

    u_next <= u+eta+a_0 sqrt(u+eta).             (7)

If a packet has a common whole-limb crest,
it is entirely nonshort; its normalized
width is 1-u and the anchored estimate
bounds it by eta+a_0 sqrt(u+eta).
At a saturation step after short filtering,
(3) instead bounds 1-u by
eta+sqrt(2(u+eta)).
Both are impossible if u,eta are sufficiently
small. Also short filtering cannot delete
the entire packet under those bounds.

Set p=2 L_macro+4, t_p=1/(64(a_0+1)^2), and
recursively for j=p-1,...,0 put

    t_j=t_(j+1)^2/(64(a_0+1)^2).

These positive constants depend only on b.
If u,eta<=t_j, then
u+eta<=2t_j<=t_(j+1)/2 and
a_0 sqrt(u+eta)<=t_(j+1)/4, by squaring
the last positive bound. Equation (7)
gives u_next<=t_(j+1).
At every stage u,eta<=t_p,
eta+a_0 sqrt(u+eta)<1/2,
eta+sqrt(2(u+eta))<1/2, whereas
1-u>1/2. The terminal contradictions
are therefore strict. These extremely
small constants are conservative,
not optimized.

If M_*>A_abs/t_0, then eta<t_0 and
D_remote/M_*<t_0/2. By the definition
of M_near choose an actual near-bank
anchored packet of width
w>M_near-t_0 M_*/2. Its initial
deficit is <t_0. Pick its common atom
as I. The finite schedule of section 5
(with at most two elementary operations
per macro-stage) constructs the
successive actual anchored packets,
until saturation or a whole-limb
crest. At both stops the displayed
strict bounds contradict its
near-maximal width. Thus

    M_* <= A_abs/t_0,

which gives (6) with a b-dependent
constant, since all absolute terms
are O_b(R+V+1+G_T+D_remote).

For an initial wide actual input with
a k-localized plus leafwise-over-critical
decomposition, the extraction estimate
of ANCHORED_PHASE_FREE_RESPONSE gives

    W(input) <= (2k+1) M_*+1/2.

Consequently if, in addition, the two native quantities
satisfy G_T+D_remote=O_b(R+V+1), we would obtain
W(input)=O_(b,k)(R+V+1), hence the vertical-width
alternative V>=c_(b,k) W(input) above a sufficiently
large absolute scale relative to R+1. For the
source's fixed initial control and HTND scale
this is the relevant amplification direction.
This does not yet license the full native
trichotomy or downstream MLC step.

## 7. Scope and new targets

The finite old interval count, short saturation
guard, and bounded deficit iteration no longer
require singleton outputs, an ambient multi-packet
replacement, or an independent small-breaking
proposition. The localized long jump replaces
the exponential canonical completion charge by
an explicit source-local escape metric. The
actual remaining analytic tasks for this route
are now:

1. establish the exact native geometric contour,
   proper middle chart, saturated critical
   hull and host-side inputs already isolated;
2. control the terminal six-limb angular
   ratio G_T, or obtain a native width
   response when it is large;
3. show global near-maximal anchored width
   can be approximated in the near-critical
   bank, or bound D_remote / produce a
   vertical response when it is large;
4. justify the source initial witness and
   downstream amplification use for this
   changed comparison class.

A near-maximal packet with a remote crest can
have nonshort leaves with endpoints in many
remote limbs; the short-band local jump does
not silently apply to that packet. Neither a
count of limbs nor the finite anchored
supremum alone bounds D_remote. The attachment
screening counterexample is a warning against
declaring an angular guard uniformly controlled
from qualitative properness; the guard here
is on the actual original terminal cylinder,
not an assumed unchanged old pulled side.

The companion regression checks the cyclic
short guard, visit census, exact jump scheduler,
and backward deficit scale. The localized
escape density, old-proper full chart and
geometric comparison are written proofs,
not established by finite tests. No ledger
promotion, unconditional stationary theorem,
or MLC claim. AI-assisted mathematics;
independent specialist review pending.

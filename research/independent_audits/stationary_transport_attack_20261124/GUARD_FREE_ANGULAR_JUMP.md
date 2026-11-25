# Guard-free short-crest angular replacement and a one-sided remote certificate

Continuation of [ANCHORED_SHORT_JUMP](ANCHORED_SHORT_JUMP.md) and
[ANGULAR_ANCHORED_ENVELOPE](ANGULAR_ANCHORED_ENVELOPE.md).

**Main advance.** The six-terminal-limb angular guard G_T is
not required in the anchored short-crest program. Instead
of lifting every path through a guarded slab, replace the
packet by an explicit semicircle lamination over the whole
translated crest. A one-sided radial width bound, a positive
boundary-derivative distortion estimate, and a choice of
destination padding limb give a loss bounded by O(V+1),
independent of degree, jump length, and all angular ratios.

This is a replacement of actual families for the anchored
comparison, not a leafwise restriction or an assertion
that the earlier guard-dependent full-lift theorem is
guard-free. It leaves the remote anchored-supremum problem
and the exact native geometric hypotheses open. A final
section makes that remote problem more explicit by locating
a possible remaining angular obstruction in a fixed-width
band of reflected remote limbs.

## 1. One-sided angular width envelope

Use the normalized cylinder of circumference one and
height M_X>0. Let I be a proper connected marked crest
interval of length ell, and write e for its midpoint in
a selected lift. A Borel lamination A of simple proper
distinct-inner-ended paths has I in every strict crest.
Suppose that, on one fixed side of e, every actual cap
endpoint is at distance at most L from e in that lift.
There is no restriction on how far the other endpoint
lies from e (besides proper simple cap typing). Necessarily
L>=ell/2 for a nonempty packet.

Then

    W(A) <= 3pi/log(2) + log_+(4L/ell)/pi.       (1)

Indeed the radial test (A) of SECTOR_PHASE_ASSEMBLY
at scale L bounds the family reaching radius L by
2pi/log(2): the endpoint on the designated side has
radius <=L, and the other endpoint is on the opposite
side of e. The half-annulus metric on [ell/4,ell/2]
bounds the family entering radius ell/4 by pi/log(2),
since both endpoints have radius >=ell/2. All other
paths lie in the half-annulus ell/4<|z-e|<L.
The density 1/(pi |z-e|) has length at least one on
them by their full argument variation pi, and area
at most log_+(4L/ell)/pi. The strip-to-cylinder
square-sum metric gives the same bounds on X, without
global injectivity or a condition on L relative to
the cylinder height. Nonrectifiable exceptions are
handled as in the earlier radial tests. This proves (1).

In particular the bound does not require the actual
traces or their whole cap bases to be contained in
one proper middle band. Constraining one end of every
oriented cap suffices.

Recall the explicit radial lower witness over a
proper marked crest interval of length ell:

    m(ell)=log_+(2s/ell)/pi,
    s=min(1/4,M_X/2).

It has exactly that width if ell<2s, and otherwise
we use the empty family and width zero. For the
nonempty witness the mark admissibility and disjoint
Borel supports are as in ANGULAR_ANCHORED_ENVELOPE.
For this note the common interval may have more than
one atom; it remains a member of the anchored class
C_* whenever it is nonempty.

## 2. Positive boundary derivative on a proper strip interval

Let the actual annular covering have degree d>=1.
Use its source universal strip of height h_s=M_X/d
and target strip of height M_X. Let F be the holomorphic
lift of the annular immersion between those strips,
with its real bottom boundary limit on a proper
open interval J=(l,u) of length a=u-l<=1/d.
On J assume the old-boundary limit is a continuous
orientation-preserving homeomorphism onto a proper
old interval. This is precisely the old-proper
full-chart hypothesis in ANCHORED_SHORT_JUMP,
not an assertion that the immersion is proper at
its outer end.

Reflection across the real bottom segment gives
analyticity near every interior point of J. The
boundary derivative F'(x) is real and strictly
positive: the imaginary part is a positive harmonic
function on the strip, zero on this segment, and
the boundary normal derivative is positive by the
Hopf lemma. Equivalently this follows from the
positive harmonic representation used next.

Put V=1/M_X. For x,y in J one has

    F'(x)/F'(y) <= exp(3pi V) *
        max(1, (y-l)/(x-l), (u-y)/(u-x))^2.     (2)

Here the derivative concerns the **old ideal
coordinate** induced by the immersion, not a
derivative of the monotone attachment collapse.

Proof. The map z -> exp(pi z/h_s) sends the entire
source strip conformally to the upper half-plane.
The composite

    H(t) = F((h_s/pi) Log t)

with the branch 0<arg(t)<pi is a holomorphic
upper-half-plane self-map (its image in fact lies
in the target strip). Its real analytic boundary
interval is (L,U)=(exp(pi l/h_s),exp(pi u/h_s)).
Use the classical positive harmonic representation
of Im H, or equivalently the Herglotz representation

    H(z)=alpha+beta z+
          integral (1/(t-z)-t/(1+t^2)) dmu(t),

where alpha is real, beta>=0, mu is a positive
measure with integral (1+t^2)^(-1)dmu finite.
The normalization of mu absorbs the usual pi
factor. The measure has no mass in (L,U):
Im H extends there continuously as zero, and the
positive harmonic boundary measure is recovered
by weak convergence of its Poisson kernels on
compact subintervals (equivalently use analytic
reflection and the Stieltjes inversion formula).
Differentiation on compact subintervals is
justified by separation from the support and
the integrability at infinity. Thus

    H'(s)=beta+integral (t-s)^(-2) dmu(t)
    (L<s<U).

For X,Y in (L,U), each summand of H'(X)
is at most

    max(1,(Y-L)/(X-L),(U-Y)/(U-X))^2

times the corresponding summand of H'(Y).
For t<=L or t>=U the distance ratio is largest
at the indicated endpoint or its limit at
infinity. The beta term satisfies the same
bound. Integration gives that bound for H'.
Positivity follows also from nonconstancy.

Now X=exp(pi x/h_s), Y=exp(pi y/h_s).
By the real mean value theorem on [l,u],
each of the two ratios of exponential differences
is at most exp(pi a/h_s) times the respective
ratio of real differences. The chain factor
X/Y is at most exp(pi a/h_s). Hence the total
factor is exp(3pi a/h_s)<=exp(3pi V), since
a<=1/d. This proves (2). In particular its
constant does not grow with d. QED.

No global univalence of F or H is assumed.
The use of an upper-half-plane self-map, rather
than an arbitrary real-analytic boundary
reparameterization, is essential.

## 3. Forward one-sided replacement

In the above proper chart let J_B be a connected
subinterval of J, with endpoints strictly inside J.
The source common crest I_s=(v,w) lies within J_B;
write ell_s=w-v and x_0=(v+w)/2. Its old image
I_old=F(I_s) is a proper marked interval of length
ell_old, and its covering image I_new=p(I_s) is a
proper marked interval of length ell_new=d ell_s.
Require these actual whole-interval markings,
as supplied by the exact proper-middle chart;
the replacement is not asserted for an unmarked
subarc of an original atom.

Choose one side of J_B, e.g. the left boundary z,
and put g=x_0-z, p_0=z-l>0. The right-hand
version uses g=z-x_0 and p_0=u-z. Suppose every
actual old cap of A crested over I_old has its
endpoint on that side between F(z) and the
corresponding end of I_old. The other endpoint
may be anywhere permitted by its actual cap
class. All these intervals and distances are
taken in the compatible oriented real lifts.

The following bound holds:

    W(A) <= m(ell_new) + C_J(V+1)
                        + (2/pi) log(1+g/p_0), (3)

where C_J=32 is a safe absolute constant. In
particular if g<=4p_0, a new actual radial packet
A' over the entire I_new satisfies

    W(A') >= W(A)-40(V+1).                      (4)

Proof. Write D=exp(3pi V). On the central half
of I_s, the inverse of (2) bounds F'(x)
below by F'(x_0)/(4D): the distances of x
from the endpoints of J are at most 3/2 of
the corresponding distances for x_0, since
x_0 is the midpoint and x stays in the
central half. Integration gives

    ell_old >= ell_s F'(x_0)/(8D).

Along the segment between z and x_0, the ratio
in (2) relative to x_0 is bounded by 1+g/p_0.
The opposite boundary ratio is at most one.
Consequently

    |F(z)-F(x_0)| <= g D (1+g/p_0)^2 F'(x_0).

The old midpoint e of I_old differs from
F(x_0) by at most ell_old. Thus the old cap
endpoint on that side is at distance at most
L=|F(z)-F(x_0)|+ell_old from e and

    L/ell_old <= 1+8D^2 (1+g/p_0)^2 g/ell_s
               <= 9D^2(1+g/p_0)^2/ell_new.

The last inequality uses g<=a<=1/d and
0<ell_new<=1. Apply (1), and use

    log(1/ell_new)
      <= log_+(2s/ell_new)+log(1/(2s)),
    log(1/(2s))=log(max(2,V))<=log(2)+V.

The absolute error is at most

    (6+1/pi)V + 3pi/log(2)+log(72)/pi,

which is smaller than 32(V+1).
The extra term is precisely the displayed
(2/pi) log(1+g/p_0). If g<=4p_0 it is
at most (2/pi)log 5<2; 40(V+1) suffices.
The new radial packet in (4) is the
explicit lower witness over I_new.
This proves (3)-(4). QED.

This is not a coefficient-one map between
the old and new leaf sets. The old width
bound and the new actual radial lower
witness supply a comparison between two
different families. That is sufficient
for the anchored maximality/deficit
iteration, which needs only a new packet
and its common whole crest, not original
parent provenance across macro-stages.
Every subsequent bounded raw-primary
argument can start afresh on that packet.

## 4. Choose a destination with one adequate padding limb

Retain the exact actual proper middle-corridor
and full-tower chart hypotheses of
ANCHORED_SHORT_JUMP section 3. In the high-type
case take q>=2b+28. Let the old common short
marked interval I meet one or two consecutive
limbs, with first limb k in the noncritical
linear order. Assume the packet has only
short leaves. As before every actual cap
base lies in the four-limb band BL_[k-1,k+2].
Use the old-proper six-limb chart band
BL_[k-2,k+3], with one padding limb on each
side. The old common interval lies inside
the inner four-limb band; this bound allows
the two-limb crest case as well.

Select the destination k_* once for F, using
**actual target conformal angular limb lengths**.
Consider the ten consecutive limbs

    [q-b-12,q-b-3].

Choose an index t of a largest angular length
in this list (ties arbitrary). If t is in the
first five positions, choose k_*=t+2;
otherwise choose k_*=t-3. In the first case
the left padding limb of the terminal
six-limb band [k_*-2,k_*+3] is t; in the
second the right padding limb is t.
The whole six-limb band is contained in
the ten-limb list, and the chosen padding
limb has angular length at least that of
each of the four inner limbs. Also

    q-b-10 <= k_* <= q-b-6.

For any middle start b+2<=k<k_*, take
r=k_*-k. At all input steps j<r,
the translated six-limb band is in
BL_[b,q-b-2]: its initial lowest index
is >=b, its last highest input index
is k_*+2<=q-b-4. Its full-tower old-
proper chart exists by the actual
commuting-square argument of the earlier
long-jump theorem. The full covering
degree is d=2^r. On that chart all
target angular lengths are scaled by
the same factor d, so the distinguished
padding margin p_0 in the source strip
is at least one quarter the length of
the inner four-limb band. The distance
g from the midpoint of the source crest
interval to that side of the inner band
is at most that full four-limb length.
Hence g<=4p_0 exactly, regardless of
the absolute angular sizes and d.

The old endpoint hypothesis of section 3
holds for the chosen side because all
short cap bases lie inside the old
four-limb band. Apply (4) to obtain an
actual radial packet over the whole
translated common marked crest Phi^r(I)
with

    W(A') >= W(A)-40(V+1).                      (5)

If its lower witness is empty, (5) says
the old width was already <=40(V+1).
No need to guarantee a full lift of
individual old paths, and no guard
ratio appears. The use of a largest
limb is only a finite choice of jump
destination, not a claim of uniform
angular comparability of nearby limbs.
The translated interval must be the
actual proper marked image as in the
full-chart hypothesis, not a formal
limb substitution.

## 5. Remove the terminal guard from the anchored maximum estimate

Use the exact geometric interval nonreturn
and positive-atom typing of ANCHORED_SHORT_JUMP,
with all its stated native hypotheses, and
the nonshort charge of ANCHORED_PHASE_FREE_RESPONSE.
Take the slightly enlarged fixed bank
B_c=BL_(-c)..BL_c with c=b+12, and define
M_near and D_remote=M_*-M_near relative
to that bank. This is the same definition
as before but for this specified enlargement;
the near supremum can only increase.
Use the corrected full-tower charts, critical
deck pair, selected deep contact and separator
inputs of those notes unchanged.

Replace the former fixed destination q-b-5
by the k_* of section 4. A short interval
with first limb k in the middle jump range
b+2<=k<k_* is replaced by (5); otherwise
take the ordinary proper-image step or
saturation guard of ANCHORED_SHORT_JUMP.
The number of critical visits before the
first saturated interval or full-limb crest
is still bounded by

    D_b=12b(18b-1),

by exact interval nonreturn and nondecreasing
proper atom count. Between visits there are
at most b+1 ordinary steps before a jump
and at most b+10 after one (one extra step
for the critical transition). A safe
bound on macro-stages is
(D_b+2)(2b+16). Every actual macro-stage
starting interval has a near-bank atom:
ordinary stages outside the jump range
are in the bank, the adaptive destination
lies in its negative side, and the exact
old-proper critical anchor image is in
the original parabolic bank B_*.
The conceptual long-iterate intermediate
intervals need not be represented by
actual path families.

At every stage discard the nonshort
subfamily using the anchored comparison
with K_c=6b(2c+h+1)+1, h=b+2, as before.
After short filtering the ordinary
propagation/saturation hypotheses or the
replacement hypothesis (5) hold.
The new family in a long jump is an
actual C_* packet, not a WAD scalar.
It has the entire translated common
interval in its strict crest. All later
series estimates compare against the
unchanged M_* but need no path identity
with the earlier macro-stage.

In the finite normalized-deficit iteration
of ANCHORED_SHORT_JUMP section 6 substitute

    A_jump=40(V+1),

and the above c and macro-stage bound.
Every other absolute or square-root
allowance is unchanged with K_c,J_c.
The same backward tolerances (with the
new finite number of stages) give

    M_* <= C_b'' (R+V+1+D_remote).              (6)

Here the constant depends only on b.
For completeness the normalized jump
deficit increases by at most
A_jump/M_*, so satisfies the former
u_next<=u+eta+a_0 sqrt(u+eta) envelope.
The final whole-limb and saturation
contradictions therefore follow by
the same strict tolerance argument.
The initial near-bank approximation
spends D_remote as before. There is
no G_T term in (6).

This proves the conditional estimate
for q>=2b+28. For the bounded smaller-q
range one can retain the ordinary
bounded-horizon program instead of
asserting a nonexistent proper middle
band (the deep-contact hypotheses and
small-q handling must still be checked
as in the earlier notes). No small-q
application is needed for the high-type
amplification route here.

## 6. A concrete remaining remote obstruction

The previous ANGULAR_ANCHORED_ENVELOPE
gives, for a globally smallest actual
atom A_* outside B_c, an explicit radial
packet A in the proper middle corridor,
with common atom A_* and width

    W(A) >= M_* - C_env - B_c^err
                      - a_c sqrt(M_*(C_env+E)),

after removing the nonshort paths whose
actual bases touch the smaller bank
B_(c-1). Use c=b+12 as in section 5.
All retained radial caps lie between
the old noncritical bank boundaries.
Let k be the limb index of A_*; thus
c<k<q-c. Choose the fixed adaptive
destination k_* as above; k<k_*.
Set r=k_*-k>0.

For the left-side comparison take the
actual old-proper full chart over

    J_old=BL_[b,k+3],

and its inner band J_B,old=BL_[c,k+2].
These bands translate properly through
r by the same chart argument: the
lowest old index is b, and the last
highest input index is k_*+2<=q-b-4.
The common atom lies in the inner
band. Every retained original cap has
its left endpoint in J_B,old between
the first dividing cut of BL_c and
the common atom, by its avoidance of
B_(c-1). The right endpoint need NOT
lie in J_B,old or J_old. This is why
the one-sided estimate (3), rather
than the earlier full-lift theorem,
is useful in this remote case.

Let p_T^rem be the actual angular length
of the target padding band

    BL_[b+r,c-1+r].

Let g_T^rem be the actual angular
distance in the translated chart from
its inner left cut (beginning of
BL_(c+r)) to the midpoint of the
translated common interval I_new.
It is positive and <=1. The actual
source chart ratio is g/p_0=
g_T^rem/p_T^rem, since the covering
is linear of degree d on the strip.
The destination atom/image interval
I_new lies in BL_(k_*), hence in B_c.

Apply (3) and the explicit radial
witness in the near bank to conclude

    D_remote <= C_env+B_c^err
       + a_c sqrt(M_*(C_env+E))
       +32(V+1) + G_rem,                       (7)

where

    G_rem=(2/pi) log(1+g_T^rem/p_T^rem).

This removes the need for a common
full-lift band containing every
remote cap, and isolates the remaining
failure in the single left-side
angular distortion ratio. If the
padding is comparable to g_T^rem,
the remote gap is only the earlier
absolute plus square-root bank-contact
loss, and (6) closes at scale
O_b(R+V+1) by elementary absorption.
In general combining (6)-(7) and
absorbing the square root gives the
conditional bound

    M_* <= C_b''' (R+V+1+G_rem).                (8)

Indeed put A=R+V+1, bound all fixed
errors by constants depending only
on b times A, and use
sqrt(M_* A)<=epsilon M_*+A/(4epsilon)
for sufficiently small b-dependent
epsilon. If a global smallest atom
is in B_c, D_remote<=C_env directly
and no remote ratio is needed.
If all atom lengths >=2s, the global
width is absolutely bounded by C_env.

The important distinction from G_T
is that the padding in (7) can be
remote. Its location is explicit:
r=k_*-k, so it consists of the fixed
number c-b of limbs at the reflected
index range b+k_*-k,...,c-1+k_*-k.
When a large remote width persists
above the R+V+1 scale, (8) forces
a large G_rem. Thus those reflected
padding limbs have a very small
total angular length relative to the
distance g_T^rem. Their atom widths
can be tested with the angular envelope.
No bound on that ratio follows merely
from its fixed number of limbs, and no
argument here asserts its absolute
control or that the reflected band is
near-critical. The remaining native
task is to bound or respond to this
specific angular degeneracy.

All these applications retain the
actual saturated geometric marking
and proper access/full-tower chart
premises, the bounded nonshort response,
and the exact corrected interval action.
The analytic boundary derivative lemma
and one-sided replacement are general
strip/modulus arguments, not verifications
of those native premises. No canonical
ledger status or MLC conclusion is
promoted. AI-assisted written mathematics;
independent specialist review pending.

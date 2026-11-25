# Angular envelope of the anchored maximum and bank-contact charge

Continuation of [ANCHORED_PHASE_FREE_RESPONSE](ANCHORED_PHASE_FREE_RESPONSE.md)
and [ANCHORED_SHORT_JUMP](ANCHORED_SHORT_JUMP.md).

This note reduces the remote-maximizer problem to explicit angular
geometry. The new comparison class has a canonical near-maximal
witness up to an absolute additive error: a concentric semicircle
packet around a smallest actual marked atom. It is not necessary
to select an arbitrary nearly maximal foliation for this class.

We also strengthen the nonshort charge: for a common-atom ambient
packet, only the tracked nonshort leaves need meet the near-critical
bank. The ambient common atom itself may be remote. As a result,
all but a quantified small part of the explicit remote maximizing
packet can be placed inside the proper middle corridor. This does
not yet relocate the packet to the near-critical bank. A large
terminal angular guard also gives an explicit actual nonshort
packet; this yields a strict relative bound on extreme guards, not
the absolute bound needed to finish the preceding long-jump program.

## 1. An absolute angular width envelope (no dynamical hypotheses)

Use a flat normalized annulus X=(R/Z)x(0,M_X), M_X>0,
with a finite marking by at least three positive-length
open atoms. Write

    s=min(1/4,M_X/2),
    m(ell)=log_+(2s/ell)/pi,
    C_env=5pi/log(2)+log(2)/pi.

Here log_+(x)=max(0,log x). Let I be any nonempty
proper connected marked interval of angular length ell,
consisting of whole atoms and their intervening cuts.
Use actual proper simple distinct-inner-ended cap paths
whose strict crest contains I. Let M(I) be the supremum
of widths of Borel laminations of such paths, with zero
if the class is empty. Then

    m(ell) <= M(I) <= m(ell)+C_env.              (1)

These are angular lengths in the conformal flat cylinder,
not combinatorial lengths or physical planar arc lengths.

### Lower bound: an actual canonical radial packet

If ell<2s, lift I to the real line with midpoint e and
endpoints e±ell/2. Take the semicircular paths
z=e+r exp(i theta), 0<theta<pi, ell/2<r<s.
They lie inside the source strip and project injectively
into X; distinct radii give disjoint simple proper paths.
Their oriented cap contains the whole I strictly between
its actual endpoints. Remove the finitely many radii
whose endpoints are marking cuts. The remaining paths
are marked-admissible: if endpoint atoms differ, at least
one whole crest atom separates them; if they coincide,
the cap takes the long route through all other atoms.
There are at least three original atoms. Their actual
Borel support and leaf parameter are explicit.
In logarithmic coordinates these are the vertical lines
in the rectangle of horizontal length log(2s/ell) and
vertical length pi. By the rectangle width calculation
(or Cauchy-Schwarz on every vertical line), their
width is exactly m(ell). Removing finitely many
radius fibers does not change this calculation.
If ell>=2s the claimed lower bound is zero.

### Upper bound: a uniform outer confinement even for a thin annulus

Lift every actual cap path containing I to the strip
with e represented by zero. Its real endpoints satisfy
x_-<=-ell/2 and x_+>=ell/2, and its base span is <1.
First charge paths whose lifted radius supremum is >=s.

If M_X>=1/2, then s=1/4, and the earlier fixed-anchor
metric of COHERENT_PACKET_GAIN at d=1 costs
4pi/log(2), independently of the strip height.

If M_X<1/2, then M_X=2s. Use instead the metric
1/(|z| log 2) on the half-annulus s/2<=|z|<=4s,
intersected with the strip. Its area is at most
3pi/log(2). Every bad path has length at least one:
if its infimum radius is <=s/2 it crosses the
radial interval [s/2,s]; if it reaches radius
>=4s, its passage through the vertical line x=0
has radius <=2s and gives a radial crossing
[2s,4s]; otherwise its trace stays in the
metric half-annulus and its argument varies
by pi. Limiting equality cases follow by
compact exhaustion. This uses the horizontal
crossing of the actual oriented strip path, not
its endpoint labels alone. Thus the same upper
cost 4pi/log(2) works at every modulus.

Next charge paths with radius infimum <=ell/4.
Since both endpoints have radius >=ell/2,
the half-annulus metric 1/(|z| log 2) on
[ell/4,ell/2] is admissible and has area
pi/log(2). Both bad metrics descend through
the strip covering by the all-sheet square-sum
without increased area. Infinite-length paths
are dealt with by vanishing constants in the
finite-area cylinder, as before.

The remaining paths lie in ell/4<|z|<s.
If ell>=2s none remain, since their endpoints
already have radius >=s. Otherwise their
argument variation is pi, so the density
1/(pi |z|) on this half-annulus is admissible
and has area log(4s/ell)/pi. Descend it by
the same square-sum rule. Subadditivity gives
the upper bound in (1), since the last area
is m(ell)+log(2)/pi. This is uniform even
if M_X tends to zero or infinity. QED.

In particular (1) compares the *entire* anchored
supremum to an explicit actual lamination, not
to a buffered canonical WAD scalar. It does not
assert that the literal source's general
controllable-Wave maximum has this envelope.

## 2. The exact angular version of the remote gap

Let M_* be the anchored maximum from the previous
notes. Let B_c=BL_(-c)..BL_c, c=b+8, and M_near the
same supremum restricted to a common atom in B_c.
Use q>=2b+20 below, so the bank and proper middle
have the intended cyclic order. Write

    ell_* = min angular length of any original atom,
    ell_near = min angular length of any atom in B_c.

These minima exist and are positive for each actual
marked annulus. Equation (1) implies

    m(ell_*) <= M_* <= m(ell_*)+C_env,
    m(ell_near) <= M_near <= m(ell_near)+C_env.

Hence, for D_remote=M_*-M_near and

    D_ang = (1/pi) log( min(2s,ell_near) /
                        min(2s,ell_*) ),

one has

    |D_remote-D_ang| <= C_env.                  (2)

This reduces the near-bank supremum gap in
ANCHORED_SHORT_JUMP to a clipped angular ratio
of two actual original marking atoms. If a
globally smallest atom occurs in B_c, the
gap is already <=C_env. If all atom lengths
are >=2s, M_*<=C_env and there is no large-width
case. Otherwise the explicit radial packet
over a globally smallest atom has width w
with M_*-w<=C_env. Its family and every radial
subfamily are supplied without a generic
near-maximal foliation selection theorem.

No uniform bound on D_ang is derived merely
from the combinatorial marking size. In
particular the count of atoms per limb is not
a conformal angular comparability theorem.

## 3. A remote ambient packet can still charge all bank-touching nonshort leaves

Use the exact corrected native geometric assumptions
of ANCHORED_PHASE_FREE_RESPONSE, including the actual
canonical H=h+2 tower, old-proper fine atoms, critical
deck pair, suffix-anchor coherence, and two-bank
host/fine-side realization. Take any fixed c>=b
with the corresponding consecutive near bank B_c.
Let A be an arbitrary member of C_* of width w>0.
Its actual common anchor may be in **any** limb.
Let S_c be the nonshort subfamily whose actual
marked cap base meets the open B_c (not merely
one of its limiting dividing cuts).

Retain the previous constants with the expanded
localization bound:

    h=b+2, H=h+2, N=h+12b*2^h, C=C_2,
    K_c=6b(2c+h+1)+1, J_c=max(12K_c,N,2),
    E=1+2^H V+H C,
    E_a=sum_(r=1)^h C_(2^r)+12b*2^h*C_(2^h),
    B_c^err=E+8K_c+(48K_c+12+2h)C+E_a+4R,
    a_c=(h+11)*sqrt(J_c).

The following strengthening is valid with the
same fixed global comparison cap M_*:

    W(S_c) <= B_c^err + a_c sqrt(M_*(M_*-w+E)). (3)

Proof. Construct the common positive raw primary
sequence through H exactly as in section 2 of
ANCHORED_PHASE_FREE_RESPONSE, using its actual
common atom wherever it lies. All images and all
fixed-probe auxiliary packets are in C_*, so
their widths are <=M_* without an endpoint
control certificate. Set d=M_*-w+E and
Q_n=sqrt(n M_* d). The global primary discard
cost E and disjoint support addition are unchanged.

The only use of a near-critical common ambient
anchor in the earlier theorem was to bound the
number of localized away modules at stages 0 and h.
For stage 0 we can instead use the defining bank
contact of the tracked subfamily S_c. If an away
cap meets B_c and both endpoint atoms are outside
B_c, it must traverse the entire connected bank,
including BL_0. This contradicts being away.
Thus each of these tracked away nonshort leaves
has an endpoint in one of the <=6b(2c+1)
bank atoms. The actual endpoint predicate is
Borel. Disjointize by first eligible atom and
apply the same bounded-probe median shift of
ANCHORED_PHASE_FREE_RESPONSE section 3, against
the entire D_1. The old ambient anchor is
noncritical on every away leaf; its remoteness
does not affect any of the six fixed median
probes, because their auxiliary packets are
capped by M_*.

The initial over-critical and central-ending
classes are charged by the same actual deck-pair
and adjacent-crest/precritical tests. Track the
central positive class by whole crests
BL_1,...,BL_(h+1), using the two end fine probes
and the raw auxiliary series allowance. Neither
the anchor of the whole primary packet nor any
singleton predicate is needed for this tracking.

At stage h the tracked remaining positive
leaves share the full crest BL_(h+1).
For their away class use the consecutive bank
BL_0,...,BL_(h+1), rather than the ambient
anchor's bank. A tracked away cap without an
endpoint in that bank would contain it entirely
and hence BL_0, again a contradiction.
Thus there are <=6b(h+2) localized modules.
The same K_c covers both stages, and the
previous median argument applies. The
over/precritical orientation charges and the
positive critical suffix/bank-contact proof
do not depend on the ambient common atom.
For small q use the same first precritical
stop as before. Every auxiliary comparison
is with the unchanged whole primary D_j,
not with an isolated tracked subpacket.
Collecting exactly the former error terms
gives

    W(S_c) <= B_c^err+4Q_(12K_c)+(h+6)Q_2+Q_N,

which implies (3). QED.

For near-bank ambient A every nonshort leaf
belongs to S_c, so the previous result follows.
For a remote A, (3) only charges the specified
nonshort bank-touching part; it does not bound
nonshort leaves wholly inside the remote
noncritical corridor.

## 4. A quantitative localization of the explicit remote maximizer

Use the c=b+8 bank in section 2 and the slightly
smaller bank B_(c-1) in the following test.
Assume M_*>C_env. If a globally smallest atom
belongs to B_c, then D_remote<=C_env by (2)
and the desired near-bank approximation is
already established.

Otherwise choose a globally smallest atom A_*
outside B_c and its actual radial packet of
width w=m(ell_*)>0 from section 1. Its midpoint
e is at positive cyclic angular distance

    rho=dist(e, closure(B_(c-1)))

from the smaller bank, with rho>=ell_*/2.
The limb of A_* and the smaller bank are
separated by at least one complete intervening
limb in either direction around the circle.
Consequently every radial path over A_* whose
cap meets the open smaller bank is nonshort:
the arc from A_* to that bank traverses a
complete intervening limb. For a semicircle
of radius r<s<=1/4, its actual oriented
cap is exactly the circular interval of
radius r about e. It meets the open bank
precisely when r>rho, up to the negligible
boundary radius. Hence the width of that
bank-touching subpacket is exactly

    (1/pi) log_+(s/rho).

Apply (3) to the explicit radial packet with
the smaller bank (the constants for c are
a safe overcount). Since M_*-w<=C_env,

    (1/pi) log_+(s/rho)
      <= B_c^err + a_c sqrt(M_*(C_env+E)).       (4)

In particular the concentric subpacket with
r<rho has width at least

    M_* - C_env - B_c^err
         - a_c sqrt(M_*(C_env+E)).              (5)

All its actual cap bases avoid B_(c-1) and
lie within the remote proper middle corridor
(the complement of that bank is contained
in BL_[b,q-b-2]). Its common atom is still
A_*, and its Borel presentation is explicit.
Thus above the large absolute scale
M_* >>_b R+V+1, there is either a near-bank
radial packet within C_env of the global
maximum, or an explicit almost-full-width
concentric packet wholly in the proper
middle corridor. The latter may include
nonshort leaves whose endpoints range over
many remote limbs.

This is an actual source-width localization,
not a claim that the latter packet can
already be long-jumped to the near bank.
To finish the remote task one now needs
relocation only for this explicit concentric
middle-corridor packet (or another native
response when its caps span many limbs),
rather than a near-maximal selection theorem
for arbitrary Borel controllable Waves.
The long-jump theorem in ANCHORED_SHORT_JUMP
requires the whole bases to lie in one
proper band through every intermediate
iterate; that condition need not hold for
all the radii in (5) at a jump moving the
anchor all the way to the near bank.

## 5. A real width response to an extreme terminal angular guard

Use the six terminal limbs and the angular guard
G_T from ANCHORED_SHORT_JUMP. Let

    p_T = min(L_T,R_T),
    L_0=log_+(1/(4s))<=V/2,
    z = (G_T-L_0)_+/pi.

Here L_T is the sum of two left padding limb lengths
and R_T is the one right padding limb length.
There is an actual whole padding limb of length
ell_p<=p_T (take the right one if it realizes the
minimum, otherwise one of the two left limbs).
It lies in B_c. The bound for L_0 follows from
s=min(1/4,M_X/2): it is zero for M_X>=1/2
and log_+(V/2)<=V/2 otherwise.

Because A_T<=1,

    G_T=log(A_T/(2p_T)) <= log(1/(2p_T))
         <= log_+(2s/p_T)+L_0.

The explicit radial packet crested over the
**whole** padding limb has width
w_p=m(ell_p)>=z by (1)'s lower construction.
If z>0 it is an actual positive-width
near-bank member of C_*; every leaf is
nonshort. If z=0 the following bound is
trivial. Apply (3) to this packet:

    w_p <= B_c^err + a_c sqrt(M_*(M_*-w_p+E)).

Since w_p>=z and the right side decreases
with w_p, we get the exact guard response

    (z-B_c^err)_+^2
       <= a_c^2 M_*(M_*-z+E).                  (6)

For example set t=1/(64(a_c+1)^2). If
E,B_c^err<=t M_* and z>(1-t)M_*,
the preceding bound on w_p would imply
w_p/M_*<=t+a_c sqrt(2t)<1/2 while
w_p/M_*>1-t>1/2. Thus

    G_T <= L_0+pi(1-t)M_*                     (7)

at that absolute scale. The guard cannot
be arbitrarily close to the full anchored
maximum on its natural logarithmic scale
without producing a near-maximal nonshort
packet and hence a contradiction.

This is a native *relative* exclusion under the
stated geometric assumptions. It does not give
G_T=O_b(R+V+1), nor the much smaller relative
guard needed by the conservative bounded
deficit schedule of ANCHORED_SHORT_JUMP.
A guard of a substantial smaller fraction
of M_* is not excluded by (6). No
quantitative comparability of terminal
limb angles is inferred from the occupancy
bound.

## 6. Remaining precise tasks

The new route now has explicit near-maximal
test foliations, not merely existence of a
global arbitrary maximum. The two residual
quantities of ANCHORED_SHORT_JUMP can be
tested directly on actual conformal angular
marking: the clipped minimum-atom ratio (2)
and the six-limb padding ratio. The new
bank-contact response supplies (5), restricting
the remote case to an actual concentric
family inside the noncritical proper middle.
The extreme-guard response (6) restricts the
possible terminal distortion, but is not
yet an absolute guard bound.

The next geometric acceptance test is to
transport the high-width concentric middle
packet to the near bank without paying its
entire long base span, or use a native
response for the radii that cannot undergo
one proper-band jump. A separate terminal
guard bound or guarded alternative response
is also needed. Exact native marking,
saturated carrier and proper-middle
realization, source initial witness typing
and downstream amplification remain
premises/gates. No phase-free unconditional
native theorem or MLC assertion is made.

The companion checker tests the clipped
ratio, radial interval factorization,
bank-distance and guard algebra. The
semicircle modulus, actual geometry and
native response proof are written mathematics,
not established by the finite tests.
No canonical ledger promotion. AI-assisted
research; independent specialist review
pending.

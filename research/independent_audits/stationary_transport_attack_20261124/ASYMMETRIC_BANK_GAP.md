# One-sided local bank expansion and marked backward distortion certificate

Continuation of [LOCAL_BANK_CAP](LOCAL_BANK_CAP.md) and
[GUARD_FREE_ANGULAR_JUMP](GUARD_FREE_ANGULAR_JUMP.md).
The symmetric enlarged bank in the former comparison can
be replaced by a strictly smaller asymmetric bank: only
the positive side needs to expand. If its minimum atom
produces a large width gap, a bounded proper-middle chart
reduces that gap to a marked subdivision ratio and a
one-sided angular boundary margin. This is a concrete
sufficient test for the remaining native estimate, not
a proof of that estimate.

## 1. Asymmetric cap

Use all actual corrected geometric, saturated graph/host,
proper-middle chart, canonical occurrence and Borel
hypotheses of LOCAL_BANK_CAP. For this note choose the
fixed b-dependent constants

    h=b+2, H=h+2, c=2b+20, t=H+2,
    B=BL_[-c,c], B^+=BL_[-c,c+t],

and q>=2(c+t)+4. The negative limb notation is modulo q.
The larger c (instead of b+12) leaves a finite reserve
for the backward chart below. Let M_B and M_+ be the
anchored suprema of actual C_* packets having a common
whole crest atom in B and B^+, respectively. Set

    Delta_+ = M_+ - M_B >= 0.

These are finite by the angular envelope. No global
remote anchored cap is used.

We verify that all uses of the expanded bank in
LOCAL_BANK_CAP can use B^+, which does not enlarge its
negative side.

**Primary sequence.** Starting with a common atom in B,
a noncritical old-proper anchor translates by one in
the positive direction; a critical one maps into
BL_[-b,b]. Therefore the actual common atoms through
H primary steps all lie in BL_[-c,c+H]. In particular
a negative anchor never moves farther out on the
negative side. All whole primary images are capped by
M_+.

**Remote median auxiliaries.** At the two relevant
stages the away localized end can still be chosen in
B: at stage zero the original common atom belongs
to B, and at stage h the tracked common whole
BL_(h+1) crest is in B. If an away cap with an
inside bank anchor had both ends outside B, it
would traverse the whole bank and therefore BL_0.
This is impossible. Disjointize its ending atom
choice as before. Let the far corridor be exactly

    J_old=BL_[c+1,q-c-1].

If the old probe atom belongs to B, its target
fine image atom is in BL_[-c,c+1] or B_b. If the
probe lies in either of the first or last limbs
of J_old, its target atom is in BL_(c+2) or
BL_(q-c), both in B^+. In the other cases the
probe lies strictly inside the proper middle
corridor. By the same endpoint argument of
LOCAL_BANK_CAP section 2, at least one of the
two raw gap ends lies outside the pulled J_old:
otherwise both would be original parent
endpoint times and both old ideal ends would
lie outside B. A simple cap containing the
interior probe and reaching outside J_old
therefore contains the whole first or last
pulled limb block, with point-cut exceptions
removed. Its simple output has a whole crest
atom in BL_(c+2) or BL_(q-c). Split into the
two cases within the actual fixed probe chart;
the total auxiliary width per probe is <=2M_+,
just as before. The negative side stays inside
B throughout. No claim is made about a remote
gap without the actual old-proper probe and
parent endpoint hypotheses.

**Other nonshort auxiliaries.** The critical deck
pair, positive/precritical crest tests, coherent
suffix anchors and actual two-bank separator
anchors all have target atoms in BL_0 through
BL_(h+2) or B_b, as recorded in the preceding
notes. These are inside B^+. No remote target
endpoint estimate is required.

**Short program.** At every ordinary macro-stage
start the common short interval meets B and
spans at most two consecutive limbs. Its end
probe atoms are therefore in BL_[-c-1,c+1].
The noncritical images move one step forward,
and critical old-proper images land in B_b.
The resulting target atoms lie in
BL_[-c,c+2], inside B^+. At saturation choose
the outside old atom in B as in LOCAL_BANK_CAP;
the images of all tested atoms stay inside B^+.
The adaptive long jump lands in the original
negative bank by the guard-free theorem. Its
width loss is <=40(V+1) and its new actual
radial family has the whole translated crest.
The starting intervals remain anchored in B;
the high-type macro-stage bound used earlier
can be enlarged to

    L_macro=(12b(18b-1)+2)(2c+16),

a safe bound depending only on b. This accounts
also for starting farther out in the larger
negative bank before a critical visit. No
conceptual intermediate long-iterate interval
requires a separate width cap.

Thus the entire nonshort and short argument of
LOCAL_BANK_CAP holds with M=M_+ and
Delta_loc=Delta_+, changing only the fixed
constants by the stated c and L_macro. In
particular its local nonshort bound uses
K=6b(2c+1) and J=max(24K,N,2) as before.
The backwards tolerance proof with this cap
gives

    M_+ <= C_b (R+V+1+Delta_+).                (1)

For the source input with k localized modules
and one actual leafwise-over-critical module,
the direct one-sided directional comparison
of LOCAL_BANK_CAP section 5 still uses only B
(the terminal six-limb bands are in it).
Consequently

    W(input) <= C_(b,k) (R+V+1+Delta_+).       (2)

The same initial Borel/leafwise typing and
downstream source requirements remain. Unlike
the symmetric local bank, a minimum atom of
B^+ outside B must lie in the bounded positive
strip BL_[c+1,c+t]; no negative expansion case
is left.

## 2. Actual bounded backward chart for a new minimum atom

Use the normalized original annulus X of height
M_X, circumference one, V=1/M_X, and
s=min(1/4,M_X/2). Let ell_B be the minimum
actual original atom length in B, ell_+ the
minimum in B^+.

If a minimum atom is already in B, the
angular envelope gives Delta_+<=C_env.
Otherwise let A_* be an actual minimizing atom
in a limb k=c+r, 1<=r<=t. Use the old proper
middle band

    J_old = BL_[b,q-b-1-r].

For every input stage j<r its translate lies
in BL_[b,q-b-2]; at the last input its right
end is q-b-2. By the proper full-tower chart
of ANCHORED_SHORT_JUMP, there is an actual
interval J_s on the full r-th source ideal
circle mapping homeomorphically under the
old limit of I_r onto J_old, and under P_r
onto the actual terminal band

    J_new=BL_[b+r,q-b-1].

The covering degree is d=2^r, bounded here
only in terms of b. The target atom A_* lies
strictly in the interior of this terminal
band, in BL_(c+r).

The corrected geometric marked action on
this fully proper interval maps every whole
original old atom to a connected union of
whole original target atoms, with the actual
orientation and cut conventions. This is
the nonempty fine-refinement property of the
standing corrected marking, iterated in the
proper middle chart (not the literal
unrestricted maximal-subset definition).
Those images have disjoint interiors and
cover the terminal band. Therefore A_* is
contained in the image I_new of exactly one
whole old original atom I_old in BL_c.
It may be a proper constituent of I_new.
We do not assume atom-to-atom behavior
merely from the absence of added carrier.

Let I_s=(v,w) be the actual corresponding
subinterval in the proper full source chart,
let x_0=(v+w)/2, ell_s=w-v, and write
J_s=(l,u) in its universal strip.
Define the actual marking and margin numbers

    L = |I_new| = d ell_s,
    S = L/ell_+ >= 1,
    G = d min(x_0-l,u-x_0) > 0.

The two margins in G are measured on the
actual target angular circle from the
midpoint of the entire forward image
I_new to the two ends of J_new, using the
compatible oriented real lifts. In
particular G<=1. S is a genuine marked
subdivision ratio, not the number of
constituent atoms in I_new. If the
proper middle marking is atom-to-atom
through this chart, then S=1 exactly.
This is an additional source check
when needed; no such equality is
assumed in this note.

## 3. Boundary derivative bound for a reverse atom comparison

Let F be the actual holomorphic strip lift
of the immersion I_r. On J_s it has its
real increasing proper old limit. Put
D=exp(3pi V). The positive Herglotz
derivative inequality of
GUARD_FREE_ANGULAR_JUMP section 2 applies:

    F'(x)/F'(y) <= D *
       max(1,(y-l)/(x-l),(u-y)/(u-x))^2.

Put g=G/d. If ell_s<=g, every x in I_s
is within g/2 of x_0 and its distances
to the chart ends are at least half the
corresponding x_0 distances. Hence

    F'(x)<=4D F'(x_0) on I_s.

For y in [x_0-g/2,x_0+g/2], the inverse
ratio gives F'(y)>=F'(x_0)/(4D), since
its distances to the chart ends are at
most 3/2 of those for x_0. The whole
old limit interval F(J_s) has real
angular length <=1. Integrating on
the latter interval of length g yields

    F'(x_0)<=4D/g.

Integrating the upper derivative on
I_s gives the actual old atom bound

    |I_old| <= 16 D^2 ell_s/g =16 D^2 L/G.    (3)

If ell_s>g, the right side exceeds
one and (3) is immediate from the
old interval length bound. Thus
(3) holds in all cases. It uses
positivity and the upper-half-plane
kernel, not a bounded distortion
claim for arbitrary real boundary
homeomorphisms. It does not require
full global univalence of I_r.

Since I_old is an actual original
atom in BL_c, ell_B<=|I_old|.
The angular envelope for the two
banks then gives (if ell_+<2s;
otherwise Delta_+<=C_env directly)

    Delta_+
       <= C_env + (1/pi) log(ell_B/ell_+)
       <= C_env + log(16)/pi + 6 V
                     + (log S+log(1/G))/pi.   (4)

In the first line the exact clipped
ratio could be smaller; using the
unclipped ell_B only weakens the
upper bound. This is a reverse
**angular replacement**, not an
assertion that the target radial
packet has a full inverse path
lamination on the earlier surface.

Thus a sufficient new native certificate
for (2) at the needed absolute scale is
a bound

    log S + log(1/G) <= C_b (R+V+1).          (5)

The subdivision term and the margin
term are both defined for one bounded
actual proper full chart, not an
unbounded remote maximizing orbit.
In particular, if atom-to-atom ancestry
is certified, a large remaining local
gap forces an exponentially small
actual distance of the whole forward
image atom to a limiting cut of the
translated proper middle corridor.
If the margins are controlled but the
gap is large, it forces a large true
angular subdivision inside the image
of an old atom, which is a different
marking/geometry issue.

## 4. Where a small margin must occur

The choice c=2b+20 ensures c-b>=t+1
because t=b+6. For r<=t we have
b+r<c. The terminal band starts at
BL_(b+r), and the minimizing atom is
in BL_(c+r). The entire limb BL_c
belongs to the left margin from that
start cut to the midpoint of I_new.
The right margin similarly contains
the whole limb BL_(q-c) (q is in
the indicated high-type range).
Both are in the original bank B.
Hence whichever margin realizes G
contains a whole B limb of angular
length at most G. Its explicit
whole-limb radial packet is an
eligible C_* near-bank family, so

    log(1/G) <= pi M_B + log(1/(2s)).

Together with (4) this gives the
weaker but unconditional-on-margin
relative constraint

    Delta_+ <= M_B + C_env + O(V+1)
                              + log(S)/pi.    (6)

It is useful as a consistency check
and shows that an extreme margin
already gives an actual near-bank
nonshort witness. It is **not** an
absolute control of Delta_+; (6)
cannot replace (5) in the strict
deficit comparison without another
response. Nor does the count of
atoms per limb bound S or G.

## 5. Disposition

The principal prior global and
terminal guard obstructions have
now been bypassed for the stated
source-localized initial class.
The remaining expansion gap is
one-sided and can be attacked by
checking actual old-to-new atom
ancestry and the two proper-band
angular margins. This is a local
finite native geometric target,
with the above explicit sufficient
quantitative certificate. The
corrected source action, actual
saturated hull/prime-end and
proper-middle charts, two-bank
host realization, initial source
typing and downstream amplification
still require verification. No
canonical ledger entry is promoted,
and no stationary or MLC theorem
is asserted unconditionally.

The companion checks are finite
index and ratio bookkeeping only;
the strip estimate and native
arguments are written mathematics.
AI-assisted research; independent
specialist review pending.

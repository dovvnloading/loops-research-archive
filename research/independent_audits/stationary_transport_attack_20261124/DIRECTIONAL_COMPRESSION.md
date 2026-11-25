# Directional boundary compression: a margin-free reduction of the local bank gap

Continuation of [ASYMMETRIC_BANK_GAP](ASYMMETRIC_BANK_GAP.md),
[PROPER_MIDDLE_ATOM_ANCESTRY](PROPER_MIDDLE_ATOM_ANCESTRY.md), and
[GUARD_FREE_ANGULAR_JUMP](GUARD_FREE_ANGULAR_JUMP.md).

**New result.** For the conditional asymmetric-bank argument, a
large positive-strip gap cannot be caused by arbitrary independent
distortion of one tiny atom. The positive boundary derivative has
two one-sided contributions. Large compression in one proper
middle step forces comparable compression of every earlier
interval, or of every later interval in the same proper corridor.
The latter case carries the new minimum atom forward into the
original negative bank and is impossible. The former case forces
a whole run of contracting limbs.

This removes the need to estimate the angular distance G to a
proper-chart endpoint in the backward-atom ratio. In its place
there is a *specific observable forward compression* of whole
limbs. This compression is not proved absolutely bounded here.
The result is conditional on the same corrected native geometry
and marking as before. In particular it is not an unconditional
closure of the KKL stationary or amplification theorem.

## 1. Standing chart and marking hypotheses

Use the actual one-step annular covering P_1 of degree two and
the holomorphic immersion I_1, with old and target cylinder X
of circumference one and height M_X>0. Put V=1/M_X.
The source cylinder has height M_X/2. Retain the actual proper
middle chart on BL_[b,q-b-2] of GUARD_FREE_ANGULAR_JUMP:
the immersion has its continuous proper homeomorphic old
boundary limit on the entire pulled open band (including the
internal dividing cuts), and the covering maps this band
homeomorphically onto BL_[b+1,q-b-1].

Use the induced angular real coordinates in those *actual*
annuli. In particular the chart is not merely a topological
limb labelling. On every noncritical middle limb the whole
old marked atom maps to a connected nonempty interval of
whole target marking atoms; interiors of the images of
distinct old atoms are disjoint. Keep the original marked
cut identification and positive fine-refinement hypotheses
used in ASYMMETRIC_BANK_GAP section 2. No atom-to-atom
hypothesis is needed until an explicit simplification in
section 4.

Write T=(a,z) for the actual terminal band in a compatible
real lift of the target inner ideal circle. Its angular
length is <=1. If y is the terminal angle and x=(y-y_0)/2
the corresponding source angle, let

    H(y)=F(x),

where F is the old-limit holomorphic strip lift of I_1.
Choose the additive real lift constants once. H is strictly
increasing on T, and

    H(BL_i) = BL_(i-1)   (b+1<=i<=q-b-1)

as actual oriented intervals, with equality of angular
lengths as measured by integrating H'. (Here the notation
means H is the reverse boundary map; not the forward
covering.) Analytic reflection gives H'(y)>0 on T by the
positive harmonic representation or the Hopf lemma.

Let L_i=|BL_i|>0 denote the actual original angular limb
lengths; their sum over all q limbs is one.

## 2. A directional positive-kernel lemma

**Lemma.** For any nondegenerate proper interval E contained
in T put A_E=|H(E)|/|E|. At least one of the following holds:

(L) For every interval D contained in T entirely to the left
    of E, |H(D)|/|D| >= exp(-pi V) A_E/2.

(R) For every interval D contained in T entirely to the right
    of E, |H(D)|/|D| >= A_E/2.

The same conclusion holds for individual points of the
corresponding open side of E, with the quotient replaced by
H'(y). These are simultaneous inequalities on the entire
specified side, not independent choices of a side for each D.

**Proof.** Use the Herglotz representation on the upper
half-plane as in GUARD_FREE_ANGULAR_JUMP section 2. The
exponential source strip coordinate is

    u(y)=exp(pi (y-y_0)/M_X).

Indeed the factor two in the covering and the factor two
in the source strip height cancel. The composed upper
half-plane map is holomorphic into the upper half-plane.
It extends real analytically on (u(a),u(z)).
Its positive harmonic boundary measure mu has no mass
on this open interval. Thus, for some beta>=0,

    H'(y) = (pi/M_X) u(y)
                 [ beta + int (v-u(y))^(-2) dmu(v) ].

As in the earlier note the differentiation is justified
by compact separation from the support and the Herglotz
integrability condition. Define the two nonnegative
parts h_L,h_R by splitting the measure into
v<=u(a) and v>=u(z), assigning beta to h_R.
Then H'=h_L+h_R.

If y<x in T, the left summands at y are at least
u(y)/u(x) times those at x: for v<=u(a), the
denominator u(y)-v is no larger than u(x)-v.
Since x-y<=1, u(y)/u(x)>=exp(-pi V).
The entire left part satisfies

    h_L(y) >= exp(-pi V) h_L(x)   (y<x).

For x<y in T the right denominators v-u(y)
are no larger than v-u(x), and the prefactor
u(y) is no smaller. The beta part also increases.
Hence

    h_R(y) >= h_R(x)   (x<y).

On E, either the average of h_L is at least
A_E/2, or the average of h_R is at least A_E/2.
For every point on the corresponding side of E,
integrate the just-proved pointwise inequality
over x in E and divide by |E|. This gives (L)
or (R) pointwise; integrate over D to obtain
the stated interval quotient. Limits at the
outer chart ends may be handled by increasing
compact subintervals, using the proper boundary
homeomorphism and monotonicity of integration.
No comparison of absolute angular margins was
used. QED.

The lemma needs a genuine holomorphic map between the
strips with a proper real boundary segment and the
positive harmonic representation. An arbitrary cyclic
order preserving map between marked intervals need not
satisfy this two-sided alternative.

## 3. Exclude right compression by forward continuation

Use c=2b+20, h=b+2, H_0=h+2, t=H_0+2, with
q>=2(c+t)+4, and the banks

    B=BL_[-c,c], B^+=BL_[-c,c+t].

(Here H_0 is a horizon, distinct from the boundary
map H.) Denote their anchored suprema by M_B,M_+ and
Delta_+=M_+-M_B. Let ell_B and ell_+ be the respective
minimum actual original marking atom lengths. Use
C_env and s=min(1/4,M_X/2) from the angular envelope.

If ell_B=ell_+, Delta_+<=C_env directly. Otherwise
choose a minimizing atom A_* in BL_k with k=c+r,
1<=r<=t. As in ASYMMETRIC_BANK_GAP its actual whole
old atom ancestor I_0 is in BL_c. Define I_j to be
the entire geometric proper marked forward image
of I_(j-1), for j=1,...,r. These are connected
nonempty whole marked intervals in BL_(c+j).
I_r contains A_*; do not replace it by A_* unless
atom-to-atom ancestry has been verified.
Let

    S=|I_r|/ell_+ >= 1,
    A_j=|I_(j-1)|/|I_j|>0,
    A=max_(1<=j<=r) A_j.

Then

    ell_B/ell_+ <= S prod_(j=1)^r A_j <= S A^r.

The first inequality uses the actual old original atom
I_0; the product telescopes exactly. If A<=2, this
already gives the desired bounded compression factor
up to S. Suppose A>2, and choose an index j_* realizing
A. Apply the directional lemma to E=I_(j_*) in the
same one-step terminal band T. Its average derivative
is exactly A, because H(I_(j_*))=I_(j_*-1).

If alternative (R) holds, consider the actual whole
marked forward image of the minimizing atom A_*.
It lies in BL_(k+1), strictly to the right of E,
and stays in T if k<=q-b-2, as is true here.
Its old image under H is exactly A_*. The lemma
shows its length is <=2 ell_+/A < ell_+.
Choose any whole constituent original atom of
that forward image; its length is no larger.
Repeat with its actual marked forward image and
one whole constituent in the next noncritical
limb. All these images stay strictly to the
right of E. The final step has old limb q-b-2
and target q-b-1, so stays within the actual
proper chart. The resulting atom belongs to
BL_(q-b-1), in the original bank B, and has
length <=ell_+, contradicting ell_B>ell_+.

This excludes (R) in the A>2 case without a
backward extension of the proper chart or a
long-iterate distortion estimate. It is also
valid when each whole marked image subdivides:
at each step select a genuine whole constituent
atom after using the derivative bound on the
entire connected image. The degree of the long
iteration is irrelevant; the same actual
one-step angular inequality applies at each
of its successive limb intervals.

Consequently (L) holds. For every j=b,...,c-1,
the entire terminal limb BL_(j+1) lies strictly
to the left of E (whose limb index is >=c+1).
Its old image under H is BL_j. Thus

    L_j/L_(j+1) >= exp(-pi V) A/2.            (1)

This is the simultaneous whole-limb contraction
assertion. It is stronger than the existence of
one small margin or one small limb.

## 4. Margin-free expansion-gap estimate

Define the observable one-step minimum compression

    Q_c = min_(b<=j<c) (L_j/L_(j+1)) > 0.

For A>2, equation (1) implies A<=2 exp(pi V) Q_c.
For A<=2 use the trivial bound. Together, for
all cases with a new minimum outside B,

    log A <= log 2 + pi V + log_+ Q_c.

Therefore the actual angular envelope gives

    Delta_+ <= C_env + (log S)/pi
                  + t (V+log(2)/pi)
                  + (t/pi) log_+ Q_c.        (2)

If ell_B=ell_+ take S=1 for this bound; no backward
ancestor need be selected in that case. Clipping at
2s in the angular envelope can only reduce the
logarithmic ratio, so (2) also covers the case
when the minimum lengths exceed the strip's radial
scale. All intervals used for the compression
argument are in the one-step proper middle chart.

When the exact full graph-side atom ancestry
of PROPER_MIDDLE_ATOM_ANCESTRY is verified,
S=1, and (2) has no subdivision or angular margin
term. A sufficient remaining native quantitative
certificate for the conditional fixed-control
width theorem is now

    log_+ Q_c <= C_b (R+V+1),                 (3)

in place of the previous log(1/G) certificate.
In particular it is enough to bound **any one**
of the finitely many actual whole-limb compression
ratios L_j/L_(j+1), b<=j<c, at that scale. For
example the ratio at j=b suffices, irrespective
of which atom of the added positive strip is
minimal. No such bound follows just from the
positive-kernel lemma; the dynamics must still
control at least one of these compressions or
give another response.

This identifies a one-sided finite-chain
failure certificate. A very large expansion
gap with negligible log S requires *every*
one of these b-dependent finitely many
actual ratios to be large, not just a
single highly compressed atom. It also
eliminates the right-margin alternative
from the remaining problem.

## 5. Telescoped relative gap and nonshort witnesses

The minimum of the ratios is no larger than their
geometric mean:

    Q_c^(c-b) <= L_b/L_c.

Hence the previous estimate strengthens to

    Delta_+ <= C_env + (log S)/pi
                  + t (V+log(2)/pi)
                  + t/(pi(c-b)) log_+(L_b/L_c).   (4)

Let w_c=log_+(2s/L_c)/pi, the width of the explicit
whole-BL_c radial packet from ANGULAR_ANCHORED_ENVELOPE.
Since L_b<=1, and log(1/(2s))=log(max(2,V))<=log 2+V,

    log_+(L_b/L_c) <= pi w_c+log 2+V.

Therefore

    Delta_+ <= E_{b,c}(V) + (log S)/pi
                         + t/(c-b) w_c,       (5)

where one can take

    E_{b,c}(V) = C_env + t(V+log(2)/pi)
                        + t/(pi(c-b))(log 2+V).

This is a relative bound in terms of the width of an
**actual whole-limb nonshort witness**, not just the
full anchored maximum. For the stated c=2b+20 the
coefficient t/(c-b) is strictly less than one.
For any larger fixed c with the same proper chart
and q>=2(c+t)+4, the directional argument and (4)-(5)
remain valid with the new indices and constants.

In fact for each integer m with 1<=m<=c-b,
(1) gives

    L_(b+m) <= (2 exp(pi V)/A)^m L_b

in the active A>2 left case. Every one of these
limbs has a corresponding explicit radial witness
with width at least

    log_+(2s (A/(2 exp(pi V)))^m / L_b)/pi.

All those packets belong to the original near-bank
anchored class. They are genuine Borel families;
there is no assertion that their different
supports are disjoint or that their widths add.
This is a sequence of lower bounds for separate
whole-limb nonshort tests.

### Why (5) alone does not close the proof

The previous finite anchored deficit argument
needs a very small relative cap gap, whose
tolerance depends on the bank radius c and
on the number of macro-stages. Increasing c
makes t/(c-b) small, but also changes that
tolerance, the localized module count, and
the macro-stage bound. One must not simply
choose c large and claim the two errors
absorb. A uniform-in-c comparison argument,
or an absolute charge for the early full
limb compression, is still required. In
particular a sequence of very small limb
lengths decreasing geometrically over this
run is compatible with the *finite scalar*
inequalities (1), (4), and (5). That is a
negative control for the scalar bookkeeping,
not a native dynamical counterexample.

The improvement over the previous angular
margin reduction is the explicit form (2):
even if the old margin is tiny, a bad gap
cannot persist without simultaneous
forward compression through the entire
early proper run. Estimating this one
dynamically realized compression profile
is the next narrower analytic target.

## 6. Scope and verification

All the exact native corrected marking, actual proper
middle chart, full-tower ancestry, saturated graph/host
and Borel/source input hypotheses of the preceding
anchored program remain in force. The old unrestricted
A.3.2 subset interpretation is not restored. The
directional analytic lemma itself requires only its
stated proper strip chart; the forward continuation
and local-bank application require the actual native
marking and limb action. The source's fixed-control
width conclusion and downstream MLC integration
remain conditional.

The companion discrete regression tests directional
positive kernel monotonicity, the forward-to-bank
indices, the product ratio implications including
subdivision, and the whole-limb telescoping bound.
Finite arithmetic is not a proof of the holomorphic
or native geometric hypotheses. No ledger status
is promoted. AI-assisted written proof; independent
specialist review pending.

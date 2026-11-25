# No-fixed-point compression bound and a constant-marking bank

Continuation of [DIRECTIONAL_COMPRESSION](DIRECTIONAL_COMPRESSION.md),
[ASYMMETRIC_BANK_GAP](ASYMMETRIC_BANK_GAP.md), and the anchored
nonshort/short comparison program.

**Main advance.** Both quantitative angular defects of the local
bank comparison can be removed under the previously stated exact
geometric hypotheses. A large left derivative contribution cannot
decay quickly enough to avoid a fixed point of the reverse boundary
shift, unless the proper corridor ends first. In that case the same
large derivative persists to the end of the corridor and transports
the new minimum atom into the original bank. This gives an absolute
bound on the relevant one-step angular compression. A finite
constant-marking plateau then removes the subdivision factor,
without requiring a separate proof that all proper middle limbs
have atom-to-atom ancestry.

Combined with the preceding local-bank response, this gives a
conditional estimate W(A)<=C_(b,k)(R+V+1) for the stated actual
localized plus leafwise-over-critical input class, independent of
the rotation denominator in the high-type range. It is a new
conditional route to the source Wave-amplification conclusion.
The actual corrected native marking, proper-middle chart, saturated
carrier/host geometry, parent realization and source-witness typing
remain hypotheses. This is not an unconditional proof of the printed
KKL stationary proposition, Proposition 3.9, or general MLC.

## 1. Use the common old/target angular coordinate

Retain the actual one-step proper-middle strip chart and the
standing geometric/marking hypotheses of DIRECTIONAL_COMPRESSION.
In particular I_1 maps the actual annulus X_1 to X=U minus T,
P_1:X_1→X is the proper degree-two covering, and the immersion
has continuous proper homeomorphic old-boundary limits on the
whole pulled band of BL_[b,q-b-2], including its internal cuts.
The actual covering image of that interval is BL_[b+1,q-b-1].

Write M_X=mod(X)>0, V=1/M_X. Use the normalized angular coordinate
of this *same* old and target annulus, cut just before BL_1.
Write x_i for the beginning of BL_i in that compatible real
coordinate for 1<=i<=q-1, with x_q the beginning of BL_0 at
the right. Let L_i=x_(i+1)-x_i>0 denote the limb angular lengths.
The terminal proper chart is the interval

    T=(a,z)=(x_(b+1),x_(q-b)),

of length <=1. Let H:T→(x_b,x_(q-b-1)) be the reverse real
boundary map from the preceding note: take the selected inverse
of the actual degree-two boundary covering, then the proper old
limit of I_1. Fix its additive real lift so that

    H(x_i)=x_(i-1)  (b+1<=i<=q-b),

with endpoint limits at the extreme cuts.

For every interior point y in BL_i, H(y) is in BL_(i-1),
so H(y)<y. The same strict inequality holds at all internal
dividing cuts, by the displayed actual endpoint identities.
Thus

    H(y)<y for all y in T.                         (1)

This is the key extra fact beyond an arbitrary increasing real
boundary homeomorphism. It uses actual limb translation on the
same normalized X on both sides, not coordinates chosen
independently for the old and new intervals. No quantitative
lower bound on any individual limb length is assumed.

The Herglotz representation of the holomorphic strip lift, with
the scaling y→x=(y-y_0)/2 of the chosen covering inverse, gives

    H'=h_L+h_R,

where h_L,h_R>=0 are the contributions of the positive boundary
measure to the left and right of the exponential interval
(u(a),u(z)), respectively (put the nonnegative linear term
in h_R). Here

    u(y)=exp(pi V (y-y_0)).

We use exactly the analytic decomposition proved in
DIRECTIONAL_COMPRESSION, section 2. In particular

    h_L(v)>=exp(-pi V) h_L(w) for a<v<=w<z,
    h_R(w)>=h_R(v)            for a<v<=w<z.        (2)

All these are pointwise statements on the actual proper strip
interval, including its internal dividing cuts by real analytic
reflection. The boundary measure has no mass in the open
exponential interval. We do not assume that the immersion is
proper at its outer end or outside the stated middle chart.

## 2. A left contribution cannot decay too quickly

Fix x_0 in T and put m=x_0-a>0. For any y in T with

    x_0<=y<=x_0+m

we claim the additional comparison

    h_L(y) >= exp(-2pi V) h_L(x_0)/4.             (3)

To prove it, consider a summand of the positive left measure at
a real point v<=u(a). For u(x_0)<=u(y), the ratio

    (u(x_0)-v)/(u(y)-v)

is minimized over v<=u(a) at v=u(a); this follows by
differentiating the real quotient, or by cross multiplication
of its positive denominators. By the mean value theorem
applied to the exponential on [a,y],

    (u(x_0)-u(a))/(u(y)-u(a))
      >= exp(-pi V (y-a)) (x_0-a)/(y-a)
      >= exp(-pi V)/2.

The last inequality uses y-a<=2m and y-a<=|T|<=1.
The left derivative summand has prefactor u(y)/u(x_0)>=1.
Squaring the ratio of denominators, multiplying by this
prefactor, and integrating the positive measure gives (3).
This reasoning also covers a measure atom at the chart endpoint;
all integration points considered for the derivative are interior.
No nonzero angular lower bound on m was used.

## 3. No-fixed-point compression theorem

**Theorem.** Let E be any nonempty proper real interval contained
in one terminal limb BL_i, b+2<=i<=q-b-1. Set

    A=|H(E)|/|E|.

If A>24 exp(3pi V), then H'(y)>1 for every point strictly to the
right of E in T.

**Proof.** Apply the directional positive-kernel lemma to the
average A. If the right part has average at least A/2 on E, (2)
immediately gives H'(y)>=A/2>1 at every such point.

Otherwise the left part has average at least A/2. Take
x_0=x_i, the actual beginning cut of the limb containing E.
It is interior to T since i>=b+2. By (2) and averaging on E,

    h_L(x_0)>=exp(-pi V) A/2.

Set m=x_0-a. The preceding whole terminal limb BL_(i-1) lies
between a and x_0, so

    m>=L_(i-1)=x_0-H(x_0)>0.                     (4)

For x_0<=y<=x_0+m in T, (3) gives

    H'(y)>=h_L(y)>= A exp(-3pi V)/8 > 3.         (5)

If z-x_0>=m, take y=x_0+3m/4, strictly inside T.
Integration of (5), the actual cut shift and (4) give

    H(y)-y > H(x_0)-x_0 + 2*(3m/4)
           >= -m+3m/2 = m/2 > 0.

This contradicts (1). Hence z-x_0<m. But then every y in
[x_0,z) lies in the interval on which (5) holds.
In particular H'(y)>1 for every point to the right of E.
This proves the theorem in both cases. QED.

The statement is not that H' is globally bounded. Large
compression near a terminal boundary is possible; the theorem
says it forces large compression all the way to the remaining
right end, given the no-fixed-point shift and the presence of
the preceding full limb in the left margin. The numerical
constant 24 is conservative. This proof does not need a
small absolute angular margin or an estimate of either
limb angular size in terms of the renormalization width.

## 4. Absolute gap bound, retaining genuine subdivisions

Take c>=2b+20, h=b+2, H_0=h+2, t=H_0+2=b+6 and
q>=2(c+t)+4. Use

    B=BL_[-c,c], B^+=BL_[-c,c+t],
    Delta_+=M_+-M_B

with the anchored suprema from ASYMMETRIC_BANK_GAP.
Let ell_B and ell_+ be the respective minimum actual
marking atom lengths. If ell_B=ell_+, the angular envelope
immediately gives Delta_+<=C_env.

Otherwise choose an actual minimizing atom A_* in BL_(c+r),
1<=r<=t. Let I_0 be its actual whole old original atom ancestor
in BL_c, and I_j the entire proper marked forward image of I_(j-1),
j=1,...,r. These intervals exist by the exact proper refinement
and actual chart hypotheses, and I_r contains A_*.
Use

    S=|I_r|/ell_+,
    A_j=|I_(j-1)|/|I_j|,   A=max_j A_j.

The previous product inequality gives

    ell_B/ell_+ <= S A^r.

If A>24 exp(3pi V), choose j_* realizing A and apply the
no-fixed-point compression theorem to E=I_(j_*).
Its limb is BL_(c+j_*), strictly beyond b+1. H(I_(j_*))
is precisely I_(j_*-1), so its average derivative is A.
Every proper marked forward image of a whole atom in the
limbs after BL_(c+j_*) is contracted in angular length:
H'>1 on each such target interval, so integration gives
a strictly larger old angular length than the target length.

In particular the actual forward image of A_* in the next
noncritical limb has length <ell_+. Choose one whole
constituent target atom of that interval and repeat. All
target intervals used remain strictly to the right of E.
The proper-middle run allows the final target limb q-b-1.
Its selected atom belongs to B and has length <ell_+,
contradicting the definition of ell_B>ell_+.

Thus A<=24 exp(3pi V). The exact clipped angular-envelope
comparison, weakened to its unclipped ratio, yields

    Delta_+ <= C_env + (log S)/pi
                       + t*(3V+log(24)/pi).    (6)

This supersedes the need to estimate G or the whole-limb
compression Q_c in the preceding certificates. Genuine
subdivisions, if any, are still accounted by S. Nothing
in this step infers exact atom-to-atom ancestry just from
the proper boundary homeomorphism.

## 5. A bounded constant-marking plateau eliminates S

The earlier graph-side ancestry note supplied sufficient
hypotheses for S=1 everywhere on the proper corridor.
For the present application it is enough to find **one**
bounded interval of limbs on which the number of actual
marking atoms is constant.

Let n_j be the number of original marking atoms in BL_j.
Retain the source occupancy consequence

    1<=n_j<=6b.

Under the actual geometric proper refinement, each old
atom in a proper-middle limb has a nonempty image which
is a union of whole target atoms; these images have
disjoint interiors and together cover the target limb
(up to their marking cuts). It follows that

    n_(j+1)>=n_j   (b<=j<=q-b-2).

If equality holds, each of the n_j old atoms contributes
exactly one whole target atom. This is just a partition
count: each contributes at least one, and the sum of the
contributions is exactly n_(j+1)=n_j. No angular size
or numerical distortion hypothesis is needed for this
atom-to-atom conclusion.

Set

    c_0=2b+20,
    t=b+6,
    c_max=c_0+(6b-1)*t,
    Q_b=2*(c_0+6b*t)+4.

Assume q>=Q_b. Consider 6b disjoint windows of transitions
of length t, beginning at

    c_i=c_0+i*t,   i=0,...,6b-1.

All these transitions lie in the proper-middle range.
Over their entire union the nondecreasing integer
atom count, bounded by 6b, can have at most 6b-1
strict increases. Consequently at least one of
the windows has no strict increase. Choose the
first such window and put c=c_i.

On every one-step transition from BL_c through
BL_(c+t), old atoms map to single whole target atoms,
by equality of the counts. Hence for any new
minimum atom of B^+ outside B, the ancestor chain
in section 4 is atom-to-atom and S=1 exactly.
This is an actual marking count argument under
the exact proper refinement, not a numerical
assertion about the widths of the atoms.
It does not require that all other proper limbs
have constant marking count, nor the additional
whole-body graph homeomorphism certificate of
PROPER_MIDDLE_ATOM_ANCESTRY for arbitrary cuts.

By (6) we now have the uniform bound

    Delta_+ <= C_env + t*(3V+log(24)/pi).       (7)

The choice of c is among finitely many b-dependent
possibilities. Although the earlier deficit-program
constants depend on c, taking their maximum over
this finite list gives a constant depending only
on b. Unlike trying to choose c arbitrarily large
to absorb a relative gap, the estimate (7) is
absolute at scale V+1, so no circular choice
of deficit tolerance occurs.

## 6. Conditional gap-free source-width theorem

Retain the full analytic and geometric hypotheses of the
preceding anchored nonshort, guard-free short and local-bank
programs. The following is the exact dependency list for
this combined result; (7) is the new quantitative input.

* Actual canonical finite Kahn towers, annular covering
  degrees, filled-graph and occurrence compatibility,
  and the Borel/finite-energy path realization used in
  CANONICAL_LIFT_AND_DIRECTION, COHERENT_PACKET_GAIN and
  EXCEPTIONAL_WIDTH_REDUCTION.
* Exact corrected geometric contour-collapse action
  (not the unrestricted literal maximal-subset A.3.2),
  whole-atom fine refinement, actual old-proper first
  and last end-fine atoms, limb order and dividing-cut
  locality, and the entire proper middle chart with
  its actual commuting-square full-iterate realization.
* Actual saturated minimal carrier/host realization,
  critical-vertex deck pair, parabolic critical image
  bank, coherent suffix anchors, selected deep inverse
  hull exclusion and two-bank host/fine-side separation
  used in SUFFIX_ANCHOR_RESPONSE and AUXILIARY_GAP_RESPONSE.
  The two actual separator hits are charged at <=4R
  by the variable-end cyclic width estimate.
* The exact deterministic marked-interval action and
  eventual saturation (no proper interval repeats),
  with the nondecreasing proper atom count and the
  bound of 6b original marking atoms per limb.
* The actual source input is a finite-width Borel
  lamination of embedded proper marked inner-ended
  paths decomposed into at most k localized modules
  and one module whose leaves individually crest over
  the entire critical limb BL_0. The localized modules
  have one common original ending atom each. A purely
  aggregate over-critical crest does not certify
  this leafwise input typing.

Write R=W(RF), V=W(U minus T), as in all the preceding
notes. Assume the high-type bound q>=Q_b and the
primitive and selected-depth conditions in the
nonshort argument. In particular the high-q
suffix case has h+1<q<=P (P is the primitive cycle
period). No singleton/unbreakability hypothesis is
imposed, and the arbitrary multi-packet phase
selection deficit is not part of this route.

**Conditional theorem.** There is a finite C_(b,k)>0,
depending only on b,k, such that

    W(A) <= C_(b,k) (R+V+1).                   (8)

**Proof.** Choose the bounded bank radius c by
section 5. ASYMMETRIC_BANK_GAP section 1 (the
local nonshort charge, local short propagation
and guard-free angular jump) gives

    M_+ <= C_(b,c) (R+V+1+Delta_+).

That proof was for c=2b+20 but its estimates hold
for every larger fixed c with the stated
q>=2(c+t)+4: the actual primary anchor bank
remains BL_[-c,c+H_0], the far-corridor median
auxiliary boundary images are BL_(c+2) and
BL_(q-c), the two-bank and suffix probes are
within the original bounded positive bank, and
the short macro-stage bound is
(12b(18b-1)+2)(2c+16). All constants can
therefore be taken at the finite list of
possible c (or its upper bound). The exact
comparison cap here is M_+ for the chosen map
and bank, not a global anchored maximum.

In more detail the prior local nonshort estimate
bounds the nonshort fraction by the absolute
error and a square-root series response against
the whole common-primary width. Removing that
part leaves a short common-crest packet. The
proper first/last signed probes propagate the
whole common interval or charge saturation using
a fixed outside old atom. The guard-free long
jump replaces a short packet by an actual radial
one over the entire proper translated crest
with loss <=40(V+1). Its adaptive destination
is in the negative bank B. The no-repeat and
finite atom count bound the number of critical
visits; thus there is the finite deficit
program and the explicit backward tolerance
argument in LOCAL_BANK_CAP. This comparison
needs only the absolute budget including
2 Delta_+, not provenance of every old leaf
through the long jump.

Substitute (7) in that budget, obtaining
M_+<=C'_b(R+V+1) after taking the maximum of
the finite b-dependent constants. In particular
M_B<=M_+ has the same bound.

For the actual initial input, LOCAL_BANK_CAP
section 5 gives the independent one-sided
localized comparison

    W(A) <= (6k+1) M_B+80k(V+1)+1/2.

It remains valid for the enlarged c:
a common adjacent crest atom outside B lies in
the proper middle range, its old localized end
lies within the four-limb inner band, and its
adaptive terminal image and both padding limbs
lie in B. If the relevant padding is small,
its own near-bank radial witness is capped by
M_B; this gives the factor-three directional
estimate in that note. A leafwise whole-critical
module itself is anchored in B. The essential
equal-end loop discard costs <=1/2, and the
point-cut exceptions have zero width.
The finitely many directional packet widths
are charged by subadditivity on the actual
input, with no assembly of their overlapping
covering images.

Combining yields (8), independent of q,P and the
particular map, under the listed hypotheses. QED.

### Explicit vertical-width consequence

For any L>0, if R>=1 and a proof-used actual
initial Wave of the stated typing has

    W(A) >= C_(b,k)(L+2) R,

then (8) gives

    V >= W(A)/C_(b,k)-R-1 >= L R.

With the actual source monotonicity
W(F)>=V (recorded in the locked source lines
1173--1175 and the occupancy/Section-4 audits),
this is the L-amplification inequality
W(F)>=L W(RF).
This is a conditional sufficient initial-width
criterion. It does not establish that the
source's trichotomy supplies the required
actual Wave and absolute width scale without
the listed native and source-witness hypotheses.
No claim is made here about arbitrary virtual
Julia sets or other combinatorial regimes.

## 7. Disposition and proof audit targets

The former scalar obstacles of this conditional route
are now discharged:

* unrelated-crest phase selection is bypassed by the
  anchored and then local-bank comparison class;
* the long proper-middle jump uses guard-free
  one-sided angular width replacement;
* the global remote maximizer is unnecessary for
  the actual localized input comparison;
* the finite local bank expansion gap is bounded
  at scale O_b(V+1) by the no-fixed-point kernel
  argument and constant-count plateau.

What remains is substantive **native geometric
and source verification**, not a numerical
estimate of the angular margin: the actual
corrected contour marking and exact old-proper
chart, fine end-atom and full-tower correspondence,
physical host/selected-deep separator realization,
and the actual input Wave typing and downstream
source use. The earlier literal A.3.2
counterexample is not repaired by simply
renaming the action. The entire chain of written
modulus and topological arguments also requires
independent specialist review.

The new derivative proof uses the old and new
angular coordinates on the same X and the exact
strict reverse shift (1). This should be a
priority check in any native application.
Without that identity the directional lemma
alone does not yield (7). Similarly the
plateau proof uses actual disjoint complete
whole-atom images and the finite per-limb count;
a synthetic count model or forward-invariant
cut labels are not sufficient.

The companion finite checker tests the exact
positive-kernel ratio, no-fixed-point inequality,
plateau combinatorics, gap budget and amplification
arithmetic. Finite arithmetic and the new Lean
declarations certify only these implications,
not the holomorphic or native geometric
hypotheses. Main and the canonical proof-
obligation ledger are not promoted. AI-assisted
research; independent specialist review pending.

# Near-critical auxiliary packet control and the end-atom direction criterion

Continuation of [AUXILIARY_GAP_RESPONSE.md](AUXILIARY_GAP_RESPONSE.md),
[COHERENT_PACKET_GAIN.md](COHERENT_PACKET_GAIN.md), and
[CANONICAL_LIFT_AND_DIRECTION.md](CANONICAL_LIFT_AND_DIRECTION.md).
This is a conditional written geometric argument, not a new Lean theorem
or a claim of native stationary closure.

## 1. Source and standing conditions

The public v1 PDF of Kahn–Kapiamba–Lyubich, arXiv:2606.27272, is
available through [this mirror](https://pdfs.assets.alphaxiv.org/2606.27272v1.pdf).
The relevant printed pages are 12–13 (limb rotation and tree model),
23 (Lemma 4.8, at most 6b atoms per limb), 39–40 (controllable Waves
and terminality), 43 (Propositions 6.6–6.7), 46 (controllability
argument), and 56–57 (Appendix A.1, marked paths and Waves).
In particular the full circle is an allowed multi-interval in A.1.
A localized Wave is specified by a common endpoint atom, not by
a common crest. Controllability means a decomposition into a Wave
over BL_0 and a bounded number of localized Waves.

Throughout use the repaired geometric marking and actual proper
simple crosscuts with disk-side caps; do not infer these from the
literal unrestricted set operation of A.3.2. Retain the complete-lift,
saturated host/fine-side realization, and selected deep carrier
contact hypotheses of AUXILIARY_GAP_RESPONSE. Set h=b+2<min(q,P),
d=2^h, with the native rotation 1/q and q>=4. Marking-cut endpoints
of actual lifted paths can be removed at zero width: there are
finitely many cuts for each fixed map and horizon, and the point
singularity metric and immersion pushforward of
EXCEPTIONAL_WIDTH_REDUCTION apply. No uniform count of all cuts
is necessary for this zero-width removal.

## 2. The separator anchors are in a bounded near-critical bank

For n=b,b+1 the full pulled separator J_n=Gamma_h(Q_n) maps
under P_h to the little Julia set K_(h-n), respectively K_2,K_1
(the predecessor-bank identification in VARIABLE_END_EXIT_TRANSFER).
K_1 contains the critical value, so by the native limb placement
it is in Omega_1; K_2 is in Omega_2 by the noncritical rotation.
Here and below the actual contour/marking identification is
required: an anchor fine atom on J_n maps to an original marking
atom in BL_1 or BL_2. This is the same fine-side realization
required to construct the auxiliary packets, not an assertion
about an arbitrary model label.

Let L be the consecutive bank BL_0, BL_1, BL_2, with the
intervening cuts. It contains at most 18b original atoms. There
are at most N_b=12b*2^h fine anchors for the two separators, as
in the preceding gap-response note.

## 3. Packet controllability lemma

Suppose a packet consists of actual simple proper inner-to-inner
crosscuts after the fixed-anchor confinement of COHERENT_PACKET_GAIN.
In the target normalized cylinder the cap bases lie in the open
angular interval of radius 1/4 about the fixed anchor a: this follows
from scaling the source half-disk radius 1/(4d) by d in the covering
coordinates. Every cap base contains the whole target anchor atom
A in BL_1 or BL_2 strictly between its endpoints. The endpoints
are in atoms different from A. Such crosscuts satisfy the fine
marked-path condition: with distinct endpoint atoms the base
traverses at least three atoms; with the same endpoint atom it
takes the long way around the circle through the other atoms.
This uses the actual oriented homotopy class, not only the
endpoint labels.

**Claim.** Each such disjoint Borel packet is itself an actual
(18b+1)-controllable Wave (on the ordered-cap geometric reading
of the native definitions).

Proof. First it is a Wave subordinate to the full circle, which
is an allowed marked multi-interval. To obtain a proper common
base for the nonlocalized part, choose the antipode y=a+1/2
on the target circle. It is outside every actual cap base.
If y lies inside an atom H, allocate all leaves with an endpoint
in H to one localized module. This includes the long same-atom
case when the complementary gap contains y inside the endpoint
atom. For the remaining leaves neither endpoint is in H; since
the cap base is a connected arc avoiding y, it cannot intersect
the closure of H. Thus the remaining packet is subordinate
to a single proper connected marked multi-interval (the
complement of the closed H, allowing the usual marking endpoint
convention). If y is a marking cut, all leaves are already
subordinate to the circle punctured at that cut.

Next allocate leaves having an endpoint in L to their first
eligible bank atom in a fixed ordering, one localized module
per atom. This costs at most 18b modules. Every remaining leaf
has both endpoint atoms outside L. Its oriented cap base
contains A; because L is a connected consecutive bank and its
endpoints are outside L, the base must traverse all of L,
including all of BL_0 strictly between its endpoint atoms.

In the common proper base obtained by cutting at y (or removing
H), the remaining endpoint atoms therefore lie on the two
opposite sides of BL_0. Their ordered end hulls are disjoint
from BL_0, and their marked base hull contains BL_0 between
these hulls. Consequently the remaining packet is one Wave
over BL_0, including in the aggregate rather than merely
leafwise sense. This is the ordinary ordered-cap interpretation
of base, ends and crest on a proper marked interval; it avoids
the ambiguous crest of an arbitrary full-circle packet.
The classes are disjoint and Borel by the finite endpoint
predicates. If any class is empty, omit it. This proves the
claim.

In particular, no bound on the number of possible remote
ending atoms is required, and no lower bound on an angular
length of an old side is used. Nor do the auxiliary leaves
need to be retained at earlier coarse filters. With the native
full-circle convention the single H-module is legitimate
even when its aggregate base is the circle. A stricter
non-native definition requiring every localized module to
have a proper base would need an additional argument there.

## 4. Consequence for the series response

The containers required in AUXILIARY_GAP_RESPONSE, section 3,
can now be the N<=N_b actual packets themselves. Their
controllability constant is at most 18b+1. This discharges
the *separate* uniform auxiliary output-controllability
hypothesis, conditional on the existing gap realization and
fine-side hypotheses. If the final primary packet is a Wave
ending at BL_0, the usual endpoint-atom partition makes it
6b-controllable; otherwise retain its actual container
hypothesis from COHERENT_PACKET_GAIN. Use a terminal class
that includes these controllability constants.

Let W=W(A)>0 be finite, R the local renormalization width,
V the vertical width, E=2^h V+h C_2, and
C_d=pi log(16d)/(log 2)^2. Write D for the width of the
parents without actual selected deep carrier contact at
the stated horizon, not a symbolic endpoint label.
The family with both physical bank hits has width <=4R
by the two degree-two peripheral components and the exit
charge of VARIABLE_END_EXIT_TRANSFER. This safe bound
does not require the sharper both-end graph bound.
Remove the primary discard, missing-contact family, two-hit
family, and at most N_b C_d of auxiliary chart failures.
The good parents with an auxiliary have width w satisfying

    w >= W-E-D-4R-N_b C_d.

Here all subfamilies are taken on the actual measurable
realization of the earlier notes; subadditivity suffices
for the deletion inequality. Write N=N_b (padding empty
containers if necessary). If no relevant controllable
output exceeds (1+lambda)W, the sum B of the auxiliary
container widths is at most N(1+lambda)W. The series law
and primary good width give

    W(C) >= W-E+w^2/B,
    w^2 <= N(1+lambda) W (lambda W+E).

The B=0 case forces w=0 and satisfies the latter inequality;
an infinite-width relevant output already violates finite
near-maximality. Thus necessarily

    D >= W-E-4R-N C_d
           -W sqrt(N(1+lambda)(lambda+E/W)).

A negative right side is simply vacuous. As one explicit
strict-response regime, set lambda=1/(64N), suppose
E<=W/(64N), and D+4R+N C_d+E<=W/2. Then w>=W/2 and
B<=2NW; hence W(C)>=W+7W/(64N)>(1+lambda)W, unless
an auxiliary output already gives a strict response.

This makes the remaining missing-contact mass quantitative.
It is not an unconditional native terminality theorem:
the actual corrected marking, directed primary chain,
selected deep contact, host/fine-side construction, and
relative telescope still require verification.

## 5. An end-atom weakening of protected-crest direction

There is also a way to weaken the protected-block
hypothesis of CANONICAL_LIFT_AND_DIRECTION section 4.
The native Proposition 6.6 (printed p.43) asserts that
the end fine atoms of a coarse pulled atom are in the
proper old-boundary inverse. Use the following precise
geometric hypothesis, rather than the disputed unrestricted
set operation: a coarse pulled atom I over an actual old
crest atom has a first fine atom E whose inner accesses
map properly to that old crest atom. E may be all of I.
The coarse/fine markings are finite cyclic partitions, the
coarse atom is proper, and there are at least three fine
atoms. Assume the same actual completed lifted simple
parent, old filled-cap embedding, raw-gap exhaustion,
and singleton simple retained output as in the earlier
protected-crest direction argument.

No raw endpoint can lie in E: at an interior parent time
its proper old-boundary image would be on T, while the
actual parent avoids T; at an original endpoint its old
access would be in the strict old crest rather than an
ending atom. Remove endpoints at marking cuts at zero
width as before. Choose e in E. A proper end-tail there
is on the old lifted disk-cap side, because its old ideal
image is in the strict old crest. The embedded old collar
and filled-cap embedding identify this side. Truncate the
tail so it avoids the completed lifted parent.

Every raw disk-side cap containing e now contains E
strictly between its endpoint atoms. It satisfies the
fine path condition by the same three-atom/long-class
argument above. It also cannot be subordinate to just
one coarse atom: the only candidate coarse atom is I,
and a proper cap contained in I cannot contain its
first fine atom E strictly between endpoints outside E.
A cap going around the circle is not subordinate to I
either. Thus every raw gap counted at e passes both
marking filters. The singleton simple retained output
and the disjointness of distinct covering lifts of its
cap imply there is at most one such raw cap over e.
The signed-crossing identity of the previous protected-
crest proof gives signed sum 1 at this tail: there is
exactly one such raw cap and its orientation agrees
with the old disk-cap orientation.

Unlike the unchanged-whole-coarse-block criterion,
this only needs one end fine atom and its actual proper
old-side property. It may therefore apply when much of
the coarse atom contains newly attached carrier. It is
still conditional on the geometric interpretation and
the stated actual end-proper property; it is not a proof
of the literal A.3.2 marking action.

## 6. Verification and remaining target

The accompanying check_near_critical_packet.py exhausts
finite cyclic bank, antipodal cut (including long same-atom
classes), and end-atom configurations. It checks the
discrete implications used here, not the analytic
confinement, native proper-access correspondence, modulus
or stationary closure. No new Lean theorem is claimed.

The next geometric target is actual selected deep contact
of large width under the repaired stationary direction.
The result above shows that once those contacts and
their host/fine-side gaps are realized, arbitrary remote
auxiliary endpoint atoms no longer obstruct a uniformly
controllable strict response. A separate possible route
is to propagate an actual old-side anchor coherently
through the complete tower and use the critical-block
saturation to exclude precritical inverse origins at
each suffix; this requires proof of anchor coherence
and full-tower contour locality and is not asserted here.

No promotion of the canonical proof ledger, general MLC,
or full stationary closure is made. Human specialist
review remains necessary. AI-assisted research.

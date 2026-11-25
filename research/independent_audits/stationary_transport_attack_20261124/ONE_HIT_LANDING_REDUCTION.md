# One interior bank hit plus a landing endpoint

2026-11-25. Conditional written extension of the finite-time exit
argument in [the exit-transfer note](../maximal_exit_transfer_20261123/NOTE.md),
Section 6, and the variable-bank bound in
[VARIABLE_END_EXIT_TRANSFER.md](VARIABLE_END_EXIT_TRANSFER.md).
This note does not construct retained stationary Waves or prove their
actual landing endpoints. The source's open obligation statuses remain
unchanged.

## 1. A one-hit exit theorem

Use the notation and hypotheses of Theorem 6.4 of the exit-transfer
note: hyperbolic conformal disks S,U; a holomorphic immersion i:S→U;
compact filled sets C,K with i⁻¹(K)=C and i|C a homeomorphism onto K;
a finite collection H of pairwise disjoint nondegenerate full continua
contained in C and compactly contained in S; and Xf=S minus their union.
An embedded parent α:(0,1)→U hits i(Q) at an interior time u,
for Q in H. Here compact containment in S is all that is needed for
the deleted continua; no interior of C is required.

Suppose, after possibly reversing the parent parameter, that either:

(A) α(t) tends as t→1 to an actual physical point y in i(Hj), for
some Hj≠Q; or

(B) in a Riemann map ψ:U→D, ψ(α(t)) tends as t→1 to a point
of the unit circle.

Then a maximal ideal-proper restriction in Xf joins the Q-circle to
a different ideal component. The endpoint in (A) is a physical limit,
not merely a prime-end impression meeting i(Hj). Case (B) concerns
the ambient outer ideal boundary, not an inner ideal circle of a
carrier complement.

### Proof

Start the unique local unpunctured lift σ at the canonical preimage
of α(u) in Q, and continue to the right on its maximal lifetime
[u,b), where u<b≤1.

If the lift hits any deleted continuum other than Q before b, choose
a first such hit on a compact segment from u to that hit. The last Q
hit before it and the first other-continuum hit give an ideal-proper
inner-to-inner exit by Lemma 6.1 of the cited note.

Assume henceforth that no such interior hit occurs. If b<1,
Lemma 6.3 gives compact escape and a single outer ideal limit.
Suppose b=1. In case (A), any interior accumulation point x of σ
satisfies i(x)=y. The full inverse identity and injectivity on C
force x to be the canonical preimage of y in Hj. A local inverse
chart at x contains a late lift point; because α(t)→y, the whole
subsequent parent tail lies in the target chart. Uniqueness of path
lifting identifies the lift tail with the inverse-chart tail, which
converges to x. Thus the lift extends continuously to t=1. Its last
Q hit a exists and is strictly before 1, since Hj is compact and
disjoint from Q. The segment σ((a,1)) avoids every deleted continuum.
Both endpoint tails are Jordan end-cuts: injectivity in the interior
follows from injectivity of α, and the terminal point in Hj was not
visited previously under the no-other-hit assumption. The initial
endpoint is in Q and is not revisited after a. The Koebe argument
in Section 6.1 gives two distinct ideal limits. Neither tail can
extend in Xf.

Otherwise (A) has no interior accumulation point; in (B) an interior
accumulation point is impossible because ψ∘i is disk-valued but
ψ∘α tends to the unit circle. Hence σ escapes every compact of S.
Choose a Riemann map φ:S→D. The disk-valued nonconstant bounded
holomorphic function h=ψ∘i∘φ⁻¹ has
h(φ(σ(t)))=ψ(α(t)) convergent. The limit is interior in (A) and on
the unit circle in (B). The proof of Lemma 6.2 (Fatou and boundary
uniqueness) applies to either complex limit, and gives a unique
outer ideal limit for φ∘σ. Compact escape means the Q-hit times
are bounded away from b; take their last time a. By the no-other-hit
assumption σ((a,b)) lies in Xf. Its initial tail is a Jordan end-cut
at Q, and its terminal tail converges to the outer ideal circle.
The compactness of all deleted continua makes the outer collar of
Xf identical to the outer collar of S. Neither end extends inside
Xf, proving maximality and properness.

In all cases maximality is in the actual lifted trace of this
parent, using the maximal component/path lifting correspondence of
Section 2.2 of the cited note. No assertion of injectivity of i on
all of S is needed. QED.

## 2. Application to the actual predecessor bank

Write K_j for the original primitive small-Julia cycle of period P,
and Q_n for the canonical n-step selected predecessor of K_0 in the
critical limb. Use the selected-predecessor recursion and distinctness
proved in [the N2 predecessor note](../../mlc_unified/kkl_stationary_n2_selected_predecessor_endpoint.md),
Sections 2 and 5. Suppose each limb contains at most b cycle members.
For b≤n<P, Q_n is disjoint from the entire original cycle.

Indeed, if K_j meets Q_n then F^n(K_j) meets K_0, so F^n(K_j)=K_0
by pairwise disjointness of the cycle. The connected K_j is contained
in a single component of the full inverse of K_0, namely Q_n,
since it meets Q_n. The selected recursion, or successively the
whole inverse components, gives F^k(K_j)⊂Q_(n−k) for 0≤k≤n.
These n+1 original cycle members are distinct because n<P and all
are in the critical limb, contradicting n+1>b.

At a final horizon m=b+r<P, 2≤r<P, let the bank consist of the
actual graph lifts Qhat_n, b≤n<m, of the variable-end note,
Corollary 5.3. The full filled-graph identity and forward invariance
of the original cycle place each Γ_m(K_j) in a component of the final
pulled small-Julia cycle. That component differs from every bank
member by the preceding disjointness. Thus a parent which physically
hits any one bank image and has an actual physical landing endpoint
on any original K_j satisfies case (A) in Section 1. A parent with a
genuine ambient outer ideal endpoint satisfies (B) instead.

For a Borel parent family, if each parent satisfies this new
criterion, the existing countable Borel least-code selection chooses
one eligible exit. The finite endpoint-cover inequality then yields
W(A_m)≤2r W(RF). The same conclusion holds for a family where the
criterion fails only on a separately proved Borel width-zero
subfamily. One fixed degree-two bank member suffices for the
stronger bound 2 W(RF).

The high-type application uses m<P (for example q>m and P≥q).
This does not assert that every stationary parent has an endpoint
on the original little Julia cycle or the outer ambient circle.
In particular, a prime end of U minus the full carrier may have a
non-singleton impression or land on a carrier edge outside the
original cycle. Neither circumstance meets (A) or (B) merely by
its name.

## 3. Why one hit alone cannot suffice

An explicit planar model falsifies the inference from a single
bank hit and parent properness in a full-carrier complement alone.
Take S=U={z:|z|<5}, i the identity, C=K the closed disk of radius
4. The deleted continua are Q={|z|≤1/2} and Hj={|z−3|≤1/4}.
Let the original full carrier T be Hj together with the polygonal
arc through (−1,0),(−1,1),(1,1),(1,0), and the attached branch
from (1,1) to (3,1) to (3,1/4). T is a compact full continuum,
disjoint from Q; the tree branches attached to the disk do not
enclose a bounded complementary domain.

The simple parent is the straight open segment from (−1,0) to
(1,0), proper in U\T with two carrier landing endpoints. It hits Q,
but not Hj. Its two maximal restrictions in Xf are the segments
(−1,−1/2) and (1/2,1) on the real axis. Their endpoints at ±1 lie
in the interior of Xf. Neither restriction is ideal-proper. This
example is not a quadratic dynamical or KKL counterexample; it
shows that mere carrier-endpoint properness cannot replace a
genuine final ideal-end condition.

## 4. Remaining native obligation

For each retained parent, establish either two actual hits as
before, one bank hit with an eligible endpoint as above, or an
actual proper exit by another argument. Alternatively bound the
width of the exceptional family by a separate estimate. In
particular the one-hit reduction does not prove the avoidance-to-
two-Waves break argument, native retention, or the stationary
pass-through itself.

The argument is written mathematical reasoning using the previously
stated analytic inputs, not a Lean proof of ideal boundary behavior.
The associated Lean module handles only finite endpoint incidence
and conditional degree accounting. No novelty or human specialist
review is claimed. Prepared with ChatGPT assistance.

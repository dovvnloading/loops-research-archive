# Gate N1 — independent red-team certificate for Borel ordered Waves

## 0. Scope and status

This note audits only

```text
STANDARD_BOREL_ORDERED_WAVE_REALIZATION
```

as used by

```text
KKL_STATIONARY_RELATIVE_WAVE_CONTINUATION.
```

The audited draft is

```text
kkl_stationary_n1_borel_ordered_wave_realization_20260726.md
```

The final snapshot audited in this note is frozen at

```text
SHA-256
C9F1C7BD37FD192E047B13B79023B3A88AC3148A5A11C5A79EC52B349114D318
```

and the analytic continuation theorem is in

```text
kkl_stationary_relative_wave_continuation.md.
```

The audit is independent in the following sense: every descriptive-set
projection, topological order assertion, and occurrence quotient used by
the draft is rederived below.  A claim is not accepted merely because it
appears in the draft.

The present verdict is:

```text
planar nesting and area coordinate:                 passes
Borel sublevel identity:                            passes
Arsenin--Kunugui leaf-range argument:                passes
hyperspace initial-subarc parameterization:          passes
maximal-lift interval coding:                        passes after expansion
proper-escape predicate:                            passes
prime-end endpoint convergence:                     passes after adding a
                                                    separate Cauchy test
duplicate occurrence quotient:                      passes after adding
                                                    nonempty overlap
KKL marking filters:                                passes, subject only to
                                                    spelling out endpoint-
                                                    track invariance
unbreakability by raw occurrence count:              false
native unbreakable path-valued recursion:             passes
successor-to-terminal-leaf-space typing:              passes
DL outer-buffer measurability:                       open at exact chartwise
                                                    buffer convexity
equal-tail prime-end edge case:                      counterexample confirmed;
                                                    Borel circle repair proved
                                                    in Section 10
```

No ledger statement is promoted by this audit alone.  Gate N2, VAAPC-I,
UPTCR, rigidity, parameter fibers, and MLC remain open.

## 1. Locked sources

| source | SHA-256 |
|---|---|
| `.tmp_wave_audit/waves-with-Misha.tex` | `AD4C774806D9902AA54FA31C56AD6146D8034946F19CC5E9CEC3C51A3F94FDD5` |
| `.tmp_wave_audit/dl23/Feigen.tex` | `EB8C50CC51039A82317CF1951B1E333F23DF100773F8AD0DF0586AC7CD465DDF` |
| `.tmp_kl06_source/wad.tex` | `B5DF40A5D33B6B590B430D47693514088AF6FC287BAA5D87B4D11015B990E580` |

One source-reading interface must remain visible:

```text
ARC_CLASS_SUBLAMINATION_IS_PROPER_BOREL
```

For the first interface, KL06 `wad.tex` 142--150 defines a proper
lamination to have Borel geometric support, calls
\(\mathcal F(\alpha)\) a sublamination, and says in the accompanying
footnote that all laminations under consideration are proper.  KKL
1911 uses the same “sublamination” language.  The intended reading is
therefore that every \(\mathcal F(\alpha)\) again has Borel support.
The source does not spell out that conclusion as a separate theorem.
If an editor rejects the semantic force of “sublamination,” this
interface must remain an explicit hypothesis; Borelness of an
arbitrary union of equivalence classes does not follow from Borelness
of the total support.

The decomposition must be indexed by

\[
 \mathcal A(\mathcal F)
 :=
 \{\alpha:\mathcal F(\alpha)\ne\varnothing\},
\tag{1.1}
\]

not by the support of the induced weighted arc diagram.  A nonempty
arc-class packet can have extremal width zero and is then absent from
the weighted support.  KL06 145--147 says that the nonempty classes
form an arc diagram.  Their number is still finite in the stationary
finite-marked surface by the usual finite-topology bound for a
pairwise-disjoint arc diagram (equivalently, apply the KKL bound to
the auxiliary coefficient-one WAD supported on those classes).

The first draft of the ordered realization also assumed that every
leaf has two distinct ideal endpoints.  That assumption is false for
the printed KKL path class.  Section 10 gives both an explicit
counterexample and a Borel parameterization of the resulting
based-circle fibers, so distinct endpoints are no longer a required
interface.

## 2. Verification of the planar-order core

Fix a proper Borel arc-class packet \(P\) in the stationary annulus.
Every leaf is boundary-parallel on the same chosen side.  For a leaf
\(\gamma\), let \(O_\gamma\) be the open preferred-side domain.  If
the two projected ideal endpoints coincide, use the Jordan-circle
compactification from Section 10 and choose its side whose ideal
boundary trace contains the crest.  Thus \(O_\gamma\) is defined on
both the ordinary crosscut and based-circle strata.

### Proposition 2.1 (strict nesting)

For distinct leaves \(\gamma,\eta\in P\), exactly one of

\[
 O_\gamma\subsetneq O_\eta,
 \qquad
 O_\eta\subsetneq O_\gamma
\tag{2.1}
\]

holds, and the difference between the larger domain and the closure of
the smaller contains a nonempty open set.

### Proof

Lift the annulus so that the selected boundary-parallel arc class is
represented in one closed strip.  A based circle in the annulus lifts
to a crosscut whose two strip-boundary endpoints are distinct deck
lifts of the same projected prime end.  A based loop with zero deck
displacement would be subordinate to an arbitrarily short boundary
multi-interval and is not a KKL path; hence the proof-used equal-end
case has nonzero deck displacement.  Ordinary arc leaves already lift
to crosscuts with distinct ideal endpoints.  Choose the lifts so that
their preferred boundary intervals contain the same fixed lift of the
crest.

If neither preferred boundary interval contained the other, their
endpoint pairs would alternate in the boundary order.  Jordan
separation would force the two crosscuts to intersect.  If the
boundary intervals are nested but the corresponding disk-side domains
are not, one crosscut must enter and leave both complementary sides of
the other, again forcing an intersection.  Thus the domains are
nested.

Equality of the domains would make their interior crosscut boundaries
equal.  Since leaves in a lamination are disjoint and the two leaves
are distinct, equality is impossible.  The region between two
distinct disjoint crosscuts is open and nonempty. \(\square\)

Individual direction above \(J\) is not sufficient across arbitrary
arc classes.  In a disk collar, take two disjoint crosscuts from a
common ideal endpoint \(a\) to endpoints \(b,c\) lying on opposite
sides of \(J\).  Choose for each crosscut the boundary side containing
\(J\).  Each crosscut is individually above \(J\), but each preferred
domain contains the other crosscut; the domains overlap and neither is
contained in the other.

The statement needed by DL has the stronger collective Wave
hypothesis.

### Proposition 2.2 (common-Wave nesting)

Let \(P\) be a Borel Wave over a nondegenerate connected ideal interval
\(J\).  Then the \(J\)-side domains of all leaves of \(P\), including
leaves from different arc classes and based-circle leaves, are strictly
nested.

#### Proof

Let \(E^-,E^+\) be the two collective end multi-intervals of the Wave.
Since \(J\) lies in the crest, neither collective end can straddle
\(J\).  In the annular strip, choose lifts

\[
 \widetilde E^-,\quad
 \widetilde J,\quad
 \widetilde E^+
\]

in their boundary order and lift every leaf so that its endpoints lie
in the two selected end blocks and its preferred side contains
\(\widetilde J\).  The equal-projected-end case is again an ordinary
crosscut between distinct deck lifts.

For two leaves with four distinct lifted endpoints, nonnested
preferred boundary intervals would alternate, forcing the crosscuts to
meet.  If the leaves share one lifted ideal endpoint, their other
endpoints lie in the same end block, on one side of
\(\widetilde J\).  Their preferred boundary intervals are therefore
nested.  Equivalently, truncate a sufficiently small common-endpoint
collar: the two truncated disjoint crosscuts have four distinct
endpoints in the same nonalternating order, so the preceding argument
applies.  If both endpoint pairs agree, the two disjoint crosscuts
bound an open strip and are ordered by which one separates the other
from \(\widetilde J\).

Thus all selected lifted domains are nested.  Each downstairs
preferred component is a disk, so each chosen lift maps
homeomorphically to it.  Nesting and the nonempty open region between
distinct lifted crosscuts therefore project to strict nesting
downstairs. \(\square\)

Choose a finite full-support Borel measure \(\mu\) on the annulus and
put

\[
 t(\gamma)=\mu(O_\gamma).
\tag{2.2}
\]

Proposition 2.1 and full support imply

\[
 O_\gamma\subsetneq O_\eta
 \quad\Longrightarrow\quad
 t(\gamma)<t(\eta).
\tag{2.3}
\]

Thus \(t\) is an injective leaf coordinate.

## 3. Verification of the sublevel and projection arguments

Let \(Z_P\) be the Borel geometric support of \(P\), and define
\(t(x)=t(\gamma)\) on the leaf containing \(x\).

For rational \(r\), set

\[
 U_r=
 \bigcup_{\eta\in P,\ t(\eta)<r}O_\eta.
\tag{3.1}
\]

The set \(U_r\) is open.  If a leaf \(\gamma\) meets \(U_r\), then it
lies strictly inside some \(O_\eta\) with \(t(\eta)<r\), so
\(t(\gamma)<t(\eta)<r\).  Conversely, if
\(t(\gamma)<t(\eta)<r\), the interior of \(\gamma\) lies in
\(O_\eta\).

Consequently,

\[
 Z_P\cap U_r
\tag{3.2}
\]

is the union of all leaves with \(t<r\), except possibly the unique
leaf whose coordinate is

\[
 \max\bigl(t(P)\cap(-\infty,r)\bigr).
\tag{3.3}
\]

There is at most one exceptional leaf because \(t\) is injective.  A
proper leaf image is closed in the open annulus, hence Borel.  Therefore
\(\{t<r\}\) is Borel.  Rational sublevels prove that
\(t:Z_P\to\mathbb R\) is Borel.

Define

\[
 G=\{(s,x)\in\mathbb R\times V:x\in Z_P,\ t(x)=s\}.
\tag{3.4}
\]

This is Borel.  Every vertical section is empty or one proper leaf.
A proper leaf is homeomorphic to \(\mathbb R\), hence sigma-compact.
Arsenin--Kunugui therefore gives

\[
 L_P=\operatorname{proj}_{\mathbb R}G=t(P)
\tag{3.5}
\]

as a Borel subset of \(\mathbb R\).  No monotone-image theorem and no
pre-existing measurable quotient is being used.

## 4. Verification of the compact-arc parameterization

First consider the two-distinct-endpoint stratum.  Let \(K_s\) be the
prime-end closure of the leaf with coordinate \(s\).  Section 10
handles the equal-endpoint stratum.

The hyperspace hit predicate

\[
 K_s\cap W\ne\varnothing
\tag{4.1}
\]

for an open \(W\) is equivalent to the interior leaf meeting
\(W\cap V\).  The latter is the projection of a Borel set whose
vertical section is an open subset of a proper leaf and therefore
sigma-compact.  Arsenin--Kunugui proves that
\(s\mapsto K_s\) is Borel into the compact hyperspace.

For ordered endpoints \(a_s,b_s\), define \(y\preceq_s x\) when \(y\)
belongs to the initial subarc \(K_s[a_s,x]\).  Apart from \(y=x\), this
is equivalent to:

\[
 \exists m\ge1\ \exists C\in\mathcal K(\overline V^{\rm pe})
 \quad
 \begin{cases}
 C\text{ is connected},\\
 a_s,y\in C,\\
 C\subset K_s,\\
 d(C,x)\ge 1/m.
 \end{cases}
\tag{4.2}
\]

For fixed \((s,x,y,m)\), the section in \(C\) is compact.  The
connectedness, incidence, containment, and distance conditions are
Borel after substitution of the Borel compact field \(K_s\).
Arsenin--Kunugui makes the projection in (4.2) Borel.

Thus \((s,x)\mapsto K_s[a_s,x]\) is a Borel compact-valued field.
For a dense sequence \((q_n)\) in the ambient compactum, put

\[
 \Theta(C)=
 \sum_{n\ge1}2^{-n}\frac{1}{1+d(q_n,C)}.
\tag{4.3}
\]

This is continuous in the Hausdorff topology.  If
\(C\subsetneq D\), choose \(z\in D\setminus C\).  Since \(C\) is
compact,

\[
 \varepsilon=d(z,C)>0.
\]

For \(q_n\) sufficiently close to \(z\),

\[
 d(q_n,D)<d(q_n,C),
\]

while every other summand in (4.3) is nondecreasing.  Hence
\(\Theta(C)<\Theta(D)\).

It follows that

\[
 u_s(x)=
 \frac{\Theta(K_s[a_s,x])-\Theta(\{a_s\})}
 {\Theta(K_s)-\Theta(\{a_s\})}
\tag{4.4}
\]

is Borel in \((s,x)\), continuous and strictly increasing on each
arc, and maps the endpoints to \(0,1\).  Its singleton-valued inverse
graph is Borel, so Lusin--Novikov supplies a jointly Borel evaluation
\(e(s,r)\).  This part of the draft is valid.

## 5. Exact maximal-lift occurrence calculus

Let \(e:L\times(0,1)\to V\) be the Borel evaluation just obtained and
let \(\iota:V'\to V\) be a holomorphic immersion.

### 5.1 Germs and maximal intervals

Choose a countable inverse-branch atlas.  A germ is coded by a source
leaf \(\ell\), a rational time \(q\), an enumerated point
\(z'\in\iota^{-1}(e(\ell,q))\), and an inverse-chart index.  Fibers of
an immersion are discrete; in a second-countable surface they are
countable.  Lusin--Novikov gives the required Borel enumeration.

Existence of continuation from \(q\) over a fixed compact rational
interval is a countable union of finite compatible inverse-chart
words, hence Borel.  Therefore the endpoints of the maximal
continuation interval

\[
 I_\omega=(a_\omega,b_\omega)
\tag{5.1}
\]

are Borel extended-real functions obtained as the infimum and supremum
of reachable rational times.  Evaluation at rational times is Borel.
Fiberwise continuity then makes the reparametrized full evaluation
jointly Borel.

### 5.2 Properness

After reparametrizing \(I_\omega\) by \((0,1)\), fix a compact
exhaustion

\[
 K_m'\subset\operatorname{int}K_{m+1}',
 \qquad
 \bigcup_mK_m'=V'.
\]

The lift is proper exactly when

\[
 \forall m\ \exists N,k\ \forall
 r\in
 \bigl((0,1/N)\cup(1-1/N,1)\bigr)\cap\mathbb Q:
 \quad
 d(\widetilde\gamma_\omega(r),K_m')\ge1/k.
\tag{5.2}
\]

If the lift is proper, its tails eventually avoid \(K_{m+1}'\).
Compact containment \(K_m'\Subset K_{m+1}'\) then supplies a positive
distance from \(K_m'\).  Conversely, continuity extends (5.2) from
rational times to full tails, so the inverse image of \(K_m'\) is
closed and contained in a compact central parameter interval.  This
is exactly properness.

### 5.3 Prime-end convergence is separate

Properness does not imply convergence to a single prime end.  In a
complete metric on the compact prime-end annulus, require on each tail

\[
 \forall k\ \exists N\ \forall r,s\in(0,1/N)\cap\mathbb Q:
 d_{\rm pe}(\widetilde\gamma_\omega(r),
            \widetilde\gamma_\omega(s))<1/k,
\tag{5.3}
\]

and analogously near \(1\).  This is Borel, is equivalent by continuity
to the full-tail Cauchy property, and yields Borel endpoint maps as
pointwise limits.  Endpoint membership in the ideal boundary is then
a Borel condition.

### 5.4 Duplicate germ codes

The following rejected predicate is vacuous on disjoint intervals:

```text
the lifts agree at every rational time in their overlap.
```

The correct equivalence is:

\[
 I_\omega\cap I_{\omega'}\ne\varnothing
 \quad\text{and}\quad
 \exists r\in\mathbb Q\cap I_\omega\cap I_{\omega'}:
 \widetilde\gamma_\omega(r)
 =
 \widetilde\gamma_{\omega'}(r).
\tag{5.4}
\]

Uniqueness of path lifting then identifies the two maximal
continuations and their intervals.  Condition (5.4) is Borel and
permits selection of the lexicographically first countable germ code.

## 6. Borel realization of the two KKL filters

The phrase “finite-subordination predicate” is not a proof by itself.
The needed result is the following.

### Lemma 6.1 (marked-arc tag lemma)

Let \(M\) be a finite-topology surface with metrizable prime-end
compactification and a finite or countable ideal marking.  Let
\[
 h:P\times[0,1]\to\overline M^{\rm pe}
\]
be jointly Borel, with continuous compactified simple-path fibers and
interiors in \(M\).  Then:

1. the endpoint-interval pair is Borel;
2. the relative proper-homotopy tag is countable-valued and Borel; and
3. subordination to any fixed marked multi-interval is Borel.

#### Proof

The map

\[
 p\longmapsto h_p
\]

is Borel into
\(C([0,1],\overline M^{\rm pe})\): inverse images of basic uniform
balls are determined by the values on a fixed countable dense set,
using fiberwise continuity.

Fix two marking intervals \(I,J\).  Lift them to the universal cover.
Choose the initial endpoint lift in one fixed lift of \(I\).  The
terminal endpoint of the lifted path lies in one of the countably many
deck translates of a fixed lift of \(J\).  Path lifting depends
continuously on a path as long as the initial lift remains in a fixed
evenly covered chart.  Therefore the terminal deck label is locally
constant on each such chart and is Borel globally after a countable
chart decomposition.

The endpoint-interval pair together with the terminal deck label is
the relative proper-homotopy tag.  There are only countably many tags.
For a fixed marked multi-interval \(X\), the tags that admit
representatives in every collar neighborhood of \(X\) are a specified
subset of this countable tag set.  Its inverse image is Borel.
\(\square\)

Apply Lemma 6.1 to the compactified occurrence evaluation.  The fine
filter

```text
is a path in (V', I')
```

rejects precisely the Borel union of tags subordinate to a fine
multi-interval of combinatorial length at most two.  The coarse filter
rejects the Borel union of tags subordinate to one interval of
\(\iota^*\mathcal I\).  Thus both KKL filters are Borel.

The word “finite” should not replace this proof.  Even with finite
marking, annular deck or winding tags can be countable.

## 7. Untagged outputs and breakability

Raw occurrence count does not compute KKL breakability.

### Counterexample schema 7.1

One source leaf may have two distinct retained restriction
occurrences \(\beta_1,\beta_2\) with

\[
 f(\beta_1)=f(\beta_2).
\tag{7.1}
\]

There are two occurrences but one untagged output.  The source leaf is
unbreakable in the KKL sense.  This is not hypothetical bookkeeping:
the analytic N1 proof explicitly distinguishes occurrences from the
unique untagged successor.

Hence the predicate

```text
the retained occurrence section is a singleton
```

must not be used as the definition of unbreakability.

There are two safe repairs.

### Repair A (native-subwave route)

KKL already calls \(A^{h\text{-nbr}}\) a subwave.  Import its Borel
status through the same proper-sublamination convention and do not
reconstruct it by counting occurrences.  On this already unbreakable
domain, select the first Borel occurrence; every occurrence has the
same untagged output, so the selected pushforward represents
\(\Phi_1\).  Keep the normalized pushed path evaluation, not merely
its compact image, as the path code if another immersion restriction
must be taken.

More explicitly, let \(L_0\) be the standard-Borel leaf space of the
native proper subwave \(A^{h\text{-nbr}}\), with evaluation \(e_0\).
Inductively suppose that

\[
 e_j:L_0\times(0,1)\to V
\tag{7.2A}
\]

is a jointly Borel, fiberwise continuous proper-path evaluation of the
unique \(j\)-th untagged output.  Apply the maximal-lift calculus of
Section 5 to \(e_j\).  Its retained-occurrence relation has nonempty
countable sections because the native \(h\)-unbreakability hypothesis
guarantees one output at the next stage.  Lusin--Novikov selects its
least occurrence \(\sigma_j(\ell)\) Borelly.  Define

\[
 e_{j+1}(\ell,r)
 :=
 f\!\left(
   \widetilde e_{j,\sigma_j(\ell)}(r)
 \right).
\tag{7.2B}
\]

This is jointly Borel, fiberwise continuous, and proper.  Although
different \(\ell\)'s may have intersecting or coincident output paths,
global injectivity is not needed for the next germ calculation: the
original source label \(\ell\) remains part of every occurrence code.
The native unbreakability assertion guarantees that the selected
pushforward in (7.2B) is the unique untagged successor.

Finite recursion constructs \(e_1,\ldots,e_h\).  When an output is
known analytically to be a leaf of a retained Wave \(R\), take its
compact image and use the Borel inverse of the target code
\(j_R:L_R\to\mathcal K(\overline V^{\rm pe})\) from Section 8.  This
is the precise interface between the path-valued recursion and the
ordered target leaf space.

### Repair B (distinct-output relation)

Let \(\Omega\to L\) be the Borel retained-occurrence space and let
\(\kappa:\Omega\to\mathcal K(\overline V^{\rm pe})\) be the Borel
compactified pushed-image code.  Define

\[
 R_{\rm out}
 =
 \{(\ell,K):
   \exists\omega\in\Omega_\ell,\ \kappa(\omega)=K\}.
\tag{7.2}
\]

The witness section over \((\ell,K)\) is countable, so the projection
in (7.2) is Borel.  Equality in the hyperspace automatically removes
duplicate occurrence codes.  Lusin--Novikov makes

\[
 \{\ell: |(R_{\rm out})_\ell|=1\}
\tag{7.3}
\]

Borel.

Repair B is valid when the KKL identity of a pushed path is its
geometric compactified path code.  If path identity retains additional
parametrized traversal data, use Repair A or enlarge \(\kappa\) to a
canonical proper-path code before applying (7.2).

Even when Repair B correctly detects a singleton geometric output, its
hyperspace value alone is not automatically a jointly Borel
parameterized path presentation for the next restriction.  In
particular, a unique pushed path can be self-intersecting, and its
compact image does not record traversal order.  Therefore one must not
derive \(A^{h\text{-nbr}}\) by saying only “iterate the compact-output
relation.”  The safe stationary construction imports the native Borel
subwave \(A^{h\text{-nbr}}\), recursively carries the selected pushed
path evaluation on that known unbreakable domain, and returns to the
compact hyperspace only when comparing with an actual retained target
Wave.

## 8. Successor typing and saturation

Let \(R\) be a retained target Wave with standard-Borel leaf space
\(L_R\).  Its compact-arc code is a Borel injection

\[
 j_R:L_R\longrightarrow
 \mathcal K(\overline V^{\rm pe}).
\tag{8.1}
\]

Lusin--Souslin implies that \(j_R(L_R)\) is Borel and that
\(j_R^{-1}\) is Borel on this range.

Therefore a successor initially coded in the hyperspace must be
transported to the target leaf space by

\[
 j_R^{-1}\circ\Phi_1
\tag{8.2}
\]

on the Borel set where \(\Phi_1\in j_R(L_R)\).  Finite successor
composition uses (8.2) at every retained Wave.

Likewise, if \(E\subset L_R\) is a Borel terminal leaf set, the
well-typed full saturation is

\[
 \Phi_h^{-1}\bigl(j_R(E)\bigr),
\tag{8.3}
\]

not the formally mismatched expression
\(\Phi_h^{-1}(E)\) when \(\Phi_h\) is hyperspace-valued.
Equation (8.3) is Borel.  Restricting the injective source evaluation
to it and applying Lusin--Souslin gives Borel geometric support.

This proves saturation closure after the type correction.

## 9. DL ordered-buffer measurability

The directed restriction used by DL is an actual Wave over its fixed
boundary interval \(J\), not merely an arbitrary union of individually
directed leaves.  Proposition 2.2 therefore supplies one Borel numeric
order on that packet.

Let \(L\subset\mathbb R\) be this Borel ordered leaf code.  Every
downward-closed subset \(D\subset L\) has the form

\[
 L\cap(-\infty,a)
 \quad\text{or}\quad
 L\cap(-\infty,a]
\tag{9.1}
\]

for \(a=\sup D\), with the evident unbounded cases.  Hence every
initial order segment is Borel; terminal segments follow by reversing
the order.

DL 2821--2842 deletes only finitely many such outermost buffers after
its finite deck-span decomposition.  The decomposition tags are
endpoint/deck predicates and are Borel by Lemma 6.1.  Therefore the DL
retained and discarded packets are Borel.

This is only a measurability statement.  The \(O(\log m)\) analytic
width charge is supplied by the locked DL proof.  No countably
additive “transverse extremal-width measure” is asserted.

## 10. Equal-endpoint counterexample and Borel circle repair

Distinct ideal endpoints are not automatic.  In the annulus

\[
 A=\{1<|z|<2\},
\]

the path

\[
 \gamma(t)=
 \left(1+\frac14\sin(\pi t)\right)e^{2\pi i t},
 \qquad 0<t<1,
\tag{10.1}
\]

is proper and embedded.  Both tails converge to the same inner prime
end \(1\), and its prime-end closure is a Jordan circle.  If the inner
boundary is marked by at least three intervals and the common endpoint
lies in one of them, this path winds around the full inner boundary.
It is therefore not subordinate to any multi-interval of
combinatorial length at most two.  KKL's path class does not remove the
example merely because the two endpoint values agree.

The example does not obstruct Borel realization.  It forces a second
hyperspace branch.

### Proposition 10.1 (Borel arc/circle split)

Let \(L\) be a standard-Borel leaf coordinate and let

\[
 s\longmapsto K_s
\]

be the Borel prime-end compactification field.  Assume each geometric
leaf is embedded, each tail has a prime-end limit, and the only
boundary points of \(K_s\) are those tail limits.  Then the sets

\[
\begin{aligned}
 L_{\rm arc}
 &:=
 \{s:|K_s\cap\partial^{\rm pe}V|=2\},\\
 L_{\rm circ}
 &:=
 \{s:|K_s\cap\partial^{\rm pe}V|=1\}
\end{aligned}
\tag{10.2}
\]

are Borel.  On \(L_{\rm arc}\), \(K_s\) is a compact arc.  On
\(L_{\rm circ}\), \(K_s\) is a Jordan circle meeting the ideal
boundary in its one distinguished point \(a_s\).

#### Proof

The boundary incidence relation

\[
 E=
 \{(s,\xi):\xi\in K_s\cap\partial^{\rm pe}V\}
\tag{10.3}
\]

is Borel with nonempty sections of cardinality at most two.
Lusin--Novikov enumerates the sections.  For a Borel relation with
finite sections, the loci on which the section has cardinality one or
two are Borel.  This proves the first assertion.

On \(L_{\rm arc}\), the compactified leaf map is a continuous
injection from \([0,1]\), hence a homeomorphism onto a compact arc.
On \(L_{\rm circ}\), its only failure of injectivity on \([0,1]\) is
the equality of the two endpoint values.  It therefore factors as a
continuous bijection from

\[
 [0,1]/(0\sim1)\simeq S^1
\]

to \(K_s\).  Compact-to-Hausdorff continuity makes this factor a
homeomorphism. \(\square\)

### Proposition 10.2 (Borel based-circle parameterization)

There is a jointly Borel map

\[
 e_{\rm circ}:L_{\rm circ}\times[0,1]
 \longrightarrow\overline V^{\rm pe}
\tag{10.4}
\]

such that, for every \(s\in L_{\rm circ}\),

1. \(e_{\rm circ}(s,0)=e_{\rm circ}(s,1)=a_s\);
2. \(e_{\rm circ}(s,\cdot)\) induces a homeomorphism
   \(S^1\to K_s\); and
3. the restriction to \((0,1)\) is a proper embedded
   parameterization of the original leaf in \(V\).

#### Proof

The one-point section of (10.3) gives a Borel map

\[
 a:L_{\rm circ}\to\partial^{\rm pe}V.
\tag{10.5}
\]

Choose a compatible metric on the compact prime-end annulus.  For
\(n\ge1\), set

\[
 F_{s,n}
 :=
 \{x\in K_s:d(x,a_s)\ge1/n\}.
\tag{10.6}
\]

The relation \(x\in F_{s,n}\) is Borel and its sections are compact.
Since \(K_s\) is nondegenerate, at least one \(F_{s,n}\) is nonempty.
The least such integer

\[
 n(s)=\min\{n:F_{s,n}\ne\varnothing\}
\tag{10.7}
\]

is Borel.  Kuratowski--Ryll-Nardzewski selection applied to
\(F_{s,n(s)}\) supplies a Borel point

\[
 c_s\in K_s\setminus\{a_s\}.
\tag{10.8}
\]

Consider the relation on pairs of nonempty compact sets
\((A_0,A_1)\):

\[
\begin{cases}
 A_0,A_1\subset K_s,\\
 A_0,A_1\text{ are connected},\\
 a_s,c_s\in A_0\cap A_1,\\
 A_0\cup A_1=K_s,\\
 A_0\cap A_1=\{a_s,c_s\}.
\end{cases}
\tag{10.9}
\]

This is a Borel relation in

\[
 L_{\rm circ}\times
 \mathcal K(\overline V^{\rm pe})^2.
\]

Indeed, compact containment, point incidence, union equality, and
connectedness are Borel hyperspace conditions.  The last equality in
(10.9) is the conjunction of

\[
 a_s,c_s\in A_0\cap A_1
\]

and, for every \(m\ge1\),

\[
 A_0\cap A_1
 \subset
 B(a_s,1/m)\cup B(c_s,1/m),
\tag{10.10}
\]

which is Borel.

For a circle and two distinct points, (10.9) has exactly two ordered
solutions: the closures of the two components of

\[
 K_s\setminus\{a_s,c_s\},
\]

in either order.  To verify uniqueness, note that every proper
nondegenerate compact connected subset of a circle is an arc.  The
intersection and union conditions in (10.9) force one arc to be the
closure of one complementary component and the other arc to be the
closure of the other.

Lusin--Novikov therefore enumerates these two ordered solutions
Borelly.  Select one by a fixed Borel linear order on the compact
hyperspace and call it

\[
 (A_s^0,A_s^1).
\tag{10.11}
\]

Both are Borel fields of compact arcs.  Apply the ordered-arc
parameterization of Section 4 to obtain jointly Borel homeomorphisms

\[
\begin{aligned}
 e_0(s,\cdot)&:[0,1]\to A_s^0,
 &e_0(s,0)&=a_s,
 &e_0(s,1)&=c_s,\\
 e_1(s,\cdot)&:[0,1]\to A_s^1,
 &e_1(s,0)&=c_s,
 &e_1(s,1)&=a_s.
\end{aligned}
\tag{10.12}
\]

Define

\[
 e_{\rm circ}(s,r)
 =
 \begin{cases}
  e_0(s,2r),&0\le r\le1/2,\\
  e_1(s,2r-1),&1/2\le r\le1.
 \end{cases}
\tag{10.13}
\]

The two formulas agree at \(r=1/2\), so the map is jointly Borel and
fiberwise continuous.  The two arcs meet only at \(a_s,c_s\).
Therefore (10.13) is injective on \([0,1)\), identifies only \(0\)
with \(1\), and maps onto \(K_s\).  It induces a continuous bijection
from \(S^1\) to \(K_s\), hence a homeomorphism.

Finally,

\[
 K_s\setminus\{a_s\}
\]

is exactly the geometric leaf in \(V\).  Its parameterization by
\((0,1)\) is proper because the inverse image of a compact subset of
\(V\) is closed in \((0,1)\) and stays a positive parameter distance
from the deleted endpoint. \(\square\)

Combining the ordinary arc evaluation on \(L_{\rm arc}\) with
(10.13) on \(L_{\rm circ}\) gives the required jointly Borel proper
leaf evaluation on all proof-used packets.  Thus equal endpoint values
are a repaired branch, not a remaining hypothesis.

## 11. Frozen-snapshot acceptance verdict

The core new idea—strict planar nesting plus the full-support area
coordinate—is mathematically sound and genuinely removes the need to
assume a measurable leaf quotient.  In the frozen `C9F1...D318`
snapshot, the following earlier defects have been repaired:

1. zero-width but nonempty arc classes are retained;
2. the distinct-endpoint arc and equal-endpoint based-circle branches
   are both parameterized Borelly;
3. maximal lift reachability is coded with compactly contained
   inverse-branch charts and positive margins;
4. properness and prime-end convergence are tested separately;
5. duplicate germs require nonempty overlap and one equality time;
6. native unbreakability, rather than raw occurrence counting or
   equality of compact images, controls recursion;
7. the recursion remains path-valued until it is typed into the actual
   target Wave through its injective compact-leaf code; and
8. terminal saturation is pulled back in the target leaf-code space.

Two qualifications remain.

### 11.1 Minor explicit argument required for the marking filters

The live draft says that subordination is invariant under relative
homotopy with endpoints moving inside two fixed marked intervals.  The
statement is correct, but its proof should be written.

Suppose \(\gamma_0\) is subordinate to a multi-interval \(X\), and
\(\gamma_0,\gamma_1\) are relatively homotopic while their two endpoint
tracks stay in fixed marked intervals \(I_-,I_+\).  Since \(X\) is a
union of complete marked intervals and contains the endpoints of
\(\gamma_0\), it contains \(I_-\cup I_+\).  Given a neighborhood
\(N\supset X\), replace \(\gamma_0\), rel its endpoints, by a path in
\(N\).  Concatenate that path with the two endpoint tracks, which also
lie in \(N\).  The result has the endpoints of \(\gamma_1\), lies in
\(N\), and is homotopic to \(\gamma_1\) rel those endpoints.  Thus
\(\gamma_1\) is subordinate to \(X\).  The reverse implication is
symmetric.  Therefore subordination is constant on the relative
homotopy classes used by both filters.

### 11.2 Promotion-blocking DL buffer gap

The frozen draft asserts that every actual DL outer-buffer deletion
intersects each ordered arc chart in an initial interval, a terminal
interval, their union, or the empty set.  The cited source does not
prove that assertion:

- DL 1791--1792 defines left and right buffers only for the vertical
  foliation of one rectangle;
- DL 2827 and 2841 use the phrase “outermost curves” for the general
  annular Wave without defining the deleted leaf set; and
- neither passage proves chartwise order convexity when the Wave has
  several arc classes.

The precise missing lemma is:

> **DL chartwise buffer-convexity.** For each deck-span packet and each
> nonempty arc chart \(\alpha\), the intersection of the exact DL
> deleted family with \(L_\alpha\) is a union of at most one lower and
> one upper ray in the nested-domain order.

A proof must work in the annular strip, identify the exact conflict
set with each relevant deck translate, prove monotonicity of that
conflict set along every fixed arc chart, and then show that the
single global \(O(\log m)\) deletion is the finite union of precisely
those chartwise rays.  It may not choose fresh width-one cuts
independently in every chart, because summing those losses would make
the analytic constant depend on the number of arc classes.

### 11.3 Optional common-Wave corollary needs a sharper hypothesis

The frozen draft no longer uses a multi-class total order in the DL
argument.  Its optional Corollary 3.2a should nevertheless say
explicitly that the two collective end blocks \(E^-,E^+\) are
mutually disjoint and that every leaf joins \(E^-\) to \(E^+\).
Without mutual disjointness, take both aggregate ends to be the same
marked interval \(I_0\) and two disjoint boundary-parallel crosscuts
cutting off disjoint caps inside \(I_0\).  Their complementary
\(J\)-side domains both contain a crest interval
\(J\subset\partial^{\rm pe}V\setminus I_0\), but overlap without either
containing the other.  This is the same-end-block fan obstruction.

With distinct end blocks, a complete proof should add the missing
strip sentence: a simple lift is disjoint from all of its nontrivial
deck translates, so its endpoint displacement is less than one deck
period; directedness over the fixed \(J\) then forces the endpoints
into the unique adjacent lifts of \(E^-\) and \(E^+\), excluding the
opposite-side fan.

The definition-level source reading
`ARC_CLASS_SUBLAMINATION_IS_PROPER_BOREL` remains visible and
source-locked to KL06 `wad.tex` 142--150 and KKL 1911.  It is an
imported convention, not a theorem derived from an arbitrary Borel
partition.

Accordingly, the frozen snapshot does **not** yet promote
`STANDARD_BOREL_ORDERED_WAVE_REALIZATION` or
`KKL_STATIONARY_RELATIVE_WAVE_CONTINUATION`.  The sole substantive
remaining proof task is `DL_CHARTWISE_BUFFER_CONVEXITY`; the filter
argument and optional common-Wave qualification are local textual
repairs.  Gate N2, VAAPC-I, UPTCR, rigidity, parameter fibers, and MLC
remain open.

## 12. Post-audit bypass of chartwise buffer convexity

The final sentence of Section 11 has been superseded by a stronger
construction, proved in

```text
kkl_stationary_n1_borel_width_envelope_20260726.md.
```

The construction does not attempt to make the literal DL discard
Borel.  If \(D_{\rm DL}\) is that possibly non-Borel discard and
\(\mathcal W(D_{\rm DL})\le C_{\rm DL}\), choose a nearly extremal
admissible metric for \(D_{\rm DL}\), regularize it from above by a
pointwise lower-semicontinuous density, and discard every source leaf
whose regularized length is at least one.  Lower semicontinuity makes
this enlarged discard Borel in the compact-open path code.  It
contains \(D_{\rm DL}\), has width at most \(C_{\rm DL}+\varepsilon\),
and therefore leaves a Borel subwave inside the actual DL injective
subwave.

The pointwise qualifier is essential: an almost-everywhere
Vitali--Carathéodory majorant need not preserve line lengths on curves
contained in an area-zero exceptional set.  The companion proof
repairs the exceptional null set by dyadic open covers before forming
the length threshold.

DL 2823's displayed aggregate inequality alone is insufficient.  The
required relative bound comes from the proof at DL 2830--2841: every
discarded nonzero span class has \(O(1)\) width, there are
\(O(\log m)\) classes, and the final outer buffer has \(O(1)\) width.
For Gate N1, \(m=2\), so the resulting constant is absolute.

Thus `DL_CHARTWISE_BUFFER_CONVEXITY` is no longer a dependency of Gate
N1.  The frozen BOWR text must be integrated with the width-envelope
lemma and its order-specific claims removed or demoted before either
N1 statement can be promoted.  The open classifications for Gate N2,
VAAPC-I, UPTCR, rigidity, parameter fibers, and MLC are unchanged.

### 12.1 Final frozen envelope snapshot

The exact envelope proof independently accepted after all traceability
repairs is

```text
kkl_stationary_n1_borel_width_envelope_20260726.md
SHA-256
9F2ABD1E8DDD0E0E1B4FFC3B55B8DAF3BA64B4BCBE4E9562454A850E5E8422BE
```

The final repairs added:

1. the retained-width corollary from the Parallel Law;
2. the named, source-locked analytic input
   `DL_RELATIVE_DISCARD_FAMILY_BOUND`; and
3. correct target typing through the proper Borel target lamination
   and KKL Proposition A.14, without claiming that DL transports the
   source Wave base.

Both independent audits return `PASS` for
`BOREL_WIDTH_ENVELOPE_PRUNING`, conditional exactly on the named
relative DL discard bound.  This proves the replacement measurable
interface; it does not by itself promote the unintegrated live BOWR or
N1 statements.

## 13. Target-Wave typing under leafwise direction

The analytic N1 note deliberately distinguishes

\[
 S\uparrow I
\]

from the assertion that the aggregate crest of \(S\) contains \(I\).
By Definition 4.0 there, \(S\uparrow I\) means only that every
singleton Wave \(\{\gamma\}\) crests over \(I\).  Consequently KKL
Proposition A.14 cannot in general be applied once with aggregate
source \(A=S\) and crest \(I\).

The injective DL image is nevertheless a KKL Wave.  The exact
source-typed argument is as follows.

Let \(C\) be the target ideal-boundary component containing \(F_*I\).
Fix a retained occurrence \(\beta\) with source leaf \(\gamma\).

1. Since \(S\uparrow I\), the singleton \(\{\gamma\}\) is a KKL Wave
   over \(I\).
2. The source leaf is in the declared unbreakable packet.  The
   covering pushforward \(f(\beta)\) is a proper marked path by KKL
   2065--2072, and injectivity on the retained DL family makes
   \(\{f(\beta)\}\) a singleton lamination contained in
   \(F_*\{\gamma\}^{\rm nbr}\).
3. KKL Proposition A.14 at 2164--2168 is therefore correctly typed on
   this singleton pair.  It says that \(\{f(\beta)\}\) is a Wave over
   \(F_*I\).  If \(B_\beta\) is its singleton base, then
   \(F_*I\subset B_\beta\) and connectedness of a multi-interval gives
   \(B_\beta\subset C\).
4. The leaf \(f(\beta)\) is subordinate to \(B_\beta\), hence to
   \(C\): every neighborhood of \(C\) is in particular a neighborhood
   of \(B_\beta\), so the defining homotopy representatives from KKL
   1867--1868 work for it.
5. KKL 1853 and 1855--1856 allow an entire ideal-boundary component
   as a multi-interval.  The injective image of the Borel retained
   family is already a proper Borel lamination by Lusin--Souslin.
   Since all of its leaves are subordinate to the one multi-interval
   \(C\), KKL 1874 makes the aggregate image a KKL Wave subordinate to
   \(C\).

The two conclusions must remain separate:

- the aggregate image is a Wave because all leaves are subordinate to
  the common whole component \(C\); and
- singleton Proposition A.14 gives the leafwise assertion
  \(R\uparrow F_*I\).

It does **not** prove that the aggregate crest of \(R\) contains
\(F_*I\), and no later N1 step may use that stronger statement.  This
typing repair is valid and rules out a fatal gap at this point, but it
must be stated explicitly in both the integrated BOWR note and Lemma
2.3 of the analytic N1 note before promotion.

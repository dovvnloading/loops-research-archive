# Variable-end stationary exit transfer

Date: 2026-11-24. Base revision: `9340778fa59029e1bfba88639b03dfb63115cab3`.

Status: written modulus theorem and its explicit native degree budget.
The existence of the exits specified below for every retained stationary
leaf is **not** proved. No independent repair of KKL Lemma 6.31, global
stationary theorem, or MLC is claimed.

AI disclosure: prepared with OpenAI GPT-6 Astra Pro assistance. This note
does not represent human specialist review or a novelty claim.

## 1. Result

The terminal stationary estimate does not require all leaves to leave the
same pulled small Julia set. It is enough to supply one actual proper exit
per parent, with one endpoint in a collection of ends having a controlled
**sum of peripheral degrees**. The other endpoint may be a different
inner end or the outer end. Neither dynamical marking retention nor
noncollision of covering images is needed in this terminal calculation.

More precisely, let `A` be a Borel lamination of simple proper parent
paths. Suppose an immersion permits selecting one maximal lift `b_alpha`
per parent, proper in a specified final surface `X`, and joining two
different ideal boundary components. Let `V` be the finite set of those
components. If `L_v` is the peripheral cyclic-cover local width of end
`v`, then

\[
 \mathcal W(A)\le
 \inf\left\{\sum_{v\in V}a_vL_v:
       a_v\ge0,\quad a_u+a_v\ge1
       \text{ for every occurring endpoint pair }\{u,v\}\right\}.
 \tag{1.1}
\]

An end whose local width is not to be used is assigned coefficient zero;
there is no multiplication of zero by an infinite quantity in (1.1).
All displayed sums can equivalently be restricted to the ends with
positive coefficient and finite local width.

For a final degree-`2^m` pullback of an actual primitive cycle, consider
all components mapping to any collection of at most `b` target small
Julia sets. Their peripheral degrees sum to at most `b 2^m`. Hence, if
every parent admits a proper exit incident to that collection,

\[
 \boxed{\mathcal W(A)\le b\,2^m\mathcal W(\mathcal RF).}
 \tag{1.2}
\]

The bound is independent of the primitive period and the limb rotation
denominator. At `m=b+2`, its coefficient is `b 2^(b+2)`. This is enough
for an `O_b(W(RF))` terminal estimate, although it is weaker numerically
than the existing fixed degree-two-end estimate when that fixed end is
available. If every selected exit has **both** endpoints in the budgeted
collection, the coefficient in (1.2) improves by a factor of two.

The pointwise premise in (1.2) is strictly different from merely having
an endpoint on the pulled Hubbard **carrier**: carrier edges remain
interior points of the surface obtained by removing only the small Julia
sets. Such an endpoint is not an eligible ideal exit.

## 2. Previously available inputs

The following results from the archive are used, with their hypotheses
unchanged:

* [Countable restriction assembly and exact cyclic-end width
  transfer](../maximal_exit_transfer_20261123/NOTE.md), Theorem 2.1 and
  Section 2.4: rational-seed enumeration of maximal lifts, Borel endpoint
  tests in the actual final surface, and a Borel least-code selection.
* The same note, Proposition 2.5: selecting one such lift per parent
  gives `W(A) <= W(B)` by transporting admissible densities on the
  injective selected support.
* The same note, Sections 3--4: a lamination joining a whole ideal end
  to different ideal components has width at most that end's peripheral
  cyclic-cover local width; that local width scales by the degree of a
  finite covering on the whole end.
* [Filled-graph naturality](../../mlc_unified/pql_iterate_filled_graph_naturality.md):
  the actual finite fiber-product domains, filled graph, and peripheral
  typing of their pulled small Julia components.

The primary source is Kahn--Kapiamba--Lyubich (KKL),
[*MLC for parabolically bounded primitive renormalization*,
arXiv:2606.27272v1](https://arxiv.org/html/2606.27272v1):
Sections 2.2 and A.2.4 define cyclic local width; Lemma 4.3, equation
(4.6), bounds every small-Julia local width by `W(RF)`; Section 3.1
defines the bound `b` on the number of small Julia sets in each limb;
and Lemma A.11 is the familiar series comparison for immersion
restrictions. The source's Lemma 6.31 and equations (6.32)--(6.34) are the
stationary application under discussion, **not** hypotheses silently
used to construct an exit in this note.

The extra ingredient here is a finite endpoint-incidence accounting
argument. Its proof keeps actual Borel supports, so it does not assume
that extremal width is an arbitrary transverse counting measure.

## 3. Exact parallel additivity on disjoint Borel supports

### Lemma 3.1

Let `B_1,...,B_k` be families of paths on a Riemann surface `X`. Suppose
their geometric supports `S_j` are Borel and pairwise disjoint. With
extremal width defined as the infimum of the areas of Borel admissible
densities,

\[
 \mathcal W_X\left(\bigcup_{j=1}^k B_j\right)
   =\sum_{j=1}^k\mathcal W_X(B_j).
 \tag{3.1}
\]

#### Proof

For any density `rho` admissible for the union, `rho 1_(S_j)` is
admissible for `B_j`. Disjointness of the supports gives

\[
 \int_X\rho^2\,dA\ge
 \sum_j\int_{S_j}\rho^2\,dA\ge\sum_j\mathcal W_X(B_j).
\]

Conversely choose densities `rho_j` admissible for `B_j` with areas
within any prescribed positive total error of their respective infima.
Replace each by `rho_j 1_(S_j)`, and define `rho` to equal this density
on `S_j` and zero elsewhere. This is a Borel density admissible for the
union. Its area is the sum of the chosen areas. Let the error tend to
zero. Cases in which a width is infinite follow from the first
inequality. QED.

No assertion about an arbitrary partition of tagged covering images is
made: images may coincide or cross. The lemma is applied below before
any covering pushforward, on pairwise disjoint actual lifted leaves.

## 4. The endpoint graph bound

### Theorem 4.1

Let `A` have the Borel parent presentation and final-surface immersion
setting of the exit-transfer note, Section 2.4. Suppose each parent has
at least one maximal lift proper in the final surface `X`, joining two
different components in a finite collection `V` of ideal boundary
circles. Require that the qualifying-lift condition is Borel. Select
the least qualifying rational-seed code for each parent and call the
resulting lamination `B`.

Let `E` be the set of unordered endpoint pairs occurring in `B`. For
each `v` let `L_v` be its peripheral local width. Then (1.1) holds.

#### Proof

The supplied enumeration and endpoint tests make the selected family
Borel. Distinct selected lifts are disjoint: lifts of different parent
leaves cannot meet, and only one lift of a given parent was selected.
The immersion is injective on their union because each parent is
embedded and there is only one chosen lift per parent. Thus Proposition
2.5 of the cited note gives

\[
 \mathcal W(A)\le\mathcal W_X(B).
 \tag{4.1}
\]

For `e={u,v}` let `B_e` be the sublamination with that endpoint pair,
and write `x_e=W_X(B_e)`. Endpoint maps are Borel. The injective Borel
evaluation map and the Lusin--Souslin theorem make the geometric
support of each `B_e` Borel. These supports are pairwise disjoint.
Lemma 3.1 therefore gives

\[
 \mathcal W_X(B)=\sum_{e\in E}x_e.
 \tag{4.2}
\]

For a fixed end `v`, the union of the `B_e` incident to `v` is a
lamination joining that whole end to different boundary components.
The cyclic-end comparison and Lemma 3.1 give

\[
 \sum_{e\ni v}x_e\le L_v.
 \tag{4.3}
\]

Now take any nonnegative coefficients satisfying `a_u+a_v>=1` on every
edge. Equations (4.2)--(4.3) imply

\[
 \mathcal W(A)
 \le\sum_{\{u,v\}\in E}x_{uv}
 \le\sum_{\{u,v\}\in E}(a_u+a_v)x_{uv}
 =\sum_v a_v\sum_{e\ni v}x_e
 \le\sum_v a_vL_v.
 \tag{4.4}
\]

Taking the infimum proves (1.1). For zero coefficients no local-width
estimate at that end is required. QED.

This is the weighted fractional vertex-cover problem for the actual
endpoint graph. It does not estimate a graph defined only by allowable
symbolic itineraries unless every selected exit has been proved to have
one of those endpoint pairs.

### Corollary 4.2: useful special cases

1. **One fixed end:** if all exits meet `v`, choose `a_v=1`, all other
   coefficients zero, and recover `W(A)<=L_v`.
2. **Variable ends in one budget:** if every exit meets a set `C` of
   ends, take `a_v=1` on `C`, zero elsewhere. Then
   `W(A)<=sum_(v in C)L_v`.
3. **Both ends in the budget:** if all exits join different members of
   `C`, take `a_v=1/2` on `C`. Then
   `W(A)<=1/2 sum_(v in C)L_v`.
4. **Bipartite endpoint graph:** either side of a bipartition is a cover,
   giving the smaller of the two sums of local widths.
5. **Width-zero failures:** the same bounds hold if the exit condition
   fails only on a Borel parent subfamily of extremal width zero, by
   subadditivity of modulus. This does not turn an unmeasured exceptional
   set into a width-zero set.

The half-sum can improve every integral choice: for a triangle with
`L_1=L_2=L_3=L`, (4.3) gives `W(A)<=3L/2`, whereas an integral vertex
cover would only give `2L`. The primal assignment `x_12=x_23=x_31=L/2`
and dual assignment `a_1=a_2=a_3=1/2` certify optimality **of this finite
budget problem**. They do not assert that a particular native KKL
surface realizes these three widths simultaneously.

## 5. A native degree budget independent of the primitive period

### Lemma 5.1

Let `P:S->U` be a proper finite holomorphic map of degree `D` between
conformal disks. Let `K_0,...,K_(p-1)` be pairwise disjoint nondegenerate
full compact continua in `U`. Assume every critical value of `P` belongs
to their union. Let `Q_(j,l)` be the components of `P^(-1)(K_j)`.
The peripheral degree `d_(j,l)` of the corresponding ideal end in

\[
 X'=S\setminus P^{-1}\Bigl(\bigcup_jK_j\Bigr)
\]

satisfies

\[
 \sum_l d_{j,l}=D\quad\text{for every }j.
 \tag{5.1}
\]

If every target end has local width at most `R`, then, for any set `J`
of target indices,

\[
 \sum_{j\in J,l}L(Q_{j,l})\le |J|D R.
 \tag{5.2}
\]

#### Proof

Choose a sufficiently small Jordan neighborhood of `K_j` that is
disjoint from the other compacta and whose boundary avoids critical
values. The complete preimage of that boundary has finitely many
components. Their covering degrees sum to `D`, since every point of the
target boundary has exactly `D` preimages.

Each component of the preimage of the filled Jordan neighborhood is a
disk: a Jordan curve in that component fills there by the argument
principle, as in the annular-properness note, Lemma 3.1. Inside such a
component all its critical values are in `K_j`. The complete pullback of
`K_j` in that component is connected and full by the same lemma. Thus
the boundary covering components correspond exactly to the `Q_(j,l)`;
shrinking the neighborhood preserves their degrees. These are their
peripheral ideal-end degrees, proving (5.1).

The whole-end covering identity gives
`L(Q_(j,l))=d_(j,l)L(K_j)`. Sum and use `L(K_j)<=R`. QED.

### Corollary 5.2: actual quadratic finite iterate

Let `P_m=f^m:U^m->U` be the actual finite fiber-product covering of a
pseudo-quadratic-like map with a primitive small-Julia cycle
`K_0,...,K_(p-1)`. Its total degree is `D=2^m`. The finite-iterate
critical-value calculation gives

\[
 \operatorname{CV}(P_m)\subset\{F(c),...,F^m(c)\}
 \subset\bigcup_jK_j,
\]

because the critical point belongs to the critical small Julia set and
the cycle is forward invariant. Hence Lemma 5.1 applies to the actual
complementary covering, with no additional global injectivity premise
on the immersion.

For a parabolically `b`-bounded cycle, let `J_0` index the small Julia
sets in the physical critical limb. The source definition gives
`|J_0|<=b`; KKL Lemma 4.3 gives `L(K_j)<=R=W(RF)`. The ideal ends above
these indices therefore satisfy

\[
 \sum_{j\in J_0,l}L(Q_{j,l})\le b2^mR.
 \tag{5.3}
\]

Suppose every parent of a stationary subfamily `A` has at least one
maximal immersion lift, proper in
`U^m\setminus P_m^(-1)(union K_j)`, joining two different ideal
components and incident to an end in (5.3). Use the least-code
selection and Corollary 4.2(2). This proves (1.2).

The criterion permits a different `j`, preimage component, access, and
other endpoint for every parent. An outer ideal endpoint is allowed.
Self-returns to the same ideal component are not allowed by this
criterion: the comparison used in (4.3) was proved for exits to
different ideal components.

### Corollary 5.3: a fixed window of limbs, or a predecessor bank

The critical limb is only one useful choice of target budget. For any
collection of `k` physical limbs, parabolic `b`-boundedness gives at most
`kb` target small Julia sets there. The identical proof gives the bound
`kb 2^m R` for exits incident to their full pullback. Thus the acceptable
limb window may include the first few postcritical limbs without
introducing dependence on the rotation denominator.

There is a sharper budget when the endpoints belong to the actual
selected predecessor chain. Put `m=b+r`, where `2<=r<p`, and let

\[
 \mathcal Q=\{\widehat Q_b,\widehat Q_{b+1},...,\widehat Q_{m-1}\},
 \qquad \widehat Q_n=\Gamma_m(Q_n).
 \tag{5.4}
\]

Each member is an entire component of the final pulled small-Julia
cycle, has whole-end degree two, and maps to `K_(m-n)`. In particular
these `r` components are distinct, and their local widths sum to at most
`2rR`.

To check this for every listed `n`, repeat the argument of the
exit-transfer note, Corollary 6.6: the first `n` arrows are univalent
selected predecessor arrows, the next arrow `K_0->K_1` has degree two,
and the remaining `m-n-1<p-1` cycle arrows are univalent. Choose
composable Jordan neighborhoods along this finite itinerary. Their
composite has full inverse compactum `Q_n` and degree two; the
filled-graph collar transfers both the component identity and the
degree to `U^m`. Distinct target indices `1,...,r<p` give distinct
source components. No claim about a chosen path follows from this
component calculation alone.

Consequently, if every parent has any actual proper exit incident to
the bank (5.4),

\[
 \mathcal W(A_m)\le2rR.
 \tag{5.5}
\]

If every selected exit joins two different members of the bank, the
bound is `rR`. For example, the longer noncollision horizon `m=b+4`
permits a variable-end bound `8R`, or `4R` for inner-bank exits. It
requires no one common member or one common pair of bank members.

The existing two-physical-hit lift theorem also applies separately to
any two distinct bank members: its continuation argument depends on
their actual graph components and proper endpoint typing, not on their
names. Thus the weaker condition that every parent physically hits
**some two** distinct members of the bank supplies an inner or outer
exit incident to the bank and proves (5.5). The choices may vary from
leaf to leaf. First-hitting times and component labels are Borel for
continuous parent paths and finitely many compacta; alternatively the
least-code selection may be applied directly to all qualifying exits.
This corollary does not assert that the stationary hypotheses force
those two hits.

## 6. What this does and does not settle

The existing fixed-component exit theorem demands a particular end
whose local degree is two. When that end is available it gives the
better constant `2R`. The present route instead accepts any degree
budget controlled solely by `b`, including every pulled end above the
at most `b` critical-limb target components. It proves an `O_b(R)`
bound without needing a common fixed endpoint.

This removes the following from the **terminal width argument**:

* a globally common small-Julia component;
* a common endpoint label or access;
* dynamical marking retention of the selected terminal exit;
* geometric noncollision of its covering images;
* extraction of a target lamination from those images;
* a transverse-measure interpretation for an arbitrary tagged partition.

The remaining existence statement is concrete:

> For every retained stationary parent, or outside a proved width-zero
> subfamily, construct one actual proper raw exit in the final surface
> incident to a component in one of the controlled banks above: a fixed
> finite limb window, or the finite selected predecessor bank (5.4).

The countable Borel construction handles selection **after** this
existence statement is proved. Full-carrier annular properness does not
by itself settle it: it concerns the complement of the pulled tree,
whereas the final surface here removes only the small Julia cycle.
Likewise, an ideal endpoint on a tree edge does not become an endpoint
on a small Julia component by changing its label.

No native counterexample to that existence statement is supplied here.
No conclusion is drawn about full immersion MARK, the independent
one-step stationary telescope, compatible all-scale towers, H1--H4,
UPTCR, or MLC.

## 7. Source import versus independent source repair

KKL v1 Lemma 6.31 states a fixed-component exit for the stationary
family `A_(N-1)`, where `N=b+3`, and also states degree one on that
component. Its proof's final sentence writes the undefined `A_N`; the
preceding definition only constructs `A_0,...,A_(N-1)`. The archive's
filled-graph calculation gives degree two on its canonical corrected
component. These are separate issues from the existential exit.

There are therefore two logically different uses of the source:

1. **Source-imported route:** explicitly take the existential part of
   Lemma 6.31 as an imported analytic theorem under its native
   hypotheses. The degree-one assertion is unnecessary for an
   `O_b(R)` conclusion: the safe full degree bound `2^(b+2)` and the
   fixed-end version of Theorem 4.1 suffice. If the archive's canonical
   identification is also used, its proved degree two gives `2R`.
2. **Independent repair route:** prove that the stationary hypotheses
   supply the required actual exits, without invoking Lemma 6.31's
   existential conclusion. The current archive has deliberately
   retained this as an open obligation. Theorem 4.1 gives a weaker,
   variable-end acceptance target for that proof.

The paper's source-stated native theorem should not be described as a
new unproved conjecture solely because this archive has not independently
reconstructed it. Conversely, merely importing precisely the theorem
under audit is not an independent repair of that audit. The archival
statuses are unchanged by this note.

## 8. Exact finite checks

Run from the repository root:

```sh
python -B research/independent_audits/stationary_transport_attack_20261124/verify.py
```

The checker validates exact rational primal/dual certificates for the
fixed-end bound, four variable degree-two bank ends, the half-budget
inner-bank case, and the triangle fractional optimum. It also checks
the per-target degree census and rejects an uncovered endpoint pair,
an overspent covering degree, an uncharged outer end used as a bound,
and a self-return mislabeled as a different-end exit. These are finite
accounting checks. The analytic modulus proof is written above, and
native exit existence is not asserted by a passing checker.

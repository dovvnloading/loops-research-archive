---
ledger: NOV26_OPEN_CREST_LIMIT
result: partial
ai: OpenAI ChatGPT, GPT-6 Astra Pro; mathematical investigation, Lean proof development, and separate AI scope/dependency audits
human_review: none
---

<a id="actual-crest-global-20261127"></a>

# All-index full-parent terminal gates and oriented actual crest arcs

## Claim

For every return-block index `p >= 17`, and every actual signed-tip parameter
constructed by the archive's `ActualTip p c` predicate, the complete literal
two-cut terminal gate in the chosen original circular parent is exactly one
interval. There is no unspecified eventual threshold, omitted angular
branch, or later admissible component. The selected closed fourth-image
arcs are simple and pairwise disjoint, including their endpoints; their
interiors lie in the upper half-plane. The complete real-intersection
census is also proved.

This is a **partial** contribution to `NOV26_OPEN_CREST_LIMIT`. The parameter
branch identification, native KKL marking and physical extremal-width
identification remain open. No ledger status change is requested.

### Exact objects and quantified statement

Let `f_c(z) = z^2+c`, `d = f_c^p(0)>0` (iterates), and

\[
 H(z)=\frac{f_c^{\,p}(dz)}{d},\qquad
 z(s,u)=-\frac34+s\left(u+i\sqrt{1-u^2}\right).
\]

Superscripts on maps denote iteration. These are the literal quadratic iterates in `normalizedReturn` and
`circlePoint`, not model stand-ins. Define `TerminalGate p c s` by existence
of **any** `u in [-1,1]` satisfying

\[
 \operatorname{Re}H(z(s,u))=0,\quad
 \operatorname{Im}H(z(s,u))>0,\quad
 -1<\operatorname{Re}H^3(z(s,u))< -\operatorname{Re}H^4(0).
\]

The definition does not use an angular selection or a clipped radius
projection. `ActualCrestAllPeriods.complete_original_parent_all_periods`
proves that, for every `p >= 17`, every `ActualTip p c` and every constructed
crossing family `F`, there is

\[
 \frac{663}{10000}<r_p<\frac{133}{2000}
\]

such that the actual third-return terminal coordinate is `-1` precisely at
`r_p` in the crossing window, and

\[
 \forall s\in[1/16,1/8],\qquad
 \operatorname{TerminalGate}(p,c,s)\ \Longleftrightarrow\ s<r_p.
\]

In particular,

\[
 \left\{s:\frac1{16}<s<\frac{p-1}{8p},\
                   \operatorname{TerminalGate}(p,c,s)\right\}
       =\left(\frac1{16},r_p\right).
\]

`exists_complete_original_parent_each_period` constructs both `c` and `F`
for each `p >= 17`. Its caller supplies only that integer inequality. The
endpoint, monotonicity, support bounds, angular uniqueness and absence of
later components are conclusions or proved dependencies.

A stronger quantitative exclusion holds in the whole outer tail:

\[
 \begin{split}
 p\ge17,\quad&s\in[133/2000,1/8],\quad u\in[-1,1],\\
 &\operatorname{Re}H(z(s,u))=0
 \quad\Longrightarrow\quad
 \operatorname{Re}H^3(z(s,u))<-1-\frac1{2000}.
 \end{split}
\]

It holds for every `ActualTip p c`, with one explicit margin independent of
the parameter, radius and angle. It does not even require positive
imaginary first image.

### Complete actual arc geometry

On `s in [1/16,133/2000]`, put `theta_p(s)=arccos(F.angle s)`. The theorem
`ActualCrestArcOrientation.all_period_actual_arc_geometry` and its supporting
theorems prove the following for every `p >= 17`:

- For each `m=2,3,4`, the full upper-semicircle image `H^m(z(s,cos t))`
  meets the real line exactly at `t=0`, `theta_p(s)`, and `pi`.
- On the selected **closed** arcs, fourth-image collisions force equality
  of both radius and cosine coordinate `u in [F.angle s,1]`.
  Therefore distinct closed leaves are disjoint, including real endpoints.
- Their selected fourth-image interiors have strictly positive imaginary
  part. `selected_arc_image_signs` proves that the successive imaginary
  signs are `+,-,+,+`.
- `ActualCrestArcCensus.full_fourth_image_lipschitz`, specialized using
  `actual_complete_support_all_periods`, gives Lipschitz constant `625`
  on the entire angular semicircle, hence bounded variation on the selected
  closed arcs. `finalClosedLeaf_eq_angular_image` identifies the angular
  image for `0 <= t <= theta_p(s)` with the set used in the disjointness
  theorem. The coordinate change is `u=cos t`; cosine is injective on
  `[0,pi]`.

The first-image real-contact census, proved separately in
`ActualCrestArcCensus.first_image_real_iff`, has only the two original
endpoints. Rectifiability is a supporting consequence, not the novelty
claim.

## Evidence

### What changes relative to the starting archive

The starting main revision is
`665e5f942d6b39902272fe6d8ca2dee6fbca8a6f`. The earlier
[actual_maximal_crest_20261127](../actual_maximal_crest_20261127/NOTE.md)
packet explicitly leaves later components in the larger original parent
open. It supplies an eventual collar on the shorter window, its coefficient
limit, and eventual injectivity on an open selected side. The present
claims address those missing quantifiers and closed-boundary geometry.

| Issue | Previously archived | This contribution |
|---|---|---|
| Return-index threshold | Sufficiently large, without an explicit common threshold for the complete collar | Every `p >= 17` |
| Radius range for the exact gate | The selected window `[1/16,133/2000]` | The entire original parent, via exclusion through `1/8` |
| Angular scope | Selected crossing family, with local/full-circle uniqueness on the short window | An existential gate allowing every upper-semicircle angle |
| Selected fourth image | Eventual injectivity on an open positive-real side | All-index joint injectivity of complete closed leaves, including crest endpoints |
| Real contacts and orientation | Selected endpoint facts and support signs | Exact full-angle census and the four-step sign chain |

The positive limiting radial coefficient and its convergence were already
proved. `ActualCrestGlobal.actual_original_parent_collars` attaches those
archived conclusions to the now-complete gate; this is not presented as a
new coefficient or width-limit theorem. The private real-center arithmetic
and sharp model-cut arithmetic reuse archived arguments and are credited
as supporting calculations.

### Proof mechanism

1. **A larger actual comparison disk.** The complete polynomial remainder
   gives, on `norm z <= 2`,
   `norm(H z-Q_(kappa_p) z) <= 216/4^p`, where
   `Q_kappa(z)=1-kappa*z^2`. For `p >= 17` this is at most `10^-7`.
   Comparing with the actual coefficient `kappa_p`, rather than its limiting
   value, makes the threshold effective.
2. **Every crossing, not one branch.** Global model angular growth at least
   `1/10` puts every actual zero of the first real part within `10^-6` of
   the exact model crossing. The full-parent radical root lies in
   `[-1/4,1/4]`. The resulting point displacement is at most `3*10^-7`.
   The first two complete model images stay in disks of radii `2/5` and
   `3/2`; actual intermediate bounds are proved before the next
   approximation is applied. Threefold actual and angular errors yield
   `norm(H^3(z)-T_(kappa_p)(s)) <= 1609/10^7`.
3. **Explicit gate margins.** Rational model estimates give
   `T_kappa(663/10000)>-1+4/10000`,
   `T_kappa(s)<-1-7/10000` on the outer tail, and
   `T_kappa(s)<-97537/100000` throughout the parent. The fourth model
   critical cut is below `9751/10000`; its actual perturbation error is at
   most `156/10^7`. These leave both the endpoint signs and the opposite
   actual terminal inequality strict at every `p >= 17`.
4. **Effective complete support.** A centered-disk recursion with error
   allowance `10^-6` controls the full input disk and all four actual
   images, and proves positive second-image and negative third-image real
   parts. Containment of each intermediate point is derived, not assumed.
5. **Closed geometry forces actual radial order.** The exact polynomial
   fiber alternative is equality or antipodality. Complete-support signs
   exclude antipodal collisions at stages two and three; positivity at
   the imaginary crossing also excludes them on the previously omitted
   closed crest boundary. Joint closed-arc injectivity therefore forces
   injectivity of the actual terminal coordinate. Continuity makes it
   strictly monotone, and the independently proved endpoint signs choose
   the decreasing orientation. The intermediate value theorem then gives
   the unique endpoint. The two-cut gate and exact original-parent interval
   follow from this order and the all-angle outer exclusion.
6. **Real-contact census and orientation.** Complex conjugation and the
   exact fibers imply that an actual image is real precisely when its
   input is on one of the coordinate axes. The support signs propagate
   this to the full semicircle census. The real part of the normalized
   secant is strictly negative; the exact identity
   `Im H(z)=2 Re(z) Im(z) Re(secant(z,conj z))` gives the four image signs.

All displayed decimal constants in the proof are exact rational numbers.
No floating-point computation supplies a proof step.

### Lean source map

All eight files are registered in the existing weighted project and theorem
index; no workflow, dependency pin or trust policy is changed.

| Module | Role |
|---|---|
| `ActualCrestLargeDisk` | Literal return error on the enlarged disk |
| `ActualCrestGlobalModel` | Full-parent model identification, domain control and an independent qualitative exclusion |
| `ActualCrestGlobalQuantitative` | Effective crossing comparison and uniform all-index outer exclusion |
| `ActualCrestQuantitativeSupport` | Complete actual support at every `p >= 17` |
| `ActualCrestArcCensus` | Complete real contacts and closed-arc collisions |
| `ActualCrestArcOrientation` | Imaginary signs and all-index actual arc geometry |
| `ActualCrestGlobal` | Full-angle gate definition and archived coefficient-limit connection |
| `ActualCrestAllPeriods` | Exact complete original-parent gate and constructed existence at every `p >= 17` |

### Validation

The complete all-index theorem and arc theorem have compiled locally with
Lean 4.32.0 and the manifest-pinned Mathlib. Local resource constraints
required narrowing historical broad imports in temporary copies; tracked
project source and CI imports are unchanged. Every new file disables
implicit undeclared parameters. The authoritative validation is the
repository's unchanged weighted Lean workflow: full original-source build,
source coverage/proof-escape scan, and transitive audit of every weighted
declaration. The earlier qualitative checkpoint passed that full workflow
at `8f9f83a`, run `46098230692`; the strengthened final source must pass its
own exact-head CI before this PR is marked ready.

Reproduction in the standard project environment:

```sh
python code/contribute.py check
cd formalization/weighted
lake build ActualCrestAllPeriods ActualCrestArcOrientation
```

The source uses no proof placeholders or new axioms. The only foundational
dependencies allowed by the unchanged audit are `propext`, `Classical.choice`
and `Quot.sound`. Separate local audits of the principal quantitative and
arc theorems and the parameter/family existence theorems returned exactly
those dependencies. Full CI remains the final validation gate.

## Dependencies

`NOV26_CREST_16`, `NOV26_OPEN_CREST_LIMIT`; the source selected circular
parent in
[crest_transport_asymptotics_20261116](../../research/independent_audits/crest_transport_asymptotics_20261116/NOTE.md);
the prior
[actual_crest_foliation_20261126](../actual_crest_foliation_20261126/NOTE.md)
and
[actual_maximal_crest_20261127](../actual_maximal_crest_20261127/NOTE.md)
contributions. Lean dependencies include `NearTwoTip`,
`QuadraticCrestDividedDifference`, `LimitingCrestEndpoint`,
`LimitingCrestModelGates`, `LimitingCrestArcGates`, `LimitingCrestPerturbation`,
and the actual crossing, integral and proper-return modules.

## Boundary

**`NOV26_OPEN_CREST_LIMIT` remains open. This is a proved partial result,
not a request to close the ledger row.**

- `p` is the return-block index in `ActualTip`. The distinguished primitive
  component branch, least critical preperiod and primitive renormalization
  period have not been identified here.
- The exact two-cut gate and actual embedded arcs do not by themselves
  identify the full native q/w endpoint gates, KKL marked proper paths,
  covering-versus-immersion access labels, or prime-end transport.
- The radial integral is not identified here with physical descendant
  extremal width or an unrestricted maximal Wave. No new claim of the
  numerical width limit `0.347004986...` is made.
- Arc geometry is proved on `[1/16,133/2000]`. The separate global estimate
  excludes terminal-admissible crossings in the remaining parent radii;
  it does not assert identical arc geometry for every radius up to `1/8`.
- The novelty comparison is with the inspected archive at `665e5f9` and its
  explicitly stated gaps. No worldwide priority claim is inferred from
  that internal comparison.

## Attribution

The existing archive supplies the actual signed-tip construction, exact
polynomial divided difference, model endpoint algebra, short-window
crossing family, and radial-integral convergence. Their classical and
Mathlib dependencies are used with their original statements. The private
real-center and sharp critical-cut computations reproduce the relevant
archived arithmetic as supporting lemmas; they are not claimed as new
mathematics. The new effective global gate and closed actual curve
conclusions, their proof development and separate AI audits are disclosed
above. Human review: none. Original contributions are released under the
repository's CC0 terms.

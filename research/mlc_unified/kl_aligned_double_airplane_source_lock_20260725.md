# Double-airplane alignment for the KL collision: source-lock audit

## 1. Question, verdict, and scope

This note audits the following proposed realization of the conditional
alignment clause in
`kl_canonical_localization_forced_collision.md`, Section 8:

> Start with the real period-three airplane polynomial, tune it by the
> airplane polynomial, take the physical first renormalization germ, and use
> that same germ as the KL direct-decoration seed.

The audit separates three assertions which must not be conflated.

1. **Ordinary primitive canonical seed.** There is a quadratic polynomial
   \(F=P_c\) with a physical quadratic-like restriction
   \[
      G=F^3:U'\longrightarrow U
   \]
   whose three little filled Julia sets
   \[
      K(G),\quad F(K(G)),\quad F^2(K(G))
   \]
   are pairwise disjoint.
2. **Same-seed KL decoration.** The quadratic-like germ \(G\), not merely its
   straightening, satisfies the KL connectedness, repelling-fixed-point, and
   non-satellite hypotheses, and its KL puzzle marking is the marking carried
   by Kahn's canonical localization of \(F\).
3. **Terminology and hypotheses.** “Primitive” in Shen--Wang and
   Inou--Kiwi means pairwise disjoint closures of all distinct bounded Fatou
   components of the postcritically finite base polynomial. “Primitive
   renormalization” in Kahn means pairwise disjoint physical little filled
   Julia sets. “Not satellite renormalizable” in KL is the escape condition
   in the top Yoccoz puzzle. These are related notions, but the checked
   sources do not identify them by a single theorem applicable to the
   proposed tuned germ.

**Verdict.** The proposed double-airplane witness is a strong and likely
correct realization candidate, but it is **not source-locked at the required
standard**. The sources prove existence of a tuned quadratic and an actual
marked physical return germ hybrid equivalent to the airplane. They do not
literally prove all of Assertions 1 and 2 for that same germ. In particular,
the checked statements do not explicitly supply:

- pairwise disjointness of the three physical outer little Julia sets;
- the KL non-satellite condition for the physical return germ;
- repelling multipliers for both fixed points of that physical germ; or
- exact preservation of the KL puzzle marking under Kahn's canonical
  localization.

Accordingly, this audit **rejects promotion of an aligned realization
theorem**. It makes no ledger-status change. It does not alter the proved
conditional propagation theorem
`KL_CANONICAL_LOCALIZATION_FORCED_COLLISION`, and it does not reopen the
former universal full-embedding route. The current
`DIRECT_DECORATION_DEGREE_ONE_PSEUDO_EMBEDDING` node is already a
non-gating restricted-class classification, not a universal assertion.

VAAPC-I, UPTCR, rigidity, and MLC remain open.

## 2. Primary-source lock

### 2.1 Shen--Wang

W. Shen and Y. Wang,
[*Primitive tuning via quasiconformal surgery*](https://arxiv.org/abs/2010.05199),
arXiv:2010.05199v1.

The checked v1 source archive has SHA-256

```text
8F38A8F23999AA59FEE3A1C4F927835D0B7560C2D16C00FE8C1BE21BB66F60A2
```

Relevant locations in `revision.tex` are:

| subject | source lines |
|---|---:|
| classical quadratic tuning recalled | 47 |
| primitive \(=\) pairwise disjoint bounded-Fatou closures | 52 |
| primitive-PCF surjectivity statement | 55--59 |
| GPL and hybrid-equivalence definitions | 128--145 |
| marked straightening theorem | 162 |
| actual physical return maps \(f^{r(v)}\) | 169--188 |
| pairwise-disjoint source puzzle pieces | 834--846 |
| surgery GPL conformally conjugate to chosen target | 850--863 |
| final polynomial and its physical \(\lambda(f_0)\)-renormalization | 895--903 |

The exact usable content is:

1. if \(f_0\) is primitive, postcritically finite, and hyperbolic, then its
   IK straightening map is bijective;
2. when \(f_0(z)=z^d+a\), the target is the full monic-centered connectedness
   locus of degree \(d\);
3. for each resulting polynomial \(f\), the renormalization is an actual
   generalized polynomial-like map whose fiber maps are physical iterates
   \(f^{r(v)}\);
4. this actual renormalization is hybrid equivalent to the chosen target and
   respects the induced external marking.

The theorem does **not** state that an output tuned polynomial is primitive
in the sense of pairwise disjoint closures of its Fatou components. More
importantly here, it does not state Kahn's exact pairwise-disjointness
condition for the cycle of physical little Julia sets of the first
renormalization.

### 2.2 Inou--Kiwi

H. Inou and J. Kiwi,
[*Combinatorics and topology of straightening maps I: compactness and
bijectivity*](https://arxiv.org/abs/0809.1262),
arXiv:0809.1262v2.

The checked v2 source archive has SHA-256

```text
F47BE43D92D843DAD8F20C45FC5EDF459EEEF2F02173B59BF9964A3CF3C858EC
```

Relevant locations are:

| subject | source location |
|---|---|
| small filled Julia sets \(K_f(v)\) | `outline.tex`, lines 457--477 |
| physical GPL renormalization | `outline.tex`, lines 480--499 |
| induced external marking | `outline.tex`, lines 501--549 |
| hyperbolic target lies in the straightening image | `outline.tex`, lines 592--616 |
| primitive polynomial definition and compactness equivalence | `outline.tex`, lines 622--640 |
| exact renormalization definition | `laminations.tex`, lines 441--453 |
| equality of GPL fibers with \(K_f(v)\) | `laminations.tex`, lines 455--487 |
| combinatorial tuning | `tuning.tex`, lines 178--382 |
| straightening/tuning inverse | `tuning.tex`, lines 382--484 |
| primitive rational lamination | `tuning.tex`, lines 485--518 |
| primitive lamination gives \(\mathcal C(\lambda)=\mathcal R(\lambda)\) | `compact.tex`, lines 1--10 and 120--178 |
| postcritically finite preimage of a PCF hyperbolic target | `thm_c.tex`, lines 8--18 |

These results prove that a physical return map exists and identify its filled
Julia fiber. They also provide the natural route for proving outer
disjointness from primitive laminations and unlinked classes. The checked
paper, however, does not state in the needed form that for the quadratic
double tuning the three planar sets
\[
  K(G),\ F(K(G)),\ F^2(K(G))
\]
are pairwise disjoint. A proof must still translate the lamination/fiber
description to Kahn's planar primitive-renormalization definition.

### 2.3 Milnor's period-three portrait

J. Milnor,
[*Periodic Orbits, External Rays and the Mandelbrot Set: An Expository
Account*](https://www.numdam.org/item/AST_2000__261__277_0/),
Astérisque 261 (2000), 277--333.

The checked Numdam PDF has SHA-256

```text
C85E9BEDCCC9ADB874B71E78C7F78C8268505787C12A6146A40C6D1A98B39965
```

Milnor identifies the real period-three component through its root
\(-7/4\) and the orbit portrait
\[
  \bigl\{\{3/7,4/7\},\{6/7,1/7\},\{5/7,2/7\}\bigr\}.
\]
His primitive/satellite classification of portraits and hyperbolic
components classifies this period-three component as primitive.

This is enough to identify the intended component. It is not, by itself, the
literal Shen--Wang hypothesis that the closures of every two distinct
bounded Fatou components of the center polynomial are disjoint. That bridge
is standard but must be proved or cited in the exact terminology before the
Shen--Wang theorem is invoked formally.

### 2.4 Kahn and KL

The checked TeX sources are:

| file | SHA-256 |
|---|---|
| Kahn I `intro.tex` | `E7DD61396FEA927903D4DE4FD386E7AAEFD0BD3E2CEE1CE6F011680AD58144E0` |
| Kahn I `psiql2.tex` | `E4EFCCEC65D8C9C2BDFE2AF8203B3D4D63ECF992B40D302F56FBA78259547228` |
| KL II `psiql.tex` | `6CC9726461473812A5FBA93377F2DC0B088DB6CAC4B9DE90C7B2AE625DFB49AF` |
| KL II `kingdom.tex` | `5DC04FEFF6B6A1D73040FFD50519C35D62EFF03C1049686DA71D595758E38FA7` |

The precise clauses are:

1. Kahn I `intro.tex`, lines 22--44, defines a primitive
   \(p\)-renormalization by pairwise disjointness of the physical small
   filled Julia sets.
2. Kahn I `psiql2.tex`, lines 549--558, forms the canonical
   renormalization by localizing the physical iterate
   \((i^p,f^p)\) at the central little Julia set and removing the entire
   little-Julia cycle.
3. KL II `psiql.tex`, lines 76--83, starts the pseudo-puzzle only after
   assuming connected filled Julia set and two repelling fixed points for
   the quadratic-like restriction.
4. KL II `kingdom.tex`, lines 77--94, defines satellite
   renormalizability and obtains finite escape depth only in the
   non-satellite case.
5. KL II `kingdom.tex`, lines 90--155, constructs the actual
   direct-decoration pieces \(P,Q_L,Q_R\) and their univalent physical
   branches.
6. KL II `kingdom.tex`, lines 211--225, identifies the terminal
   principal-nest map with a primitive renormalization and then imposes the
   standing assumption that the seed \(f\) is primitively renormalizable.

Thus, a mere hybrid equivalence with a named airplane polynomial is
insufficient. The physical germ occurring in Kahn's canonical localization
must satisfy the KL assumptions.

## 3. What is established directly for the airplane center

Let
\[
  h(c)=c^3+2c^2+c+1.
\]
For \(P_c(z)=z^2+c\),
\[
\begin{aligned}
 P_c(0)&=c,\\
 P_c^2(0)&=c^2+c=c(c+1),\\
 P_c^3(0)&=(c^2+c)^2+c
          =c\bigl(c^3+2c^2+c+1\bigr)
          =c\,h(c).
\end{aligned}
\]
Furthermore,
\[
  h(-9/5)=-19/125<0,\qquad h(-7/4)=1/64>0,
\]
and
\[
  h'(c)=3c^2+4c+1=(c+1)(3c+1)>0
  \quad\text{for }c<-1.
\]
Hence there is a unique real zero
\[
  a\in(-9/5,-7/4)
\]
of \(h\). Since \(a\ne0,-1\), the critical point \(0\) has exact period
three for
\[
  A=P_a.
\]
Thus \(A\) is a postcritically finite hyperbolic quadratic polynomial.

The fixed points of \(A\) satisfy
\[
  z^2-z+a=0,
  \qquad
  A'(z)=2z=1\pm\sqrt{1-4a}.
\]
Since \(a<-7/4\),
\[
  \sqrt{1-4a}>\sqrt8>2.
\]
Consequently,
\[
  \left|1+\sqrt{1-4a}\right|>1,\qquad
  \left|1-\sqrt{1-4a}\right|
  =\sqrt{1-4a}-1>1.
\]
Both fixed points of the named target polynomial \(A\) are repelling.

These calculations are exact. They establish the target parameter and the
target fixed-point condition. They do **not** establish either the primitive
bounded-Fatou-closure hypothesis for Shen--Wang or repelling fixed points for
an arbitrary physical germ merely hybrid equivalent to \(A\).

## 4. The conditional double-tuning construction

Assume temporarily the following bridge:

> **Bridge A.** The airplane center \(A=P_a\) is primitive in the
> Shen--Wang/Inou--Kiwi sense: closures of all distinct bounded Fatou
> components of \(A\) are pairwise disjoint.

Then Shen--Wang applies with base \(f_0=A\). The reduced scheme has one
periodic critical Fatou component with return time three and degree two.
Choose the target generalized polynomial to be \(A\) again. The main theorem
produces a quadratic polynomial
\[
  F=P_c
\]
and an actual physical quadratic-like return map
\[
  G=F^3:U'\longrightarrow U
\]
with connected filled Julia set, externally marked and hybrid equivalent to
\(A\).

This much is a literal consequence of the source once Bridge A is supplied.
It establishes a physical tuned germ; it is stronger than an abstract
hybrid-class existence statement.

To invoke `KL_CANONICAL_LOCALIZATION_FORCED_COLLISION` at the outer stage,
one still needs:

> **Bridge B.** The planar little-Julia cycle
> \[
>    K(G),\quad F(K(G)),\quad F^2(K(G))
> \]
> is pairwise disjoint.

Bridge B is exactly Kahn's primitive-renormalization hypothesis for the
ordinary quadratic \(F\). Shen--Wang's pairwise-disjoint source puzzle
pieces in `revision.tex`, lines 834--846, belong to the base model before
the final semiconjugacy. The final map in lines 895--903 is initially
obtained using a continuous surjection. Therefore, source-puzzle
disjointness cannot simply be pushed through that map without an
injectivity argument. Inou--Kiwi's primitive-lamination machinery is the
right candidate for such an argument, but the exact planar conclusion must
be written.

## 5. Why hybrid equivalence does not finish the KL alignment

Suppose Bridges A and B are granted. Kahn's canonical renormalization of
the ordinary outer seed \(F\) is then defined and its dynamical leg is the
localization of the physical return \(F^3\) at \(K(G)\). The KL
direct-decoration construction still requires three further facts about
the **same physical localized germ**.

### 5.1 Repelling fixed points

The target polynomial \(A\) has two repelling fixed points by Section 3.
Multipliers are not invariants of arbitrary hybrid conjugacy. Therefore,
one may not transfer the inequalities
\[
  |A'(\alpha_A)|>1,\qquad |A'(\beta_A)|>1
\]
to \(G\) merely from \(G\simeq_{\rm hybrid}A\).

A valid proof route is available: choose the postcritically finite preimage
of the postcritically finite hyperbolic target supplied in Inou--Kiwi
`thm_c.tex`, lines 14--18; prove that the resulting physical \(F\) is
hyperbolic; prove that the two fixed points of \(G=F^3|U'\) lie on its
Julia set; then use the theorem that periodic points on the Julia set of a
hyperbolic polynomial-like map are repelling. Those deductions are not
assembled as a literal theorem in the checked source set.

### 5.2 Non-satellite escape

Milnor classifies the airplane component as primitive, and the target
airplane is therefore non-satellite in the standard quadratic
combinatorial sense. KL's usable hypothesis, however, is its concrete
top-puzzle condition:
\[
  G^{qm}(0)\notin Y^1
  \quad\text{for some }m,
\]
with the least such escape defining \(\nu\) and the decoration pieces.

The marked straightening preserves the external marking and rational
lamination, so a proof should transport the target escape itinerary to
\(G\). The checked source statements do not explicitly perform this
translation for the physical tuned germ and KL's particular
\(\alpha\)-puzzle. This is **Bridge C**.

### 5.3 Canonical-localization marking

Kahn's canonical renormalization is a localization of
\((i^3,F^3)\); it is not merely the ordinary quadratic-like map \(G\).
KL then takes a quadratic-like restriction of the localized
\(\psi\)-quadratic-like map and builds rays and puzzle pieces from that
restriction.

The desired same-seed statement is:

> **Bridge D.** The embedded quadratic-like restriction of Kahn's
> canonical localization is the marked germ \(G\) in a neighborhood large
> enough to contain the complete KL top puzzle and the direct-decoration
> pieces \(P,Q_L,Q_R\), with the same cyclic ray marking and escape
> itinerary.

Kahn proves that the localization produces a degree-two
\(\psi\)-quadratic-like map and that the localization map is a covering off
the marked continuum. KL proves that a \(\psi\)-quadratic-like map admits a
quadratic-like restriction. Neither checked statement literally identifies
that restriction, together with the complete KL puzzle marking, with the
pre-localization physical return germ. Thus exact germ/marking alignment
cannot be inferred from a shared hybrid class.

## 6. The most promising proof of the missing outer-disjointness bridge

This section records a proof program, not a promoted theorem.

Let \(\lambda_A\) be the rational lamination of the airplane center.
Milnor's period-three portrait identifies the primitive component. One
should first prove that \(\lambda_A\) is primitive in the Inou--Kiwi sense:
no rational-lamination class meets the closures of two distinct infinite
\(\lambda_A\)-unlinked classes.

Choose the postcritically finite preimage \(F\) of the target \(A\) from
Inou--Kiwi's hyperbolic-surjectivity construction. Combinatorial tuning is
the smallest closed equivalence relation containing:

1. the outer relation \(\lambda_A\); and
2. the pulled-back inner airplane relations within each relevant infinite
   outer unlinked class.

The intended contradiction argument is then:

1. suppose two outer little Julia sets \(F^iK(G)\) and \(F^jK(G)\),
   \(i\ne j\), meet;
2. because \(F\) is postcritically finite, its Julia set is locally
   connected and rational rays encode all relevant landing
   identifications;
3. an intersection point supplies a tuned rational-lamination class
   incident to both corresponding outer unlinked classes;
4. inner tuning relations are inserted within a single outer unlinked
   class and cannot create such a cross-class incidence;
5. the original outer relation cannot create it because
   \(\lambda_A\) is primitive.

The contradiction would prove Bridge B.

Every step must be stated in the exact language of Inou--Kiwi's fibers
\(K_F(v)\). In particular, Step 3 requires a theorem translating an
intersection of two full planar fibers to a rational class incident to both
unlinked classes. It is not enough to say that the labels differ or that
the finite lamination polygons are unlinked. A common irrational boundary
point must also be excluded. Postcritical finiteness/local connectivity is
expected to do this, but the exact landing theorem and its hypotheses must
be cited.

## 7. A possible primitive-airplane bridge and its audit status

There is also a direct topological proof candidate for Bridge A.

Let \(U_0,U_1,U_2\) be the three immediate basins in the superattracting
cycle of \(A\). If two of their closures meet, forward invariance produces
contacts around the entire cycle. If the three contacts are distinct, the
component-attachment graph contains a cycle, contrary to the standard
Hubbard-tree attachment theorem. If all contacts coincide, their common
point is fixed by \(A\), which is incompatible with the primitive
period-three orbit portrait. Distinct preperiodic Fatou components can then
be handled at the first iterate at which their images coincide: away from
the critical point, a local inverse of a Jordan-domain boundary cannot
merge two distinct components, and the unique critical point lies in the
interior of \(U_0\).

This is a plausible complete proof skeleton, but it uses several results
not collected as one checked implication:

- Jordan boundaries for all relevant postcritically finite Fatou
  components;
- the no-cycle attachment/Hubbard-tree statement;
- identification of a common periodic attachment with the orbit-portrait
  root;
- the local pullback argument for all preperiodic components.

It is therefore not silently substituted for a source theorem in this
audit.

## 8. Exact completion theorem required

The alignment may be promoted only after proving the following proposition.

> **Double-airplane marked alignment proposition.** Let \(A=P_a\), where
> \(a\) is the unique real zero in \((-9/5,-7/4)\) of
> \(c^3+2c^2+c+1\). There exists a postcritically finite quadratic
> polynomial \(F=P_c\) and disks \(U'\Subset U\) such that:
>
> 1. \(G=F^3:U'\to U\) is quadratic-like with connected filled Julia set
>    and is externally marked hybrid equivalent to \(A\);
> 2. \(K(G),F(K(G)),F^2(K(G))\) are pairwise disjoint;
> 3. both fixed points of the physical germ \(G\) are repelling;
> 4. \(G\) is non-satellite in KL's top-puzzle definition and has a finite
>    marked escape route;
> 5. Kahn's first canonical localization of \(F\) has an embedded
>    quadratic-like restriction equal to \(G\) as a marked germ on every
>    domain used to form the KL pieces \(P,Q_L,Q_R\).

Clauses 1 and the existence part are source-licensed once the airplane base
is proved primitive. Clauses 2--5 are the missing alignment bridges.

If this proposition is proved, then the already-proved forced-collision
theorem applies to the outer ordinary primitive stage and its exact
pullback propagation reaches the KL direct-decoration depths of that same
canonical seed. This supplies an actual aligned direct-decoration
nonembedding witness.

If any clause fails, the failure certificate must name the first offending
object:

- a touching pair among the three physical little Julia sets;
- a nonrepelling fixed point of \(G\);
- a KL critical orbit which never exits \(Y^1\);
- a ray/prime-end marking changed by localization; or
- a direct-decoration piece leaving the domain on which the localized and
  physical germs agree.

## 9. Dependency and promotion consequence

The audited logical chain is
\[
\begin{aligned}
&\text{primitive airplane base}\\
&\quad+\text{Shen--Wang/IK tuning}\\
&\quad+\text{outer planar disjointness}\\
&\quad+\text{physical KL hypotheses}\\
&\quad+\text{marked canonical-germ identity}\\
&\Longrightarrow
\text{aligned double-airplane KL collision}.
\end{aligned}
\]

Only the tuning existence and marked hybrid-equivalence term is presently
source-locked. The remaining terms are not optional terminology changes;
each is a hypothesis of the downstream theorem.

Therefore:

- do not add an `ALIGNED_DOUBLE_AIRPLANE_KL_COLLISION` proved node;
- do not strengthen the statement of
  `KL_CANONICAL_LOCALIZATION_FORCED_COLLISION`;
- do not cite this candidate as a named counterexample in the manuscript;
- keep the current restricted-class
  `DIRECT_DECORATION_DEGREE_ONE_PSEUDO_EMBEDDING` node open and non-gating;
  and
- retain the unconditional conclusion already proved: Kahn's canonical
  localization inclusion is noninjective at every ordinary primitive
  polynomial seed.  The later Kahn-iterate theorem supplies conditional
  fixed-seed interior alignment whenever a KL direct-decoration stage
  exists; this audit still does not prove that the proposed double-airplane
  seed satisfies the hypotheses needed to produce such a stage.

## 10. Skeptic audit

1. **Named-component shortcut rejected.** Milnor's “primitive component”
   was not silently equated with Shen--Wang's bounded-Fatou-closure
   definition.
2. **Source-puzzle shortcut rejected.** Pairwise-disjoint puzzle pieces for
   the base were not pushed through a merely continuous final
   semiconjugacy.
3. **Fiber-label shortcut rejected.** Distinct schema fibers do not by
   themselves prove disjoint planar little Julia sets.
4. **Hybrid-multiplier shortcut rejected.** Repelling multipliers were
   proved only for the target \(A\), not transferred through a hybrid
   conjugacy.
5. **Primitive/non-satellite shortcut rejected.** Kahn's primitive
   little-Julia condition and KL's finite escape condition were kept
   distinct.
6. **Hybrid-class alignment shortcut rejected.** The target airplane, the
   physical return germ, and the localized canonical seed were not treated
   as literally identical.
7. **Local-germ/domain shortcut rejected.** Agreement near the filled Julia
   set is not yet agreement on every puzzle and decoration domain.
8. **Existence/quantifier shortcut rejected.** A conditional theorem about
   every aligned seed was not turned into an existential realized example.
9. **Obsolete-node shortcut rejected.** The former universal embedding
   claim is no longer the ledger node; no current restricted-class
   classification was declared refuted.
10. **Global overreach rejected.** This audit has no implication for
    VAAPC-I, UPTCR, rigidity, or MLC.

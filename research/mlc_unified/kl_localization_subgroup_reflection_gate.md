# KL localization: subgroup reflection and the forced canonical collision

## 1. Result and scope

This note identifies the exact covering-space condition for a localization
lift whose underlying map has independently been proved to be a physical
embedding.  At a general bold \(\psi\)-ql stage KL supplies an immersion,
so realization as such an embedding lift is a separate prerequisite.

There are now two distinct conclusions.  The abstract criterion below
remains valid for any independently specified pair of covers.  For Kahn's
**full canonical localization** of an ordinary primitively renormalizable
quadratic-like stage, however, the reflection equality is not merely
unproved: the forced-collision theorem below proves that it is false.
Consequently the old universal full-embedding route is unavailable and is
not a gate toward the global argument.

### Theorem 1.1 — subgroup-reflection criterion

Let \(X_s,X_t\) be connected, locally path-connected, semilocally simply
connected spaces.  Let

\[
 p_s:\widetilde X_s\to X_s,
 \qquad
 p_t:\widetilde X_t\to X_t
\]

be connected based covers, corresponding to subgroups

\[
 H_s\leq\pi_1(X_s,x_s),
 \qquad
 H_t\leq\pi_1(X_t,x_t).
\]

Let \(a:(X_s,x_s)\hookrightarrow(X_t,x_t)\) be a based embedding and let

\[
 A:\widetilde X_s\longrightarrow\widetilde X_t
\]

be a based lift satisfying

\[
 p_t\circ A=a\circ p_s.
\tag{1.1}
\]

Existence of \(A\) gives

\[
 a_*(H_s)\subseteq H_t.
\tag{1.2}
\]

Then

\[
 \boxed{
 A\text{ is injective}
 \quad\Longleftrightarrow\quad
 a_*^{-1}(H_t)=H_s.
 }
\tag{1.3}
\]

If equality fails, every class

\[
 [\gamma]\in a_*^{-1}(H_t)\setminus H_s
\tag{1.4}
\]

is an exact collision certificate: the lift of \(\gamma\) to
\(\widetilde X_s\) has distinct endpoints, and \(A\) identifies those
endpoints.

The theorem is an abstract covering-space criterion.  Its KL application
is conditional on identifying the relevant bold inclusion as the lift of
the specified physical embedding between the specified covers.  It does
not assert the missing equality (1.3) for a KL stage.

### Corollary 1.2 — conditional revised-or-restricted route

At every KL localization stage whose underlying map is a physical
embedding \(a\), suppose the source and target localization covers satisfy

\[
 a_*^{-1}(H_t)=H_s.
\tag{1.5}
\]

Then the localized inclusion is an embedding on the covered complementary
component.  If (1.5) holds through the complete direct-decoration horizon,
then all induced degree-one universal-cover tile maps are injective.
Together with the already proved component-bijection and gluing criterion,
this proves the corresponding fixed pseudo-piece inclusion is an interior
holomorphic embedding.

Kahn and Kahn--Lyubich prove the inclusion (1.2), which is needed for a
lift to exist.  The checked sources do not prove the reflection equality
(1.5).  The following source-locked theorem proves its failure for the
canonical primitive stage.

### Theorem 1.3 — forced canonical subgroup defect

Let \(f:U^1\to U^0\) be an ordinary quadratic-like restriction of a
quadratic polynomial which is primitively renormalizable of period
\(p>1\).  Put

\[
 F=f^p:U^p\longrightarrow U^0,\qquad
 a=i^p:U^p\hookrightarrow U^0,
\]

\[
 A=K_p,\qquad
 B=\mathcal K_p=\bigcup_{j=0}^{p-1}f^j(A).
\tag{1.6}
\]

For Kahn's canonical localization, the complementary source and target
surfaces are

\[
 \Omega_s=U^p\setminus F^{-1}B,\qquad
 \Omega_t=U^0\setminus B.
\tag{1.7}
\]

Let \(H_s,H_t\) be the corresponding based localization subgroups.  Then
there is a based loop \(\gamma\subset\Omega_s\) such that

\[
 [\gamma]\in a_*^{-1}(H_t)\setminus H_s.
\tag{1.8}
\]

Hence the full canonical localized inclusion is noninjective.

The exact geometric certificate is as follows.  The global degree of
\(F\) is \(2^p\), while its degree on the central pullback \(A\) is two.
Therefore \(F^{-1}A\) has an excess component \(X\ne A\).  Primitive
disjointness and \(F(f^jA)=f^jA\) give

\[
 X\cap B=\varnothing.
\tag{1.9}
\]

The finite full-pullback theorem gives a finite pairwise-disjoint family of
full components of \(F^{-1}B\).  Thus one can choose a Jordan domain
\(D_X\Subset U^p\) containing \(X\) and disjoint from
\((F^{-1}B\setminus X)\cup B\).  Conjugating
\(\partial D_X\) to the localization basepoint gives \(\gamma\).
Its winding number about \(X\) is one, whereas every loop from the source
local subgroup has winding number zero about \(X\); hence
\([\gamma]\notin H_s\).  In the target, \(D_X\cap B=\varnothing\), so
\(a\gamma\) contracts through \(D_X\subset\Omega_t\).  Thus
\(a_*[\gamma]=1\in H_t\), proving (1.8).  Theorem 1.1 then gives two
distinct source-cover endpoints with one target endpoint.

The complete component, fullness, isolating-disk, winding, and exact
pullback-propagation proofs are source-locked in
`kl_canonical_localization_forced_collision.md`.  In particular, this is
an actual canonical KL localization collision, not an abstract annulus
countermodel.

The minimal state which must survive any replacement is

\[
 \mathscr S_{\rm loc}
 =
 a_*^{-1}(H_t)/H_s.
\tag{1.10}
\]

Here (1.10) denotes the pointed coset set; it is not asserted to be a
quotient group unless normality is proved.  Its non-base cosets record
source sheet displacements erased by target localization.  A ribbon-tree
or carrier quotient which collapses this set loses the proved analytic
obstruction.

The subsequent theorem
`KL_LOCALIZATION_SHEET_RESOLUTION_FACTORIZATION` constructs this state
canonically.  With \(K=a_*^{-1}(H_t)\), the localized lift factors as

\[
 \widehat X_s\xrightarrow qP_K\xrightarrow e\widehat X_t,
 \qquad A=e\circ q,
\]

where \(q\) is the \(H_s\)-to-\(K\) covering, \(e\) is embedded, and the
kernel pairs of \(A\) and \(q\) agree.  The cover monodromy, rather than
any unproved quotient-group operation, is the exact transport groupoid.
For the actual canonical seed, winding separates the powers of the
peripheral class and proves

\[
 [K:H_s]=\infty.
\]

Thus the required state is not a finite raw sheet list.  Exact base change
propagates the factorization through full, unselected Kahn equalizers on
the complementary-cover locus.  Selected direct-decoration component
alignment, filled completion, and prime-end realization remain open.

The intended universal full-canonical formulation of
`DIRECT_DECORATION_DEGREE_ONE_PSEUDO_EMBEDDING` is therefore unavailable
as a proof route.  Conditional retained-collar embedding statements remain
valid under their own hypotheses.  VAAPC-I, UPTCR, and MLC remain open.

## 2. Proof of Theorem 1.1

Choose base lifts

\[
 \widetilde x_s\in p_s^{-1}(x_s),
 \qquad
 \widetilde x_t=A(\widetilde x_s).
\]

The standard lifting criterion says that the based lift \(A\) exists if
and only if

\[
 a_*\bigl(p_{s*}\pi_1(\widetilde X_s,\widetilde x_s)\bigr)
 \subseteq
 p_{t*}\pi_1(\widetilde X_t,\widetilde x_t),
\]

which is exactly (1.2).

### 2.1 Reflection equality implies injectivity

Assume

\[
 a_*^{-1}(H_t)=H_s.
\tag{2.1}
\]

Let \(\widetilde u,\widetilde v\in\widetilde X_s\) satisfy

\[
 A(\widetilde u)=A(\widetilde v).
\tag{2.2}
\]

Projecting (2.2) and using (1.1),

\[
 a(p_s(\widetilde u))
 =
 p_t(A(\widetilde u))
 =
 p_t(A(\widetilde v))
 =
 a(p_s(\widetilde v)).
\]

Since \(a\) is injective,

\[
 p_s(\widetilde u)=p_s(\widetilde v)=u.
\tag{2.3}
\]

Choose paths \(\widetilde\alpha,\widetilde\beta\) in
\(\widetilde X_s\) from \(\widetilde x_s\) to
\(\widetilde u,\widetilde v\), respectively, and write

\[
 \alpha=p_s\circ\widetilde\alpha,
 \qquad
 \beta=p_s\circ\widetilde\beta.
\]

By (2.3), both \(\alpha\) and \(\beta\) run from \(x_s\) to \(u\).
The source endpoints agree,

\[
 \widetilde u=\widetilde v,
\]

if and only if the loop

\[
 \gamma=\alpha\cdot\beta^{-1}
\]

has class in \(H_s\).

On the target side, \(A\circ\widetilde\alpha\) and
\(A\circ\widetilde\beta\) are the lifts, from the same base lift, of
\(a\circ\alpha\) and \(a\circ\beta\).  Equation (2.2) says that their
endpoints agree.  Therefore

\[
 a_*[\gamma]\in H_t.
\]

By (2.1),

\[
 [\gamma]\in H_s.
\]

Hence \(\widetilde u=\widetilde v\), and \(A\) is injective.

### 2.2 Injectivity implies reflection equality

Assume \(A\) is injective.  Inclusion (1.2) gives

\[
 H_s\subseteq a_*^{-1}(H_t).
\tag{2.4}
\]

For the reverse inclusion, let

\[
 [\gamma]\in a_*^{-1}(H_t).
\]

Lift \(\gamma\) from \(\widetilde x_s\) and denote its endpoint by
\(\widetilde y_s\).  The path \(A\circ\widetilde\gamma\) is the lift of
\(a\circ\gamma\) from \(\widetilde x_t\).  Since
\(a_*[\gamma]\in H_t\), this target lift is closed.  Consequently

\[
 A(\widetilde y_s)=A(\widetilde x_s).
\]

Injectivity of \(A\) gives

\[
 \widetilde y_s=\widetilde x_s.
\]

Thus the source lift of \(\gamma\) is closed, so

\[
 [\gamma]\in H_s.
\]

This proves

\[
 a_*^{-1}(H_t)\subseteq H_s.
\]

Together with (2.4), it proves (1.3).

### 2.3 Exact failure certificate

If

\[
 [\gamma]\in a_*^{-1}(H_t)\setminus H_s,
\]

then the source lift of \(\gamma\) begins at
\(\widetilde x_s\) and ends at a distinct point
\(\widetilde y_s\), while the target lift of \(a\circ\gamma\) is closed.
Therefore

\[
 \widetilde y_s\neq\widetilde x_s,
\qquad
 A(\widetilde y_s)=A(\widetilde x_s).
\tag{2.5}
\]

This is a point-level collision, not merely a failure of a label map.
The loop class records the exact sheet displacement that becomes invisible
after target localization.

## 3. Equivalent path-reflection formulation

Let \(\alpha,\beta\) be source paths with the same endpoints.  Their lifts
from one source lift have the same endpoint exactly when

\[
 [\alpha\beta^{-1}]\in H_s.
\]

Their target images have lifts with the same endpoint exactly when

\[
 a_*[\alpha\beta^{-1}]\in H_t.
\]

Thus (1.3) is equivalent to:

\[
 \boxed{
 \text{target equivalence of two source paths}
 \Longrightarrow
 \text{source equivalence of those paths}.
 }
\tag{3.1}
\]

This is the homotopy-reflection direction.  Functoriality supplies the
opposite implication automatically:

\[
 \text{source equivalence}
 \Longrightarrow
 \text{target equivalence}.
\tag{3.2}
\]

The distinction between (3.1) and (3.2) is the central logical point.

## 4. Source-locked KL compatibility universe

The complete active TeX inputs of Kahn I and Kahn--Lyubich II were searched.
The source archives are:

```text
.tmp_kl06_source.tar
SHA256 3A63FC9773DB8B60ED4A0EB9A1C551E6F66C08E66AB92C36F4E2B482570AB817

.tmp_kl08_source.tar
SHA256 DA8FCF924793267421F80BE3E17CD7EB2B72CD4F5B08E3F5A38E2161EC608234
```

### 4.1 Ordinary quadratic-like nesting

Kahn I `pullback.tex`, lines 2--7 and 25--36, has literal physical nesting
and an inclusion embedding.  It also warns that the natural triangle made
from dynamics and inclusions is not a commuting triangle.  This physical
model cannot simply be substituted for a later bold localization map.

### 4.2 Abstract \(\psi\)-ql definition

Kahn I `psiql2.tex`, lines 15--41, assumes an immersion \(i\), a proper
degree-\(d\) branch \(f\), and the common inverse

\[
 i^{-1}(K)=f^{-1}(K)=K'.
\]

It supplies no global factorization between \(i\) and \(f\).
`psi_ql_global_injectivity_no_go.md` proves by an explicit complete
\(\psi\)-ql pair that these axioms do not force global injectivity.

### 4.3 Genuine Cartesian pullback iteration

`psiql2.tex`, lines 188--301, constructs the categorical pullback and proves
that injectivity is inherited by the opposite pullback leg when an input
map is already injective.  Lines 350--416 construct the iterated squares

\[
 i_n\circ f_{n+1}=f_n\circ i_{n+1}.
\]

These squares are genuine pullbacks.  They preserve an embedding already
present at the input.  They do not prove that a later localization map,
which is only known to be an immersion, is embedded.

### 4.4 Localization is functorial, not asserted Cartesian

`psiql2.tex`, lines 430--505, constructs localization covers and a unique
commuting lift

\[
 \pi_t\circ\widehat a=a\circ\pi_s.
\]

The theorem calls this construction functorial and says that localization
preserves immersions.  It does not assert that the naturality square is a
pullback, and it does not state (1.5).  Theorem 1.3 now proves that (1.5)
fails for the full canonical primitive localization.

### 4.5 Dynamical localization retains the same gap

`psiql2.tex`, lines 510--546, concludes that the localized \(i\)-leg is an
immersion and the localized \(f\)-leg is a branched cover.  The listed
obstacle hypothesis is one-sided.  No component-exhaustion or
subgroup-reflection equality is supplied.

### 4.6 Path-space formulation proves only the forward direction

`psiql2.tex`, lines 612--619, observes that applying the source map sends a
valid source path to a valid target path and sends equivalent source paths
to equivalent target paths.  This is (3.2).

The converse (3.1), which is exactly what injectivity needs, is not stated
or proved.

### 4.7 Only limited end properness is used

Kahn I `conclusions.tex`, lines 33--49, explicitly says that the former
embedding has become an immersion.  The proof uses properness only at ends
corresponding to little Julia sets.  A statement that the immersion is
homotopic to a homeomorphism controls degree and peripheral homotopy
classes; it does not imply point injectivity.

### 4.8 KL II keeps the dynamical and inclusion arrows separate

KL II `psiql.tex`, lines 95--161 and 169--207, constructs:

- a branched covering induced by dynamics; and
- an immersion induced by inclusion.

For the inclusion arrow, the component map is explicitly “surjective but
not necessarily injective,” and the universal-cover tile maps are called
immersions.  The isomorphism theorem for the dynamical tile arrow does not
transfer to the inclusion arrow.

### 4.9 Outer-end behavior remains uncontrolled

KL II `psiql.tex`, lines 248--253, permits source ideal boundary to map
into target interior.  `moduli.tex`, lines 420--443, uses maximal initial
lifts that may terminate at a source \(O\)-boundary.  These statements are
incompatible with silently assuming full outer-end properness.

### 4.10 Direct-decoration physical branches do not identify the arrows

KL II `kingdom.tex`, lines 133--155, gives univalent physical dynamical
branches \(Q_L,Q_R\to P\).  Their induced bold dynamical maps are
isomorphisms by `psiql.tex`, lines 186--196.  The inclusion-induced bold
map is the separate immersion of lines 198--206.  No source identity
equates those two arrows.

## 5. Properness as a stronger analytic substitute

If the relevant bold complementary-annulus immersion is proper and has
degree one, then it is a biholomorphism:

1. a holomorphic immersion is a local biholomorphism, hence open;
2. a proper map into a Hausdorff locally compact target is closed;
3. the image is nonempty, open, and closed in a connected annulus, hence
   is the whole annulus;
4. a proper local biholomorphism is a finite covering; and
5. degree one makes it one-sheeted.

Thus full outer-end properness, together with the already controlled inner
end, would discharge the abstract gate.  It cannot hold for the full
canonical map of Theorem 1.3, because that map already has a point
collision.  The checked KL arguments use only selected inner-end
properness, and their conditional embedded-collar conclusion is not
affected.

## 6. Failure classifications

There are now three sharply separated failure levels.

### 6.1 Abstract annulus failure

`KAHN_ANNULUS_GLOBAL_INJECTIVITY_NO_GO` shows that Kahn's annulus-lemma
hypotheses do not imply global injectivity.

### 6.2 Full abstract \(\psi\)-ql failure

`PSI_QL_GLOBAL_INJECTIVITY_NO_GO` shows that even the proper companion map
and exact common connected pullback do not imply global injectivity.

### 6.3 Actual canonical KL localization failure

For the full canonical primitive localization, the underlying map is the
physical embedding \(a=i^p\), and Theorem 1.3 supplies the exact cover
obstruction

\[
 [\gamma]\notin H_s,
 \qquad
 a_*[\gamma]\in H_t.
\]

Equivalently, two source-distinct path classes become target-equivalent.
Thus subgroup reflection, Cartesianity of the same localization square,
and full proper degree-one embedding are all impossible for this full
canonical map.  If a different bold map is only an immersion, a base
collision remains an independent obstruction not detected by subgroup
reflection.

The winding computation in Theorem 1.3 certifies
\([\gamma]\notin H_s\).  A finite boundary label, an inner-collar
embedding, or one-sided properness cannot erase or quotient away the
resulting non-base coset.

## 7. Project consequence

The full canonical-localization embedding route is closed negatively.
For that map one may not continue by trying to prove subgroup reflection,
Cartesianity of the unchanged square, or full outer-end properness: the
explicit class (1.8) disproves all three required conclusions.

A replacement must instead do at least one of the following:

1. synchronize the source and target obstacle packets and then recompute
   both localization subgroups;
2. work with a sheet-sensitive immersion whose state retains
   \(a_*^{-1}(H_t)/H_s\);
3. restrict to a separately proved embedded inner collar while charging
   every discarded coset, sheet, access, and width contribution; or
4. retime or revise the interface and repeat the complete horizon and
   final-root audit.

The full collision certificate consists of the excess component \(X\),
its isolating access \(\partial D_X\), its complete \(p\)-step itinerary,
the class \([\gamma]\), the two distinct source endpoints, their common
target endpoint, and the non-base coset of (1.10).  No replacement may
quotient this information away.

Theorem 1.3 rejects one universal embedding architecture.  It proves no
Wave-horizon exhaustion, width estimate, compactness, rigidity, or
parameter shrinking.  No global MLC obligation is promoted.

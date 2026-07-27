# KKL stationary typed paired-Wave realization: construction attempt, mode exhaustion, and exact obstruction

## Post-audit status correction (2026-07-26)

This construction attempt remains an optional stronger route.  The
later native-proof audit identifies
`KKL_STATIONARY_RELATIVE_WAVE_CONTINUATION` as the immediate Gate N1 and
does not consume doubled-width paired response at line 1603.  The
cyclic-cover audit also refutes the broad coefficient-one source-Wave
theorem on which a completed paired response would otherwise rely.
Nothing below promotes the typed realization or makes it part of the
active native dependency.

## 1. Verdict and status

This pass attempts the actual obligation

```text
KKL_STATIONARY_TYPED_PAIRED_WAVE_REALIZATION.
```

It does not prove that obligation.

The source-checkable result is more precise than a generic “missing
geometry” verdict:

\[
\boxed{
\begin{minipage}{0.90\linewidth}
The already proved survivor partition, segmented-occurrence
reconstruction, access-seeded continuation theorem, and
Freudenthal/access type audit do not construct a width-faithful
paired-Wave realization.

At native family level, the first absent object is a width-faithful
single-valued marked occurrence presentation of the physical survivor
leaves.  Conditional on such a presentation, the first absent
source-geometric map is a Borel bilateral component selector
\[
 \sigma_h^\pm:
 \Lambda_h\longrightarrow
 \operatorname{Comp}_{\rm prop,mark}
 \bigl(I_h^{-1}(|\gamma^\pm_\lambda|)\bigr)
\]
whose selected components realize the two complete untrimmed portions
at the same actual \(L_0^h\) occurrence.

`DIRECT_WAVE` merely supplies this map as part of its input.
`ACCESS_LOCAL` presently supplies only the continuity and Borel
behavior of maximal continuation after continuous product seeds have
already been constructed; it does not prove whole-portion landing,
properness, marking survival, or full-width exhaustion.
`FREUDENTHAL` cannot be started from a marked access without a new
access-splitting localization and, even after legitimate fixed ends are
supplied, the fixed-end WAD theorem does not force the two orientations
to exit at one common occurrence.

Once genuine source Waves exist, the whole-ending-multi-interval
degree clause is not a further obstruction: the global covering bound
\(\deg P_h\le 2^h\) bounds the degree on each actual ending
multi-interval.
\end{minipage}}
\tag{1.1}
\]

The obstruction is a **source-derivability obstruction**, not an
example of a KKL dynamical block in which the desired pair is false.
Two exact analytic models and one finite dependency model below show
that the missing implications cannot be obtained from the currently
listed abstract hypotheses alone.

No ledger or manuscript file is changed in this pass.  In particular,
the following remain open:

- `KKL_STATIONARY_TYPED_PAIRED_WAVE_REALIZATION`;
- `KKL_STATIONARY_BL0_UNIFORM_SURVIVOR_RESPONSE`;
- `KKL_STATIONARY_SURVIVOR_EXCLUSION_OR_CHARGE`;
- the stationary repair used by VAAPC-I;
- `VAAPC-I`;
- `UPTCR`; and
- `MLC`.

## 2. Locked sources and imported scope

The active source files are:

```text
.tmp_wave_audit/waves-with-Misha.tex
SHA-256 AD4C774806D9902AA54FA31C56AD6146D8034946F19CC5E9CEC3C51A3F94FDD5

.tmp_wave_audit/not-all-good2.tex
SHA-256 B5D40812E40D2E44037A8FC249DB687211CD67275E66EFFF8E7F29BC7CEDFB01

.tmp_kl06_source/appendix.tex
SHA-256 EA2BE5CC544100D7931C9992E7ED476EBBE4CCE52FAF620BFF357071CB3916F3

.tmp_kl06_source/wad.tex
SHA-256 B5DF40A5D33B6B590B430D47693514088AF6FC287BAA5D87B4D11015B990E580

.tmp_kl06_source/psiql2.tex
SHA-256 E4EFCCEC65D8C9C2BDFE2AF8203B3D4D63ECF992B40D302F56FBA78259547228
```

The exact KKL clauses used are:

| source lines | imported content | excluded inference |
|---|---|---|
| master 406 | a proper path has two ideal-boundary limits | escape from compacta is not automatically properness |
| 439--461 | pseudo-quadratic-like maps and finite relation towers | an immersion is not globally injective |
| 1225--1274 | the complementary-surface covering/immersion and pulled marking | an interval itinerary is not a path selector |
| 1355--1358 | breaking and \(N\)-unbreakability | one untagged output does not remember its occurrence |
| 1547--1548 | \(N=b+3\), \(A_0\), and \(A_n\) for \(0<n<N\) | the printed \(A_N\) at line 1605 is not used |
| 1597--1603 | \(K_0^n,L_0^n\), one restriction ending at \(L_0^n\), and the proposed two-portion argument | line 1603 is not used as a proved pair theorem |
| 1839--1875 | ideal markings, proper paths, laminations, and Waves | a marked access is not a Freudenthal end |
| 2065--2078 | covering pushforward and the degree-loss estimate | the lemma does not construct its source lamination |
| 2080--2097 | set-valued immersion restriction and both marking filters | an inverse component need not survive the filters |
| 2099--2108 | the three-way interval-itinerary alternative | adjacency and common-pullback alternatives are not path occurrences |
| 2149--2152 | Wave pushforward from an already constructed source Wave | no source Wave is created by this lemma |

The fixed-end theorem is
`not-all-good2.tex`, lines 514--545.  It starts with an already chosen
set of source **Freudenthal ends** on which the immersion is proper of
degree one.  It then lifts an oriented realizing foliation until exit
and assembles a valid source WAD.  It does not select a marked access,
construct an access localization, or identify two opposite exits.

The KL06 inputs are:

- `wad.tex`, lines 83--160: arcs, valid WADs, and Borel proper
  laminations;
- `wad.tex`, lines 404--443: restriction of an already realizing
  foliation and Series-law domination;
- `appendix.tex`, lines 12--88: extremal length/width, Series and
  Parallel laws, and holomorphic monotonicity; and
- `psiql2.tex`, lines 188--214, 259--265, and 350--421: the finite
  equalizer/pullback relation.

A valid KL06 WAD supplies a Borel union of proper leaves.  It does not,
by definition alone, supply a countable partition into continuous
product rectangles, a selected immersion sheet, or a Borel
occurrence map.

The project files used as proved reductions are:

```text
kkl_stationary_bl0_survivor_analysis.md
SHA-256 5F94E965B612B710DF24B643ACDFB79FC3FC216BE0127FFA4D9C4176CB544C48

kkl_stationary_segmented_occurrence_binder.md
SHA-256 2C8B17AC7EC73912DB6EAD2E46702D8F9F570C16EE54759B266A26E8CBBD965A

kkl_stationary_route_exit_invariant.md
SHA-256 786DC781CEAA4CDFD54D2004D112362A1D82F5FFABD0E165A5FC7D71D64C3D09

kkl_stationary_fixed_end_topological_obstruction.md
SHA-256 9284C52BC7E954DF0B1E211B5CFF1124B1F3878CAA103E5CB1F47A612479A6E2

kkl_access_seeded_maximal_lift_measurability.md
SHA-256 2460ABCB137BC04987932731E0B40F26BBFC28CEBE8A403A7AED9472D66C65FF
```

Every conclusion below is restricted to the stated hypotheses of those
files.

## 3. Native stationary data and the exact target family

### 3.1 Maps, horizons, and source indexing

Fix one parabolically \(b\)-bounded stationary KKL block.  Put

\[
\begin{aligned}
 X_0&=\mathcal U\setminus\mathcal T,\\
 X_h&=\mathcal U^h\setminus\mathcal T^h,\\
 P_h&=f^h:X_h\longrightarrow X_0,\\
 I_h&=\iota_h:X_h\longrightarrow X_0,\\
 N&=b+3,\qquad m_{\rm rt}=N-1=b+2.
\end{aligned}
\tag{3.1}
\]

Here \(P_h\) is an unbranched finite covering on the complementary
surfaces, while \(I_h\) is a holomorphic immersion.  The safe covering
bound is

\[
 D_h:=\deg P_h\le 2^h.
\tag{3.2}
\]

KKL define

\[
 A_0=A^{N\text{-nbr}}\setminus A^{\rm sh}
\tag{3.3}
\]

and, for \(0<n<N\), the nested subwave \(A_n\subset A_{n-1}\) maximal
with \(F_*^nA_n\) a Wave ending at \(BL_0\).

The line-1603 call uses \(\alpha\in A_{n+1}\).  Since \(A_{n+1}\) must
be defined, its complete deep range is

\[
 b\le n\le b+1,
 \qquad
 h=n+1\in\{b+1,b+2\}.
\tag{3.4}
\]

No \(A_N\) is introduced.

### 3.2 Two different “survivor” universes

There are two related but nonidentical objects in the project.

First, on a **supplied** width-faithful marked occurrence presentation
\((\Omega,\pi_A)\), the route-exit survivor is

\[
 E_A^{\rm surv}
 =
 \left\{
 \omega\in\Omega:
 \beta_N(\pi_A(\omega))=\infty,\
 q_{\rm sh}(\omega)=0
 \right\}.
\tag{3.5}
\]

The predicate \(\beta_N=\infty\) means that the native filtered
ambient image remains a singleton through \(N\); it is not a statement
that one named marked route survives.

Let \(q_{BL}\) be the raw, not quotient-only, predicate that the
proof-used replacement at the selected horizon is a Wave ending at
\(BL_0\), with an actual declared \(L_0^h\) occurrence.  The exact
typed target of the ledger obligation is

\[
 \Omega_{\rm BL,surv}
 =
 E_A^{\rm surv}\cap q_{BL}^{-1}(\{1\}).
\tag{3.6}
\]

If the occurrence presentation implements the required first-failure
priority, define

\[
 \Omega_h
 =
 \{\omega\in\Omega_{\rm BL,surv}:h(\omega)=h\}.
\tag{3.7}
\]

The map \(\pi_A:\Omega\to\Lambda_A\) is required to be injective.
Consequently the sets (3.7) are disjoint at the level of physical
leaves and cannot count one leaf at two horizons.

Second, the native line-1603 argument has the source-language
failure set

\[
 \widetilde{\mathcal R}_{1603}
 =
 \left\{
 (n,\alpha):
 b\le n\le b+1,\ 
 \alpha\in A_{n+1},\
 \neg\operatorname{Pass}_n(\alpha)
 \right\}.
\tag{3.8}
\]

The symbol \(\operatorname{Pass}_n\) deliberately retains KKL's phrase
“passes through \(K_0^n\).”  The source does not type that phrase as
physical intersection, component incidence after removing
\(\mathcal K^h\), or a proper path ending on a selected component.
Those predicates are not interchangeable.

Thus (3.8) is a source-language set, not yet a measurable marked
lamination.  A proof using it quantitatively must supply:

\[
\mathsf{PT}:
\quad
\operatorname{Pass}_n
\text{ is an actual geometric Borel predicate with the meaning used
by the later component-extraction argument.}
\tag{3.9}
\]

### 3.3 The missing scope bridge

The statement “the entire nonshort ambient-singleton
\(BL_0\)-ending survivor” is stronger than the source statement for
one \(\alpha\in A_{n+1}\).  To apply the line-1603 geometry to all of
(3.6), one needs a Borel scope map

\[
 e:\Omega_{\rm BL,surv}\longrightarrow\{b+1,b+2,\mathsf{charged}\}
\tag{3.10}
\]

such that:

1. if \(e(\omega)=h\), then
   \(\pi_A(\omega)\in A_h\);
2. the proof-used deep occurrence is the actual \(L_0^h\) occurrence
   used by the source separator argument;
3. the corresponding line-1603 antecedent is satisfied;
4. if \(e(\omega)=\mathsf{charged}\), the leaf is assigned once to an
   independently valid \(V(F)\)-, \(R(F)\)-, or zero-width class; and
5. \(e\) preserves the native transverse-width accounting.

None of the four dependencies of
`KKL_STATIONARY_TYPED_PAIRED_WAVE_REALIZATION` constructs (3.10).
The pointwise survivor switch says that a retained replacement exists;
it does not put every replacement into a deep \(A_h\) occurrence.

This is a separate coverage gate.  The rest of the construction attempt
is conditional on a supplied width-faithful \(\Omega_h\) whose leaves
really are eligible for the declared deep occurrence.

## 4. Borel first-horizon and target-splitting reduction

This section proves what can be proved once an actual continuous
product presentation and a unique crossing have been supplied.

### Lemma 4.1 (Borel hit sets on a continuous product piece)

Let \(\Lambda\) and \(Y\) be second-countable metric spaces, and

\[
 \Phi:\Lambda\times(0,1)\longrightarrow Y
\tag{4.1}
\]

continuous.  Let \(K\subset Y\) be closed.  Then

\[
 H_K=
 \{\lambda\in\Lambda:
   \Phi(\{\lambda\}\times(0,1))\cap K\ne\varnothing\}
\tag{4.2}
\]

is Borel.

#### Proof

For \(m\ge3\), put

\[
 R_m=
 \{(\lambda,t)\in\Lambda\times[1/m,1-1/m]:
   \Phi(\lambda,t)\in K\}.
\tag{4.3}
\]

The set \(R_m\) is closed in
\(\Lambda\times[1/m,1-1/m]\).  Projection from a product with a compact
second factor maps closed sets to closed sets: if
\(\lambda_j\to\lambda\) and
\((\lambda_j,t_j)\in R_m\), compactness gives a subsequence
\(t_{j_k}\to t\), and closedness gives \((\lambda,t)\in R_m\).
Therefore \(\operatorname{pr}_\Lambda(R_m)\) is closed.

Every \(t\in(0,1)\) belongs to
\([1/m,1-1/m]\) for some \(m\), so

\[
 H_K=\bigcup_{m\ge3}\operatorname{pr}_\Lambda(R_m).
\tag{4.4}
\]

It is \(F_\sigma\), hence Borel. \(\square\)

### Lemma 4.2 (Borel unique-occurrence split)

Retain (4.1).  Assume:

1. every path
   \(\alpha_\lambda(t)=\Phi(\lambda,t)\) is embedded;
2. distinct path images are disjoint;
3. \(L\subset Y\) is closed; and
4. for every \(\lambda\), there is exactly one
   \(t_L(\lambda)\in(0,1)\) with
   \(\Phi(\lambda,t_L(\lambda))\in L\).

Then \(t_L:\Lambda\to(0,1)\) is Borel.  The fields

\[
\begin{aligned}
 \gamma^-_\lambda(u)
 &=
 \Phi\bigl(\lambda,u\,t_L(\lambda)\bigr),\\
 \gamma^+_\lambda(u)
 &=
 \Phi\bigl(\lambda,t_L(\lambda)
             +u(1-t_L(\lambda))\bigr),
 \qquad 0<u<1,
\end{aligned}
\tag{4.5}
\]

are Borel path fields.  For each \(\lambda\), their untrimmed open
images are disjoint and their union omits only the common occurrence
point.

#### Proof

For rational \(a\in(0,1)\),

\[
\{\lambda:t_L(\lambda)<a\}
=
\{\lambda:
 \exists t\in(0,a),\ \Phi(\lambda,t)\in L\}.
\tag{4.6}
\]

As in Lemma 4.1, the right side is a countable union of projections of
closed sets over compact parameter intervals contained in \((0,a)\).
It is Borel.  Therefore \(t_L\) is Borel.

The two evaluation maps in (4.5) are compositions of the continuous
map \(\Phi\) with Borel maps of \((\lambda,u)\), so they are jointly
Borel.  If, in addition, the compact-open path space used here is
standard Borel (for example a Polish \(C((0,1),Y)\) model obtained from
a compatible complete separable metric on \(Y\)), then the maps
\(\lambda\mapsto\gamma_\lambda^\pm\) are Borel as path-valued maps:
the Borel sigma-algebra is generated by evaluation at a countable dense
set of parameter values, and every such evaluation is Borel by (4.5).
Without this path-space hypothesis, only the jointly Borel evaluation
fields asserted in the first sentence are used.  Since
\(\alpha_\lambda\) is embedded and

\[
 (0,t_L(\lambda))
 \cap
 (t_L(\lambda),1)=\varnothing,
\tag{4.7}
\]

the two open images are disjoint.  The unique common limiting point is
not in either open image. \(\square\)

### Corollary 4.3 (conditional first-horizon accounting)

Suppose the eligible survivor family is partitioned into finitely or
countably many product pieces satisfying Lemma 4.1, each relevant
pass-through predicate is a closed-set hit predicate on those pieces,
and each declared \(L_0^h\) occurrence satisfies Lemma 4.2 with its
two marked accesses recorded.

Then:

1. the least eligible horizon is Borel;
2. its horizon fibers are Borel;
3. each physical leaf occurs in exactly one fiber;
4. (4.5) supplies Borel, pairwise disjoint, untrimmed target portions;
   and
5. no target width is lost merely by the first-horizon partition or
   by the split, because every leaf of the supplied transversal is
   retained exactly once.  This means that the original target packet
   is unchanged as a curve family; it does not assert
   \(\mathcal W(\{\gamma_\lambda^\pm\})=\mathcal W(S)\).

#### Proof

Lemma 4.1 makes each finite-horizon eligibility predicate Borel.
Taking the least member of a finite ordered set gives Borel fibers by
finite Boolean operations.  Injectivity of the physical-leaf
presentation gives (3).  Lemma 4.2 gives (4).  The construction neither
removes nor duplicates a transversal element, proving (5) at the
target-family level. \(\square\)

### Qualification 4.4

Corollary 4.3 is not an instantiation on the KKL residual.

The source has not proved:

- the width-faithful occurrence presentation \(\Omega\);
- the scope map (3.10);
- a continuous product exhaustion of the relevant survivor WAD;
- a unique physical crossing of the selected \(L_0^h\) component;
- two distinct marked accesses at that crossing; or
- zero width of excluded seams or exceptional leaves.

If a leaf touches, travels along, leaves and reenters, or encounters the
same continuum more than once, hypothesis 4 of Lemma 4.2 fails.  A
coarse \(L_0^h\) label cannot choose one occurrence.

## 5. The common direct realization certificate

All three start modes must ultimately produce the same analytic object.

Fix one Borel horizon packet \(\Lambda_h\), its target paths
\(\alpha_\lambda\), and a Borel split
\(\gamma_\lambda^\pm\) as in (4.5).  Let

\[
 \mathscr P_h^{\rm mark}
\tag{5.0}
\]

be a supplied standard-Borel atlas of parametrized source paths,
restriction components, source sheets, accesses, and segmented
occurrence records.  Calling a selector below Borel is meaningful only
relative to this atlas; the finite response alphabet does not construct
it.  Let

\[
\mathcal C_h^\epsilon(\lambda),
\qquad \epsilon\in\{-,+\},
\tag{5.1}
\]

be the set of all parametrized source paths
\(\beta:(0,1)\to X_h\) satisfying:

1. **complete exact image**
   \[
      I_h\circ\beta=\gamma_\lambda^\epsilon
   \tag{5.2}
   \]
   on all of \((0,1)\), after one recorded orientation-compatible
   parameter gauge;
2. **properness:** \(\beta\) extends to two specified points of the
   KKL ideal boundary of \(X_h\);
3. **fine marking:** \(\beta\) is a path in
   \((X_h,P_h^*\mathcal I)\);
4. **coarse survival:** it is not discarded as subordinate to one
   interval of \(I_h^*\mathcal I\);
5. **occurrence provenance:** its component, source sheet, both
   accesses, cyclic slots, parent/attachment data, and complete
   occurrence window are recorded; and
6. **segmented horizon:** its full stage paths and every nested
   occurrence map form a complete segmented prefix flag through \(h\).

The word “component” in (5.1) means the component of the actual raw
inverse trace containing \(\beta\), not a ribbon-tree label.

### Definition 5.1 (bilateral direct selector)

A bilateral direct selector consists of Borel maps

\[
 \sigma_h^\epsilon:
 \Lambda_h\longrightarrow\mathscr P_h^{\rm mark},
 \qquad \epsilon\in\{-,+\},
\tag{5.3}
\]

with
\(\sigma_h^\epsilon(\lambda)\in\mathcal C_h^\epsilon(\lambda)\)
for every retained \(\lambda\),
such that, writing
\(\beta_\lambda^\epsilon=\sigma_h^\epsilon(\lambda)\):

1. each family
   \[
      B_h^\epsilon
      =
      \{\beta_\lambda^\epsilon:\lambda\in\Lambda_h\}
   \tag{5.4}
   \]
   is an actual valid proper lamination and an actual KKL source Wave;
2. the same parameter \(\lambda\), same physical target leaf, same
   horizon, and same declared \(L_0^h\) occurrence are used for both
   signs;
3. the source transverse accounting realizes all of the target packet
   width, with no artificial occurrence multiplicity;
4. every omitted leaf belongs to a separately proved zero-width,
   \(V(F)\)-charged, or \(R(F)\)-charged family; and
5. the two target images in (5.2) are the disjoint untrimmed portions
   of Lemma 4.2.

No terminal deck noncollision is required here.  It is irrelevant to
the exact occurrence Series inequality.  If later terminality is
claimed, output Wave containment and controllability must be supplied
separately.

### Proposition 5.2 (mode reduction)

For a fixed width-faithful target packet, the
carrier/marking/family/complete-horizon part of a **typed** realized
two-branch response packet is equivalent to a bilateral direct selector
(5.3) together with the ending-degree bound of Section 6.

`DIRECT_WAVE`, `ACCESS_LOCAL`, and `FREUDENTHAL` are not three different
conclusions.  They are three possible ways of constructing (5.3).

#### Proof

Given (5.3), clauses 1--5 of Definition 5.1 supply the same
transversal, two genuine source Waves, exact parametrized images,
proper marked ends, and no-duplication accounting required by the
response-packet definition.  Section 6 supplies the ending degree.

Conversely, a realized packet already consists of actual Borel source
Wave leaves paired leafwise to the target portions with the exact image
identity.  Selecting its two source leaves defines (5.3), and all six
conditions defining \(\mathcal C_h^\epsilon(\lambda)\) are among the
packet's path, marking, occurrence, and complete-horizon hypotheses.
\(\square\)

### Consequence 5.3

`DIRECT_WAVE` is a certificate mode, not a construction lemma.  Saying
“use `DIRECT_WAVE`” without supplying (5.3) restates the desired
carrier/marking conclusion.

The segmented-occurrence theorem also is not a construction lemma for
(5.3).  It proves that supplied full stage paths and supplied occurrence
windows reconstruct a unique compatible prefix flag.  It creates
neither full path nor window.

## 6. The ending-degree clause is conditional but automatic

### Lemma 6.1 (global covering degree bounds every actual ending set)

Let \(P:X\to Y\) be a finite covering of degree at most \(D\), equipped
with a pulled ideal marking \(P^*\mathcal I\).  Let \(J\) be an actual
multi-interval in that pulled marking on which the ideal extension used
by the KKL covering calculus is defined.  Then

\[
 \deg_J(P)\le D.
\tag{6.1}
\]

#### Proof

The degree on \(J\) counts sheets of the restriction over the
corresponding target ideal set.  Every such sheet is a sheet of the
global covering \(P\).  A target point has at most \(D\) preimages in
all of \(X\), hence at most \(D\) preimages lying on \(J\).  Taking the
supremum over the whole target multi-interval gives (6.1). \(\square\)

### Corollary 6.2 (stationary ending-degree certificate)

If \(B_h^\epsilon\) in (5.4) is an actual source Wave in
\((X_h,P_h^*\mathcal I)\), and \(J_h^\epsilon\) is its actual ending
multi-interval, then

\[
 \deg_{J_h^\epsilon}(P_h)
 \le D_h
 \le 2^h
 \le 2^{b+2}.
\tag{6.2}
\]

The constant is independent of primitive period, satellite period,
rotation number, selector history, and path occurrence.

#### Proof

Apply Lemma 6.1 to \(P_h\) and use (3.2) and
\(h\le b+2\). \(\square\)

Consequently the explicit degree-dependent part of KKL's Wave error
satisfies

\[
 1+\log\deg_{J_h^\epsilon}(P_h)
 \le 1+(b+2)\log 2.
\tag{6.3}
\]

This does not prove that the hidden multiplicative constant in KKL's
\(O(1+\log d)\) is uniform over every marking/packet used here; that
separate source-uniformity obligation remains open.

### Qualification 6.3

Corollary 6.2 cannot be applied to:

- a local inverse germ;
- a partial maximal lift;
- a raw inverse-trace component with no two ideal endpoints;
- a path rejected by either marking filter; or
- a generic source lamination not proved to be a Wave.

Thus it removes the degree clause **after** the genuine source Wave is
constructed.  It does not help construct that Wave.

## 7. Mode-by-mode construction audit

### 7.1 `DIRECT_WAVE`

The direct route asks for the maps (5.3) as input.

The strongest native pointwise source statement before line 1603 is:

\[
 \forall\alpha\in A_h\quad
 \exists\Theta^\ast
 \quad
 [\Theta^\ast
 \text{ is one proper restriction ending at }L_0^h].
\tag{7.1}
\]

Even granting (7.1) literally, it does not specify:

1. the selected occurrence time or access on \(\alpha\);
2. which sign \(\Theta^\ast\) represents;
3. a second restriction component;
4. exact realization of either complete portion;
5. a Borel choice as \(\alpha\) varies;
6. a valid source Wave family; or
7. either marking-filter certificate.

The first source-lift map absent after a target split has been supplied
is therefore

\[
 \sigma_h^+:
 \lambda\longmapsto
 \text{the retained component realizing }
 L_0^h\rightsquigarrow
 \partial_{\rm C}\mathcal T\setminus BL_0,
\tag{7.2}
\]

or symmetrically \(\sigma_h^-\), because (7.1) does not type which
route its one path realizes.

#### Finite dependency countermodel

The source assertions before line 1603 are compatible with the
following finite model:

1. every stage has one untagged ambient output;
2. every output has one retained predecessor occurrence;
3. the terminal retained predecessor is declared to end at \(L_0^h\);
4. two formal route labels \(-,+\) are recorded;
5. the \(-\) label is realized by the retained predecessor; and
6. one transition of the \(+\) label uses the adjacency alternative
   allowed by the interval-itinerary proposition, with no path
   occurrence.

This model has the one retained chain and all finite route labels but
no second segmented occurrence and hence no (7.2).  It is a dependency
countermodel, not a KKL analytic block.

There is also a minimal holomorphic one-sided model.  Let

\[
 Y=\mathbb D,\qquad
 \Omega=\mathbb D\cap\{\operatorname{Im}z>0\},
\tag{7.2a}
\]

choose a Riemann map \(\phi:\mathbb D\to\Omega\), and let
\[
 I=\operatorname{incl}\circ\phi:\mathbb D\to\mathbb D.
\tag{7.2b}
\]
For
\[
 \alpha(t)=i(1-2t),\qquad 0<t<1,
\tag{7.2c}
\]
the two target portions at \(t=1/2\) are the positive and negative
open imaginary half-diameters.  The first lies in \(I(\mathbb D)\) and
has one proper inverse component ending at the access over \(0\); the
second is disjoint from \(I(\mathbb D)\) and has no inverse germ.
Thus

\[
\text{holomorphic immersion + one proper inverse + two target portions}
\not\Longrightarrow
 \text{bilateral direct selector}.
\tag{7.2d}
\]

The source disk may simultaneously carry the proper degree-two map
\(P(z)=z^2\); this does not create the missing immersion branch.  The
model is not a KKL marked block, and is used only to refute the stated
general bridge.

**Verdict:** `DIRECT_WAVE` stops at the bilateral component selector.

### 7.2 `ACCESS_LOCAL`

The proved access-seeded theorem applies to a supplied continuous
product piece

\[
 \Phi:\Lambda\times(0,1)\to X_0
\tag{7.3}
\]

and a supplied continuous lifted seed

\[
 \widehat\Phi_0^\epsilon:
 \Lambda\times(0,t_0]\to X_h,
 \qquad
 I_h\widehat\Phi_0^\epsilon=\Phi.
\tag{7.4}
\]

It proves:

- openness of the joint continuation domain;
- continuity of the maximal lift there;
- lower semicontinuity and Borelness of the exit time; and
- Borel landing and finite-horizon codes in a supplied compact metric
  ideal model.

It does not prove:

- a continuous product exhaustion of the actual survivor WAD;
- the seed (7.4) on either selected access;
- seed-side access properness;
- that maximal continuation covers the complete target portion;
- landing at the required far endpoint;
- fine/coarse marking survival;
- assembly into a valid source lamination or Wave;
- transverse-width equality; or
- bounded seed/occurrence multiplicity.

The first unconditional failure is therefore

```text
A0_NO_RLS_A_PLUS_PRODUCT_AND_SEED
```

on the actual KKL family.

There is a useful charitable refinement.  If one strengthens KKL's
phrase “passes through \(L_0^h\)” to an actual ordered two-sided
crossing in the finite embedded neighborhood of the pulled filled set,
then the two short local germs exist and their access cyclic order is
defined.  Even with those local germs, the first full-route gate is

```text
A1_NO_WHOLE_PORTION_MAXIMAL_LIFT
```

because the source proves no no-intermediate-collision theorem.

#### Exact slit-disk countermodel

Let

\[
 Y=\mathbb D,\qquad
 \Omega=\mathbb D\setminus[0,1),
\tag{7.5}
\]

let \(\phi:\mathbb D\to\Omega\) be a Riemann map, and put
\(I=\operatorname{incl}\circ\phi\).
At every interior point of the slit there are two distinct cyclically
ordered prime-end accesses.

Choose

\[
\begin{aligned}
 p&=i, &s_1&=0.8, &u_1&=0.65-0.15i,\\
 r&=0.5, &u_2&=0.35+0.15i, &s_2&=0.2,\\
 q&=-i
\end{aligned}
\tag{7.6}
\]

and let \(\alpha\) be the simple polygonal path

\[
 p\longrightarrow s_1\longrightarrow u_1\longrightarrow r
 \longrightarrow u_2\longrightarrow s_2\longrightarrow q.
\tag{7.7}
\]

The two germs at \(r\) lift at the two slit accesses.  Their maximal
components, with each target portion oriented from \(r\) toward its
far endpoint, are proper, but they cover only

\[
 s_1\longrightarrow u_1\longrightarrow r
\quad\text{and}\quad
 r\longrightarrow u_2\longrightarrow s_2.
\tag{7.8}
\]

Their far endpoints lie over \(s_1,s_2\), not \(p,q\).  Hence both
continuous singleton product seeds and both proper maximal lifts exist,
while neither exact whole-portion identity (5.2) holds.

This proves that

\[
\text{bilateral access seeds + Borel maximal continuation}
\not\Longrightarrow
\text{bilateral direct selector}.
\tag{7.9}
\]

The model is not asserted to be a KKL Hubbard block.  It proves that a
KKL-specific no-intermediate-collision/whole-portion theorem is an
independent hypothesis.

**Verdict:** `ACCESS_LOCAL` is the only currently plausible native
repair route, but it stops first at actual product/seed construction
and then at whole-portion landing and marking.

### 7.3 legitimately localized `FREUDENTHAL`

On the native complementary surface, \(BL_0\) and \(L_0^h\) are marked
ideal intervals/accesses.  The fixed-end theorem is typed by
Freudenthal ends.  Therefore a legitimate invocation must first
construct:

\[
\begin{aligned}
 &X_{h,\mathrm{loc}}^\epsilon
   \xrightarrow{\,I_{h,\mathrm{loc}}^\epsilon\,}X_{0,\mathrm{loc}},\\
 &e_{h,\mathrm{Fr}}^\epsilon
   \in\mathcal E(X_{h,\mathrm{loc}}^\epsilon),
\end{aligned}
\tag{7.10}
\]

such that:

1. the chosen marked access becomes the specified topological end;
2. the induced immersion is proper of degree one there;
3. the target Wave restricts width-faithfully to the localization; and
4. the localization does not create a fake exit before the proof-used
   occurrence.

The locked KKL source constructs no (7.10).  This is the first
Freudenthal failure:

```text
F0_NO_ACCESS_SPLITTING_LOCALIZATION
```

There is a conditional stronger obstruction.  Under the physical
carrier hypotheses
\(\mathrm{TWO}_0\wedge\mathrm{TWO}_h\wedge\mathrm{INC}_h\), all
tree-side accesses refine one inner Freudenthal end, and that end is
nonproper for \(I_h\).  The conditional conclusion does not apply
without those hypotheses, but it forbids silently using the native
inner end as the proper degree-one end required by the fixed-end
theorem.

Even if legitimate localizations and two proper starting ends are
supplied, the fixed-end theorem does not prove the diagonal occurrence
identity.  Write the two first-exit maps as

\[
 \xi_h^\pm:\Lambda_h\longrightarrow\Xi_h.
\tag{7.11}
\]

The paired construction needs

\[
 \xi_h^-(\lambda)=\xi_h^+(\lambda)
\quad\text{with the same component, access, sheet, and occurrence
window for every retained }\lambda.
\tag{7.12}
\]

The fixed-end theorem partitions the two oriented lifts separately by
source homotopy class.  It contains no statement implying (7.12).

#### Exact two-obstacle counterconfiguration

Let

\[
 V=\{1<|z|<4\}
\tag{7.13}
\]

and choose a narrow radial product rectangle \(R\subset V\).  Place two
disjoint closed Jordan obstacles \(Q_1,Q_2\Subset V\) across the full
angular width of \(R\), in radial order, and set

\[
 V'=V\setminus(Q_1\cup Q_2),
 \qquad i:V'\hookrightarrow V.
\tag{7.14}
\]

The inclusion is proper of degree one at both annular ends.  The radial
product foliation is a valid target WAD.  Starting at the inner end,
the maximal lift first exits at \(Q_1\); starting at the outer end, the
reverse lift first exits at \(Q_2\).  Thus

\[
 \xi^-=Q_1\ne Q_2=\xi^+.
\tag{7.15}
\]

All abstract fixed-end hypotheses hold, but the common-occurrence
condition fails.  With one obstacle and two boundary accesses, even a
common component label need not give the same marked access.

This is not a KKL block.  It proves that (7.12) is an additional
geometric theorem, not a consequence of the fixed-end WAD theorem.

**Verdict:** the native Freudenthal mode is ill-typed; a legitimately
localized mode would still require a new diagonal-exit and complete
marking theorem.

## 8. Formal interface nonclosure from the present dependency set

### Theorem 8.1 (the current four exported interfaces do not discharge typed realization)

Use only the explicit conclusions, with their native hypotheses, of
the statements currently recorded as:

1. stationary survivor partition and pointwise switch;
2. segmented occurrence reconstruction;
3. access-seeded maximal-lift measurability; and
4. fixed-end/access type obstruction

Then an additional analytic construction is required before
`KKL_STATIONARY_TYPED_PAIRED_WAVE_REALIZATION` can be invoked:
none of those four exported interfaces supplies the bilateral selector
(5.3).

#### Proof

The survivor theorem is conditional on a supplied single-valued
occurrence space and supplies only pointwise nonempty retained
predecessor fibers.  It proves no width-faithful Borel selector.

The segmented-occurrence theorem reconstructs a prefix relation path
from already supplied full stage paths and occurrence windows.  The
finite dependency model in Section 7.1 satisfies one retained chain
while having no second occurrence.  Therefore that theorem cannot
construct the missing bilateral selector.

The access theorem starts after the continuous product and access seed
have been supplied.  The slit-disk model (7.5)--(7.9) satisfies
bilateral singleton product seeds and proper maximal continuations but
fails both complete image identities.  Thus its conclusions do not
imply a direct selector.

The fixed-end/access audit proves that a marked access is not already
an eligible Freudenthal end.  Even after proper ends are supplied, the
two-obstacle model (7.13)--(7.15) satisfies the fixed-end theorem's
hypotheses while failing the common-exit identity.

Each possible start mode therefore stops before Proposition 5.2.
The countermodels prove that the tempting *general bridge principles*
used to fill those interface gaps are false.  This is an interface and
source-derivability conclusion; it is not a model-theoretic
counterexample satisfying all hypotheses of an actual stationary KKL
block. \(\square\)

### Corollary 8.2 (the first missing map after a supplied presentation)

Assume, in addition, a width-faithful occurrence presentation, the
scope bridge (3.10), a Borel first-horizon partition, and a unique
marked occurrence split.  Then the first common missing construction
is the bilateral Borel component selector (5.3).

#### Proof

The additional assumptions supply the target family, target
accounting, and target portions.  Proposition 5.2 shows that all three
mode-specific routes must next construct (5.3).  Sections 7.1--7.3
show that no current mode does so. \(\square\)

## 9. Exact obstruction certificate

An actual future KKL block audit must stop at the first failed item in
the following order.

### 9.1 Family-level prefix

Record

\[
\begin{split}
\mathfrak O_{\rm fam}=
(&F,b,N,\Omega,\pi_A,\nu_A,\omega,\alpha,h;\\
 &\text{native survivor word},\text{short flag},
   \text{scope-map value};\\
 &\text{actual }L_0^h\text{ component},
   \text{occurrence time/window},
   \text{two accesses and cyclic slots}).
\end{split}
\tag{9.1}
\]

Allowed first codes are:

```text
R0_NO_WIDTH_FAITHFUL_OCCURRENCE_PRESENTATION
R1_NO_SCOPE_BRIDGE_TO_DEEP_A_h
R2_FIRST_HORIZON_NOT_BOREL_OR_DUPLICATED
R3_NO_UNIQUE_MARKED_L0_OCCURRENCE
R4_PRODUCT_SEAMS_OR_OMITTED_FAMILY_NOT_ZERO_WIDTH
```

At the present source boundary the unconditional audit stops at `R0`.
If the route-exit occurrence presentation is supplied as a hypothesis,
the source-specific line-1603 audit can still stop at `R1` or `R3`.

### 9.2 Per-sign component record

For each \(\epsilon\in\{-,+\}\), record

\[
\begin{split}
\mathfrak O_h^\epsilon=
(&\alpha,\epsilon,\gamma^\epsilon;
  \text{start mode},\text{source sheet},\text{seed/end};\\
 &\text{maximal raw component and parameter interval};
  \text{two ideal limits or first nonlanding};\\
 &\text{full segmented stage paths and windows};
  \text{fine endpoints};\\
 &\text{coarse subordination flag};
  \text{terminal Wave identity};
  \text{ending multi-interval}).
\end{split}
\tag{9.2}
\]

Mode-specific codes are:

```text
DIRECT:
  D0_NO_BILATERAL_COMPONENT_SELECTOR

ACCESS_LOCAL:
  A0_NO_RLS_A_PLUS_PRODUCT_AND_SEED
  A1_NO_WHOLE_PORTION_MAXIMAL_LIFT
  A2_MAXIMAL_LIFT_NONLANDING

FREUDENTHAL:
  F0_NO_ACCESS_SPLITTING_LOCALIZATION
  F1_START_END_NOT_PROPER_DEGREE_ONE
  F2_OPPOSITE_EXIT_CODES_DIFFER
```

Common post-start codes are:

```text
C0_EXACT_UNTRIMMED_IMAGE_FAILS
C1_SOURCE_PATH_NOT_PROPER
C2_FINE_MARKING_FAILS
C3_COARSE_FILTER_REJECTS
C4_SEGMENTED_HORIZON_INCOMPLETE
C5_SOURCE_FAMILY_NOT_A_VALID_WAVE
C6_BOREL_OR_FULL_WIDTH_ACCOUNTING_FAILS
C7_OCCURRENCE_MULTIPLICITY_EXCEEDS_ONE
C8_ENDING_MULTIINTERVAL_NOT_ACTUAL
```

There is no independent `C9_DEGREE_TOO_LARGE` once `C8` passes:
Corollary 6.2 supplies the uniform degree bound.

### 9.3 Present exact certificate

No individual dynamical leaf \(\alpha\) can honestly be entered in
(9.1) from the locked source, because the width-faithful occurrence
presentation itself is absent.  The present certificate is therefore:

\[
\boxed{
\begin{aligned}
 \text{level}&=\text{source derivability},\\
 \text{first code}&=\texttt{R0\_NO\_WIDTH\_FAITHFUL\_OCCURRENCE\_PRESENTATION},\\
 \text{conditional next code}&=\texttt{D0\_NO\_BILATERAL\_COMPONENT\_SELECTOR},\\
 \text{replacement invariant}&=
 (\Omega_h,\pi_A,t_h,a_h^\pm,\sigma_h^\pm,
   \mathfrak S_h^\pm,\mathfrak m_h^\pm).
\end{aligned}}
\tag{9.3}
\]

Here \(a_h^\pm\) are the two marked accesses,
\(\mathfrak S_h^\pm\) are the complete segmented flags, and
\(\mathfrak m_h^\pm\) are the two complete marking/filter records.

This certificate does not assert that an actual KKL block realizes
one of the countermodels in Section 7.

## 10. Adversarial audit

1. **The target residual is not silently assumed measurable.**
   Equations (3.5)--(3.7) are conditional on a supplied
   width-faithful occurrence presentation.
2. **The route-exit survivor is not identified with the line-1603
   residual.**  The scope bridge (3.10) is explicit.
3. **“Passes through” is not retyped without proof.**
   Equation (3.9) remains an obligation.
4. **First-horizon labels do not duplicate physical leaves.**
   Injectivity of \(\pi_A\), not finite label cardinality, supplies
   no-duplication.
5. **A Borel leaf set is not called a continuous product.**
   Lemmas 4.1--4.2 apply only on supplied product pieces.
6. **A unique physical hit is required.**  Multiple hits, tangency,
   travel along \(L_0^h\), and touch/reentry invalidate Lemma 4.2.
7. **Open portions are not finitely truncated.**  Formula (4.5) uses
   the complete open parameter intervals on both sides of the
   occurrence.
8. **One existential restriction is not duplicated.**
   Equation (7.1) does not supply (7.2).
9. **An interval itinerary is not called a path.**
   The adjacency and common-pullback alternatives remain possible.
10. **A terminal equalizer path does not replace full stage paths.**
    Definition 5.1 requires the complete segmented prefix flags.
11. **A local germ is not called a proper source path.**
    Two ideal limits and both marking filters are explicit.
12. **Escape from compacta is not called prime-end landing.**
    `A2_MAXIMAL_LIFT_NONLANDING` is retained.
13. **Wave subordination is not literal collar containment.**
    The slit-disk model attacks precisely that inference.
14. **A marked access is not called a Freudenthal end.**
    The localization (7.10) must be constructed.
15. **Two fixed-end decompositions are not automatically paired.**
    The diagonal identity (7.12) is independent.
16. **Component-label equality is not access equality.**
    The one-obstacle variant of the annular model has two accesses to
    one component.
17. **Terminal output collision is not made a binder failure.**
    The paired Series/Wave response does not require deck
    noncollision.
18. **Output collision is not called terminality.**
    A common controllable output Wave and ambient-width threshold are
    later, separate obligations.
19. **The covering degree is used only after an actual ending
    multi-interval exists.**  Corollary 6.2 cannot license a partial
    trace.
20. **Pointwise selection is not called Borel.**
    The maps (5.3) are family-level data.
21. **A null transverse-measure set is not automatically declared
    zero extremal width.**  Every omission needs the width statement
    in Definition 5.1(4).
22. **The line-1603-dependent proposition is not used.**
    No part of this note invokes Proposition `into the critical limb`
    to prove its own pair construction.
23. **No global constant is promoted.**
    The hidden Wave-error uniformity and output controllability remain
    outside this pass.
24. **The countermodels have the correct scope.**
    They are logical/analytic countermodels to proposed general
    implications, not dynamical KKL counterexamples.
25. **Global status remains open.**
    Nothing here proves VAAPC-I, UPTCR, rigidity, or MLC.

## 11. Historical optional constructive theorem

Within this optional pre-QA route, the proposed source-specific theorem
was no longer “choose one of three labels.”  It was:

> **Width-faithful bilateral retained-Wave assembly.**  
> For every native stationary critical-end Wave:
>
> 1. construct a width-faithful single-valued survivor occurrence
>    presentation and the scope map (3.10);
> 2. partition the eligible residual by its Borel first horizon without
>    duplicate physical leaves;
> 3. on a conull/full-width union of continuous product pieces, type the
>    actual \(L_0^h\) encounter as one unique ordered crossing with two
>    specified cyclically ordered accesses;
> 4. construct the two Borel component selectors (5.3);
> 5. prove that both maximal components realize the complete untrimmed
>    target portions, land at their required far ideal ends, and are
>    proper;
> 6. construct both complete segmented prefix flags and prove every
>    fine/coarse marking predicate;
> 7. prove that the selected families are valid source Waves with
>    native transverse-width accounting and occurrence multiplicity
>    one; and
> 8. place every omitted leaf in an independently proved zero-width,
>    \(V(F)\)-charged, or \(R(F)\)-charged class.

Corollary 6.2 then supplies the whole-ending degree bound automatically.
The exact occurrence Series theorem and conditional paired-Wave
response theorem can be invoked only after items 1--8.

If item 3 fails on an actual block, retain the first multiple/tangent
occurrence and both access traces.  If item 5 fails, retain the first
intermediate component or nonlanding oscillation.  If item 6 fails,
retain the first rejected full stage path and exact occurrence window.
If item 7 fails, retain the transverse product piece and the first
duplicated or unmeasured leaf.

This theorem is falsifiable and strictly stronger than the current
finite schemas.  It is also the smallest common repair of all three
typed start modes identified in this pass.

## 12. Final conclusion

The attempted construction does not close the stationary survivor.
It does, however, settle the logical architecture of the next pass:

\[
\begin{split}
 &\text{width-faithful survivor presentation}
 \longrightarrow
 \text{unique marked occurrence split}\\
 &\longrightarrow
 \text{bilateral Borel component selectors}
 \longrightarrow
 \text{proper marked segmented source Waves}\\
 &\longrightarrow
 \text{automatic ending-degree bound}
 \longrightarrow
 \text{paired response}.
\end{split}
\tag{12.1}
\]

The current source stops before the first arrow unconditionally and
before the bilateral selector even after the occurrence presentation is
granted.  The next research pass must construct the actual KKL product
pieces and bilateral whole-portion lifts, or end with the first
leaf-level certificate (9.1)--(9.2).  Relabeling an access, route word,
or finite occurrence token cannot discharge that task.

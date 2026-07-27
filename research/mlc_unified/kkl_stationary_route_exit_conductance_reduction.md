# KKL stationary route-exit conductance: source reduction and first obstruction

## 1. Question, answer, and proof status

This note tests the route-localized replacement proposed in
`kkl_stationary_uniform_collar_charge_attack.md`:

\[
 \sum_{h=1}^{b+2}\mathfrak E_h(F)
 \stackrel{?}{\leq}
 C_b\bigl(V(F)+1\bigr),
 \qquad
 V(F):=\mathcal W(\mathcal U\setminus\mathcal T).
\tag{1.1}
\]

Here \(\mathfrak E_h(F)\) is intended to be the extremal width of the
fully marked proof-used continuations whose chosen
\(\iota_h\)-inverse branch first fails at horizon \(h\).

There is a necessary preliminary normalization.  If the ambient KKL
leaf itself breaks within the horizon, it already belongs to
\(A^{H\text{-br}}\); if it remains ambient-unbreakable but is in the
maximal short subwave, it already belongs to \(A^{\rm sh}\).  Those
leaves are part of KKL's native

\[
 B_A=A^{H\text{-br}}\cup A^{\rm sh}
\tag{1.1a}
\]

and must not be charged a second time as a new route defect.  The
intrinsic new conductance is the width of the **nonshort ambient
survivor exits** defined in Section 5.  Consequently, (1.1), if read
as a sum over all selected exits, is stronger than the stationary
repair needs.

The source-first verdict is:

\[
\boxed{
\begin{minipage}{0.88\linewidth}
Conditional on a measurable proper packet, the locked KKL source
proves a uniform finite-horizon charge for every exit whose selected
source restriction is a proper vertical path.  Conditional on the
listed properness, marking, incidence, and packet-count certificates,
it also reduces several properly landed tree-side exits either to a
bounded Wave/Shift family, to a family bounded by
\(\mathcal W(\mathcal RF)\), or to KKL's terminal-Wave response.

It does not prove that every selected continuation has a measurable
first failure and a unique proper ideal landing.  Even after those
facts are assumed, a tree-side exit can project to a Wave ending at
\(BL_0\); the only source estimate for that class is Proposition
`into the critical limb`, whose proof contains the stationary
line-1603 gap being repaired.  Using it here would be circular.

Consequently (1.1) is not proved from the locked sources.  The
source-supported **conditional** conclusion is the charged/response
decomposition in Theorem 9.1 below.
\end{minipage}}
\tag{1.2}
\]

This is a source-derivability obstruction, not a counterexample in the
class of actual parabolically bounded KKL maps.  No claim in this note
promotes the stationary repair, `VAAPC-I`, `UPTCR`, or `MLC`.

## 2. Locked sources and exact clauses

The locked KKL source is

```text
.tmp_wave_audit/waves-with-Misha.tex
SHA-256 AD4C774806D9902AA54FA31C56AD6146D8034946F19CC5E9CEC3C51A3F94FDD5
```

The clauses used here are:

- lines 439--448: pseudo-quadratic-like maps and their full filled-set
  width;
- lines 458--461: the finite pullback tower;
- lines 1145--1156: the marked surface
  \(\mathcal U\setminus\mathcal T\), vertical width, and terminal
  alternative;
- lines 1225--1241: on complements, \(f\) is a covering and
  \(\iota\) is an immersion; \(\iota\) is injective near the filled
  set;
- lines 1355--1368: breakability, unbreakability, and the
  `small breaking` proposition;
- lines 1429--1492: **under end-properness**, a one-step broken leaf
  restricts to a vertical path, one Wave over the pulled crest, or two
  Waves over its pulled endpoints;
- lines 1442--1445: the one-step vertical estimate
  \[
    \mathcal W(A^{\rm ver})
    \leq\mathcal W(\mathcal U'\setminus\mathcal T')
    \leq2V(F);
  \]
- lines 1513--1532: bounded unbreakable Waves over \(BL_0\) and the
  Shift estimate away from \(BL_0\);
- lines 1534--1623: the critical-end stationary argument, including
  the unsupported universal pass-through assertion at line 1603;
- lines 1613--1617: **after actual component incidence is obtained**,
  a pushforward lamination connecting the required small-Julia
  components is bounded by \(2\mathcal W(\mathcal RF)\);
- lines 1707--1709: the \(h\)-fold pair
  \((f^h,\iota_h)\) on
  \(\mathcal U^h\setminus\mathcal T^h\);
- lines 1749--1758: the native long-iterate vertical-family estimate;
- lines 1844--1875: ideal closures, proper paths, laminations, and
  Waves;
- lines 2065--2078: coverings and the pushforward-lamination lemma;
- lines 2080--2108: immersion restriction, domination, and the
  itinerary alternatives;
- lines 2149--2152: the Wave pushforward lemma;
- lines 2157--2168: properness, end-properness, and unbreakable
  combinatorial transport; and
- lines 2171--2178: the Shift lemma.

The locked Kahn source is

```text
.tmp_kl06_source/psiql2.tex
SHA-256 E4EFCCEC65D8C9C2BDFE2AF8203B3D4D63ECF992B40D302F56FBA78259547228
```

Its pullback construction proves the finite interior relation and the
commuting tower maps.  The locked clauses do **not** state a Borel
maximal-inverse-branch selector, unique ideal landing for every
selected route, or a quantitative theorem about the width of
nonproper immersion ends.

## 3. Native finite-horizon setting

Fix a parabolically \(b\)-bounded stationary KKL block and put

\[
 X_0=\mathcal U\setminus\mathcal T,\qquad
 X_h=\mathcal U^h\setminus\mathcal T^h,\qquad
 N=b+3,\qquad H=N,\qquad m=N-1=b+2.
\tag{3.1}
\]

Write

\[
 P_h=f^h:X_h\longrightarrow X_0,
 \qquad
 I_h=\iota_h:X_h\longrightarrow X_0.
\tag{3.2}
\]

On these complementary surfaces:

1. \(I_h\) is a holomorphic immersion, hence a local conformal
   homeomorphism;
2. \(P_h\) is an unbranched covering; and
3. its total degree obeys
   \[
      D_h:=\deg P_h\leq2^h.
   \tag{3.3}
   \]

The inequality in (3.3), rather than an asserted degree-one route, is
the safe global bound.  Any sharper degree statement must be proved
on the actual marked endpoint or component to which it is applied.

The stationary route pullbacks use only \(1\leq h\leq m\), while
ambient breakability is tested through the source-selected horizon
\(H=N\).  Thus

\[
 \sum_{h=1}^{m}D_h
 \leq
 \sum_{h=1}^{m}2^h
 =
 2^{m+1}-2
 =
 2^{b+3}-2.
\tag{3.4}
\]

We also put

\[
 R(F):=\mathcal W(\mathcal RF).
\tag{3.5}
\]

All curve families below must be genuine laminations in the
source-stated marked surfaces.  A finite set of combinatorial labels
does not itself define such a family.

## 4. What “first inverse-branch failure” can mean

An arbitrary boundary of a chosen Jordan collar is not an intrinsic
failure locus.  Since \(I_h\) is an immersion, a local inverse branch
can often continue straight through that artificial boundary.  The
intrinsic object is maximal continuation on the full source surface
\(X_h\).

### Definition 4.1 (oriented route germ)

An oriented \(h\)-route germ consists of:

1. an oriented path
   \(\gamma:[s_0,s_1]\to X_0\), normally a parameterized portion of
   a proof-used Wave leaf;
2. a time \(t_0\in[s_0,s_1)\);
3. a point \(x_0\in X_h\) satisfying
   \(I_h(x_0)=\gamma(t_0)\); and
4. the occurrence, access, sheet, and filter labels selecting this
   germ.

A forward lift is a path \(\widetilde\gamma\) satisfying

\[
 \widetilde\gamma(t_0)=x_0,
 \qquad
 I_h\circ\widetilde\gamma=\gamma.
\tag{4.1}
\]

Its maximal continuation interval is denoted
\([t_0,\tau)\), where \(\tau\leq s_1\).

### Lemma 4.2 (maximal-lift alternative)

Let \(I:X\to Y\) be a local homeomorphism between locally compact
metric spaces, let \(\gamma:[t_0,s_1]\to Y\) be continuous, and
let \(\widetilde\gamma:[t_0,\tau)\to X\) be a maximal lift.  If
\(\tau<s_1\), then

\[
 \widetilde\gamma(t)
 \text{ escapes every compact subset of }X
 \quad(t\uparrow\tau).
\tag{4.2}
\]

Equivalently, if a sequence \(t_n\uparrow\tau\) has
\(\widetilde\gamma(t_n)\) in one compact subset of \(X\), the lift
extends beyond \(\tau\).

#### Proof

Assume a compact \(K\Subset X\) contains
\(\widetilde\gamma(t_n)\) for a sequence \(t_n\uparrow\tau\).
After passing to a subsequence,

\[
 \widetilde\gamma(t_n)\longrightarrow x\in K.
\tag{4.3}
\]

Continuity of \(I\) and \(\gamma\) gives

\[
 I(x)
 =
 \lim_n I(\widetilde\gamma(t_n))
 =
 \lim_n\gamma(t_n)
 =
 \gamma(\tau).
\tag{4.4}
\]

Choose an open neighborhood \(V\ni x\) on which \(I\) is a
homeomorphism onto an open neighborhood \(W\ni\gamma(\tau)\).
Shrink \(V,W\), if necessary, and choose \(\varepsilon>0\) so that

\[
 \gamma([\tau-\varepsilon,\tau+\varepsilon]\cap[t_0,s_1])
 \subset W.
\tag{4.5}
\]

For a sufficiently large \(n\),
\(t_n>\tau-\varepsilon\) and
\(\widetilde\gamma(t_n)\in V\).  On the connected interval from
\(t_n\) to \(\tau\), compare \(\widetilde\gamma\) with the lift
\((I|_V)^{-1}\circ\gamma\).  Two lifts of the same path under a local
homeomorphism which agree at one time agree throughout their common
connected parameter interval: the equality set is nonempty and is
both open and closed by local injectivity.  Hence

\[
 \widetilde\gamma(t)
 =
 (I|_V)^{-1}(\gamma(t)).
\tag{4.6}
\]

The right side extends continuously to \(\tau\) and, by (4.5), a
little beyond it.  This contradicts maximality.  Therefore (4.2)
holds. \(\square\)

### Corollary 4.3 (sheet overlap is not a branch endpoint)

A collision of the image \(I_h(X_h)\) with another immersion sheet
does not, by itself, terminate the selected lift.  At every source
point \(I_h\) remains locally invertible, and the already selected
germ determines the local continuation uniquely.

Thus “the global inverse is no longer single-valued” is not a valid
first-failure certificate.  A genuine finite-time failure must be
escape from \(X_h\), as in Lemma 4.2.  If a proof deliberately
restricts to a smaller globally embedded sheet, hitting the boundary
of that sheet is only a proof-device failure until noncontinuability
on the full \(X_h\) is established.

## 5. Landing and measurability certificate

Lemma 4.2 produces escape, not a usable KKL proper path.  To classify
the escaped lift by extremal width, one needs the following additional
theorem.

### RLS\(_h\) (route landing and selection certificate)

For the proof-used \(h\)-route family there is:

1. a standard Borel leaf space \((\Lambda,\nu)\) for the ambient
   source-native Wave;
2. a **complete single-valued** Borel selector: its domain is exactly
   the set of leaves on which at least one declared proof-used route
   fails; it chooses the globally first failure stage, then one route
   by a fixed finite priority rule, and records whether the failure is
   failure to produce a full retained KKL path or failure only of the
   declared marked route state;
3. a Borel field of the selected initial germs;
4. in the first case of clause 2, a Borel maximal continuation time
   \(\tau_h(\lambda)\);
5. a source compactification \(\widehat X_h\) compatible with the
   KKL ideal marking;
6. a Borel landing map for every uniquely landing route,
   \[
     \ell_h(\lambda)
     =
     \lim_{t\uparrow\tau_h(\lambda)}
       \widetilde\gamma_\lambda(t)
     \in\widehat X_h\setminus X_h;
   \tag{5.1}
   \]
7. a Borel code for the first source-boundary stratum; and
8. preservation of the transverse measure defining the lamination
   width.

The complete failure code must distinguish the following boundary
strata, together with the separate non-boundary state class
\(\mathsf Q_h\):

- \(\mathsf O_h\): the outer ideal boundary inherited from
  \(\partial\mathcal U^h\);
- \(\mathsf T_h^{\rm dec}\): the declared pulled-tree access;
- \(\mathsf T_h^{\rm exc}\): a different pulled-tree side, root,
  attachment, or access;
- \(\mathsf Z_h\): an explicitly removed obstacle;
- \(\mathsf M_h\): a marking endpoint or a locus on which the
  coarse subordinate filter ceases to retain a path;
- \(\mathsf Q_h\): a full retained KKL restriction exists, but the
  named access, sheet, obstacle, occurrence-window, or other declared
  route-state coordinate fails; and
- \(\mathsf N_h\): nonunique landing, a nontrivial cluster set, or
  failure of unique ideal-end convergence for the selected route.

At a vertex where several sides meet, the full access tag, not the
unmarked topological point, determines the code.

The locked KKL and Kahn clauses do not prove RLS\(_h\).  This is the
first dependency obstruction: without RLS\(_h\), the symbol
\(\mathfrak E_h(F)\) need not denote a measurable lamination width.

### Exhaustiveness once RLS\(_h\) is assumed

For a selected route, exactly one of the following occurs:

1. it reaches the declared remote access as a full retained path with
   the complete declared route state and is not an exit;
2. it fails to produce a full retained named path and has a unique
   landing in
   \(\mathsf O_h\), \(\mathsf T_h^{\rm exc}\),
   \(\mathsf Z_h\), or \(\mathsf M_h\);
3. it fails to produce a full retained named path, has no usable
   unique landing, and belongs to \(\mathsf N_h\); or
4. it does produce a full retained named path but fails the declared
   route state and belongs to \(\mathsf Q_h\).

For the geometric-failure cases, exhaustiveness follows from Lemma
4.2 and the boundary partition in RLS\(_h\).  The fourth case is the
non-boundary state-mismatch alternative recorded separately in
RLS\(_h\)(2).  Thus Lemma 4.2 alone does not prove the displayed
four-way exhaustion.  Nor is this a claim that each class is
numerically controlled.

Only after the complete single-valued selector, first-horizon rule,
landing code, and transverse-measure compatibility have been supplied
do we set

\[
 \mathfrak E_h(F)
 :=
 \mathcal W(\mathscr E_h),
\tag{5.2}
\]

where \(\mathscr E_h\) is the resulting marked first-exit
sublamination.  Before then, \(\mathfrak E_h(F)\) is a proposed
invariant, not an imported KKL quantity.

### 5.1 Ambient survivor normalization

Fix the ambient proof-used Wave \(A\), use KKL's ambient
unbreakability horizon \(H=N=b+3\), and retain route pullback horizons
\(1\leq h\leq m=N-1=b+2\).  Let \(\mathscr E_h\) be the leaves whose
complete selector has first failed route horizon \(h\), and put

\[
\begin{aligned}
 \mathscr E_h^{\rm amb\text{-}br}
  &=\mathscr E_h\cap A^{H\text{-br}},\\
 \mathscr E_h^{\rm amb\text{-}sh}
  &=\mathscr E_h\cap A^{H\text{-nbr}}\cap A^{\rm sh},\\
 \mathscr S_h
  &=\mathscr E_h\cap A^{H\text{-nbr}}\setminus A^{\rm sh}.
\end{aligned}
\tag{5.3}
\]

These are disjoint and exhaust \(\mathscr E_h\).  Moreover,

\[
 \mathscr E_h^{\rm amb\text{-}br}
 \cup\mathscr E_h^{\rm amb\text{-}sh}
 \subset B_A,
 \qquad
 \mathscr S_h\cap B_A=\varnothing.
\tag{5.4}
\]

This is the set-theoretic survivor reduction proved separately in
`kkl_stationary_route_exit_survivor_reduction.md`.  It uses only the
definitions of KKL's \(H\)-breakable part and maximal short subwave.

Hence every disjoint stationary defect estimate must first relabel
the first two families into \(B_A\).  Only

\[
 \mathfrak S_h(F):=\mathcal W(\mathscr S_h)
\tag{5.5}
\]

is a new route-defect coordinate.  A projected Wave that is short at
stage \(h\) need not lie in the original ambient \(A^{\rm sh}\);
throughout the rest of this note “short residual” means such a
stage-output short family and not the absorbed family
\(\mathscr E_h^{\rm amb\text{-}sh}\).

## 6. The vertical class is uniformly charged

An outer landing is chargeable only when the selected restriction can
be completed to the actual proper path used by KKL.  We therefore
state every required hypothesis.

### Definition 6.1 (proper vertical exit packet)

A measurable target sublamination
\(\mathscr S_h^{\rm ver}\subset\mathscr S_h\subset X_0\) has a proper
vertical exit packet if there are a source lamination
\(\mathscr B_h^{\rm ver}\subset X_h\) and a Borel map

\[
 \sigma_h^{\rm ver}:
 \mathscr S_h^{\rm ver}\longrightarrow
 \mathscr B_h^{\rm ver}
\tag{6.0}
\]

such that:

1. \(\sigma_h^{\rm ver}(\alpha)\) is the unique restriction path
   selected by the complete first-exit record over \(\alpha\), and
   \(I_h^*\alpha\) contains this leaf;
2. every \(\beta\) is a proper path connecting the pulled-tree ideal
   boundary to the outer ideal boundary of \(X_h\);
3. the selected restrictions retain the fine marking and are not
   discarded as subordinate to one pulled coarse interval;
4. \(\mathscr B_h^{\rm ver}\) is a genuine lamination, with its native
   transverse measure; and
5. the relevant endpoints belong to the ideal-boundary locus on which
   \(P_h\) has its covering extension, the degree on every such
   endpoint locus is at most \(D_h\), and \(P_h(\beta)\) is a proper
   path connecting the two boundary components of \(X_0\).

Clause 2 includes backward completion from the local seed to the
proof-used tree access.  A partial arc from an interior seed to the
outer boundary is not enough.

For disjoint leaf accounting, the occurrence-tagged map
\(\sigma_h^{\rm ver}\) must also be injective modulo transverse
measure zero.  This follows if distinct ambient leaves have disjoint
images and the selected source leaf maps into the corresponding
ambient leaf, but that implication must be checked in the actual
marked surface; it is not inferred merely from distinct route labels.
KKL domination below only needs clause 1.  Injectivity is needed to
ensure that the source packet does not duplicate the native
leaf-by-leaf defect mass.

### Theorem 6.2 (explicit vertical charge)

If \(\mathscr S_h^{\rm ver}\) has a proper vertical exit packet, then

\[
 \mathcal W(\mathscr S_h^{\rm ver})
 \leq
 D_h\bigl(V(F)+2\bigr)
 \leq
 2^h\bigl(V(F)+2\bigr).
\tag{6.1}
\]

Consequently,

\[
 \sum_{h=1}^{b+2}
 \mathcal W(\mathscr S_h^{\rm ver})
\leq
\bigl(2^{b+4}-4\bigr)\bigl(V(F)+1\bigr).
\tag{6.2}
\]

#### Proof

By Definition 6.1(1), every target leaf has a selected restriction
containing a leaf of \(\mathscr B_h^{\rm ver}\).  KKL's domination
lemma, lines 2086--2090, gives

\[
 \mathcal W(\mathscr S_h^{\rm ver})
 \leq
 \mathcal W(\mathscr B_h^{\rm ver}).
\tag{6.3}
\]

Apply KKL's pushforward-lamination lemma, lines 2075--2078, to
\(P_h\).  The endpoint-degree hypothesis is Definition 6.1(5);
interior total degree by itself is not substituted for the required
ideal-end statement.  There is a lamination
\(\mathscr C_h^{\rm ver}\subset
P_{h*}\mathscr B_h^{\rm ver}\) such that

\[
 \mathcal W(\mathscr B_h^{\rm ver})
 \leq
 D_h\mathcal W(\mathscr C_h^{\rm ver})+2D_h.
\tag{6.4}
\]

By Definition 6.1(5),
\(\mathscr C_h^{\rm ver}\) connects the two boundary components of
\(X_0=\mathcal U\setminus\mathcal T\).  The same vertical-family
monotonicity used explicitly by KKL at lines 1752--1758 gives

\[
 \mathcal W(\mathscr C_h^{\rm ver})\leq V(F).
\tag{6.5}
\]

Combining (6.3)--(6.5) proves (6.1).  Summing and using (3.4),

\[
\begin{aligned}
 \sum_{h=1}^{m}
  \mathcal W(\mathscr S_h^{\rm ver})
 &\leq
 (2^{m+1}-2)(V(F)+2)\\
 &\leq
 2(2^{m+1}-2)(V(F)+1)\\
 &=
 (2^{b+4}-4)(V(F)+1),
\end{aligned}
\tag{6.6}
\]

because \(V(F)\geq0\) and \(m=b+2\). \(\square\)

Theorem 6.2 is the complete numerical consequence of the cited source
lemmas **conditional on construction of the packet in Definition
6.1**.  KKL do not supply RLS\(_h\), the selector, or the packet for
the new route-exit family.  Once those hypotheses are proved, the
estimate is the \(h\)-fold analogue of KKL lines 1442--1445 and the
same numerical pattern used at lines 1749--1758.

## 7. Tree-side landing: what does and does not follow

Suppose a lift lands at an excess pulled-tree access or an obstacle
that has been explicitly identified with a marked tree side.  This
does not automatically produce a KKL Wave.  The following clauses are
still required:

1. the partial lift completes to a proper path at both ends;
2. both endpoints lie in retained fine-marking intervals;
3. the path is not subordinate to one coarse pulled interval;
4. the applicable immersion is proper or end-proper on the relevant
   end-intervals;
5. the image has a single declared covering multiplicity; and
6. the source paths form a measurable lamination.

KKL's itinerary proposition, lines 2099--2108, explicitly permits
adjacent fine intervals and pairs lying in one pulled coarse interval.
Those alternatives are combinatorial records, not retained proper
paths.  Therefore “the access labels agree” is insufficient.

### Lemma 7.1 (conditional Wave projection)

Let \(\mathscr S_h^{\rm wav}\subset\mathscr S_h\) be a target
sublamination dominated by a source Wave
\(\mathscr B_h^{\rm wav}\subset X_h\).  Assume:

1. the six properness and marking clauses above;
2. \(\mathscr B_h^{\rm wav}\) ends at a marked multi-interval
   \(J_h\); and
3. \(P_h\) has degree at most \(d_h\leq D_h\) on \(J_h\).

Then KKL's Wave lemma supplies a Wave
\(\mathscr C_h^{\rm wav}\subset
P_{h*}\mathscr B_h^{\rm wav}\) satisfying

\[
\begin{aligned}
 \mathcal W(\mathscr S_h^{\rm wav})
 &\leq
 \mathcal W(\mathscr B_h^{\rm wav})\\
 &\leq
 \mathcal W(\mathscr C_h^{\rm wav})
 +c_{\rm W}(1+\log d_h)\\
 &\leq
 \mathcal W(\mathscr C_h^{\rm wav})+C_b.
\end{aligned}
\tag{7.1}
\]

Here \(c_{\rm W}\) denotes a constant admissible for the fixed source
normalization in the \(O(1+\log d)\) at KKL line 2151.  No numerical
value is claimed.  If the hidden constant is recorded only after the
parabolic bound and marking convention are fixed, it is absorbed into
\(C_b\).  With a uniform choice of \(c_{\rm W}\), one may take

\[
 C_b=c_{\rm W}\bigl(1+(b+2)\log2\bigr).
\tag{7.2}
\]

#### Proof

The first inequality is KKL domination.  The second is the Wave lemma
with degree \(d_h\), and the last follows from
\(d_h\leq D_h\leq2^{b+2}\). \(\square\)

Lemma 7.1 reduces width control to the **type of the actual output
Wave**.  It does not bound that output by itself.

## 8. Complete source-facing output classification

The following table records every output type that the locked
stationary proof uses.  “Bounded” always means a bound uniform over
the individual block after \(b\) is fixed.

| actual projected output | exact additional certificate | source consequence | bucket |
|---|---|---|---|
| vertical path family | proper completion as in Definition 6.1 | \(D_h(V+2)\) | \(V\)-charged |
| empty Wave after pushforward | actual emptiness in the marked surface | \(O_b(1)\) through (7.1) | bounded |
| Wave over \(BL_0\) | the entire packet lies in the one-step unbreakable part | \(O_b(1)\), KKL 1513--1521 | bounded |
| localized Wave away from \(BL_0\) | shifting base and the endpoint nesting in the Shift lemma | width at most \(2\) for the unbreakable part | bounded/response |
| localized Wave away from \(BL_0\) | only the hypotheses of KKL 1523--1532 | \(\mathcal W(C^{\rm nbr})\leq\mathcal W(C^{\rm sh})+O(1)\) | short residual plus bounded |
| lamination connecting the prescribed small-Julia component to the remaining small-Julia cycle | actual component incidence, proper paths, and degree bound | \(C_b(R(F)+1)\) | \(R\)-charged |
| one or two Waves arising from a genuine ambient break | end-properness, retained markings, bounded multiplicity, and controllability transport | the ambient leaf already lies in \(A^{H\text{-br}}\subset B_A\) | absorbed, not a survivor residual |
| a new response constructed from an ambient-singleton survivor | an independent survivor-response theorem | no consequence from KKL `small breaking` alone | survivor-response residual |
| Wave ending at \(BL_0\) through the full stationary horizon | precisely the missing alignment/pass-through theorem | no noncircular bound available | critical-end residual |
| path ending at a marking endpoint or discarded by the coarse subordinate filter | a new refinement/survival theorem would be needed | none | marking residual |
| escaping lift with nonunique ideal cluster or no Borel first-failure code | RLS\(_h\) would be needed | none | nonlanding residual |

Two rows need explicit derivations.

### 8.1 Small-Julia incidence is \(R\)-charged, not \(V\)-charged

Let \(\mathscr B_h^{\rm ren}\) be a proper source lamination in the
actual component-complement surface
\(\mathcal U^h\setminus\mathcal K^h\), obtained by restricting the
selected exit paths from the tree-complement surface.  Assume:

1. every leaf of
   \(\mathscr S_h^{\rm ren}\subset\mathscr S_h\) contributes a leaf
   of \(\mathscr B_h^{\rm ren}\), so KKL domination gives
   \[
     \mathcal W(\mathscr S_h^{\rm ren})
     \leq\mathcal W(\mathscr B_h^{\rm ren});
   \tag{8.1a}
   \]
2. \(\mathscr B_h^{\rm ren}\) connects one component \(K_h\) of the
   proof-used pulled small-Julia family to its prescribed complement;
3. its endpoints lie in the extension locus of the covering, and the
   degree on its ending set is at most \(D_h\); and
4. its \(P_h\)-image has exactly the component incidence used in KKL
   lines 1613--1617.

The passage from the tree complement to the component complement in
clause 1 is an analytic restriction obligation; it is not supplied by
the common access label alone.  Under these hypotheses, the
pushforward-lamination lemma gives a lamination
\(\mathscr C_h^{\rm ren}\) with

\[
 \mathcal W(\mathscr B_h^{\rm ren})
 \leq
 D_h\mathcal W(\mathscr C_h^{\rm ren})+2D_h.
\tag{8.1}
\]

KKL's renormalization-width comparison for this exact final
stationary incidence is

\[
 \mathcal W(\mathscr C_h^{\rm ren})\leq2R(F).
\tag{8.2}
\]

Hence, including domination from the target exit family,

\[
 \mathcal W(\mathscr S_h^{\rm ren})
 \leq
 2D_h\bigl(R(F)+1\bigr)
 \leq
 2^{h+1}\bigl(R(F)+1\bigr).
\tag{8.3}
\]

Equation (8.3) controls one actual incidence packet.  If a horizon
contains several component packets, their number cannot be suppressed
merely because the component inventory is finite.  Let \(q_b\) be a
proved upper bound, depending only on \(b\), for the number of
disjoint incidence packets required at one horizon.  Summing over the
finite horizon then gives

\[
 \sum_{h=1}^{b+2}
 \mathcal W(\mathscr S_h^{\rm ren})
 \leq
 q_b(2^{b+4}-4)\bigl(R(F)+1\bigr).
\tag{8.4}
\]

If no such uniform packet-count theorem has been proved, the packet
count remains an additional response-state coordinate and (8.4)
cannot be asserted uniformly.  In the native stationary KKL setting,
the required bound must be derived from the parabolically
\(b\)-bounded component and marking inventory; it is not inferred
here from the word “finite.”

This safe estimate uses the total degree.  A degree-one or
degree-two improvement requires the actual component degree theorem;
it is not inferred from a route label.

Clause 4 is therefore a genuine per-packet certification hypothesis.
KKL lines 1613--1617 prove (8.2) only after their final stationary
alignment has supplied the stated component incidence.  They do not
classify every earlier route horizon or every arbitrary small-Julia
attachment as such a packet.

Nothing in the locked clauses compares \(R(F)\) from above by
\(V(F)+1\).  Thus (8.4) does not imply the desired pure vertical
bound (1.1).

### 8.2 The critical-end row is circular

KKL Proposition `into the critical limb`, lines 1534--1537, states

\[
 \mathcal W(C^{N\text{-nbr}})
 \leq
 \mathcal W(C^{\rm sh})+O(R(F))
\tag{8.5}
\]

for a Wave \(C\) ending at \(BL_0\).  Its proof depends on the
alignment lemma at lines 1591--1605.  Line 1603 asserts that every
surviving leaf passes through a specified component; the current
stationary repair exists because that assertion is not established.

Therefore a route-exit proof may not cite (8.5) to control a projected
critical-end exit.  That would assume the conclusion whose defect is
being estimated.  Such a survivor exit belongs to
\(\mathscr S_h^{\rm crit}\) until either:

1. the segmented occurrence and component-incidence binder is proved
   for its actual proper restrictions; or
2. the exit is converted, with bounded multiplicity, into KKL's
   independent terminal-response configuration.

## 9. The proved conditional reduction

Assume RLS\(_h\) for \(1\leq h\leq b+2\), perform the ambient
survivor normalization (5.3), assume a proved uniform packet bound
\(q_b<\infty\) for the renormalization and bounded-Wave outputs at
each horizon, and assume **every survivor exit**, including the
nonuniquely landing class, admits a measurable partition, modulo
width zero, into

\[
\begin{split}
\mathscr S_h={}&
\mathscr S_h^{\rm ver}
\sqcup\mathscr S_h^{\rm ren}
\sqcup\mathscr S_h^{\rm bd}
\sqcup\mathscr S_h^{\rm newresp}\\
&\sqcup\mathscr S_h^{\rm crit}
\sqcup\mathscr S_h^{\rm out\text{-}sh}
\sqcup\mathscr S_h^{\rm mark}
\sqcup\mathscr S_h^{\rm nl}.
\end{split}
\tag{9.1}
\]

The first class must have the exact packet in Definition 6.1.  The
second must be a disjoint union of at most \(q_b\) packets satisfying
all four hypotheses in Section 8.1.  The bounded class must be a
disjoint union of at most \(q_b\) actual source-Wave packets, each of
which is one of the following:

1. its projected output Wave is empty;
2. its projected output is contained in the one-step unbreakable part
   of an actual Wave over \(BL_0\) to which KKL lines 1513--1521
   apply; or
3. its projected output is contained in the unbreakable part of an
   actual shifting-base Wave satisfying both endpoint-nesting
   hypotheses of KKL's Shift lemma.

Merely assigning the label ``bounded'' does not meet this hypothesis.
The new-response class must have a response theorem constructed on
ambient-singleton survivors, with bounded multiplicity and
controllability transport.  It cannot be justified merely by citing
KKL's one-step breakable-family proof.
The last four are retained residuals.

### Theorem 9.1 (survivor-exit charged/response reduction)

Under the preceding hypotheses,

\[
\begin{aligned}
\sum_{h=1}^{b+2}\mathcal W(\mathscr S_h)
\leq{}&
A_b\bigl(V(F)+1\bigr)
+
B_b\bigl(R(F)+1\bigr)\\
&+
\sum_{h=1}^{b+2}\Bigl[
 \mathcal W(\mathscr S_h^{\rm newresp})
 +\mathcal W(\mathscr S_h^{\rm crit})
 +\mathcal W(\mathscr S_h^{\rm out\text{-}sh})\\
&\hspace{40mm}
 +\mathcal W(\mathscr S_h^{\rm mark})
 +\mathcal W(\mathscr S_h^{\rm nl})
\Bigr],
\end{aligned}
\tag{9.2}
\]

where \(A_b,B_b<\infty\) depend only on the fixed parabolic bound.
One may take the vertical contribution to \(A_b\) to be
\(2^{b+4}-4\), before adding the bounded-output constants.

If the new-response sum has a fixed positive fraction of the ambient
Wave width, a separately proved survivor-response theorem may give
terminality instead of a numerical bound.  An actual KKL breaking
certificate would instead relabel those leaves into
\(A^{H\text{-br}}\subset B_A\), leaving no new residual.

#### Proof

By modulus subadditivity applied to (9.1),

\[
 \mathcal W(\mathscr S_h)
 \leq
 \sum_{\star}
 \mathcal W(\mathscr S_h^\star).
\tag{9.3}
\]

Theorem 6.2 bounds the sum of the vertical terms by
\((2^{b+4}-4)(V+1)\).  Equation (8.4) bounds the renormalization terms
by \(q_b(2^{b+4}-4)(R+1)\).  The empty, critical-over, and certified
Shift packets in \(\mathscr S_h^{\rm bd}\) have \(O_b(1)\) width by
Lemma 7.1 and KKL lines 1513--1532 and 2171--2178.  There are at most
\(q_b\) such packets at each of only \(b+2\) horizons, so their
additive total is absorbed into both displayed \(+1\) terms after
increasing \(A_b,B_b\).

No estimate has been asserted for the five retained survivor classes.
Keeping their widths on the right gives (9.2).  A terminal conclusion
for the new-response term is an additional theorem, not part of this
numerical reduction. \(\square\)

### Corollary 9.2 (what would prove the numerical target)

The source-faithful pure vertical estimate for the new survivor
conductance,

\[
 \sum_h\mathfrak S_h(F)\leq C_b(V(F)+1),
\tag{9.3a}
\]

follows from Theorem 9.1 only after proving all of:

\[
\begin{aligned}
 B_b(R(F)+1)
 &\leq C_b(V(F)+1),\\
 \sum_h\mathcal W(\mathscr S_h^{\rm newresp})
 &\leq C_b(V(F)+1),\\
 \sum_h\bigl[
   \mathcal W(\mathscr S_h^{\rm crit})
  +\mathcal W(\mathscr S_h^{\rm out\text{-}sh})
  +\mathcal W(\mathscr S_h^{\rm mark})
  +\mathcal W(\mathscr S_h^{\rm nl})
 \bigr]
 &\leq C_b(V(F)+1).
\end{aligned}
\tag{9.4}
\]

None of the three lines of (9.4) follows from the locked clauses.
The survivor-response route avoids the second numerical line only if
the independent response theorem is proved.  The original estimate
(1.1) for **all** exits also includes families already absorbed into
\(B_A\), and is not required by the disjoint stationary reduction.

## 10. First obstructions in dependency order

There are two distinct first obstructions.

### 10.1 Foundational obstruction: no source-defined exit measure

The first obstruction in a backward dependency audit is RLS\(_h\).
KKL define the restriction \(I_h^*\gamma\) setwise as the collection
of retained proper paths.  The source does not choose one Borel local
germ per leaf, prove that its maximal continuation has a unique ideal
landing, or prove that the resulting first-failure partition preserves
the transverse measure.

Therefore neither the proposed all-exit quantity
\(\mathfrak E_h(F)\) nor its survivor restriction
\(\mathfrak S_h(F)\) is yet an imported source object.  They become
legitimate extremal widths only after the RLS\(_h\) theorem and the
native leafwise survivor partition are realized measurably.

### 10.2 First analytic output obstruction after RLS\(_h\)

Grant RLS\(_h\), proper path completion, and all marking-survival
clauses.  The first output not controlled by the independent source
lemmas is:

\[
\boxed{
\text{an excess tree-side access whose retained pushforward is a
Wave ending at }BL_0.
}
\tag{10.1}
\]

It is not vertical, so Theorem 6.2 does not apply.  It need not have
the prescribed small-Julia component incidence, so (8.3) does not
apply.  It is not covered by the over-critical or away-from-critical
Shift estimates.  Invoking Proposition `into the critical limb` is
circular by Section 8.2.

The pointwise reduction in
`kkl_stationary_survivor_route_switch_reduction.md` sharpens this
obstruction.  Because the ambient leaf is \(N\)-unbreakable, the
  complete filtered \(F_*\)-image supplies a full retained replacement
  restriction at the first named-route failure and, pointwise, a
  complete alternative segmented chain through \(N\), after choosing
  the simple oriented path representatives and occurrence windows
  required by the segmented-binder lemma.  The first switch is
either a strict replacement path or a retained-path state mismatch.
This does not yet give a Borel replacement lamination, a uniform
multiplicity bound, or a width estimate.

The exact replacement invariant is therefore not one scalar route
conductance.  After all breakable and ambient-short leaves have been
absorbed into \(B_A\), it is the marked survivor-response tuple

\[
\mathfrak S_h^{\rm resp}
=
\left(
\begin{array}{c}
\mathcal W(\mathscr S_h^{\rm ver}),\
\mathcal W(\mathscr S_h^{\rm ren}),\
\mathcal W(\mathscr S_h^{\rm crit}),\\
\mathcal W(\mathscr S_h^{\rm out\text{-}sh}),\
\mathcal W(\mathscr S_h^{\rm mark}),\
\mathcal W(\mathscr S_h^{\rm nl});\\
\text{first-failure horizon, access, occurrence window, sheet,}\\
\text{properness flag, filter-survival flag, and response type}
\end{array}
\right).
\tag{10.2}
\]

The tuple may be forgotten only after each numerical coordinate is
charged or a large responsive coordinate is proved to force
terminality.

## 11. Adversarial checks

### 11.1 Artificial collar boundary

Touching or crossing a chosen collar boundary is not counted as a
branch failure.  Lemma 4.2 runs on the full immersion domain.  This
prevents an arbitrarily thin collar from creating arbitrarily large
fake exit conductance.

### 11.2 Hidden immersion sheet

An image collision with another sheet is not itself a failure
(Corollary 4.3).  If the lift later escapes along a nonproper end, it
must still receive an RLS\(_h\) landing code.  A sheet label alone
does not make the exit vertical.

### 11.3 Endpoint without access

A limit at a vertex of the pulled tree is ambiguous until the side
and access are specified.  Coding only the topological vertex can
misclassify a critical-end exit as an ordinary Shift exit.

### 11.4 Coarse filter loss

KKL lines 2096--2108 discard restrictions subordinate to one pulled
coarse interval.  Such a discarded segment cannot be inserted into a
Wave packet merely because it exists as a topological arc.

### 11.5 Non-locally-connected filled set

No local connectivity is assumed.  Proper ideal landing is an
explicit RLS\(_h\) hypothesis.  Euclidean convergence to a filled-set
point is not substituted for convergence to a marked ideal access.

### 11.6 Multiple first-failure horizons

The family must be partitioned by its **first** failed horizon.
Counting the same leaf at every later horizon can introduce a factor
depending on the route record.  The finite factor \(b+2\) is harmless
only after a measurable first-horizon partition is proved.

### 11.7 Width is not cardinality

A bounded number of access labels does not bound their extremal
width.  Every numerical estimate above uses domination plus a KKL
pushforward, Wave, Shift, or vertical-width lemma.

### 11.8 The \(R\)-term cannot be silently absorbed

The source gives a renormalization-width bound for actual
small-Julia incidence.  It does not give
\(R(F)\leq C_b(V(F)+1)\).  Equation (8.4) must therefore remain an
\(R\)-charge unless a new comparison is proved.

### 11.9 Critical-end circularity

The gap at line 1603 cannot be repaired by applying the proposition
whose proof contains line 1603.  The critical-end residual in (9.2)
is intentionally visible.

### 11.10 Abstract disk countermodel

The disk family in
`kkl_stationary_uniform_collar_charge_attack.md` has a globally
embedded immersion.  It confirms that global collar conductance and
route conductance are different quantities.  It does not refute
Theorem 6.2: a genuinely vertical selected path is still bounded by
the vertical annulus width.

### 11.11 Ambient breaking is not a new response coordinate

If a selected route exit is also an actual KKL break within the
horizon, its ambient leaf lies in
\(A^{H\text{-br}}\subset B_A\).  It must be relabelled there before
the defect widths are summed.  KKL's one-/two-Wave breaking argument
cannot simultaneously be used to create an additional responsive
residual carrying the same leaf mass.

### 11.12 Source-packet descent

Domination proves the numerical inequality in Theorem 6.2 from the
existence of a source restriction leaf for every target leaf.  A
disjoint defect ledger needs more: the complete selector must choose
one occurrence-tagged source leaf, at one first horizon, for each
ambient leaf, and that assignment must be injective modulo zero or
otherwise proved not to duplicate transverse mass.  Definition 6.1
records this stronger accounting requirement.

## 12. Exact next theorem

The next constructive theorem should not assert (1.1) wholesale.  It
should prove the following **route-exit trichotomy** on the actual
stationary leaf family:

1. construct the complete single-valued RLS\(_h\) selector and proper
   segmented restrictions;
2. relabel every ambient break and ambient-short exit into the native
   \(B_A\) term before summing widths;
3. prove every remaining nonshort ambient-survivor exit is either
   - a proper vertical packet,
   - an actual small-Julia incidence packet, or
   - an independently proved survivor-response packet;
4. prove that the critical-end, stage-output-short, marking, and
   nonlanding survivor residuals have zero width or enter the new
   response class with bounded multiplicity; and
5. keep the \(R(F)\)-charge separate unless a new
   \(R\)-to-\(V\) comparison is proved.

Equivalently, one may first prove the Marked Replacement Exclusion or
Charge Theorem stated in
`kkl_stationary_survivor_route_switch_reduction.md`: every strict-path
or marked-state switch is impossible, \(V\)-charged,
\(R\)-charged, or independently responsive, with a Borel selector and
uniformly bounded or summably charged multiplicity.

This trichotomy, combined with the algebraic response alternative,
is more source-faithful than a global collar estimate.  It also
identifies the first falsifiable failure certificate: a **nonshort
ambient-singleton survivor** with a marked critical-end access and a
proper retained itinerary which is neither vertical, small-Julia
incident, nor covered by an independent survivor-response theorem.

Until that theorem is proved, the stationary quantitative repair,
`VAAPC-I`, `UPTCR`, and `MLC` remain open.

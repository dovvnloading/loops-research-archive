# KKL stationary two-occurrence binder: minimal invariant and exact audit schema

> **Post-audit correction.**  The common-parameter equalizer theorem
> in Section 6 is correct, but it models only the special case in which
> every successive immersion image equals the whole preceding covering
> image.  KKL's actual set-valued restriction requires only
> containment in that image.  Valid sequential occurrences therefore
> use nested parameter windows, and the truncated fiber-product
> coordinates need not be proper even when every selected one-step
> path is proper.  Consequently the semantic core in Section 4 and the
> certificate in Section 7 are sufficient but not necessary and are
> **not** the minimal KKL binder.  They must not be used to promote
> `KKL_STATIONARY_TWO_OCCURRENCE_BINDER`.  The replacement invariant
> and an explicit degree-two annulus countermodel are in
> `kkl_stationary_segmented_occurrence_binder.md`.

## 1. Verdict and scope

This note isolates the smallest occurrence-level object that could prove
or refute

```text
KKL_STATIONARY_TWO_OCCURRENCE_BINDER
```

without confusing an untagged path image with a retained occurrence.
It proves the finite categorical part of the construction:

1. every path in the complete Kahn fiber product has a canonical
   synchronized array of one-step coordinates;
2. conversely, a commonly parameterized array satisfying every
   Cartesian synchronization identity determines a unique interior
   path in the complete fiber product;
3. if the stage paths also satisfy the proper-path and KKL retention
   predicates, their covering images form one coherent retained
   \(F_*\)-chain;
4. two such records do not imply two distinct terminal images.  That
   is the later deck-path noncollision problem.

The actual analytic existence of the two records attached to the two
portions in KKL line 1603 is **not** proved.  In particular, the note
does not infer:

- properness from a connected inverse image;
- filter survival from endpoint membership;
- a prime-end extension from an interval label;
- a common fiber-product occurrence from independent stagewise choices;
- terminal noncollision from distinct source components; or
- a measurable lamination from pointwise occurrence choices.

Thus the two-occurrence binder, retained-portion realization,
two-sided noncollision, VAAPC-I, UPTCR, and MLC remain open.

The principal refinement of the earlier record (7.1) in
`kkl_stationary_retained_realization_source_audit.md` is the following.
A complete component and a list of stage paths are not by themselves a
coherence certificate.  One must record either:

\[
 \text{one common-parameter path in the full fiber product},
\tag{1.1}
\]

or, equivalently, all pointwise Cartesian synchronization identities
needed to reconstruct it.  Untagged equality of consecutive path
images is weaker than (1.1).

## 2. Source locks and native limitations

The locked Kahn--Koropecki--Lyubich source is

```text
.tmp_wave_audit/waves-with-Misha.tex
SHA-256 AD4C774806D9902AA54FA31C56AD6146D8034946F19CC5E9CEC3C51A3F94FDD5
```

The current arXiv record was rechecked on 2026-07-26.  Its submission
history still contains only v1, submitted 2026-06-25.  Thus there is no
later public source revision from which to import an occurrence-level
repair.

The source occurrences used here are:

- line 406: a proper path is a map \((0,1)\to V\) extending to
  \([0,1]\) with both endpoints in the ideal boundary;
- lines 1241--1274: the actual pulled Hubbard-tree marking,
  Proposition 6.5, refinement
  \(f^*\mathcal I\succcurlyeq\iota^*\mathcal I\), and
  \(F_*BL_0=\partial_{\mathrm C}T\);
- lines 1354--1358: breaking and finite unbreakability;
- lines 1547--1548: \(N=b+3\) and the defined subwaves \(A_r\);
- lines 1597--1603: the selected pulled limbs, the one-path sentence,
  the separator, and the two proposed portions;
- lines 1844--1875: ideal markings, subordination, marked paths, and
  Waves;
- lines 2081--2108: immersion restriction, the line-2097 filter, and
  the three-way itinerary alternative;
- lines 2128--2167: the set-valued action \(F_*=f_*\iota^*\) and
  breaking.

The locked Kahn source is

```text
.tmp_kl06_source/psiql2.tex
SHA-256 E4EFCCEC65D8C9C2BDFE2AF8203B3D4D63ECF992B40D302F56FBA78259547228
```

The source occurrences used here are:

- lines 188--214: the pullback universal property and the
  set-theoretic equalizer;
- lines 259--265: when one leg is an immersion, the analytic pullback
  has the underlying topological pullback;
- lines 350--399: the first pseudo-polynomial-like pullback;
- lines 410--416: the finite tower and the commuting identities; and
- lines 418--424: identification of that tower with iteration of the
  underlying relation.

Two limitations are source-explicit.

First, KKL define
\(\iota^*\gamma\) as the set of proper paths **contained** in
\(\iota^{-1}(\gamma)\).  A retained component need not map onto the
whole of \(\gamma\).  Therefore equality of one untagged output with
the next stage's source label is not a pointwise gluing theorem.

Second, KKL Proposition 2099 allows a consecutive itinerary transition
to be represented by:

1. an actual restriction path;
2. adjacency; or
3. containment in one pulled target interval.

Only the first alternative supplies an occurrence.  The other two
cannot appear in a binder certificate.

## 3. The stationary fiber-product coordinates

Put

\[
 X_0=\mathcal V=U\setminus T,
 \qquad
 X_1=\mathcal V'=U'\setminus T',
\tag{3.1}
\]

and write the stationary one-step maps as

\[
 i_0=\iota:X_1\longrightarrow X_0,
 \qquad
 f_0=f:X_1\longrightarrow X_0.
\tag{3.2}
\]

Apply Kahn's pullback construction first to the ambient disks.  Kahn
lines 418--421 identify its underlying set with the finite relation
chain

\[
 \mathcal U^{[h]}
 =
 \left\{
 (z_1,\ldots,z_h)\in(\mathcal U')^h:
 f_0(z_r)=i_0(z_{r+1})\ (1\le r<h)
 \right\}.
\tag{3.3a}
\]

This formula fixes the order of the coordinates and does not assume
that an immersion leg is globally injective.  On the complementary
surfaces define the safe relation domain

\[
 X_h
 =
 \left\{
 (z_1,\ldots,z_h)\in\mathcal U^{[h]}:
 z_r\in X_1\text{ for every }r
 \right\}.
\tag{3.3b}
\]

Every trace occurring below is required to lie in (3.3b).  KKL line
1707 supplies the same proof-used complete iterate on
\(\mathcal U^h\setminus\mathcal T^h\); identifying a proposed trace
with that native host, including every pulled obstacle, is part of the
analytic certificate and is not inferred merely from ambient
fiber-product notation.

The ambient pullback tower has maps

\[
 i_r,f_r:X_{r+1}\longrightarrow X_r
 \qquad(r\geq0)
\tag{3.3}
\]

such that

\[
 i_r\circ f_{r+1}=f_r\circ i_{r+1}.
\tag{3.4}
\]

For a horizon \(h\geq1\), define

\[
 I_h=i_0\circ i_1\circ\cdots\circ i_{h-1},
 \qquad
 P_h=f_0\circ f_1\circ\cdots\circ f_{h-1}.
\tag{3.5}
\]

These are respectively the complete immersion and proper projections
on the ambient tower.  Their restrictions are the proof-used maps on
the safe relation domain.  Properness of a path at the ideal boundary
is not inherited from ambient properness and remains an explicit
clause below.

For \(1\leq r\leq h\), define the \(r\)-th one-step coordinate

\[
\begin{split}
 q_{h,r}
 &=
 f_1\circ\cdots\circ f_{r-1}
 \circ
 i_r\circ\cdots\circ i_{h-1}
 :
 X_h\longrightarrow X_1.
\end{split}
\tag{3.6}
\]

An empty string of \(f\)'s or \(i\)'s is the identity.  Thus

\[
 q_{h,1}=i_1\circ\cdots\circ i_{h-1},
 \qquad
 q_{h,h}=f_1\circ\cdots\circ f_{h-1}.
\tag{3.7}
\]

Also define the prefix projection

\[
 \pi_{h,r}
 =
 i_r\circ i_{r+1}\circ\cdots\circ i_{h-1}
 :
 X_h\longrightarrow X_r.
\tag{3.8}
\]

### Lemma 3.1 (coordinate synchronization)

For \(1\leq r<h\),

\[
 f_0\circ q_{h,r}=i_0\circ q_{h,r+1}.
\tag{3.9}
\]

Moreover,

\[
 I_h=i_0\circ q_{h,1},
 \qquad
 P_h=f_0\circ q_{h,h}.
\tag{3.10}
\]

#### Proof

Formula (3.10) follows directly from (3.5)--(3.7).  For (3.9), start
with

\[
 f_0\circ f_1\circ\cdots\circ f_{r-1}
 \circ i_r\circ\cdots\circ i_{h-1}.
\tag{3.11}
\]

The case \(j=r-1\) of (3.4) is

\[
 f_{r-1}\circ i_r=i_{r-1}\circ f_r.
\tag{3.12}
\]

Use (3.12) in (3.11), then use the cases
\(j=r-2,r-3,\ldots,0\) successively.  This moves the \(i\)-map all the
way to the left and gives

\[
 i_0\circ f_1\circ\cdots\circ f_r
 \circ i_{r+1}\circ\cdots\circ i_{h-1},
\tag{3.13}
\]

which is \(i_0\circ q_{h,r+1}\). \(\square\)

The identities in Lemma 3.1 are equalities of maps, not merely
equalities of component labels.  They are the synchronization laws
that an occurrence audit must preserve.

## 4. Semantic occurrence core

Fix a proof-used

\[
 b\leq n\leq N-2=b+1,
 \qquad
 h=n+1,
 \qquad
 \alpha\in A_h.
\tag{4.1}
\]

The upper bound in (4.1) is mandatory because \(A_N\) is not defined by
KKL line 1548.

Let \(|\alpha|\subset X_0\) denote the image of a selected
parameterization of the leaf.  A **full occurrence component** is a
connected component

\[
 C\in\operatorname{Comp}\bigl(I_h^{-1}(|\alpha|)\bigr).
\tag{4.2}
\]

The component (4.2) is not yet a path.  A **semantic occurrence core**
is a tuple

\[
 \mathfrak o
 =
 \bigl(
   C,[\Theta],\epsilon,\mathfrak r
 \bigr),
 \qquad
 \epsilon\in\{-,+\},
\tag{4.3}
\]

with the following data and conditions.

1. \(\Theta:(0,1)\to C\subset X_h\) is a continuous path, considered
   modulo orientation-preserving reparameterization.
2. \(\Theta\) extends to a proper path
   \[
      \overline\Theta:[0,1]\longrightarrow
      X_h\cup\partial_I X_h.
   \tag{4.4}
   \]
   The actual two endpoint prime ends, not only their host intervals,
   are part of \(\mathfrak r\).
3. For every stage \(r\), the one-step coordinate
   \[
      \gamma_r=q_{h,r}\circ\Theta
   \tag{4.5}
   \]
   is a proper path in
   \((X_1,f^*\mathcal I)\).
4. No \(\gamma_r\) is subordinate to one interval of
   \(\iota^*\mathcal I\).  Thus every \(\gamma_r\) survives the exact
   KKL line-2097 filter.
5. The initial trace
   \[
      \delta_0=I_h\circ\Theta=i_0\circ\gamma_1
   \tag{4.5a}
   \]
   is itself a proper path in \((X_0,\mathcal I)\).  When the record is
   asserted to arise from the source leaf \(\alpha\), the same
   parameterization also certifies
   \(\delta_0((0,1))\subset|\alpha|\).  Properness alone is not enough:
   without the marked-path predicate, \(F_*\delta_0\) is not typed.
6. The route record \(\mathfrak r\) identifies actual ordered endpoint
   accesses and actual subarcs showing that the occurrence realizes
   the \(\epsilon\)-portion in KKL line 1603.  An adjacency or a
   same-pulled-interval step is forbidden.

Define the synchronized base traces

\[
\begin{aligned}
 \delta_0&=i_0\circ\gamma_1=I_h\circ\Theta,\\
 \delta_r&=f_0\circ\gamma_r
          =i_0\circ\gamma_{r+1}
          &&(1\leq r<h),\\
 \delta_h&=f_0\circ\gamma_h=P_h\circ\Theta.
\end{aligned}
\tag{4.6}
\]

The middle equality is Lemma 3.1.  The path \(\delta_0\) may be the
proof-used portion of \(\alpha\), rather than all of \(\alpha\).
This is allowed by KKL's definition of immersion restriction, but
clause 5 separately requires that it be a proper marked path and that
its image containment in the selected leaf be certified.  Neither
property follows from an untagged interval label.

### Why the core is minimal

Once the tower, ideal markings, and route convention are frozen, the
semantic information is:

\[
 \boxed{\text{component }C
 \;+\;
 \text{common-parameter path }[\Theta]
 \;+\;
 \text{oriented route type }\epsilon.}
\tag{4.7}
\]

The stage paths, trace images, sheet fibers, endpoint intervals, and
filter decisions are derived from (4.7).  They must nevertheless be
written into an audit certificate because each derived assertion is a
separate proof obligation.  A symbolic stage list without
\([\Theta]\), or without the synchronization laws equivalent to it,
does not encode (4.7).

## 5. The complete audit expansion

For a semantic occurrence core, the following finite record is its
**audit expansion**:

\[
\begin{split}
 \mathfrak B^\epsilon_{n,\alpha}
 =\bigl(
 &h,\alpha,\epsilon;
 C,[\Theta],\phi^{\rm base}_0;
 \{C_r,\gamma_r,\delta_{r-1},\delta_r\}_{r=1}^{h};\\
 &\{\mathfrak e_{r,\nu}\}_{r,\nu};
 \{s_r,p_r,\phi_r,\omega_r\}_{r=1}^{h};
 \mathfrak r,\mathfrak t
 \bigr),
\end{split}
\tag{5.1}
\]

where \(\nu\in\{0,1\}\) is the oriented endpoint index.

### 5.1 Stage component and maps

The prefix host component is

\[
 C_r
 =
 \operatorname{Comp}_{\,\pi_{h,r}(\Theta)}
 \bigl(I_r^{-1}(|\alpha|)\bigr).
\tag{5.2}
\]

This notation means the unique component containing
\(\pi_{h,r}(\Theta)\).  It asserts containment, not the stronger and
generally unproved equality

\[
 \pi_{h,r}(C)=C_r.
\tag{5.3}
\]

If a downstream proof uses (5.3), it must be added and proved as a
separate component-surjectivity clause.

For each \(r\), the record stores the literal formulas

\[
 \gamma_r=q_{h,r}\Theta,
 \qquad
 \delta_{r-1}=i_0\gamma_r,
 \qquad
 \delta_r=f_0\gamma_r.
\tag{5.4}
\]

For \(r<h\), it also stores the Cartesian checksum

\[
 f_0\gamma_r=i_0\gamma_{r+1}
\quad\text{pointwise under one common parameter.}
\tag{5.5}
\]

Set equality after forgetting parameter and occurrence is not (5.5).

The base-path record appearing in (5.1) is

\[
 \phi^{\rm base}_0
 =
 \bigl(
   \mathrm{Prop}_0,\mathrm{Marked}_0,
   \delta_0((0,1))\subset|\alpha|;
   \mathsf w_0
 \bigr).
\tag{5.5a}
\]

Here \(\mathrm{Prop}_0=\mathrm{Marked}_0=1\), and
\(\mathsf w_0\) is the actual proper-extension, endpoint-marking, and
image-containment witness.  This datum is logically separate from the
fine/coarse retention record for the lifted paths \(\gamma_r\).

### 5.2 Endpoint and protected-access record

For each endpoint, put

\[
 \mathfrak e_{r,\nu}
 =
 \bigl(
   \zeta_{r,\nu},
   J^f_{r,\nu},
   \widetilde J^\iota_{r,\nu},
   o_{r,\nu},
   a_{r,\nu},
   \sigma_{r,\nu},
   \tau_{r,\nu}
 \bigr).
\tag{5.6}
\]

Here:

- \(\zeta_{r,\nu}\in\partial_I X_1\) is the actual ideal endpoint of
  \(\gamma_r\);
- \(J^f_{r,\nu}\in f^*\mathcal I\) is its fine host interval;
- \(\widetilde J^\iota_{r,\nu}\in\iota^*\mathcal I\) is its coarse
  host interval;
- \(o_{r,\nu}\) is the origin flag:
  \[
     o_{r,\nu}
     =
     \operatorname{direct}
     \quad\text{or}\quad
     \operatorname{attached}(X,x),
  \tag{5.7}
  \]
  where \(X\) is an actual component of \(T'\setminus T\) attached at
  the actual point \(x\in T\);
- \(a_{r,\nu}\) is the marked prime-end access, including its side;
- \(\sigma_{r,\nu}\) is the cyclic-order slot in the complete local
  marking; and
- \(\tau_{r,\nu}\) is the complete rooted parent/predecessor word for
  the endpoint's tree or attachment component.

The distinction in (5.7) is forced by KKL Proposition 6.5: direct
inverse intervals and Carathéodory boundaries of attached components
can belong to the same coarse interval.  Their coarse label alone does
not determine filter behavior or survival under a later root
enlargement.

### 5.3 Sheet record

Choose once and for all any interior parameter \(t_*\in(0,1)\).  If a
later sheet convention requires avoiding cuts or crossings, the
certificate must separately name the forbidden set and prove that an
admissible \(t_*\) exists.  No finiteness of such a set is assumed
here.  Define

\[
 s_r=
 \bigl(
  t_*,
  \gamma_r(t_*),
  \delta_{r-1}(t_*),
  \delta_r(t_*)
 \bigr).
\tag{5.8}
\]

It carries the two checked identities

\[
 i_0(\gamma_r(t_*))=\delta_{r-1}(t_*),
 \qquad
 f_0(\gamma_r(t_*))=\delta_r(t_*).
\tag{5.8a}
\]

Thus \(s_r\) is an actual source point together with both its immersion
fiber and covering fiber.  After choosing base lifts, the two fiber
positions can equivalently be recorded by deck cosets.  A bare integer
``sheet number'' is not invariant under a change of base lift, while
(5.8)--(5.8a) are.

The sheet record is not a substitute for the full relative homotopy
class of the path.  Two paths can have the same endpoint fiber data and
different winding.

### 5.4 Parent and attachment record

The parent record is

\[
 p_r=
 \bigl(
   \operatorname{parent}(\gamma_r),
   \operatorname{attachment\ access},
   \operatorname{root\ ancestry},
   \operatorname{stage\ sheet}
 \bigr).
\tag{5.9}
\]

Every parent is an actual component or actual side of the pulled
Hubbard tree.  A coarse color, depth, or limb label is insufficient,
because multiple components with the same label may be absorbed into
one interval of \(\iota^*\mathcal I\).

### 5.5 Exact filter record

Let

\[
 \operatorname{Sub}_{\iota^*\mathcal I}(\gamma_r)
 =
 \left\{
  \widetilde J\in\iota^*\mathcal I:
  \gamma_r\text{ is subordinate to }\widetilde J
 \right\}.
\tag{5.10}
\]

The filter record is

\[
 \phi_r=
 \bigl(
  \mathrm{Prop}_r,\mathrm{Marked}_r,
  \operatorname{Sub}_{\iota^*\mathcal I}(\gamma_r),
  \mathrm{Retained}_r;
  \mathsf w_r
 \bigr),
\tag{5.11}
\]

where:

- \(\mathrm{Prop}_r=1\) means that the prime-end extension is proper;
- \(\mathrm{Marked}_r=1\) means that \(\gamma_r\) is a path in
  \((X_1,f^*\mathcal I)\), including KKL's non-subordination to a
  fine multi-interval of length at most two;
- \(\mathrm{Retained}_r=1\) means
  \[
    \mathrm{Prop}_r=\mathrm{Marked}_r=1,
    \qquad
    \operatorname{Sub}_{\iota^*\mathcal I}(\gamma_r)=\varnothing;
  \tag{5.12}
  \]
- \(\mathsf w_r\) is the actual proof of (5.12), or, on failure, the
  first offending fine or coarse interval.

The Boolean in (5.12) is not evidence by itself.  The proof must use
the full proper-arc class.  Accordingly \(\omega_r\) in (5.1) is the
relative homotopy/deck word of \(\gamma_r\), with actual endpoint
accesses fixed.  Endpoint intervals alone do not determine
\(\omega_r\).

### 5.6 Route and terminal record

The route record \(\mathfrak r\) consists of a finite ordered hit word

\[
 \mathfrak r
 =
 \bigl(
   H_0,H_1,\ldots,H_\ell;
   \{\theta_j\}_{j=0}^{\ell-1}
 \bigr),
\tag{5.13}
\]

where every \(H_j\) is an actual marked side, component, or access and
every \(\theta_j\) is an actual nonconstant subarc connecting
\(H_j\) to \(H_{j+1}\).  The two required signatures are

\[
\begin{aligned}
 \epsilon=-:\quad&
 BL_0\rightsquigarrow L_0^{\,n+1},\\
 \epsilon=+:\quad&
 L_0^{\,n+1}
 \rightsquigarrow
 \partial_{\mathrm C}T\setminus BL_0.
\end{aligned}
\tag{5.14}
\]

The record must state on which level each symbol in (5.14) lives and
which prime-end access represents it.  An itinerary edge certified
only by adjacency or same-pulled-interval containment is not a
\(\theta_j\).

The terminal record is

\[
 \mathfrak t=
 \bigl(
  \delta_h,
  [\delta_h],
  J_{h,\mathrm{in}},
  J_{h,\mathrm{out}},
  \text{named terminal Wave-family membership}
 \bigr).
\tag{5.15}
\]

For one leaf, the last entry means that \(\delta_h\) is a retained
path belonging to the named Wave family.  It does not assert that a
singleton path has positive extremal width.

## 6. What the fiber-product universal property proves

### Theorem 6.1 (synchronized-chain reconstruction)

Let

\[
 \gamma_r:(0,1)\longrightarrow X_1,
 \qquad 1\leq r\leq h,
\tag{6.1}
\]

be continuous parameterized paths satisfying

\[
 f_0\circ\gamma_r=i_0\circ\gamma_{r+1}
 \qquad(1\leq r<h)
\tag{6.2}
\]

pointwise.  Then there is a unique continuous path

\[
 \Theta:(0,1)\longrightarrow X_h
\tag{6.3}
\]

such that

\[
 q_{h,r}\circ\Theta=\gamma_r
 \qquad(1\leq r\leq h).
\tag{6.4}
\]

Conversely, every continuous \(\Theta\) in (6.3) produces paths
\(\gamma_r=q_{h,r}\Theta\) satisfying (6.2).

#### Proof

Kahn's lines 203--208 identify a topological pullback with its
set-theoretic equalizer, lines 259--265 show that an analytic pullback
along an immersion has that underlying topological space, and lines
418--421 identify the iterated pullback with iteration of the
underlying relation.  Hence (3.3a) is the literal point-set model of
the ambient \(h\)-fold pullback.

Define

\[
 \Theta(t)=
 \bigl(\gamma_1(t),\ldots,\gamma_h(t)\bigr).
\tag{6.5a}
\]

Equation (6.2) says exactly that (6.5a) belongs to the relation-chain
equalizer (3.3a) for every \(t\).  Since every \(\gamma_r\) lands in
\(X_1\), it in fact belongs to the safe domain (3.3b).  The equalizer
has the subspace topology, so \(\Theta\) is continuous.  Its coordinate
projections are the prescribed paths; under the canonical
identification of (3.3a) with Kahn's recursively defined pullback,
those coordinate projections are precisely (6.4).  This proves
existence.

If two paths have all the same one-step coordinates, their ordered
tuples in (3.3a) agree pointwise.  They are therefore equal, proving
uniqueness.  Conversely, a path in the relation-chain equalizer
satisfies every defining equality in (3.3a), which is (6.2).
\(\square\)

### Qualification 6.2

Theorem 6.1 is an interior categorical theorem.  It does **not** prove
any of the following:

1. that \(\Theta\) extends properly to the ideal boundary of \(X_h\);
2. that a coordinate \(\gamma_r\) is a proper marked path;
3. that a coordinate survives the line-2097 filter;
4. that \(\Theta\) is an entire connected component of an inverse
   image;
5. that its endpoints land at the claimed accesses; or
6. that two reconstructed paths belong to different complete
   components.

Those are the analytic clauses in Sections 4--5.

### Corollary 6.3 (coherence criterion)

A list of one-step path occurrences represents one common interior
fiber-product occurrence if and only if it admits orientation-compatible
parameterizations satisfying (6.2).

#### Proof

The forward implication is the converse clause of Theorem 6.1.  The
reverse implication is its reconstruction clause. \(\square\)

In particular, the following data are insufficient:

\[
 f_0(|\gamma_r|)
 =
 i_0(|\gamma_{r+1}|)
\quad\text{as untagged sets},
\tag{6.5}
\]

or

\[
 [f_0\gamma_r]=[i_0\gamma_{r+1}]
\quad\text{as unmarked homotopy classes}.
\tag{6.6}
\]

They forget parameter order, occurrence provenance, and endpoint
accesses.

### Proposition 6.4 (retained-chain consequence)

Let \(\mathfrak o\) be a semantic occurrence core.  Then

\[
 \delta_r\in F_*\delta_{r-1}
 \qquad(1\leq r\leq h).
\tag{6.7}
\]

Consequently

\[
 \delta_h\in F_*^h\delta_0.
\tag{6.8}
\]

If \(\delta_0\) is a proper restriction portion of \(\alpha\) and
\(\gamma_1\subset i_0^{-1}(\alpha)\), then the same complete record
proves

\[
 \delta_h\in F_*^h\alpha .
\tag{6.8a}
\]

#### Proof

By (4.6),

\[
 i_0(\gamma_r)=\delta_{r-1},
 \qquad
 f_0(\gamma_r)=\delta_r.
\tag{6.9}
\]

The stage-admissibility clauses say that \(\gamma_r\) is a proper path
contained in \(i_0^{-1}(\delta_{r-1})\), is a path in the fine marking,
and is not subordinate to one interval in the coarse marking.
Therefore it is one of the components retained by KKL line 2097.
The definition \(F_*=f_*\iota^*\) gives (6.7).  Induction gives
(6.8).  Under the final hypotheses, \(\gamma_1\) is also a retained
member of \(i_0^*\alpha\), because its proper-path and subordination
properties are properties of that same source path.  Hence
\(\delta_1=f_0(\gamma_1)\in F_*\alpha\).  Apply (6.7) for stages
\(2,\ldots,h\) to obtain (6.8a). \(\square\)

### Proposition 6.5 (what two retained occurrences do not prove)

Two semantic occurrence cores may have distinct complete components

\[
 C^-\ne C^+
\tag{6.10}
\]

and nevertheless satisfy

\[
 \delta_h^-=\delta_h^+
\tag{6.11}
\]

after the occurrence tags are forgotten.

#### Proof

The map \(P_h\) need not be injective on the union of two distinct
immersion-restriction components.  The exact quadratic
pseudo-quadratic-like model in
`stationary_occurrence_collision_obstruction.md` already has two
distinct proper source components interchanged by \(z\mapsto-z\) and
one common \(z^2\)-image.  That model is not asserted to be a KKL Wave,
but it proves that (6.10) does not imply (6.11)'s negation from the
abstract map types alone. \(\square\)

Thus the two-occurrence binder must precede, and cannot replace,
`KKL_STATIONARY_SELECTED_COLLAR_DECK_NONCOLLISION`.

## 7. Candidate binder certificate

A **pointwise stationary two-occurrence certificate** is

\[
 \mathfrak C_{n,\alpha}
 =
 \bigl(
   \mathfrak B^-_{n,\alpha},
   \mathfrak B^+_{n,\alpha},
   \mathsf w_{\rm sep}
 \bigr),
\tag{7.1}
\]

where:

1. both records use the same tower, horizon \(h=n+1\), and leaf
   occurrence \(\alpha\);
2. both are valid semantic occurrence cores with complete audit
   expansions;
3. \(\mathfrak B^-\) has the first route in (5.14), and
   \(\mathfrak B^+\) has the second;
4. every stage has \(\mathrm{Retained}_r^\epsilon=1\);
5. each terminal trace belongs to the named terminal Wave family with
   actual endpoint intervals recorded;
6. \(C^-\ne C^+\); and
7. \(\mathsf w_{\rm sep}\) is an analytic component-separation
   witness, such as disjoint component localizations or separation by
   a specified removed full continuum.  Two different symbolic
   component IDs are not a witness.

No inequality

\[
 \delta_h^-\ne\delta_h^+
\tag{7.2}
\]

is included in (7.1).  Equation (7.2) is precisely a later
noncollision clause.

### Theorem 7.1 (certificate soundness)

If a certificate (7.1) is analytically realized, then the two portions
in KKL line 1603 have two distinct, coherent, fully retained
fiber-product occurrence records through the complete horizon.

If, in addition, (7.2) is proved, then the \(h\)-fold untagged action
contains at least two path elements.  Hence the source leaf is not
\(h\)-unbreakable: some single path in its orbit breaks at a stage
strictly before \(h\).

#### Proof

The route clauses bind the two records to the two actual portions.
Theorems 6.1 and 6.4 prove full-horizon coherence and retained
membership.  Clause 6 and the witness in clause 7 give distinct
complete components.

Under (7.2), Proposition 6.4 supplies two different members of the
final \(F_*^h\)-image.  Let \(m\leq h\) be the first index for which
\(F_*^m\alpha\) is not a singleton.  The final image is nonempty, so
no earlier image can be empty.  Therefore
\(F_*^{m-1}\alpha=\{\beta\}\) for one path \(\beta\), while
\(F_*\beta\) contains at least two paths.  By KKL line 2161,
\(\beta\) breaks under \(F_*\); equivalently, \(\alpha\) is not
\(h\)-unbreakable. \(\square\)

Theorem 7.1 is a soundness theorem for a supplied analytic
certificate.  It does not construct the certificate.

### Lemma 7.2 (finite ribbon-route split)

Let \(R\) be a finite tree, let \(u,v,x\in R\), and suppose the unique
simple path \([u,v]_R\) contains \(x\) with \(x\notin\{u,v\}\).  Then

\[
 [u,v]_R=[u,x]_R\cup[x,v]_R,
 \qquad
 [u,x]_R\cap[x,v]_R=\{x\},
\tag{7.3}
\]

and the two oriented portions are uniquely determined.

#### Proof

A tree contains a unique simple path between every two vertices.
Both \([u,x]_R\) and \([x,v]_R\) are subpaths of \([u,v]_R\).  If
their intersection contained a point other than \(x\), their union
would contain a cycle or the original \(u\)-to-\(v\) path would not be
simple.  Their union is connected and contains \(u,v\), hence equals
the unique path \([u,v]_R\). \(\square\)

Lemma 7.2 validates the finite combinatorial decomposition only after
the actual path incidence at \(x\) is known.  It does not prove that
either ribbon portion is realized by a proper analytic restriction,
survives KKL's filter, or lands at a specified prime end.

## 8. Pointwise versus family-level binders

KKL's definition of breaking is pointwise, so Theorem 7.1 needs only
the two records for one \(\alpha\).  Width and domination arguments
need more.

A **family binder** over a sublamination \(A^\circ\subset A_h\) must
add:

1. Borel or otherwise source-authorized selections
   \[
      \alpha\longmapsto
      \mathfrak B^\epsilon_{n,\alpha};
   \tag{8.1}
   \]
2. pairwise disjointness of the selected path representatives in each
   sign family;
3. occurrence multiplicity and measurable weights;
4. proof that the selected family is a lamination in the final marked
   surface; and
5. the hypotheses of KKL's restriction-domination lemma.

None of these follows from pointwise finite choice.  Conversely, they
are not needed to decide whether a single leaf breaks.  Keeping the
two levels separate prevents a measurable-selection obligation from
being hidden in a pointwise binder.

## 9. Necessity audit for every recorded field

| omitted datum | adversarial failure | exact consequence |
|---|---|---|
| full component \(C\) | two source occurrences have one untagged image | multiplicity is lost |
| common parameter \([\Theta]\) or (5.5) | independently retained stages have matching labels but no proved pointwise lift | no full fiber-product occurrence |
| prime-end extension | an interior inverse trace escapes through a nonproper end | no proper path |
| fine interval \(J^f\) | an endpoint lies outside the refined marking | the coordinate is not a KKL path |
| coarse interval \(\widetilde J^\iota\) | both ends are absorbed into one pulled interval | line 2097 removes the coordinate |
| direct/attachment origin | late root enlargement merges an attached boundary with a direct interval | filter history is not stable |
| actual access and cyclic slot | the same interval has multiple accesses or monodromy swaps sides | the route sign is not defined |
| fiber-point/deck sheet \(s_r\) | deck-related lifts have identical base labels | occurrence distinction disappears |
| relative homotopy word \(\omega_r\) | two paths have the same endpoints and different winding | endpoint pairs do not decide collision or subordination |
| parent component and ancestry | equal limb labels refer to different pulled components | attachment routing is ambiguous |
| route hit word \(\mathfrak r\) | both records realize the same separator side | no minus/plus binder |
| complete horizon | a late filter or attachment failure is omitted | a prefix is misreported as a complete occurrence |
| terminal family membership | the output is retained but has the wrong Wave base or crest | the source line-1603 conclusion is not typed |
| family selector, when widths are used | pointwise choices cross or are nonmeasurable | no lamination and no domination inequality |

This table establishes logical necessity relative to the stated proof
architecture.  It does not assert that every row is realized by an
actual KKL block.

## 10. First-failure certificate

For a proposed sign \(\epsilon\), inspect the stages in increasing
order.  The first failure record is

\[
\begin{split}
 \mathfrak F
 =(&n,\alpha,\epsilon,h,r;
 C,C_r,\gamma_r,\delta_{r-1},\delta_r;\\
 &\mathfrak e_{r,0},\mathfrak e_{r,1},
 s_r,p_r,\omega_r;
 \mathrm{code},\mathrm{witness}).
\end{split}
\tag{10.1}
\]

The allowed codes are:

```text
F0_TOWER_TYPE
F1_NO_FULL_COMPONENT
F2_NO_PROPER_CORE
F3_NOT_FINE_MARKED_PATH
F4_COARSE_SUBORDINATION
F5_CARTESIAN_SYNC
F6_WRONG_ROUTE
F7_ACCESS_OR_CYCLIC_ORDER
F8_COMPONENT_MERGER
F9_TERMINAL_NOT_IN_WAVE
F10_FAMILY_SELECTION
F11_TERMINAL_COLLISION
```

`F11_TERMINAL_COLLISION` is not a failure of the pointwise binder; it
is a failure of the later noncollision theorem.  `F10` is not a
failure of a pointwise binder; it is a failure of its family-level
promotion.

A failed proposed record does not refute the binder theorem.  A
refutation must prove that **every** possible candidate for one sign
fails, or exhibit an actual block in which one of the required route
fibers is empty.  Since relative homotopy and deck classes may be
infinite, finiteness of the Wave horizon alone does not justify
enumerating all analytic candidates.

## 11. Exact remaining analytic theorem

The finite categorical work reduces the open binder to the following
source-specific assertion.

> **Analytic two-route realization problem.**  
> For every proof-used \(n,\alpha\) satisfying the line-1603
> non-pass-through antecedent, construct two proper paths
> \(\Theta^\pm\) in \(X_{n+1}\) such that:
>
> 1. their actual component hosts in
>    \(I_{n+1}^{-1}(|\alpha|)\) are distinct;
> 2. their prime-end endpoint records realize the two ordered routes
>    in (5.14);
> 3. every coordinate \(q_{n+1,r}\Theta^\pm\) is a path in
>    \(f^*\mathcal I\);
> 4. no coordinate is subordinate to one interval of
>    \(\iota^*\mathcal I\);
> 5. all direct-versus-attached origins and parent predecessor words
>    agree with KKL Proposition 6.5; and
> 6. both terminal traces belong to the required terminal Wave
>    families.

The locked source proves none of clauses 1--6 for both routes.  Its
one-chain theorem proves only that some retained coordinate exists at
each unbreakable stage after occurrence tags have been forgotten.

The proof should attack clause 2 first on the actual final pulled
surface, then compute clauses 3--5 from the resulting paths.  Starting
from an interval itinerary is logically weaker because its adjacency
and same-pullback alternatives do not define \(\Theta^\pm\).

## 12. Adversarial validation

The companion script

```text
audit_stationary_two_occurrence_binder_schema.py
```

tests only the finite certificate logic.  It checks:

1. a syntactically complete two-record certificate;
2. rejection of a broken Cartesian synchronization;
3. rejection of a line-2097 filter loss;
4. rejection of a missing parent/access field;
5. rejection of a false distinct-component claim;
6. acceptance of equal endpoint pairs with different homotopy words;
7. acceptance of a binder whose terminal images collide, while
   separately rejecting it as a noncollision certificate; and
8. rejection of stagewise nonempty labels that do not form one
   synchronized chain;
9. rejection of a nonpositive horizon;
10. rejection of a missing proper full-core predicate;
11. rejection of an unmarked initial trace; and
12. acceptance of an expanded route word when its first and last
    accesses, and every intervening subarc witness, are correct.

These are diagnostic regressions.  They do not establish analytic
existence, properness, prime-end landing, or KKL-specific noncollision.

## 13. Skeptic audit

1. The proof-used range is \(n=b,b+1\), never the undefined \(A_N\).
2. A connected inverse-image component is not called a proper path.
3. A proper full-tower path is not assumed to have proper coordinate
   projections.
4. A stagewise list is not called coherent without pointwise
   synchronization.
5. Set-image equality is not substituted for occurrence equality.
6. An interval label is not substituted for a prime-end access.
7. An endpoint pair is not substituted for a relative homotopy class.
8. A filter Boolean is not treated as its own proof.
9. Attachment absorption is not promoted to an actual loss without
   whole-path subordination.
10. Distinct full components are not promoted to distinct terminal
    images.
11. A pointwise selection is not promoted to a measurable lamination.
12. The finite reconstruction theorem is not promoted to analytic
    realization.
13. No global obligation is promoted in this note.

## 14. Conclusion

The correct minimal occurrence invariant is one component-tagged,
commonly parameterized proper path in the complete Kahn fiber product,
together with its oriented route.  The endpoint, access, sheet,
parent, homotopy, filter, and terminal arrays are the mandatory audit
expansion of that semantic core.

The full fiber-product universal property now closes the finite
coherence calculation: exact pointwise stage synchronization is
necessary and sufficient for an interior full-horizon path.  The
remaining obstacle is purely analytic and source-specific: construct
the two route cores, prove every prime-end and filter clause, and prove
their component separation on the actual KKL pulled Hubbard-tree
surfaces.

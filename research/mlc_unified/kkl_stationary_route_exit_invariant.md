# Marked route-exit conductance without arbitrary collars

## 1. Result and status

This note constructs the minimal **formal** state needed to formulate a
collar-independent stationary route-exit estimate.  The state retains:

1. a standard Borel occurrence space for the proof-used oriented
   continuations;
2. the bounded-length raw route word of actual branch, access,
   cyclic-slot, sheet, and exact occurrence-window data, together with
   a separately supplied finite response-type quotient;
3. the maximal source-lift prefix;
4. its Borel first-failure time;
5. the complete set of simultaneous first-failure causes together with
   one deterministic primary code; and
6. a literal Borel exit subarc cut from the original target path after
   the last proof-authorized route gate;
7. the native ambient breaking word through the complete horizon and
   membership in KKL's maximal short subwave; and
8. a single-valued selector allowing at most one charged route record
   over each physical Wave leaf; and
9. for every ambient-singleton survivor, the raw retained predecessor
   flag, its occurrence embeddings, and its first strict-path or
   marked-state switch carrying the same ambient outputs after the
   named route dies.

True ambient KKL breaks are absorbed into \(A^{N\text{-br}}\), and
ambient-unbroken short exits are absorbed into \(A^{\rm sh}\).  Only
the nonshort, ambient-singleton survivor exits create new marked
route-exit conductance coordinates.  Their conductance is independent
of arbitrary Jordan neighborhoods and annular collars.  Under
explicitly stated measurability and width-typing hypotheses, ordinary
overflow monotonicity gives the rigorous inequality

\[
 {\mathcal W}(\text{nonshort ambient-singleton failed routes})
 \leq
 {\mathcal W}(\text{their selected exit subarcs}).
\tag{1.1}
\]

This is a schema theorem, not an analytic estimate.  It does not:

- construct the occurrence presentation for KKL's native stationary
  Wave;
- prove that every candidate `D1` leaf has a measurable source lift;
- bound the route-exit conductance by vertical or renormalization width;
- prove the Quantitative Stationary Defect Bound;
- repair KKL's stationary Wave proof; or
- promote any ledger obligation.

In particular,
`KKL_STATIONARY_UNIFORM_COLLAR_EXIT_CHARGE`,
`KKL_STATIONARY_QUANTITATIVE_DEFECT_BOUND`,
`KKL_PARABOLIC_WAVE_STATIONARY_PROOF_REPAIR`, VAAPC-I, UPTCR, and MLC
remain open.

## 2. Source locks and the exact gap

The locked KKL source is

```text
research/mlc_unified/.tmp_wave_audit/waves-with-Misha.tex
SHA-256 AD4C774806D9902AA54FA31C56AD6146D8034946F19CC5E9CEC3C51A3F94FDD5
```

The relevant clauses are:

- lines 439--461: pseudo-quadratic-like maps and their finite
  fiber-product iterates;
- lines 512--535: Hubbard-tree edges and the covering/immersion action;
- lines 1142--1183: the marked complementary surface, Waves, and width;
- lines 1225--1243: the covering and immersion on tree complements;
- lines 1355--1392: ambient \(N\)-breakability, unbreakability, the
  short family, and
  \(B_A=A^{N\text{-br}}\cup A^{\rm sh}\);
- lines 1423--1494: the response for actual one-step breaks;
- lines 1547--1622: the finite stationary horizon and the disputed
  stationary-alignment step; and
- lines 2083--2162: all proper restrictions, the marking filter, and
  the source definition of ambient breaking;
- lines 2347--2408: route partitions and the statement that a parallel
  route class carries its extremal-width measure.

The locked Kahn extremal-width source is

```text
research/mlc_unified/.tmp_kl06_source/appendix.tex
SHA-256 EA2BE5CC544100D7931C9992E7ED476EBBE4CCE52FAF620BFF357071CB3916F3
```

Lines 12--68 define extremal length and width, overflow, the series
law, and the parallel law.  The overflow definition is geometric:
every path in the first family must literally contain a path in the
second family.  Equal endpoints, equal access labels, or equality in a
finite quotient do not establish overflow.

The qualitative embedded-neighborhood and collar analysis is in:

```text
kkl_stationary_quantitative_defect_repair.md, Sections 10--11
kkl_stationary_uniform_collar_charge_attack.md, Sections 3--8
kkl_stationary_route_exit_survivor_reduction.md, Sections 2--7
```

It proves a block-dependent annular estimate only for a selected
source-lift segment that genuinely crosses the chosen annulus.  It
also proves that the desired vertical-linear collar charge is not
derivable from the qualitative pseudo-polynomial-like hypotheses.
Consequently the next invariant must be defined from the actual route
and its failure, rather than from a freely chosen collar.

The survivor reduction proves a second constraint: selected-route
failure and ambient KKL breaking are different predicates.  It gives
the exact disjoint partition into ambient breaks, unbroken short exits,
and nonshort ambient-singleton survivors.  The invariant below builds
that partition before any width is charged.

## 3. Ambient path space

Let \(Y\) be the proof-used target Riemann surface.  Since a Riemann
surface is second countable and metrizable, choose a complete
compatible metric \(d_Y\).  A KKL proper path has two ideal endpoints;
neither endpoint need be a point of \(Y\).  Therefore use

\[
 {\mathcal P}_{\rm rt}(Y)=C((0,1),Y)
\tag{3.1}
\]

with the compact-open topology, rather than silently adjoining the
remote endpoint.  For example, a compatible complete path metric is

\[
 d_{\rm rt}(\gamma,\eta)
 =
 \sum_{n=3}^{\infty}2^{-n}
 \min\left\{
  1,\sup_{1/n\leq t\leq1-1/n}
  d_Y(\gamma(t),\eta(t))
 \right\}.
\tag{3.2}
\]

The space \({\mathcal P}_{\rm rt}(Y)\) is Polish and hence standard
Borel.  No local connectivity or prime-end landing is used.

Selected finite exit arcs do have both endpoints in the working
surface.  Put

\[
 {\mathcal P}_{\rm ex}(Y)=C([0,1],Y).
\tag{3.3}
\]

An oriented route is an element of \({\mathcal P}_{\rm rt}(Y)\).
Here an orientation-preserving reparametrization means an
orientation-preserving homeomorphism of \((0,1)\).  Such a
reparametrization does not change conformal length or the associated
extremal-width family.  The orientation is nevertheless retained
because "first failure" depends on it.

For

\[
 \Delta_{\rm ex}=\{(u,v):0<u<v<1\},
\]

define the normalized restriction map

\[
 \operatorname{res}(\gamma,u,v)(t)
 =
 \gamma\bigl((1-t)u+tv\bigr).
\tag{3.4}
\]

The map

\[
 \operatorname{res}:{\mathcal P}_{\rm rt}(Y)\times\Delta_{\rm ex}
 \longrightarrow{\mathcal P}_{\rm ex}(Y)
\tag{3.5}
\]

is continuous.  Indeed, if
\((\gamma_n,u_n,v_n)\to(\gamma,u,v)\), uniform continuity of
\(\gamma\) on a compact interval
\([u-\varepsilon,v+\varepsilon]\subset(0,1)\)
and compact-open convergence of \(\gamma_n\) there give

\[
\begin{aligned}
 \sup_t d_Y(&\gamma_n((1-t)u_n+tv_n),
              \gamma((1-t)u+tv))\\
 &\leq
 \sup_{u-\varepsilon\leq s\leq v+\varepsilon}
 d_Y(\gamma_n(s),\gamma(s))
 +
 \sup_t d_Y(\gamma((1-t)u_n+tv_n),
             \gamma((1-t)u+tv))
 \longrightarrow0.
\end{aligned}
\tag{3.6}
\]

This elementary continuity is the measurable-selection mechanism for
the final exit subarc.  It does not supply the failure time or the
source lift; those are separate analytic data.

## 4. Finite marked route skeleton

Fix one stationary proof block.  A **finite marked route skeleton** is

\[
 {\mathsf S}
 =
 \left(
 N,m_{\rm rt},\mathsf O,
 \{\overline{\mathsf G}_r\}_{0\leq r\leq m_{\rm rt}},
 \overline{\mathsf T},\overline{\mathsf S},G,\prec,
 q_{\rm gate},q_{\rm term},q_{\rm switch}
 \right),
\tag{4.1}
\]

where:

- \(N=b+3\) is the ambient KKL unbreakability horizon;
- \(m_{\rm rt}=N-1=b+2\) is the maximum stationary route depth;
- \(\mathsf O\) is the finite set of proof-call or route-class tokens;
- \(\overline{\mathsf G}_r,\overline{\mathsf T}\), and
  \(\overline{\mathsf S}\) are supplied finite alphabets of,
  respectively, gate-response types, terminal-response types, and
  switch-response types;
- \(\bot\in\overline{\mathsf S}\) is the declared no-switch sentinel;
- \(G<\infty\) bounds the number of proof-authorized route gates in one
  occurrence; and
- \(q_{\rm gate},q_{\rm term},q_{\rm switch}\) are Borel quotient maps
  from supplied standard-Borel raw-record spaces to those finite
  alphabets; and
- \(\prec\) is a fixed order on the finite first-failure alphabet
  introduced below.

The quotient maps are part of a *supplied finite block certificate*.
Their response-soundness—equal type implies identical treatment in
every later estimate—is an external proof obligation.  Their alphabet
sizes may depend on the block, primitive period, and raw marking.
Nothing here proves a universal response bound.  If no proved finite
response quotient exists, the compiler below does not apply.

A route gate is the tuple

\[
 g_j=
 \left(
 t_j,r_j,\beta_j^{\rm raw},
 a_j^{-,{\rm raw}},a_j^{+,{\rm raw}},
 c_j^{-,{\rm raw}},c_j^{+,{\rm raw}},
 s_j^{\rm raw},J_j^{\rm raw};
 \overline g_j
 \right),
\tag{4.2}
\]

where:

\[
\begin{gathered}
 0<t_0<t_1<\cdots<t_k<1,\qquad k<G,\\
 0\leq r_0\leq\cdots\leq r_k\leq h\leq m_{\rm rt},\\
 c_j^{-,{\rm raw}}\neq c_j^{+,{\rm raw}},\qquad
 \overline g_j=q_{\rm gate}
  (\beta_j^{\rm raw},a_j^{-,{\rm raw}},a_j^{+,{\rm raw}},
   c_j^{-,{\rm raw}},c_j^{+,{\rm raw}},
   s_j^{\rm raw},J_j^{\rm raw})
 \in\overline{\mathsf G}_{r_j}.
\end{gathered}
\tag{4.3}
\]

For a failed occurrence, the recorded gate word contains only gates
actually passed before the first failure, so \(t_j<\tau\) for every
recorded \(j\).  The next attempted transition is stored separately in
the terminal active/requested labels.  Recording a future gate as if it
had already been crossed is invalid.

The times identify literal places on the target path.  Every
\(J_j^{\rm raw}\) is the actual occurrence embedding/window, not a
finite symbol.  It, the raw branch, accesses, cyclic slots, and sheet
remain in the occurrence payload.  Only the barred value enters the
finite signature.  Distinct raw histories may be merged only after
response-soundness of the quotient has been proved.

No Jordan neighborhood, collar, collar modulus, or arbitrary boundary
curve occurs in (4.1)--(4.3).

## 5. Measurable occurrence presentation

### Definition 5.1 (marked occurrence presentation)

A marked occurrence presentation over \(\mathsf S\) consists of:

1. a standard Borel space \((\Omega,\mathcal B)\);
2. a standard Borel transversal \(\Lambda_A\) for the native Wave,
   carrying its native transverse measure, and an injective Borel map
   \[
      \pi_A:\Omega\longrightarrow\Lambda_A,
   \tag{5.1}
   \]
   so at most one selected route record lies over any physical leaf;
3. a Borel target-path field
   \[
      \gamma:\Omega\longrightarrow{\mathcal P}_{\rm rt}(Y);
   \tag{5.2}
   \]
4. a Borel interior seed
   \(s:\Omega\to(0,1)\), Borel fields for the proof-call token, route
   depth \(1\leq h\leq m_{\rm rt}\), orientation, and variable-length
   gate word, including every real gate time, and Borel fields for the
   ambient singleton word \(\mathbf u_N\) and short predicate
   \(q_{\rm sh}\), with \(t_0=s(\omega)\);
5. a supplied countable index set \(\Xi\), a standard-Borel atlas
   \(\{X_\xi\}_{\xi\in\Xi}\) for the raw source surfaces and sheets,
   the standard-Borel disjoint union
   \(X^{\sqcup}=\bigsqcup_{\xi\in\Xi}X_\xi\), a Borel field
   \(\omega\mapsto X_\omega\), and a partial Borel selected
   inverse-germ field over
   \(\gamma_\omega(s(\omega))\); outside its Borel domain set
   \(\tau=s\) and
   \(C=\{\texttt{INITIAL\_GERM\_MISSING}\}\);
6. the Borel continuation domain
   \[
     {\mathcal D}
     =
     \{(\omega,t):s(\omega)\leq t<\tau(\omega)\}
   \tag{5.3}
   \]
   and a jointly Borel map
   \[
     \widetilde\gamma:{\mathcal D}
     \longrightarrow
     X^{\sqcup}
   \tag{5.4}
   \]
   whose section at \(\omega\) is the maximal lifted path
   \[
     \widetilde\gamma_\omega:
     [s(\omega),\tau(\omega))\longrightarrow X_\omega
   \tag{5.5}
   \]
   on the declared sheet and through the declared occurrence windows,
   satisfying the actual commuting identity
   \[
     I_\omega\circ\widetilde\gamma_\omega(t)
     =
     \gamma_\omega(t)
     \quad(s(\omega)\leq t<\tau(\omega));
   \tag{5.6}
   \]
7. a Borel terminal time (first-failure time on failures and \(1\) on
   success)
   \[
      \tau:\Omega\longrightarrow(0,1];
   \tag{5.7}
   \]
8. a finite-valued Borel first-cause/outcome set, a Borel raw terminal
   payload \(\mathfrak t_{\rm raw}\) containing the actual geometric
   failure locus and active/requested access, sheet, and exact-window
   data, and the equality
   \(q_{\rm term}(\mathfrak t_{\rm raw})\in
   \overline{\mathsf T}\); the degree-one, critical-value-free, and
   every other clean-`D1` predicate are also required to be Borel; and
9. the proof that (5.5) is maximal relative to the declared route
   data;
10. on every ambient-unbroken selected-route failure, either a Borel
    choice of one retained predecessor at every stage or a Borel
    relation-level encoding of the nonempty predecessor fibers, and
    the first strict-path or marked-state switch, with complete
    access/cyclic-order, exact occurrence-window, sheet, obstacle,
    attachment/parent, localization, relative-cover, remote-end,
    whole-target-coverage, both-filter, and future-prefix data, and
    exact common ambient-output equalities; in either mode the tagged
    raw switch record \(\mathfrak s_{\rm raw}\) itself is a Borel map,
    and \(q_{\rm switch}\) is defined on that tagged raw-record space.

The finite response skeleton does not supply the source atlas or raw
sheet charts; these are independent data in clause 5.  Equation (5.6)
is required as an equality of actual maps.  A ribbon-tree label
equality is not a substitute.

By Lusin--Souslin, the injective Borel map \(\pi_A\) has Borel image
and Borel inverse onto that image.  Equivalently, \(\Omega\) is the
graph of one partial Borel first-exit selector on \(\Lambda_A\).  A
second failed presentation of the same
leaf must be resolved by the fixed priority rule; it cannot become a
second charged occurrence.  The selector first minimizes the actual
failure time/stage, then uses a fixed finite order on competing route
roles, and finally the cause priority from Section 6.2.  This
lexicographic rule is part of the certificate and must be Borel.

The occurrence space need not be finite or countable.  It normally
parametrizes a continuum of Wave leaves.  "Finite bookkeeping" below
means a finite type alphabet and a bounded-length record for each
occurrence, not enumeration of \(\Omega\).

### Definition 5.2 (width-faithful presentation)

For use with KKL's lamination width, the occurrence presentation is
**width-faithful** if:

1. the fields \(\gamma_\omega\) and
   \(\epsilon_\omega\), although hosted measurably in the continuous
   path spaces of Section 3, are the source-authorized smooth
   (or explicitly imported rectifiable) KKL/KL paths on which the
   cited extremal-width definition applies;
2. \(\Omega\) is a measurable transversal for the actual oriented
   lamination, modulo a width-zero set;
3. \(\omega\mapsto\gamma_\omega\) does not count the same physical leaf
   with artificial multiplicity, modulo width zero;
4. every Borel fiber used below is an actual measurable
   sublamination; and
5. its inherited transverse width agrees with the extremal width of
   the corresponding proof-used path family.

These are typing hypotheses, not consequences of standard Borel
bookkeeping.  If two occurrence labels represent the same physical
path and the source formalism counts both, ordinary extremal width of
the geometric union forgets that multiplicity.  A bounded-degree
realization theorem would then be required before applying (1.1).

## 6. First-failure time and code

### 6.1 Measurable maximal time

Pointwise analytic continuation does not automatically make
\(\tau\) Borel.  A sufficient certificate is a Borel
valid-through relation

\[
 {\mathcal V}\subset\Omega\times(0,1)
\tag{6.1}
\]

whose section at \(\omega\) is the interval beginning at
\(s(\omega)\) on which the declared germ, sheet, access, and window
data remain valid.  Define

\[
 \tau(\omega)
 =
 \sup\left(
   \{q\in\mathbb Q\cap(0,1):(\omega,q)\in{\mathcal V}\}
   \cup\{s(\omega)\}
 \right).
\tag{6.2}
\]

For every rational \(q\),

\[
 \{\omega:\tau(\omega)>q\}
 =
 \{\omega:s(\omega)>q\}
 \ \cup\
 \bigcup_{\substack{r\in\mathbb Q\cap(0,1)\\r>q}}
 \{\omega:(\omega,r)\in{\mathcal V}\},
\tag{6.3}
\]

provided each section is
\([s(\omega),\tau(\omega))\), or the corresponding interval with an
audited choice of endpoint inclusion, and has supremum
\(\tau(\omega)\).  The right side is a countable union of Borel sets,
so \(\tau\) is Borel.

The initial-interval hypothesis is essential.  For an arbitrary Borel
subset of a product, a first-hit projection need only be analytic; it
need not be Borel.  Thus (6.1) and the section audit are proof
obligations, not decorative notation.

### 6.2 Complete cause/outcome set

Use the finite cause alphabet

```text
INITIAL_GERM_MISSING
CRITICAL_VALUE_HIT
SOURCE_DOMAIN_EXIT
SHEET_COLLISION
WINDOW_EXIT
ACCESS_FAILURE
HORIZON_EXHAUSTED
TARGET_TOUCH_REENTRY
OTHER_SHEET_CONTINUATION
REMOTE_REACHED
```

with the following meanings.

- `INITIAL_GERM_MISSING`: no declared source germ exists at the seed.
- `CRITICAL_VALUE_HIT`: the claimed degree-one inverse branch meets a
  critical-value obstruction.
- `SOURCE_DOMAIN_EXIT`: the maximal source lift reaches the boundary
  or a recorded proper end of its intrinsically declared route domain
  before the remote access.  The exact boundary component or end is
  retained as the first-failure locus token.
- `SHEET_COLLISION`: the declared sheet ceases to be unique or is
  forced to merge/switch.
- `WINDOW_EXIT`: the continuation leaves the exact authorized
  occurrence window.
- `ACCESS_FAILURE`: the marked access or its cyclic slot does not
  survive.
- `HORIZON_EXHAUSTED`: the proof asks for a stage beyond the complete
  declared horizon.
- `TARGET_TOUCH_REENTRY`: target-only data show a touch and reentry but
  do not certify a source-domain exit.
- `OTHER_SHEET_CONTINUATION`: the target continues through a different
  global immersion sheet, with no certified continuation of the
  selected source germ.
- `REMOTE_REACHED`: the route reaches its declared remote access; this
  is success, not an exit charge.

Define on all of \(\Omega\)

\[
 C(\omega)\subset{\mathsf C}_{\rm out}
\tag{6.4}
\]

as follows: when \(\tau(\omega)<1\), it is the nonempty set of
**all** causes active at the first failure time; when
\(\tau(\omega)=1\), it is
\(\{\texttt{REMOTE\_REACHED}\}\).  Fix a priority order \(\prec\)
once and put

\[
 c(\omega)=\min_\prec C(\omega).
\tag{6.5}
\]

The primary code makes the fibers disjoint, while the complete set
\(C(\omega)\) prevents a simultaneous critical/sheet/window collision
from being erased by the tie breaker.  A clean source-exit class is
defined conservatively by

\[
\begin{split}
 D_{1,h}^{\rm clean}
 =
 \{\omega:\;&h(\omega)=h,\ 
 C(\omega)=\{\texttt{SOURCE\_DOMAIN\_EXIT}\},\\
 &\text{the corridor is degree one and critical-value free,}\\
 &\text{and (5.5)--(5.6) hold for }
   s(\omega)\leq t<\tau(\omega)\}.
\end{split}
\tag{6.6}
\]

In particular, a target touch/reentry or continuation on another sheet
is not relabeled as `D1` merely because its target trace resembles a
collar exit.

The critical-free flag and the cause set must agree.  In particular,
an occurrence carrying `CRITICAL_VALUE_HIT` cannot simultaneously be
certified critical-value free.

The map \(C\) must be Borel as a map to the finite power set, and the
raw terminal payload and every terminal predicate used in (6.6) must
have the Borel typing required in Definition 5.1.  Pointwise
classification alone does not prove this.

The value
\(C(\omega)=\{\texttt{REMOTE\_REACHED}\}\) is reserved for a
successful presentation with \(\tau(\omega)=1\); it is not a failure.
Thus \(\Omega\) may contain failures and successes, while every charged
family below is a Borel subset of
\[
 D_{\rm fail}
 =
 \{\omega\in\Omega:
   C(\omega)\neq\{\texttt{REMOTE\_REACHED}\}\}.
\tag{6.6a}
\]

### 6.3 Ambient survivor typing

The selected-route failure time \(\tau\) is not KKL's ambient breaking
time.  For the physical leaf \(\alpha=\pi_A(\omega)\), define

\[
 \beta_N(\alpha)
 =
 \min\{0\leq j<N:
   F_*^j\alpha\text{ is a single path and breaks under }F_*\},
\tag{6.7}
\]

and put \(\beta_N(\alpha)=\infty\) when the ambient filtered image
remains one path at every required stage through \(N\).  The definition
stops at the first break; it does not assign later single-path symbols
after the ambient path has already split.

The occurrence certificate retains the finite ambient-singleton word

\[
 \mathbf u_N(\omega)
 =
 (u_0,\ldots,u_{N-1}),
\tag{6.8}
\]

up to and including the first false entry.  Thus either all \(N\)
entries are true, or the word is

\[
 (\underbrace{\mathrm{true},\ldots,\mathrm{true}}_{j\ {\rm entries}},
  \mathrm{false})
\tag{6.9}
\]

and records \(\beta_N=j\).  Entries after the first false value are
forbidden.  The certificate also retains the Borel predicate

\[
 q_{\rm sh}(\omega)
 =
 \mathbf 1_{\{\pi_A(\omega)\in A^{\rm sh}\}}.
\tag{6.10}
\]

On the selected presentation space \(\Omega\), define the ambient
response classes

\[
\begin{aligned}
 E_A^{\rm br}
  &=\{\omega:\beta_N(\pi_A(\omega))<\infty\},\\
 E_A^{\rm sh}
  &=\{\omega:\beta_N(\pi_A(\omega))=\infty,\
                 q_{\rm sh}(\omega)=1\},\\
 E_A^{\rm surv}
  &=\{\omega:\beta_N(\pi_A(\omega))=\infty,\
                 q_{\rm sh}(\omega)=0\}.
\end{aligned}
\tag{6.11}
\]

These three Borel families are pairwise disjoint and exhaust
\(\Omega\).  The first lies in KKL's \(A^{N\text{-br}}\); the second
lies in \(A^{\rm sh}\); and only the third lies outside

\[
 B_A=A^{N\text{-br}}\cup A^{\rm sh}.
\tag{6.12}
\]

The proof is the two successive binary partitions
\(A=A^{N\text{-br}}\sqcup A^{N\text{-nbr}}\) and
\(A^{N\text{-nbr}}
=(A^{N\text{-nbr}}\cap A^{\rm sh})
\sqcup(A^{N\text{-nbr}}\setminus A^{\rm sh})\).
The partition must be made on the single-valued occurrence space before
widths are summed.

For \(\omega\in E_A^{\rm surv}\), write the ambient singleton chain as

\[
 \delta_0=\pi_A(\omega),
 \qquad
 \delta_{j+1}=F_{j*}\delta_j
 \quad(0\leq j<N).
\tag{6.13}
\]

Here every \(F_{j*}\) is the actual native stage action, with the
actual pulled marking, used in KKL's definition of
\(N\)-unbreakability.  No independently changed marking is
substituted.

For every stage define the actual retained predecessor fiber

\[
\begin{split}
 \operatorname{Ret}_j(\delta_j,\delta_{j+1})
 =
 \{\,\gamma:\;&
 \gamma\in\iota_j^*\delta_j,\quad
 \gamma\text{ is a full path in the fine pulled marking},\\
 &\gamma\text{ is not discarded as subordinate to one coarse pulled
 ideal-marking interval},\quad
 f_{j*}\gamma=\delta_{j+1}\,\}.
\end{split}
\tag{6.14}
\]

Because every \(F_{j*}\delta_j\) is the nonempty singleton
\(\{\delta_{j+1}\}\), the source definition
\(F_{j*}=f_{j*}\iota_j^*\), including its proper-path and marking
filters, gives

\[
 \operatorname{Ret}_j(\delta_j,\delta_{j+1})\neq\varnothing
 \qquad(0\leq j<N).
\tag{6.15}
\]

Finite pointwise choice therefore gives a stagewise retained
predecessor flag

\[
 \widehat{\mathfrak S}_\omega
 =
 (\delta_0;\widehat\gamma_0,\delta_1,\ldots,
   \widehat\gamma_{N-1},\delta_N),
 \qquad
 \widehat\gamma_j\in
 \operatorname{Ret}_j(\delta_j,\delta_{j+1}).
\tag{6.16}
\]

Let \(r=r(\omega)\) be the first stage at which the selected named
route fails.  Choose (6.16) to agree with the selected valid chain
before \(r\).  Exactly one of the following first-switch types occurs.

1. **Strict path replacement.**  The named stage-\(r\) object is not
   in \(\operatorname{Ret}_r(\delta_r,\delta_{r+1})\)—including the
   cases in which it is partial, nonproper, removed by a marking
   filter, or has the wrong \(f_{r*}\)-image—and
   \(\widehat\gamma_r\) is a different full retained restriction.
2. **Marked-state mismatch.**  The named full retained restriction
   exists geometrically, but its actual successor state differs in
   access/cyclic order, exact occurrence window, sheet,
   obstacle/attachment/parent data, localization, relative-cover
   compatibility, remote landing/end, whole-target-portion coverage,
   either marking filter, or future-prefix compatibility.  The same
   underlying path may serve as
   \(\widehat\gamma_r\); the two complete marked states must differ.

For one fixed \(\omega\), the resulting selected marked-switch witness
is

\[
 \mathfrak s_{\rm sel}(\omega)
 =
 \left(
  \widehat{\mathfrak S}_\omega,\,
  r,\,
  \mathsf{switch\_kind},\,
  \mathsf{dying\_state},\,
  \mathsf{replacement\_state}
 \right),
\tag{6.17}
\]

with all equalities in (6.14)--(6.16).  Equality of coarse endpoint
labels is insufficient.  Pointwise finite choice proves only existence
of (6.16), and hence of \(\mathfrak s_{\rm sel}(\omega)\), for one
leaf.  It does not make
\(\omega\mapsto\mathfrak s_{\rm sel}(\omega)\) Borel.

The flag is not yet a segmented occurrence merely because its stages
exist.  For each \(j\), one must prove the actual containment in
(6.14) for specified simple oriented Wave representatives.  Lemma 4.2
of `kkl_stationary_segmented_occurrence_binder.md` then extracts the
unique raw occurrence embedding
\[
 a_j:(0,1)\longrightarrow(0,1),\qquad
 \delta_j\circ a_j=\iota_j\circ\widehat\gamma_j .
\tag{6.17a}
\]
The full paths together with all \(a_j\) form the linked prefix flag
of that lemma.  They do **not** produce one deepest full proper
fiber-product path: earlier coordinates may be strict nonproper
segments.  Nor does Lemma 4.2 prove survival of either ideal endpoint.

Pointwise finite choice proves neither a Borel selector, a uniform
bound on predecessor-fiber cardinality or marked states, preservation
of transverse width, nor a response theorem.

Consequently the new clean source-exit residual is

\[
 D_{1,h}^{\rm new}
 =
 D_{1,h}^{\rm clean}\cap E_A^{\rm surv}.
\tag{6.18}
\]

Neither `SOURCE_DOMAIN_EXIT` nor any other selected-route failure code
implies \(\beta_N<\infty\).  KKL's breaking response can absorb
\(E_A^{\rm br}\), but it cannot be applied to
\(E_A^{\rm surv}\), whose defining ambient leaves remain single.
Likewise \(E_A^{\rm sh}\) is already present in the native short term
and must not become a second route-exit charge.

## 7. Intrinsic exit subarc

On the Borel gated-failure domain
\[
 D_{\rm gate}
 =
 \{\omega\in D_{\rm fail}:
   s(\omega)<\tau(\omega)<1\},
\tag{7.0}
\]
the gate word begins with the actual interior seed
\(t_0=s(\omega)\in(0,1)\).
Let

\[
 j_*(\omega)
 =
 \max\{j:t_j(\omega)<\tau(\omega)\},
\qquad
 \ell(\omega)=t_{j_*(\omega)}(\omega).
\tag{7.1}
\]

Because the gate word has length at most \(G\), the sets on which
\(j_*=j\) are finite Boolean combinations of Borel inequalities.
Hence \(j_*\) and \(\ell\) are Borel.  The strict inequality in (7.1)
prevents a failure occurring at a gate from producing a degenerate
zero-time segment.

Define the target exit path

\[
 \epsilon_\omega
 =
 \operatorname{res}
 \bigl(\gamma_\omega,\ell(\omega),\tau(\omega)\bigr).
\tag{7.2}
\]

Equations (3.5), (5.2), (5.7), and (7.1) imply that

\[
 \epsilon:D_{\rm gate}\longrightarrow{\mathcal P}_{\rm ex}(Y)
\tag{7.3}
\]

is Borel.  The constant-path subset of
\({\mathcal P}_{\rm ex}(Y)\) is closed, so
\[
 D_{\rm chg}
 =
 \{\omega\in D_{\rm gate}:
   \epsilon_\omega\text{ is nonconstant}\}
\tag{7.4}
\]
is Borel.  Every charged family below is required to be a Borel subset
of \(D_{\rm chg}\).

By construction, \(\epsilon_\omega\) is a **literal contiguous
subpath** of \(\gamma_\omega\).  This is the entire point of retaining
the path and the two times.  The following weaker data are
insufficient:

- the same two endpoint components;
- the same two prime-end labels;
- the same ribbon-tree edge word;
- homotopy relative to the carrier;
- the statement that the target trace touched an image boundary; or
- a separately chosen path in the same route class.

The last gate is supplied by the proof-authorized access/sheet/window
route skeleton.  It is not the boundary of a chosen Jordan collar.

## 8. Complete finite signature

Define the bookkeeping map
\(\kappa:D_{\rm fail}\to\overline{\mathsf K}\), where
\(\overline{\mathsf K}\) is the finite product/word space determined
by the supplied alphabets, by

\[
\begin{split}
 \kappa(\omega)=
 (&o(\omega),h(\omega),\operatorname{or}(\omega),\\
  &\mathbf u_N(\omega),q_{\rm sh}(\omega),\\
  &[(r_j,\overline g_j)]_{0\leq j\leq k(\omega)},\\
  &q_{\rm switch}(\mathfrak s_{\rm raw}(\omega)),\\
  &C(\omega),c(\omega),
    q_{\rm term}(\mathfrak t_{\rm raw}(\omega))).
\end{split}
\tag{8.1}
\]

The raw payload \(\mathfrak s_{\rm raw}\) is a tagged Borel record in
one of the two modes allowed by Definition 5.1(10).

- In `SELECTED_FLAG` mode it contains a **Borel-selected** full
  predecessor flag (6.16), all actual paths, containments, occurrence
  embeddings, ambient-output equalities, and both complete marked
  states.
- In `RELATION` mode it contains instead the Borel graphs of all
  retained predecessor fibers, their containment/output relations,
  and the Borel first-switch relation and complete state data.  No
  pointwise chosen flag is inserted.

The supplied map \(q_{\rm switch}\) is defined on this tagged union of
raw record spaces.  Thus the pointwise witness
\(\mathfrak s_{\rm sel}(\omega)\) from (6.17) is used inside
\(\mathfrak s_{\rm raw}\) only in `SELECTED_FLAG` mode.
\(\mathfrak t_{\rm raw}\) contains the actual failure locus and
active/requested access, sheet, and window data.  Those raw objects,
the real times, and the geometric target path are **not** coordinates
of \(\kappa\).  Only their supplied barred response types enter the
finite key.  For an ambient break the raw switch witness and its type
are represented by a no-switch sentinel, with
\(q_{\rm switch}(\bot)=\bot\in\overline{\mathsf S}\).  The same
sentinel is used whenever the switch predicate is inapplicable.

### Theorem 8.1 (finite Borel bookkeeping)

For a supplied finite skeleton \(\mathsf S\), Borel finite quotient
maps from Section 4, a marked occurrence presentation satisfying
Sections 5--7, and a Borel chargeable family
\(D\subset D_{\rm chg}\), let
\[
 \mathsf Q_D=\kappa(D),\qquad
 D_q=D\cap\kappa^{-1}(\{q\})
 \quad(q\in\mathsf Q_D).
\tag{8.1a}
\]
Then:

1. \(\kappa\) is Borel;
2. \(\mathsf Q_D\) is finite;
3. every \(D_q=D\cap\kappa^{-1}(\{q\})\) is Borel; and
4. the exit-path field restricted to every \(D_q\) is Borel.

If
\(\overline{\mathsf G}
=\bigsqcup_r(\{r\}\times\overline{\mathsf G}_r)\) and
\(k(\omega)<G\), then one coarse bound is

\[
 |\mathsf Q_D|
 \leq
 4|\mathsf O|m_{\rm rt}(N+1)\,
 |{\mathsf C}_{\rm out}|\,
 \bigl(2^{|{\mathsf C}_{\rm out}|}-1\bigr)
 |\overline{\mathsf T}|\,|\overline{\mathsf S}|
 \sum_{j=1}^{G}|\overline{\mathsf G}|^j.
\tag{8.2}
\]

#### Proof

By hypothesis, every barred coordinate in (8.1) is a finite-valued
Borel map.  The raw witness need not have finite image.  The
variable-length gate word belongs to the finite disjoint union

\[
 \bigsqcup_{j=1}^{G}\overline{\mathsf G}^{\,j},
\tag{8.3}
\]

so it too is finite-valued and Borel.  Products of finitely many
Borel maps are Borel, proving (1).

The factors displayed in (8.2) respectively bound orientation and
short membership, proof-call token, route depth, the \(N+1\)
possible ambient break-time words, primary cause, nonempty complete
cause set, terminal and switch response types, and gate word.  Thus
the image is finite,
proving (2).  A singleton in a finite discrete space is Borel; taking
its inverse image and intersecting with Borel \(D\) proves (3).
Finally (7.3) is Borel on \(D\), hence
on each Borel subset \(D_q\), proving (4). \(\square\)

The bound (8.2) is deliberately block-dependent.  The theorem also
does not prove that the finite quotients are response-sound.  It proves
neither a universal state dimension nor a bound independent of the
primitive period.

## 9. Marked route-exit conductance and overflow

For a Borel chargeable family \(D\subset D_{\rm chg}\), define

\[
 \Gamma_D
 =
 \{\gamma_\omega:\omega\in D\},
\qquad
 \Sigma_D
 =
 \{\epsilon_\omega:\omega\in D\}.
\tag{9.1}
\]

The geometric **route-exit conductance** of a supplied family is

\[
 \mathfrak E(D)
 =
 {\mathcal W}(\Sigma_D)\in[0,\infty].
\tag{9.2}
\]

For \(q\in\mathsf Q_D\), also put

\[
 \mathfrak e_q(D)
 =
 {\mathcal W}(\Sigma_{D_q}).
\tag{9.3}
\]

Equation (9.2) can be evaluated formally on any supplied route-exit
family, but the new response state retains only

\[
 \mathfrak E^{\rm surv}(D)
 :=
 \mathfrak E(D\cap E_A^{\rm surv})
\tag{9.4}
\]

and its signature fibers.  The parts in \(E_A^{\rm br}\) and
\(E_A^{\rm sh}\) are relabelled into the already present native terms
before any width sum is formed.  The total (9.4), not the sum of an
arbitrarily refined code vector, is the minimal new geometric
invariant.

### Theorem 9.1 (literal route-exit overflow)

Assume every \(\epsilon_\omega\), \(\omega\in D\), is a nonconstant
literal subpath of \(\gamma_\omega\).  Then

\[
 {\mathcal W}(\Gamma_D)
 \leq
 \mathfrak E(D)
 \leq
 \sum_{q\in\mathsf Q_D}\mathfrak e_q(D).
\tag{9.5}
\]

#### Proof

For every \(\gamma_\omega\in\Gamma_D\), equation (7.2) supplies
\(\epsilon_\omega\in\Sigma_D\) as a literal subpath.  Thus
\(\Gamma_D\) overflows \(\Sigma_D\) in the Kahn--Lyubich definition.
If a conformal metric is admissible for \(\Sigma_D\), every selected
subpath has length at least one, so every containing full path has
length at least one.  The same metric is therefore admissible for
\(\Gamma_D\).  Taking the infimum of its area gives

\[
 {\mathcal W}(\Gamma_D)
 \leq{\mathcal W}(\Sigma_D)
 =\mathfrak E(D).
\tag{9.6}
\]

Since

\[
 \Sigma_D=\bigcup_{q\in\mathsf Q_D}\Sigma_{D_q},
\tag{9.7}
\]

the finite parallel-law inequality gives

\[
 {\mathcal W}(\Sigma_D)
 \leq
 \sum_{q\in\mathsf Q_D}{\mathcal W}(\Sigma_{D_q}).
\tag{9.8}
\]

Combining (9.6)--(9.8) proves (9.5). \(\square\)

### Corollary 9.2 (new clean survivor exits)

If the presentation is width-faithful and
\(D_{1,h}^{\rm new}\) from (6.18) is a Borel sublamination, then

\[
 {\mathcal W}
 \bigl(\Gamma_{D_{1,h}^{\rm new}}\bigr)
 \leq
 \mathfrak E_h^{\rm new}(F),
\qquad
 \mathfrak E_h^{\rm new}(F)
 :=
 {\mathcal W}
 \bigl(\Sigma_{D_{1,h}^{\rm new}}\bigr).
\tag{9.9}
\]

This is a formal overflow inequality, not the required analytic
calibration.

## 10. Independence and covariance

### Proposition 10.1 (collar independence)

The families in (9.1) and the number in (9.2) use only:

- the actual target path;
- its selected source-germ continuation;
- the intrinsic first failure of the declared branch/sheet/window
  route;
- the last proof-authorized marked route gate; and
- literal path restriction.

They contain no choice of \(O_h^-\), \(O_h^+\), \(Q_h\), or a collar
modulus.  Hence changing an auxiliary embedded collar while keeping
the marked occurrence data fixed leaves \(\mathfrak E(D)\) unchanged.

#### Proof

Inspect equations (5.1)--(9.2).  None contains collar data.  The exit
path is uniquely computed by (7.1)--(7.2) from the occurrence record.
Therefore a collar change changes no member of \(\Sigma_D\), and
extremal width is unchanged. \(\square\)

### Proposition 10.2 (presentation covariance)

The total conductance \(\mathfrak E(D)\) is unchanged under:

1. a Borel isomorphism of occurrence spaces transporting all fields;
2. a bijective renaming of raw access, sheet, window, and branch data,
   with the finite response-quotient values transported unchanged, and
   a bijective renaming of proof-call tokens; and
3. an orientation-preserving reparametrization of every target path,
   provided gate and failure times are transported by the same
   reparametrization.

Refining the failure code without changing the selected geometric exit
paths leaves \(\mathfrak E(D)\) unchanged, although it can change the
vector (9.3) and its parallel-law upper bound.

#### Proof

The first two operations leave the geometric set \(\Sigma_D\)
unchanged.  The third changes only path parametrization.  Conformal
length, admissibility, and extremal width are invariant under such a
reparametrization.  A code refinement changes the partition
\(\{D_q\}\) but not its union or the exit-path map, so (9.2) is
unchanged. \(\square\)

The invariant is relative to the proof-authorized route skeleton and
the initial source germ.  Changing those semantic data can change the
exit family.  No absolute canonicity is claimed before the KKL
source-to-route certificate is proved.

## 11. Why every field is retained

The state is minimal in the following operational sense: each retained
field blocks a distinct invalid inference.

| Dropped field | First ambiguity introduced |
|---|---|
| injective physical-leaf selector / width typing | pointwise choices need not form a measurable sublamination, and two presentations of one leaf can be charged twice |
| ambient-singleton word | selected-route failure is falsely identified with an actual KKL break |
| native short-membership flag | a leaf already represented in \(A^{\rm sh}\) becomes a duplicate new charge |
| full retained predecessor chain and first-switch state | an ambient-singleton survivor is recorded as a bare dead end, losing the strict-path or marked-state switch that keeps \(F_*\alpha\) single |
| orientation | "first" failure is undefined |
| maximal time \(\tau\) | a later convenient exit can hide an earlier obstruction |
| complete cause set | a primary tie breaker can erase a simultaneous critical or sheet collision |
| access word and cyclic slots | the terminal endpoint label does not determine prime-end transport |
| complete sheet word | two continuation histories can end on one coarse terminal sheet |
| complete exact-window word | strict nested occurrence restrictions can have the same final containing interval |
| exact failure-locus token | one sheet/window/access label can abut several source ends or seams with different exit geometry |
| last gate time | no intrinsic exit segment is selected |
| literal target path and exit subarc | matching endpoints or ribbon labels do not imply overflow |
| degree-one / critical-free flag | a branched failure is falsely charged as a univalent `D1` exit |

This table is a necessity audit, not a category-theoretic proof that no
equivalent encoding can use fewer symbols.  Equivalent lossless
encodings are allowed.

## 12. Finite diagnostics

The companion validator is

```text
audit_stationary_route_exit_schema.py
```

It checks a finite ribbon/path-word shadow of the schema.  In
particular it attacks:

1. a recorded failure that skips an earlier event;
2. deletion of one simultaneous cause;
3. a wrong primary tie-break code;
4. an invented path with the correct endpoints but not a literal
   subpath;
5. target touch/reentry mislabeled as clean `D1`;
6. continuation on another sheet mislabeled as clean `D1`;
7. histories with identical terminal sheet labels;
8. histories with identical terminal window labels;
9. distinct failure loci hidden behind identical terminal labels;
10. sensitivity of the geometric exit family to mere label renaming;
11. sensitivity of the union exit family to code refinement;
12. critical or degree-two failures mislabeled as clean `D1`;
13. a critical cause paired with a contradictory critical-free flag;
14. an unreached future gate inserted into the completed history;
15. selected-route failure conflated with ambient KKL breaking;
16. failure to absorb a true ambient break;
17. failure to absorb an ambient-unbroken short exit;
18. duplicate presentations of one physical leaf charged twice;
19. an incomplete ambient-singleton word falsely called unbroken;
20. status entries retained after the first ambient break;
21. an active survivor with no retained replacement route;
22. a claimed strict replacement identical to the dying path;
23. a replacement that does not map to the common ambient output;
24. a survivor chain with an empty retained predecessor stage;
25. a claimed marked-state switch with identical marked states;
26. Borel selection inferred from pointwise finite choice;
27. a uniform predecessor-fiber bound inferred from pointwise finite
    choice;
28. loss of histories assigned distinct proved response types;
29. use of a route stage at the ambient-only stage \(N\);
30. dependence of the finite signature on a mere raw-label renaming;
31. accidental insertion of the raw predecessor/switch witness into
    the finite signature;
32. failure of a supplied response type to separate histories which
    the quotient declares distinct;
33. a retained stage with no actual occurrence-window extraction;
34. inference of one deepest full proper path from a linked prefix
    flag; and
35. inference of ideal-end survival from interior occurrence windows.

It also includes a positive clean-survivor control and a positive
marked-state switch in which the same underlying path survives with a
different actual successor state.

The script cannot test Borel measurability, analytic continuation,
prime-end realization, extremal width, or uniform constants.

## 13. Adversarial audit

### 13.1 Target touch is not source exit

A target trace can touch and reenter the image of a local branch while
the selected source lift does not cross any intrinsic source boundary.
It can also continue through another global immersion sheet.  The
codes `TARGET_TOUCH_REENTRY` and `OTHER_SHEET_CONTINUATION` preserve
these cases.  They are not included in (6.6).

### 13.2 Pointwise first failure is not measurable first failure

The supremum of pointwise continuation domains need not be a Borel
function without the initial-section certificate (6.1).  The schema
requires that certificate and proves Borelness by the rational formula
(6.3).

### 13.3 One primary code cannot erase simultaneous geometry

The primary code is used only to obtain a disjoint finite partition.
The full cause set remains a signature coordinate.  A mixed
`SOURCE_DOMAIN_EXIT`/`CRITICAL_VALUE_HIT` occurrence is not a clean
degree-one exit.

### 13.4 Route exit is not ambient breaking

The selected route follows one branch, sheet, access, and window word.
KKL ambient breaking applies all proper restrictions and the marking
filter, and asks whether the resulting full \(F_*\)-image is one path.
A selected route can fail while another retained route-state keeps that
image single.  Therefore a route-failure code never determines the
ambient-singleton word.

### 13.5 Single-valuedness precedes charging

Two failed presentations over one physical leaf are resolved by the
fixed priority selector before forming \(\Omega\).  They cannot be
inserted into two signature fibers and then "corrected" after widths
are summed.  The injectivity of \(\pi_A\) is an exact schema clause.

### 13.6 A survivor is a switch, not a bare exit

If the named route fails while the full ambient image is one path,
the definition of \(F_*\) supplies a nonempty retained predecessor
fiber at every stage.  The first switch is either a different retained
path or the same underlying path with a different actual marked
successor state.  The state therefore retains both marked states and
the full chain (6.14)--(6.16).
Endpoint equality or a boolean "replacement exists" flag is not
enough.  Measurable priority selection among multiple replacements
remains an analytic obligation.

### 13.7 Finite type is not finite lamination

\(\Omega\) can be uncountable.  Theorem 8.1 proves only that supplied
Borel finite response quotients produce finitely many signature
fibers.  It neither proves response-soundness nor sums pointwise
leaves or replaces a lamination by a finite graph.

### 13.8 A code partition is not an extremal-width measure

General extremal width is subadditive under unions, not automatically
additive over arbitrary Borel labels.  The second inequality in (9.5)
uses only the parallel-law upper bound.  Any exact transverse
additivity used by QSDB requires Definition 5.2.

### 13.9 Code refinement can worsen the scalar upper bound

Although
\(\mathfrak E(D)={\mathcal W}(\Sigma_D)\) is unchanged by refinement,
\(\sum_q\mathfrak e_q(D)\) can increase.  Thus the intrinsic total and
the labeled vector must not be conflated.

### 13.10 No hidden collar has been renamed a gate

A gate is an access/sheet/window transition already demanded by the
proof route.  It is not a newly chosen Jordan curve.  If the actual
proof supplies no such finite gate before failure, the occurrence is
not chargeable by this version of the invariant; one must use the full
maximal prefix or enlarge the route skeleton explicitly.

### 13.11 No analytic bound follows from the schema

The family \(\Sigma_D\) can have infinite extremal width.  Theorem 9.1
still holds in the extended interval \([0,\infty]\), but then it gives
no useful estimate.

## 14. Exact next analytic theorem

The collar-independent stationary target can now be stated without a
neighborhood choice.  Use the source-typed notation

\[
 V(F)={\mathcal W}(\mathcal U\setminus\mathcal T),
 \qquad
 R(F)={\mathcal W}(\mathcal R F).
\tag{14.1}
\]

> **Open marked route-exit calibration.**  For every parabolic bound
> \(b\), construct a width-faithful marked occurrence presentation for
> every native stationary KKL block, selecting each physical leaf at
> most once, absorbing the ambient-break and unbroken-short classes,
> covering every remaining proof-used clean nonshort
> ambient-singleton `D1` survivor at every route depth
> \(1\leq h\leq m_{\rm rt}=b+2\), with ambient singleton data through
> \(N=b+3\), and
> prove
> \[
>    \sum_{h=1}^{b+2}
>    \mathfrak E_h^{\rm new}(F)
>    \leq
>    C_b\bigl(V(F)+R(F)+1\bigr),
> \tag{14.2}
> \]
> with \(C_b\) independent of primitive period, degeneration,
> satellite data, and route length.

The stronger right side
\(C_b(V(F)+1)\) would recover the original vertical-only
route-localized collar replacement.  The survivor reduction itself
justifies neither bound; it only identifies the family to be bounded.
Its pointwise retained-chain construction also does not provide the
Borel selector or a uniform bound on predecessor-fiber or marked-state
cardinality.  A finite response vector uniform over blocks requires a
separate, width-compatible finite response-type quotient; Theorem 8.1
proves only blockwise finite bookkeeping after such finite alphabets
are supplied.

To use (14.2) in strengthened QSDB one must still prove:

1. the native transverse-measure typing in Definition 5.2;
2. that every proof-used selected route exit is assigned exactly once
   to \(E_A^{\rm br}\), \(E_A^{\rm sh}\), or
   \(E_A^{\rm surv}\);
3. that every survivor `D1` occurrence is either in the new clean class
   (6.18) or receives a separately justified mixed-failure charge;
4. a Borel, transverse-width-compatible selection of the full retained
   predecessor flag (6.16) and its occurrence embeddings (6.17a), or
   a relation-level replacement avoiding arbitrary choice;
5. a uniform finite response-type quotient if classwise finite
   extraction is used;
6. the absolute HTND or \(R(F)+1\) scale needed to absorb the defect;
7. the disjoint
   \(B=A^{N\text{-br}}\cup A^{\rm sh}\) estimate; and
8. the KKL small-breaking transfer to the ambient Wave.

The present construction isolates the geometric family whose width
must be estimated and makes the overflow step checkable.  It does not
prove (14.2).

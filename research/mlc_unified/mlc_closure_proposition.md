# Universal Protected-Tower Compactness and Rigidity Proposition

## 1. Status and purpose

**Status: OPEN.**

This note packages the remaining construction, transition, compactness, and
rigidity work into one falsifiable proposition. It does not prove that
proposition and does not prove MLC. It does prove the logical implication

\[
  \mathrm{UPTCR}\Longrightarrow\mathrm{MLC}.
\]

The package is deliberately stronger than a scalar a-priori-bound statement.
It includes the marked carrier construction, its analytic realization, the
finite response state, the backward transition, coercivity in the marked
topology, and parameter rigidity. Omitting any one of these six clauses
invalidates the implication.

The machine-ledger status is therefore:

- `UNIVERSAL_PROTECTED_TOWER_CLOSURE`: **open**;
- `UPTCR_IMPLIES_MLC`: **proved conditional implication**;
- `MLC`: **open**.

## 2. Source boundary

The source lock date is 2026-07-23.

### 2.1 Dudko's virtual-hull paragraph

Dudko's Interpolation Problem 4.4 asks for a Virtual-Molecule version of the
Near-Degenerate Regime. The following paragraph proposes partially invariant
virtual Julia sets: connected hulls of the corresponding Cantor small Julia
sets containing only a prescribed finite part of the critical orbit. The
paragraph is a strategy. It does not construct:

- a canonical connector or rooted predecessor closure;
- protected prime-end accesses and their survival maps;
- a component-exhaustion theorem;
- relative-cover lifts or properness;
- a universal response state;
- a backward transition inequality; or
- compactness and rigidity for arbitrary mixed towers.

Accordingly none of UPTCR-1--UPTCR-6 is imported from that paragraph.

### 2.2 KKL rigidity

KKL Theorem B states that a family of **prime primitive** types with beau
bounds and bounded puzzle Teichmüller diameter is rigid. KKL also explicitly
separates the transfer to broader mixed quadratic-like or
\(\psi\)-quadratic-like categories from the scope of that article.

UPTCR-6 therefore uses KKL Theorem B only when a tower lies in its native
prime-primitive category and its hypotheses have been verified. For a mixed
primitive, satellite, neutral, puzzle, or virtual tower, UPTCR-6 is a new
uniform theorem to be proved. Beau bounds alone are not treated as rigidity.

### 2.3 Existing internal inputs

The following internal facts may be used:

1. the backward-record lemma in
   [master_transition.md](master_transition.md#7-record-lemma);
2. finite root-pullback and endpoint-accounting theorems in the present
   research package; and
3. the exact protected-access obstruction in
   [canonical_virtual_interface_carrier.md](canonical_virtual_interface_carrier.md#6-exact-analytic-access-collision-obstruction).

These results constrain a proof of UPTCR. They do not prove any complete
UPTCR clause.

## 3. Typed tower data

Let \(f_c(z)=z^2+c\) be infinitely quadratic-like renormalizable. A UPTCR
tower supplies a canonical increasing sequence of entropy-clock checkpoints
\(n\in\mathcal N(c)\subset\mathbb N\) and, for every noninitial checkpoint, a
predecessor \(p(n)\in\mathcal N(c)\) with \(p(n)<n\).

At checkpoint \(n\), the marked carrier is

\[
  \mathfrak T_n=
  (\Sigma_n,H_n,B_n,P_n,\mathcal I_n,\Gamma_n,
    \mathscr Q_n,\mathfrak A_{{\rm prot},n}).
\tag{3.1}
\]

Here:

- \(\Sigma_n\) is the selected marked Riemann surface or relative cover;
- \(H_n\) is the actual full connected carrier in its authorized
  localization;
- \(B_n\) is the base or neutral boundary marking;
- \(P_n\) is the finite postcritical package used through the declared
  horizon;
- \(\mathcal I_n\) is the complete proof-used ideal/prime-end marking;
- \(\Gamma_n\) is the declared extremal curve family;
- \(\mathscr Q_n\) is the typed proof-use inventory of cells, components,
  orbit segments, branches, return words, sheets, and obstacles; and
- \(\mathfrak A_{{\rm prot},n}\) is the protected attachment invariant.

The protected attachment invariant is

\[
  \mathfrak A_{{\rm prot},n}
  =
  \left(
    C_{\infty,n},
    \chi_n,
    \{\tau_n(X)\}_{X},
    \{\varsigma_{n,X}\}_{X}
  \right).
\tag{3.2}
\]

In (3.2), \(C_{\infty,n}\) is the least finite attachment-orbit closure in
the implication-complete cell model, \(\tau_n(X)\) is the complete
attachment trace and itinerary of \(X\), and \(\varsigma_{n,X}\) is the
partial survival map on protected accesses. The collision invariant is

\[
  \chi_n=
  (\chi_{{\rm sheet},n},\chi_{{\rm crit},n},
   \chi_{{\rm obs},n},\chi_{{\rm access},n},
   \chi_{{\rm loc},n}).
\tag{3.3}
\]

The coordinates in (3.3) are fatal for the current protected analytic core:
a nonzero value is not made admissible merely by occurring in a bounded
window. A raw defect may be assigned to a window only after a declared
retiming, localization, sheet-set, or carrier replacement produces a local
protected model with zero collision invariant. The replacement, rather than
the failed raw model, is what may contribute a bounded charge.

The cell model is a certificate, not a substitute for the planar carrier:
UPTCR-1 must prove analytic realization and agreement with the actual
rooted puzzle-cell predecessor closure.

At the same checkpoint, the realized normalized response state is

\[
  \mathscr R_n
  =
  \frac{1}{r_{B,n}}
  \left(
    Q_n,\Lambda_n,\mathbf V_n,
    W_n^{\rm std},\mathbf\Xi_n
  \right),
  \qquad r_{B,n}>0.
\tag{3.4}
\]

The entries respectively record the response form, transport/transition
data, every required KKL Value moment, standard-width normalization, and the
finite shear, chart, endpoint-frame, and symbolic side state. The quotient
notation in (3.4) means simultaneous normalization in the declared
homogeneous gauge; it does not delete exact combinatorial labels.

## 4. Universal constants

All constants are chosen before the polynomial and its tower:

\[
\begin{gathered}
  d_0,w_0,m_0\in\mathbb N,\qquad
  \rho_0,\kappa_0,T_0,D_*,E_0<\infty,\\
  \eta_0>0,\qquad
  \lambda_{\rm raw}>1,\qquad
  0\leq\delta<\lambda_{\rm raw}-1.
\end{gathered}
\tag{4.1}
\]

Set

\[
  \lambda=\lambda_{\rm raw}-\delta>1.
\tag{4.2}
\]

The constants in (4.1) must be independent of:

- every satellite period and rotation number;
- every continued-fraction entry and depth;
- every Wave-horizon or corridor length;
- every virtual-Molecule depth and raw marking count;
- every counter value and stack-word length; and
- the number and order of primitive, neutral, satellite, puzzle, and virtual
  transitions.

A parameter-dependent finite prefix may enter the final bound for that
parameter. It may not be hidden in a constant advertised as universal or
beau.

## 5. Universal Protected-Tower Compactness and Rigidity Proposition

### Proposition UPTCR (open)

There are constants satisfying (4.1) such that every infinitely
renormalizable quadratic polynomial admits the canonical checkpoints and
predecessors of Section 3 and satisfies all six clauses below.

#### UPTCR-1 — canonical protected carrier

Every checkpoint has an actual marked carrier (3.1), constructed from the
rooted predecessor closure of all proof-supported puzzle cells. It contains
every small Julia component, critical-orbit segment, fjord, dam, obstacle,
and access used by Wave, Wanderers, quasi-additivity, covering, response, or
width arguments through the complete declared horizon.

The construction:

1. starts with the simultaneous root-pullback package;
2. freezes the complete protected free routing domain, applies the proved
   free-component criterion after the open
   `VIRTUAL_COMMON_FREE_COMPONENT`, and uses the resulting regulated tree
   together with the open `VIRTUAL_PROTECTED_ROUTING_CERTIFICATE`;
3. fullifies only while every protected-access survival map remains
   injective and cyclic-order preserving; and
4. on failure, either stops or constructs a declared collision-free
   replacement local model in an entry, exit, or terminal defect window.

Every realized protected core, including every central degree-one corridor,
has \(\chi_n=0\). Every raw defect used by a replacement model lies in a
defect window of depth at most \(m_0\), and the replacement must preserve all
proof-used accesses. The planar carrier realizes \(C_{\infty,n}\), is
independent of presentation and completion order, and no connector unforced
by the rooted predecessor or lamination-routing certificate is inserted.

#### UPTCR-2 — exact analytic realization

For every stage \(j+1\to j\) of every complete Wave horizon, the actual
pulled and immersed carriers satisfy

\[
  g_j^{-1}(H_{j+1})
  =
  H'_j
  =
  \iota_j^{-1}(H_j).
\tag{5.1}
\]

The selected quadratic-like return **spine** has exactly one declared
degree-two stage. Every other spine corridor map is univalent and
critical-value-free. Each auxiliary proof branch \(\beta\) carries its full
critical word and has degree

\[
  \deg(\beta)=2^{m(\beta)},
\tag{5.2}
\]

where \(m(\beta)\) is its number of critical encounters; in particular, the
bounded terminal Wave fan is not replaced by a lone degree-two component.
The stage maps:

- transport the full packages, obstacles, attachment traces, and survival
  maps equivariantly;
- extend to the complete prime-end markings without assuming local
  connectivity of \(H_j\);
- preserve cyclic order;
- induce compatible relative-cover subgroup lifts;
- are proper on the analytic cores and end-proper on every proof-used ideal
  interval; and
- charge only defects resolved by the collision-free bounded-window models
  from UPTCR-1.

The equality (5.1), component exhaustion, subgroup compatibility,
properness, and complete-horizon coverage are proved on the actual carriers,
not inferred from labels in a ribbon tree.

#### UPTCR-3 — uniform finite response state

The source-faithful active-core and WAD modules have dimensions at most
\(d_0\) and \(w_0\). If \(\rho_n\) denotes marking-to-replica congestion and
\(\kappa_n\) the normalized topological charge, then

\[
  \rho_n\leq\rho_0,
  \qquad
  \frac{\kappa_n}{r_{B,n}}\leq\kappa_0.
\tag{5.3}
\]

The state (3.4):

- retains exact counter, stack, endpoint-frame, Frobenius-flag, and chart
  semantics until a proved block closure forgets or compactifies them;
- is future-observable for every required KKL Value functional;
- transports exactly across every enabled core and WAD branch; and
- compares, with universal distortion and additive error in the calibrated
  gauge, to the applicable KKL WAD/Value, pseudo-Siegel sectorial, puzzle,
  and valid quadratic-like curve families.

“Applicable” means that the native hypotheses of the comparison theorem
hold. No ordinary satellite-root modulus is used uniformly in its relative
period.

#### UPTCR-4 — backward transition

There is one nonnegative calibrated potential

\[
  L_n=L_{t_n}(\mathscr R_n;\sigma_n)
\in[0,\infty)
\tag{5.4}
\]

such that, whenever \(L_n>D_*\),

\[
  L_{p(n)}
  \geq
  (\lambda_{\rm raw}-\delta)L_n-E_0
  =
  \lambda L_n-E_0.
\tag{5.5}
\]

Every complete block satisfies at least one certified route:

1. its accumulated entropy is at least \(\eta_0\);
2. it is absorbed by a uniformly controlled pseudo-Siegel
   regularization; or
3. it belongs to a transient or finite-shear alternative that is included
   in a larger complete block carrying strict contraction.

All localization, congestion, antirenormalization, cloning, and chart-change
errors in a block \(B\) satisfy

\[
  G_B(e_B)\leq\delta L_n+E_0.
\tag{5.6}
\]

Neutral chart changes are grouped with the dynamical block that supplies
strict contraction. A positive entropy label without the accumulated
\(\eta_0\) threshold does not discharge this clause. If bookkeeping requires
one route label, it uses an explicit deterministic priority rule; no
mathematical disjointness of the three routes is assumed.

#### UPTCR-5 — coercive marked compactness

For any sequence of normalized UPTCR checkpoints, a uniform bound on
\(L_n\), together with (5.3) and the protected side constraints, has a
subsequence converging in a specified marked-tower topology. The limit
retains:

- all proof-used carrier components and accesses;
- the relative-cover and stage-map relations;
- the response and Value observables; and
- the finite endpoint, chart, and shear state.

Unbounded counters and nesting or stack words are either forgotten after a
proved complete-block closure or embedded in a compact end/cylinder topology
on which carriers, guards, observables, and transitions extend continuously.
They cannot survive as uncontrolled discrete factors.

#### UPTCR-6 — tower rigidity and parameter fiber

The puzzle families associated with every UPTCR tower have Teichmüller
diameter at most \(T_0\) in the precisely declared marked category. If two
quadratic parameters have identical full marked combinatorics, finite-depth
pullback produces quasiconformal conjugacies with a universal dilatation
bound. Compactness from UPTCR-5 supplies a limiting global quasiconformal
conjugacy of the sphere, normalized at infinity. Every limiting Beltrami form
is invariant, and every controlled UPTCR tower supports no invariant line
field. Hence the limiting Beltrami form vanishes, the conjugacy is conformal,
and comparison of coefficients in the monic centered normalization gives
equality of parameters.

For each infinitely renormalizable \(c\), there is in addition a nested
sequence \(\Pi_N(c)\) of nonempty compact connected relative neighborhoods
of \(c\) in \(\mathcal M\) such that:

\[
  \Pi_{N+1}(c)\subseteq\Pi_N(c),
  \qquad
  \bigcap_{N\geq0}\Pi_N(c)
  =
  \{\text{parameters with the full marked combinatorics of }c\}.
\tag{5.7}
\]

Consequently the intersection in (5.7) is \(\{c\}\). Neither this singleton
conclusion nor shrinking of the pieces may be assumed in the construction
of the pullback conjugacies or in the proof of the no-invariant-line-field
statement.

## 6. Clause-to-ledger crosswalk

| UPTCR clause | Existing gates discharged only after a proof |
|---|---|
| UPTCR-1 | `PROTECTED_REGULATED_CONNECTOR_REALIZATION`, `PROTECTED_FREE_COMPONENT_CRITERION`, `AUGMENTED_ATOM_COMMON_DOMAIN`, `AUGMENTED_PACKET_CLOSURE_AUDIT`, and `HORIZON_FIRST_INVENTORY_AUDIT` plus the open `VIRTUAL_WAVE_HORIZON_CERTIFICATE`, `VIRTUAL_AUGMENTED_ATOM_PORT_CERTIFICATE`, `VIRTUAL_COMMON_FREE_COMPONENT`, `VIRTUAL_PROTECTED_ROUTING_CERTIFICATE`, `VIRTUAL_CANONICAL_INTERFACE_CARRIER`, `H1_CELL_TREE_EXTRACTION`, and the carrier part of `H1_MARKED_CONSTRUCTION` |
| UPTCR-2 | `H1_ANALYTIC_ACCESS_REALIZATION`, `VIRTUAL_CORRIDOR_PAIR_NATURALITY`, `VIRTUAL_ATTACHMENT_RESOLUTION` (with `VIRTUAL_ATTACHMENT_FREE_ANCHOR` only as its stronger Route A), `VIRTUAL_BOUNDED_ATTACHMENT_SUPPORT`, the analytic part of `H1_MARKED_CONSTRUCTION` |
| UPTCR-3 | `H2_RESPONSE_REALIZATION`, `H2_UNIFORM_CORE_WAD_DIMENSION`, `H2_VALUE_FEATURE_REALIZATION` |
| UPTCR-4 | `H2_DISCOUNTED_ERROR_CHARGE`, `H2_CHART_CYCLE_EXPANSION`, `H2_ENTROPY_DICHOTOMY`, `MBTT` |
| UPTCR-5 | `H3_SYMBOLIC_SIDE_COMPACTNESS`, `H3_COERCIVITY` |
| UPTCR-6 | `H4_RIGIDITY` |

This table is a promotion map, not a proof. In particular, proving (5.5)
alone does not prove UPTCR, coercivity, rigidity, or MLC.

## 7. Two proved logical lemmas

### Lemma 7.1 — nested compact singleton fibers shrink

Let \((X,d)\) be a metric space and let

\[
  K_0\supseteq K_1\supseteq K_2\supseteq\cdots
\]

be nonempty compact sets with \(\bigcap_n K_n=\{x\}\). Then
\(\operatorname{diam}K_n\to0\).

#### Proof

Suppose instead that \(\operatorname{diam}K_n\not\to0\). Since the diameters
are nonincreasing, there is \(\epsilon>0\) such that for every \(n\) there
is \(y_n\in K_n\) with \(d(x,y_n)\geq\epsilon/2\). Compactness of \(K_0\)
gives a convergent subsequence \(y_{n_k}\to y\in K_0\). For each fixed
\(N\), all sufficiently large \(n_k\) satisfy \(n_k\geq N\), hence
\(y_{n_k}\in K_N\). Since \(K_N\) is closed, \(y\in K_N\). Thus
\(y\in\bigcap_NK_N=\{x\}\), contradicting
\(d(x,y)\geq\epsilon/2\). \(\square\)

Connectedness is not needed for the diameter conclusion. It is needed when
the \(K_n\) are used as connected relative neighborhoods in the definition
of local connectivity.

### Theorem 7.2 — UPTCR implies MLC

If Proposition UPTCR is true, then the Mandelbrot set is locally connected.

#### Proof

Let \(c\in\mathcal M\).

If \(f_c\) is not infinitely quadratic-like renormalizable, the imported
Yoccoz theorem supplies local connectivity at \(c\).

Assume that \(f_c\) is infinitely renormalizable. Apply UPTCR and set
\(\lambda=\lambda_{\rm raw}-\delta>1\). The backward-record lemma applied
to (5.5) gives

\[
  \sup_{n\in\mathcal N(c)}L_n
  \leq
  \max\left\{
    L_{\rm prefix}(c),\,
    D_*,\,
    \frac{E_0}{\lambda-1}
  \right\}<\infty,
\tag{7.1}
\]

where \(L_{\rm prefix}(c)\) is the maximum over the finite initial
checkpoint prefix not governed by the recurrence. Indeed, a later value
strictly above the right side and maximal up to its checkpoint would force
the earlier value \(L_{p(n)}\) to be still larger, a contradiction.

UPTCR-5 converts (7.1), together with the universal side constraints, into
precompactness of the normalized marked tower. UPTCR-6 constructs the
uniformly quasiconformal finite-depth pullback conjugacies and a limiting
global normalized conjugacy. If its invariant Beltrami form were nonzero on
a positive-measure invariant set, normalization by its modulus would give an
invariant line field. Thus the Beltrami form vanishes. The conjugacy is
conformal and hence affine, say \(h(z)=az+b\). Comparing coefficients in
\(h\circ f_c=f_{c'}\circ h\) gives \(a=a^2\), \(2ab=0\), and therefore
\(a=1\), \(b=0\), and \(c=c'\). Hence the full marked combinatorial fiber in
(5.7) is \(\{c\}\).

Apply Lemma 7.1 to \(\Pi_N(c)\). Their diameters tend to zero. If \(U\) is
a relatively open neighborhood of \(c\) in \(\mathcal M\), choose \(r>0\)
with \(B(c,r)\cap\mathcal M\subset U\). For large \(N\),
\(\operatorname{diam}\Pi_N(c)<r\), and since \(c\in\Pi_N(c)\),
\[
  \Pi_N(c)\subset B(c,r)\cap\mathcal M\subset U.
\]
Thus every point has arbitrarily small connected relative neighborhoods.
Consequently every component of every relatively open subset is open, and
\(\mathcal M\) is locally connected at every infinitely renormalizable
parameter as well.

The two cases exhaust \(\mathcal M\), so \(\mathcal M\) is locally
connected. \(\square\)

The proof is conditional on all six UPTCR clauses. It neither proves UPTCR
nor changes the open status of MLC.

## 8. Proof obligations and first-failure certificates

A proposed proof of a clause must either close every row below or stop at
the first failure and record the specified certificate.

| Clause | Required proof | First-failure certificate |
|---|---|---|
| UPTCR-1 | actual rooted carrier, protected survival, bounded defect windows | block, first excess component, attachment access, full itinerary, collision coordinate |
| UPTCR-2 | equality (5.1), prime-end naturality, relative-cover lift, properness | stage, source and target components, subgroup image, extra sheet or ideal end |
| UPTCR-3 | independent core/WAD dimension bounds and exact Value observability | state dimension, missing future functional, failed quotient square, or congestion ratio |
| UPTCR-4 | complete-block routing and (5.5)--(5.6) | block word, transition matrix, chart cycle, entropy charge, error term, failed margin |
| UPTCR-5 | sequential compactness in an explicit marked topology | escaping carrier/access or uncontrolled counter/stack subsequence |
| UPTCR-6 | qc pullback, limiting conjugacy, no line field, connected parameter basis | finite depth, dilatation defect, limiting Beltrami form, or failed relative-neighborhood property |

If the first failure is a protected-access collision, the failed raw core is
inadmissible even in a bounded window. The state may be enlarged or retimed
only after proving that the replacement local model has zero protected
collision invariant and closes that exact failure. If it is a transition
failure, the replacement state must retain the matrix, chart, or memory
coordinate responsible. A coarse quotient that merely hides the defect is
not admissible.

## 9. Adversarial validation matrix

| Attack | Clause under attack | Required response |
|---|---|---|
| upper-half-disk protected-access collision | 1 | stop the raw model; a bounded window is usable only after constructing a replacement carrier with proved access survival and zero protected collision |
| rapidly increasing satellite periods | 1--4 | no constant or ordinary root-modulus comparison may depend on the period |
| alternating primitive and neutral blocks | 3--4 | close every chart cycle and group neutral changes with a strict block |
| entropy increments tending to zero | 4 | accumulate at least \(\eta_0\) or use a proved nonentropy route |
| unbounded virtual-Molecule depth and markings | 1, 3, 5 | retain exact proof-use data while bounding the active response state |
| late root enlargement and sheet merger | 1--2 | invalidate the prior sheet certificate and recompute the protected closure |
| relative-cover subgroup mismatch | 2 | stop; a set-theoretic carrier square is insufficient |
| topology-preserving width rescaling | 3 | invoke a proved analytic comparison, never topology alone |
| reducible polynomial shear | 3--4 | retain the shear flag until a strictly contracting complete block closes it |
| neutral chart cycle | 4 | prove strict product gain in one gauge or retime the block |
| unbounded counters or stack words | 3, 5 | prove forgetting or continuous extension to a compact end topology |
| prime-end monodromy or non-locally-connected carrier | 1--2 | use full-carrier collars and explicit cyclic-order transport |
| qc limit with nonzero invariant Beltrami form | 6 | stop; rigidity has failed and no singleton fiber follows |
| bounded-type Feigenbaum or bounded satellite | all | recover the established native theorem without weakening its hypotheses |
| KKL parabolically bounded primitive tower | 3, 4, 6 | specialize to the native KKL state and invoke Theorem B only after its beau-bound and puzzle-diameter hypotheses hold |

Finite regressions can falsify an incidence formula, closure rule, or record
threshold. They cannot establish any analytic UPTCR clause.

## 10. Promotion decision

This pass promotes only `UPTCR_IMPLIES_MLC`, the conditional implication
proved in Theorem 7.2.

It does **not** promote:

- `UNIVERSAL_PROTECTED_TOWER_CLOSURE`;
- `H1_MARKED_CONSTRUCTION`;
- `MBTT`;
- `H3_COERCIVITY`;
- `H4_RIGIDITY`; or
- `MLC`.

UPTCR may be promoted only after source-checkable proofs of all six clauses,
a backward dependency audit, a source-hypothesis audit, a
universal-constant audit, all diagnostic regressions, and a warning-free
rendered-manuscript audit.

## 11. Cross-validation disposition

The independent proof check is
[uptcr_cross_validation.md](uptcr_cross_validation.md). It establishes the
corrected conditional implication in Theorem 7.2 and audits the six clauses
in dependency order.

The topological realization from a protected ribbon-routing certificate is
now proved in
[protected_regulated_connector.md](protected_regulated_connector.md).
The unconditional attempt still stops at UPTCR-1 because current public
hypotheses do not prove `VIRTUAL_COMMON_FREE_COMPONENT` for an actual
virtual-Molecule block. The proved criterion in
[virtual_protected_routing_domain.md](virtual_protected_routing_domain.md)
constructs the certificate exactly when one component of the completed free
routing domain has simultaneous singleton ports to every root-shadow
cluster. Neither inclusion minimality nor monotone absorption fills the gap:
the former has no least connected solution, and the latter fails on the
critical-value-free \(z^2\) upper-half-disk example by erasing a protected
access. After the common component is proved, the larger
`VIRTUAL_PROTECTED_ROUTING_CERTIFICATE` must still realize every component
and critical word and close its future-complexity clauses.

The common-component gate now has a further proved reduction.  By
[virtual_common_free_component.md](virtual_common_free_component.md), a
finite family of pairwise disjoint full augmented atom/obstacle packets
inside one Jordan localization has connected complement.  Explicit
surviving free ports on the original atoms then prove the common-component
certificate.  The missing virtual assertion is
`VIRTUAL_AUGMENTED_ATOM_PORT_CERTIFICATE`: the actual block must supply the
future-complete assignment, disjoint fullifications, and surviving ports.
The fixed-packet theorem in
[augmented_packet_closure_audit.md](augmented_packet_closure_audit.md)
proves that the fullifications are unique and order-independent, that
same-label merger, localization, and empty-exposure defects persist, and
that individual ports can be truncated to a disjoint family.  The public
connected-hull paragraph still does not supply the actual inventory, zero
collision, original-atom exposure, complete-horizon transport, or uniform
incidence/compression.  This refinement does not alter the open status of
UPTCR-1.

The [horizon-first inventory audit](vaapc_inventory_source_audit.md)
isolates the first missing inventory field.  A fixed finite proof-use graph
has one least dependency closure, but Dudko's “appropriate number” of first
returns does not define the stopping horizon needed to form that graph.
KKL's native Hubbard-tree inventory also requires an unproved typed bridge
before it can be used on the virtual carrier.  Thus
`HORIZON_FIRST_INVENTORY_AUDIT` is proved while
`VIRTUAL_WAVE_HORIZON_CERTIFICATE` and `VAAPC-I` remain open.

This is a proof that the present derivation does not close; it is not a
counterexample to UPTCR or MLC. Their ledger statuses remain open.

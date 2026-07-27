# Regime classification and marked virtual-hull specification

## 1. Scope

This note separates three assertions that are easy to conflate:

1. KKL's exhaustive classification of a **family** of prime types;
2. a block decomposition of one infinite renormalization tower;
3. a geometric object that survives transitions between the blocks.

Only the first is currently a source-locked theorem/definition. The second and third are
formalized below as the exact new construction problem.

## 2. The family-level four-regime partition

For a prime satellite copy with rotation number

\[
  \frac pq=[a_1,\ldots,a_k],
\]

write \(h=\max_i a_i\) and \(d=k\). For a prime primitive copy \(M\), let
\(\ell(M)\) be the length of its maximal chain of satellite ancestors, and let
\(h(M),d(M)\) be the maxima of the satellite invariants along that chain, as in
KKL26. For a family \({\cal C}\), take the corresponding suprema.

**Proposition 2.1 (exhaustive family partition).** Every family \({\cal C}\) of
prime types belongs to exactly one of the following disjoint classes:

\[
\begin{array}{c|c}
\text{class} & \text{condition}\\ \hline
A & \ell({\cal C}),h({\cal C}),d({\cal C})<\infty,\\
P & \ell({\cal C}),d({\cal C})<\infty,\ h({\cal C})=\infty,\\
N & \ell({\cal C})<\infty,\ d({\cal C})=\infty,\\
V & \ell({\cal C})=\infty.
\end{array}
\]

**Proof.** First decide whether \(\ell\) is finite. If not, the family is in
\(V\). If it is finite, decide whether \(d\) is finite. If not, the family is
in \(N\). If both are finite, decide whether \(h\) is finite. The finite and
infinite alternatives give \(A\) and \(P\), respectively. The precedence makes
the four cases disjoint and exhaustive. \(\square\)

This proposition is deliberately modest. It does not say that a single tower is made of
four canonically delimited finite blocks.

## 3. Why a canonical tower decomposition is additional work

Let \(\tau_n=(\ell_n,h_n,d_n)\) be the local combinatorial data at renormalization
level \(n\). Every \(\tau_n\) is finite. Consequently the finite/infinite test in
Proposition 2.1 applies only to a set or tail of types, not to one level.

A finite block decomposition requires thresholds. For a triple
\({\bf B}=(B_\ell,B_h,B_d)\), define a provisional label

\[
L_{\bf B}(n)=
\begin{cases}
V,&\ell_n>B_\ell,\\
N,&\ell_n\le B_\ell,\ d_n>B_d,\\
P,&\ell_n\le B_\ell,\ d_n\le B_d,\ h_n>B_h,\\
A,&\text{otherwise}.
\end{cases}
\]

Maximal constant runs give a decomposition, but it is not canonical: changing
\({\bf B}\) changes both labels and endpoints. A proof needs a dynamically defined stopping
rule whose constants are fixed by the analytic lemmas, not by the tower.

### Required stopping rule

A valid stopping rule \(\sigma\) must output

\[
0=n_0<n_1<n_2<\cdots
\]

and block types \(t_j\in\{A,P,N,V\}\), with:

- **measurability from finite data:** \(n_{j+1}\) is determined by the return data through
  level \(n_{j+1}\);
- **bounded active interaction:** the non-translation core and the number of interaction
  types modulo each translation corridor are universally bounded; the total number of
  faithfully retained ideal intervals need not be bounded;
- **functoriality:** hybrid-equivalent marked towers have the same stopping data;
- **persistence:** extending a finite tower does not move earlier endpoints;
- **analytic certification:** each block satisfies the hypotheses of exactly one
  amplification or regularization theorem;
- **no discarded transition:** every iterate between \(n_j\) and \(n_{j+1}\) occurs in
  the marked partial orbit of the block.

No source in the ledger constructs such a rule for arbitrary mixtures. This is
Construction Gap `C1`.

## 4. Marked virtual pseudo-Siegel hull

### Definition 4.1 (admissible marked hull datum)

At a checkpoint \(n\), an admissible datum is

\[
{\mathfrak H}_n=(S_n,H_n,B_n,P_n^{\le r_n},{\cal I}_n,\Gamma_n)
\]

with the following properties.

1. \(S_n\) is the normalized dynamical surface on which the checkpoint return map is
   defined. It may be ql, \(\psi^\bullet\)-ql, sectorial, or puzzle-marked.
2. \(H_n\Subset S_n\) is a compact, connected, **full** continuum. Fullness means that
   \(S_n\setminus H_n\) has no unrecorded bounded complementary component.
3. \(H_n\) contains the small Julia sets assigned to the checkpoint and may contain the
   prescribed return orbit as in D25. Independently, every orbit point used by the proof
   is labeled in \(P_n^{\le r_n}\); membership in one global hull does not authorize use
   of the global degree-\(2^q\) complement return.
4. \(B_n\) contains every satellite base-cycle point, neutral access, parabolic gate, or
   dam endpoint used to define a pullback or homotopy class.
5. \(P_n^{\le r_n}=\{f^j(0):0\le j\le r_n\}\), after normalization and removal of
   repetitions, contains every postcritical point used by Wave, Wanderers,
   quasi-additivity, covering, or holonomy in this block.
6. \({\cal I}_n\) is the ideal/translation marking of boundary accesses and gates.
7. \(\Gamma_n\) is a nonempty marked homotopy-saturated family of essential closed
   curves and/or proper arcs in
   \[
      X_n=S_n\setminus(H_n\cup B_n\cup P_n^{\le r_n})
   \]
   separating the critical-value collar from the outer checkpoint boundary. Every
   proper arc has its endpoints in declared ideal intervals or access-boundary
   components encoded by \({\cal I}_n\). Homotopies are taken relative to all markings
   and, for proper arcs, relative to their declared endpoints (or named ideal endpoint
   classes).

The fullness and marking clauses are not cosmetic. Without fullness, filling a forgotten
component changes the homotopy class. Without \(B_n\), the BLOT estimate shows that the
ordinary root annulus is the wrong uniform object. Without \(P_n^{\le r_n}\), a pullback
may cross an omitted critical value and cease to be univalent.

### Definition 4.2 (candidate marked degeneration)

Here \(\operatorname{Ext}\) denotes extremal length for the declared marked family,
whether it consists of closed curves, proper arcs, or both. Use the convention in
which the essential core curves of an annulus \(A\) have width
\(1/\operatorname{mod}(A)\); that annular core family is only the checkpoint special
case. Set

\[
 D^\#({\mathfrak H}_n)
 =\operatorname{Ext}_{X_n}(\Gamma_n).
\]

The symbol \(D^\#\) always includes the surface, all markings, and the curve family.
Writing \(D(H_n)\) is prohibited because the same continuum with different markings can
represent different dynamical pullback problems.

### Construction 4.3 (regime-local hulls)

This is the target construction, with its proof status exposed.

| Regime | Proposed \(H_n\) | Marking | Local source | Status |
|---|---|---|---|---|
| \(A\) | filled Julia set/puzzle core and the prescribed little Julia sets | canonical rays, equipotentials, critical orbit used by the return | Kahn/Lyubich puzzle and ql theory, DL23 | `KNOWN LOCALLY` |
| \(P\) | primitive core plus parabolic gate collars | ideal and translation markings | KKL26 | `KNOWN FOR PARABOLICALLY BOUNDED SUBCASE` |
| \(N\) | pseudo-Siegel disk with fjords filled and dams attached | neutral accesses, dams, finite critical orbit | DL22/DL25 | `KNOWN LOCALLY IN THEIR SETTING` |
| \(V\) | full connected hull of the assigned Cantor small Julia sets and prescribed return orbit | all satellite base cycles, virtual accesses, finite postcritical labels | D25 proposal, with a required selected localization/fiber-product return | `OPEN` |

At an interface, take the full hull of the union of the two adjacent local objects and
carry forward the union of markings required by either side. This defines a set, but
does not prove bounded active interaction or width distortion. Distinct return accesses
must not be identified merely to force bounded marking cardinality; see
`virtual_block_quotient.md`.

## 5. Partial invariance

Let \(R_n\) be the return map attached to block \(n\), and let
\({\cal O}_n=P_n^{\le r_n}\). The datum is partially invariant if:

\[
  R_n(H_n\cap\operatorname{Dom}R_n)\subset H_n
\]

for every branch traversed before the stopping time, and every critical value of a
traversed branch belongs to \({\cal O}_n\).

For a pullback chain

\[
 \gamma,\ R_n^{-1}\gamma,\ldots,R_n^{-q}\gamma,
\]

admissibility additionally requires all \(q\) inverse branches to be defined in
\(X_n\) and univalent away from the single explicitly counted quadratic branch.

**Lemma 5.1 (finite-orbit sufficiency).** If the preceding branch condition holds, every
homotopy and covering calculation in that declared pullback chain is determined by the
marked datum through time \(r_n\); later postcritical points are irrelevant to that
calculation.

**Proof.** Each branch domain and each obstruction to univalence is decided by the
critical values encountered before its terminal time. By hypothesis these points and
all boundary accesses used by the chain are marked. No later iterate enters a branch
domain or its homotopy during the finite calculation. \(\square\)

This lemma does not prove that a desired Wave/Wanderers chain satisfies the branch
condition. That verification is the principal orbit audit in Construction Gap `C2`.

Partial invariance also does not imply pullback-component saturation. The exact
right-half-disk example in `selected_marked_fast_forward_fan.md`, Proposition 3.3,
has full connected source and target hulls with a surjective forward map but the
source hull is only a proper subset of the unique pullback component.
`saturated_virtual_seed_forest.md` supplies the canonical repair once
forward-coherent connected seeds are constructed: replace every seed by the
pullback component containing it. The repair may enlarge the carrier, so all
newly absorbed components and erased access families must be audited.

Putting the entire segment \(\{f_c^j(0):1\le j\le q\}\) into one full target hull makes
the global complement return proper, but its degree is \(2^q\); this is a diagnostic,
not the desired virtual renormalization. A degree-two selected return can be recovered
either by KKL-style localization/fiber products while retaining the global hull, or by
the stagewise pullback construction of Lemma 7.8 and Corollary 7.9 in
`virtual_block_quotient.md`. Constructing one of these alternatives with the exact
Wave/Wanderers branches and uniform geometry remains Gap `C2`.

## 6. Compatibility obligations

For consecutive checkpoint data \({\mathfrak H}_n,{\mathfrak H}_{n+1}\), a transition
map must provide:

\[
\Phi_n:
X_n'\longrightarrow X_{n+1}'
\]

between the subsurfaces actually used by the curve families, with controlled degree and
dilatation. The following are the required estimates.

### `K1` Marking transport

\(\Phi_n\) sends base cycles, accesses, and partial postcritical points used downstream
to their declared successors. No marked point may disappear until the last argument
that uses it.

### `K2` Width comparison

For the transported family,

\[
\left|
\operatorname{Ext}_{X_{n+1}}(\Gamma_{n+1})
-a_n\operatorname{Ext}_{X_n}(\Gamma_n)
\right|\le e_n,
\]

where \(a_n\) is the explicit covering/entropy factor. For neutral regularization,
\(\Gamma_n\) is split into vertical, peripheral, and residual families before this
comparison.

### `K3` Amortized interface loss

Across any antirenormalization chain contained in one block,

\[
 \sum e_n\le E_0
\]

with \(E_0\) universal, **or**

\[
\sum e_n\le \delta D_{\rm block}+E_0
\]

where \(\delta\) is smaller than the amplification margin. A bound \(e_n=O(1)\) per
elementary scale is insufficient when the satellite chain length is unbounded. KKL's
translation model naturally gives a topology term proportional to the marking
cardinality, so relative domination is an essential permitted mechanism.

### `K4` Bounded active interaction complexity

The complement decomposes into a core with at most \(T_0\) active WAD vertices,
effective limbs, and degree-\(>1\) branches, together with a universally bounded number
of faithfully marked translation corridors. For fixed localization radius, the number
of corridor interaction types modulo translation is bounded independently of corridor
length. The raw number of ideal intervals is allowed to grow.

### `K5` Return completeness

Every orbit segment used by Wave, Wanderers, quasi-additivity, covering, or
phase--parameter holonomy lies in one of the two adjacent partial postcritical markings.

| Transition | `K1` | `K2` | `K3` | `K4` | `K5` |
|---|---:|---:|---:|---:|---:|
| \(A\to A\), bounded combinatorics | local theory | local theory | local theory | local theory | local theory |
| parabolically bounded \(P\to A/P\) | KKL setting | KKL setting | relative topology error controlled in KKL's high-degeneration regime | active core plus translation marking | KKL setting |
| \(N\to N\) inside one neutral tower | DL setting | DL estimates | antirenormalization mechanism | tilings controlled away from explicit threshold issue | DL setting |
| arbitrary \(N\leftrightarrow P/A\) | open | open | open | open | open |
| any transition involving \(V\) | open | open | open | open | open |

“Local theory” means only under that theory's hypotheses. The table is not a claim that
the hypotheses automatically persist across a mixed tower.

## 7. Entropy-clock blocks

KKL's Value contradiction uses positive core entropy. Near the molecule this entropy can
approach zero, so a fixed number of elementary levels cannot have a uniform contraction.

For a positive-entropy checkpoint \(j\), let \(\rho_j>1\) be the Perron factor of its
finite core transition matrix, and set \(\epsilon_j=\log\rho_j\). Put
\(\epsilon_j=0\) for a sectorially regularized zero-entropy step. For a block \(B\), define

\[
 E(B)=\sum_{j\in B}\epsilon_j.
\]

An entropy-clock block ends at the first checkpoint where either:

- \(E(B)\ge\eta_0\), for a universal \(\eta_0>0\); or
- the entire remaining degeneration has entered a pseudo-Siegel hull and satisfies the
  sectorial controlled alternative.

This is the natural repair for vanishing one-step entropy, but it is not yet a theorem.
To work, the accumulated interface error must satisfy either an absolute summability
bound or

\[
 \sum_{j\in B} e_j \le c\,E(B)D_B+E_0
\]

with \(c\) small enough for Value contraction to dominate, or directly
\(\sum e_j\le\delta D_B+E_0\) below the amplification margin. This estimate is Gap
`C3`.

## 8. Special-case recovery tests

| Test | Reduction |
|---|---|
| bounded-type Feigenbaum | Hull reduces to ordinary ql core; entropy blocks have bounded length; DL23 supplies beau bounds and rigidity. |
| parabolically bounded primitive | Hull and WAD reduce to the KKL26 setting; its amplification and puzzle-Teichmüller theorem apply. |
| neutral Siegel limit | Positive entropy clock is zero; pseudo-Siegel vertical/peripheral decomposition is the active branch, as in DL22/DL25. |
| high-type satellite \(\mathcal QG\) | Classical root modulus is not required; the result must be compatible with the shrinking theorem of CS15. |
| rapidly increasing satellite periods | Root-annulus comparison is forbidden; \(B_n\) and the sectorial/marked family must absorb the period. |
| alternating neutral/primitive blocks | Every interface invokes `K1`--`K5`; no existing source proves their uniform composition. |

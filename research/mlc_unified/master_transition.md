# Master Transition: no-go theorem and corrected target

## 1. Conventions

Renormalization levels increase toward smaller/deeper scales:

\[
F_0\longmapsto F_1\longmapsto F_2\longmapsto\cdots .
\]

For a genuine ql annulus \(A=V\setminus \overline U\), the KKL width convention is

\[
W(F)=\frac{1}{\operatorname{mod}(A)}.
\]

Large width means degeneration.

## 2. Exact obstruction from unbounded satellites

**Theorem 2.1 (unmarked root-width no-go).** There do not exist universal constants
\(K,C<\infty\) and a scalar hull functional \(D\) such that, for every quadratic
satellite polynomial-like cycle of relative period \(s\),

\[
 D\le K
 \quad\text{and}\quad
 \left|D-\frac1{\operatorname{mod}(A)}\right|\le C
\]

for a root annulus \(A\).

**Proof.** BLOT's Main Theorem, specialized to a degree-two polynomial, gives

\[
 \operatorname{mod}(A)
 <
 \frac{2\pi}{\log(4(s+1))}.
\]

Therefore

\[
 \frac1{\operatorname{mod}(A)}
 >
 \frac{\log(4(s+1))}{2\pi}.
\]

The right side tends to infinity with \(s\). The two assumed inequalities would instead
give \(1/\operatorname{mod}(A)\le K+C\), a contradiction for sufficiently large
\(s\). \(\square\)

**Corollary 2.2.** At an unbounded-satellite root, a uniformly controlled
pseudo-Siegel/virtual quantity cannot be universally additively comparable to ordinary
inverse root modulus. A valid comparison theorem must do at least one of the following:

- change the marked surface by including the base cycle and required postcritical data;
- change the curve family to sectorial/vertical/peripheral families;
- skip the root as a ql checkpoint and compare only after a declared block transition.

This is why “quadratic-like modulus only at valid checkpoint scales” needs a formal
validity predicate. Without it, the Width Comparison lemma is false.

## 3. The proposed forward induction does not close

The plan proposed a successor inequality

\[
 D_{n+k}\ge\lambda D_n-C,\qquad \lambda>1,
\]

followed by a contradiction with a “global Teichmüller/covering growth bound.”

**Proposition 3.1 (logical no-go).** A forward lower recurrence alone cannot give a
uniform upper bound for \(D_n\).

**Proof.** For any \(\lambda>1\), the sequence \(D_n=\lambda^n\) satisfies
\(D_{n+1}\ge\lambda D_n-C\) for every \(C\ge0\), and is unbounded. A contradiction
requires an independent upper growth estimate. \(\square\)

No such period-independent upper estimate is imported in the source ledger. Indeed,
Theorem 2.1 permits ordinary satellite inverse root widths of arbitrary size as the
relative period varies. Thus the proposed global induction is not a consequence of the
listed tools.

The successful Feigenbaum/KKL architecture has the opposite orientation: bad geometry
at a deeper level forces worse geometry at an earlier level. A record at a deep level
then contradicts its own record property.

## 4. The replacement state

Use the marked hull datum from `regime_and_hulls.md`:

\[
{\mathfrak H}_n=(S_n,H_n,B_n,P_n^{\le r_n},{\cal I}_n,\Gamma_n),
\qquad
D_n^\#=\operatorname{Ext}_{X_n}(\Gamma_n),
\]

where

\[
X_n=S_n\setminus(H_n\cup B_n\cup P_n^{\le r_n}).
\]

At a neutral block, \(\Gamma_n\) is a declared sum of vertical, peripheral, and residual
families. Degeneration consumed by pseudo-Siegel fjords is represented in \(H_n\) and is
not counted again as residual degeneration. At a satellite block, the base cycle is in
\(B_n\); \(D_n^\#\) is not ordinary root width.

The BLOT marked-geodesic theorem supports this change of state: after the base cycle is
added to the postcritical marking, the relevant hyperbolic geometry behaves in the
opposite direction from the shrinking root annulus. It does not by itself prove the
needed extremal-width transition estimate.

## 5. Width-comparison ledger

The intended comparison theorem must be split by chart.

### `WC-A`: ordinary ql/puzzle chart

If the checkpoint annulus is non-satellite or belongs to a source-locked bounded family,
and the added collars have uniformly bounded conformal geometry, require

\[
  |D_n^\#-W(F_n)|\le C_A.
\]

This is available only inside the existing ql/puzzle theories satisfying their
hypotheses. It is not asserted at arbitrary satellite roots.

### `WC-P`: parabolic/translation chart

For a source-licensed KKL translation marking, let \(Q\) be the retained
core/short-WAD coordinate, \(S\) the aggregate standard width, and \(\kappa\) the
marked surface/translation complexity. After a separate localization comparison with
error \(e_{\rm loc}\), the source-compatible target is

\[
  Q-e_{\rm loc}
  \le D_n^\#
  \le Q+4S+C_{\rm net}\kappa+e_{\rm loc}.
\tag{WC-P}
\]

Thus the comparison becomes multiplicative or affine-relative only after proving
\[
  4S+C_{\rm net}\kappa+e_{\rm loc}
  \le\delta L_n+E_0
\]
in the calibrated gauge, or the corresponding density estimate. Passing to
translation-orbit types bounds **active interaction complexity** but does not erase
the unbounded marking labels. A universal additive constant is available only in a
subchart where the displayed raw charge is itself uniformly bounded.

### `WC-N`: pseudo-Siegel chart

Use the vertical, peripheral, and residual families of DL22/DL25 only inside their
source hypotheses. Their widths are not automatically additive merely because the
families are named separately. Construct the actual parallel/serial response rule
\(\mathcal A_N\) and require, in normalized cell units,
\[
  \left|
    D_{n,\rm cell}^\#
    -
    \mathcal A_N
    \left(
      D_{n,\rm cell}^{\mathrm{ver}},
      D_{n,\rm cell}^{\mathrm{per}},
      D_{n,\rm cell}^{\mathrm{res}}
    \right)
  \right|
  \le e_N,
\tag{WC-N}
\]
where \(e_N\) is bounded, relative, or future-entropy-discounted in the common gauge.
If the realized geometry proves that the families are independent parallel families,
\(\mathcal A_N\) is their sum; this must not be assumed. Aggregated tile errors may be
\(O(r_m)\) or \(O(r_m\sqrt{A_m})\), so a bare global \(O(1)\) is not asserted. The
pseudo-Siegel hull consumes the invariant fjord component. DL25 gives local estimates,
including transitional-level bounds, but says applications need global input.
Transport through a mixed transition is open.

### `WC-V`: virtual-molecule chart

After isolating a bounded active core and encoding each translation corridor by
interaction orbits, first prove global WAD-coordinate injectivity and a
translation-realized surface decomposition. The target is

\[
  Q_n-e_{n,\rm loc}
  \le D_n^\#
  \le
  Q_n+4S_n+C_{\rm net}\kappa_n+e_{n,\rm loc},
\tag{WC-V}
\]

with universally bounded active interaction types and with all used returns faithfully
marked in the core or in a corridor. The raw error must then satisfy the
density/congestion or entropy-discounted budget required by Lemma 5.4. Orbit
compression does not make \(S_n\) or \(\kappa_n\) universally bounded.
This is Dudko's Interpolation Problem in proof-ready form and is open.

### Vector state and cone calibration

The quotient obstruction shows that the unified datum cannot initially be summarized by
the raw scalar \(D_n^\#\). Before response realization, padding absent corridors by
zero gives the local bookkeeping vector

\[
\mathscr D_n^{\rm raw}=
\left(
D_n^{\rm act},
W_{n,1}^{\rm std},\ldots,W_{n,r_0}^{\rm std},
\operatorname{val}({\cal O}_n)
\right)\in\mathbb R_{\ge0}^{r_0+2}.
\]

This raw vector does not remember arbitrary serial/parallel wiring. The proposed common
homogeneous coordinate after response realization is instead
\[
\mathscr D_n:=\mathscr R_n=
\left(
  \frac{Q_n}{r_{B,n}},
  \frac{\Lambda_n}{r_{B,n}},
  \frac{\mathbf V_n}{r_{B,n}},
  \frac{W_n^{\rm std}}{r_{B,n}},
  \frac{\mathbf\Xi_n}{r_{B,n}}
\right)\in{\cal C}_{t_n},
\]
with side/error data
\[
\sigma_n=
\left(
  r_{B,n},
  \boldsymbol\nu_n,
  \omega_n,
  \rho_n,
  \frac{\kappa_n}{r_{B,n}},
  {\cal P}_n,
  {\cal F}_n
\right).
\]
Here \(\mathbf V_n\) is the vector of outgoing KKL Value moments not already
recoverable from a proved Value-faithful port state; `bc2_value_feature.md` gives its
exact lifted-state rank test. The unbounded vector \(\boldsymbol\nu_n\) records the
declared exact corridor/return counters; its dimension, unlike its values, must be
universal. The word \(\omega_n\in\mathcal T^*\) retains the full ordered
nested-molecule data whenever future admissibility depends on it. It may be
compressed or operated on as a pushdown stack only after a source theorem proves a
universal finite-alphabet LIFO rule with predecessor frame/WAD recovery; until then
it remains an opaque, uncompressed labeled word. Its depth may be unbounded and it is
never a homogeneous coordinate. The provisional vector \(\mathbf\Xi_n\) records
non-regularized nilpotent shear moments, and \({\cal F}_n\) records the discrete
Frobenius flag/transfer type. The Virtual Corridor Transfer Trichotomy must prove
\(\mathbf\Xi_n\) has universally finite dimension and transports homogeneously, or
show sectorial regularization removes it; it is zero outside that retained-shear
branch. Only \(\mathscr R_n\) is scaled by a homogeneous gauge.
The cell count, counters, and optional stack word
\((r_{B,n},\boldsymbol\nu_n,\omega_n)\), congestion, normalized topology charge, and
port/ribbon order and endpoint core frame/holonomy constrain the admissible chart;
their constants must be uniform even when these raw discrete values diverge.
The lemmas below use \(\mathscr D_n\) for a generic realized cone coordinate. The
matrix/covector specialization requires a chart into a nonnegative orthant; the
ordered-cone form of Lemma 5.4 applies directly when a response-form order and error
gauge have been proved.

For the translation-clone branch,
`virtual_clone_entropy.md` proves an exact gain. If the complete virtual corridor has
a source-licensed corrected clone model of gate dimension at most \(d\), maximum
first-return length at most \(N\), and common delay \(n>N\), then its forward Value
coordinate contracts by less than \(2^{-1/(2d)}\). The period-independent constant
is proved internally from the exact \(t^{-k}\) return equation and integer
edge-occurrence counts. Constructing that reduced clone and controlling its
WAD/surface error is still open; a coarse translation picture does not imply the
typed edge graph. The printed KKL \(+\lambda^k\) finite-\(n\) bridge remains
quarantined as a source claim by `kkl_transfer_orientation_audit.md`.

This branch is not exhaustive. `corridor_entropy_shear_dichotomy.md` proves that a
bounded-dimensional nonzero irreducible non-permutation **framed return** has a
uniform entropy gap, whereas nonexpanding transfers may be transient or accumulate
polynomial shear. An open layer has no intrinsic spectral radius.
`corridor_support_automaton.md` reduces a source-faithful nonstationary language to a
uniformly short support skeleton plus an ordered history of contextual numerical loop
occurrences. The transition theorem must therefore carry finite
automaton/frame/transfer/flag state until each complete return is routed to clone,
closed source-licensed positive entropy, transient extinction, or
pseudo-Siegel/shear regularization.

Write \(\Phi_{tu}\) for the **backward** transition from the current chart \(u\) at
level \(n\) to the predecessor chart \(t\) at level \(p(n)\); its directed edge is
\(u\to t\). It must first give a componentwise homogeneous inequality

\[
\mathscr D_{p(n)}
\succeq \Phi_{tu}(\mathscr D_n)-e_n,
\tag{5.1}
\]

where \(\Phi_{tu}\) is order preserving and positively homogeneous. WAD series
composition uses harmonic sum, so a fixed positive matrix is not uniformly comparable
without a balance or bottleneck-chamber theorem; see
`corridor_network_calibration.md`, Theorem 6.2.

The raw marking-complexity term
\[
\kappa_n=|\chi(S_n)|+|\mathcal I_n|+\sum_aN_{n,a}
\]
is not a coercive coordinate of \(\mathscr R_n\): any uniformly positive coefficient on
\(\kappa_n\) would force the final potential to diverge along unbounded translation
markings. It must be absorbed by relative degeneration, charged to entropy, canceled,
or retained only through the side density \(\kappa_n/r_{B,n}\) before cone
calibration.

If a balance/chamber lemma supplies nonnegative matrices \(A_{tu}\) satisfying
\[
\Phi_{tu}(x)\succeq A_{tu}x
\]
with uniform comparison, then the following conditional linear reduction applies.

**Lemma 5.1 (cone calibration implies scalar amplification).** Suppose there are
positive covectors \(v_t\), a number \(\lambda>1\), and \(C<\infty\) such that for every
allowed backward chart edge \(u\to t\)

\[
v_t^{\mathsf T}A_{tu}\ge\lambda v_u^{\mathsf T}
\tag{5.2}
\]

componentwise, and

\[
v_t^{\mathsf T}e_n\le C.
\tag{5.3}
\]

Then

\[
L_n:=v_{t_n}^{\mathsf T}\mathscr D_n
\]

satisfies

\[
L_{p(n)}\ge\lambda L_n-C.
\]

The same conclusion, with a smaller factor \(\lambda-\delta>1\), holds if
\[
v_t^{\mathsf T}e_n\le\delta L_n+C
\quad\text{for }0\le\delta<\lambda-1.
\]

**Proof.** Apply the matrix lower bound to (5.1), multiply by
\(v_t^{\mathsf T}\), apply (5.2), and subtract the
error estimate. In the relative case the resulting coefficient is
\(\lambda-\delta>1\). \(\square\)

**Lemma 5.2 (homogeneous Lyapunov reduction).** Suppose every chart \(t\) has a function
\[
L_t:\mathbb R_{\ge0}^d\to\mathbb R_{\ge0}
\]
that is monotone, positively homogeneous, and subadditive. Suppose an allowed
backward edge \(u\to t\) satisfies
\[
\mathscr D_{p(n)}
\succeq
\Phi_{tu}(\mathscr D_n)-e_n
\]
and
\[
L_t(\Phi_{tu}(x))\ge\lambda L_u(x)
\tag{5.4}
\]
for every \(x\ge0\), where \(\lambda>1\). Then
\[
L_t(\mathscr D_{p(n)})
\ge
\lambda L_u(\mathscr D_n)-L_t(e_n).
\tag{5.5}
\]
If
\[
L_t(e_n)\le\delta L_u(\mathscr D_n)+C,
\qquad
0\le\delta<\lambda-1,
\tag{5.6}
\]
then the potentials satisfy the backward recurrence
\[
L_t(\mathscr D_{p(n)})
\ge
(\lambda-\delta)L_u(\mathscr D_n)-C.
\tag{5.7}
\]

**Proof.** Put \(z=\Phi_{tu}(\mathscr D_n)\). Since the state is nonnegative,
\[
\mathscr D_{p(n)}\succeq(z-e_n)_+.
\]
Monotonicity gives
\[
L_t(\mathscr D_{p(n)})\ge L_t((z-e_n)_+).
\]
Componentwise,
\[
z\preceq(z-e_n)_++e_n.
\]
Monotonicity and subadditivity therefore give
\[
L_t(z)
\le L_t((z-e_n)_++e_n)
\le L_t((z-e_n)_+)+L_t(e_n).
\]
Rearrange and apply (5.4), then (5.6). \(\square\)

**Lemma 5.3 (error-stable Lyapunov reduction).** Suppose \(L_t\) is monotone and
positively homogeneous and has an error gauge \(G_t\) satisfying
\[
L_t((x-e)_+)\ge L_t(x)-G_t(e)
\tag{5.8}
\]
for all \(x,e\ge0\). If
\[
L_t(\Phi_{tu}(x))\ge\lambda L_u(x)
\tag{5.9}
\]
and
\[
\mathscr D_{p(n)}
\succeq
\Phi_{tu}(\mathscr D_n)-e_n,
\]
then
\[
L_t(\mathscr D_{p(n)})
\ge
\lambda L_u(\mathscr D_n)-G_t(e_n).
\tag{5.10}
\]

**Proof.** Monotonicity gives
\[
L_t(\mathscr D_{p(n)})
\ge L_t((\Phi_{tu}(\mathscr D_n)-e_n)_+).
\]
Apply (5.8) and then (5.9). \(\square\)

Lemma 5.2 is the special case \(G_t=L_t\). A bottleneck gauge
\[
L_t(x)=\min_i a_ix_i
\]
satisfies (5.8) with
\[
G_t(e)=\max_i a_ie_i,
\]
because
\[
\min_i a_i(x_i-e_i)_+
\ge
\min_i a_ix_i-\max_i a_ie_i.
\]
Thus min/harmonic chamber calibrations are included even though a minimum of linear
forms need not be subadditive.

Thus the “one functional” is a calibrated Lyapunov function, not the unmarked width of
the continuum \(H_n\). It may be the chart norm \(L_n\) after a verified matrix
reduction, or a positive homogeneous nonlinear function adapted directly to the maps
\(\Phi_{tu}\). Lemma 5.2 proves the scalar reduction in the latter setting. Constructing
the gauges and proving (5.4) remain part of mixed-chart analysis.

Forward comparison estimates use different notation. Write
\[
  \Psi_{ut}:{\cal C}_t\longrightarrow{\cal C}_u
\]
for a map from a predecessor state \(x\) in chart \(t\) to its successor state
\(y\) in chart \(u\). A forward upper estimate
\[
  y\preceq \Psi_{ut}(x)+e
\tag{5.11}
\]
is not itself a backward lower estimate. The following lemma states the additional
calibration needed to invert it at the scalar level.

**Lemma 5.4 (forward contraction implies backward amplification).** Suppose
\({\cal C}_t,{\cal C}_u\) are ordered cones, \(L_t,L_u\) are monotone, positively
homogeneous gauges, and \(G_u\) is an error gauge satisfying
\[
  y\preceq z+e
  \quad\Longrightarrow\quad
  L_u(y)\le L_u(z)+G_u(e)
\tag{5.12}
\]
for all admissible \(y,z,e\in{\cal C}_u\). If (5.11) holds and, for some
\(0<\mu<1\),
\[
  L_u(\Psi_{ut}(x))\le \mu L_t(x),
\tag{5.13}
\]
then
\[
  L_t(x)\ge
  \mu^{-1}L_u(y)-\mu^{-1}G_u(e).
\tag{5.14}
\]
Consequently, if
\[
  G_u(e)\le\delta L_u(y)+C,
  \qquad 0\le\delta<1-\mu,
\tag{5.15}
\]
then
\[
  L_t(x)\ge
  \frac{1-\delta}{\mu}L_u(y)-\frac C\mu,
\tag{5.16}
\]
whose multiplicative factor is strictly larger than one.

**Proof.** Apply (5.12) to (5.11), then (5.13):
\[
  L_u(y)
  \le L_u(\Psi_{ut}(x))+G_u(e)
  \le\mu L_t(x)+G_u(e).
\]
Rearranging proves (5.14); inserting (5.15) proves (5.16). \(\square\)

Thus there are two legitimate interfaces to MBTT: prove a backward componentwise
lower transition \(\Phi_{tu}\) and use Lemmas 5.1--5.3, or prove a forward upper
transition \(\Psi_{ut}\) together with the strict forward contraction (5.13) and use
Lemma 5.4. Here \(\Psi_{ut}\) may, and generally must, be the composition over a
complete entropy-clock block; identity localization/chart changes are grouped with
the dynamical step that supplies contraction. A forward upper block transition without
(5.13) supplies no amplification.

## 6. Corrected Master Transition Theorem

The following is the exact theorem that would replace the proposed forward lemma.

**Marked Backward Transition Theorem (MBTT, `OPEN`).** There are universal constants
\[
D_*<\infty,\quad
\lambda_{\rm raw}>1,\quad
0\le\delta<\lambda_{\rm raw}-1,\quad
E_0<\infty,\quad
\eta_0>0,
\]
and a canonical entropy-clock stopping rule with the following property. Set
\[
  \lambda=\lambda_{\rm raw}-\delta>1,
  \qquad C=E_0.
\]

For every infinitely renormalizable quadratic map, construct regularized marked
checkpoint data \({\mathfrak H}_n\), finite-dimensional homogeneous
response-density states \(\mathscr R_n\), admissible side data \(\sigma_n\), and
calibrated scalar potentials \(L_n=L_{t_n}(\mathscr R_n;\sigma_n)\). Raw cell count,
counter values, and optional stack depth in \(\sigma_n\) may be unbounded. If
\(L_n>D_*\), then there is a preceding checkpoint
\(p(n)<n\) such that

\[
 L_{p(n)}\ge\lambda L_n-C.
\tag{MBTT}
\]

The transition from \(p(n)\) to \(n\) satisfies:

1. every nonexpanding subblock is routed to transient extinction, absorbed into a
   pseudo-Siegel/virtual hull, or retained only inside an augmented complete block
   with its own proved strict contraction;
2. every remaining entropy-driven contraction comes from closed source-framed
   subblocks with accumulated entropy at least \(\eta_0\);
3. before the error is subtracted, the calibrated scalar transition has factor at
   least \(\lambda_{\rm raw}\), and its aggregated antirenormalization/chart-change
   error obeys
   \[
     G_B(e_B)\le\delta L_n+E_0;
   \]
4. the active WAD topology, number of translation corridors, and interaction types
   modulo translation are universally bounded; raw marking cardinality may be unbounded;
5. all orbit segments used by the proof are present in the partial postcritical marking;
6. if regularization leaves no residual family, then \(L_n\le D_*\), so the premise
   of (MBTT) is false rather than an alternative needing further induction.

Clause 6 incorporates the “regularizes” branch into the definition of the regularized
state. This makes the record argument unambiguous.

## 7. Record lemma

**Lemma 7.1 (backward recurrence bounds every tower).** Let \(D_n\ge0\). Suppose that
there are \(D_*,C<\infty\) and \(\lambda>1\) such that, whenever \(D_n>D_*\), there is
some \(p(n)<n\) with

\[
D_{p(n)}\ge\lambda D_n-C.
\]

Then

\[
\sup_{n\ge0}D_n
\le
\max\left\{D_0,D_*,\frac{C}{\lambda-1}\right\}.
\]

If the recurrence begins only after checkpoint \(N_0\), replace \(D_0\) by
\(\max_{0\le j\le N_0}D_j\).

**Proof.** Put
\[
K=\max\left\{D_0,D_*,\frac{C}{\lambda-1}\right\}.
\]
If some \(D_n>K\), choose the first index at which the running maximum exceeds \(K\).
The recurrence gives
\[
D_{p(n)}\ge\lambda D_n-C>D_n,
\]
because \(D_n>C/(\lambda-1)\). But \(p(n)<n\), contradicting the choice of \(n\) as a
new running maximum. The delayed version is identical after treating the finite prefix
as the initial record. \(\square\)

This is the exact closure mechanism used by the corrected architecture. It needs no
unsupported global growth bound.

## 8. What must be proved to establish MBTT

### `M1` Virtual-hull construction

Construct full connected \(H_n\), markings, and curve families at every entropy-clock
checkpoint, including arbitrary \(V\)-blocks. Decompose the complement into a bounded
active core and faithfully marked accelerated-translation corridors. Prove uniform
interaction complexity modulo translation. A bounded quotient preserving all marked
accesses is impossible by `virtual_block_quotient.md`, Theorem 2.2.

`virtual_hull_realization.md`, Proposition 3.2 and Theorem 5.1 prove the relevant
complexity and calibration algebra under a sharper sufficient model. The actual
missing result has two layers: a monotone finite cell-tree quotient of the Cantor
carrier, followed by analytic prime-end/access realization. The analytic layer must
prove complete access incidence, \(\sum N_a=O(R)\), \(S=O(R)\), and a positive density
of genuinely distinct parallel WAD replicas. Connectedness of the Cantor small-Julia
hull proves none of these.

Writing \(r_{\rm mark}\) for marking cells and \(r_\parallel\) for parallel replicas,
the exact conditional estimate contains the congestion factor
\[
\rho_B=\frac{r_{\rm mark}}{r_\parallel}:
\qquad
W\le
\left[
1+
\frac{4b+C_{\rm net}c}{aD}\rho_B
\right]Q.
\]
Thus the required invariant is bounded \(\rho_B\), or at least
\(\rho_B/D\) below the expansion margin. Raw return count is not replication: serial
cells combine harmonically and repeated isotopic accesses do not add WAD weight.

The orbit-packing lemma in `corridor_network_calibration.md` gives a concrete sufficient
criterion for the interaction bound. For accelerated corridor length \(q_B\) and
inactive buffer \(b_B\), prove
\[
q_B\ge2b_B,
\qquad
\frac{3|\chi(S_B)|+|\mathcal I_B|}{q_B}\le\tau_0,
\]
and prove that every good class has an admissible translated representative through
the \(q_B-b_B\) interior cells. Raw topology may grow; normalized marked topology may
not.

For a return of time \(q\), also construct a selected pullback factorization with exactly
one degree-two step and all other steps univalent. The proper global complement map has
degree \(2^q\) and cannot substitute for this factorization.

Equivalently, prove the Finite-Horizon Analytic Inflation Theorem of
`finite_horizon_inflation.md`: promote the partial postcritical data through the
stopping time to a \(\psi\)-ql fiber-product correspondence without assuming a globally
forward-invariant enlargement. This now has three separately audited parts:

1. stagewise forward closure and relative-cover lifting;
2. local saturation, core properness, and orbit admissibility through the horizon;
3. quantitative localization with relative or entropy-amortized width loss.

The first part has formal criteria. The virtual existence and the quantitative estimate
remain open. Theorem 7.1 of that note rules out deriving width control from topological
inflation alone.

### `M2` Mixed-chart calibration

Prove `WC-A`--`WC-V` with additive, relative, density-normalized, or discounted errors
stated explicitly and with all comparison parameters independent of relative period,
rotation number, continued-fraction depth, virtual-molecule depth, and neighboring
regime. Extract either backward lower maps with a common expanding calibration, or
complete forward upper block maps with a common strictly contracting calibration.
Alternatively, prove a uniform balance/bottleneck-chamber lemma, extract transition
matrices, and verify the corresponding chart covectors.

`network_response_state.md` gives a third, structurally exact candidate: a
bounded-terminal response matrix on which parallel gluing is addition and serial
elimination is Schur complement. Its surface comparison and an expanding scalar gauge
remain open. Whichever state is used, every directed cycle of chart transitions must
expand as a composition. An identity or neutral cycle on a state of positive gauge
rules out a common edgewise factor \(\lambda>1\).

`marked_collar_calibration.md` proves the scalar connected-exterior case by annular
exhaustion. The open part is precisely the access-faithful multi-corridor extension:
localization must act on the finite vector state without joining marked components or
losing a fixed amount at each of unboundedly many interfaces.

### `M3` Amortized antirenormalization error

If a block contains \(q\) elementary scales, an \(O(1)\) loss per scale is not enough.
Prove either

\[
\sum_{j=1}^{q}e_j\le E_0
\]

or the entropy-weighted form

\[
\sum_{j=1}^{q}e_j\le \delta D_B+E_0
\]

with \(\delta\) below the amplification margin, or an entropy-amortized analogue.
KKL's exact translation estimate has a term \(6N\), so relative domination by
degeneration is a source-validated mechanism; absolute \(O(1)\) summability is not the
only admissible route.

At a neutral interface, \(A_m=\ell_mK_F\) is a per-tile scale, not the total
corridor scale. With \(r_m=\mathfrak q_{m+1}\) tiles, the corrected target is
\[
\frac{Q_{\rm orb}}{r_m}\asymp A_m,
\qquad
Q_{\rm orb}\asymp r_mA_m\asymp K_F.
\]
The DL25 peripheral loss aggregates as \(O(r_m\sqrt{A_m})\), hence is
\(O(A_m^{-1/2})\) relative to \(Q_{\rm orb}\). This comparison requires an actual
common curve family with controlled distortion, multiplicity, and parallel
orientation; projecting access labels is insufficient.

`corridor_network_calibration.md`, Lemma 11.1, is the special bounded-congestion case
of the replication estimate. These realization and comparison hypotheses, not the
absorption algebra, are the open interface theorem.

For an entropy block, a qualitative claim that entropy “pays” error is not sufficient.
If
\[
v_{j+1}\le e^{-\epsilon_j}v_j+\eta_j,
\qquad
E_B=\sum_j\epsilon_j,
\]
the required charge is the discounted sum
\[
\sum_j
e^{-\sum_{k>j}\epsilon_k}\eta_j
\le
\theta(1-e^{-E_B})v_0+C,
\qquad \theta<1.
\]
Only a bound of this form, or a proved telescoping equivalent, yields a uniform
contraction when \(E_B\ge\eta_0\).

### `M4` Entropy/sectorial dichotomy

Prove that every block either has accumulated positive core entropy
\(E(B)\ge\eta_0\), allowing a uniform Value contraction, or its degeneration is entirely
captured by the pseudo-Siegel/virtual regularization.

For a raw \((n,p)\)-translation marking, the label density per translation step is
exactly \(2p\). Thus increasing \(n\) cannot absorb unbounded \(p\). The dichotomy must
identify large translation density with a valid neutral/sectorial chart or construct a
different acceleration; that identification is not supplied by the arithmetic identity
alone.

### `M5` Backward transport

Combine Thin--Thick, Wave, Wanderers, quasi-additivity, and covering estimates to
transport residual bad geometry to \(p(n)\). The output must either satisfy the
backward cone inequality (5.1), so that one of Lemmas 5.1--5.3 applies, or satisfy a
forward upper comparison and the strict contraction hypothesis of Lemma 5.4. The same
calibrated scalar potential \(L\) must be valid on both sides.

### `M6` Coercivity

Show that a bound on all regularized \(L_n\) coercively controls the geometric
response-density coordinate \(\mathscr R_n\). Together with the declared uniform side
constraints on \(\rho_n,\kappa_n/r_{B,n},{\cal P}_n\) and the controlled hull geometry,
this must imply the required precompactness of normalized renormalizations, while raw
\(r_{B,n}\), counter values, and stack depth may remain unbounded. Proposition 6.1 of
`virtual_language_memory.md` shows that unbounded discrete side data are not
precompact merely because the geometric coordinate is bounded. The theorem must
prove that these data are forgotten after block closure, bounded, or continuously
compactified in a cylinder/end topology. Since \(\mathscr R_n\) intentionally ignores
root-annulus degeneration at large satellites, this implication is nontrivial and
cannot be borrowed from ordinary ql modulus compactness.

### `M7` Parameter rigidity

Prove uniform phase--parameter transfer and bounded puzzle Teichmüller diameter, or a
replacement rigidity theorem, for the marked towers. The endpoint must provide
connected relative parameter neighborhoods forming a basis at the parameter, with
diameters tending to zero (or a theorem deriving that basis from triviality of the
fiber under precisely stated hypotheses). Diameter shrinkage of an arbitrary nested
sequence alone does not imply local connectivity. KKL26 explicitly shows why beau
bounds alone are not the final step.

## 9. Adversarial checks

### Rapid satellite growth

Take relative periods \(s_j\to\infty\) arbitrarily fast. `WC-A` must not be invoked on
the root annulus. All dependence on \(s_j\) must be absorbed by \(B_j\), the sectorial
chart, the accelerated translation corridors, and the stopping time.

### Alternating neutral and primitive blocks

For a sequence \(N,P,N,P,\ldots\), each interface incurs a chart-change error. `M3`
must bound the whole block error, not merely each interface.

### Vanishing positive entropy

If \(\log\rho_j\to0\), no fixed one-step contraction is available. The entropy clock
must wait until \(\sum\log\rho_j\ge\eta_0\), while `M3` prevents the waiting error from
overwhelming the gain.

### Long partial-return chains

If a Wave argument uses \(q_j\) first returns, the marking must contain the critical
orbit through the final branch. A claim of “partial invariance” without this audit does
not satisfy `M1` or `M5`.

## 10. Present verdict

Theorem 2.1 and Proposition 3.1 are proved. Lemma 7.1 is proved. The source-locked
special cases of the width calculus remain available in their original domains.

MBTT is not proved: `M1`--`M7` contain results not present in the cited literature.
In particular, no published theorem currently constructs accelerated translation
corridors for arbitrary virtual hulls, supplies `WC-V`, controls mixed-chart error, or
proves marked-tower rigidity. These are the precise replacement obligations; concealing
them inside a single undefined \(D(H)\) would be circular.

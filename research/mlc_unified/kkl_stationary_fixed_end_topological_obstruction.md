# KKL stationary fixed-end route: topological-end obstruction

## 1. Status and result

This note cross-examines the proposed use of KKL's
immersion-decomposition theorem at the stationary critical-end
transition.  The theorem is useful, but its word **end** has a
specific topological meaning which is strictly coarser than a KKL
marked access.

The unconditional conclusion is:

\[
\boxed{
\begin{minipage}{0.88\linewidth}
KKL's fixed-end immersion-decomposition theorem is typed by
Freudenthal ends of finite-topology surfaces.  The objects \(BL_0\)
and \(L_0^h\) in the stationary Wave argument are marked ideal
intervals/accesses, not, without a separately constructed
localization, Freudenthal ends.  The locked source constructs no
access-splitting localization and proves no proper-degree-one
Freudenthal end representing the selected \(BL_0\) access.  Hence the
fixed-end theorem cannot presently be instantiated from that access.

There is a sharper conditional obstruction.  If the actual physical
pulled carrier \(T^h\) is proved compact, connected, and full, and if
the associated immersion has the required boundary compatibility at
the selected \(L_0^h\) occurrence, then the tree complement has one
inner end, that end is nonproper, and any fixed-end exit term based at
the only other end is vertical.  Those two physical-carrier premises
are not proved by the locked clauses audited here and remain explicit
hypotheses.
\end{minipage}}
\tag{1.1}
\]

The first paragraph is a proved source-type obstruction.  The
two-end/vertical refinement is conditional.  Neither is a
counterexample to the intended stationary estimate or to KKL's
immersion-decomposition theorem.  It also
does not refute an access-localized replacement theorem which has not
yet been proved.

No global obligation is promoted.  The native stationary repair,
VAAPC-I, UPTCR, and MLC remain open.

## 2. Locked sources and type distinction

The locked KKL master source is

```text
.tmp_wave_audit/waves-with-Misha.tex
SHA-256 AD4C774806D9902AA54FA31C56AD6146D8034946F19CC5E9CEC3C51A3F94FDD5
```

The relevant clauses are:

- lines 439--444: \(U^0,U^1\) are conformal disks and the filled sets
  are compact, connected, and full;
- lines 458--461: the finite Kahn pullback tower and the associated
  immersions \(I_h\);
- line 524: \(f^{-1}(T)\) is again an abstract tree;
- lines 1225--1226: the covering and immersion on tree complements;
- line 1241: the immersion is injective on a neighborhood of the
  filled set;
- lines 1355--1358: pointwise breaking and finite unbreakability;
- lines 1442--1444: \(U'\setminus T'\) has exactly the two ideal
  boundary components used in the vertical family;
- lines 1547--1548: \(N=b+3\) and the nested stationary Waves;
- lines 1597--1603: the pulled continua \(L_0^h\), the disjointness
  from \(T\), and the disputed two-portion assertion;
- lines 1707--1709: \(T^h=f^{-h}(T)\) and the associated inclusion
  \(I_h:U^h\setminus T^h\to U^0\setminus T\); and
- lines 1844--1875: KKL's finer ideal boundary, intervals, marked
  paths, and Waves.

The imported immersion theorem is in

```text
.tmp_wave_audit/not-all-good2.tex
SHA-256 B5D40812E40D2E44037A8FC249DB687211CD67275E66EFFF8E7F29BC7CEDFB01
```

at lines 514--545.

Its topological vocabulary comes from the locked KL06 WAD source

```text
.tmp_kl06_source/wad.tex
SHA-256 B5DF40A5D33B6B590B430D47693514088AF6FC287BAA5D87B4D11015B990E580
```

where:

- lines 11--20 define finite topology;
- lines 35--45 define the Freudenthal end set \(\mathcal E(S)\) and
  the endpoints of a proper path;
- lines 300--311 define properness of a holomorphic map at one such
  end; and
- lines 343--353 again use subsets of \(\mathcal E(S)\), not marked
  subintervals of one end.

The distinction is therefore literal:

\[
\begin{array}{c|c}
\text{KL06 / `thm:immer-decomp'}&
\text{KKL Wave marking}\\ \hline
\text{Freudenthal end }e\in\mathcal E(V)&
\text{ideal interval or access }J\subset\partial_I V\\
\text{one point per deleted complementary component}&
\text{many cyclically ordered intervals on one ideal component}.
\end{array}
\tag{2.1}
\]

In particular, \(BL_0\) is a marked multi-interval on an ideal
boundary.  The cited source does **not** prove that \(BL_0\) defines
a Freudenthal end separate from the remote intervals or from the
access represented by \(L_0^h\).  Under the additional physical-carrier
hypothesis \(\mathrm{TWO}_h\) below, all of these tree-side accesses
refine the same inner Freudenthal end.

## 3. Conditional two-end topology of a pulled tree complement

Write

\[
 V_h=U^h\setminus T^h,\qquad h\ge0.
\tag{3.1}
\]

### Hypothesis \(\mathrm{TWO}_h\)

Assume that the **actual physical** pulled carrier \(T^h\), not merely
its finite combinatorial quotient, is a compact connected full subset
of the conformal disk \(U^h\).

### Lemma 3.1 (two-end topology under \(\mathrm{TWO}_h\))

Under \(\mathrm{TWO}_h\), \(V_h\) has exactly two
Freudenthal ends:

\[
 \mathcal E(V_h)=\{e_{\mathrm{out}}^h,e_{\mathrm{in}}^h\}.
\tag{3.2}
\]

The outer end is represented by escape to \(\partial U^h\), and the
inner end is represented by approach to \(T^h\).  Every KKL ideal
interval belonging to a side of \(T^h\), including every lift of
\(BL_0\) and every access to \(L_0^h\), lies over
\(e_{\mathrm{in}}^h\).

#### Proof

Kahn's pullback construction gives a conformal disk \(U^h\) at every
finite level.  In the locked Kahn source
`.tmp_kl06_source/psiql2.tex`, lines 372--392 prove at one pullback
that the new domain is a disk, and lines 410--416 iterate the
construction.

By \(\mathrm{TWO}_h\), \(T^h\) is a compact connected full subset of
that disk.  A disk minus a compact connected full subset has one end approaching
the deleted continuum and one end approaching the boundary of the
disk.  One way to see this without using prime ends is to choose
nested connected neighborhoods

\[
 N_k^{\mathrm{in}}\supset T^h,\qquad
 N_k^{\mathrm{out}}\supset\partial U^h,
\tag{3.3}
\]

with disjoint closures in the annular complement.  For every
sufficiently large compact exhaustion set, the complement has
exactly the component represented by \(N_k^{\mathrm{in}}\setminus
T^h\) and the component represented by
\(N_k^{\mathrm{out}}\cap U^h\).  These give the two inverse systems
of unbounded components and hence the two Freudenthal ends.

KKL's one-step formulation at lines 1442--1444 calls these
exactly “the two components” of the ideal boundary of
\(U'\setminus T'\).  This is consistent with (3.2), but is not used
as a proof of \(\mathrm{TWO}_h\) for every physical iterated carrier.

All sides and accesses of one connected deleted tree are refinements
of its one inner end.  The ideal marking at KKL lines 1844--1875
records those refinements but does not split the underlying
Freudenthal end. \(\square\)

### Audit note 3.2

Lemma 3.1 is conditional because KKL line 524 supplies an abstract
one-step tree, not a complete proof that every non-locally-connected
physical \(T^h\) is compact, connected, and full in the sense required
above.  That carrier theorem must be proved before (3.2) is used.

Even under \(\mathrm{TWO}_h\), Lemma 3.1 does **not** identify all KKL ideal intervals with each
other.  They remain distinct marked accesses with cyclic order.
It says only that the older KL06 fixed-end theorem cannot distinguish
them, because its input is an element of \(\mathcal E(V_h)\).

## 4. The inner end is nonproper

Let

\[
 I_h:V_h\longrightarrow V_0=U^0\setminus T
\tag{4.1}
\]

be the associated immersion/inclusion.

### Hypothesis \(\mathrm{INC}_h\)

Assume there is a boundary point

\[
 x\in\partial T^h\cap(L_0^h\setminus T)
\tag{4.2a}
\]

and a sequence \(z_k\in V_h\) approaching \(x\) from the selected
pulled-tree access such that

\[
 I_h(z_k)\longrightarrow x
\quad\text{in }U^0.
\tag{4.2b}
\]

This is the precise boundary-compatibility statement needed from the
phrase “associated inclusion.”  Calling \(I_h\) an inclusion on the
open complementary surface does not, by itself, prove (4.2b) at an
omitted carrier point.

### Proposition 4.1 (conditional inner-end nonproperness)

Assume \(h\ge b\), \(\mathrm{TWO}_h\), and
\(\mathrm{INC}_h\).  Then

\[
 I_h\text{ is not proper at }e_{\mathrm{in}}^h.
\tag{4.2}
\]

#### Proof

Take \(x\) and \(z_k\) from \(\mathrm{INC}_h\).  Since \(x\notin T\) and
\(T\) is closed, there is a compact disk

\[
 K_x\Subset U^0\setminus T=V_0
\tag{4.4}
\]

containing \(x\) in its interior.

The sequence leaves every compact subset of \(V_h\), and by Lemma 3.1 it tends to
\(e_{\mathrm{in}}^h\).

Hypothesis \(\mathrm{INC}_h\) gives
\(I_h(z_k)\to x\).

In particular, \(I_h(z_k)\in K_x\) for all sufficiently large \(k\).
Thus a sequence tending to \(e_{\mathrm{in}}^h\) does not leave every
compact subset of \(V_0\).

KL06 `wad.tex` lines 300--306 define properness at an end precisely
by preservation of escape from compacta.  Equation (4.2b) violates
that definition, proving (4.2). \(\square\)

### Audit note 4.2

The point \(x\) is an interior point of the **target complement**
\(V_0\), even though it belongs to the deleted pulled tree \(T^h\)
in the source.  This is exactly why local properness at the original
\(BL_0\) access cannot be promoted to properness of the whole inner
Freudenthal end.

The proof does not use local connectivity once
\(\mathrm{TWO}_h\) and \(\mathrm{INC}_h\) have been supplied.  Those
two hypotheses are precisely where physical-carrier and boundary
naturality must be established; a finite ribbon tree is not a
substitute.

## 5. Consequence for the fixed-end WAD theorem

KKL `thm:immer-decomp` assumes a set

\[
 E'\subset\mathcal E(V_h)
\tag{5.1}
\]

on every member of which \(I_h\) is proper and degree one.  Put
\(E=I_h(E')\).

### Theorem 5.1 (conditional fixed-end alternative on the tree complement)

Let \(Y\) be a valid target WAD whose arcs have **both** Freudenthal
endpoints on the target inner end \(e_{\mathrm{in}}^0\), as happens
for the nonvertical stationary Wave family with both marked endpoints
on tree-side accesses.  Suppose that
\(\mathrm{TWO}_0\), \(\mathrm{TWO}_h\), \(\mathrm{INC}_h\), and
`thm:immer-decomp` are applicable to \(I_h:V_h\to V_0\) and \(Y\).
Then every paired exit arc in its witness connects
\(e_{\mathrm{out}}^h\) to \(e_{\mathrm{in}}^h\).  In particular, the
paired exit summand is vertical in the sense used at KKL lines
1442--1444.  No claim is made about additional terms allowed by the
inequality \(Y'\ge\sum_a v_a\beta'_a\).

If \(I_h\) has no proper degree-one outer end mapping to
\(e_{\mathrm{in}}^0\), then the theorem is not applicable to \(Y\)
at all.

#### Proof

Every target arc has both endpoints at \(e_{\mathrm{in}}^0\).
For `thm:immer-decomp` to apply, at least one endpoint of every arc
must belong to \(E\); hence \(e_{\mathrm{in}}^0\) must belong to

\[
 E=I_h(E').
\tag{5.2}
\]

Hence some \(e'\in E'\) must map to \(e_{\mathrm{in}}^0\).
Lemma 3.1 leaves only
\(e_{\mathrm{in}}^h\) and \(e_{\mathrm{out}}^h\) as candidates.
Proposition 4.1 excludes \(e_{\mathrm{in}}^h\), because every member
of \(E'\) must be proper.  Therefore

\[
 e'=e_{\mathrm{out}}^h.
\tag{5.3}
\]

If the outer end is not a proper degree-one preimage of the target
inner end, (5.2) is impossible and the theorem cannot be applied.

Assume it is such a preimage.  The second alternative in
`thm:immer-decomp`, lines 527--530, says that every exit arc has one
endpoint in \(E'\) and the other outside \(E'\).  The first endpoint
is \(e_{\mathrm{out}}^h\).  The only other source end is
\(e_{\mathrm{in}}^h\), so the exit arc joins the two distinct
boundary components.  This is exactly the vertical topology in KKL
line 1442. \(\square\)

### Corollary 5.2 (conditional failure to produce a nonvertical line-1603 pair)

Assume \(\mathrm{TWO}_0\), \(\mathrm{TWO}_h\),
\(\mathrm{INC}_h\), and the target-WAD/applicability hypotheses of
Theorem 5.1.  Then the fixed-end theorem on
\(V_h=U^h\setminus T^h\) cannot construct the two nonvertical
portions asserted at KKL line 1603.

#### Proof

It cannot start from the \(BL_0\) access as a separate proper end,
because that access belongs to the nonproper end
\(e_{\mathrm{in}}^h\).  Starting from the outer end either is
impossible or puts every exit term in the vertical class by Theorem
5.1.  A full term in the theorem maps one complete source arc to the
complete target arc; it is not a pair of proper portions meeting the
same internal \(L_0^h\) occurrence. \(\square\)

## 6. Effect on the six-clause certificate

The proposed marked fixed-end pair used the clauses

\[
 C_h^-\wedge X_h^-\wedge C_h^+\wedge X_h^+
 \wedge P_h\wedge M_h.
\tag{6.1}
\]

If \(C_h^\pm\) is interpreted as a certificate for a **topological
source end** in the hypothesis of `thm:immer-decomp`, then the
locked source does not prove it.  Under
\(\mathrm{TWO}_h\wedge\mathrm{INC}_h\), the critical-side instance
fails:

\[
 C_h^- =0
\quad\text{for a start at the inner }BL_0\text{ access}.
\tag{6.2}
\]

If \(C_h^\pm\) is instead interpreted as local properness on a marked
ideal interval or one prime-end access, then it is not the hypothesis
of the imported theorem.  Substituting that finer object silently
changes the theorem.

Thus the obstruction category is:

```text
TYPE_MISMATCH:
    Freudenthal end  !=  marked ideal interval/access

CONDITIONAL FIRST_FAILURE (TWO_h and INC_h):
    the unique inner Freudenthal end is nonproper for I_h

CONDITIONAL SURVIVING IMPORTED OUTPUT
(TWO_0, TWO_h, INC_h, and Theorem 5.1 applicability):
    any fixed-end exit term based at the outer end is vertical
```

Unconditionally, the source failure is the earlier type mismatch:
line 1600 does not choose or construct an eligible topological end.
Conditionally on \(\mathrm{TWO}_h\wedge\mathrm{INC}_h\), the sharper
statement holds: at the desired inner end there is no eligible
topological end to choose.

## 7. Required replacement invariant

The correct replacement cannot be a finite list of Freudenthal ends.
It must retain an access-localized object

\[
 \mathfrak e
 =
 (e_{\mathrm{in}}^h,J,a,\mathcal C,\omega,\tau),
\tag{7.1}
\]

where:

- \(J\) is the actual KKL ideal interval;
- \(a\) is the prime-end access and cyclic slot inside the inner end;
- \(\mathcal C\) is a univalent collar germ at that access;
- \(\omega\) is the occurrence/window and relative homotopy record;
- \(\tau\) is the first-exit trace from the collar, including the
  landing end or nonlanding cluster; and
- the record states whether the complete path survives the fine and
  coarse KKL filters.

The missing analytic replacement is an **access-localized immersion
decomposition theorem**:

> Starting from a specified univalent marked-access collar, lift a
> realizing target foliation until its first exit; partition the
> result measurably into complete, vertical, small-Julia incidence,
> and residual access-exit WADs; preserve coefficient weight; and
> prove that every residual is either charged or yields a terminal
> response with multiplicity uniform in the stationary block.

Unlike `thm:immer-decomp`, this new theorem must allow local
properness at one access of a globally nonproper end.  It must also
record the exit trace \(\tau\), because two access-local lifts can
merge, land at different obstacles, or be discarded by the coarse
filter.

## 8. Adversarial audit

1. **Accesses were not collapsed geometrically.**  They remain
   distinct in KKL's ideal marking; only the imported theorem's input
   was typed at the coarser Freudenthal-end level.
2. **One bad access is enough, conditionally on common-end
   identification.**  Properness at a Freudenthal end
   quantifies over every sequence tending to that end.  The sequence
   in Proposition 4.1 therefore disproves properness of the whole
   inner end.
3. **A local univalent collar does not repair end properness.**  It
   proves local access naturality only.  Other accesses of the same
   end still contain the nonproper sequence.
4. **The outer-end case was not discarded.**  Under the two-end
   hypotheses it was classified.
   Its paired exit terms have vertical topology and are candidates
   for the previously stated conditional vertical charge.  The
   proper-packet, fine/coarse-filter, covering, and
   transverse-measure hypotheses of that charge remain separately
   required.
5. **A full fixed-end lift is not a two-occurrence binder.**  It maps
   one complete source arc to one complete target arc.
6. **No width follows from topology alone.**  The vertical numerical
   charge still needs the proper packet hypotheses already stated in
   `kkl_stationary_route_exit_conductance_reduction.md`.
7. **No source theorem was declared false.**  The obstruction is a
   failed instantiation of its hypotheses.
8. **No global claim moved.**  The stationary repair and all global
   MLC gates remain open.

## 9. Exact next task

The next constructive pass should not attempt to prove
\(C_h^\pm\) merely by relabeling marked accesses as topological ends
of the unlocalized tree complement.
It should:

1. choose the actual \(BL_0\) prime-end access and its univalent
   collar at each proof-used horizon;
2. construct the access-local maximal-lift foliation;
3. prove Borel first-exit and unique ideal landing, or retain the
   nonlanding class explicitly;
4. identify every exit as vertical, exact small-Julia incidence,
   bounded Wave output, or a marked \(BL_0\) residual;
5. prove bounded multiplicity after occurrence and sheet tags are
   retained; and
6. attack the remaining \(BL_0\) residual without citing KKL's
   proposition whose proof contains line 1603.

That access-local theorem, rather than a second application of the
Freudenthal fixed-end theorem, is the immediate analytic gate.

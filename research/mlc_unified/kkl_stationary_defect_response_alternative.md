# KKL stationary quantitative defect-response alternative

## 1. Purpose and status

The global filled-set collar charge

\[
 \mathfrak C_{\le b+2}^{\rm comp}(F)
 \le C_b\bigl(V(F)+1\bigr)
\]

does not follow from the qualitative pseudo-polynomial-like and
embedded-neighborhood hypotheses.  The exact disk family in
`kkl_stationary_uniform_collar_charge_attack.md` proves that source
derivability fails even when every immersion is globally embedded.

This note gives a weaker replacement.  It is not necessary to charge
every unresolved stationary route numerically.  A residual family may
instead be allowed to trigger the terminal-Wave alternative already
present in KKL.

The note proves the algebraic implication from this
**Quantitative Stationary Defect-Response Alternative** to the
stationary short-or-terminal conclusion.  It does not construct the
analytic response family.  Consequently the native stationary repair,
VAAPC-I, UPTCR, and MLC remain open.

The locked source is

```text
.tmp_wave_audit/waves-with-Misha.tex
SHA-256 AD4C774806D9902AA54FA31C56AD6146D8034946F19CC5E9CEC3C51A3F94FDD5
```

The proof uses:

- KKL lines 1151--1156, defining terminal Waves;
- lines 1355--1368, defining breakability and `small breaking`;
- lines 1370--1392, constructing the disjoint auxiliary family
  \(B=A^{N\text{-br}}\cup A^{\rm sh}\);
- lines 1429--1492, the three-type breaking response;
- lines 1547--1589, the stationary critical-end telescoping; and
- lines 1627--1635, assembly of the Wave types.

## 2. Frozen notation

Put

\[
 V(F)=\mathcal W(\mathcal U\setminus\mathcal T),
 \qquad
 R(F)=\mathcal W(\mathcal RF),
 \qquad
 N=b+3.
\tag{2.1}
\]

All partitions below are taken in the native transverse width measure
of the proof-used KKL lamination.  For arbitrary curve-family unions,
only modulus subadditivity is used.

For a \(k\)-controllable Wave \(A\), define

\[
 B_A=A^{N\text{-br}}\cup A^{\rm sh}.
\tag{2.2}
\]

KKL source lines 1375--1387 give the two facts used later:

\[
 B_A^{N\text{-nbr}}\subset A^{\rm sh},
\tag{2.3}
\]

and \(B_A^{N\text{-nbr}}\) is short, hence
\(12b\)-controllable.

## 3. Charged and responsive stationary defects

At the final stationary level, the defect family need not be assigned
one uniform numerical estimate.  Partition it into:

\[
 D=D_{\rm ch}\sqcup D_{\rm resp}
\quad\text{modulo width zero}.
\tag{3.1}
\]

The charged family contains defects for which an actual extremal-width
estimate is available.  The responsive family contains the remaining
marked failures: for example, an inverse-branch exit which is not
controlled by a compatible collar but may produce the two-Wave
configuration in KKL's breaking argument.

After assembling all Wave types, write
\(\mathscr E_A\subset A\) for the responsive residual descended to the
original Wave.  All occurrence, window, access, sheet, and
first-failure labels are retained.  The required charged inequality is

\[
\boxed{
 \mathcal W(A)
 \le
 \mathcal W(B_A)
 +a_bV(F)+c_bR(F)+C_b(k+1)
 +\mathcal W(\mathscr E_A).
}
\tag{3.2}
\]

Equation (3.2) is the disjoint estimate from
`kkl_stationary_quantitative_defect_repair.md`, with the uncharged
residual retained instead of discarded.

### QSDRA

The **Quantitative Stationary Defect-Response Alternative** consists
of (3.2) and the following response clause:

\[
\begin{split}
 \forall\,0<\epsilon<1\quad
 \exists\,\delta_{b,\epsilon}>0,\ \eta_{b,\epsilon}<\infty
 \quad\forall A:\qquad
 \mathcal W(\mathscr E_A)>\epsilon\mathcal W(A)\\
 \Longrightarrow
 A\text{ is }(\delta_{b,\epsilon},\eta_{b,\epsilon})
 \text{-terminal}.
\end{split}
\tag{3.3}
\]

The terminal controllability bound must be independent of the input
controllability \(k\), satellite period, rotation denominator, and
individual block.  Dependence on the fixed parabolic bound and the
chosen response fraction is allowed.

QSDRA is **formally weaker** than QSDB: QSDB implies it by taking
\(\mathscr E_A=\varnothing\).  A route-exit conductance estimate implies
it only after one proves that route exits exhaust the residual and
that every non-exit defect is already charged or analytically
realized.  The converse has not been separated on an actual KKL block,
so no strict logical separation is claimed.  QSDRA is designed to
allow the route-exit conductance to be large when that large family
forces terminality.

## 4. Main conditional theorem

### Theorem 4.1 (QSDRA suffices)

Assume:

1. QSDRA, including its native transverse-measure typing;
2. KKL Proposition `small breaking` in its source-stated scope; and
3. either KKL's native HTND absolute scale or the explicit condition
   \[
    \mathcal W(A)\ge
    C_{b,k,\lambda}\bigl(R(F)+1\bigr).
   \tag{4.1}
   \]

Then, for every \(0<\lambda<1\), every sufficiently wide
\(k\)-controllable Wave \(A\) is either strictly \(\lambda\)-short or
\((\delta,\eta)\)-terminal, where
\[
 \delta=\delta_{b,\lambda}>0,\qquad
 \eta=\eta_{b,\lambda}<\infty
\]
are independent of \(k\) and of the individual block.  The response
hypothesis (3.3) allows \(\eta\) to depend on \(\epsilon\), hence on
\(\lambda\); the theorem does not erase that dependence.

Consequently QSDRA is sufficient for every fixed-\(\lambda\)
stationary short-or-terminal call.  It recovers KKL Proposition
`mostly short` with a single source-universal controllability constant
only under either of these additional hypotheses:

1. (3.3) holds with one \(\eta_b\) for all \(\epsilon\); or
2. only the finite, predetermined \(\lambda\)-list in the proof of KKL
   Lemma `terminal` is needed, in which case the maximum of the
   finitely many \(\eta_{b,\lambda}\) is universal for that proof.

#### Proof

Choose

\[
 \lambda<\lambda_3<1.
\tag{4.2}
\]

Apply KKL `small breaking` with

\[
 n=N,\qquad k_0=12b,\qquad\text{parameter }\lambda_3.
\tag{4.3}
\]

Let \(\delta_3>0\) and \(\eta_3\) be the resulting constants.  The
source states that \(\delta_3\) is independent of the eventual
controllability parameter \(k\), and \(k_0\) is fixed by \(b\).

Choose

\[
 \max\left\{
  \frac{\lambda}{\lambda_3},
  \frac1{1+\delta_3}
 \right\}
 <\theta<1
\tag{4.4}
\]

and put

\[
 \epsilon=\frac{1-\theta}{3}.
\tag{4.5}
\]

Define the admissible vertical terminal constant

\[
 \delta_v=
 \begin{cases}
  \min\{1/2,\epsilon/a_b\},&a_b>0,\\
  1/2,&a_b=0.
 \end{cases}
\tag{4.6}
\]

There are three preliminary cases.

First, if

\[
 V(F)>\delta_v\mathcal W(A),
\tag{4.7}
\]

then \(A\) is terminal through KKL's vertical alternative.

Second, suppose (4.7) fails but

\[
 \mathcal W(\mathscr E_A)>
 \epsilon\mathcal W(A).
\tag{4.8}
\]

Then QSDRA (3.3) makes \(A\) terminal.

Third, suppose neither (4.7) nor (4.8) holds.  Then

\[
 a_bV(F)\le\epsilon\mathcal W(A),
\qquad
 \mathcal W(\mathscr E_A)\le\epsilon\mathcal W(A).
\tag{4.9}
\]

Use the HTND or absolute-scale hypothesis to enlarge the scoped
threshold until

\[
 c_bR(F)+C_b(k+1)
 \le\epsilon\mathcal W(A).
\tag{4.10}
\]

Substituting (4.9)--(4.10) in (3.2) gives

\[
 \mathcal W(B_A)
 \ge(1-3\epsilon)\mathcal W(A)
 =\theta\mathcal W(A).
\tag{4.11}
\]

By (2.3), \(B_A^{N\text{-nbr}}\) is \(12b\)-controllable.  Increase
the original threshold once more so that (4.11) makes \(B_A\) wide
enough for `small breaking`.  That proposition gives two cases.

If \(B_A\) is
\((\delta_3,\eta_3)\)-terminal, its vertical alternative gives

\[
 V(F)>
 \delta_3\mathcal W(B_A)
 \ge\delta_3\theta\mathcal W(A).
\tag{4.12}
\]

Its wider-Wave alternative supplies an \(\eta_3\)-controllable Wave
\(C\) satisfying

\[
 \mathcal W(C)>
 (1+\delta_3)\mathcal W(B_A)
 \ge(1+\delta_3)\theta\mathcal W(A).
\tag{4.13}
\]

By (4.4), both alternatives make \(A\)
\((\delta_A,\eta_3)\)-terminal, where

\[
 \delta_A=
 \min\{
  \delta_3\theta,\,
  (1+\delta_3)\theta-1
 \}>0.
\tag{4.14}
\]

If \(B_A\) is \((N,\lambda_3)\)-unbreakable, then (2.3) gives

\[
\begin{aligned}
 \mathcal W(A^{\rm sh})
 &\ge\mathcal W(B_A^{N\text{-nbr}})\\
 &\ge\lambda_3\mathcal W(B_A)\\
 &\ge\lambda_3\theta\mathcal W(A)\\
 &>\lambda\mathcal W(A).
\end{aligned}
\tag{4.15}
\]

Thus \(A\) is strictly \(\lambda\)-short.

The vertical split, response split, and the two `small breaking`
outputs exhaust all cases.  A single pair of terminal constants valid
in every terminal branch is

\[
 \delta=
 \min\{\delta_v,\delta_{b,\epsilon},\delta_A\}>0,
 \qquad
 \eta=
 \max\{\eta_{b,\epsilon},\eta_3\}<\infty .
\tag{4.16}
\]

These constants are independent of \(k\) and of the individual block;
their permitted dependence on \(b,\lambda\) is exactly the dependence
recorded above. \(\square\)

## 5. Exact source-facing response certificate

The exact survivor reduction in
`kkl_stationary_route_exit_survivor_reduction.md` first partitions a
single-valued target-leaf exit family as

\[
 \mathscr E_A
 =
 \mathscr E_A^{\rm br}
 \sqcup
 \mathscr E_A^{\rm sh}
 \sqcup
 \mathscr E_A^{\rm surv},
\tag{5.0}
\]

where

\[
\begin{aligned}
 \mathscr E_A^{\rm br}&\subset A^{N\text{-br}},\\
 \mathscr E_A^{\rm sh}
   &\subset A^{N\text{-nbr}}\cap A^{\rm sh},\\
 \mathscr E_A^{\rm surv}
   &\subset A^{N\text{-nbr}}\setminus A^{\rm sh}.
\end{aligned}
\tag{5.0a}
\]

The first two classes must be relabelled into
\(B_A=A^{N\text{-br}}\cup A^{\rm sh}\) before widths are summed.
Only \(\mathscr E_A^{\rm surv}\) is a genuinely new responsive
residual.

The response clause (3.3) is not a numerical assumption in disguise.
KKL lines 1429--1492 apply directly only to the breakable subclass
\(\mathscr E_A^{\rm br}\), which is already absorbed into \(B_A\).
They do not prove a response for the survivor subclass merely because
its selected marked route failed.  A new auxiliary Wave built from
survivor traces might itself be breakable, but constructing it and
transporting its terminal response back to \(A\) is a separate
analytic theorem.

For the measurable breakable subclass, the required
**route-exit-to-breaking certificate** must construct, occurrence by
occurrence:

1. an actual restriction of the ambient leaf in the proof-used pulled
   surface;
2. a named failure stage \(r\), the ambient stage Wave, and proof that
   the responsive leaf lies in that Wave's one-step breakable part;
3. the KKL priority partition---vertical first, then the two-endpoint
   case, then the remaining outward case---rather than an unsupported
   assertion that the three geometric descriptions are intrinsically
   disjoint;
4. the applicable KKL alternative:
   - a path joining the two boundary components;
   - one retained Wave over the pulled crest; or
   - two retained Waves over the two pulled endpoints;
5. the fine-marking and coarse-filter witnesses for every retained
   restriction;
6. the covering images with their multiplicities;
7. a transverse-measurable, pairwise-disjoint partition by alternative;
8. end-properness on the actual ambient crest used at stage \(r\);
9. descent of each selected exit to an actual first-break family
   \(E_r\subset A^{r\text{-br}}\), with multiplicity uniformly bounded
   independently of period and block;
10. alignment of horizon, stage, and crest labels;
11. preservation of a fixed width fraction after splitting among the
    finitely many horizons and alternatives;
12. inheritance of the controllability hypothesis needed by KKL
    Lemmas `pushing controllable` and `wave`; and
13. quantitative width transport from the selected restrictions back
    to the original Wave \(A\).

If the first priority class has a fixed fraction of \(A\), KKL lines
1442--1448 give vertical terminality.  Lines 1454--1459 give a
factor-two estimate for the pulled two-endpoint Wave, but terminality
still requires the pushforward, its additive loss, inherited
controllability, and assembly with the retained pieces.  In the
applicable outward class of KKL's full one-step partition, lines
1463--1488 give a nonlinear estimate for the auxiliary pulled Wave
\(B\):

\[
 \mathcal W(B)
 \ge
 \left(
  1-2\delta_{\rm sm}+
  \frac{(\epsilon-2\delta_{\rm sm})^2}{6N_{\rm imp}}
 \right)\mathcal W(A)
\tag{5.1}
\]

after the source's auxiliary families are assembled, where
\[
 N_{\rm imp}\le 4b(2b+2)
\]
is the number of improper intervals in source line 1464.  It is not
the horizon \(N=b+3\).  Equation (5.1) is not yet an estimate for the
final pushed Wave.  Only after the Wave lemma, controllability
transport, and absorption of their additive loss at the stated
absolute scale may one infer a smaller strict gain for an actual
controllable pushed Wave.

Thus (5.1) alone does not prove (3.3).  All thirteen clauses above
are required even to place the **breakable subclass** into the
source-native one-step partition with its quantitative data; after
that placement the subclass is relabelled into
\(A^{N\text{-br}}\).  An iterated route exit may occur while another
restriction still makes \(F_*\alpha\) a single path, so “route exit”
is not synonymous with “KKL break.”

The actual missing response theorem is geometric and measurable:

\[
 \boxed{
 \mathcal W(\mathscr E_A^{\rm surv})
 >\epsilon\mathcal W(A)
 \Longrightarrow
 A\text{ is }
 (\delta_{b,\epsilon},\eta_{b,\epsilon})\text{-terminal}.
}
\tag{5.2}
\]

Alternatively, one may prove
\(\mathscr E_A^{\rm surv}=\varnothing\) or charge its width
numerically.  Coarse interval adjacency and same-pulled-interval
transitions prove none of these alternatives.  A target trace which
touches and reenters the embedded collar, changes global immersion
sheet, or loses one named portion in the coarse subordinate filter may
have no certified full restriction of the required type.

## 6. Relation to the route-exit conductance

Let \(\mathfrak E_h(F)\) denote the width of the fully marked,
measurably selected first-failure family at horizon \(h\).

There are now two sufficient analytic routes:

1. **numerical route**
   \[
    \sum_{h=1}^{b+2}\mathfrak E_h(F)
    \le C_b(V(F)+1),
   \tag{6.1}
   \]
   which places every exit in \(D_{\rm ch}\); or
2. **response route**, which partitions the exit family into a charged
   part, the two \(B_A\)-absorbed classes in (5.0a), and the survivor
   part satisfying (5.2).

The response route is formally weaker than imposing (6.1).  The total
route-exit conductance may be large, provided every large uncharged
subfamily is independently proved to force terminality.  Strict
separation on the native KKL block class remains unproved.

## 7. Adversarial audit

1. No terminal subwave is declared to make its ambient Wave terminal
   without the quantitative factors (4.12)--(4.14).
2. KKL shortness is strict; (4.4) gives
   \(\lambda_3\theta>\lambda\).
3. The terminal constant in (4.6) lies in \((0,1)\).
4. The fixed additive charge is absorbed only under an absolute-scale
   hypothesis.
5. General modulus is not called an additive measure.
6. The residual family is retained explicitly in (3.2).
7. A large residual does not become terminal by definition; (3.3) is
   a separate open analytic response theorem.
8. The finite list of three breaking types applies only to an ambient
   breakable family; it is not a response theorem for an
   ambient-singleton survivor.
9. No collar crossing is asserted for touch/reentry or sheet-switch
   failures.
10. No numerical diagnostic can promote (3.3) or (5.2).

## 8. Exact next obligation

Freeze the actual marked first-failure occurrence space, perform the
breakable/short/survivor relabelling before summing widths, and prove
one of:

1. the numerical route-exit estimate (6.1); or
2. a measurable charged/response partition satisfying (3.2)--(3.3),
   by proving the survivor response theorem (5.2).

If both fail, record the first route exit whose source lift:

- has no vertical crossing;
- produces no one- or two-Wave retained restriction;
- survives the ambient singleton \(F_*\)-image;
- and cannot be charged to \(R(F)\) or a bounded family.

That certificate is the first genuine unhandled stationary defect and
must be retained as a new response-state coordinate.

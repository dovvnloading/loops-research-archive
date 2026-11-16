# Four-push crest transport on the near-minus-two real primitive-tip family

**Audit: 2026-11-16.** This is a six-period *whole-radius-bin interval certificate* plus a precisely delimited conditional analytic interpretation. **It does not establish an all-period uniform transport bound, its failure, or a decay rate.** No existing source file, native wave transfer, ledger or research index is changed.

## Scope and imported physical hypotheses

Use the distinguished leftmost near-\(-2\) real primitive branch of [PR #80](https://github.com/dovvnloading/loops-research-archive/pull/80): \(f_c(z)=z^2+c\), \(G_p=f_c^p\), \(x_j=f_c^j(0)\), \(x_{6p}=-x_{3p}>0\), with the strict orbit/cut order and the *central* degree-two proper component \(V_p\Subset U_p\), \(U_3=D(0,1/4)\), \(U_p=D(0,2^{-p})\) for \(4\le p\le8\). The global degree of \(G_p\) is \(2^p\), **not** the degree of the central restriction. PR #80 certifies local real roots, source cuts and the selected parent-wave gates for \(p=3,\ldots,8\), but its higher-period identification with the complete real Hubbard tree and actual locally connected slit-side prime ends is **conditional** on its physical-realization and KKL hypotheses. Those hypotheses, including the locally connected real/slit marking, genuine proper restrictions and conformal width, are imported here rather than proven by Python.

At \(p=3\) use the **actual PR #68/PR #78 Wave**: center \(d_3=-9/64\), radii \(3/256<r<1/64\), base \((I_9,I_0,I_1)\), zero-old-edge closed crest \(I_0\). The center and individual radii of that wave are *not* exactly the \(x_p\)-normalized ones below, despite having the same radial ratio. At \(p=4,\ldots,8\) use PR #80's **chosen, noncanonical** parent waves
\[
d_p=-\tfrac34x_p,\quad \frac{x_p}{16}<r<\frac{p-1}{8p}x_p.
\]
Their radial ratios are \(R_3=4/3\) and \(R_p=2(p-1)/p\) for \(p\ge4\); the parent width is \(W(S_p)=\log R_p/(2\pi)\) *when the analytic conformal-width hypotheses hold*. This is not a return-period-only invariant.

## The six certified collars and strongest published coefficients

Let \(s=r/x_p\) for \(p\ge4\). The new checker encloses **every radius in each open collar**, not sample radii, and reports these rational certified enclosures for the exact ratio \(w_p=W(S_{4,p}^\pm)/W(S_p)\):

| \(p\) | Strict chosen subcollar | Number of whole bins | \(c_p\le w_p\) | Certified upper bound on \(w_p\) |
|---:|---|---:|---:|---:|
| 3 | \(1/80<r<1/77\) | 512 | 0.5676 | 0.5684 |
| 4 | \(63/1000<s<667/10000\) | 512 | 0.5729 | 0.5733 |
| 5 | \(313/5000<s<663/10000\) | 512 | 0.4902 | 0.4904 |
| 6 | \(1/16<s<663/10000\) | 512 | 0.4620 | 0.4622 |
| 7 | \(1/16<s<663/10000\) | 512 | 0.4375 | 0.4376 |
| 8 | \(1/16<s<663/10000\) | 512 | 0.4213 | 0.4214 |

The displayed \(c_p\) is the **largest certified multiple of \(10^{-4}\)** below the exact lower envelope produced by this specified 512-bin rational procedure. It is **not** a global optimum among all possible collars, width functionals or descendants. The paired upper endpoints bound the *same specified collar integral*, not an optimal descendant. In particular the **finite-family** conditional consequence is \(w_p\ge4213/10000\) for all six \(p\in\{3,\dots,8\}\). The original strict \(p=3\) coefficient \(1/2\) from PR #78 is recovered and sharpened only for its fixed physical collar.

Each row has the same **two** selected depth-four marked descendants after *four distinct proper restrictions \(\iota^*\) and covering pushes \(G_{p*}\)*:

| Chosen genuine q-side subfamily (under KKL path interpretation) | Terminal source endpoints | Covering target base | Closed crest | Old real edge side |
|---|---|---|---|---|
| Upper | \(S_0,S_3\) | \(I_0,I_1,I_2,I_3\) | \(\overline{I_1\cup I_2}\) | \(I_1\), upper side of \(E_0=(x_{5p},x_{3p})\) |
| Lower | \(S_{17},S_0\) | \(I_7,I_8,I_9,I_0\) | \(\overline{I_8\cup I_9}\) | \(I_9\), lower side of **the same** physical edge \(E_0\) |

At \(p=3\), \(E_0=E_{20}=(x_{15},x_9)\) in the older notation. Two prime-end sides **are not two physical Hubbard-tree edges**. The original crest \(I_0\), and first-stage crests \(I_2,I_8\), carry no old edge; the fourth-stage selected closed crests do. No assertion is made about *every* cyclic word or every path at the third stage. In particular the other third-stage endpoint can pass a cut and is **not** given a constant source atom.

### Separate operators, four stages

The finite marking is reconstructed by applying \(G_p\) to real sample points strictly inside each source atom and separately computing which target-side block each source atom inhabits under inclusion:
\[
G_{p*}(S_s)=I_{s\bmod10},\qquad
\iota^*(I_i)=P_i,\quad
(P_0,\ldots,P_9)=
( [18,19,0,1,2],[3,4],[5],[6],[7,8,9],
[10],[11,12,13],[14],[15],[16,17]).
\]
The \(S_{19},S_0,S_1\) attachment is interior under \(\iota\); hence \(P_0\) is not fully proper. It is invalid to replace \(\iota^*\) by the covering function, to regard an attached access as a pointwise boundary image, or to assume \(F_*\overline I=\overline{F_*I}\).

The first restricted half-circles cover-push to crests \(I_2,I_8\). On the selected terminal q-side (after the intervening \(I_5\) and \(I_0\) crest stages), the new third-stage real meeting is in \((-x_p,-x_{4p})\), creating the **terminal source \(S_0\)**. The q-side meeting is in \((x_{5p},-\alpha_p)\), with upper/lower source sides \(S_3,S_{17}\). The upper terminal endpoints occupy *different* pullback blocks \(P_0,P_1\), the lower \(P_9,P_0\); each source/target shortest arc contains four atoms, not a KKL-deleted short path. The image of the terminal real meeting lies in \((x_{2p},x_{5p})\). Real endpoint cut assertions, whole-disk envelopes, angular monotonicity, the q-side gate and these finite endpoint-host predicates are machine-checked separately for each \(p\). Their interpretation as KKL *genuine* path subfamilies and conformal univalence uses the stated analytic/physical premises.

## Exact width and the nature of the arithmetic certificate

For each collar \(a_p<r<b_p\), the verifier isolates the **unique** \(u_p(r)\in(-1/8,1/4)\) solving
\[
\mathrm{Re}\,G_p\!\left(d_p+r(u+i\sqrt{1-u^2})\right)=0,\qquad
\theta_p(r)=\arccos u_p(r).
\]
A Taylor coefficient dominance check on the **entire largest closed disk** proves strict angular monotonicity and positive imaginary-half-plane preservation for every radius up to the selected upper endpoint. A 384-bit outward integer interval implementation uses the square-root-free recurrence
\[
X_0=d_p+ru,\ B_0=1,\ Y^2=r^2(1-u^2),\quad
X_{k+1}=X_k^2-Y^2 B_k^2+c,\quad B_{k+1}=2X_k B_k.
\]
The full interval for every radius bin, including *all* values of \(u\) it brackets, is propagated through the first imaginary meeting, \(G_p(iYB_p)\), its real return and the terminal real meeting. Thus this is not finite-radius sampling. All twelve/ \(4p\) physical iterate disk envelopes are outward bounded; the first three center selectors and second/third image half-plane signs are checked. The verifier recomputes the parameter-root signs and local derivative uniqueness and independently reconstructs \(G_{p*}\) and \(\iota^*\).

Under the imported KKL/prime-end/conformal assumptions, the specified conformally injected q-side leaves have variable angular height \(\theta_p(r)\); Cauchy–Schwarz with the extremizing density \(1/\theta_p(e^x)\) in \(x=\log r\) gives the **exact**, not quadrature-defined, identity
\[
W(S_{4,p}^+)=W(S_{4,p}^-)=\int_{a_p}^{b_p}\frac{dr}{r\theta_p(r)},\quad
w_p=\frac{2\pi}{\log R_p}\int_{a_p}^{b_p}\frac{dr}{r\theta_p(r)}.
\]
The arithmetic certificate bounds \(\theta\) using \(\arcsin(u)\ge u\) for \(u\ge0\), and \(|\arcsin u|\le(65/64)|u|\) for \(|u|\le1/8\); it proves the required rational \(\pi\) enclosure through Machin's identity and alternating arctan series and logarithms through a positive atanh series with explicit rational tail. Binwise lower/upper Riemann-*integral* enclosures yield the displayed **two-sided strict rational bounds**. Nothing relies on floating-point quadrature, decimal roots, or test-point interpolation.

**Critical edge case:** at \(p=6,7,8\), part of the selected angular root is **negative**, so \(\theta_p>\pi/2\) there. The \(p=3\) shortcut \(u>0\Rightarrow\theta<\pi/2\) cannot be transplanted unchanged. Both signs are handled by the interval arcsin estimates. The parent-wave radius normalization and the selected *subcollar* are separate; comparing width to the collar alone would exaggerate the answer.

## All-period conclusion: what is proved, what remains open

**Proved for every \(p\ge3\), conditional on quantitative geometric hypotheses (general bounded-collar lemma).** If a realized central degree-two return has a correctly marked genuine four-step descendant with one old real edge side in its closed crest, the selected conformal paths contain a logarithmic radial subcollar of length at least \(\delta\log R_p\), are injectively pushed without cancellation, and have angle heights at most \(H\), then
\[
\frac{W(S_{4,p})}{W(S_p)}\ \ge\ \frac{2\pi\delta}{H}.
\]
This is a correct *all-\(p\) analytic implication*, but **its extra \(\delta,H\) hypotheses do not follow from PR #80's finite combinatorics or real kneading alone**. It does not imply that such a uniform \(\delta>0\) exists.

**Chebyshev asymptotics and the missing quantitative step.** As \(p\) increases, the numerical data suggest the normalized return \(t\mapsto G_p(x_pt)/x_p\) approaches a quadratic \(Q_\kappa(t)=1-\kappa t^2\), where the candidate \(\kappa\) is characterized by \(f_{-\kappa}^{6}(0)+f_{-\kappa}^{3}(0)=0\) on the near-\(1.79\) branch. This is an *asymptotic heuristic*, **not** a theorem of the finite verifier or PR #80. To promote it to the requested all-\(p\) claim requires an **explicit uniform complex-domain \(C^1\) error estimate** for \(G_p(x_pt)/x_p-Q_\kappa(t)\), and errors under four compositions small enough to preserve the strict \(S_0\) and q-side cut margins, central-component admissibility, prime-end path survival and Koebe/noncancellation bounds. No such all-\(p\) quantified distortion estimate has been proved here. Nor has \(c_p\to0\) been proved: the negative angular cosines for large finite \(p\) **do not** imply decay. Both an unconditional positive lower bound for all \(p\ge3\) under PR #80, and a decay theorem with rate, remain **open**.

The only *period-uniform numerical coefficient* proved from the published finite certificates is \(4213/10000\) **for \(3\le p\le8\)**, under those six physical/KKL realizations. Extrapolating it to \(p\ge9\) would be unjustified. The choice of parent Wave affects all ratios, so no canonical period-only \(c_p\) is asserted.

## Reproduction, trust boundary, and hostile-review checks

From repository root:

```sh
python research/independent_audits/crest_transport_tip_family_20261116/verify.py
python -m unittest discover -s research/independent_audits/crest_transport_tip_family_20261116 -p 'test_*.py' -v
python research/independent_audits/real_primitive_tip_family_uniform_20261116/verify.py
python research/independent_audits/issue40_crest_transport_20261116/verify_crest_transport.py --check-manifest
lake build TipKKLTreeMarking TipNativeProperRestriction
```

The new read-only verifier uses only Python standard-library integer/rational arithmetic. Its locked result JSON holds every period's parameter bracket, radial collar, rational \(u\)-bounds, exact width expression, two-sided ratio bound and the typed endpoint/crest census. Seven adversarial unit tests exercise bad parameter brackets, misplaced collars, broken \(\iota^*\) blocks, nonmonotone imaginary gates, and basic outward arithmetic. No new Lean theorem about physical prime ends or analytic widths is introduced; the dedicated workflow rebuilds the existing honest discrete Lean targets and dispatches the **unchanged** Research validation and Weighted spectral mathlib workflows against the exact PR SHA.

**What is not certified by the new Python/Lean:** the analytic KKL proper-restriction and surviving-path rules, homeomorphic identification of the entire little Julia Hubbard tree, local connectivity, conformal widths, universal Chebyshev/Koebe distortion and all-\(p\) physical existence. **Numerical only:** convergence and candidate limiting-shape heuristics. **Open:** the requested all-period uniform lower bound or all-period decay law, arbitrary chosen Waves, and general Issue #40/MLC amplification.

The review specifically checked: \(p=3\) non-normalized center; p-dependent **full parent** denominator; strict bin endpoints; uniqueness versus merely a sign change; interval recurrences with no hidden square roots; negative \(u\) for \(p\ge6\); upper and lower sides of a *single* old edge; the third-stage other endpoint's cut crossing; degree-two central versus degree-\(2^p\) global; the two distinct functors; and conditional analytic inputs. The alternating-series \(\pi\) enclosure was corrected during review before publishing.

Sources: merged [PR #78](https://github.com/dovvnloading/loops-research-archive/pull/78), [PR #80](https://github.com/dovvnloading/loops-research-archive/pull/80), PR #68, and the cited Kahn–Kapiamba–Lyubich Appendix A / §6.1 analytic framework as imported in those audits.

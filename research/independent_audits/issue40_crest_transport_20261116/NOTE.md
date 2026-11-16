# Issue #40: genuine marked crest transport at the physical PR #68 tip

**2026-11-16. A finite-depth physical-example result, not a solution of the general Issue #40 theorem.** This independent audit uses only new files. No existing source, ledger, research map or native Wave transfer is modified.

## Statement and source hypotheses

Take the *physical* three/nine Misiurewicz tip from PR #68, with parameter \(c\) strictly in the certified interval

\[
\frac{-607918036626757496169199575185708826140}{2^{128}}<
c<
\frac{-607918036626757496169199575185708826139}{2^{128}}.
\]

Let \(f_c(z)=z^2+c\), \(G=f_c^3:V_3\to U_3=D(0,1/4)\) be the connected **degree-two central quadratic-like restriction**, and \(\iota:V_3\hookrightarrow U_3\) the *inclusion embedding*. Import the physical real tree \(T=[x_6,x_3]\), its central preimage \(T'=[-x_3,x_3]\), locally connected slit-side prime ends, and the analytic content of Kahn–Kapiamba–Lyubich (KKL), arXiv:2606.27272v1, Section 2.5, Section 6.1 Proposition 6.5 and Appendix A.1/A.3.2–A.3.4. These imported geometric and analytic assertions are not formal outputs of the verifier. Global \(f_c^3\) has degree eight; using that as the central restriction degree would be wrong.

The target inner ideal circle has ten cyclic *open* marking atoms \(I_0,\ldots,I_9\), and the source has twenty \(S_0,\ldots,S_{19}\). Their types, old-tree edge sides and the distinct operators are

\[
 \begin{aligned}
  &I_1,I_9:\ E_{20}=(x_{15},x_9),\\
  &I_3,I_7:\ E_{0\alpha},\qquad I_4,I_6:\ E_{\alpha1},\\
  &I_0,I_2,I_5,I_8:\ \text{zero old-edge atoms},\\
  &G_*S_s=I_{s\bmod10},\quad
  \iota^*I_i=P_i,\quad F_*=G_*\circ\iota^*.
 \end{aligned}
\]

The ten **actual immersion pullback blocks**, not images under \(G_*\), are

| \(i\) | Open source atoms of \(P_i\) |
|---|---|
| 0 | \(18,19,0,1,2\) |
| 1 | \(3,4\) |
| 2 | \(5\) |
| 3 | \(6\) |
| 4 | \(7,8,9\) |
| 5 | \(10\) |
| 6 | \(11,12,13\) |
| 7 | \(14\) |
| 8 | \(15\) |
| 9 | \(16,17\) |

The attached component has **three** new source boundary atoms \(S_{19},S_0,S_1\); source halfturns, closures of crests and endpoint accesses cannot be replaced by single integer states.

Let \(d=-9/64\), and take PR #68's **genuine** Wave \(S\) consisting of the slit circles \(d+r e^{it}\), \(0<t<2\pi\) and \(3/256<r<1/64\). Its base is \((I_9,I_0,I_1)\), its actual *closed* crest \(I_0\) has zero old Hubbard edge incidence, and

\[
\mathcal W(S)=\frac{\log(4/3)}{2\pi}.
\]

### Physical example theorem

Use the **fixed** rational subcollar \(a=1/80<r<b=1/77\), strictly inside the original Wave's radius interval. Under the actual successive KKL proper restrictions \(\iota^*\) and covering pushes \(G_*\), at depth four there are two **genuine marked descendant sub-Waves**, \(S_4^+\) and \(S_4^-\), whose bases and *closed* crests are

| Descendant | Marked target base | Closed crest (native access closure inside base) | Positive old-edge atom |
|---|---|---|---|
| \(S_4^+\) | \(I_0,I_1,I_2,I_3\) | \(\overline{I_1\cup I_2}\) | \(I_1\), the upper side of \(E_{20}\) |
| \(S_4^-\) | \(I_7,I_8,I_9,I_0\) | \(\overline{I_8\cup I_9}\) | \(I_9\), the lower side of \(E_{20}\) |

These are actual restricted conformal path laminations, *not* phantom Waves assigned to every three-atom interval word. Both old-edge sides refer to the same graph edge \(E_{20}\) for edge-traversal counting; they are distinct prime-end boundary accesses.

Define \(u(r)\) as the **unique** real solution in \((0,1/2)\) to

\[
\operatorname{Re}G\left(d+r(u+i\sqrt{1-u^2})\right)=0,\qquad
\theta(r)=\arccos u(r).
\]

Then the exact extremal width and its *exact* ratio to the **entire original** PR #68 Wave are

\[
\boxed{\mathcal W(S_4^\pm)=
\int_{1/80}^{1/77}\frac{dr}{r\,\theta(r)},\qquad
\frac{\mathcal W(S_4^\pm)}{\mathcal W(S)}
=\frac{2\pi}{\log(4/3)}
\int_{1/80}^{1/77}\frac{dr}{r\,\theta(r)}.}
\]

The definite integral is an exact specification using a uniquely defined algebraic-angle function. It is **not** asserted to have an elementary antiderivative. The uniform-in-this-subcollar bounds \(0<u(r)<1/2\), and in fact the tighter \(3/32<u(r)<7/64\), imply \(\theta(r)<\pi/2\). Therefore

\[
\mathcal W(S_4^\pm)>\frac{2\log(80/77)}{\pi}>
\frac{\log(4/3)}{4\pi}=\frac12\mathcal W(S).
\]

The second inequality follows from **exact integer arithmetic**
\(3\cdot80^8>4\cdot77^8\). Thus the explicit physical lower-bound coefficient is \(c=1/2\); neither the interval proof nor the width proof uses numerical sampling. The constant is **not** derivable from four steps, covering degree two, branching multiplicity and Perron eigenvalue \(\phi=(1+\sqrt5)/2\) alone: existence and size of this collar are a separately checked *analytic geometric condition*.

For orientation **only**, floating quadrature produces \(W(S_4^\pm)\approx0.02599522\) and \(W(S_4^\pm)/W(S)\approx0.56775452\). These decimals are not certification or inputs to the result.

## The exact transport path: distinct \(G_*\) and \(\iota^*\)

The original left crossing \(w=d-r\) lies in \((-x_{12},x_6)\), and its right endpoint \(q=d+r\) is in \((x_{15},-\alpha)\). Proper restriction breaks the initial full circle at its **two distinct** \(S_1,S_{19}\) attachment accesses. KKL's A.1 short-path and A.3.2 single-pullback-cell filters retain both half-circles. Covering \(G_*\) then gives the first actual Wave crests \(I_2\) and \(I_8\) (PR #68). The successive real endpoint and crest census is:

| Output step | Real endpoint control and source access before push | Target crest |
|---|---|---|
| 1 | source attachment accesses \(S_1,S_{19}\) and right endpoints \(S_3,S_{17}\) | \(I_2\) or \(I_8\) |
| 2 | \(G(w)\in(-\alpha,x_9)\), \(G(q)\in(x_{18},\alpha)\), source \(S_4,S_6\) (with lower mates) | \(I_5\), base \(I_4,I_5,I_6\) |
| 3 | \(G^2(w),G^2(q)\in(-x_6,x_{12})\), opposite accesses \(S_9,S_{11}\) | \(I_0\), base \(I_9,I_0,I_1\) |
| 4 | new source crossing \(R_3(r)\in(-x_3,-x_{12})\), **terminal atom \(S_0\)**; \(G^3(q)\in(x_{15},-\alpha)\), upper \(S_3\) and lower \(S_{17}\) | \(I_1,I_2\) or \(I_8,I_9\), edge positive |

A delicate countercheck: the *other* stage-three endpoint \(G^3(w)\) can cross the marking cut at \(-\alpha\) as the radius varies; it is **not** claimed to stay in source \(S_3,S_{17}\). The constructed depth-four descendants are the selected **q-side** sub-Waves, for which the endpoints remain in \(S_3,S_{17}\) throughout. Claiming a fixed atom for the other side of the full third-stage Wave would be false.

On an original upper half-leaf the map \(G\) preserves the upper half-plane and \(\operatorname{Re}G(d+re^{i\theta})\) is strictly decreasing as \(\theta\) increases from zero to \(\pi\). The cosine equation therefore gives a **unique** imaginary-axis crossing, \(G(z)=iy\) with \(y>0\). The exact interval evaluation, for every radius in the slab, proves

\[
 R_2(r)=G(iy)>x_3,\qquad
 -x_3<R_3(r)=G(R_2(r))<-x_{12},\qquad
 x_6<G(R_3(r))<x_{15}.
\]

The second-stage real meeting is outside the preimage tree, so it does not add a restriction cut. The third-stage real meeting *is* inside \(T'\) and produces the new proper restriction. This terminal source atom \(S_0\), through \(-x_3\), is **not** the earlier pair \(S_1,S_{19}\). The selected upper q-side source path has endpoints \(S_0,S_3\), the lower has \(S_{17},S_0\). They have shortest cyclic source span four and covering target span four, strictly above the KKL A.1 deletion threshold of two. Under \(\iota^*\) their endpoint hosts are respectively \(P_0,P_1\) and \(P_9,P_0\), so they are *not* subordinate to a single pullback interval. All these predicates use the actual blocks above, then **and only then** the covering \(G_*S_s=I_{s\bmod 10}\) reads the selected pushed bases and their **closed** crest endpoints. Nothing relies on the invalid assertion \(F_*\overline I=\overline{F_*I}\) or on a universal edge incidence of all positive-width Waves.

## Complete-domain analytic arguments and exact width

The verifier encloses the **whole complex disk** \(D(d,b)\) by the elementary rational disk-radius recurrence for each of twelve applications of \(f_c\), and at each third iterate establishes containment in \(D(0,1/4)\). The centers of the first three image disks lie in the actual \(T'\), selecting the correct degree-two inverse component. The wave supports lie successively in the negative real half-plane, the first image is controlled by a positive imaginary difference factor, the second image lies in the positive real half-plane, and the third in the negative real half-plane. At each of the four covering stages, two distinct points of the relevant restricted support cannot be opposite, and central degree-two evenness gives **univalence** of the push on that support. A global degree-eight inverse-branch argument would not justify this conclusion.

More explicitly, with the physical polynomial
\(G(d+\zeta)=\sum_{k=0}^8 a_k\zeta^k\),
the exact coefficient tests

\[
 a_1>\sum_{k=2}^8 |a_k|\,k\,b^{k-1},\qquad
 a_1>\sum_{k=2}^8 |a_k|\,k^2b^{k-1}
\]

ensure strict imaginary sign and strict angular monotonicity on **whole circles**, not merely sample leaves. On the first image disk, writing \(G(z)=P(z^2)\), the negative linear coefficient of \(P\) dominates its higher terms in \(\operatorname{Im}G(z)/\operatorname{Im}z\); on the second image disk a similar negative-sign Taylor bound ensures that no additional undetected crossing appears. The unique root \(u(r)\) is enclosed using exact Chebyshev \(T_k,U_k\) recurrences, with 256-bit outward dyadic balls on 384 **entire radius bins**. Full-gate margins from the source cuts exceed \(1/4096\).

Every selected q-side final leaf is the conformal image of the original angular segment \(0<t<\theta(r)\), or its lower conjugate. In logarithmic coordinates
\[
 x=\log r,\quad y=t,\quad \log(1/80)<x<\log(1/77),\quad
 0<y<\theta(e^x),
\]
these are exactly the vertical leaves of a strip of variable height \(h(x)=\theta(e^x)\). For any admissible density whose length across each vertical leaf is at least one, Cauchy–Schwarz gives area at least
\(\int dx/h(x)\); equality is attained by density \(1/h(x)\) on that strip. Thus the *specified path-family* extremal width is the displayed exact integral. Density outside the support does not affect these leaves. This argument is analytic, not claimed to be verified by Python or Lean.

## Strongest general version justified; limitation of finite combinatorics

**Conditional bounded-collar crest transport lemma.** Suppose a physical source-defined full-circle Wave has logarithmic radial span \(L>0\) and width \(L/(2\pi)\), and an admissible sequence of properly restricted, conformally injective pushes produces a genuine marked descendant with a closed crest containing an **old** Hubbard dual-edge side. Suppose the selected descendant family contains a subcollar of logarithmic radial length at least \(\delta L\), and the corresponding leaf-angle heights are uniformly at most \(H>0\). Then, by the same exact strip argument,

\[
  \mathcal W(S')\ge \frac{\delta L}{H}
  =\frac{2\pi\delta}{H}\mathcal W(S).
\]

Its hypotheses include native path/closed-access inclusions and noncancellation; neither an open whole-atom cyclic word nor a Perron edge matrix substitutes for them. In this fixed physical example the **independently certified** collar has \(\delta=\log(80/77)/\log(4/3)>1/8\) and \(H=\pi/2\), yielding the strict \(c=1/2\). This is a concrete theorem conditional only on explicitly verified physical and imported analytic hypotheses, **not a universal \(c(4,2,\phi)\) inferred from the finite data**.

There is **no proof here** that such a \(\delta\) is bounded away from zero for a different Wave or as the number of critical returns increases. A uniform-in-steps or large-limb-count assertion would require a native prime-end gate/collar theorem for all proof-selected *closed* crests, admissible no-cancellation of proper restrictions, and uniform Koebe/bounded-distortion or a comparable modulus lower bound protecting a definite fraction of the extremal-width collar through long iterates. The finite Perron factor \(\phi\) and the number of sheets alone give no analytic collar width. **No source-defined arbitrary-depth counterexample is claimed.** Issue #40, the global KKL bounded-visit interval growth and parabolic Wave amplification, H1–H4, UPTCR and MLC all stay open.

## Certificate, finite-model trust boundary, and replication

The source-locked checker under this directory independently recomputes 256-bit outward interval orbit data, requires the original PR #68 Wave, verifies the previously established Issue #40 physical \(\iota^*\) blocks *separately* from covering labels, computes the degree-eight polynomial \(f_c^3\) directly, proves uniform gate/cut inequalities across all 384 radius bins, and verifies the exact integer width inequality. Its locked JSON manifest is deterministic. The adversarial mode must reject (i) changed parameter, (ii) false first-step edge crests, (iii) removal of the attached source atom \(S_0\) and (iv) conflation of \(G_*\) with \(\iota^*\). The checker and its tests require only Python standard libraries.

**Analytic inputs, not exact-computation outputs:** the connected central quadratic-like restriction, local connectivity and slit prime ends, KKL Proposition 6.5 and proper path semantics, univalence from central degree two, and the extremal-density calculation. **Numerical-only:** the two orientation decimals quoted above. **Open:** arbitrary proof-selected Waves, non-LC/canonical immersion cases, and all return-step-uniform statements.

No Lean file is added: the new bridge is analytic and the finite atom arithmetic is already modelled in the existing hole-free TipKKLTreeMarking formalization, which the dedicated CI rechecks. A fake Lean theorem about actual extremal widths would overstate what was formalized. The dedicated workflow also dispatches **unchanged** Research validation (lean-proofs.yml) and Weighted spectral mathlib proofs (weighted-lean.yml), waits for both **at the PR's exact head SHA**, and fails if either does not pass.

Reproduce from repository root:

    python research/independent_audits/issue40_crest_transport_20261116/verify_crest_transport.py --check-manifest
    python research/independent_audits/issue40_crest_transport_20261116/verify_crest_transport.py --adversarial
    python research/independent_audits/issue40_native_attachment_edge_incidence_20261115/verify_native_attachment_edge_incidence.py --check-manifest
    python research/independent_audits/verify_tip_KKL_tree_marked_breakage.py --check-manifest
    lake build TipKKLTreeMarking TipNativeProperRestriction

Primary mathematics source: Kahn–Kapiamba–Lyubich, arXiv:2606.27272v1, Sections 2.5, 6.1 and Appendix A. This note does not claim independent specialist validation of the analytic argument.

# Exact two-level real quadratic return certificate

**Date:** 2026-11-05. **Status:** Exact computer-assisted real one-dimensional dynamics, with a compact analytic proof of the return-interval conclusions and a reproducible integer-arithmetic certificate.

**Reproduce:** Run

    python research/independent_audits/verify_real_nested_3_9.py

This standard-library-only program is in the regular GitHub Actions research validation workflow. It uses no floating point, root finder, hidden downloaded datasets, or heuristic orbit pictures.

## 1. Actual quadratic parameter; exact algebraic identity

Consider the *actual* real quadratic polynomial \(f_c(x)=x^2+c\) and its critical orbit
\(x_0(c)=0\), \(x_{j+1}(c)=x_j(c)^2+c\). Write \(P_{27}(c)=x_{27}(c)\).

Fix the integers

\[
K=-607890580437450502081459824019535455703,\qquad B=2^{128}.
\]

There is **exactly one** real number \(c_*\) in the explicit rational interval

\[
\boxed{K/B<c_*<(K+1)/B}
\]

for which \(P_{27}(c_*)=0\). The decimal display is

\[
c_*\approx-1.786429858055761060267498053956.
\]

The attached program rigorously computes:

- \(P_{27}(K/B)>0\);
- \(P_{27}((K+1)/B)<0\);
- \(P_{27}'(c)<0\) for every \(c\) in this entire dyadic bracket.

All three statements are verified using **outward-rounded signed integer interval arithmetic at scale \(2^{224}\)**. The derivative is calculated by the exact recursion

\[
x_{j+1}=x_j^2+c,\qquad
d_{j+1}=2x_jd_j+1,\quad x_0=d_0=0.
\]

The recurrence's enclosure operations implement floor and ceiling integer division, so rounding can only enlarge, not shrink, a true range. By continuity and the intermediate value theorem a root exists; by the strict derivative enclosure it is unique in this bracket.

The same arithmetic proves \(x_1(c_*),x_3(c_*),x_9(c_*)\ne0\). Because the divisors of 27 are \(1,3,9,27\), the critical point has **exact period 27**.

**This is an exact algebraic specification**, not just an approximate period-27 parameter.

## 2. Two nested restrictive real intervals

At the certified parameter \(c_*\) set \(x_j=f_{c_*}^{\,j}(0)\) and define

\[
\boxed{I_3=[x_6,x_3],\qquad I_9=[x_9,x_{18}].}
\]

The integer interval enclosures verify

\[
x_6<x_9<0<x_{18}<x_3,
\]

hence \(I_9\Subset\operatorname{int}I_3\) as real intervals. Approximate endpoint values (for **display only**) are

| Interval | Lower endpoint | Upper endpoint |
|---|---:|---:|
| \(I_3\) | \(-0.146066217773028645\) | \(0.187319152541063984\) |
| \(I_9\) | \(-0.019846491851317216\) | \(0.014847493903615959\) |

The certificate propagates the **entire starting interval**, not just selected orbit points, through the interval extension \(J\mapsto J^2+c\). It verifies exact separation of the following closed images:

- \(I_3,f(I_3),f^2(I_3)\) are pairwise disjoint.
- \(I_9,f(I_9),\dots,f^8(I_9)\) are pairwise disjoint.
- For \(j=1,\dots,2\), every point of \(f^j(I_3)\) is nonzero.
- For \(j=1,\dots,8\), every point of \(f^j(I_9)\) is nonzero.

Because
\[
(f^m)'(x)=2^m\,x\,\prod_{j=1}^{m-1}f^j(x),
\]
these sign enclosures prove that **the only critical point of either return map \(f^3|_{I_3}\) or \(f^9|_{I_9}\) is \(0\)**. The certificate counts one negative intermediate phase for \(m=3\), so \(f^3\) has a strict *maximum* at \(0\). It counts four negative intermediate phases for \(m=9\), so \(f^9\) has a strict *minimum* at \(0\).

Finally, the exact period-27 critical orbit gives the endpoint images:

\[
\begin{array}{c|ccc}
 &\text{left endpoint}& 0 &\text{right endpoint}\\
 f^3|_{I_3}&x_9&x_3&x_6\\
 f^9|_{I_9}&x_{18}&x_9&x_{27}=0
\end{array}
\]

Since \(x_6<x_9<0<x_{18}<x_3\), the extreme-value/monotonicity argument proves **exactly**

\[
\boxed{f^3(I_3)=I_3,\qquad f^9(I_9)=I_9.}
\]

These are real restrictive intervals with first return periods **3** and **9**, respectively. No earlier iterate of either interval can return to it because the intermediate closed images are pairwise disjoint. Both return maps are real unimodal, with their unique critical point at the original critical point \(0\).

The same outward integer enclosures certify the **entire 26-symbol critical sign itinerary** (at times \(1\) through \(26\), with the final iterate \(x_{27}=0\)):

    -++-+--+--++-+--++-++-+--+

Under the first return \(g=f^3\), the eight nonzero critical images have signs \(+--+-++-\); under the inner return \(f^9\), the two nonzero critical images have signs \(-+\). These exact sign words are reproducible inputs for a future real-kneading/external-ray audit, **not** a proof of a specific external-angle portrait.

## 3. Actual two-scale phase transport

The first return is \(g=f^3|_{I_3}\); its inner return on \(I_9\) is

\[
g^3|_{I_9}=f^9|_{I_9}.
\]

The three intervals \(I_9,g(I_9),g^2(I_9)\) are pairwise disjoint and contained in \(I_3\). For each \(0\le j<9\),

\[
f^j(I_9)\subset f^{\,j\bmod3}(I_3).
\]

The containment follows from \(I_9\subset I_3\), \(f^3(I_3)=I_3\), and applying the same polynomial iterate to an inclusion. Thus the nine actual phase windows have a **canonical forgetful phase map**

\[
\mathbb Z/9\mathbb Z\longrightarrow\mathbb Z/3\mathbb Z,
\qquad j\longmapsto j\bmod3,
\]

which intertwines the physical forward dynamics. This is not merely shifting binary labels in an abstract Cantor model; every phase interval is an **actual real subset of the dynamical plane**.

This verifies a concrete two-level *real* return geometry in a single quadratic polynomial. It also provides a nine-window physical marking/inclusion testbed for any proposed source-stage abstraction.

## 3a. A certified finite-horizon complex Jordan collar

The exact integer interval calculation yields **strict, quantitative** bounds for both return levels \(p\in\{3,9\}\):

\[
\begin{aligned}
&|f^j(x)|<2
 &&(0\le j<p,\ x\in I_p),\\
&\operatorname{dist}(0,f^j(I_p))>1/10
 &&(1\le j<p),\\
&\operatorname{dist}(f^i(I_p),f^j(I_p))>1/100
 &&(0\le i<j<p).
\end{aligned}
\]

Here the distance is ordinary Euclidean distance along the embedded real line. The certificate computes enclosing intervals for the *whole* forward image, not just the orbit of \(0\), and checks these bounds via strict signed-integer comparisons.

For each level let

\[
\epsilon=2^{-40},\qquad
U_p=\{z\in\mathbb C:\operatorname{dist}(z,I_p)<\epsilon\}.
\]

This \(U_p\) is an **explicit bounded simply connected Jordan domain**, the open stadium/tube around the closed real interval.

**Theorem (actual quadratic finite-horizon complex collar).** For the real algebraic \(c_*\) constructed above and either \(p=3\) or \(p=9\),

1. the complex sets \(f^0(U_p),f^1(U_p),\ldots,f^{p-1}(U_p)\) are pairwise disjoint;
2. for every \(1\le j<p\), the image \(f^j(U_p)\) omits the unique critical point \(0\) of \(f\);
3. the holomorphic iterate \(f^p\) has **exactly one critical point inside \(U_p\)**, namely \(0\), with local degree two.

**Proof.** Given \(z\in U_p\), choose \(x\in I_p\) with \(|z-x|<\epsilon\). If \(|f^j(z)-f^j(x)|\le\delta_j\le1\) and \(|f^j(x)|<2\), then

\[
|f^{j+1}(z)-f^{j+1}(x)|
=|f^j(z)-f^j(x)|\,|f^j(z)+f^j(x)|
\le\delta_j(4+\delta_j)\le5\delta_j.
\]

Induction gives \(\delta_j=5^j2^{-40}\). For \(0\le j\le8\),

\[
5^j2^{-40}\le5^82^{-40}<10^{-6},
\]

an exact rational inequality included in the script. Thus each complex image \(f^j(U_p)\) lies in the \(10^{-6}\)-neighborhood of the verified real interval \(f^j(I_p)\). Distinct phase intervals are separated by more than \(10^{-2}\), so their \(10^{-6}\)-tubes do not meet. Noninitial phase intervals lie farther than \(10^{-1}\) from \(0\), so none of their tubes contains \(0\).

Finally, differentiating the polynomial iterate gives

\[
(f^p)'(z)=2^p z\prod_{j=1}^{p-1} f^j(z).
\]

No factor with \(j\ge1\) vanishes anywhere in \(U_p\); hence the only critical point of \(f^p|_{U_p}\) is \(z=0\), with a simple derivative zero (local degree two). \(\square\)

**Exact limitation:** This is a genuine finite-horizon **complex** separation and unique-critical-point result for an explicitly bounded Jordan domain around each real return interval. It **does not** show that \(f^p:U_p'\to U_p\) admits a proper quadratic-like restriction with \(U_p'\Subset U_p\), nor does it provide canonical Kahn–Lyubich external rays, prime-end accesses, closed puzzle pieces, sheet/coset completeness, or a nonattracting H3-compatible parameter. These require separate constructions. In particular, the terminal superattracting center still fails \(K(f)=J(f)\).

## 4. Critical limit: this center does **not** satisfy Paper 2's H3

The critical point is an exact period-27 superattracting point of \(f_{c_*}\): since \(f^{27}(0)=0\) and \(f'(0)=0\), the derivative \((f^{27})'(0)=0\). A sufficiently small complex neighborhood of \(0\) is attracted to this cycle. Consequently the filled Julia set \(K(f)\) has **nonempty interior** and is not equal to its boundary \(J(f)\).

Therefore the real center \(c_*\) **does not satisfy** Paper 2's standing hypothesis \(K(f)=J(f)\). In addition, even though the *real interval images* are disjoint, the certificate does not establish that **complex little Julia sets** are pairwise disjoint, that there are Jordan puzzle boundaries/prime-end transports, or that Kahn localization and the KL direct-decoration atlas align on the same physical germ.

It would be an error to promote the Paper 2 hypotheses, the open H1 marked-carrier gate, or any MLC claim on the strength of this real certificate.

This also avoids replaying the archive's earlier [double-airplane source audit](../mlc_unified/kl_aligned_double_airplane_source_lock_20260725.md), which correctly rejected source promotion of the complete complex same-germ alignment. The present parameter is an independently specified **period-27 real model**. It is not labeled a particular airplane tuning without a separate external-ray/lamination identification.

## 5. Precise contribution and next mathematical bridge

**Previously:** The archive had a candidate double-airplane *complex* alignment with unresolved planar little-Julia disjointness and KL marking. No exact named two-scale real restriction with checkable parameter, endpoint inequalities and disjoint physical phase windows was recorded in that audit.

**Now:** We have a unique algebraically certified real quadratic, genuine nested return periods 3 and 9, exact phase-window separation, and an explicit phase quotient on *physical* intervals. This is a positive proof-of-concept for a two-level return-state model, not a new MLC parameter class.

**Next theorem to target:** Given the exact \(I_3\supset I_9\) restriction above, choose source-specific complex Jordan neighborhoods \(U_3'\Subset U_3\), \(U_9'\Subset U_9\) around the relevant real intervals and prove that the polynomial restrictions \(f^3\) and \(f^9\) are each **degree-two quadratic-like** with the right nesting and non-interference. Prove or refute the pairwise disjointness of the complex outer/inner little Julia sets and their compatible ray/prime-end markings. If the superattracting Fatou geometry prevents a Paper-2-specific application, keep the example as the real control and move to a suitable non-attracting parameter in the same nested windows; **do not silently replace the source's H3**.

A valid actual two-scale KL certificate must still transport *all* proof-used accesses, cosets, branch sheets and obstacle data. The present real phase quotient does not solve that sheet-sensitive problem. The long-run MLC H1/H2/H3/H4 gates remain open.

## Certificate integrity and reproducibility

The Python file commits the exact integer \(K\), the dyadic scale \(2^{128}\), and its arithmetic precision \(2^{224}\). The parameter search that originally suggested \(K\) is **not** needed to verify its certificate. The program itself proves a root exists uniquely and all asserted interval signs and separations, with only arithmetic and continuity/derivative facts needed to interpret the output.

The GitHub Actions research validation runner executes this certificate beside the existing five-module core Lean suite, pinned mathlib proofs, and original ledger consistency tests. The integer program does not pretend to be Lean-checked source geometry; its interval arithmetic is transparent and can be ported to a formal proof checker in a later pass. No statuses in the 465-entry ledger are changed.

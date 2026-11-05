# A certified complex quadratic-like lift of the period-3/period-9 model

**Date:** 2026-11-05. **Status:** A concrete, finite **two-scale complex polynomial-like renormalization** for an exact quadratic polynomial and a small *open complex parameter disk*, with an outward signed-integer certificate for all quantitative inequalities. This is **not** a Kahn–Lyubich marked puzzle atlas, Paper 2 H3-compatible instance, MLC parameter-class theorem, or solution of an H1–H4 program gate. No independent expert mathematical referee is claimed.

**Reproduce (repository root):**

~~~sh
python research/independent_audits/verify_real_nested_3_9.py
python research/independent_audits/verify_complex_window_obstructions.py
python research/independent_audits/verify_complex_quadratic_like_3_9.py
~~~

The last script uses the existing \(2^{-224}\) outward dyadic interval engine. It performs no floating-point sampling and is run in regular research CI. The finite inequalities are computer-checked; the complex-analytic interpretation below uses explicitly stated classical theorems (Rouché, Riemann–Hurwitz, and the connectedness criterion for quadratic-like maps) and is not Lean-kernel-formalized.

## 1. Main theorem

Let \(f_c(z)=z^2+c\). As certified previously, there is a unique real \(c_*\) in the rational bracket

\[
\frac{-607890580437450502081459824019535455703}{2^{128}}
<c_*<
\frac{-607890580437450502081459824019535455702}{2^{128}}
\]

such that \(f_{c_*}^{27}(0)=0\). In particular \(c_*\approx-1.786429858055761\), and the critical point has exact period 27.

Put

\[
\mathcal D=\{c\in\mathbb C:|c-c_*|<2^{-32}\},\qquad
U_3=D(0,1/4),\qquad
U_9=D(0,1/32),
\]

and, for \(p=3,9\) and \(c\in\mathcal D\), let \(V_{p,c}\) be the connected component containing \(0\) of \(f_c^{-p}(U_p)\). Let \(K_{p,c}\) be the filled Julia set of the resulting return restriction.

**Theorem (parameter-uniform, two-scale complex quadratic-like returns).** For **every** complex parameter \(c\in\mathcal D\):

1. \(V_{p,c}\Subset U_p\) is a simply connected Jordan domain and
   \[
   f_c^p:V_{p,c}\longrightarrow U_p
   \]
   is a proper holomorphic map of **degree two** for both \(p=3\) and \(p=9\). Its unique critical point in the domain is \(0\), with local degree two.
2. The inner domain satisfies
   \[
   \overline{V_{9,c}}\subset D(0,13/512)\Subset U_9
   \subset V_{3,c}\Subset U_3.
   \]
3. The complex physical phase families
   \[
   \{f_c^j(V_{3,c}):0\le j<3\},
   \qquad
   \{f_c^j(V_{9,c}):0\le j<9\}
   \]
   are pairwise disjoint *within each family*. Furthermore,
   \[
   f_c^{3k}(U_9)\subset V_{3,c}
   \qquad (k=0,1,2).
   \]
   Consequently the **actual** complex inner phase cells refine the outer ones:
   \[
   f_c^j(V_{9,c})\subset f_c^{j\bmod 3}(V_{3,c}),
   \qquad 0\le j<9.
   \]
   The quotient \(j\bmod9\mapsto j\bmod3\) intertwines the physical successor map, rather than merely quotienting abstract address symbols.
4. The critical point never escapes either quadratic-like restriction. Both \(K_{3,c}\) and \(K_{9,c}\) are therefore **connected**, and
   \[
   \boxed{K_{9,c}\subset K_{3,c},\qquad
   f_c^j(K_{9,c})\subset f_c^{j\bmod3}(K_{3,c})
   \quad(0\le j<9).}
   \]

At the exact real center, the previously certified invariant intervals \(I_3=[x_6,x_3]\) and \(I_9=[x_9,x_{18}]\) also satisfy \(I_3\subset K_{3,c_*}\) and \(I_9\subset K_{9,c_*}\). Thus the new complex domains contain the **actual real restrictive models**, not merely a combinatorially equivalent model.

This proves a useful positive complex lift of the repository's real two-scale certificate. It does **not** assert a KL-specific ray/prime-end atlas or that any of these attracting parameters satisfies **Paper 2's H3: \(K(f_c)=J(f_c)\)**. Indeed merged PR #9 rules out that hypothesis on a much larger parameter disk.

## 2. Proof of the explicit boundary and critical-point estimates

Write \(x_j=f_{c_*}^{\,j}(0)\) and

\[
f_{c_*}^{\,j}(z)=x_j+a_j z^2+h_j(z),\qquad h_j(z)=O(z^4).
\]

The exact recursion is

\[
x_1=c_*,\quad a_1=1,\quad h_1=0,\qquad
x_{j+1}=x_j^2+c_*,\quad a_{j+1}=2x_j a_j,
\]

and

\[
h_{j+1}(z)
=2x_jh_j(z)+(a_jz^2+h_j(z))^2.
\]

Hence on \(|z|\le R\), defining \(T_1(R)=0\), the rigorous majorant recursion is

\[
\boxed{
T_{j+1}(R)\le 2|x_j|T_j(R)
+\bigl(|a_j|R^2+T_j(R)\bigr)^2.
}
\]

Using the earlier enclosing dyadic interval \(X_j\ni x_j\), a new outward enclosing interval \(A_j\ni a_j\), and upward-rounded integers for every \(T_j\), the script checks the following strict *positive* center margins, in ordinary complex modulus:

| Source circle | Target disk | Certified positive margin |
|---|---|---:|
| \(|z|=1/4\), \(f_{c_*}^3\) | \(|w|<1/4\) | \(>0.127520\) |
| \(|z|=1/32\), \(f_{c_*}^9\) | \(|w|<1/32\) | \(>0.023376\) |
| \(|z|=13/512\), \(f_{c_*}^9\) | \(|w|<1/32\) | \(>0.001817\) |

For each row the precise integer-verified inequality is

\[
|a_p|R^2
>
|x_p|+T_p(R)+R_{\mathrm{target}}+\text{margin}.
\]

Every displayed decimal is a **truncated conservative lower bound**, not a floating-point test.

**Uniformity in the complex parameter.** For \(c\in\mathcal D\) and \(z\) in any of the three source disks, compare its orbit with \(f_{c_*}^{\,j}(z)\). The same center bounds ensure \(|f_{c_*}^{\,j}(z)|<2\) throughout the relevant nine stages. With \(\delta=2^{-32}\), we therefore have

\[
e_0=0,\qquad e_{j+1}\le 5e_j+\delta
\quad(0\le j<9),
\]

as long as \(e_j\le1\), which the integer certificate independently checks. Thus

\[
e_j\le\frac{5^j-1}{4}\,\delta.
\]

In particular \(e_9<0.000114\). This loss is strictly smaller than **each** of the three boundary margins above. The same strict bounds show that none of the intermediate images \(f_c^j(U_p)\) for \(1\le j<p\) meets \(0\).

For any \(|w|<R_{\mathrm{target}}\), Rouché's theorem on the appropriate circle therefore compares

\[
f_c^p(z)-w
\quad\text{to}\quad
a_pz^2.
\]

The difference from \(a_pz^2\) has smaller modulus on that circle, so **exactly two roots counted with multiplicity** occur inside it. The first two rows give exactly two roots in \(U_3\) and \(U_9\), uniformly for all \(w\) in their respective targets. The third gives exactly two *already inside* \(D(0,13/512)\) for every \(w\in U_9\).

Because \(|f_c^p(z)|>R_{\mathrm{target}}\) on the boundary of each target source disk, its inverse-image portion inside the disk is relatively compact. The component containing \(0\) maps properly onto the target disk. At \(0\), \(f_c^p\) has local degree exactly two (the intermediate iterates omit the sole critical point). As there are only two preimages of any target value within the source disk, counted with multiplicity, no second inside component can occur. Hence the entire inside preimage is \(V_{p,c}\), a connected degree-two branched covering of \(U_p\).

The boundary is a finite union of smooth real-analytic curves because \(f_c^p\) has **no critical point on that boundary**. Riemann–Hurwitz for the bordered planar degree-two covering with one simple branch point gives

\[
\chi(V_{p,c})=2\,\chi(U_p)-1=1.
\]

A connected bounded planar domain with smooth finite boundary and Euler characteristic one is a disk, so \(V_{p,c}\) is simply connected with a Jordan boundary. Its closure is compactly contained in \(U_p\). This is the Douady–Hubbard quadratic-like definition, not merely unique-criticality on a finite collar.

The third boundary inequality excludes **every** inner preimage point in \(U_9\setminus D(0,13/512)\), because the number of roots in the smaller circle is already the total number of roots in \(U_9\). The strict boundary gap also keeps its closure inside the smaller disk. Thus \(V_{9,c}\Subset D(0,13/512)\).

## 3. Proof of complex phase separation and actual 9-to-3 routing

At center parameter \(c_*\), for each integer \(j\le9\), the recurrence above encloses the *whole image* of the source disk \(D(0,R)\) inside

\[
f_{c_*}^{\,j}(D(0,R))
\subset D\bigl(x_j,\,|a_j|R^2+T_j(R)\bigr)
\quad(j\ge1),
\]

with \(j=0\) given by \(D(0,R)\). For \(|c-c_*|<2^{-32}\), simply enlarge every radius by the certified \(e_j\).

- For \(R=1/4\), the three stage-\(0,1,2\) disks remain separated with a certified minimum gap \(>0.927691\).
- For the **shrunken** inner source radius \(R=13/512\), all **nine** stage-\(0,\dots,8\) disks remain separated, with minimum gap \(>0.004286\). It is essential to shrink \(V_9\) first; checking only the whole \(U_9\) would give inconclusive phase-disk bounds.

Because \(V_{3,c}\subset U_3\) and \(V_{9,c}\subset D(0,13/512)\), these bounds prove the pairwise disjointness assertions for the actual complex return domains.

Separately, running the majorant for **the full \(U_9=D(0,1/32)\)** verifies the four strict containments

\[
\boxed{
f_c^{\,j}(U_9)\subset U_3
\quad\text{for }j\in\{0,3,6,9\}.
}
\]

Their smallest uniform margin to \(\partial U_3\) is \(>0.052862\). Since

\[
V_{3,c}
=\{z\in U_3:f_c^3(z)\in U_3\},
\]

the pair of containments for times \(3k\) and \(3k+3\) gives

\[
f_c^{3k}(U_9)\subset V_{3,c}
\qquad(k=0,1,2).
\]

Apply \(f_c^r\), \(r=0,1,2\), to obtain the claimed complex phase refinement. This is a statement about **physical images in one common complex dynamical plane** at one parameter, not an abstract rewrite of first-symbol deletion.

## 4. Proof of connected filled Julia sets and their nesting

Take \(r=2^{-13}\) and any \(c\in\mathcal D\). For \(z\in\overline{D(0,r)}\), use the exact center critical orbit \(x_j\) and define error upper bounds

\[
E_0=r,\qquad
E_{j+1}=
E_j(2|x_j|+E_j)+2^{-32}.
\]

At each arithmetic operation the script rounds *outward*. It verifies

\[
\boxed{2E_{27}<r},
\qquad |x_9|+E_9<1/32,
\qquad |x_{18}|+E_{18}<1/32.
\]

Because \(x_{27}=0\) exactly, for every parameter \(c\in\mathcal D\) these give

\[
f_c^{27}\bigl(\overline{D(0,r)}\bigr)
\subset D(0,r/2)\subset D(0,r),
\]

and

\[
f_c^9\bigl(\overline{D(0,r)}\bigr)\subset U_9,
\qquad
f_c^{18}\bigl(\overline{D(0,r)}\bigr)\subset U_9.
\]

Starting at \(0\in D(0,r)\), every time \(9m\) is one of \(27q\), \(27q+9\), or \(27q+18\). Therefore the critical orbit at all 9-block times stays in \(U_9\), hence in \(V_{9,c}\) because the next 9-block image also lies in \(U_9\). Thus \(0\in K_{9,c}\) for **every** complex parameter in \(\mathcal D\).

The standard quadratic-like connectedness criterion says that a quadratic-like filled Julia set is connected if and only if all critical points in the restriction are nonescaping. There is exactly one, \(0\). Hence \(K_{9,c}\) is connected.

For any \(z\in K_{9,c}\), all iterates \(f_c^{9q}(z)\) are in \(V_{9,c}\subset U_9\). Each subsequent block-\(3\) or block-\(6\) image of that point is in \(V_{3,c}\) by the cross-scale containment already proved. Therefore *every* \(f_c^{3m}(z)\in V_{3,c}\), yielding \(z\in K_{3,c}\). This establishes

\[
K_{9,c}\subset K_{3,c}.
\]

It also shows that all \(f_c^{3k}(K_{9,c})\) are contained in \(K_{3,c}\), so the claimed inclusion of their nine physical phase images in the three outer phases follows. Since \(0\in K_{9,c}\subset K_{3,c}\), the same critical nonescape criterion proves that \(K_{3,c}\) is connected.

At the real center, the earlier interval certificate supplies \(f_{c_*}^p(I_p)=I_p\) and \(I_p\subset U_p\) for \(p=3,9\). Thus every point of \(I_p\) is nonescaping under the corresponding quadratic-like return, giving \(I_p\subset K_{p,c_*}\).

## 4a. Corollary: source-independent identification of the inner straightening

At the **exact real parameter \(c_*\)**, both complex target disks are centered at zero and the maps \(f_{c_*}\) commute with complex conjugation. The corresponding unique preimage components \(V_{3,c_*}\) and \(V_{9,c_*}\) are therefore also invariant under conjugation.

Since both polynomial-like filled Julia sets are connected, the Douady–Hubbard straightening theorem assigns to each return a unique normalized complex quadratic polynomial \(z^2+t_p\), up to hybrid equivalence, where \(p\in\{3,9\}\) denotes the *return time* (so \(t_9\) belongs to the inner return). The conjugate normalized polynomial \(z^2+\overline{t_p}\) straightens the complex-conjugate return, which is the same return. Uniqueness implies

\[
\boxed{t_3,t_9\in\mathbb R.}
\]

The hybrid conjugacy respects the unique critical point and its forward orbit. From \(f_{c_*}^{27}(0)=0\) and \(x_3,x_9,x_{18}\ne0\), the outer return \(f_{c_*}^{3}\) has critical orbit of exact period **9**, while the inner return \(f_{c_*}^{9}\) has critical orbit of exact period **3**. Therefore their normalized straightenings satisfy

\[
\operatorname{per}_{z^2+t_3}(0)=9,\qquad
\operatorname{per}_{z^2+t_9}(0)=3.
\]

In particular **the inner straightening parameter \(t_9\) is uniquely identified algebraically** as the one real root in \((-2,-1)\) of

\[
\boxed{t^3+2t^2+t+1=0.}
\]

Indeed \((z^2+t)^3(0)=t\bigl(t^3+2t^2+t+1\bigr)\); exact period 3 excludes \(t=0\). The cubic has derivative \((t+1)(3t+1)>0\) on \((-\infty,-1)\), and changes sign from \(-1\) at \(t=-2\) to \(+1\) at \(t=-1\). For \(-1\le t\le0\), it equals \(1+t(t+1)^2\ge23/27>0\), and for \(t\ge0\) it is positive. Thus it has exactly one real root.

The outer straightening parameter \(t_3\) is a real exact-period-9 superattracting quadratic center, but this argument does **not** determine which of the possible real period-9 roots it is. Neither statement identifies the original parameter \(c_*\) by a KL external-angle portrait, equates hybrid straightening with a source-specific ray marking, nor proves compatibility of peripheral sheet/coset data across the two physical levels. Those stronger source-alignment tasks remain open.

This is a classical-straightening corollary of the newly certified polynomial-like maps, not a claim that straightening theory itself is new.

## 5. Reproducible exact margins (strict lower displays)

The code checks all inequalities as signed integers in units of \(2^{-224}\). The following are rounded **down**, solely for legibility:

| Certification | Minimum after parameter loss |
|---|---:|
| Period-3 properness/Rouché boundary margin | \(>0.127520\) |
| Period-9 properness/Rouché boundary margin | \(>0.023263\) |
| Inner-domain shrinking boundary margin | \(>0.001703\) |
| Three outer complex phase separations | \(>0.927691\) |
| Nine inner complex phase separations | \(>0.004286\) |
| Physical inner-to-outer four-time containments | \(>0.052862\) |

The numerical format is not a substitute for proof: the strict comparisons are made *before* printing, on the exact rounded integers, and the complex analysis derives the geometric statements from those comparisons.

## 6. What the theorem changes, and what it does not

**Positive new research object:** The archive now has an actual, explicit and reproducible two-level complex quadratic-like polynomial system, not merely real restrictive intervals or a finite complex collar. The domain pairs are explicit disk-preimage constructions, both degree two; the smaller domain is compactly nested in the larger, the nine inner images are separated, and the physical \(9\to3\) phase projection is realized by actual inclusions. These statements persist over a specified **open disk of complex parameters**, and both little filled Julia sets are connected there.

**Still open:** This family is deep inside a period-27 attracting parameter region. As established by the separate merged [attracting-window audit](two_scale_complex_window_obstructions_20261105.md), the ambient filled Julia set has interior and does not satisfy Paper 2's \(K(f)=J(f)\). The present theorem therefore does not source-license Paper 2's direct-decoration compactification hypothesis, a KL end-fiber identification, an external-ray/prime-end atlas, the infinite localization sheet/coset transport from Paper 1, or the complete H1 marked carrier. It proves no MLC analytic gate, including H2 calibration, H3 coercivity, H4 rigidity, or universal protected-tower closure.

**Next scientific test:** Seek a *nonattracting* source-compatible parameter with a certified KL puzzle/prime-end marking and a physically faithful two-scale phase/sheet atlas. Alternatively, attempt to transport the present analytically certified nested return domains to a source-compatible parameter regime through an independently verified continuation theorem. Neither follows from this finite attracting-window result.

## 7. Attribution and review status

The definition of polynomial-like maps, their degree-two connectedness criterion and the straightening framework are due to **Adrien Douady and John H. Hubbard**, *On the dynamics of polynomial-like mappings*, *Annales scientifiques de l'École Normale Supérieure* **18** (1985), 287–343 ([public source](https://pi.math.cornell.edu/~hubbard/PolyLikeMaps.pdf)). Rouché's theorem and Riemann–Hurwitz are standard classical tools. This manuscript does not claim those theorems as new.

The **new within-archive deliverable** is the independently checkable choice of two complex return disks at this exact parameter, the quantified 27-step and degree-two boundary conditions, and the compatible physical phase nesting over an explicit complex parameter disk. No claim of mathematical priority over earlier literature is made.

**AI assistance disclosure:** OpenAI GPT-6 assisted with the domain search, proof design, exact integer certificate, and drafting under the repository steward's direction. The certificate was exercised by GitHub research CI; the displayed analytic deductions are provided for human checking. Specialist verification has not been represented as completed. The previously released papers and the source-locked 465-entry proof ledger remain unchanged.

# An exact ramified precritical marking **inside both actual period-3 and period-9 filled sets**

**Date:** 2026-11-07. **Status:** a proved local holomorphic/algebraic theorem for the archive's **actual nonattracting 3/9 Misiurewicz tip**, with an independently certified rational coefficient, exact degree-two parameter monodromy, an honest two-scale component-membership argument, and a new spatial scaling corollary for the physical phase-clock parameters of merged [PR #52](https://github.com/dovvnloading/loops-research-archive/pull/52). **Not** a new global MLC case, a holomorphic motion of the *whole* Julia set, a transported ray/prime-end atlas, or universal H1–H4 closure.

## 1. What the changed lens discovers

The last research pivot proved phase-to-parameter windows for **actual quadratic polynomials**, whereas earlier KKL work repeatedly required unproved global side/prime-end transport. This note asks a more local, checkable question: what happens to the *actual precritical points of the repelling period-nine orbit* as their parameter crosses the certified Misiurewicz tip? Crucially, do those points still belong to the **existing nested polynomial-like returns**, or are they merely arbitrary solutions outside the little filled Julia sets?

The answer is unexpectedly sharp: the two points belong to **both genuine little filled sets** for all sufficiently small complex parameter perturbations. They form a nontrivial **two-sheeted square-root cover of the parameter disk**, branching once over the original tip. No globally continuous ordered labeling of this pair exists on a punctured parameter disk; a natural two-fold ramified parameter base change resolves that obstruction. The coefficient and the direction of real/imaginary splitting are certified by *exact outward integer arithmetic*.

This is a local **algebraic precritical marking**, not an identification of individual ambient external-ray angles. Finite ray markings of the tip have been established in [the exact Misiurewicz ray atlas](./period27_misiurewicz_tip_ray_access_20261106.md) and [Levin's 3/9 ray interface](./levin_tip_p2_carath%C3%A9odory_two_scale_20261106.md); their continuation onto the new two sheets is still a separate dynamical-ray landing problem. Classical stability of rays at repelling periodic cycles and Misiurewicz transversality are prior art (e.g. Lyubich, *Dynamics of Quadratic Polynomials*, §37.10; Hutz–Towsley, *Misiurewicz Points for Polynomial Maps and Transversality*). The contribution here is the explicit **source-realized 3/9 fiber, exact coefficient, nested little-filled membership, and phase-clock conversion**, not discovery of square-root branching in general.

## 2. Source-locked quadratic parameter and honest little returns

Write

\[
 f_c(z)=z^2+c,\qquad P_0(c)=0,\quad P_{j+1}(c)=P_j(c)^2+c.
\]

The archive's exact nonattracting tip is the unique real root \(c_*\) of

\[
 G(c):=P_{18}(c)+P_9(c)=0
\tag{2.1}
\]

in the strict interval

\[
 \frac{-607918036626757496169199575185708826140}{2^{128}}
 <c_*<
 \frac{-607918036626757496169199575185708826139}{2^{128}}.
\tag{2.2}
\]

Its critical orbit has **minimal preperiod 10 and eventual period 9**. In particular, \(P_{18}(c_*)=-P_9(c_*)\), \(P_{19}(c_*)=P_{10}(c_*)\), \(P_9(c_*)\ne0\), and its eventual 9-cycle is repelling. Let \(F_c=f_c^9\), and set

\[
 Z_*:=P_{10}(c_*),\quad
 \lambda_*:=\partial_zF_{c_*}(Z_*)\in(3,4).
\]

The holomorphic implicit-function theorem gives a **unique single-valued holomorphic** repelling fixed-point continuation \(Z(c)\) in a full complex parameter disk \(D(c_*,\delta)\):

\[
 F_c(Z(c))=Z(c),\quad Z(c_*)=Z_*.
\tag{2.3}
\]

Set \(p(c)=f_c^8(Z(c))\). Then the following identities hold on the *entire* disk, not only at its center:

\[
 \boxed{F_c(p(c))=p(c),\qquad f_c(p(c))=Z(c).}
\tag{2.4}
\]

At \(c_*\), \(p(c_*)=P_{18}(c_*)=-P_9(c_*)\), with

\[
 P_9(c_*)\approx-0.0228386678824,\qquad
 p(c_*)\approx+0.0228386678824.
\]

For the **actual** two-scale geometry, take the same round target disks as in the source-certified complex domain proof:

\[
 U_3=D(0,1/4),\quad U_9=D(0,1/32),\quad
 V_j(c)=\operatorname{Comp}_0(f_c^{-j}(U_j)),\quad j\in\{3,9\}.
\tag{2.5}
\]

Here \(\operatorname{Comp}_0\) denotes the connected component containing \(0\). The certificate [*Two actual complex quadratic-like returns*](./nonattracting_tip_complex_two_scale_20261106.md) proves \(f_{c_*}^j:V_j(c_*)\to U_j\) is proper degree two, \(V_j\Subset U_j\), and \(K_9(c_*)\subset K_3(c_*)\). Its finitely many strict Rouché/disk/phase margins are **open conditions**. Consequently there is some common complex parameter disk in which both proper restrictions and the strict three-block phase containments still hold. It is essential that nearby **connectedness** of \(K_9(c)\) and \(K_3(c)\) is *not* asserted.

## 3. The exactly factored precritical fiber

Put

\[
 A_8:=(f_{c_*}^8)'(c_*)=\prod_{j=1}^{8}2P_j(c_*),
 \qquad A_9:=(f_{c_*}^9)'(c_*)=2P_9(c_*)A_8.
\tag{3.1}
\]

The exact dyadic interval certificate proves

\[
 \boxed{93.43<A_8<93.45,\quad -4.27<A_9<-4.26.}
\tag{3.2}
\]

In particular the inverse of \(w\mapsto f_c^9(w)\) near \((c_*,c_*)\) exists holomorphically: there is a unique \(W(c)\) near \(c_*\) such that

\[
 \boxed{f_c^9(W(c))=Z(c),\qquad W(c_*)=c_*.}
\tag{3.3}
\]

Define the **source-defined precritical discriminant**

\[
 \boxed{R(c)=W(c)-c.}\tag{3.4}
\]

### Theorem 3.1 — exact square-root fiber and certified transversality

For a sufficiently small bidisk about \((c_*,0)\), the following identities are **exact**, with no discarded higher-order terms:

\[
 \boxed{f_c^{10}(s)=Z(c)
 \quad\Longleftrightarrow\quad
 s^2=R(c).}\tag{3.5}
\]

Furthermore \(R\) has a **simple** zero at \(c_*\) and

\[
 \boxed{
 R'(c_*)=\frac{G'(c_*)}{(\lambda_*-1)A_8}
 =-\kappa,
 \quad 0.276<\kappa<0.277,
 \quad\kappa\approx0.276592060183468506.
 }\tag{3.6}
\]

The displayed interval is **strictly rationally certified**, not inferred from a floating-point fit. In particular,

\[
 \boxed{R(c)=-\kappa(c-c_*)+O((c-c_*)^2).}\tag{3.7}
\]

For real parameters sufficiently close to but different from \(c_*\):

- **Right side** \(c>c_*\): \(R(c)<0\), so the two precritical points \(s_\pm(c)=\pm i\sqrt{-R(c)}\) are distinct and **purely imaginary**.
- **Left side** \(c<c_*\): \(R(c)>0\), so \(s_\pm(c)=\pm\sqrt{R(c)}\) are distinct and **real**.

On the right,

\[
 \boxed{
 s_\pm(c)=\pm i\sqrt\kappa\,\sqrt{c-c_*}
    \bigl(1+O(c-c_*)\bigr),\qquad
 0.525<\sqrt\kappa<0.527.
 }\tag{3.8}
\]

**Proof.** The identity \(f_c^{10}(s)=f_c^9(c+s^2)\) is elementary but is the key to keeping the physical critical point and parameter clocks correct. Since \(w\mapsto f_c^9(w)\) is locally univalent at \((c_*,c_*)\), its specified local inverse image of \(Z(c)\) is precisely \(W(c)\). Thus (3.5) follows by substituting \(w=c+s^2\).

Use the **actual landing displacement** \(\Delta(c)=P_{10}(c)-Z(c)\) from merged PR #52. Differentiating (3.3) at \(c_*\) and comparing with the derivative of \(P_{10}(c)=f_c^9(c)\) gives

\[
 \Delta'(c_*)=A_9(1-W'(c_*)),
 \quad\text{hence}\quad
 R'(c_*)=-\frac{\Delta'(c_*)}{A_9}.
\tag{3.9}
\]

The source's exact factorization

\[
 f_c^9(P_{10}(c))-P_{10}(c)
 =(P_{18}(c)-P_9(c))(P_{18}(c)+P_9(c))
\]

and the repelling fixed-point derivative give

\[
 \Delta'(c_*)=
 \frac{(P_{18}(c_*)-P_9(c_*))G'(c_*)}{\lambda_*-1}
 =\frac{-2P_9(c_*)G'(c_*)}{\lambda_*-1}.
\tag{3.10}
\]

Insert \(A_9=2P_9(c_*)A_8\) into (3.9). The small but nonzero factor \(2P_9(c_*)\) **cancels exactly**, giving the stable coefficient (3.6). The already-certified \(G'(c_*)\in(-71,-70)\), \(\lambda_*>1\) and \(A_8>0\) establish \(R'<0\). A new full \(2^{-256}\) outward-integer certificate refines this to \(0.276<\kappa<0.277\) by **three independently evaluated formulas**: \(\Delta'/A_9\), \(-G'/[(\lambda-1)A_8]\), and \((P'_9+p')/A_8\), with \(p'\) calculated by a separate eight-step parameter derivative iteration. The sign, expansions and square-root bounds follow. \(\square\)

## 4. These branches live inside BOTH real polynomial-like filled sets

The remaining question is not algebraic. A preperiodic point can lie in the wrong dynamical component, which would make a supposed 3/9 marking meaningless. Here that failure **does not occur**.

### Theorem 4.1 — actual two-scale precritical orbit and little-filled membership

For every sufficiently close complex parameter \(c\), let \(s_\pm(c)\) be the two roots of (3.5), understood as an **unordered pair** unless a branch cut or double cover has been chosen. Then the full central degree-nine return satisfies

\[
 \boxed{
 F_c(s_\pm(c))=-p(c),\quad
 F_c(-p(c))=p(c),\quad
 F_c(p(c))=p(c).
 }\tag{4.1}
\]

Moreover, with \(K_j(c)\) the genuine filled sets of the proper quadratic-like restrictions (2.5),

\[
 \boxed{s_+(c),s_-(c),-p(c),p(c)\in K_9(c)\subset K_3(c).}\tag{4.2}
\]

The points \(p(c)\) and its forward 9-cycle are repelling. The pair \(s_\pm(c)\) is a *two-step preperiodic portrait for \(F_c\)*, not a pair of guessed virtual-Julia sheet labels. Formula (4.2) does **not** say that either little filled set is connected for nearby parameters.

**Proof of the exact 9-return portrait.** Define \(q(c)=f_c^8(W(c))\). By (3.3),

\[
 f_c(q(c))=f_c^9(W(c))=Z(c)=f_c(p(c)).
\]

At \(c_*\), \(q(c_*)=P_9(c_*)=-P_{18}(c_*)=-p(c_*)\), and \(q(c_*)\ne p(c_*)\). Since \(f_c(q)-f_c(p)=(q-p)(q+p)=0\), continuity/holomorphy forces \(q(c)=-p(c)\) throughout a smaller disk. For either root \(s\) of (3.5), \(f_c(s)=W(c)\), so

\[
 F_c(s)=f_c^8(W(c))=q(c)=-p(c).
\]

Equation (2.4) gives \(F_c(p)=p\); evenness of the first quadratic iterate gives \(F_c(-p)=F_c(p)=p\). This proves (4.1) **as an actual polynomial identity along the constructed holomorphic branches**.

**Proof of component membership.** At \(c_*\), the three points \(0,P_9(c_*),P_{18}(c_*)\) lie in \(K_9(c_*)\subset V_9(c_*)\), by the existing real restrictive interval and complex quadratic-like certificates. They are therefore in the **interior of the same open component** \(V_9(c_*)\) of \(f_{c_*}^{-9}(U_9)\). Choose, within this open connected component, compact polygonal paths from \(0\) to each of the other two points, and small closed disks about all three points. Their images by \(f_{c_*}^9\) are compact subsets of \(U_9\). By continuity in parameter, the same paths/disks remain in \(f_c^{-9}(U_9)\) for all sufficiently small complex perturbations. Since \(s_\pm(c)\to0\), \(-p(c)\to P_9(c_*)\), and \(p(c)\to P_{18}(c_*)\), all four points lie in the **component containing 0**, namely \(V_9(c)\). Their exact future \(F_c\)-orbit is the finite chain (4.1), so every iterate remains in \(V_9(c)\). By the definition of filled set, they lie in \(K_9(c)\).

Finally the strict finite three-block inclusions of the original complex certificate persist for a small parameter disk:

\[
 \overline{f_c^{3k}(U_9)}\subset V_3(c),\qquad k=0,1,2,
\tag{4.3}
\]

with closure notation understood after replacing \(U_9\) by its fixed closed disk of radius \(1/32\), as licensed by those strict circle margins. For every \(z\in K_9(c)\), the points \(F_c^n(z)\) lie in \(U_9\). Applying \(f_c^{3k}\), \(k=0,1,2\), keeps all \(f_c^{3(3n+k)}(z)\) in \(V_3(c)\). Therefore every \(f_c^3\)-iterate of \(z\) remains in \(V_3(c)\), proving \(K_9(c)\subset K_3(c)\). No Julia-boundary continuity or local connectivity is used. \(\square\)

**Scope caveat.** Equation (4.3) relies on the *specific strict finite source disk and component margins* recorded in the earlier period-3/9 complex certificate, not on the general statement that all polynomial-like renormalizations are nested under parameter perturbation. A separate audit of these margins is appropriate before a published two-scale persistence claim.

## 5. Genuine parameter-space braid and its minimal analytic repair

### Theorem 5.1 — unavoidable transposition and canonical ramified base change

In a sufficiently small complex disk \(D\) centered at \(c_*\), the subset

\[
 \mathscr P=\{(c,s)\in D\times\mathbb C: f_c^{10}(s)=Z(c),\ |s|\text{ small}\}
 =\{(c,s):s^2=R(c)\}
\tag{5.1}
\]

is a connected two-sheeted holomorphic cover of \(D\setminus\{c_*\}\) with one **simple branch point** at \((c_*,0)\). Analytic continuation around any once-positive loop encircling \(c_*\) exchanges its two precritical points. In particular, there is **no continuous global ordered pair** \(s_1(c),s_2(c)\) of the roots on the full punctured disk, nor any single-valued holomorphic labeling on that disk.

There is, however, a natural local resolution: write \(c=c_*+u^2\). As \(R(c_*+u^2)/u^2\) extends holomorphically with value \(-\kappa\ne0\), choose its holomorphic square root \(a(u^2)\), with \(a(0)=i\sqrt\kappa\). Then the two branches become

\[
 \boxed{s_\pm(u)=\pm u\,a(u^2),\quad
 c=c_*+u^2,\quad s_\pm(0)=0.}
\tag{5.2}
\]

They are **holomorphic** over the ramified parameter variable \(u\), with simple crossing at \(u=0\). The deck involution \(u\mapsto-u\) interchanges them; the unordered fiber and its symmetric polynomials remain single-valued over \(c\).

**Proof.** By (3.6), \(R\) has a simple zero. The argument principle implies \(R\) winds once about 0 on a small positive parameter loop. A globally continuous square root would have half-integer winding, impossible. Hence the two roots transpose. The analytic expansion \(R(c)=(c-c_*)h(c)\) with \(h(c_*)=-\kappa\ne0\) gives (5.2) on the degree-two base change. Minimality of the two-fold cover follows from the nontrivial order-two monodromy. \(\square\)

**Interpretation for marks.** A proposed *ordered algebraic precritical sheet label* that distinguishes these two points cannot live continuously over a full punctured parameter disk. One must either work with the **unordered marked pair**, restrict to a simply connected slit parameter sector, or retain the **two-fold ramified parameter coordinate**. This is a genuine holomorphic obstruction **inside the actual K9/K3 little filled sets**. It is **not** a theorem that all external-ray accesses or all possible protected markings are impossible to continue: such a conclusion would require the missing ray-to-root identification.

## 6. Connect to the previously proved physical return clocks

The merged phase-to-parameter result, PR #52, supplies real curves \(c_n(t)>c_*\) on a small fixed target interval \(J\) with

\[
 c_n(t)-c_*=B(t)\lambda_*^{-n}
      +O(n\lambda_*^{-2n}),\quad B(t)>0,\quad n\to\infty,
\tag{6.1}
\]

uniformly for \(t\in J\); their physical critical-orbit time is \(10+9n\). Apply (3.8) to these actual parameters:

\[
 \boxed{
 s_\pm(c_n(t))
 =\pm i\sqrt{\kappa B(t)}\;\lambda_*^{-n/2}
   \bigl(1+O(n\lambda_*^{-n})\bigr),
 }\tag{6.2}
\]

uniformly on \(J\), since \(B(t)\) is bounded above and below by positive constants there. Equivalently the two legitimate marked precritical points in **both** little filled sets have separation

\[
 \boxed{
 |s_+(c_n(t))-s_-(c_n(t))|
 =2\sqrt{\kappa B(t)}\,\lambda_*^{-n/2}
   \bigl(1+O(n\lambda_*^{-n})\bigr).
 }\tag{6.3}
\]

Thus the physical parameter phase window contracts at multiplier \(\lambda_*^{-n}\), but the accompanying *spatial precritical sheet separation* contracts at the **square-root rate \(\lambda_*^{-n/2}\)**. The coefficient \(\kappa\in(0.276,0.277)\) is not a free parameter, and the 9-return multiplier \(\lambda_*\approx3.73298234\) belongs to the source-certified polynomial.

This gives the first explicit **two-scale, spatial-and-parameter phase calibration** in the archive at the actual nonattracting period-3/9 tip. It is not a bound on arbitrary renormalization towers or an automatically defined holomorphic ray motion; it isolates the extra one-bit parameter monodromy that a future finite marked transport must retain.

## 7. Exact checker, non-promotions and next acceptance gate

Run from the repository root:

```bash
python -m py_compile research/independent_audits/verify_tip_ramified_precritical_pair.py
python research/independent_audits/verify_tip_ramified_precritical_pair.py --check-manifest
```

The checker independently encloses the original root bracket at integer precision \(2^{-256}\), the critical orbit/derivative recurrences, \(A_8,A_9,\lambda_*,G',\Delta'\), **three algebraically different formulas for \(\kappa\)**, and strict rational bounds \(0.276<\kappa<0.277\), \(0.525<\sqrt\kappa<0.527\). A separately evaluated 100-digit decimal Newton diagnostic tests the periodic-point continuation, inverse branch, sign of \(R\), and exact orbit identity for three small positive displacements. These diagnostics **do not** prove the holomorphic inverse-function theorem, component paths or monodromy; those are proven in the written argument from the cited existing finite domain conditions and elementary complex analysis.

**New independent geometric question:** Can the **source-certified external-ray landing pairs** of the repelling period-nine orbit and their complete inverse-ray classes be assigned consistently to the two branches of (5.2) on a chosen parameter sector, with their 3/9 KL \(O/\xi/\eta\) ideal-side tags and finite proper-path tests? A successful construction would yield a genuinely marked phase transition through the **correct ramified base**. If it fails, the first offending source ray, crosscut or access can be named exactly. In either case it is a more substantive next step than another KKL Wave width model.

**Explicitly open:** no identification of an individual ray angle with \(s_+(c)\) or \(s_-(c)\) has been proved; no full KL based sheet/coset natural transformation; no uniform bounds; no new locally connected parameter class; no change to H1–H4, UPTCR or MLC. Underlying periodic-ray stability, holomorphic inverse branches, parameter monodromy and square-root branching are classical mathematics; Kahn–Lyubich, Levin and the archive's earlier tip work retain their original attributions. OpenAI GPT-6 assisted the source-specific calculation, rigorous verifier and exposition. Independent specialist review and novelty/priority assessment are necessary.

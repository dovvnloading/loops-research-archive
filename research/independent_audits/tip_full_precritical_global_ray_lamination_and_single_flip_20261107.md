# The complete 1,023-class Misiurewicz inverse-ray lamination and its single real-parameter flip

**Date:** 2026-11-07 (Eastern). **Scope:** exact, fully enumerated dynamical-ray landing classes of the entire degree-1,024 physical fiber over the source-certified period-nine repelling point at the **actual twice-airplane-tuned real Misiurewicz quadratic**. This extends the 12-point/24-access local census in stacked [PR #56](https://github.com/dovvnloading/loops-research-archive/pull/56), and its parent complete inverse-angle count in draft [PR #55](https://github.com/dovvnloading/loops-research-archive/pull/55). The result is not a full KL localization-sheet/groupoid construction, a global holomorphic motion of dynamical rays, or a proof of MLC. The combinatorial enumeration is machine-exact; ray landing and analytic continuation rely on the separately identified source theorems.

## 1. Two ordinary periodic rays and the actual critical-value slit

Write \(f_c(z)=z^2+c\). At the exact archived real Misiurewicz parameter \(c_*\), the critical point has **minimal preperiod 10** to a repelling nine-cycle, with \(Z_*=f_{c_*}^{10}(0)\) and \(f_{c_*}^9(Z_*)=Z_*\). The exact rational source certificate and Milnor's primitive orbit-portrait bound, used in PR #55, establish that the **entire ray portrait at \(Z_*\)** consists of precisely

\[
 T=\left\{\frac{228}{511},\frac{283}{511}\right\}.\tag{1.1}
\]

The actual critical value \(c_*=f_{c_*}(0)\) has exactly two landing rays (Zakeri's real Misiurewicz theorem), with angles

\[
 \tau=\frac{116791}{261632},\qquad 1-\tau=\frac{144841}{261632}.\tag{1.2}
\]

The earlier physical alpha-puzzle construction in [*Complete ambient alpha-ray pullback table*](./tip_puzzle_ray_tree_20261106.md), §2, proves the **actual holomorphic inverse-branch rule** for

\[
 S=\mathbb C\setminus(\mathcal R_{c_*}(\tau)\cup\{c_*\}).\tag{1.3}
\]

The complement is simply connected and avoids the only critical value. Its two holomorphic inverse branches \(b_0,b_1\) of \(f_{c_*}\) are distinguished by their disjoint outer angular half-circles. With \(\kappa=\tau/2\), these are

\[
 I_0=(\kappa,\kappa+1/2),\qquad
 I_1=(\kappa+1/2,\kappa+1)\pmod 1.\tag{1.4}
\]

For any ambient ray angle \(\theta\) whose ray lands at a point \(v\in S\), let

\[
 L_i(\theta)=\left\{\frac\theta2,\frac{\theta+1}2\right\}\cap I_i,
 \tag{1.5}
\]

where the braces denote the **unique** element in that interval. Pulling back a two-ray landing class \(\{\alpha,\beta\}\) at \(v\ne c_*\) yields the two genuine two-ray classes

\[
 \boxed{\{L_0(\alpha),L_0(\beta)\},\qquad
 \{L_1(\alpha),L_1(\beta)\}.}\tag{1.6}
\]

**Why these angles really co-land.** Both rays ending at \(v\in S\) lift by the same conformal inverse branch \(b_i\) with a common endpoint \(b_i(v)\). In the Böttcher coordinate their lifts have the particular angles in (1.5). They therefore land at the same *actual* physical inverse point. The analytic input is the source's simply connected slit and its holomorphic branch continuation, **not** the fact that the two angle numerators happen to have the same denominator.

**Only exception: the real critical value.** If \(v=c_*\), its two target rays are the slit ray and its conjugate. They pull back to the **four** rays landing at the unique critical point \(0\):

\[
 \boxed{\left\{\frac{\tau}{2},\frac{1-\tau}{2},
          \frac{\tau+1}{2},\frac{2-\tau}{2}\right\}.}\tag{1.7}
\]

This must be **one four-ray class**, not two distinct inverse points: \(f_{c_*}^{-1}(c_*)=\{0\}\) with multiplicity two. No analytic inverse of \(f_{c_*}\) exists at that endpoint, so (1.6) is intentionally *not* used there. The four angles are exactly the tip's previously certified critical quartet.

## 2. Global theorem: exactly 1,023 landed classes, all explicitly assigned

For \(n\ge0\), set \(\mathcal P_n=f_{c_*}^{-n}(Z_*)\) and let \(\mathscr A_n\) denote the rational external rays ending at these points. The exact source critical orbit has no earlier arrival at the repelling target: \(f_{c_*}^{j}(0)\ne Z_*\) for all \(j<10\). Thus **none of the depth \(n<9\) target points is the critical value**: if \(c_*\in\mathcal P_n\), then \(f^{n+1}(0)=Z_*\), contrary to minimal preperiod ten. On the other hand \(c_*\in\mathcal P_9\), because \(f_{c_*}^9(c_*)=Z_*\). It is a single target point, not a second critical-value component.

### Theorem 2.1 (complete source-ray inverse tree)

Start with the unique two-ray class \(T\) at \(Z_*\) in (1.1). Repeatedly apply (1.6) to **every two-ray class** through nine inverse steps. On the tenth inverse step, apply (1.7) **exactly once**, to the unique class \(\{\tau,1-\tau\}\) landing at \(c_*\), and (1.6) to all other classes. Then:

1. For \(0\le n\le9\), there are exactly \(2^n\) distinct physical inverse points, each with exactly two ambient ray accesses. The total angle count is \(2^{n+1}\).
2. At \(n=10\), there are exactly \(1023\) distinct physical inverse points: **1022 ordinary two-ray points and one four-ray critical point**. There are precisely \(2048\) distinct ambient rational rays, with no omissions or duplicate angles.
3. All landing classes have exact rational angles in
   \[
    \mathcal F_{10}=\left\{\frac{t+k}{1024}:t\in T,\quad k=0,1,\ldots,1023\right\}.
    \tag{2.1}
   \]
   Using common denominator \(523264=1024\cdot511\), the **entire 1023-class partition**, including each ordinary inverse-branch word in \(\{0,1\}^{10}\) and the unique critical word ending in \(C\), is committed verbatim in the JSON manifest. There are no unnamed ray-angle pairs left in this global depth-ten fiber.
4. All **1022 simple-point two-ray chords are pairwise unlinked** in the external angle circle. This follows analytically from actual disjoint dynamic rays and distinct landing points; independently, the checker exhausts \(\binom{1022}{2}=521731\) exact integer crossing tests and finds none.

**Proof.** For \(n<9\), every target point has no critical predecessor, because the critical value would force a critical orbit arrival before time ten. The source's actual inverse branches \(b_0,b_1\) apply to each two-ray target class and give both distinct roots and both distinct ray pairs; the branches have disjoint images. Induction supplies exactly \(2^n\) two-ray classes at each depth through nine. At depth nine the unique critical value is present, with its two source rays \(\tau,1-\tau\). Every other point has two distinct simple inverse points and the ordinary lift (1.6); the critical value has one double inverse point and the special four-ray lift (1.7). Consequently the last count is \(2(512-1)+1=1023\), with 1022 two-ray classes and one four-ray class, and the total ray count is \(2(1022)+4=2048\). The inverse angle map halves the angle, optionally adding 1/2, so (2.1) follows by induction. Distinct lifted positive-potential Böttcher rays cannot cross or share an angle; the degree-1024 target fiber and its complete two-ray periodic portrait rule out any omitted roots or extra rays. The noncrossing statement follows from disjointness of genuine rays landing at distinct points (and is separately checked exhaustively). \(\square\)

**Explicit critical inverse word.** With source sheet `0` chosen as the half-circle \(I_0\), the critical point is the word

\[
 \boxed{010010110C,}\tag{2.2}
\]

where the terminal \(C\) is a *critical fold*, not a third sheet. The code's finite partition contains 1022 ordinary depth-ten words and this one terminal fold word. The word records the route through the ray-cut complements; it is **not** a finite replacement for an arbitrary infinite KL localization coset.

## 3. A complete **single-pairing-switch** at the real tip

Let the four critical angles in strict external order be

\[
 a=\frac{116791}{523264},\quad
 b=\frac{144841}{523264},\quad
 d=\frac{378423}{523264},\quad
 e=\frac{406473}{523264}.\tag{3.1}
\]

Merged [PR #53](https://github.com/dovvnloading/loops-research-archive/pull/53) proves that the critical double root splits as \(s_\pm(c)^2=R(c)\), \(R'(c_*)\in(-0.277,-0.276)\). Merged [PR #54](https://github.com/dovvnloading/loops-research-archive/pull/54) proves the actual rational-ray pairing bifurcation on the **real Mandelbrot parameter slice**:

\[
\begin{array}{c|cc}
&\text{first inverse point}&\text{second inverse point}\\\hline
 c<c_*&\{a,e\} \text{ at }+\sqrt{R(c)}&\{b,d\}\text{ at }-\sqrt{R(c)}\\
 c>c_*&\{a,b\}\text{ at }+i\sqrt{-R(c)}&\{d,e\}\text{ at }-i\sqrt{-R(c)}.
\end{array}\tag{3.2}
\]

### Theorem 3.1 (global rational-ray equivalence changes only once)

There is a real \(\varepsilon>0\) such that the **same complete set of 2048 rational external-ray angles** gives the ray-access fiber of \(f_c^{10}(z)=Z(c)\) for every real \(|c-c_*|<\varepsilon\). For all such \(c\ne c_*\), the 1024 inverse points are simple, each with two rays. Exactly **1022** of their ray-pair equivalence classes are independent of \(c\) across the entire interval. The remaining four rational rays undergo **only** the pairing switch (3.2). At \(c=c_*\), these four co-land at the single critical point. Thus the complete depth-ten external ray equivalence undergoes a *single local noncrossing pairing flip*; no other 2044 angles change their pairings.

**Proof.** PR #55 establishes that there are precisely two periodic rays at the repelling continuation \(Z(c)\) for all real \(c\) sufficiently near \(c_*\). All 1024 holomorphic inverse points of \(f_c^{10}(z)=Z(c)\) are simple in a punctured complex neighborhood except for the two near-critical sheets, by PR #55's one-transposition theorem. Each of the other 1022 inverse points has a distinct root at \(c_*\). The implicit-function theorem continues it holomorphically throughout a smaller parameter disk. Choose disjoint small dynamical disks around the finite set of 1022 roots. Repelling periodic-ray stability and analytic inverse continuation of the selected rays' terminal segments place the **same two rational inverse rays** at that root throughout a sufficiently small *real* interval; root and ray landings cannot switch without a collision, which has been excluded by the local inverse and finite disks. Because the set is finite, one interval works for all 1022. The only remaining four rays are exactly the critical quartet, whose physically proved left/right grouping is (3.2). The degree count proves every ray and point is included; no additional pairing can occur. \(\square\)

**Noncrossing order check.** Both pairings (3.2) are noncrossing for the strict cyclic order \(a<b<d<e\): on one side the pairs are nested, on the other they are disjoint. At the critical parameter all four form one equivalence class. This is a **real-slice lamination switch**, not a claim that the entire parameter disk admits a single-valued ordered precritical/ray marking (the actual complex parameter monodromy obstructs that, as PR #53 proved).

## 4. Exact match to the two-scale 3/9 geometry

The new global enumeration is independently compared to the source-geometric 32-ray selector in stacked PR #56. Its explicit 15 actual \(K_3\) physical ray groups (including three \(K_9\) groups and the twelve coarse-only groups) form an **exact subset of the new 1023 groups**, with **all 32 rational ray angles in matching groups**. The checker directly compares the complete group sets, not just counts or their first and last numerators.

That cross-check provides two genuinely different constructions of the same 12 coarse-only physical pairs:

- **Inward from infinity:** the source's Zakeri critical-value ray slit, lifted ten physical f-steps, including exactly one critical encounter;
- **From the renormalization core:** the source's ambient alpha critical-face sieve, Levin's verified period-3 angle map, and three quadratic-like G-return ray inverse steps.

They agree **pair by pair** with no fitted phase shift and no invented finite topological sheet identification. These are finite, landed dynamical-ray equivalences; the unbounded KL localization sheet/coset fibers and canonical \(O/\xi/\eta\) pseudo-piece transition are still **open**.

## 5. Reproduction, Lean boundary, and the remaining real obstruction

Run from the repository root:

```sh
python -m py_compile research/independent_audits/verify_tip_full_precritical_ray_lamination.py
python research/independent_audits/verify_tip_full_precritical_ray_lamination.py --check-manifest
```

The **complete 1023-row JSON** records every physical angle numerator (common denominator 523264), the ordered source-sheet inverse word, all intermediate-depth counts, exact noncrossing control and the left/right critical pairing switch. Its SHA-256 digest covers the entire complete landing partition and detects a lost or altered ray class. It independently reuses the **committed PR #56 manifest only to compare** the 15 K3 groups; its own 1023-class recurrence never reads the PR #56 construction.

The Python standard-library checker exhaustively verifies **521731** pairwise noncrossing tests among the 1022 ordinary chords and checks all 2048 external angles once. All checks are on exact rationals/integers, not on a sampled pixel rendering. The **mathematical identification** of the angle groups with genuine landed rays comes from the actual slit inverse-branch theorem, the Zakeri/Milnor source ray inputs, and periodic-ray stability. These are *written/imported analytic facts*, not Python theorems. The separate stacked PR #56 **Lean 4** module already formalizes the 2048-to-32 genuine alpha-face count and the 15 fine/coarse grouping arithmetic. This global 1023-group regression remains a complete exact finite certificate rather than a Lean formalization of complex ray landing.

The next genuine frontier is to assign these **explicit source slit words and four coarse-only original G puzzle face classes** to actual KL \(O/\xi/\eta\) access-side and based **infinite** localization sheet/coset data. A finite inverse-ray word does not determine a winding coset by fiat; such a claim needs the original proper-path, lifting, and gluing proof. The source's direct-versus-iterated canonical localization embedding gives a candidate comparison but is not asserted to act on every ray mark established here. UPTCR, H1--H4, Issue #40 and MLC remain **OPEN**.

**Attribution:** Milnor (orbit portraits, Böttcher ray landing and stability), Zakeri (real critical-value rays), Douady–Hubbard (quadratic-like straightening), and Kahn–Lyubich/Levin (genuine puzzle and angle geometry). The source-dependent finite enumeration and exposition were developed with OpenAI GPT-6. Independent originality/priority and specialist expert review have **not** been established.

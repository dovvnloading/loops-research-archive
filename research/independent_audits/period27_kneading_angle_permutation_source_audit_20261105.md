# Period-27 kneading-angle identity and full cyclic orbit permutation

**Date:** 2026-11-05. **Status:** Exact signed-integer verification of a classical symbolic-combinatorial correspondence on the archive's unique real period-27 quadratic center. This is a new source comparison *within this archive*, not a new general theorem of kneading theory, a complete parameter-ray identification, a prime-end/sheet atlas, or progress claimed on an MLC gate.

## 1. Correct the parameter-ray target

Let \(c_*\) be the exact superattracting period-27 real center previously isolated in the archive. The periodic *parameter* rays of the Mandelbrot set do **not** land at \(c_*\), which lies inside a hyperbolic component \(H_*\). They land at the **parabolic root on the boundary** of a hyperbolic component.

This is the established periodic-parameter-ray landing theorem (Douady–Hubbard; D. Schleicher, *Rational Parameter Rays of the Mandelbrot Set*, arXiv:math/9711213; S. Zakeri, *External Rays and the Real Slice of the Mandelbrot Set*, arXiv:math/0210382, §2). The intended Issue #12 question is therefore: do the candidate rays land at the root of **the component \(H_*\) whose center is \(c_*\)**?

## 2. Exact real input

The center is the unique real zero of \(f_c^{27}(0)=0\), where \(f_c(z)=z^2+c\), in the dyadic interval

\[
\frac{K}{2^{128}}<c_*<\frac{K+1}{2^{128}},
\qquad K=-607890580437450502081459824019535455703.
\]

The existing outward-rounded \(2^{-224}\) signed integer certificate establishes existence and uniqueness, exact period 27, every nonzero critical-orbit sign, and the strict order of all 27 orbit vertices \(x_j=f_{c_*}^j(0)\), \(0\le j<27\). These are **exact geometric** inputs, not floating-point orbit pictures.

## 3. Baker–Chen–Li–Qian's kneading-angle definition

Matthew Baker, Andrea Chen, Sophie Li and Matthew Qian, *Necklaces, permutations, and periodic critical orbits for quadratic polynomials*, European Journal of Combinatorics **134** (2026), 104352, [arXiv:2508.12924v2, §6.1](https://arxiv.org/html/2508.12924v2), define the kneading angle of a real critically periodic quadratic by its signed orbit. Put \(\kappa_0=*\), \(\kappa_j=\operatorname{sgn}(x_j)\), \(j=1,\ldots,26\). Start with \(t_1=0\); when \(\kappa_j=+\), retain the previous bit \(t_{j+1}=t_j\), and when \(\kappa_j=-\), flip it \(t_{j+1}=1-t_j\).

Applying this *published definition* to the certified sign enclosures yields the exact 27-bit word

\[
t_1\cdots t_{27}=
011100100100011011100011011.
\]

The classical **kneading-angle invariant** of the actual polynomial is therefore

\[
\boxed{\theta_{\mathrm{knead}}(c_*)=
0.\overline{011100100100011011100011011}_2
=\frac{59914011}{134217727}.}
\]

The new exact program verifies every source sign, the 27-bit integer, the primitive doubling period, and the fact that this is the unique angle closest to \(1/2\) within its doubling orbit, as predicted by Baker et al., Theorem 6.2.

**Critical distinction:** this number is here a *kneading-angle invariant*, defined by real critical-orbit signs. Its equality with the previously proposed lower external angle is **not, by itself, a proof that it is the lower characteristic parameter-ray angle for \(H_*\)**.

## 4. A second independent test: the entire 27-vertex cycle

Baker et al., §4.1, define \(\lambda\), a bijection from primitive binary necklace-inversion classes to cyclic unimodal permutations. Their §6.1 identifies the resulting permutation with the **increasing real-order ranks** of the critically periodic orbit.

Let \(t\) be the 27-bit word above, \(\iota\) bitwise complementation and \(L\) the cyclic left shift. Start with \(s=\iota(t)\), whose initial bit is 1. Define the twisted shift

\[
F(s)=
\begin{cases}
L(s),&L(s)_1=1,\\
\iota(L(s)),&L(s)_1=0.
\end{cases}
\]

For odd period 27, the ordinary nonexceptional case of §4.1 applies; signed-string extension is unnecessary. The 27 iterates \(\mu_j=F^{j-1}(s)\) are pairwise distinct; rank them lexicographically. The resulting complete permutation is

\[
\boxed{
(1,27,18,9,19,10,6,22,13,\,
3,25,16,7,21,12,4,24,15,\,
2,26,17,8,20,11,5,23,14).
}
\]

**Independent exact comparison.** The earlier arithmetic enclosures sort the *actual* real orbit vertices in increasing order by their iterate index:

\[
(1,19,10,16,25,7,13,22,4,6,24,15,9,0,\,
18,12,21,3,5,23,14,8,26,17,11,20,2).
\]

For each \(j=1,\ldots,27\), find the actual rank of \(x_j\), taking \(x_{27}=x_0\). All **27 ranks agree** exactly with the pure twisted-shift result. The source permutation is also cyclic unimodal: the rank successor map decreases up to the critical vertex and increases thereafter. No numerical orbit sampling is used.

This is an exact, independently falsifiable **instance** of Baker et al.'s classical permutation theorem. It is not a new general theorem or a claim of mathematical priority.

## 5. Separate proven tuning geometry from the missing identification

Let \(A\) denote the real airplane component of period 3 with characteristic root ray pair \(3/7=0.\overline{011}_2\) and \(4/7=0.\overline{100}_2\). Classical Douady–Hubbard tuning, stated in Zakeri §2, gives an embedding \(\iota_A\) of the Mandelbrot set, preserving **centers and roots**, multiplying hyperbolic component periods, and acting on external angles by substitution

\[
\sigma(0)=011,\qquad \sigma(1)=100.
\]

Applying the source tuning rule twice shows that the root of the **specified twice-tuned hyperbolic component \(A*A*A\)** receives the actual parameter rays

\[
\frac{59914011}{134217727}
\quad\text{and}\quad
\frac{74303716}{134217727}.
\]

This is imported source mathematics, distinct from the exact arithmetic at \(c_*\). We now have two independent results with the same rational number:

\[
\theta_{\mathrm{knead}}(c_*)
=\theta_{-}(A*A*A)
=\frac{59914011}{2^{27}-1}.
\]

**First unclosed bridge:** show, using an exact theorem with compatible conventions (or a separate direct parameter classification proof), that the *real-center kneading-angle map* equals the **lower characteristic root ray-angle map** for the hyperbolic component containing that center. This relationship must not be inferred merely by equating the two binary words. If established, it would imply \(H_*=A*A*A\) and identify \(c_*\) as its center. It would still *not* make the parameter rays land at \(c_*\).

**Next harder bridge:** give actual *dynamical-plane* ray landing/identification and compatible Kahn–Lyubich puzzle, prime-end access, and Paper-1 sheet/coset transport at both physical return scales. The attracting center fails Paper 2's \(K(f)=J(f)\) hypothesis, so a separate source-compatible parameter is ultimately required.

## 6. Status and reproduction

| Exact statement | Status |
|---|---|
| Period-27 real critical orbit enclosures | Previously certified |
| \(\theta_{\rm knead}(c_*)=59914011/(2^{27}-1)\) | **Exactly verified** using published definition |
| Source twisted-shift permutation matches all 27 real ranks | **Exactly verified** |
| Tuned component \(A*A*A\)'s root ray pair | Imported tuning theorem, finite blocks checked |
| \(c_*\) is the center of the specified tuned component | **Not promoted; source-convention bridge remains open** |
| Dynamical-plane KL ray, access, and sheet compatibility | Open |
| H1–H4, UPTCR and MLC | Open and unchanged |

To reproduce:

    python research/independent_audits/verify_period27_symbolic_atlas.py --check-manifest
    python research/independent_audits/verify_period27_kneading_angle_permutation.py

The new verifier uses only exact integer arithmetic and the already independently checked outward dyadic engine; it runs in regular research CI. The cited source theorems are **not** kernel formalized by this script, and external mathematical referee review has not occurred.

**AI disclosure:** OpenAI GPT-6 performed source comparison, code, proof compilation and drafting under the repository steward's direction. No affiliation or endorsement by Baker et al., Zakeri, Schleicher or any other cited author is implied. No released PDF or source-locked proof-ledger status was changed.

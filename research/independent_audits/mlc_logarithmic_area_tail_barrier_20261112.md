# A universal inverse-log-cubed obstruction for Mandelbrot Laurent-area tails

**Date: 2026-11-12 | Independent follow-on to PR #70 | mathematical status: written theorem conditional only on classical published inputs; not a proof of MLC.**

## Result and precise provenance

Let \(M\) be the Mandelbrot set, with the normalized exterior conformal map

\[
\Psi(w)=w-\frac12+\sum_{n\ge1} b_n w^{-n},\qquad |w|>1.
\]

Write

\[
E_N=\sum_{n>N}n|b_n|^2,\qquad
A_N=\pi\left(1-\sum_{n=1}^N n|b_n|^2\right),\qquad
T_j=E_{2^j-1}.
\]

**Theorem 1 (unconditional dyadic logarithmic energy obstruction).** Under the standard Douady--Hubbard external uniformization and the published landing claims below,

\[
\boxed{\displaystyle \limsup_{j\to\infty} j^3 T_j\;\ge\;
\frac{\pi^2}{12\log2}=1.1865691104\ldots.}
\tag{1}
\]

Consequently the rigorous Laurent area upper approximants satisfy

\[
\boxed{\displaystyle\limsup_{N\to\infty} (\log N)^3\bigl(A_N-\operatorname{Area}(M)\bigr)
\ge \frac{\pi^3(\log2)^2}{12}>0.}
\tag{2}
\]

In particular \(A_N-\operatorname{Area}(M)\ne o((\log N)^{-3})\). This is a **quantitative** strengthening, at the area-energy level, of the earlier qualitative no-algebraic-tail observation in PR #70. It does not prove that MLC is true or false. This is a deduction from classical inputs; mathematical priority outside this archive has **not** been established.

**Imported inputs, with scope.**

1. Bielefeld--Fisher--von Haeseler, *Computing the Laurent Series of the Map \(\Psi\)*, MPI/88-46 (1988), published *Advances in Applied Mathematics* **14** (1993), 25--38, DOI 10.1006/aama.1993.1002, preprint pp. 14--15, Claim 4.0: the radial parameter rays with angles
   \(\theta_m=2\pi(1/3+1/(4^m-1))\) land at \(c_m=-1+e^{2\pi i/m}/4\), while \(\theta_m\to 2\pi/3\). The source imports the landing assertion from Douady--Hubbard; **we do not re-prove ray landing**. Preprint: https://archive.mpim-bonn.mpg.de/id/eprint/3259/1/preprint_1988_46.pdf . The preprint p. 15 has an evident minus-sign typo in its displayed \(|c_m-3/4|\); its own preceding formula and the correct comparison use \(c_\infty=-3/4\).
2. Gronwall's area theorem for exterior univalent maps: \(\sum_{n\ge1}n|b_n|^2=1-\operatorname{Area}(M)/\pi\le1\). Its application to the Mandelbrot map is classical and appears in Ewing--Schober, *The Area of the Mandelbrot Set*, *Numerische Mathematik* **61** (1992), 59--72.
3. Carathéodory's theorem: a continuous boundary extension of the normalized inverse exterior map is equivalent to local connectivity of \(M\) (a connected, full compact set). Only the implication "uniform absolute convergence \(\Rightarrow\) continuous extension" is used in the argument.

The 1993 paper already proves a weaker non-Hoelder consequence. **The constant (1) and log-cubed estimate are derived here, not attributed to the source authors.** External novelty/priority remains unassessed.

## Proof

### Lemma 2 (a dyadic tail-to-absolute-tail estimate)

Set

\[
B_j=\left(\sum_{2^j\le n<2^{j+1}}n|b_n|^2\right)^{1/2},\qquad
T_j=\sum_{k\ge j}B_k^2.
\]

If, for some \(A\ge0\) and all sufficiently large integers \(j\),

\[
T_j\le A j^{-3},
\tag{3}
\]

then for all sufficiently large integers \(J\),

\[
\sum_{j\ge J}B_j\le\frac{\sqrt{3A}}{J}\sqrt{1+J^{-1}},
\tag{4}
\]

and

\[
\boxed{\displaystyle
\sum_{n\ge2^J}|b_n|\le
\frac{\sqrt{3A}}{J}\sqrt{(1+J^{-1})(\log2+2^{-J})}.}
\tag{5}
\]

**Proof (weighted discrete Hardy estimate).** Since \(B_j^2=T_j-T_{j+1}\), Abel/summation by parts and the nonnegativity of \(T_j\) give, for \(J\) past the threshold in (3),

\[
\begin{aligned}
\sum_{j\ge J}j^2B_j^2
&\le J^2T_J+\sum_{j>J}(j^2-(j-1)^2)T_j\\
&\le \frac{A}{J}+A\sum_{j>J}\frac{2j-1}{j^3}\\
&\le \frac{A}{J}+2A\sum_{j>J}j^{-2}
\le\frac{3A}{J}.
\end{aligned}
\]

Here the boundary term \(M^2T_{M+1}\) vanishes as \(M\to\infty\) by (3), and \(\sum_{j>J}j^{-2}\le J^{-1}\). A second Cauchy--Schwarz estimate, using \(\sum_{j\ge J}j^{-2}\le J^{-1}+J^{-2}\), yields

\[
\sum_{j\ge J}B_j
\le\left(\sum_{j\ge J}j^2 B_j^2\right)^{1/2}
\left(\sum_{j\ge J}j^{-2}\right)^{1/2}
\le\frac{\sqrt{3A}}{J}\sqrt{1+J^{-1}},
\]

which is (4). The leading \(\sqrt3\) factor is **optimal for this abstract nonnegative sequence lemma**: setting \(B_j^2=3A/j^4\) gives \(T_j\sim A/j^3\) and \(\sum_{k\ge J}B_k\sim\sqrt{3A}/J\). This does **not** imply sharpness of the Mandelbrot-specific constant (1).

For every dyadic frequency block, weighted Cauchy--Schwarz gives

\[
\sum_{n=2^j}^{2^{j+1}-1}|b_n|
\le B_j\left(\sum_{n=2^j}^{2^{j+1}-1}\frac1n\right)^{1/2}
\le B_j\sqrt{\log2+2^{-j}};
\]

the final inequality follows by integral comparison for the decreasing function \(1/x\). Sum over \(j\ge J\), use (4), and obtain (5). In particular, the Laurent series is **absolutely and uniformly convergent on the unit circle** whenever (3) holds. \(\square\)

### Theorem 1

If \(L=\limsup_{j\to\infty}j^3T_j=+\infty\), (1) is immediate. Otherwise \(L<\infty\). Fix \(A>L\). Then \(T_j\le Aj^{-3}\) for all sufficiently large \(j\). Lemma 2 implies \(\sum_n|b_n|<\infty\), so the uniform boundary value

\[
f(\theta)=e^{i\theta}-\tfrac12+\sum_{n\ge1}b_ne^{-in\theta}
\]

exists and equals the radial limit of \(\Psi\). Thus the **published landed external rays** give

\[
f(\theta_m)=c_m=-1+\tfrac14e^{2\pi i/m},\quad
f(\theta_\infty)=-\tfrac34,\quad
\delta_m=|\theta_m-\theta_\infty|=\frac{2\pi}{4^m-1}.
\]

Hence

\[
\lim_{m\to\infty}m|f(\theta_m)-f(\theta_\infty)|
=\lim_{m\to\infty}\frac m2\sin(\pi/m)=\frac\pi2.
\tag{6}
\]

Choose \(J_m=2m-\lceil\sqrt m\rceil\). By Gronwall and Cauchy--Schwarz, the contribution of the explicit \(e^{i\theta}\) term and of frequencies \(n<2^{J_m}\) to the difference satisfies

\[
\begin{aligned}
&|e^{i\theta_m}-e^{i\theta_\infty}|
+\sum_{n<2^{J_m}}|b_n|\cdot|e^{-in\theta_m}-e^{-in\theta_\infty}|\\
&\qquad\le \delta_m+
\delta_m\left(\sum_{n\ge1}n|b_n|^2\right)^{1/2}
\left(\sum_{n<2^{J_m}}n\right)^{1/2}\\
&\qquad\le\delta_m\left(1+\frac{2^{J_m}}{\sqrt2}\right).
\end{aligned}
\tag{7}
\]

The right side, multiplied by \(m\), goes to zero because \(2^{J_m}=4^m2^{-\lceil\sqrt m\rceil}\) and \(m2^{-\sqrt m}\to0\).

For the remaining frequencies, the elementary bound \(|e^{ix}-e^{iy}|\le2\) and Lemma 2 give

\[
\begin{aligned}
\left|\sum_{n\ge2^{J_m}}b_n(e^{-in\theta_m}-e^{-in\theta_\infty})\right|
&\le2\sum_{n\ge2^{J_m}}|b_n|\\
&\le\frac{2\sqrt{3A}}{J_m}\sqrt{(1+J_m^{-1})(\log2+2^{-J_m})}.
\end{aligned}
\tag{8}
\]

Multiply (7)--(8) by \(m\) and let \(m\to\infty\). Since \(J_m/m\to2\), the source landing separation (6) forces

\[
\frac\pi2\le \sqrt{3A\log2},\qquad
A\ge\frac{\pi^2}{12\log2}.
\]

This holds for every \(A>L\), hence \(L\ge\pi^2/(12\log2)\). Finally Gronwall's area equality yields \(A_N-\operatorname{Area}(M)=\pi E_N\). Along \(N_j=2^j-1\), \(\log N_j\sim j\log2\), giving (2). \(\square\)

## Interpretation and failure conditions

- (1) is **unconditional with respect to MLC**, not unconditional with respect to the classical published ray-landing and area inputs: if the limsup were finite, the hypothesized rapid decay would *itself* force a continuous boundary extension. If it is infinite, the result is immediate. The argument therefore does not assume the conjectural extension.
- This is a necessary constraint on **global area energy**, not a construction of a dynamically faithful marked-width carrier, a KKL Wave bound, or an MLC proof.
- It permits \(E_{2^j-1}=O(j^{-3})\) with a sufficiently large constant, but excludes \(o(j^{-3})\). It does **not** show the area tail has a lower bound at *every* scale, nor does it establish a matching upper bound.
- A short finite table cannot verify any limsup result. The companion script independently recomputes Laurent coefficients from the **published Ewing--Schober recursion** and checks deterministic finite arithmetic; it does not machine-prove Lemma 2, Claim 4.0, or the infinite limit.
- Contrast with PR #70's earlier **conditional best-degree approximation** bound \(\gtrsim (\log N)^{-1}\); (1) is a distinct, genuinely unconditional obstruction to *area-tail* convergence speed.

## Reproducibility and next research action

Run the companion verifier from the repository root (default 127 coefficients, or 511 for nine complete dyadic packets):

```sh
python research/independent_audits/verify_mlc_spectrum_extended.py --max-index 127
python research/independent_audits/verify_mlc_spectrum_extended.py --max-index 511 --check-manifest results/mlc_spectrum_exact_511_20261112.json
```

The exact recursion is independently checked against 28 published scaled integers in OEIS A331814, as well as the initial published rational coefficients. It yields finite packet energies, not a rate bound. The main unresolved positive target remains a uniform spectral Cauchy/cancellation certificate, compatible with the obligatory slow rates (1)--(2).

**Source index:** Bielefeld--Fisher--von Haeseler (1993) DOI `10.1006/aama.1993.1002`; https://archive.mpim-bonn.mpg.de/id/eprint/3259/1/preprint_1988_46.pdf ; Ewing--Schober (1992), *Numerische Mathematik* 61; OEIS A331814 at https://oeis.org/A331814 ; PR #70 and the parent file `mlc_boundary_spectral_program_20261111.md`.
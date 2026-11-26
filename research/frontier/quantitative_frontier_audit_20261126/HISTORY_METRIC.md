# Quantitative recovery of backward history

**Target:** The exact history theorem in [HISTORY.md](HISTORY.md) and the question of which actual marked observables suffice to distinguish histories. Fixed physical 3/9 tip only. No change to the ledger.

## 1. Two-sided exponential stability in an intrinsic analytic observable

Use the enlarged real interval \(I=[-29/20,5/4]\), invariant complex stadium \(U\), and inverse branches from HISTORY.md. Write \(J=[-11/10,11/10]\subset\operatorname{int}I\). For a normalized univalent chart define its pre-Schwarzian
\[
 B_H=H''/H'.
\]
This is unchanged by postcomposition with a nonconstant complex affine map; it determines the normalized chart uniquely on a connected domain (equality gives a constant derivative ratio and then equality at 0). All \(H_\eta\) are real on \(I\), by limits of real compositions.

There exist constants \(C_1,C_2>0\) and \(0<\beta,\lambda<1\) such that for distinct histories \(\eta,\zeta\) with longest common suffix of length \(k\),
\[
 C_1\beta^k\ \le\ \|B_{H_\eta}-B_{H_\zeta}\|_{C(I)}\
 \le\ C_2\lambda^k .                                     \tag{1}
\]
The constants need not be uniform over parameters and we do not assert explicit numerical values for \(C_1,\beta\).

**Compactness on the enlarged domain.** The chart family is compact in the compact-open topology on \(U\). Indeed normalized univalence gives normality on \(U\), and any sequence of histories has a convergent subsequence in the compact history space. The prior uniform suffix estimate on the original neighborhood of 0 identifies any analytic subsequential limit on \(U\) with the chart of that history, by the identity theorem. Thus the extension is continuous in this topology, including derivatives of each fixed order on compact subsets. Since every chart derivative is nonzero, the pre-Schwarzian family is likewise compact in the compact-open topology.

Let \(\mathcal D=\{B_{H_\xi}-B_{H_\upsilon}:\xi_1\ne\upsilon_1\}\). The opposite-last-letter set is a compact set of pairs. Hence \(\mathcal D\) is compact in the compact-open topology, and contains no identically zero function, by HISTORY.md and the normalization. The functions are real on \(I\).

**Uniform analytic finite-order detection.** There exist an integer \(M\ge0\) and \(\gamma>0\) such that
\[
 \max_{0\le j\le M}|D^{(j)}(x)|\ge\gamma\qquad
 (D\in\mathcal D,\ x\in J).
 \tag{2}
\]
Otherwise, for each \(m\) choose \(D_m,x_m\) with the first \(m\) derivatives all of magnitude less than \(1/m\). Compactness and Cauchy convergence of each fixed derivative give a limit \(D,x\) with every derivative zero at \(x\), contradicting the identity theorem. The family also has a finite common bound on \(|D^{(M+1)}|\) on \(J\).

For every nondegenerate closed real subinterval \(K\subset J\), there is a uniform \(c_0>0\) with
\[
 \sup_K |D|\ge c_0\min(1,|K|)^M.                           \tag{3}
\]
Here \(|K|\) denotes length. To prove this, first take \(\ell=|K|\le1\) and \(x\) its left endpoint. For \(M\ge1\) evaluate Taylor's formula at the \(M+1\) distinct points \(x+i\ell/M\), \(i=0,\ldots,M\). The fixed invertible Vandermonde matrix on the nodes \(i/M\) bounds the maximum of the scaled coefficients \(D^{(j)}(x)\ell^j/j!\) by a constant times \(\sup_K|D|+C\ell^{M+1}\). By (2) that maximum is at least \(\gamma\ell^M/M!\). For sufficiently small positive \(\ell\) the remainder is at most half the resulting lower bound. For larger intervals take a subinterval of that fixed small length. This yields (3) after decreasing \(c_0\). When \(M=0\) it follows directly from (2). Taylor's integral remainder is valid on the closed real segment; no assertion about the order of vanishing at a nonreal point is used.

Let \(m=\min_{j,x\in I}|\phi_j'(x)|>0\), and \(\lambda=3/4\), so \(m\le|\phi_j'|\le\lambda\). For any word \(w\) of length \(k\), the real map \(\phi_w\) is monotone, \(|\phi_w'|\in[m^k,\lambda^k]\) on \(I\), and for \(k\ge1\), \(\phi_w(I)\subset J\). By the pre-Schwarzian chain rule and exact normalized append relation,
\[
 B_{H_{\xi w}}-B_{H_{\upsilon w}}
     = (B_{H_\xi}-B_{H_\upsilon})\circ\phi_w\cdot\phi_w'.
 \tag{4}
\]
For distinct histories with longest common suffix \(w\), their preceding histories have opposite last letters. Thus \(D\in\mathcal D\). The upper bound in (1) follows from compact boundedness on \(I\). The image interval \(K=\phi_w(I)\) has length at least \(m^k |I|\); (3) and (4) give a lower bound of the form \(C_1 m^{(M+1)k}\) for \(k\ge1\). For \(k=0\), compactness, nonvanishing of \(\mathcal D\) and the identity theorem give a strictly positive minimum of the norm on \(I\). Decrease \(C_1\) to include this case. This proves (1) with \(\beta=m^{M+1}\).

In particular the inverse recovery of the past from its affine-invariant analytic data is Hölder, not merely continuous, in the standard binary suffix ultrametric \(2^{-k}\); the forward map is also Hölder. The norm in (1) is a full real-interval derivative observable, not a claimed uniform bound for an arbitrary finite set of measurements.

## 2. Finite native marker test for the most recent symbol

The prior physical audit identifies the pre-alpha attachment points \(e_p=\phi_p(\alpha)\) for finite words \(p\) as actual marks dense in the real end Cantor set, inside the original chart neighborhood. Let \(a_0=\alpha,\ a_1=-\alpha\) be two distinct actual anchors. Define the affine ratio
\[
 R_p(H)=\frac{H(e_p)-H(a_0)}{H(a_1)-H(a_0)}.
\]
The denominator does not vanish by univalence.

There exists a finite collection of actual words \(p_1,\ldots,p_N\) and \(\epsilon>0\) such that for every opposite-last-letter pair of charts
\[
 \max_i|R_{p_i}(H_\xi)-R_{p_i}(H_\upsilon)|\ge\epsilon.       \tag{5}
\]
Indeed if all ratios were equal for a pair, the two charts after their anchor affine normalization would agree on the dense set of actual pre-alpha attachments. This set has an accumulation point in their common analytic domain, so the identity theorem would make the normalized charts equal, contrary to HISTORY.md. Thus for every pair at least one ratio separates it. Continuity gives an open neighborhood of pairs on which that ratio difference has a positive lower bound. Compactness of the opposite-last-letter pair set gives a finite subcover, and the minimum of these finitely many positive bounds is positive. This is an existence theorem for a finite native marker test; we do not certify a particular finite word list or a numerical noise threshold.

## 3. Exact finite-depth readout using descendants

Equation (5) detects the last symbol from a finite marker vector, with a uniform gap. To read a preceding symbol, the last symbol already recovered determines the inverse branch to cancel. For example, \(H_{\xi j}=T_jH_\xi\) means \(H_{\xi j}\circ g\) on \(\phi_j(U)\)'s target is not the relevant cancellation formula; the correct identity on \(\phi_j(U)\) is
\[
 H_\xi(t)=D_{\xi,j} H_{\xi j}(g(t))+H_\xi(\phi_j(0)).
\]
Thus continuation of \(H_{\xi j}\circ g\) from this open set determines \(H_\xi\) up to affine normalization, but this requires analytic data outside a fixed finite vector. Alternatively, for any fixed depth \(d\), the distinct suffix classes of length \(d\) have compact disjoint chart images. Repeat the compactness argument of (5) on pairs with distinct length-\(d\) suffixes: there is a finite collection of *actual* pre-alpha marker ratios which detects those \(d\) symbols with a uniform positive separation. The number and choice of marks and the gap can depend on \(d\).

No finite truncated symbolic address, without other data, determines the entire chart. We have not proved that no fixed finite collection of **real-valued** marker ratios can be injective on the full history space; a finite real-valued vector can encode infinitely many bits. Nor have we established a uniformly bounded number of finite marker measurements, a numerical list for (5), an affine readout of every proof-used relative width, or a physical Wave realization. These distinctions are important: finite cardinality of a discrete state space is different from finite-dimensional continuous observations.

## Scope and attribution

The proof uses the new singularity injectivity result, the actual native attachment markers and the prior analytic graph compactification. Classical ingredients: Cauchy's derivative estimates, identity theorem, compactness, Taylor/Vandermonde interpolation and the pre-Schwarzian chain rule. The inverse stability and finite native marker separation are written consequences on this one physical tip; they do not prove H1, H2 calibration, H3, H4, or MLC. AI assistance: GPT-6.2; no independent human review or global novelty search.

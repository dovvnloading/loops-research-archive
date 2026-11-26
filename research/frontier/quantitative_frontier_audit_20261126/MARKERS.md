# One explicit physical attachment ratio recovers the full history

**Target:** the proof-used marking/observable interface at the end of the [analytic-history audit](../../independent_audits/decoration_analytic_history_end_blowup_20261126/NOTE.md), §8, and the unresolved explicit separating mark in its §4 equation (3). This is the strongest fixed-tip marker-level consequence of [SCALAR.md](SCALAR.md), not a statement about all protected Wave markings.

## 1. Three actual attachment points, one real ratio

Retain the source-realized 3/9 tip, \(a=-c_*\), \(g=f^2\), the two physical inverse branches and the normalized charts. The prior physical audit identifies the pre-alpha attachments \(e_p=\phi_p(\alpha)\), for finite words \(p\), and the anchors \(\alpha,-\alpha\). Choose the explicit ordered triple
\[
 x_0=\alpha,\qquad
 x_1=e_{LR}=\phi_L(\phi_R(\alpha))=\phi_L(-\alpha),\qquad
 x_2=-\alpha.
\]
All three are actual source-labelled points. They are strictly ordered: \(\phi_L\) is strictly increasing, \(\phi_L(\alpha)=\alpha\), and \(\phi_L(-\alpha)<0<-\alpha\). They lie in the real interval \(I_0\) of DIMENSION.md.

For a normalized limiting chart define the single physical affine ratio
\[
  R_\eta=\frac{H_\eta(x_1)-H_\eta(x_0)}
                  {H_\eta(x_2)-H_\eta(x_0)}\in(0,1).
\]
This ratio is invariant under nonconstant affine postcomposition. In contrast with the differential observable of SCALAR.md, it requires no derivative measurement: its three inputs are the chart images of explicitly identified actual attachment marks.

**Theorem.** The map \(\eta\mapsto R_\eta\) is injective. More precisely, for distinct histories with longest common suffix \(w\) there are constants \(C_-,C_+>0\), independent of the histories, such that
\[
 C_-|\phi_w'(0)|\le |R_\eta-R_\zeta|\le C_+|\phi_w'(0)|.       \tag{1}
\]
The image \(R(\Omega_-)\) is a compact real Cantor set of Hausdorff dimension equal to the physical end dimension, lying strictly between \(89/150\) and \(19/32\). Its correspondence with the pre-Schwarzian scalar set \(B_0\) is bi-Lipschitz. In fact the argument works for *any* three fixed distinct ordered real input points in \(I_0\); the triple above is a concrete native choice.

## 2. Proof from the uniformly ordered pre-Schwarzians

Let \(U=H_\eta,V=H_\zeta\), and write \(b_U=U''/U'\), \(b_V=V''/V'\). The interval certificate and identity in SCALAR.md §§2–3 imply more than separation at a point. If the predecessor of the common suffix \(w\) ends in L for \(\eta\) and R for \(\zeta\), the sign of \(b_U-b_V\) on the whole interval \(I_0\) is the sign of \(\phi_w'\). It is constant and never zero; reversing the histories reverses the sign. Indeed the sign of the predecessor difference is positive at every real input by the certified L/R separation, and \(\phi_w\) is monotone. By exchanging \(U,V\) if necessary, assume \(b_U>b_V\) everywhere.

Use the bounded distortion constant \(D\) of DIMENSION.md, \(\delta=1/200\), \(d_w=|\phi_w'(0)|\). SCALAR.md (1) gives uniformly on \(I_0\)
\[
       \delta D^{-1}d_w < b_U-b_V \le 4D d_w.              \tag{2}
\]
The empty suffix is included. Every chart is real on \(I_0\), univalent with \(H'(0)=1\), and hence \(H'(x)>0\) throughout the real interval (the derivative is real, continuous and never zero). As \(|b_H|<2\), integration from 0 shows
\[
       e^{-2r}\le H'(x)\le e^{2r},\qquad r=93/100 .
\]
The derivative ratio \(q=U'/V'\) therefore belongs to \([e^{-4r},e^{4r}]\), and
\[
 q'(x)=q(x)(b_U(x)-b_V(x)).
\]
By (2), for \(s<t\) in \(I_0\),
\[
 e^{-4r}\delta D^{-1}d_w(t-s)
 < q(t)-q(s)
 \le 4e^{4r}D d_w(t-s).                                   \tag{3}
\]

Put \(\ell_1=x_1-x_0,\ \ell_2=x_2-x_1,\ \ell=\ell_1+\ell_2\). Directly expanding the quotient difference by integrating derivatives gives
\[
 R(V)-R(U)=
 \frac{\displaystyle\int_{x_0}^{x_1}\int_{x_1}^{x_2}
       V'(s)V'(t)(q(t)-q(s))\,dt\,ds}
 {(U(x_2)-U(x_0))(V(x_2)-V(x_0))}.
\]
The numerator is strictly positive. The product of the derivative factors and the denominator can be bounded by \(e^{\pm4r}\) and \(\ell^2e^{\pm4r}\), respectively. Since the double integral of \(t-s\) is \(\ell_1\ell_2\ell/2\), (3) yields the concrete valid constants
\[
 C_- = e^{-12r}\delta D^{-1}\frac{\ell_1\ell_2}{2\ell},\qquad
 C_+ = 4e^{12r}D\frac{\ell_1\ell_2}{2\ell}.
\]
This proves (1), also when the histories were exchanged. These constants use a finite fixed-tip distortion constant, not a uniform-in-parameter bound. In particular the one chosen native ratio separates *all* histories, including histories differing arbitrarily far back, not just the two constant histories that the prior proof distinguished by multipliers. Continuity and compactness give a homeomorphism onto the ratio image.

The scalar pre-Schwarzian distances at 0 in SCALAR.md are also bounded above and below by fixed positive multiples of \(d_w\). Therefore the correspondence \(b_\eta(0)\mapsto R_\eta\) and its inverse are Lipschitz on their respective Cantor subsets of the real line. Hausdorff dimension is preserved by a bi-Lipschitz map (apply the elementary diameter inequality to any fine cover and to the inverse), and SCALAR.md §4 gives the asserted equality and bracket.

## 3. The order is the reflected binary order

There is an exact order consequence. Read a history from most recent to oldest, writing \(r_i=0\) for L and \(1\) for R, and set \(p_i=r_1\oplus\cdots\oplus r_i\) (with \(p_0=0\)). If two histories first differ at index \(i\), the sign of their pre-Schwarzian difference is determined by their distinct letters at that index and the common parity \(p_{i-1}\). This follows from (2) before taking absolute values and the positive derivative of L versus the negative derivative of R. The integral argument shows the ratio difference has the opposite sign. Consequently the order of \(R_\eta\) in the real line is exactly the lexicographic order of the parity sequence \(p_1,p_2,\ldots\) with \(0<1\). The map from histories to these sequences is bijective since \(r_i=p_i\oplus p_{i-1}\). Adjacent binary endpoints are not identified: (1) supplies a positive gap whenever the histories differ. This is an exact ordering law for the native marked affine geometries, not an assertion that their gaps have the sizes of a linear Cantor model.

## 4. Interpretation and limitations

A single real-valued ratio of three fixed actual attachment images is a sufficient statistic for the entire normalized affine chart. Together with the forward address and the independent ordered-sector parity it gives a homeomorphic representation of the previous graph boundary by \(\Omega_+\times R(\Omega_-)\times\mathbb Z/2\). For chart-dependent observables the reconstruction is continuous because the ratio map is a compact-to-Hausdorff homeomorphism onto its image. Thus the prior unresolved question about a finite collection of marked real ratios has a strong positive answer in this fixed native affine setting. A **finite discrete** state space still cannot suffice: one ratio is a real value ranging over a Cantor continuum.

This does not show that the ratio alone reconstructs ambient relative-cover sheet classes or additional obstacles outside the authorized chart, nor that it is a conformal invariant under arbitrary changes of root coordinates. It does not prove an effective uniform distortion constant across distinct parameters or levels, or authorize missing physical Wave roots. H1–H4, UPTCR and MLC remain open. The proof relies on the exact all-history interval certificate in SCALAR.md and its already stated source inputs; it is not a numerical scatterplot or an extrapolation from a finite history sample. AI-assisted proof development by GPT-6.2; no independent specialist review or priority claim.

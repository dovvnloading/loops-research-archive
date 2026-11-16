# Near-\(-2\) real primitive tips: ten independent physical certificates and an orbit-centred radial witness

**Audit 2026-11-16. Status: PARTIAL. The all-period realization and canonical KKL Wave width questions remain OPEN.**

This is an additive follow-up to [the merged conditional audit](../real_primitive_tip_family_uniform_20261116/NOTE.md). In particular the directory name \`unconditional\` **does not** claim that all requested hypotheses have been removed. Nothing below silently strengthens the old KKL/prime-end assumptions. The scripts are stand-alone; no existing files or native regenerators have been modified.

## Finite unconditional theorem: \(p=3,\ldots,12\)

Write \(f_c(z)=z^2+c,\ x_j=f_c^j(0),\ G=f_c^p\), and \(P_p(c)=x_{6p}+x_{3p}\). The target branch is the signed prefix \(x_1<0,\ x_2,\dots,x_p>0\), signed returns \(+--+-+\), and \(x_{3p}<0<x_{6p}\). **The equation \(P_p=0\) by itself does not select this branch.** At \(p=9\), for instance, another nearby root around \(-1.9999435233972100931\) has the wrong return itinerary. The mutation test uses this second root to check that the verifier actually rejects it.

**Theorem 1 (ten individually certified realizations).** For each integer \(3\le p\le12\), \`verify.py\` certifies precisely one root in the *specified rational seed interval*, \((s_p-10^{-75},s_p+10^{-75})\), by outward interval endpoint signs and a strictly negative enclosure of \(P_p'\) throughout the entire interval. It outputs adjacent \(2^{-256}\) rational brackets; this is **local** uniqueness, not uniqueness throughout the primitive window. At each certified root, the following strict orders hold:
\[
x_{2p}<x_{5p}<x_{3p}<0<x_{6p}<\alpha<x_{4p}<x_p,\quad G(\alpha)=\alpha,
\]
\[
-x_p<-x_{4p}<x_{2p}<x_{5p}<-\alpha<x_{3p}<x_{6p}<\alpha<-x_{5p}<-x_{2p}<x_{4p}<x_p.
\]
The intermediate real-image intervals prove the required monotonic two-sheeted restriction. Full complex images \(f_c^j(D(0,R_p))\), \(0\le j<p\), are enclosed by whole-disk bounds and are pairwise disjoint.

**Direct degree-two Rouché theorem for all ten periods, including \(p=3\).** Put \(R_3=1/4,\ R_p=2^{-p}\) for \(4\le p\le12\), \(U_p=D(0,R_p)\), and \(V_p=\operatorname{component}_0(G^{-1}(U_p))\). Writing \(G(z)=d_p+A_pz^2+E_p(z)\), the induction from squaring gives the deterministic whole-disk bounds
\[
d_{k+1}=d_k^2+c,\qquad A_1=1,\quad A_{k+1}=2d_kA_k,
\]
\[
T_{k+1}=2|d_k|T_k+(|A_k|R_p^2+T_k)^2,\quad T_0=0,
\qquad |E_p(z)|\le T_p\quad(|z|\le R_p).
\]
The interval program proves for **each** \(p=3,\dots,12\), strictly,
\[
m_p:=|A_p|_{\rm lower}R_p^2-|d_p|_{\rm upper}-T_p-R_p>\frac1{25}.
\]
Consequently \(A_pz^2\) dominates \(G(z)-w\) on \(|z|=R_p\) for *every* \(|w|\le R_p\). By Rouché, there are exactly two preimages in \(D(0,R_p)\) of every \(w\in U_p\); there are no boundary preimages, and the central critical component is a proper degree-two map \(G:V_p\Subset U_p\). This is a finite analytic result, not just real orbit evidence. **No all-\(p\) induction, uniform-in-\(p\) Rouché margin, or large-\(p\) error estimate is supplied.**

The new verifier independently rechecks the 10 target / 20 source marked labels, distinct covering \(f_*\) and immersion \(\iota^*\), the filtered crossing 2 vs avoiding 1 paths, edge-occurrence matrix
\[
M=\begin{pmatrix}0&0&1\\1&0&1\\1&1&0\end{pmatrix},\qquad \rho(M)=\frac{1+\sqrt5}{2},
\]
zero-old-edge crest types \(I_0,I_2,I_8\), and the **symbolic** two-half-width reciprocal identity. Actual ideal-boundary/KKL meaning still depends on the original slit/prime-end hypotheses.

## Source-defined radial witness, **not** the unrestricted canonical KKL Wave

The earlier \(W_p=\log(2-2/p)/(2\pi)\) originated in a freely selected inner/outer radius ratio. We replace that arbitrary *period formula* with a reproducible construction from **orbit data**. For the same five ordered cuts and fixed \(\alpha\), set
\[
m=(x_{2p}+x_{5p})/2,\quad
r_{\rm in}=(x_{5p}-x_{2p})/2,\quad
r_{\rm gate}=\min(-\alpha-m,\ x_{4p}+m).
\]
The radial circles \(|z-m|=r\) satisfy the two real endpoint gates \(q=m+r\in(x_{5p},-\alpha)\) and \(w=m-r\in(-x_{4p},x_{2p})\) *exactly* for \(r_{\rm in}<r<r_{\rm gate}\). Assuming the strict source cut order, for any period \(p\),
\[
(-\alpha-m)-r_{\rm in}=-\alpha-x_{5p}>0,\qquad
(x_{4p}+m)-r_{\rm in}=x_{4p}+x_{2p}>0,
\]
hence that *conditional real gate* is always nonempty. The midpoint convention makes this maximal only **among round leaves with that prescribed centre**, not maximal among all KKL admissible Waves. It is invariant under positive affine rescaling of the marked real coordinate but **not** intrinsic to the KKL geometry.

For **each** of the ten independently certified physical maps, the active upper gate is \(-\alpha-m\). The whole closed disk \(D(m,r_{\rm gate})\) maps strictly inside \(U_p\) with lower disk-image margin \(>(2/5)R_p\), and the real centre is connected to the central component, so the circles in this open gate are valid physical circular crossing witnesses. The avoiding comparison disk is also checked. Their radial logarithmic aspect ratio has the exact *definition*
\[
W_p^{\rm radial}:=\frac{1}{2\pi}\log(r_{\rm gate}/r_{\rm in}).
\]
A robust integer-interval bound holds at **every** tested parameter:
\[
\frac{\log(24/5)}{2\pi}<W_p^{\rm radial}<
\frac{\log(26/5)}{2\pi},\qquad 3\le p\le12.
\]
Some strict radius-ratio enclosures (the program calculates a millionth bracket separately for every period):

| \(p\) | \(r_{\rm gate}/r_{\rm in}\), strictly between |
|:---:|:---|
| 3 | 4.861313 and 4.861314 |
| 4 | 5.073489 and 5.073490 |
| 6 | 5.134400 and 5.134401 |
| 8 | 5.138064 and 5.138065 |
| 10 | 5.138292 and 5.138293 |
| 12 | 5.138307 and 5.138308 |

**These finite bounds neither prove all-period nondegeneration nor decide the asymptotic growth/decay of the maximal KKL Wave.** The analytic logarithmic-rectangle identification required to turn these radial coefficients into actual extremal widths is the old conditional input. In particular a lower bound for a particular radial family is *not* a proof of the canonical maximal KKL Wave width, canonical WAD weight, or asymptotic equivalence.

## Hostile review: correction to the merged note

The former theorem's prose incorrectly says all three filtered source paths have three-atom short arcs. The actual source short-arc lengths are **3, 3, 7**:
- crossing \((S_3,S_1)\): \([1,2,3]\);
- crossing \((S_{19},S_{17})\): \([17,18,19]\);
- avoiding \((S_3,S_{17})\): \([17,18,19,0,1,2,3]\).

Under the separate *covering*, the corresponding target short-arc lengths are **3, 3, 5**, not three in every case. The old verifier only checked the weaker, correct predicate \(\operatorname{length}>2\). Its finite 2-versus-1 conclusion survives; its prose's **three/three/three length assertion does not**. Both the new Python arithmetic and the new Lean decidable shadow explicitly check the corrected counts. No old file was changed.

## Scope, reproducibility and explicit remaining research debt

From repository root:

\`\`\`bash
python research/independent_audits/real_primitive_tip_family_unconditional_20261116/verify.py
python -m unittest discover -s research/independent_audits/real_primitive_tip_family_unconditional_20261116 -p 'test_*.py' -v
lake env lean research/independent_audits/real_primitive_tip_family_unconditional_20261116/RealPrimitiveTipUnconditionalDiscrete.lean
\`\`\`

\`verify.py\` uses Python standard-library \`Fraction\` and an outward \(2^{-512}\) integer interval grid, never floating-point as a proof oracle, and never imports the native Wave regenerators. The decimal seeds are **not** assumed roots: rational endpoint signs, derivatives and all orbital predicates are checked. The checked-in \`results.json\` is verified **byte-for-byte** in read-only mode; \`--write\` is solely for deliberate regeneration. \`test_verify.py\` mutates seeds, polynomial-branch choice, matrix, and immersion labels. The dedicated CI workflow runs these plus the old six-period regression, mirrors existing research-validation commands and checks Lean's finite model. Lean does not formalize complex Rouché analysis or claim a canonical conformal width.

The tasks **not solved** are: (1) existence and uniqueness of this specified tip branch over the *entire* real primitive window for all \(p\ge3\) or every \(p\ge p_0\), plus explicit uniform high-\(p\) Rouché/modulus bounds; (2) identification and asymptotic analysis of the **unrestricted** KKL-maximal Wave or canonically renormalized conformal-width invariant, including bounded-below/vanishing/growth classification and rate; and (3) the deeper prime-end/complete Julia tree identifications imported by the original conditional theorem. The archive has ten finite physical certificates and a conditional all-period real-gate identity, **not** an unconditional all-period uniform-tip or canonical-width theorem.

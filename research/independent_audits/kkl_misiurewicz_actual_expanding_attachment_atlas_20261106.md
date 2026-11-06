# Issue #40 — an exact *periodically repelling* quadratic attachment/prime-end/incidence certificate

**Date:** 2026-11-06.  
**Result:** explicit connected **Misiurewicz quadratic** \(P_c\), its genuine postcritical Hubbard tree \(T\subset P_c^{-1}(T)\), complete excess branch, exact source/target conformal prime-end charts, the source-defined inclusion-immersion pullback for open/closed inputs, and an edge-incidence matrix with **Perron root \(\sqrt2>1\)** derived from those same maps.  
**Status:** a rigorously analytic **control / positive realization in a periodically repelling quadratic stage**. It is **not** a primitively renormalizable prime KKL stage, is not a KKL-native-category counterexample, and does not close the bounded-visits interval-growth or full Wave theorem.

**References:** Kahn–Kapiamba–Lyubich [arXiv:2606.27272v1](https://arxiv.org/html/2606.27272v1), §2.1 (quadratic-like \(\psi\)-ql pairs), §2.5 (Hubbard edge incidence, inverse sheets and the non-LC lift), Proposition 6.5 (full attached branch boundary for **separate open and closed** interval inputs), Appendix A.3.2–A.3.4 (proper-path immersion restriction and closed-input warning). The exact identities below are proved directly from the explicit real polynomial, not imported as a black box. Companion [basilica branch model](./kkl_basilica_actual_immersion_attachment_atlas_20261106.md) has an attracting period-two cycle and \(\lambda=1\); this new example removes **both** deficiencies but still lacks prime primitive renormalization.

## 1. Exact repelling/preperiodic parameter and postcritical Hubbard hull

Let \(c\) be the **unique real root** of
\[
H(c)=c^3+2c^2+2c+2=0,\qquad -\tfrac85<c<-\tfrac32,
\tag{1.1}
\]
and set
\[
P=P_c(z)=z^2+c,\qquad b=c^2+c,\qquad
\alpha=-b.
\tag{1.2}
\]
The derivative \(H'(c)=3(c+\frac23)^2+\frac23>0\) gives uniqueness; \(H(-8/5)<0<H(-3/2)\) gives the interval. Therefore \(c<-3/2\), \(3/4<b<-c\), and
\[
b^2+c+b
=c\bigl(c^3+2c^2+2c+2\bigr)=0.
\tag{1.3}
\]
The actual critical orbit is
\[
\boxed{0\ \longmapsto\ c\ \longmapsto\ b\
\longmapsto\ \alpha=-b\ \longmapsto\ \alpha.}
\tag{1.4}
\]
The fixed point \(\alpha\) is repelling:
\[
|P'(\alpha)|=2b>3/2>1.
\tag{1.5}
\]
In particular \(P\) is a real **Misiurewicz polynomial** with strictly preperiodic critical orbit, and its connected filled Julia set has no attracting periodic cycle. Standard postcritically finite polynomial theory gives that its periodic cycles are repelling. The old terminal vertex \(x=b\) is exactly the **other preimage of this repelling fixed point** \(\alpha\):
\[
P(\alpha)=P(b)=\alpha,\qquad \alpha\ne b.
\tag{1.6}
\]
This is a genuinely holomorphic realization of the **second-preimage-of-a-repelling-vertex candidate** discussed in the KKL critical-root audit, but it does **not** identify the root of KKL Proposition 6.8 for an arbitrary primitive renormalization.

The actual minimal real hull of the finite postcritical set and its entire inverse tree are
\[
\boxed{
T=[c,b],\quad P(T)=T,\quad
T'=P^{-1}(T)=[c,-c],\quad X=T'\setminus T=(b,-c].
}
\tag{1.7}
\]
The equality \(P(T)=T\) follows because the critical minimum on \([c,b]\) is \(c\), and the maximum occurs at \(z=c\) with \(P(c)=b\). The full preimage is real because \(z^2=P(z)-c\in[0,b-c]=[0,c^2]\), hence \(z\in[c,-c]\). There is exactly **one** added component \(X\), attached at the old **tip** \(x=b\); \(x\) is not the critical point \(0\).

Choose \(U=D(0,3)\) and \(U'=P^{-1}(U)\), which is a Jordan disk containing the connected filled Julia set. Since \(|z|^2<3+|c|<5\) on \(U'\), \(U'\Subset U\). Thus \((P,\mathrm{inclusion}):U'\rightrightarrows U\) is a real quadratic-like/\(\psi\)-ql stage. The **two actual complements** are \(V=U\setminus T\) and \(V'=U'\setminus T'\), with holomorphic covering \(P:V'\to V\) and separate nonproper inclusion immersion \(\iota:V'\hookrightarrow V\).

## 2. Same polynomial gives the complete source and target prime-end charts

Let \(C',C\) be the inner Carathéodory access circles of \(V',V\). Their exact Joukowski slit-uniformizations are
\[
\begin{split}
\Psi_{T'}(w)&=-\frac c2(w+w^{-1}),\\
\Psi_T(u)&=\frac{c+b}{2}+\frac{c^2}{4}(u+u^{-1}),
\qquad |w|,|u|>1.
\end{split}
\tag{2.1}
\]
They are conformal in collars of the **real slit domains**; the outer boundary curves of \(U',U\) need not be circular. The exact identity
\[
\boxed{
P\bigl(\Psi_{T'}(w)\bigr)
=c+\frac{c^2}{4}(w^2+2+w^{-2})
=\Psi_T(w^2)
}
\tag{2.2}
\]
uses \(b=c^2+c\). Therefore the actual boundary covering \(p=f_*\) is, in these genuine prime-end coordinates,
\[
\boxed{p(s)=2s\pmod1.}
\tag{2.3}
\]

The landing projections (defined here because both carrier slits are locally connected) are
\[
L_{T'}(s)=(-c)\cos(2\pi s),\qquad
L_T(t)=\frac{c+b}{2}+\frac{c^2}{2}\cos(2\pi t).
\tag{2.4}
\]
The old target **tip** \(x=b\) corresponds to **one** target prime end \(t=0\). Define the actual source gate angle
\[
\theta:=\frac{1}{2\pi}\arccos\frac{b}{-c}
=\frac{1}{2\pi}\arccos(-c-1),
\quad 0<\theta<\frac14.
\tag{2.5}
\]
There are **two different source prime ends** \(s=\theta\) and \(s=1-\theta\), both landing at the single planar \(x=b\). The entire added branch \(X=(b,-c]\), with its two physical side-access traces, occupies precisely
\[
\boxed{B_X=[1-\theta,1]\cup[0,\theta]\subset C'.}
\tag{2.6}
\]
It has normalized angular span \(2\theta\), and its two limiting access gates are \(\theta,1-\theta\). This is a direct analytic Carathéodory-boundary census, including root gates and the far endpoint access.

The source old-tree portion is the complementary arc \([\theta,1-\theta]\), whose two old physical side traces are \((\theta,\tfrac12)\) and \((\tfrac12,1-\theta)\). These are actual complement-access arcs, not abstract graph atoms.

## 3. Full immersion pullback on open versus closed source markings

Take the **actual two-side ideal marking** on the old target segment:
\[
I_+=(0,\tfrac12),\qquad I_-=(\tfrac12,1)
\tag{3.1}
\]
(the two intervals are upper and lower physical slit sides; they are a valid ideal marking of this example, **not** asserted to be the KKL original small-Julia vertex-side marking).

The real embedded contour also determines an order-preserving degree-one **coding map** \(q:C'\to C\): on the old source sides it is uniquely obtained by matching the physical landing points and their upper/lower sides; on the entire added block \(B_X\) it is constant with value 0 (the old tip access). For completeness, if
\[
R(s):=\frac{2(-c)\cos(2\pi s)-(c+b)}{c^2},
\tag{3.2}
\]
the code is
\[
q(s)=
\begin{cases}
0\pmod1,&s\in[1-\theta,1]\cup[0,\theta],\\
(2\pi)^{-1}\arccos R(s),&s\in[\theta,\tfrac12],\\
1-(2\pi)^{-1}\arccos R(s),&s\in[\tfrac12,1-\theta].
\end{cases}
\tag{3.3}
\]
The formulas join continuously at the true gates and at \(s=1/2\), and \(q\) is monotone and degree one. **It is not a pointwise prime-end boundary extension of the holomorphic inclusion \(\iota\)**: source paths approaching interior points of \(X\) cease to be proper target paths. This q is a *derived contour/access code* only, not a general axiom for KKL immersions.

### Theorem 3.1 (actual two-sheet and attachment-complete \(\iota^*\))

For the real source immersion \(\iota=\mathrm{inclusion}\), its maximal proper-path boundary restriction for the marked open inputs and **separately** their closures is exactly
\[
\boxed{
\begin{aligned}
\iota^* I_+&=(\theta,\tfrac12),&
\iota^*\overline{I_+}
   &=[1-\theta,1]\cup[0,\tfrac12],\\
\iota^* I_-&=(\tfrac12,1-\theta),&
\iota^*\overline{I_-}
   &=[\tfrac12,1]\cup[0,\theta].
\end{aligned}
}
\tag{3.4}
\]
Thus the complete \(B_X\) (rather than just a point or one side) is **born at the closed old tip** \(t=0\). These results agree with \(q^{-1}(J)\) for the four checked marked sets \(J\), but no global pointwise \(\iota\)-boundary map is inferred.

**Proof.** The real coordinate (2.4) identifies the complete old upper/lower side traces exactly as in (3.4). The only excess component of \(T'\setminus T\) is \(X\), with one planar root \(x=b\), and its full prime-end boundary is the block \(B_X\) of (2.6). The root tip access \(t=0\) belongs to **neither open** side atom \(I_\pm\) but belongs to **both closures**. In terms of the genuine source-defined path-subordination relation of KKL Appendix A.3.2 and the complete-branch rule of Proposition 6.5, the old side remains in the immersion restriction, and the entire attached \(B_X\) is inserted precisely for inputs containing the tip access. There is no other attachment component to add, and the opposite old side is excluded by its distinct physical proper-path class. This proves all four formulas and their maximality. The explicit q from the *same actual slits* independently confirms their contour order; it was **derived after** the geometry, not chosen to prescribe it. \(\square\)

### Theorem 3.2 (strict endpoint-triggered saturation, now with a repelling polynomial)

For the same **actual** covering \(p(s)=2s\), the open upper-side image is proper:
\[
F_*I_+=p((\theta,\tfrac12))=(2\theta,1).
\tag{3.5}
\]
The *closed* source interval, whose source angular lift runs from \(1-\theta\) to \(3/2\) and has length \(1/2+\theta>1/2\), saturates:
\[
F_*\overline{I_+}=C.
\tag{3.6}
\]
Therefore
\[
\boxed{
F_*\overline{I_+}=C\ne
[2\theta,1]=\overline{F_*I_+}.
}
\tag{3.7}
\]
The same phenomenon occurs for the lower side. This realizes KKL Appendix A.3.4's open/closed warning with an **actual Misiurewicz quadratic having repelling periodic dynamics**, not only with an attracting example or synthetic circle covering.

**Proof.** Apply (2.3) to the genuinely derived immersion intervals (3.4), using \(0<\theta<1/4\). The open source interval has angular span \(1/2-\theta<1/2\) and therefore maps injectively to the proper target arc \((2\theta,1)\). The closed source interval includes the *whole* attached branch contour and has span \(1/2+\theta>1/2\); the degree-two covering necessarily maps it onto the entire target circle. The closure of the proper open target arc is \([2\theta,1]\ne C\), yielding (3.7). \(\square\)

**Distinction:** The full closed \(\iota^*\) adds a positive-length prime-end block, not merely an endpoint of angular measure zero. This is **genuinely immersion-born** attachment mass; the covering merely transports and saturates it. Under the original source's proper-path definition, discarding this \(B_X\) is wrong even though all planar roots are known.

## 4. Exact expanding edge incidence from these very same maps

The old real postcritical Hubbard interval has the four **actual distinguished points**
\[
c < \alpha=-b < 0 < b.
\tag{4.1}
\]
Refine its graph at these actual postcritical and critical points, producing three monotone edges
\[
A=[c,\alpha],\qquad B=[\alpha,0],\qquad D=[0,b].
\tag{4.2}
\]
The **same polynomial** has the exact endpoint maps
\[
P(c)=b,\quad P(\alpha)=\alpha,\quad P(0)=c,\quad P(b)=\alpha.
\tag{4.3}
\]
It is monotone on each chosen edge, hence the actual edge traversals are
\[
A\longmapsto B\,D,\qquad
B\longmapsto A,\qquad
D\longmapsto A.
\tag{4.4}
\]
(The image of \(A\) is the interval \([\alpha,b]\) traversed once, while each of \(B,D\) maps homeomorphically to \([c,\alpha]\).)

With **row = source edge**, **column = target edge**, the exact access/graph incidence is
\[
\boxed{
M=
\begin{pmatrix}
0&1&1\\
1&0&0\\
1&0&0
\end{pmatrix},
\qquad
w=(\sqrt2,1,1)^\top>0,\qquad Mw=\sqrt2\,w.
}
\tag{4.5}
\]
Thus the **genuine holomorphic graph system has strict Perron eigenvalue**
\[
\boxed{\lambda=\sqrt2>1.}
\tag{4.6}
\]
The directed graph has period two, so \(M\) is **irreducible but not primitive**. This is not KKL's specific \(T_F\) for a prime primitive *small-Julia-cycle* Hubbard tree; it is the **Markov-refined postcritical Hubbard graph** of the actual repelling Misiurewicz quadratic.

The full actual preimage of **each** target edge has precisely two holomorphic monotone strips; their old/new partition is obtained directly by solving \(z^2=y-c\):

| Target edge | Preimage strip(s) within old \(T\) | Preimage strip(s) in added \(X\) |
| --- | --- | --- |
| \(A=(c,\alpha)\) | \(B=(\alpha,0)\), \(D=(0,b)\) | none |
| \(B=(\alpha,0)\) | negative portion of \(A=(c,\alpha)\) | positive portion of \(X=(b,-c)\) |
| \(D=(0,b)\) | complementary negative portion of \(A\) | complementary positive portion of \(X\) |

The old preimage counts are \((2,1,1)\) in target order \((A,B,D)\), agreeing with the **column sums** of (4.5), and the added counts are \((0,1,1)\). Each total is **exactly two**. On each strip \(P'(z)=2z\ne0\), so the two physical side germs transfer biholomorphically to the corresponding target edge-side germ, with side orientation reversed on the negative branch and preserved on the positive one. The exact Carathéodory source and target coordinates in §2 provide these same access-side traces; there is no disconnected edge automaton.

**Proof of the strip partition.** Over the first target edge \((c,\alpha)\), the solutions of \(z^2=y-c\) satisfy \(|z|\in(0,b)\), giving the two **old** source edges \(B,D\), since \(b^2+c=\alpha\). Over \((\alpha,b)\), they satisfy \(|z|\in(b,-c)\). The negative preimage branch lies in the old edge \(A=[c,\alpha]\), and the positive branch in the added component \(X=(b,-c]\). Splitting the target interval at 0 separates \(B,D\), but does not change the counts. Each source segment is an actual holomorphic inverse branch of the *same* polynomial appearing in (2.2) and (3.4). This proves the table and (4.5). \(\square\)

**Why this matters for Issue #40:** Even in this **expanding** actual edge-incidence realization (\(\lambda>1\)), the genuine *closed* endpoint pullback can jump to the full prime-end circle as in (3.7). A Perron weight cannot replace the \(\iota^*\) attachment census or open/closed Wave crest audit. Conversely, a source-full branch boundary plus the real cover gives the exact incidence without a synthetic transition table.

## 5. Native-category boundary and next analytic gate

What is **proved** here from one real polynomial:
- true quadratic-like pair, periodically repelling postcritical map;
- genuine old and complete inverse Hubbard segments, one excess branch rooted at the **second preimage of a repelling fixed point**;
- explicit \(f_*\) annular-cover coordinates and **derived** immersion access coding;
- full \(B_X\) with its two distinct prime-end gates, proper-path open/closed membership, strict \(F_*\overline I\ne\overline{F_*I}\);
- the two complete inverse edge strips for each target Markov edge, and expanding \(3\times3\) edge-incidence **with multiplicities** from exactly the same maps.

What is **not** proved: that every genuine primitive KKL root \(x\) equals \(\alpha_F'\), that the actual non-LC small-Julia contact impressions have these slit crosscuts, that the KKL vertex-side marking agrees with this auxiliary postcritical Markov refinement, that all zero-weight sectors escape, or that true **closed Wave crests** obey the corrected interval-growth inequalities. The graph here is irreducible but imprimitive, and this is **not** a prime primitive renormalization.

**Status:** a stronger rigorous *periodically repelling* quadratic geometric realization/control, **not** the Issue #40 acceptance theorem or native-category counterexample. Keep Issue #40, KKL_BOUNDED_VISITS_INTERVAL_GROWTH_REPAIR, KKL_PARABOLIC_WAVE_AMPLIFICATION, and global MLC **OPEN**. No synthetic interval simulation or independent specialist verification has been claimed.

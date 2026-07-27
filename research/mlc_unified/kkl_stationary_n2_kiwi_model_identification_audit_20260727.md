# Gate N2: Kiwi model identification and quotient-level audit

**Date:** 2026-07-27  
**Scope:** KKL stationary line-1598, non-locally-connected model lift  
**Status:** one point-collapse obstruction proved; exact KKL/Kiwi model
identification open  
**Global status:** Gate N2, VAAPC-I, UPTCR, and MLC remain open

## 1. Question audited

The previous sufficient package \(\mathrm{MFL}_H\) used a monotone
semiconjugacy
\[
 \pi:K(F)\longrightarrow K(F)_{\rm com}
\]
and, in its first formulation, required
\[
 \pi(K_i)=\{\bar v_i\}
\tag{1.1}
\]
for every primitive small-Julia continuum \(K_i\).

The audit asks two separate questions.

1. Which parts of the monotone-model package follow from a complete
   primary theorem after passing from KKL's \(\psi\)-quadratic-like map
   to an ordinary quadratic-like restriction and straightening it?
2. Is the point-valued clause (1.1) compatible with that theorem?

The answer to the second question is **no**.  Clause (1.1) conflates
the geometric rational-lamination projection with a later finite-tree
quotient.

## 2. Locked and primary sources

### 2.1 KKL

`research/mlc_unified/.tmp_wave_audit/waves-with-Misha.tex`

SHA-256:
`AD4C774806D9902AA54FA31C56AD6146D8034946F19CC5E9CEC3C51A3F94FDD5`

Relevant lines:

- 451--457: same-filled-continuum quadratic-like restriction;
- 478--490: the physical primitive small-Julia cycle;
- 497--504: physical limbs and their dynamics;
- 514--520: the \(K_i\) are continuum-vertices of the geometric
  Hubbard carrier, followed by an abstract finite-tree encoding;
- 542--543: a locally connected rational-lamination model, a natural
  projection, descent of \(F\), and an instruction to lift the
  corresponding objects.

### 2.2 Dudko-Lyubich

`research/mlc_unified/.tmp_wave_audit/dl23/Feigen.tex`

SHA-256:
`EB8C50CC51039A82317CF1951B1E333F23DF100773F8AD0DF0586AC7CD465DDF`

Relevant lines:

- 938--942: straightening for a connected quadratic-like map;
- 953--958: locally connected combinatorial model and a natural
  semiconjugating projection;
- 968--970: lifting the model Hubbard dendrite to a Hubbard continuum;
- 973--978: a geodesic continuum is explicitly the full inverse image
  of a model arc.

### 2.3 Kiwi

Jan Kiwi, *Real laminations and the topological dynamics of complex
polynomials*, Advances in Mathematics 184 (2004), 207--267,
[DOI](https://doi.org/10.1016/S0001-8708(03)00144-0);
[full article](https://www.academia.edu/91433960/Real_laminations_and_the_topological_dynamics_of_complex_polynomials).

The primary-source check uses:

- Theorem 2, pp. 209--210;
- Proposition 4.2, pp. 233--234; and
- Theorem 5.12, pp. 243--244.

For a polynomial with connected Julia set and no irrationally
indifferent cycle, Theorem 5.12 supplies the monotone semiconjugacy to
the real-lamination model and states that its restriction to the set
of finite-orbit Julia points is a homeomorphism onto its image.
The full-fiber conclusion uses the additional source chain:
Theorem 2 proves \(\operatorname{Fiber}(z)=\{z\}\) for every
periodic or preperiodic \(z\); Proposition 4.2 defines the quotient
\(q\) by the fiber equivalence; and the proof of Theorem 5.12 states
\(h=\widehat w^{-1}\circ q\).  Consequently
\[
 h^{-1}(h(z))=\{z\}
\]
for every periodic or preperiodic \(z\).

The active KKL map is periodically repelling.  Its same-filled
quadratic-like restriction has connected filled Julia set, and its
straightening has no irrationally indifferent cycle.  Thus Kiwi's
theorem applies to the straightened polynomial.  Transport through
the straightening gives an existential monotone model for the KKL
filled continuum.

This does **not** yet identify the transported Kiwi map with the
specific projection denoted \(\pi\) at KKL lines 542--543.

## 3. Clause-by-clause audit

| desired clause | source-checkable result | unresolved identification |
|---|---|---|
| continuous monotone surjective semiconjugacy onto a locally connected model | Kiwi Theorem 5.12, transported through the same-filled restriction and straightening | equality with KKL's named natural projection |
| locally connected target | Kiwi Theorem 5.12, transported through the same-filled restriction and straightening | the dendrite property required by Proposition 4.5 and equality with KKL's precise rational-lamination model |
| singleton full fibers at periodic and preperiodic points | Kiwi Theorem 2, Proposition 4.2, and \(h=\widehat w^{-1}\circ q\) in the proof of Theorem 5.12 | equality of the transported labels with KKL's selected \(\bar\alpha^n\) |
| singleton selected predecessor fibers | the preceding source chain applies to every transported preperiodic predecessor | equality of transported predecessors with KKL's selected predecessors |
| \(T=\pi^{-1}(T_{\rm com})\) | DL uses full inverse images for individual geodesic continua | neither DL nor KKL writes the global carrier equality with every proof-used marking |
| selected-sheet correspondence | singleton root fibers give a punctured-component bijection once the correct physical and model roots are identified | identification of KKL's \(Q_n\)-selected \(\Omega_n\) with the transported component |
| small-Julia correspondence | the continuum-valued clause \(\pi(K_i)\subset\bar K_i\) is compatible with Kiwi | proof that the image is KKL's predetermined geometric model continuum |

No exact KKL clause is promoted by this table.  It isolates the
remaining issue as a model-identification theorem, not as existence of
some monotone model.

## 4. Point-collapse obstruction

### Proposition 4.1

Let \(\pi_{\rm Kw}\) be the monotone semiconjugacy on \(K(F)\) obtained
by transporting Kiwi's model through KKL's same-filled
quadratic-like restriction and a straightening.  Let
\[
 \mathcal K=\{K_0,K_1,\ldots,K_{P-1}\},
 \qquad K_i=F^i(K_0),
\]
be the nondegenerate primitive small-Julia cycle of period \(P\).
Then
\[
 \#\pi_{\rm Kw}(K_i)\ge2
 \qquad(0\le i<P).
\tag{4.1}
\]
In particular, \(\pi_{\rm Kw}\) cannot collapse \(K_i\) to a point.
A later carrier-tree quotient may collapse the nondegenerate geometric
image to an abstract vertex \(\bar v_i\), but that is a different map.

### Proof

Let
\[
 G=F^P:V'\longrightarrow V
\]
be the quadratic-like renormalization whose filled Julia set is
\(K_0\).  Straighten \(G\) to a quadratic polynomial
\[
 P_c(z)=z^2+c.
\]
The two finite fixed points of \(P_c\) are the roots of
\[
 z^2-z+c=0.
\tag{4.2}
\]
They both lie in \(K(P_c)\), because their forward orbits are constant.
They are distinct.  Indeed, equality of the two roots is equivalent
to
\[
 1-4c=0,
\]
so \(c=1/4\) and the repeated fixed point is \(z=1/2\), whose
multiplier is
\[
 P_c'(1/2)=1.
\]
The filled Julia set \(K(P_{1/4})\) contains the open immediate
parabolic basin.  A global quasiconformal straightening takes \(K_0\)
onto \(K(P_c)\) and preserves ambient interior.  Periodic repulsion,
the same-filled quadratic-like restriction, and the
no-wandering-domain theorem give
\(\operatorname{int}K(F)=\varnothing\); since \(K_0\subset K(F)\),
the case \(c=1/4\) is impossible.

The straightening conjugacy therefore transports the two fixed points
to distinct points \(x_0,y_0\in K_0\) satisfying
\[
 F^P(x_0)=x_0,\qquad F^P(y_0)=y_0.
\tag{4.3}
\]
For \(0\le i<P\), put
\[
 x_i=F^i(x_0),\qquad y_i=F^i(y_0).
\]
Both belong to \(K_i\) and have finite \(F\)-orbits.  They are
distinct: if \(x_i=y_i\), applying \(F^{P-i}\) would give
\(x_0=y_0\), contrary to construction.

Here is the missing domain check.  The active KKL map is periodically
repelling, so the same-filled quadratic-like restriction and the
no-wandering-domain theorem give
\(\operatorname{int}K(F)=\varnothing\), hence \(K(F)=J(F)\).
In particular the \(F\)-periodic points \(x_i,y_i\) lie in the
finite-orbit Julia set on which Kiwi's theorem is injective.

Kiwi Theorem 5.12 is injective on finite-orbit points.  Hence
\[
 \pi_{\rm Kw}(x_i)\ne\pi_{\rm Kw}(y_i).
\]
Both points lie in \(\pi_{\rm Kw}(K_i)\), proving (4.1). \(\square\)

## 5. Correct quotient typing

There are two maps:

\[
\begin{CD}
 T @>{\pi_{\rm geom}|_T}>> T_{\rm com}\\
 @. @V{r_T}VV\\
 @. |G_{\rm com}|.
\end{CD}
\]

Here:

- \(\pi_{\rm geom}\) is the monotone geometric model projection;
- \(\bar K_i\subset K(F)_{\rm com}\) is a geometric continuum; and
- \(r_T:T_{\rm com}\to|G_{\rm com}|\) is the carrier-tree quotient,
  with \(r_T(\bar K_i)=\bar v_i\).

No quotient or retraction from all of \(K(F)_{\rm com}\) to
\(|G_{\rm com}|\) is asserted.

The corrected model-lift condition is
\[
 \pi_{\rm geom}(K_i)\subset\bar K_i,
\tag{5.1}
\]
not point collapse.  Model pruning must first prove
\[
 \bar K_i\subset L_{0,\rm com}^n.
\tag{5.2}
\]
Together with
\[
 \pi_{\rm geom}^{-1}(L_{0,\rm com}^n)=L_0^n,
\tag{5.3}
\]
equations (5.1)--(5.3) give
\[
 K_i\subset L_0^n.
\]

## 6. Chosen sufficient identification theorem

The maximal source-checkable existential conclusion used here is:

> A periodically repelling KKL map admits, after the same-filled
> quadratic-like restriction and straightening, a monotone
> semiconjugacy to a locally connected model whose restriction to the
> finite-orbit Julia set is injective and whose complete fibers at
> periodic and preperiodic points are singletons.

The dendrite target and the marked identification with KKL's model
remain separate hypotheses in the present audit.

One source-exact sufficient identification package for the
monotone-full-lift route is:

\[
\boxed{
\begin{gathered}
\exists\,\text{a marked dynamical homeomorphism }
J:K_{\rm Kw,com}\longrightarrow K_{\rm KKL,com}
\text{ with }J\circ\pi_{\rm Kw}=\pi_{\rm KKL},\\
T=\pi_{\rm KKL}^{-1}(T_{\rm com}),\\
\pi_{\rm KKL}(Q_n)\subset\bar\Omega_n,\\
\pi_{\rm KKL}(K_i)\subset\bar K_i,
\end{gathered}}
\tag{6.1}
\]

with the complete limb, sheet, parent, and marked-access labels used
by the Wave proof.

The first line in (6.1) requires \(J\) to preserve the complete
external, limb, sheet, parent, and access markings.  Only after such a
marked identification is fixed may the two projections be denoted by
one symbol.  It cannot be inferred from the shared phrase "natural
projection."

## 7. Skeptic audit

1. **Existence is not identification.**  Kiwi gives a monotone model;
   it is not silently substituted for KKL's \(\pi\).
2. **A continuum-vertex is not a point.**  KKL's geometric \(K_i\)
   remains a continuum until the finite-tree quotient.
3. **No local connectivity is assumed for \(K(F)\).**  It is the
   target model that is locally connected.
4. **Straightening is used only as a topological dynamical
   transport.**  No modulus or conformal-width comparison is inferred.
5. **The no-collapse proof uses actual periodic points.**  It does not
   rely on a numerical picture or density assertion.
6. **The carrier full-lift remains open.**  DL's full-preimage
   convention for one geodesic continuum is not expanded to a global
   carrier equality without proof.
7. **No global promotion follows.**  Gate N2, VAAPC-I, UPTCR, and MLC
   remain open.

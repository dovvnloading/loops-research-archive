# Issue #40 — native bounded-degree proper-path packets, without a global non-LC access selector

**Date:** 2026-11-06. **Status:** source-defined **covering-sheet theorem** in the actual KKL analytic category, derived from Lemma 5.27 and ordinary unique path lifting. This advances the *multiplicity* side of Issue #40 without asking for singleton prime-end impressions. **It does not determine the immersion \(\iota^*\) attachment membership**, prove a full native endpoint gate census, or close the Wave/interval-growth/MLC gates.

**Source lock:** Kahn–Kapiamba–Lyubich, [arXiv:2606.27272v1](https://arxiv.org/html/2606.27272v1), Lemma 5.27 (§5.6; topological degree of iterated inverse components), §§2.5–2.7 (genuine Hubbard bivertical arc realization), Proposition 6.5 and §6.1 (complete attached-component Carathéodory boundaries), Appendix A.3.1–A.3.2 (covering versus immersion and actual proper path restriction). This document uses **one actual selected inverse branch domain**, not a freely chosen finite automaton.

## 1. Source-defined set-up

Fix a periodically repelling and primitively renormalizable KKL stage \(F=(f,\iota)\), and a permitted iterate \(g=f^n\) on its genuine source and target domains. Choose a **simply connected** target subsurface \(U\) with \(\partial U\cap\mathcal K=\varnothing\) as in the source's Lemma 5.27, and an **actual connected component** \(V\) of \(g^{-1}(U)\). Let

\[
m=\#\pi_0(U\cap\mathcal K)<\infty,\qquad
d=\deg(g|_V).
\tag{1.1}
\]

KKL's *native holomorphic degree theorem* is

\[
\boxed{d\le 2^m.}
\tag{1.2}
\]

Its proof observes that every degree-two step must encounter the critical point in a distinct component of \(\mathcal K\) whose forward iterate lies in \(U\). This statement is about the **actual** polynomial/psi-ql inverse component and is valid independently of whether individual small filled Julia continua are locally connected.

Let \(U^\circ=U\setminus\mathcal K\), and let \(V^\circ=V\setminus g^{-1}(\mathcal K)\). Since the critical values of the iterated holomorphic map lie in \(\mathcal K\) in this cycle, the restriction

\[
g:V^\circ\longrightarrow U^\circ
\tag{1.3}
\]

is an unbranched proper finite covering of degree \(d\), *provided* that \(g|_V\) is the proper map specified in Lemma 5.27 and that all critical values in \(U\) belong to \(\mathcal K\). The latter follows for a completed forward-invariant small-Julia cycle, but is retained as an explicit hypothesis if working with an intermediate \(\psi\)-ql truncation.

Choose any **specific actual proper path**

\[
\gamma:(0,1)\longrightarrow U^\circ
\tag{1.4}
\]

with distinct or equal boundary access endpoints, whose interior is disjoint from \(\mathcal K\). Its prime-end impression(s) may be non-singleton. Fix \(t_0\in(0,1)\) and the regular value \(y_0=\gamma(t_0)\).

## 2. Theorem: full native sheet count and a proper-path bound

### Theorem 2.1 (covering-sheet packet and proper-path subpacket)

Under (1.1)–(1.4), the set of **complete parametrized lifts** of \(\gamma\) through \(V^\circ\),

\[
\operatorname{Lift}_V(\gamma)
=\{\tilde\gamma:(0,1)\to V^\circ:
g\circ\tilde\gamma=\gamma\},
\]

has exactly \(d\) distinct elements. More precisely, evaluation at \(t_0\) yields a canonical bijection

\[
\boxed{
\operatorname{Lift}_V(\gamma)
\ \xrightarrow[\;\sim\;]{\ \tilde\gamma\mapsto\tilde\gamma(t_0)\ }
g^{-1}(y_0)\cap V.
}
\tag{2.1}
\]

Because \(g:V^\circ\to U^\circ\) is **proper**, every lift of a target-proper path is itself proper in \(V^\circ\). Now let \(\operatorname{Lift}^{\rm admiss}_V(\gamma)\) be **any** subpacket whose members have *additionally* been verified to be admissible under the distinct KKL immersion/marking restriction in the intended application. Then

\[
\boxed{
\#\operatorname{Lift}^{\rm admiss}_V(\gamma)\le d\le2^m.
}
\tag{2.2}
\]

The proper finite **covering** does preserve properness: it is the *different immersion* \(\iota\), or an additional marking/path-admissibility requirement, that may discard members of this full \(d\)-sheet packet. Appendix A.3.2 concerns the immersion restriction, not the covering lift. Nor does it classify the full \(\partial_C X\) of any attached excess-tree component.

**Proof.** The restriction (1.3) is a covering map. The interval \((0,1)\) is simply connected. Fix any \(z_0\in g^{-1}(y_0)\cap V\). Unique path lifting gives exactly one lift \(\tilde\gamma\) of the entire parametrized path with \(\tilde\gamma(t_0)=z_0\). For a proper finite cover, every path through the base lifts for the whole interval, and different starting points yield different lifts. There are exactly \(d\) distinct fiber points over the regular value \(y_0\), proving (2.1). Every lift is proper in \(V^\circ\) because inverse images of compact sets under the proper covering are compact, so a nonproper lift of a proper \(\gamma\) would contradict properness of \(\gamma\). The separately **admissible** subpacket is a subset of the \(d\) lifts, giving the first inequality in (2.2). The second is KKL Lemma 5.27. This proof takes place in the **interior** of actual Riemann surfaces, so uses neither pointwise landing nor a complete extension of the covering to a non-LC prime-end circle. \(\square\)

### Corollary 2.2 (typed multiplicity preservation)

Let \(\mathscr P\subset\operatorname{Lift}^{\rm admiss}_V(\gamma)\) be any subpacket that has independently been certified to survive the KKL \(\iota^*\) **proper-path** restriction in the required source/target direction. Then the multiset

\[
\mathcal M_\gamma:=
\bigl\{(\tilde\gamma,\tilde\gamma(t_0)):
\tilde\gamma\in\mathscr P\bigr\}
\tag{2.3}
\]

has exactly \(\#\mathscr P\) distinct sheet tags and every element maps to the same underlying target path \(\gamma\) under \(g\). No two separate source sheets are **canceled** in this labeled multiset. **Forgetting the tags** can, however, identify the images set-theoretically; it is not a valid justification for an edge-weight equality.

**Proof.** By (2.1), distinct source paths have distinct fiber points at \(t_0\). The multiset stores that point and does not identify it under pushforward. The restriction to \(\mathscr P\) preserves injectivity; the underlying pushed-forward map is \(\gamma\) for every element by definition. \(\square\)

This is a **multiplicity-preserving bookkeeping theorem for genuine holomorphic lifts**, not a positive expansion theorem for KKL's original *vertex-side* marking. It is compatible with the native bivertical arc operator of §§2.6–2.7 and can be used to tag candidate dual witnesses without guessing how many different **prime ends** share a planar impression.

## 3. When the bound is uniform in the limb rotation number

If the selected simply connected target \(U\) contains at most \(b\) components of the **actual** small-Julia cycle, then

\[
m\le b
\quad\Longrightarrow\quad
\boxed{
\#\operatorname{Lift}^{\rm admiss}_V(\gamma)\le2^b.
}
\tag{3.1}
\]

KKL's parabolic \(b\)-occupancy condition bounds the number of small-Julia components in a limb, but **one must show the chosen \(U\) is confined to the required limb or union with the counted components** before substituting \(m\le b\). Choosing an uncontrolled global neighborhood cannot justify this inequality. A local proof-used packet over a genuinely bounded set of small Julia vertices has degree independent of the large rotation denominator \(q\), even if the corresponding target impressions are non-LC.

**Important limitation:** (3.1) bounds the multiplicity of lifts of **one fixed parametrized target path** within **one connected inverse component**. It does **not** bound the total number of different boundary accesses, the number of excess components \(X\subset\mathcal T'\setminus\mathcal T\), or the genealogy of all possible paths as \(\gamma\) varies. Those may require substantially more analytic input.

## 4. How this changes the root-contact strategy

The missing KKL immersion correspondence is

\[
F_*=f_*\iota^*
\]

on the **carrier complement** \(\mathcal U\setminus\mathcal T\), which is not identical to the punctured-small-Julia complement \(\mathcal U\setminus\mathcal K\) of the arc diagram. These are **different source types**.

The bounded-sheet packet theorem gives a route that may avoid a global prime-end selector:

1. For a proof-used genuine bifurcating/corridor path \(\gamma\) or bivertical Hubbard arc representative, identify its actual simply connected \(U\) and selected \(V\) from KKL's existing localization/subsurface construction (such as §5.6). Prove \(m\le b\) or record the actual \(m\).
2. Pull back **the very same parametrized path** by the genuine covering \(g\), tagging each lift by its \(y_0\)-fiber point. This certifies all multiplicities before forgetting sheets.
3. Only then apply the actual immersion proper-path restriction and complete attached-boundary rule of Proposition 6.5. This is a membership/subordination problem **within a finite packet** when the path and chosen inverse component are fixed. It is not an assertion that a whole non-LC access fiber is finite.
4. To get a positive \(\mathfrak T\)-dual witness, show that at least one surviving tagged proper lift has nonzero intersection with the native bivertical Hubbard arc diagram. For the corrected bounded-visits argument, this only needs to be done on a **hypothetical periodic interval that returns to the critical limb** (as established in the companion dual-WAD note, Theorem 5.2).
5. For a singleton closed Wave crest, one still needs the specific **endpoint-access proper-path relation**, because a finite sheet count cannot show whether an entire \(B_X\) is born on closure or whether an admissible Wave with such a crest exists.

The **first unresolved geometric gate** is consequently no longer “construct the whole global prime-end quotient”: it is the **survival and dual intersection** of an explicitly bounded, actual holomorphic lift packet at a critical-return contact, plus the original marking/crest admissibility requirements.

## 5. Adversarial checks / no-go inferences

- A bound on \(\deg(g|_V)\) does **not** imply a bound on total distinct prime ends at a non-LC point. Theorem 2.1 counts *lifts of one chosen path*, not all paths.
- All \(d\) lifts of a proper path stay proper **for the proper covering**. Only the **additional immersion/marking-admissible subpacket** may be smaller. Any omission must be certified by Appendix A.3.2 or by a specified marking filter; no counting argument can invent a missing lift.
- Distinct source proper paths pushed to one **set** are not automatically two disjoint target WAD classes; the labeled multiset stores multiplicity, but a geometric WAD proof must establish actual disjointness/validity.
- A sheet bound for the \(\mathcal K\)-punctured surface is not automatically a bound for a path in the \(\mathcal T\)-complement without an explicit inclusion/transfer.
- Nonempty horizontal WAD valuation cannot be obtained from covering degree alone. The source's §2.7 requires a **positive dual-crossing witness**, not just a covering multiplicity.
- The earlier proposed adjacent-atom zero-crest Wave is **inadmissible** by Appendix A.1 and has been withdrawn; no such counterexample is used here.

**Status:** theorem on the actual native \(\psi\)-ql cover and finite genuine proper-path packets, uniform bound conditional on \(m\le b\). Native root-contact \(\iota^*\), marked boundary-to-dual visibility, valid zero-core Waves, repaired interval growth, Wave amplification and MLC remain **OPEN**. Lean formalization in the companion module checks only finite pigeonhole and algebraic spectral implications, **not** this analytic path-lifting theorem. No independent specialist review.

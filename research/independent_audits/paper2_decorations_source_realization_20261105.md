# Paper 2 — source-verified shallow and deep puzzle pullback audit

**Date:** 2026-11-05. **Status:** Independent internal source check, not mathematical peer review and not a claim of a proved MLC gate. The original source-locked PDF, 465-entry ledger, and proof statuses remain unchanged.

## Primary references

Jeremy Kahn and Mikhail Lyubich, *A priori bounds for some infinitely renormalizable quadratics: II. Decorations*, [arXiv:math/0609046v2](https://arxiv.org/pdf/math/0609046v2) (2007), published in *Ann. Sci. Éc. Norm. Supér.* 41 (2008), 57–84, [DOI 10.24033/asens.2063](https://doi.org/10.24033/asens.2063).

- **Printed p. 4, §1.1 and footnote 1:** A pullback of a closed disk means the closure of an interior pullback component. Closures of distinct components may in general touch.
- **Printed pp. 5–6, §2.1:** The critical separator P=Y^((n−1)q+1), first kingdom V^0=Y^(nq+1), escape depth n≥1, and two contained univalent f^q-pullbacks Q_L,Q_R of P attached to the two indicated vertices.
- **Printed p. 6, Lemma 2.1:** For each of the 2^n vertices v of P, a univalent f^(nq)-pullback Q^v ⊂ P of depth (2n−1)q+1 is provided; the pieces Q^v are explicitly **pairwise disjoint**. The proof obtains them as components of the n-fold iterate of the shallow two-branch map.
- **Printed pp. 7–8, §2.2:** The modified principal nest ends, upon the primitive-renormalization stopping condition, in a quadratic-like first return f^p, its invariant connected little filled Julia set K_0, and the primitive cycle K_i=f^i(K_0).

Companion internal primary target: [Paper 2, main_v2.tex](../../papers/paper2_rooted_end_compactification/main_v2.tex), especially lines 294–523, 1064–1179, 1250–1263 and 1335–1353.

## Hypothesis-by-hypothesis verdict

| Input | Shallow f^q choice | Deeper f^(nq) choice |
|---|---|---|
| H1: closed Jordan P,Q_0,Q_1 within P | Standard source puzzle disks and two univalent pullbacks. **Closed disjointness requires a supplementary proof**, not merely distinct open components. | Lemma 2.1 directly supplies **closed pairwise disjoint** Q^v for distinct vertices. Select two. |
| H2: closed homeomorphic inverse branches | Univalent interior pullbacks, plus Carathéodory/Jordan boundary extension, support closed homeomorphisms. | Same argument for each f^(nq) univalent pullback; do not assume boundary injectivity for arbitrary non-Jordan pullbacks. |
| H3: K(f)=J(f) | Explicit additional hypothesis, not supplied for arbitrary decoration parameters by Lemma 2.1. | Unchanged because f is unchanged. |
| H4: nondegenerate full terminal K_0 in first-level gap | Depends on the **primitive stopping/nest**, placement K_0 in int(V^0), and distinct same-depth pieces. Not a consequence of Lemma 2.1 alone. | Every deep Q^v lies in Q_L or Q_R by the source's iterative construction, hence remains disjoint from K_0 ⊂ int(V^0), provided that nest placement is verified. |
| Symbolic dynamics | One deleted address symbol corresponds to f^q. | One deleted symbol corresponds to f^(nq). The whole root-arrow and intermediate-orbit bookkeeping must be retimed. |
| Genuine next-scale map and uniform estimates | Not supplied. | Not supplied. Selecting two of 2^n branches does not provide a canonical all-scale marking. |

## Shallow separation: an explicit missing link that can be supplied

**Lemma (primitive-cycle fixed-point avoidance).** Suppose p>1, f(α)=α, 0∈K_0, f^p(K_0)=K_0, and K_0∩f(K_0)=∅. Then

  f^m(0) ≠ α for every m≥0.

**Proof.** Otherwise f^m(0)=α; since α is fixed, f^(kp)(0)=α for every sufficiently large k. Since 0∈K_0 and f^p(K_0)=K_0, α∈K_0. But f(α)=α also puts α in f(K_0), contradicting their disjointness. QED.

This lemma uses a **primitive**, period-p>1 little-Julia cycle. It cannot be applied to an arbitrary non-satellite parameter or without connectedness ensuring the critical point belongs to K_0.

For the Kahn–Lyubich Yoccoz puzzle, a bounded critical orbit cannot lie on an escaping external-ray/equipotential arc; each puzzle vertex is a preimage of the dividing fixed point α (source p. 5). The lemma therefore excludes the critical point from all applicable depth graphs. If a boundary point z of two shallow f^q-pullbacks were critical for f^q, some f^i(z)=0 with i<q would place 0 on a forward image of a puzzle graph, contradiction. Hence the hypothetical shared boundary point is **regular** for f^q. A regular holomorphic local coordinate and the Schoenflies theorem imply that the local inverse image of int(P) is connected. Distinct pullback components cannot both accumulate at z.

**Verdict:** Paper 2's local-uniqueness argument for shallow **closed** disjointness is mathematically plausible and has a precise primitive-cycle justification. Its critical-orbit avoidance step should be stated explicitly and source-checked against the exact puzzle-graph convention. The source's warning about touching pullbacks does not automatically invalidate this specific carefully selected pair.

## Deeper fallback: an actual source-supported alternative, with boundaries

For any two distinct vertices v,w of P, set

  τ := n q,  g_* := f^τ,  Q_0^* := Q^v,  Q_1^* := Q^w.

Kahn–Lyubich Lemma 2.1 gives Q_a^* ⊂ P with **disjoint closed sets**, and univalent restrictions of f^τ to their interiors. Source Jordan boundaries and Carathéodory extension supply the closed homeomorphism on each pullback. The construction of the Q^v as components of the n-th iterate of the two original shallow branches places each Q^v inside the shallow Q_L or Q_R. Thus, assuming the primitive nest's K_0 ⊂ int(V^0) and the same-depth separation of V^0 from the shallow pullback interiors, K_0 is disjoint from every deep Q^v, preserving the root gap.

For n=1, deep time equals q and Lemma 2.1 reinforces the shallow disjointness directly. For n>1, the deeper branches give a genuinely different symbolic clock.

**This is not a canonical choice.** Lemma 2.1 supplies 2^n branches; choosing two arbitrarily may erase proof-used endpoint, localization-sheet, contact, and forward-transition data. No source statement proves that an arbitrary binary selection is compatible with the *next actual renormalization scale*. It supports a one-scale abstract rooted-end construction, not H1_MARKED_CONSTRUCTION.

## Precise retiming audit — not a global substitution q → nq

The period q in the satellite rotation number, source depth P=Y^((n−1)q+1), first kingdom V^0=Y^(nq+1), and depth (2n−1)q+1 of Q^v must **not** change under the fallback. The escape depth n also keeps its meaning.

Only the chosen **inverse-branch time** changes from q to τ=nq:

| Item | Shallow | Deep block |
|---|---|---|
| Branch map | g=f^q | g_*=f^τ |
| Inverse word w | f^(q·len(w)) branch | f^(τ·len(w)) branch |
| First-symbol shift | g(K_aw)=K_w, g(E_aω)=E_ω | g_*(K^*_aw)=K^*_w, g_*(E^*_aω)=E^*_ω |
| Intermediate-orbit compactness | union of f^r(P) for 0≤r<q | union of f^r(P) for 0≤r<τ |
| Two-sheet map | f^q on first-symbol sheets | f^τ on newly selected first-symbol sheets |
| **Terminal root arrow** | f^q(K_0)=K_(q mod p) | **f^τ(K_0)=K_(τ mod p)** |
| Combinatorial puzzle depths | Original q,n | Unchanged |

The root arrow stays **separate** from the symbolic shift. If p divides τ, it lands back on K_0; this is consistent with its separate typing. The original paper's figures, equivariance theorem, K(f) compactness proof, two-sheet theorem, and root-arrow display use the shallow q-clock.

**Concrete editorial defect:** [The existing fallback remark](../../papers/paper2_rooted_end_compactification/main_v2.tex#L510-L523) says that only the transition time per address symbol changes and the architecture is otherwise intact. This should not be read as literal validity of the existing q-time theorem for the deeper family. A retimed deep-block corollary must update the intermediate iterates, all dynamical arrows, and especially the root arrow. A blind replace-all of q would also corrupt the original source's puzzle depths.

## Remaining MLC-relevant blockers

The direct-decoration rooted-end compactification is a **first-scale** mathematical construction. Neither the shallow branch proof nor the deeper fallback supplies:

1. canonical future-faithful selection among 2^n branches, including sheet memory, full contact/trace ports, obstacles, and protected prime-end endpoints;
2. a second **genuine renormalization-scale** return rather than another same-scale symbol deletion;
3. cofinal prime-end chains on every end, including endpoint addresses (DIRECT_DECORATION_END_PRIME_END_COFINALITY);
4. all-depth sheet-sensitive incidence/contact closure (DIRECT_DECORATION_ALL_DEPTH_CONTACT_CLOSURE); or
5. period-independent analytic energy/extremal-width estimates, H2 calibration, or H3 coercivity.

These are the appropriate live targets. One-scale binary coding or additional conditional formal lemmas are not substitutes.

## Recommended next falsifiable experiment

Choose one **actual twice-renormalizable quadratic** (with documented primitive first stopping and source puzzle) and attempt to transport its complete first-scale separator across the next actual renormalization. Record the source domains, return times, endpoint rays, root cycle index modulo p, prime-end/access chains, all live covering sheets, and any omitted first-contact component. If an actual source map cannot preserve one datum, record the first precise failure certificate instead of assuming future-faithful compactness. Only then test period growth and uniformity.

## Review / completion checklist

- [x] Source closed-pullback definition and touching warning located (printed p. 4).
- [x] Shallow Q_L,Q_R source construction located (printed p. 6).
- [x] Closed-disjoint deep Q^v source lemma and nested iteration located (printed p. 6).
- [x] Primitive terminal nest source located (printed pp. 7–8).
- [x] Independent primitive-cycle fixed-point avoidance argument written.
- [x] Root-arrow, address-time, intermediate-orbit and puzzle-depth clocks separated.
- [ ] Expert confirmation of exact root containment and boundary regularity in the selected terminal primitive setting.
- [ ] Fully edited and independently checked deep-block corollary, including protected prime-end data.
- [ ] Actual two-scale source-verified geometric transition with all necessary markings.

**Bottom line:** Paper 2's closed-piece hypotheses have a substantive mathematical justification in its specific primitive puzzle setting; the deeper fallback is directly supported for closed separation by the primary source. But a correct fallback requires retyping its time and terminal arrow and proves nothing yet about next-scale dynamical realization or universal MLC gates.

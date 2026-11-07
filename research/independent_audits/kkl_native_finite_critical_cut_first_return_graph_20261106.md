# Issue #40 — a SOURCE-DEFINED finite **critical-cut first-return graph** with a q-independent number of vertices

**Date:** 2026-11-06.  
**Status:** a rigorous native **reduction and iff certificate**, not a synthetic simulation. The actual map \(\Phi=F_*=f_*\iota^*\) is the **only** transition input. For a parabolically \(\mathbf b\)-bounded primitive stage, every short positive-length critical-return state that can continue properly belongs to one of at most \(2(r-1)(12\mathbf b-1)\) **actual original-marking cut-side interval states**, where \(r=\ell(\mathbf L_0)\le6\mathbf b\). A canonical **partial first-return map** on these states is defined by the genuine \(\Phi\)-iterates, with immediate termination upon saturation, marked-length increase, or absence of a return. Under the native nondecreasing-proper-length hypothesis, its cycles are **equivalent** to the remaining periodic critical-return obstruction. The actual map has **not yet been computed or proved acyclic** for all non-LC KKL stages; Issue #40 remains open.

**Primary source:** Kahn–Kapiamba–Lyubich [arXiv:2606.27272v1](https://arxiv.org/html/2606.27272v1), §4 Lemma 4.8 (open limb, \(r\le6\mathbf b\)), §6.1 Proposition 6.5 (proper-path \(\iota^*\), complete attachments, independent open/closed inputs), Proposition 6.6 and paragraph after its proof (\(\Phi\mathbf L_0=C\)), Proposition 6.7 (noncritical proper translation corridor), Appendix A.1 (finite original vertex-side atoms and cuts). Companion [native cut-gate theorem](./kkl_native_critical_cut_gate_reduction_20261106.md) proves the geometric cut-boundary obstruction and the sharper conditional visit bound.

## 1. Actual intrinsic gate vertex set

Fix an actual source KKL stage with original finite cyclic marking \(\mathcal I\), total atom number \(M\), and **open critical limb** \(\mathbf L_0\subset C\) consisting of \(r\ge1\) full consecutive original marking atoms. Let \(\mathsf{Cut}_{\rm crit}\) be its \(r-1\) **internal** original marked cuts. For each integer \(k\) satisfying
\[
1\le k<\min(M,12\mathbf b),
\tag{1.1}
\]
define the **real set of input intervals**
\[
\boxed{
\mathcal G_k
=\left\{J:\begin{array}{l}
J\subsetneq C\text{ is a genuine connected open }\mathcal I\text{-multi-interval},\\
\ell(J)=k,\quad J\cap\mathbf L_0\ne\varnothing,\quad
\mathbf L_0\not\subset J,\quad
\partial_C J\cap\mathsf{Cut}_{\rm crit}\ne\varnothing
\end{array}\right\}.
}
\tag{1.2}
\]

These are **not** invented states: each \(J\) is a real original-marking interval on \(\partial_C\mathcal T\) determined by its original cuts, and the \(\Phi\) iteration will use the genuine complex analytic \(f,\iota\) and attached Carathéodory boundaries. No global prime-end quotient is chosen.

For each internal cut \(e\) there are at most two length-\(k\) cyclic intervals ending/starting at \(e\), so

\[
\boxed{
|\mathcal G_k|\le2(r-1),
\qquad
\left|\bigsqcup_{1\le k<\min(M,12\mathbf b)}
\mathcal G_k\right|
\le2(r-1)(12\mathbf b-1).
}
\tag{1.3}
\]

Since \(r\le6\mathbf b\), the total vertex bound is

\[
\boxed{
|\mathcal G_{\rm short}|\le
(12\mathbf b-2)(12\mathbf b-1),
}
\tag{1.4}
\]
**independent of the rotation denominator \(q\)**. For \(\mathbf b=1\), it is at most \(110\) real marked input intervals, however large \(q\) is. For \(r=1\), \(\mathcal G_{\rm short}=\varnothing\).

The bound is on **candidate interval input states**, not all actual prime ends, connected attached components or their internal crosscut chains. To compute \(\Phi(J)\) for these inputs one still must apply the **whole** actual Proposition 6.5 proper-path/attachment relation, including all eligible \(\partial_C X\).

## 2. A CANONICAL partial native first-return operator

For each \(k\) consider the true deterministic native operation \(\Phi\) on marked connected open multi-intervals, with full-circle \(C\) absorbing. Fix \(J\in\mathcal G_k\). If there exists \(n\ge1\) with:

- for every \(1\le j\le n\), the **actual** image \(\Phi^jJ\) is a *proper* connected open marked interval and has **the same length \(k\)**;
- no intermediate \(1\le j<n\) has a full-atom encounter with the open critical limb;
- the return image \(\Phi^n J\) lies in \(\mathcal G_k\), hence meets the critical limb but not entirely contains it;

choose the **least such \(n\)** and define

\[
\boxed{R_k(J)=\Phi^nJ\in\mathcal G_k.}
\tag{2.1}
\]

Otherwise \(R_k(J)\) is **undefined**. An output can terminate because it saturates, increases length, fails to be marked/typed, or never returns to the critical limb. Since \(\Phi\) is a deterministic actual source-defined operation, this defines an unambiguous **partial map**

\[
R_k:\mathcal G_k\rightharpoonup\mathcal G_k.
\tag{2.2}
\]

No list of transition values is postulated. Every defined arrow must be derived from the actual \(f_* \iota^*\) at the selected stage and its true connected open interval images. The full attached-component boundary must be transported **before** using the covering; coincident planar impressions do not identify distinct prime ends.

### Theorem 2.1 (finite first-return cycles are exactly the critical periodic obstruction)

Assume the native marked interval action is defined on the considered iterates and **nondecreasing in combinatorial length while proper**. Then for every fixed \(k\) in (1.1):

\[
\boxed{
R_k\text{ has a directed cycle}
\quad\Longleftrightarrow\quad
\Phi\text{ has a proper positive-length period-}p\text{ orbit
of constant length }k\text{ meeting }\mathbf L_0.
}
\tag{2.3}
\]

**Proof (⇒).** A directed \(R_k\)-cycle consists of finitely many actual \(\Phi\)-orbit segments, each of positive iterate time, staying proper and length \(k\), and with exactly one critical return at the endpoint of the segment. Concatenating these genuine deterministic orbit segments gives some \(\Phi^pJ=J\) with \(p\ge1\), all intermediate states proper and length \(k\), and an actual critical-limb encounter.

**Proof (⇐).** Suppose a \(\Phi\)-periodic orbit of proper marked intervals meets the critical limb. By source saturation \(\Phi(\mathbf L_0)=C\), **no** periodic proper state can contain the entire limb. Thus each critical-intersecting state lies in the internal-cut vertex set \(\mathcal G_k\), by the [cut-gate lemma](./kkl_native_critical_cut_gate_reduction_20261106.md). Nondecreasing proper marked length along the period forces all states to have a common fixed length \(k\). Starting at a critical-intersecting state, the actual successive *first critical return times* yield defined arrows in \(R_k\). Since the orbit is periodic, these arrows form a directed cycle. \(\square\)

**No hidden analytic theorem:** This is a **mathematical equivalence conditional on the native finite marked interval action and proper length monotonicity**. It does not assert any actual source-defined \(R_k\) is acyclic. A real directed cycle, if found from valid \(\iota^*\) attachment diagrams for a genuine required KKL stage, would be a **native first-failure certificate** for the missing nonreturn requirement; an acyclicity proof would discharge it.

### Corollary 2.2 (short critical-visit growth from gate acyclicity)

Under the high-rotation \(q\ge24\mathbf b\) Wave-to-open-core interface already proved in [the canonical active/critical atom notes](./kkl_native_critical_atom_contact_and_full_wave_interface_20261106.md), and the remaining proper-length monotonicity/closed-input well-typedness assumptions, if **every** \(\mathcal G_k\)'s actual return map \(R_k\) is **acyclic**, then every continuing short critical-visit chain has

\[
\boxed{N<(2r-1)(12\mathbf b-1)\le(12\mathbf b-1)^2.}
\tag{2.4}
\]

This is the corrected strict pigeonhole theorem of the companion [critical-cut note](./kkl_native_critical_cut_gate_reduction_20261106.md), now with a **precise finite acyclicity acceptance test**. The spectral \(T_F\) dual-WAD strategy is **one possible proof of this acyclicity**, not an extra theorem that must be proved globally.

## 3. How to prove the **actual** graph acyclic (not synthetic tests)

For each of the **at most \(2(r-1)(12\mathbf b-1)\)** actual input intervals \(J\):

1. **Typed old access:** record its genuine two endpoint cuts, cyclic side orientation, original marking length and which **internal critical cut** it uses. Do not infer access identity from planar root labels in the non-LC category.
2. **Immersion pullback:** compute \(\iota^*J\) as KKL Proposition 6.5's old boundary portion **plus the COMPLETE Carathéodory boundary of each eligible attached component**. Preserve exact sheet/gate multiplicity and whether the component appears only for a **closed** endpoint input.
3. **Covering:** apply the genuine degree-two \(f_*\) and determine properness or saturation. If proper, the covering is **injective on the one connected** source pullback; it cannot silently cancel distinct source accesses.
4. **First return:** use the actual corridor properness (Prop. 6.7) to compress long stretches of noncritical limb translation and compute the first positive return to \(\mathbf L_0\) that **preserves** interval length \(k\). Terminate the arrow upon full-circle saturation or any strict length growth.
5. **Acyclicity certificate:** exhibit an intrinsic strictly decreasing rank along every defined \(R_k\)-arrow, using source-justified native gate/crosscut order, or prove absence of cycles directly. A nonzero bivertical dual-WAD obstruction from KKL §§2.6–2.7 is an alternative. If a genuine directed cycle occurs, exhibit **the actual finite sequence of source-defined pullback intervals and attached boundary contributions** as the sharp counterexample.

This is **a finite set of geometric proof obligations for fixed \(\mathbf b\)**, not a numerical automaton: *the states are determined by original marked critical cuts, the arrows are defined exclusively by the real holomorphic \(F\)*. The total number of vertices is uniform in \(q\), though the **return times** of their arrows and the complexity of their non-LC attached boundaries need not be uniformly bounded without further analysis.

## 4. Trust boundary

- **No LC shortcut:** A finite number of input **marked cuts** does not imply finitely many actual prime ends in their impressions or attached-component boundary. Each arrow still needs complete analytic proper-path data.
- **No arbitrary matrix:** The source already supplies the real \(T_F\) on bivertical Hubbard arcs, and the present reduction does not invent a transition matrix. If one writes a matrix for \(R_k\), its rows must come from the **actual first-return gate atlas**, not a synthetic cyclic word.
- **No false width claim:** Conformal Wave width is not identified with the induced WAD norm without independent parallel-law verification.
- **No promotion:** Proving the *finite bound* on the size of the native gate family does not prove its first-return map is acyclic.

**Status:** a genuine KKL source-defined finite first-return **equivalence** and a q-independent native geometric acceptance certificate, not the completed critical-cut gate atlas. **Issue #40, KKL_BOUNDED_VISITS_INTERVAL_GROWTH_REPAIR, KKL_PARABOLIC_WAVE_AMPLIFICATION, and MLC remain OPEN**. Independent specialist review pending.

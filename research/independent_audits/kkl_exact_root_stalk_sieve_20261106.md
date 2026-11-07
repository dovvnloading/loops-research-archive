# Issue #40: exact closed-root-stalk sieve for critical marked intervals

**Date:** 2026-11-06. **Status:** an unconditional finite-cyclic-marking theorem and a **conditional** sharpening of the actual Kahn–Kapiamba–Lyubich (KKL) critical-Wave return count. This does not close Issue #40, the native nonreturn/interval-growth gate, Wave amplification, or MLC.

**Source interface:** [KKL arXiv:2606.27272v1](https://arxiv.org/html/2606.27272v1), §4 Lemma 4.8; §6.1 Propositions 6.5–6.9 (especially the designated attachment-root corridor in the proof of 6.8); Appendix A.1/A.3.4 for the original marked cuts and distinct open/closed actions. The companion [root-exposure absorption theorem](./kkl_native_root_exposure_absorption_20261106.md), [native cut-gate reduction](./kkl_native_critical_cut_gate_reduction_20261106.md) and [closed-crest Wave interface](./kkl_native_critical_atom_contact_and_full_wave_interface_20261106.md) state the **additional** geometric hypotheses. No global pointwise prime-end quotient is assumed.

## Theorem 1: exact root-avoiding candidate count

Take a circle partitioned into M ≥ 2 cyclically ordered open marked atoms, with cuts numbered modulo M. Let the open critical limb L consist of r consecutive atoms 0,...,r−1, where 1 ≤ r < M. For 1 ≤ k ≤ M−r, write J_s for the connected **open** k-atom interval from cut s to cut s+k; its **closed crest** D_s includes both endpoint cuts. Restrict attention to J_s meeting L.

There are exactly **r+k−1** critical-meeting J_s. For a selected marked access a in the closed critical limb, the exact number whose *closed crest* contains a, followed by the number whose crest avoids a, is:

| Location of a | D_s contains a | D_s avoids a |
|---|---:|---:|
| Interior of a critical marking atom | k | **r−1** |
| Outer cut 0 or r of the critical limb | k | **r−1** |
| Internal critical cut h (1 ≤ h ≤ r−1) | k+1 | **r−2** |

These are **combinatorial input-interval counts**; neither the table nor the test script counts prime ends, attached components, Wave leaves, or realizable native returns.

**Proof.** Work in an integer lift of the critical block. A k-atom run [s,s+k−1] intersects [0,r−1] precisely when

\[
1-k\le s\le r-1. \tag{1}
\]

There are r+k−1 starts; k ≤ M−r makes them distinct modulo M and excludes any further cyclic representatives.

If a is inside atom t with 0 ≤ t ≤ r−1, its atom belongs to J_s precisely when t−k+1 ≤ s ≤ t: k starts in (1). If a is a cut h with 0 ≤ h ≤ r, the **closed** crest contains that cut precisely when

\[
h-k\le s\le h. \tag{2}
\]

For 1 ≤ h ≤ r−1, all k+1 starts in (2) are within (1). If h=0, only the k starts [1−k,0] remain; if h=r, only [r−k,r−1] remain. Subtract from r+k−1. QED.

### Endpoint-defect corollary

For an **internal** cut h, the open J_s itself contains h only when s<h<s+k, which holds for **k−1** starts. The closed crest contains h for **k+1** starts. Thus recording only the open-core root test loses exactly **two endpoint-only terminal states per length**. For either *outer* cut, closing the crest adds exactly one root-containing state.

The length hypothesis is essential: for M=4, r=3, k=3 and h=1, the actual internal-cut root-avoiding count is 0, not r−2=1; here k>M−r.

## Corollary 2: a sharper source-conditional native gate capacity

Fix an actual parabolically b-bounded prime-primitive KKL stage with rotation denominator q ≥ 24b. Let M be its total original marking atoms, r its critical-limb atom count, with source bounds M ≥ q and r ≤ 6b. A *genuine* short critical-wave core J has 1 ≤ k < 12b under the companion native Wave interface, so

\[
k\le12b-1<24b-6b\le M-r. \tag{3}
\]

Use **only the source-selected ideal-access occurrence** a_x in KKL Proposition 6.8, not every access with the same planar impression. Under the actual root-exposure absorption theorem and correctly typed **closed-crest** positive-time inclusions, any continuing short critical successor has a source crest D=closure(J) **avoiding** a_x: a crest containing it carries an entire long corridor and cannot have a later short successor.

If this specific a_x lies at an **internal original marked cut** of the critical limb, Theorem 1 leaves at most **r−2** continuing source candidate intervals at any fixed short k, and at most

\[
\boxed{(r-2)(12b-1)\le(6b-2)(12b-1)} \tag{4}
\]

across all short lengths. This halves the previous bound 2(r−2)(12b−1) for the same root placement. In particular, r=2 leaves zero continuing candidates; r=3 leaves at most one per k.

If the source-selected a_x instead lies **inside one marked critical atom** or at an **outer marked critical cut**, Theorem 1 leaves at most r−1 per length, hence

\[
\boxed{(r-1)(12b-1)\le(6b-1)(12b-1)}. \tag{5}
\]

The upper bounds (4)–(5) apply to *actual continuing crests* only once the source-selected access, its exact original-marking placement, root exposure, and proper closed Wave action are verified. If no such placement is certified, no promotion to a native theorem is justified. In particular, an unmarked or non-locally-connected shared *planar* root does not identify its ideal-boundary accesses.

## Corollary 3: improved **conditional** number of continuing transitions

Assume, in addition to the precisely typed genuine closed/open critical-visit chain above:

1. Every source core of a continuing short critical visit is a positive regular connected open marked interval, and the actual positive-time image of its **open** core is contained in the next such open core.
2. **Proper** original-marked length is nondecreasing on all proof-used genuine Phi iterates, where Phi=F_*=f_* iota^*.
3. There is **no proper periodic root-avoiding critical-return interval** among these actual states. This is the still-open native nonreturn/dual-WAD gate, *not* a consequence of merely knowing the Perron eigenvalue is greater than one.

For a chain with N continuing transitions J_0 → J_1 → ... → J_N, count the **N source states** J_0,...,J_(N−1). Their lengths k_i are nondecreasing by (1)–(2). In a constant-length block, every inclusion Phi^(m_i)J_i ⊆ J_(i+1) is an equality: the image is proper, has at least k_i atoms by (2), and lies in a regular connected open marked interval with exactly k_i atoms. A repeated source state of that length would therefore be periodic under the true positive-time composition, contradicting (3). Each k can occur in just one block and at most g distinct continuing source states, where g is r−2 or r−1 according to the root placement. There are at most 12b−1 lengths. Thus the **transition** count, with no artificial +1 per plateau, satisfies

\[
\boxed{N\le(r-2)(12b-1)} \quad\text{(internal root cut)}
\]

or \(N\le(r-1)(12b-1)\) (root atom or outer cut).

This bound does *not* count an initial wave before it is short/critical or a final terminal wave. It remains **conditional** on native nonreturn, proper-length monotonicity, and the closed/open Wave bridge.

## Finite regression and remaining analytic task

Run `python research/independent_audits/verify_root_stalk_sieve.py --check-manifest`. The deterministic manifest `results/root_stalk_sieve_20261106.json` covers every M from 2 to 40, every r,k in 1≤r<M and 1≤k≤M−r, every critical cut and atom root placement, both open/closed cut conventions, and an outside-regime negative control. It is a finite **regression**, not a substitute for the written counting proof or a certificate of any real KKL immersion.

**Next native experiment:** For one actual KKL stage, certify the source-selected a_x as an original cut/atom access, enumerate the remaining r−2 (or r−1) candidate starts at one k, and compute the true **complete** iota^* attached Carathéodory boundaries for their *closed* crests. A survivor needs an actual proper-path first return, zero-edge escape, or nonzero dual-WAD/Shift-Lemma witness. An invented atom substitution, even with an expanding matrix, cannot close that gate.

**Status:** finite counting theorem proved, regression tested, native application conditional. Issue #40 and all analytic/MLC gates remain **OPEN**; novelty and referee validation beyond this archive are not established.

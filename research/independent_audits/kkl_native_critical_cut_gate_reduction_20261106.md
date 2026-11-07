# Issue #40 — critical-root CUT GATES: exact native periodic-state localization and sharper visit bound

**Date:** 2026-11-06.  
**Status:** **new native interval-dynamics theorem**, using the *actual* KKL \(F_*=f_*\iota^*\), Proposition 6.6's exact saturation of the entire critical limb, proper-path monotonicity, and the **original** finite vertex-side marking. It sharply reduces the still-missing positive dual-WAD nonreturn proof to **at most \(2(\ell(\mathbf L_0)-1)\)** critical-cut/side states for each fixed positive interval length. In the one-atom critical-limb case there is **no** proper periodic critical-return interval, independently of the Perron eigenvalue. A refined conditional critical-visit bound improves the previous \(216\mathbf b^2\) constant. This is not a full-category proof of the remaining nonreturn when the critical limb has several atoms.

**Primary KKL v1 source:** [arXiv:2606.27272v1](https://arxiv.org/html/2606.27272v1), §4 Lemma 4.8 (\(\mathbf L_0\) is an open connected original marking multi-interval of length \(r\le6\mathbf b\)), §6.1 Proposition 6.5 (native \(\iota^*\) full attached-boundary and monotone source restriction), **Proposition 6.6, after its proof:** 
\[
\boxed{F_*\mathbf L_0=\partial_C\mathcal T=C}
\tag{0.1}
\]
and \(F_*\mathbf L_j=\mathbf L_{j+1}\) for \(j\ne0\); Appendix A.1/A.3.2 (finite original marking and proper-path pullback). Source §6.1 proof of Lemma 6.4 supplies the short crest length \(\ell<12\mathbf b\); see also our [high-rotation native Wave interface](./kkl_native_critical_atom_contact_and_full_wave_interface_20261106.md).

## 1. The crucial saturation observation

Let \(\mathcal I\) be KKL's **actual finite original vertex-side ideal marking** of \(C\). The **critical limb** \(\mathbf L_0\subset C\) is a connected **open multi-interval**, consisting of \(r=\ell(\mathbf L_0)\) consecutive full marking atoms, with
\[
1\le r\le6\mathbf b.
\tag{1.1}
\]
Write \(\Phi=F_*\) for the **genuine** marked connected-interval action, including the complete actual immersion/attachment relation from KKL Proposition 6.5.

### Lemma 1.1 (an interval containing the critical limb saturates immediately)

For every connected marked interval \(J\) such that \(\mathbf L_0\subset J\),

\[
\boxed{\Phi(J)=C.}
\tag{1.2}
\]

**Proof.** The real immersion restriction is monotone on marked inputs, so \(\Phi(\mathbf L_0)\subset\Phi(J)\). But source Proposition 6.6 gives \(\Phi(\mathbf L_0)=C\). The target is a subset of \(C\), hence equality. \(\square\)

No finite transition automaton, matrix eigenvalue, local connectivity or global pointwise \(\iota\)-boundary quotient is used. This is **literally an implication of two native source statements**.

A *proper forward orbit* is an actual orbit \(J,\Phi J,\Phi^2J,\ldots\) whose states all remain **proper**, i.e. unequal to the whole circle. Every state on such an orbit therefore satisfies
\[
\boxed{\mathbf L_0\not\subset J_n.}
\tag{1.3}
\]

## 2. The topological endpoint-gate lemma

Choose an orientation of the actual prime-end circle and label its finite marking cuts cyclically by integers modulo the total number \(M=|\mathcal I|\) of atoms. The critical limb is one open block \((a,a+r)\) in an integer lift, including the internal cuts \(a+1,\ldots,a+r-1\) but excluding its outer cuts \(a,a+r\). Let

\[
\mathsf{Cut}_{\mathrm{crit}}=
\{a+1,\ldots,a+r-1\}
\subset C
\tag{2.1}
\]
be its **actual internal marked cuts** (not a set of planar critical points), of cardinality \(r-1\).

### Lemma 2.1 (proper critical overlap forces an **internal** limb cut)

If \(J\subsetneq C\) is a positive-length connected open marked multi-interval satisfying

\[
J\cap\mathbf L_0\ne\varnothing,\qquad
\mathbf L_0\not\subset J,
\tag{2.2}
\]

then at least one of the **two endpoint marked cuts** of \(J\) belongs to \(\mathsf{Cut}_{\mathrm{crit}}\).

**Proof.** Consider the two boundary cuts of the proper connected circular interval \(J\). If neither cut belonged to the interior of the connected open arc \(\mathbf L_0\), then as one moves continuously along the connected arc \(\mathbf L_0\), membership in \(J\) could not change: any change from inside to outside \(J\) must cross a boundary cut of \(J\), and no such cut lies inside \(\mathbf L_0\). Hence \(\mathbf L_0\) would be entirely contained in \(J\) or entirely disjoint from it, contradicting (2.2). Thus some endpoint of \(J\) belongs to the **interior** of \(\mathbf L_0\). Being an original marked cut, it is necessarily one of its \(r-1\) internal cuts. \(\square\)

This argument also handles a **punctured-circle** marked interval \(J=C\setminus\{e\}\): the two end cuts then coincide at \(e\). If \(J\) intersects but fails to contain the critical limb, the missing point \(e\) lies at an internal critical cut. No assumption about singleton *planar impressions* is made.

For a fixed positive proper interval length \(k\), specifying a cut \(e\) and whether it is the **left or right** endpoint of \(J\) determines at most one cyclic \(k\)-atom interval. Thus the number of length-\(k\) proper marked intervals satisfying (2.2) is at most

\[
\boxed{
N_{\rm gate}(k)\le2(r-1)\le12\mathbf b-2.
}
\tag{2.3}
\]

This bound is **independent of \(k\), \(q\), the number of unrelated boundary accesses and the non-LC impression fibers**. It is a count of **candidate interval states** for each fixed length, not a count of all attached tree components or all prime ends.

## 3. Theorem — every proper periodic critical return is an internal-cut gate cycle

### Theorem 3.1 (native cut-gate reduction of critical-return periodicity)

Suppose a **nonempty proper marked interval** \(J\) has an actual \(\Phi\)-periodic forward orbit of period \(p\ge1\), and at least one orbit state intersects the open critical limb \(\mathbf L_0\). Then **some state in this periodic orbit** has an endpoint at an internal critical cut in \(\mathsf{Cut}_{\mathrm{crit}}\). More strongly, **every critical-intersecting state** in this orbit has such an endpoint.

For each fixed length \(k\), this orbit can visit the critical limb only through the **at most \(2(r-1)\)** states in (2.3). Consequently, the missing *positive-length periodic critical-return* lemma can be proved by excluding cycles among these **actual internal-cut/side states**—it is unnecessary to assign a dual-WAD witness to arbitrary periodic intervals that have no such cut.

**Proof.** Every state of the periodic orbit is proper, because if some state equaled \(C\), then \(\Phi(C)=C\) and the orbit could not return to its original proper state. If a critical-intersecting state contained the whole \(\mathbf L_0\), Lemma 1.1 would make its next iterate \(C\), contradiction. Hence each critical-intersecting state satisfies (2.2) and has an internal cut by Lemma 2.1. The fixed-length count (2.3) gives the remaining assertion. \(\square\)

### Corollary 3.2 (the one-atom critical limb has **no** proper critical-return cycles)

If \(r=\ell(\mathbf L_0)=1\), then

\[
\boxed{
\text{no nonempty proper periodic marked interval has an orbit intersecting }
\mathbf L_0.
}
\tag{3.1}
\]

**Proof.** An open single-atom limb contains no internal marked cuts, so the candidate set (2.1) is empty. Theorem 3.1 forbids a proper periodic critical-return orbit. Equivalently, if a marked interval meets an open one-atom limb, it contains the whole atom \(\mathbf L_0\), hence saturates on its next iterate by Lemma 1.1. \(\square\)

**This conclusion is genuinely NATIVE and does not use the unproved PF/WAD witness bridge.** Its domain is the actual KKL source category and the additional source property \(r=1\). It is not a claim that all KKL critical limbs have length one.

## 4. Stronger corrected visit counting from the true internal-cut gate count

Fix the large-\(q\) short critical-visit class \(q\ge24\mathbf b\), so by the companion [canonical-Wave/closed-crest/open-limb theorem](./kkl_native_critical_atom_contact_and_full_wave_interface_20261106.md) every genuine short critical successor has a canonical regular positive **open crest core** \(J_i\), satisfying
\[
1\le \ell(J_i)<12\mathbf b,\qquad
\Phi^{m_i}J_i\subset J_{i+1},\quad m_i\ge1,
\]
and each \(J_i\) meets \(\mathbf L_0\) in a **full original atom**.

The remaining nonperiodicity hypothesis can now be made **even narrower**:

> **(CRIT-CUT-NONRETURN)** There exists no proper positive-length periodic \(\Phi\)-interval whose orbit reaches one of the *internal critical-cut/side states* in (2.3). This is a genuine native dynamics statement, to be proved through direct gate maps or a positive dual-WAD witness only for those states; **it is not inferred from \(\lambda_F>1\)**.

### Theorem 4.1 (sharper **conditional** critical-visit bound)

Assume in addition that the original native marked length is nondecreasing for proper iterates and that (CRIT-CUT-NONRETURN) holds. Let \(N\) be the number of consecutive **critical-visit transitions** in a continuing short critical-Wave chain, with genuine closed source actions defined. Then

\[
\boxed{
N < (2r-1)(12\mathbf b-1)
\ \le\ (12\mathbf b-1)^2.
}
\tag{4.1}
\]

**Proof.** Let \(k_i=\ell(J_i)\). The source-defined open-core inclusion and nondecreasing proper length imply that the \(k_i\) do not decrease. If a block of \(L=2(r-1)+1=2r-1\) **successive visit transitions** had no marked-length increase, every inclusion in that block would be an equality, since source and target are connected open marked intervals of the **same** integer length. Hence its visit states lie along a **single actual deterministic** \(\Phi\) orbit, all with positive length \(k\).

For each of the first \(L\) visit states in this block, the next transition is defined, has a positive iterate time, and ends at a **proper** continuing successor. Therefore the state cannot contain all of \(\mathbf L_0\), by Lemma 1.1 (otherwise its very next one-step iterate would saturate, and \(\Phi(C)=C\) forever). Every such state meets \(\mathbf L_0\) in a full atom by the native critical-crest theorem; hence each is one of the at most \(2(r-1)\) states of Lemma 2.1/count (2.3). But \(L=2(r-1)+1\) exceeds that number, so two different forward times yield the **same** interval, producing a proper periodic **critical-cut-return** orbit—contrary to (CRIT-CUT-NONRETURN). Thus every block of \(2r-1\) transitions strictly increases \(k\).

Since \(1\le k_i<12\mathbf b\), there can be fewer than \(12\mathbf b-1\) such length-increasing blocks. Therefore \(N<(2r-1)(12\mathbf b-1)\). Since \(r\le6\mathbf b\), \(2r-1\le12\mathbf b-1\), giving the final bound. \(\square\)

**One-atom case (unconditional strengthening).** If \(r=1\), a short positive core meeting \(\mathbf L_0\) necessarily contains the entire \(\mathbf L_0\) and its **next one-step** image is the whole boundary. Therefore no **further proper short critical successor** can follow it. This gives a direct terminality/no-continuing-short-chain result when \(r=1\) in the large-\(q\) class **without CRIT-CUT-NONRETURN or any dual PF witness**. The universal estimate (4.1) is intentionally stated conditional for arbitrary \(r\).

## 5. Exact remaining analytic proof obligation

The critical-return interval growth gap has now been reduced from an unconstrained prime-end atlas and a general dual-WAD visibility theorem to **the genuine return dynamics of at most \(2(r-1)\) endpoint-side states per fixed interval length**, with

\[
r\le6\mathbf b
\quad\Longrightarrow\quad
2(r-1)\le12\mathbf b-2.
\]

Each candidate is a **real marked interval** having an endpoint at one of the \(r-1\) internal cuts of the **critical limb itself**. It is not an abstract automaton state: its two sides and closed attachment records are fixed by KKL §6.1's actual \(f,\iota,\iota^*\). The spectral dual-WAD method is now only one potential way to exclude **cycles in this specific finite native gate family**. A direct source-defined endpoint-access orbit proof would be equally acceptable.

**What remains OPEN:** compute/prove no periodic critical-cut gate cycles for \(r\ge2\) in the full prime-primitive non-LC class; independently justify nondecreasing proper marked length and all necessary well-defined native closed iterations; handle the finitely many low-\(q\) stages \(q<24\mathbf b\) not covered by the high-rotation Wave simplification. No claim of full repaired Lemma 6.4 or MLC closure.

**Lean:** The companion module \`formalization/weighted/NativeWaveGate.lean\` certifies the **integer cut-overlap/endpoint gate** implications and the strict \(2(r-1)+1\) pigeonhole arithmetic. It does **not** verify the actual \(\Phi\)-orbit/non-return or KKL analytic \(\iota^*\) correspondence.

**Status:** genuinely native cut-gate localization, unconditional no-critical-return theorem for \(r=1\), sharpened conditional visit count; subject to independent specialist review. **Leave Issue #40, KKL_BOUNDED_VISITS_INTERVAL_GROWTH_REPAIR, KKL_PARABOLIC_WAVE_AMPLIFICATION and MLC OPEN.**

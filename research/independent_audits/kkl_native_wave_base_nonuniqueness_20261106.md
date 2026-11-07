# Issue #40 — a **native analytic nonuniqueness** of the Wave base in KKL Appendix A.1

**Date:** 2026-11-06.  
**Status:** **an actual marked-annulus counterexample to literal uniqueness of “the smallest” Wave base for disconnected laminations**. It uses disjoint positive-width foliated quadrilaterals in the **actual KKL carrier complement** with the **original vertex-side ideal marking**, not a synthetic circle automaton. It is a counterexample to a *definition-level uniqueness assertion* in the class of Wave-like laminations permitted by the literal Appendix A.1 wording; it is **not** a counterexample to KKL Proposition 6.5, the prime-end growth repair, Wave amplification, or global MLC.

**Primary source:** Kahn–Kapiamba–Lyubich [arXiv:2606.27272v1](https://arxiv.org/html/2606.27272v1), §4 (original vertex-side marking), Appendix A.1 (a lamination of valid marked paths subordinate to a connected multi-interval is called a Wave, and *“the smallest such multi-interval B”* is called its base), Appendix A.2 (positive-width foliations/valid WADs). The source **does not state that a Wave lamination must have connected support** or one arc homotopy class.

## 1. Exact analytic native carrier set-up

Fix **any actual KKL primitively renormalizable, periodically repelling stage** whose carrier complement \(V=\mathcal U\setminus\mathcal T\) is a connected annulus with its native inner Carathéodory circle \(C=\partial_C\mathcal T\) and whose **original vertex-side marking** has at least ten cyclically ordered nondegenerate atoms. Such large finite markings arise in the high-rotation part of the KKL category, because a rotation-\(1/q\) small-Julia cycle meets all \(q\) limbs and induces marked vertex sides.

Let the first ten consecutive atoms be \(\mathbf I_0,\ldots,\mathbf I_9\). The ten-atom construction below is the simplest explicit witness; **Corollary 2.2 proves equal-minimum-length ambiguity for every \(M\ge10\)** by placing the two packets opposite in even markings and using a 3-atom/4-atom asymmetry in odd markings. Thus no choice of minimum marked length repairs uniqueness in the whole large-marking native category.

Let \(Q_0\subset V\) be a **genuine embedded quadrilateral** in a conformal collar of the inner boundary with opposite end sides in compact nondegenerate subarcs of \(\mathbf I_0\) and \(\mathbf I_2\). Its connecting paths are chosen boundary-parallel to the **three-atom** arc \(\mathbf I_0\cup\mathbf I_1\cup\mathbf I_2\). Choose another genuine quadrilateral \(Q_1\subset V\), **disjoint from \(Q_0\)**, with opposite sides in \(\mathbf I_5\) and \(\mathbf I_7\), and paths boundary-parallel to the corresponding three-atom arc. Their existence and disjointness are elementary in the actual conformal annular collar: choose disjoint small boundary collars about the two disjoint three-atom segments and insert conformally nondegenerate quadrilaterals there.

Each quadrilateral carries a positive-extremal-width lamination \(\mathcal F_j\) by pairwise disjoint simple proper paths. Set

\[
\boxed{\mathcal F=\mathcal F_0\cup\mathcal F_1.}
\tag{1.1}
\]

The two packets are disjoint, so their union is still a genuine lamination, with \(\mathcal W(\mathcal F)>0\).

**The paths really are admissible.** Every leaf of \(\mathcal F_0\) is subordinate to the three-atom arc from \(\mathbf I_0\) to \(\mathbf I_2\), and every leaf of \(\mathcal F_1\) to the three-atom arc from \(\mathbf I_5\) to \(\mathbf I_7\). Neither homotopy class is subordinate to any connected marked multi-interval with at most **two** full atoms: both its endpoint atoms are distinct and **nonadjacent** in the relevant boundary-parallel class, and the alternative cyclic path goes the long way around the annular inner boundary. Thus each leaf is an actual marked path under KKL Appendix A.1, unlike the **withdrawn adjacent-atom construction**.

This construction does **not** require the planar filled Julia continuum to be locally connected. All endpoints are actual prime ends in the interior of original marked arcs.

## 2. Theorem: two equal smallest bases, neither containing the other

For the case \(M=10\), let \(B_+\) be the **proper** connected marked multi-interval containing the consecutive atoms

\[
\mathbf I_0,\mathbf I_1,\ldots,\mathbf I_7,
\]

and \(B_-\) be the other **proper** connected marked multi-interval containing the cyclic sequence

\[
\mathbf I_5,\mathbf I_6,\ldots,\mathbf I_9,
\mathbf I_0,\mathbf I_1,\mathbf I_2.
\]

The open connected sets include the marked cuts between the listed atoms but omit the two outermost cuts. Each has exactly **eight** full original marking atoms.

### Theorem 2.1 (native positive-width Wave-base nonuniqueness)

The actual positive-width lamination \(\mathcal F\) above is subordinate to **both** \(B_+\) and \(B_-\), yet

\[
\boxed{
B_+\not\subset B_-,\qquad
B_-\not\subset B_+,\qquad
\ell(B_+)=\ell(B_-)=8.
}
\tag{2.1}
\]

They are **both inclusion-minimal** among all connected marked multi-intervals to which \(\mathcal F\) is subordinate, and they are **both minimum-length** choices. Consequently there is **no least/smallest base** for \(\mathcal F\) under inclusion, and even “choose a base of shortest marked length” does **not** select one uniquely.

**Proof.** Each three-atom boundary-parallel leaf packet lies in both cyclic candidate bases, so both bases subordinate the entire genuine lamination. The first base contains the gap atoms \(\mathbf I_3,\mathbf I_4\) while omitting \(\mathbf I_8,\mathbf I_9\); the second contains \(\mathbf I_8,\mathbf I_9\) while omitting \(\mathbf I_3,\mathbf I_4\). This proves incomparability.

The source homotopy classes force any connected marked base subordinating \(\mathcal F\) to contain the *whole three-atom support block* \(\mathbf I_0,\mathbf I_1,\mathbf I_2\) and the disjoint three-atom support block \(\mathbf I_5,\mathbf I_6,\mathbf I_7\). A connected circular interval containing both must bridge one of the two intervening **two-atom gaps** \(\{\mathbf I_3,\mathbf I_4\}\) or \(\{\mathbf I_8,\mathbf I_9\}\), so it contains at least \(3+3+2=8\) atoms. The bases \(B_+\) and \(B_-\) each attain that bound. Removing either extreme occupied atom would lose a marked leaf endpoint; removing a gap atom disconnects the base or makes it fail to contain one of the two prescribed boundary-parallel arc classes. Thus both are inclusion-minimal and there is no smaller connected marked interval contained in both. \(\square\)

### Corollary 2.2 (equal-length nonunique bases for **every** \(M\ge10\))

The **equal-length** conclusion does not require an original marking with exactly ten atoms. It works for **every finite cyclic original marking with \(M\ge10\)**, by placing two packets with balanced gaps:

- If \(M=2s\ge10\), choose a 3-atom first packet supported on atoms \(0,1,2\) and a 3-atom second packet supported on atoms \(s,s+1,s+2\). The two unused connecting gaps both have **\(s-3\ge2\) atoms**. The two candidate minimal connected bases have equal length **\(s+3\)**.
- If \(M=2s+1\ge11\), choose the first packet on atoms \(0,1,2\) and the second on atoms \(s,s+1,s+2,s+3\), using an actual boundary-parallel **four-atom** marked path for the second quadrilateral. The gaps both have **\(s-3\ge2\) atoms**. The two minimal bases have equal length **\(s+4\)**.

Each packet has a valid marked leaf class of length \(3\) or \(4\), thus neither admits a forbidden two-atom shortcut. They lie in disjoint actual conformal-collar quadrilaterals, so the union is a positive-width KKL-marked lamination. Each minimal base must contain both entire packet support arcs and exactly one connecting gap; the two gap choices have the same size by construction. Thus **both minimal bases have equal minimum length but are incomparable** for every \(M\ge10\).

**Proof.** The counts and inequalities are immediate from the cyclic atom positions just specified. The source marked-path and geometric-minimality arguments are identical to Theorem 2.1; they do not depend on the equal size of the two packet supports. \(\square\)

**Category precision:** The construction is in the actual *marked annulus of a KKL stage*—not in an artificial degree-two circle quotient—and uses genuine proper paths/positive conformal widths. It does **not** specify a single explicit parameter \(c\) or an entire prime-primitive contact gate census. The theorem only concerns the **admissible Wave-definition input data**, which are available at any such stage with the stated marking. If a stricter category of “indecomposable/connected single-arc-class Waves” is intended, that missing hypothesis must be supplied, and this counterexample does not apply to that stricter category.

## 3. Narrowest correction and consequences for Issue #40

The literal Appendix A.1 wording says that \(\mathcal F\) subordinate to \(B\) is a Wave and calls *“the smallest such multi-interval B”* its base. The theorem shows this is not guaranteed for an arbitrary **disconnected** lamination satisfying the explicitly printed marked-path conditions.

There are two narrow safe repairs:

1. **Base-tagged Waves:** define a Wave as \((\mathcal F,B,E_-,E_+)\), with \(B\) an **explicit chosen inclusion-minimal** connected marked base, and \(E_-,E_+\subset B\) a **chosen minimal end pair** satisfying the one-end-of-each-leaf assignment. Then the crest \(C=B\setminus(E_-\cup E_+)\) is unambiguous **as a tagged object**, even if the same underlying lamination admits another tag. State critical visits and Wave-pushforward theorems for **these tags** and prove their conclusions independent of choice if needed.
2. **Indecomposable/single-arc packet restriction:** work with one connected foliated arc-homotopy packet (or impose an equivalent canonical-base condition) and prove a unique minimal base for that restricted Wave class. A union of two separated packets is then treated as two Waves, rather than forcing a nonexistent common canonical base.

The earlier [proper-base no-point-crest theorem](./kkl_wave_nonempty_crest_noncrossing_20261106.md) remains mathematically valid **for every specified proper minimal base with a specified minimal end pair contained in it**: its noncrossing proof uses only that data. The current result says one must not treat the base as **globally canonical** for all lamination unions without an additional source-defined rule. The [two-component deck-collision note](./kkl_two_component_wave_deck_collision_20261106.md) should likewise be understood as operating on **base-tagged** crests.

**This is a native-domain first-failure certificate, not full Issue #40 completion.** It does not prove KKL’s analytic Wave amplification theorem false: the proof may be repairable by choosing a canonical tag, splitting disconnected laminations, or restricting to indecomposable packets. Such a repair must also preserve extremal widths and the source's critical-visit quantifiers, and cannot be assumed automatically. The original open/closed \(\iota^*\) attachment and positive dual-witness obligations remain open.

## 4. Referee checks and trust boundary

- The two quadrilaterals must be built in the **actual conformal collar** with endpoints in the **original vertex-side atom interiors**, not a made-up cyclic word model.
- Each individual leaf uses a **three-atom homotopy class**. It is therefore **valid** under Appendix A.1's two-atom exclusion. Contrast the retracted adjacent-atom attempt.
- Each packet's **minimal supporting boundary block** must be retained with its homotopy type; merely seeing four endpoint labels is insufficient to distinguish the two bases.
- Connectedness of the **lamination's union** or a *single homotopy class* is **not** required in the printed source Wave definition. If a hidden convention adds it, the example certifies a **missing hypothesis**, not a counterexample to that restricted theorem.
- The theorem does not claim the resulting Wave is *wide*, *short* under KKL's critical limb notion, or participates in any actual critical-visit chain. It only refutes **unique smallest-base selection at the definition stage**.

**Status:** a real positive-width native annular first-failure certificate for universal base uniqueness; the correct repair is base-tagging or restricting to packets with canonical bases. **Issue #40, KKL_BOUNDED_VISITS_INTERVAL_GROWTH_REPAIR, KKL_PARABOLIC_WAVE_AMPLIFICATION, and MLC remain OPEN.** No specialist referee review or priority claim.

# Integration map for the corrected clone theorem

## 1. Scope and verdict

This note maps every live project claim that depends on either

1. the rejected positive-exponent reduction
   \[
     \widehat T_t(i,j)=\sum_{\gamma:i\to j}t^{|\gamma|},
   \]
   or
2. the resulting finite-block estimate
   \[
     \lambda_n^n\ge 2^{1/d^2}.
   \]

The fixed-cross-section spectral theorem is repaired in
`corrected_clone_theorem_derivation.md`. The repair is exact, but it does **not**
preserve the old finite-\(n\) constant. The correct reduced row-source operator is
\[
  \mathcal H(t)
  =
  \sum_{k=2}^{N}t^{-k}R_k
  =
  t^{-1}D(tI-Q)^{-1}C,
\tag{1.1}
\]
where \(R_k\) counts first-return paths of length \(k\), and
\[
  R:=\mathcal H(1)=\sum_{k=2}^{N}R_k.
\tag{1.2}
\]
For the literal length-\(n\) clone,
\[
  q_n:=\lambda_n^n=\rho(\mathcal H(\lambda_n)).
\tag{1.3}
\]
If \(R\) is irreducible and not a directed-cycle permutation and \(\dim R\le d\),
the sharp integer-matrix gap proved in
`corrected_clone_quantitative_audit.md`, Section 10, is
\[
  g_d^\sharp:=2^{1/d}.
\]
It follows by choosing two first-return loops at a branching vertex, pigeonholing
their binary concatenations by total length, and is sharp for a directed \(d\)-cycle
with one doubled edge. The project's previous bound
\(g_d^{\rm old}=2^{1/d^2}\) remains valid but is not the recommended constant. Then
\[
  \lambda_n^{-N}R
  \le
  \mathcal H(\lambda_n)
  \le R
\]
and hence, for \(n\ge1\),
\[
  q_n
  \ge
  \rho(R)^{\,n/(n+N)}
  \ge
  (g_d^\sharp)^{\,n/(n+N)}
  =
  2^{\,n/[d(n+N)]}.
\tag{1.4}
\]
In the project branch in which the surviving clone length satisfies \(n>N\),
\[
  q_n>(g_d^\sharp)^{1/2},
  \qquad
  q_n^{-1}<(g_d^\sharp)^{-1/2}
  =
  2^{-1/(2d)}.
\tag{1.5}
\]
Thus the corrected theorem still gives a universal complete-block contraction, but
the recommended generally valid displayed factor is \(2^{-1/(2d)}\), not
\(2^{-1/d^2}\). The exact dimension-only length-dependent factor is
\[
  2^{-\,n/[d(n+N)]}.
\tag{1.6}
\]
If the project elects not to integrate the sharp gap proof immediately, every
formula remains valid conservatively after replacing \(d\) in the exponent by
\(d^2\); that fallback gives \(2^{-1/(2d^2)}\).

For an entrywise retained operator
\[
  \widetilde{\mathcal H}_t
  \ge
  (1-\epsilon)\mathcal H(t)
\]
which satisfies its own corrected equation
\(\widetilde q=\widetilde\lambda^n
=\rho(\widetilde{\mathcal H}_{\widetilde\lambda})\),
\[
  \widetilde q
  \ge
  \bigl((1-\epsilon)g_d^\sharp\bigr)^{\,n/(n+N)}.
\tag{1.7}
\]
The sharp strict-expansion threshold is
\[
  \epsilon<1-(g_d^\sharp)^{-1}=1-2^{-1/d}.
\tag{1.8}
\]
For \(n>N\), however, the uniform multiplier is only
\[
  \widetilde q>
  \sqrt{(1-\epsilon)g_d^\sharp}.
\tag{1.9}
\]

The source defect remains real: the printed KKL \(+\lambda^k\) equation is still not
an importable theorem. What is now closed is the independent mathematical repair,
not the attribution to the printed proof.

## 2. Primary mathematical integration

| File and section | Old live claim | Correct replacement | Ledger effect |
|---|---|---|---|
| `corrected_clone_theorem_derivation.md`, Sections 2--5 and Theorem 4.3 | No old false claim. The revised file now proves both the fixed-graph repair and the sharp family-uniform estimate (1.4)--(1.5). | Treat this as the canonical theorem. Keep its hypotheses: literal common-delay clone, no \(E\)-to-\(E\) edge, nilpotent active block \(Q\), strong connectivity, and \(\rho(R)>1\). A primitive base supplies the non-permutation certificate but need not make delayed clones primitive. | This is the primary evidence that permits `KKL_CLONE_EIGEN` to move from `open` to `proved`. |
| `corrected_clone_quantitative_audit.md`, Sections 1--10 | Sections 1--8 first certify the conservative \(2^{1/d^2}\) gap; Section 10 then proves the sharp \(2^{1/d}\) replacement. | Use Sections 10.4--10.9 for downstream constants. Retain Sections 3, 5--8 for the exact delay, perturbation, eigencone, and large-entropy derivations. The conservative formulas remain valid fallback checks, not the canonical ledger constants. | Supplies the strengthened matrix-gap and variable-clone evidence without adding an obligation ID. |
| `corrected_clone_theorem_redteam.md`, Sections 1--9 | Independent audit of the corrected theorem. | Use its two-sided estimate \(\rho(R)^{n/(n+K)}\le q_n\le\rho(R)^{n/(n+2)}\), its \(n=0\) guard, and its counterexamples to uniform fixed-template convergence/eigencones. Lock “cross section” to directed walks and \(K\) to the actual largest first-return edge exponent. | Add as adversarial evidence for `KKL_CLONE_EIGEN` and the corrected variable/eigencone nodes; no new ID needed. |
| `virtual_clone_entropy.md`, Sections 1--2 | A “reduced labeled clone datum” uses positive weights \(t^{k(e)}\), so \(\widehat T_t\ge A\) for \(t\ge1\). | Replace the datum by \(R_k\), \(R=\sum R_k\), and \(\mathcal H(t)=\sum t^{-k}R_k\). Require \(2\le k\le N\), the literal-clone hypotheses, \(n\ge1\), and \(\rho(R)>1\). The order is \(t^{-N}R\le\mathcal H(t)\le R\), not \(\mathcal H(t)\ge R\). A positive-weight family may remain only as a separately named abstract weighted-transfer model; it is not a literal clone theorem. | No status change by itself; all clone nodes must cite the corrected datum. |
| `virtual_clone_entropy.md`, Theorem 3.1 | The gap is stated only for primitive integer matrices and uses the non-sharp bound \(2^{1/d^2}\). | Use the sharp theorem from `corrected_clone_quantitative_audit.md`, Section 10: every irreducible non-permutation integer \(d\times d\) matrix has \(\rho(R)\ge g_d^\sharp=2^{1/d}\). A primitive base plus the corrected Lemma 4.1 excludes the permutation case. | Strengthen both `PRIMITIVE_INTEGER_ENTROPY_GAP` and `IRREDUCIBLE_TRANSFER_ENTROPY_DICHOTOMY`; use the latter for corrected \(R\), which need not be primitive. |
| `virtual_clone_entropy.md`, Theorem 4.1 | \(q_n=\lambda_n^n\ge g_d\), hence Value contracts by \(g_d^{-1}=2^{-1/d^2}\), independently of length. | Prove (1.4). In the surviving long-corridor branch \(n>N\), use (1.5). Without a lower bound on \(n/N\), no uniform factor away from \(1\) follows. | `VARIABLE_CLONE_BLOCK_CONTRACTION` remains proved only after its statement is weakened and its dependencies include the corrected clone theorem and the irreducible entropy dichotomy. |
| `virtual_clone_entropy.md`, Theorem 4.2 | \(\widetilde q\ge(1-\epsilon)g_d\). | Replace by (1.7); retain threshold (1.8); record (1.9) when \(n>N\). The comparison must hold for the negative-weight family and the perturbed operator must satisfy its own corrected equation. | `PERTURBED_CLONE_CONTRACTION` remains proved after its statement is corrected. |
| `virtual_clone_entropy.md`, Theorem 5.2 | \(g_d\le q_n\le H^2\); positive weights lie in a compact interval; full-chain ratios are bounded by \(H^2\). | If \(\rho(R)\le H\) and \(n\ge N\), then \((g_d^\sharp)^{1/2}\le q_n\le H\), \(\lambda_n^N=q_n^{N/n}\le H\), and each nonzero return weight is at least \(H^{-1}\). Irreducibility and the integer entry bound give weighted entries in a compact set with upper bound \(H^d\), so both **reduced cross-section** Perron eigencones are compact. Chain-layer ratios are bounded by \(q_n\le H\). | `BOUNDED_ENTROPY_EIGENCONE` may remain proved after proof replacement and an explicit \(n\ge N\) (or another uniform \(N/n\)) condition. |
| `virtual_clone_entropy.md`, Section 6 | If \(\rho(R)>H\), then block contraction is \(<H^{-1}\). | Use \(q_n\ge\rho(R)^{n/(n+N)}\). For \(n>N\), contraction is \(<H^{-1/2}\). The sharper factor is \(H^{-n/(n+N)}\). | No separate node; update every use of the large-entropy branch. |
| `virtual_clone_entropy.md`, Sections 7, 9, 10 | Virtual realization must independently postulate an exact equation (2.2); the fixed theorem and limit are still open. | Once the literal corridor graph, typed incidence, and common delay are proved, (1.3) is a theorem. The open realization must instead prove the literal block hypotheses, \(n>N\) after endpoint absorption/grouping, the non-permutation/strict-return certificate, and the WAD/Value identification. The printed KKL proof remains quarantined, but the internal spectral repair is closed. | Add `KKL_CLONE_EIGEN` as a dependency of `H2_VIRTUAL_CLONE_REALIZATION`; that H2 node remains open. |
| `bc2_value_feature.md`, Section 6 and Source lock | Corollary 6.1 is conditional on an unspecified independent proof of the fixed-template limit. | Cite the corrected fixed-cross-section theorem. For one fixed datum, \(q_n\to\rho(R)>1\), so the existing eventual statement with any \(1<\mu_{\rm cl}<\rho(R)\) is unchanged. Retain the separate KKL Value and dynamical-hypothesis conditions. | Add `KKL_CLONE_EIGEN` to `CLONED_VALUE_BLOCK_CONTRACTION`; status remains proved. |

## 3. Downstream theorem and summary replacements

| File and section | Old claim | Required replacement | Ledger/status consequence |
|---|---|---|---|
| `block_contraction_program.md`, status discussion near the clone branch | Universal clone factor \(2^{-1/d^2}\). | Use the exact factor (1.6), or the uniform \(2^{-1/(2d)}\) after stating \(n>N\). | No node changes beyond `VARIABLE_CLONE_BLOCK_CONTRACTION`. |
| `master_transition.md`, clone paragraph in Section 5 | Forward Value contraction at most \(2^{-1/d^2}\). | Replace by \(2^{-n/[d(n+N)]}\), and by \(2^{-1/(2d)}\) in the certified \(n>N\) branch. Preserve the open WAD/error realization warning. | `MBTT` remains open. Its numerical margin must be recomputed with the corrected factor. |
| `dynamical_corridor_certificate.md`, Theorem 4.1 and Corollary 4.2 | The graph certificate is sent to the old positive-weight Theorem 4.1; Value factor \(2^{-1/d_0^2}\). | `FC6` already requires the surviving \(n>N_0\). Apply the corrected literal-clone theorem and use \(2^{-1/(2d_0)}\), or retain the sharper \(2^{-n/[d_0(n+N_0)]}\). The spectral equation no longer needs to be an extra hypothesis once `FC1`--`FC6` and typed incidence hold. KKL Value eligibility and the outgoing error bound remain extra hypotheses. | `FINITE_STATE_CORRIDOR_CERTIFICATE` remains proved. `FINITE_STATE_CORRIDOR_VALUE_COROLLARY` remains proved with the corrected constant through the variable-clone dependency. |
| `corridor_clone_criterion.md`, Corollary 3.3 and Source boundary | Points to the old clone contraction and says this note does not repair the spectral recurrence. | Point to the corrected theorem and state the \(n>N\) factor. The graph note itself still does not prove the spectral theorem, but it may cite the independent repair. | `EXACT_CORRIDOR_CLONE_CRITERION` and its graph dependents are unchanged. |
| `README.md`, Results 11--14 and ledger count | Fixed-clone limit is open; variable exact clones inherit the old full \(2^{-1/d^2}\) factor; counts are 8/95/29. | Say the printed source bridge remains rejected but the literal clone theorem is independently proved with negative return weights. State the sharp graph gap \(g_d^\sharp=2^{1/d}\), long-clone factor \(2^{-1/(2d)}\), and perturbation threshold \(1-2^{-1/d}\). If no new obligation ID is introduced, counts become 8 imported, 96 proved, 28 open. | Promote only `KKL_CLONE_EIGEN`; MLC remains open. |
| `manuscript.md`, clone paragraph in the virtual block theorem | Refers vaguely to a perturbation below the old graph gap \(2^{1/d^2}-1\). | State the actual relative-loss condition \(\epsilon<1-2^{-1/d}\), the corrected negative-weight equation, \(n>N\), and the multiplier lower bound \(\sqrt{(1-\epsilon)2^{1/d}}\). Do not equate \(2^{1/d}-1\) with the permitted relative entrywise loss. | Main theorem remains conditional/open. |
| `corridor_entropy_shear_dichotomy.md`, Theorem 3.1 and Corollary 3.2 | Direct framed-return gap \(2^{1/d^2}\) and Value factor \(2^{-1/d^2}\). | Strengthen to \(2^{1/d}\) and \(2^{-1/d}\). This direct-return factor has no clone square-root loss. | Strengthen `IRREDUCIBLE_TRANSFER_ENTROPY_DICHOTOMY`; status remains proved. |
| `corridor_support_automaton.md`, Theorem 4.1 and Corollary 4.2; `support_automaton_redteam.md`, repaired summaries | Displayed cyclic non-simple support gap \(2^{1/d^2}\). | Strengthen the spectral gap to \(2^{1/d}\). Keep the independent support-state count \(s2^{d^2}\) exactly as written. | Strengthen `BOUNDED_BRANCH_SUPPORT_WITNESS`; status remains proved. |
| `dependency_audit.md`, P56--P61, P71, P77, and minimal next target | P57/P71/P77 use the non-sharp graph gap; P58 has the false clone factor \(2^{-1/d^2}\); P61 has the conservative threshold but omits the corrected multiplier; P56 treats the fixed theorem as only conditional. | P56 cites the proved corrected fixed theorem. Strengthen P57/P71/P77 to \(2^{1/d}\). P58 uses (1.4)--(1.5) and states \(n>N\). P59 uses the corrected compactness bounds. P61 uses (1.7)--(1.9) and threshold \(1-2^{-1/d}\). The next-target text should request literal-clone hypotheses, not a free positive-weight recurrence. | Update descriptions; only the fixed clone spectral node changes status. |
| `source_ledger.md`, typed clone audit, variable-clone addendum, and transfer/shear addendum | Says the limit and eigenvector convergence remain open pending a corrected proof; records the old positive-weight variable theorem and \(2^{1/d^2}\) graph gaps. | Preserve the source no-go, then add that `corrected_clone_theorem_derivation.md` independently proves (1.1)--(1.3), the limits, and both typed cross-section eigenvector limits. Replace the variable theorem by (1.4)--(1.9) and record the sharp \(2^{1/d}\) internal graph theorem. | `KKL_PRINTED_CLONE_EQUATION_NO_GO` stays proved; `KKL_CLONE_EIGEN` becomes proved internally, not imported. |
| `kkl_transfer_orientation_audit.md`, Sections 6--7 and 10 | Calls \(t^{-k}\) only a candidate and describes the project's \(t^{k}\) model as the live declared clone model; says `KKL_CLONE_EIGEN` is open. | Keep the source criticism, but cite the independent block-equation proof showing that \(t^{-k}\) is the correct literal-clone operator. Relabel any \(t^k\) construction as an unrelated abstract weighted-transfer model. Update remediation status. | Same promotion as above. |
| `virtual_automaton_source_research.md`, top correction, Section 4.4, and Section 10 | Calls the mathematical spectral repair open and says the parabolic construction is usable only up to that repair. | Distinguish “not imported from KKL” from “proved internally.” The literature verdict is unchanged: no source constructs the virtual automaton. The literal finite graph now has an internal spectral theorem once its hypotheses are realized. | No analytic/open H1 or H2 status changes. |
| `transfer_convention_and_frame.md`, Section 2.2 | Allows only an independently verified clone equation as a hypothesis. | Retain the prohibition on importing \(+\lambda^k\); add the proved internal formula \(\mathcal H(t)=t^{-1}D(tI-Q)^{-1}C\) and its transpose for the project matrix. | No status change to the convention nodes. |
| `post_repair_semantic_audit.md`, final snapshot | Says the clone limit remains open and reports 8/95/29. | Add a superseding audit note recording the corrected theorem and, if IDs are reused, 8/96/28. Do not rewrite the earlier snapshot as though it had already included this proof. | Audit metadata only. |
| `research_log.md`, variable-clone entry and final clone quarantine entry | Historical entries record the positive-weight factor \(2^{-1/d^2}\), \(q\le H^2\), large-entropy factor \(H^{-1}\), and an open repair. | Preserve chronology and append a new dated supersession entry with (1.1)--(1.9), the sharp \(2^{1/d}\) gap, corrected eigencone bounds, and the promotion. | Counts become 8/96/28 if no node is added. |
| `audit_transfer_regressions.py`, clone regression | Tests that \(+\!k\) fails and says the \(-k\) equation merely “happens to hold.” | Rename or extend the test to certify the independently proved \(-k\) equation for the three-vertex example, retain the \(+\!k\) failure, and add a numerical check of \(q_n\ge2^{n/(n+3)}\). Diagnostics remain non-proof evidence. | No ledger status change. |
| `adversarial_audit.md`, A57 and A88 | A88 requests an independent repair; A57 records the conservative \(1-2^{-1/d^2}\) perturbation threshold. | Mark A88's mathematical repair completed internally while keeping the source import rejected. Strengthen A57 to the sharp threshold \(1-2^{-1/d}\), but record that the finite-\(n\) retained multiplier is (1.7), not \((1-\epsilon)2^{1/d}\). Add a short-clone test \(n/N\to0\), for which the old uniform factor fails. | No theorem promotion beyond `KKL_CLONE_EIGEN`; the matrix-gap statements are strengthened in place. |

## 4. Exact `proof_obligations.json` remediation

The least disruptive ledger repair reuses the existing ID
`KKL_CLONE_EIGEN`; no new obligation is necessary.

| ID | Current defect | Correct statement/dependency action | Status |
|---|---|---|---|
| `KKL_PRINTED_CLONE_EQUATION_NO_GO` | None. | Keep unchanged. The independent repair does not make the printed equation true. | `proved` |
| `KKL_CLONE_EIGEN` | Still asks for the repair and is `open`. | State the literal typed theorem: (1.1)--(1.3), \(\lambda_n\to1\), \(q_n\to\rho(R)>1\), and convergence of project-left/project-right cross-section weights; primitive base is sufficient for strictness, clone primitivity is unnecessary. Point primary evidence to Sections 2--5 of `corrected_clone_theorem_derivation.md` and adversarial evidence to `corrected_clone_theorem_redteam.md`. The no-go may remain a contextual dependency, but it is not a mathematical premise. | Promote to `proved`. |
| `CLONED_VALUE_BLOCK_CONTRACTION` | Conditional on an unspecified independently proved limit. | Add `KKL_CLONE_EIGEN` to dependencies and state the fixed-datum corollary. Keep `KKL_VALUE_CONTRACTION` and `KKL_TYPED_VALUE_INCIDENCE`. | Remains `proved`. |
| `PRIMITIVE_INTEGER_ENTROPY_GAP` | Its \(2^{1/d^2}\) statement is valid but non-sharp. | Strengthen to \(2^{1/d}\) using the first-return-loop pigeonhole proof. Use the correspondingly strengthened `IRREDUCIBLE_TRANSFER_ENTROPY_DICHOTOMY` in corrected clone dependencies. | `proved` |
| `IRREDUCIBLE_TRANSFER_ENTROPY_DICHOTOMY` | Its \(2^{1/d^2}\) statement is valid but non-sharp. | Strengthen the non-permutation branch to \(\rho\ge2^{1/d}\). | `proved` |
| `BOUNDED_BRANCH_SUPPORT_WITNESS` | Its displayed-square gap is \(2^{1/d^2}\). | The skeleton-length bound \(s2^{d^2}-1\) is unchanged, but the spectral gap of a cyclic non-simple \(d\)-dimensional displayed square strengthens to \(2^{1/d}\). | `proved` |
| `VARIABLE_CLONE_BLOCK_CONTRACTION` | False finite-\(n\) bound \(2^{-1/d^2}\). | Require corrected literal-clone data, \(\dim R\le d\), \(R\) irreducible non-permutation, maximum return length \(N\), and \(n>N\). State factor \(2^{-n/[d(n+N)]}<2^{-1/(2d)}\). Add `KKL_CLONE_EIGEN` and `IRREDUCIBLE_TRANSFER_ENTROPY_DICHOTOMY`; retain the Value and typed-incidence dependencies. | Remains `proved` after proof rewrite. |
| `PERTURBED_CLONE_CONTRACTION` | False multiplier \((1-\epsilon)2^{1/d^2}\). | Replace it by (1.7); retain strict threshold (1.8); state the \(n>N\) uniform margin (1.9). Add the corrected clone and irreducible-gap dependencies. | Remains `proved` after proof rewrite. |
| `BOUNDED_ENTROPY_EIGENCONE` | Evidence uses the wrong sign and \(H^2\) bound. | State compactness for the corrected return family, with a uniform \(N/n\) bound (the project already uses \(n>N\)); use \(q_n\le H\), nonzero weights \(\ge H^{-1}\), and chain ratio \(\le H\). Clarify that this is a reduced-cross-section/chain claim, not automatically a bound on every active-coordinate normalization. | Remains `proved` after proof rewrite. |
| `FINITE_STATE_CORRIDOR_VALUE_COROLLARY` | Inherits the old numerical factor through `VARIABLE_CLONE_BLOCK_CONTRACTION`. | No direct status change; its evidence must display the corrected factor. | `proved` |
| `H2_VIRTUAL_CLONE_REALIZATION` | Treats the exact spectral equation as an additional open postulate. | Add `KKL_CLONE_EIGEN`; require realization of its graph hypotheses and \(n>N\), after which the equation is automatic. Keep the source/WAD/Value/error realization obligations and the printed-equation no-go as a guard. | `open` |
| `H2_VALUE_FEATURE_REALIZATION`, `H2_ENTROPY_DICHOTOMY`, `MBTT`, `MLC` | Depend downstream on the clone margin. | Recompute margins using (1.5) or (1.9). No analytic realization follows from the graph theorem. | Remain `open` |

With this reuse-only plan, the ledger total remains 132 and the projected status
counts are
\[
  \text{imported}=8,\qquad
  \text{proved}=96,\qquad
  \text{open}=28.
\]

## 5. Independent claims and coordinated sharp-constant updates

The old \(2^{\pm1/d^2}\) matrix bounds remain logically true, but the sharp
\(2^{1/d}\) theorem should be propagated deliberately. A blind replacement by the
**clone** square-root factor would be wrong:

1. `corridor_entropy_shear_dichotomy.md`, Theorem 3.1 and Corollary 3.2, concern a
   single closed or canonically framed irreducible return matrix, with no delay
   exponent. Strengthen its graph gap to \(2^{1/d}\) and its direct Value factor to
   \(2^{-1/d}\), not to the clone factor \(2^{-1/(2d)}\).
2. `corridor_support_automaton.md` and `support_automaton_redteam.md` use the graph
   gap for a bounded-dimensional cyclic non-simple support witness. Strengthen that
   gap to \(2^{1/d}\). The Boolean-support skeleton length
   \(s2^{d^2}-1\) is a state-counting bound and does **not** change.
3. Strengthen `PRIMITIVE_INTEGER_ENTROPY_GAP`,
   `IRREDUCIBLE_TRANSFER_ENTROPY_DICHOTOMY`, and the spectral clause of
   `BOUNDED_BRANCH_SUPPORT_WITNESS` in place. Their statuses do not change.
4. `adversarial_audit.md` A57's sharp threshold becomes
   \(1-2^{-1/d}\). Its qualitative conclusion survives: the tolerance still tends
   to zero with dimension, now at order \(d^{-1}\) rather than \(d^{-2}\).
5. Every occurrence which quotes or refutes the printed \(+\lambda^k\) source
   equation should remain. It should be followed, where relevant, by a pointer to
   the independent negative-weight repair, not silently rewritten as though KKL had
   printed it.
6. `virtual_language_memory.md`, `virtual_core_cocycle_program.md`,
   `virtual_support_automaton_construction.md`, and
   `support_automaton_redteam.md` correctly insist that exact length remain in a
   counter/clone/weighted equation and correctly reject the printed equation. Their
   memory and pumping theorems do not change. They may add `KKL_CLONE_EIGEN` as the
   now-available spectral endpoint after a literal graph has been realized.
7. `corridor_network_calibration.md` uses “clone” only as one branch of the open
   transfer trichotomy and contains no old clone multiplier. Its calibration
   obligations are unchanged.
8. The clone counterexample passages in `adversarial_audit.md`,
   `post_repair_semantic_audit.md`, `virtual_automaton_source_research.md`,
   `kkl_transfer_orientation_audit.md`, and `research_log.md` remain valid historical
   or source-audit statements. Only their “repair still open” conclusions need a
   superseding internal-proof note.

## 6. Adversarial limits of the repair

The following downstream conclusions do not follow from the corrected theorem and
must remain open or be weakened.

1. **The old \(2^{-1/d^2}\) finite-block factor is not recoverable in general.**
   The one-dimensional gate already prevents that claim at finite \(n\). For fixed
   \(N>0\), (1.4) approaches \(g_d^\sharp\) only as \(n\to\infty\). For a uniform
   family with only \(n>N\), the sharp dimension-only conclusion supplied by this
   comparison is \(2^{-1/(2d)}\). (For \(d\ge2\), this happens to be at least as
   strong as the old numerical factor, but it follows from a different theorem and
   cannot validate the old positive-weight proof.)
2. **No lower bound on \(n/N\) means no uniform contraction.** For \(n=0\),
   \(q_n=\lambda_n^0=1\). More generally, the exponent \(n/(n+N)\) tends to zero if
   \(n/N\to0\). Endpoint absorption must be performed before checking \(n>N\).
3. **The large-entropy factor \(H^{-1}\) is not a finite-\(n\) theorem.** It must be
   replaced by \(H^{-n/(n+N)}\), or \(H^{-1/2}\) under \(n>N\).
4. **Primitivity does not propagate through delay.** The corrected spectral theorem
   needs strong connectivity and \(\rho(R)>1\), not primitive clones. Any use of the
   imported KKL Value theorem may still require a separately proved primitive
   dynamical block; `ROBUST_CLONE_PRIMITIVITY` is therefore not obsolete.
5. **Fixed-graph eigenvector convergence is not family-uniform compactness.** The
   corrected theorem normalizes on the fixed gate \(E_0\). Uniform control over a
   varying family needs bounded gate/active dimension, return depth, multiplicity,
   and support. The reduced eigencone theorem does not by itself control arbitrary
   WAD intersection lengths or every active-coordinate normalization.
6. **Literal-clone purity is essential.** Unequal delays, direct \(E\)-to-\(E\)
   edges, side branches at interior layers, omitted multiplicities, or a non-nilpotent
   active block change the Schur reduction. They are not perturbations of the exponent
   sign unless a new operator and a quantitative comparison are proved.
7. **The cross section is a walk condition and \(N\) must bound actual edge
   exponents.** If “path” is read as “simple path,” an active directed cycle may
   survive and \(Q\) need not be nilpotent. The test \(n>N\) must use the actual
   maximum first-return edge length \(K\), or a declared upper bound with the same
   counting convention.
8. **Fixed-template convergence is not uniform over varying multiplicities.** Even
   with one gate and bounded return depth, choosing the number of length-two returns
   of order \(e^n\) can force \(\lambda_n\to e\) rather than \(1\). The limit
   \(\lambda_n\to1\) applies after \(Q,C,D\) are fixed. The uniform finite-block
   lower bound is a different statement.
9. **The theorem is spectral, not dynamical.** It does not construct Dudko's virtual
   hull, prove the finite core/WAD incidence, establish phase--parameter transfer, or
   bound outgoing geometric error. Consequently no H1/H2 analytic obligation and no
   MLC dependency is closed by this repair alone.

## 7. Recommended edit order

1. Promote `KKL_CLONE_EIGEN` with the exact typed statement and evidence.
2. Rewrite `virtual_clone_entropy.md` around (1.1)--(1.9), then update the three
   clone contraction/eigencone ledger nodes.
3. Update `bc2_value_feature.md`, `dynamical_corridor_certificate.md`, and
   `corridor_clone_criterion.md`.
4. Propagate the corrected delay-adjusted margin through `block_contraction_program.md`,
   `master_transition.md`, `manuscript.md`, and `dependency_audit.md`.
5. Update source/status documents without erasing the printed-source no-go.
6. Extend the regression and adversarial audits, run `audit_proof.py` and
   `audit_transfer_regressions.py`, and verify the projected 8/96/28 count.

# Master mathematical QA report

Date: 2026-07-26

## 1. Executive verdict

This audit does **not** validate a proof of Mandelbrot local connectivity.
It does produce a materially safer research state:

1. one proposed Wave theorem has been disproved by an explicit analytic
   counterexample and quarantined;
2. the literal broad wording of the KKL coefficient-one Wave-pushforward
   assertion is contradicted under the printed definitions;
3. the narrower Dudko--Lyubich one-common-interval annular theorem is not
   contradicted;
4. the native KKL stationary argument has been reconstructed into four
   exact open gates;
5. the machine ledger now distinguishes a documentary source assertion
   from usable mathematics;
6. formal hypotheses are visible in the generated manuscript ledger;
7. a clause-promotion regression prevents an open mapped clause from being
   hidden beneath a proved parent; and
8. the corrected manuscript, regressions, extracted text, and targeted PDF
   pages have been checked.

The authoritative status is

```text
430 obligations
30 imported
292 proved
108 open

MLC                                      open
UNIVERSAL_PROTECTED_TOWER_CLOSURE        open
VAAPC-I                                  open
KKL_PARABOLIC_WAVE_STATIONARY_PROOF_REPAIR
                                         open
```

No global closure obligation was promoted.

## 2. Scope and stop rule

The QA pass froze proof construction and examined four layers:

1. source versions, frozen hashes, and custody;
2. the machine dependency graph and all public status surfaces;
3. the native KKL stationary proof at the locked source lines; and
4. every recent extremal-width, Wave, paired-response, and collision
   argument.

The pass used the following rule:

> A claim is retained as proved only if its definitions, quantifiers,
> curve-family type, measurability, degree, and constant dependence survive
> direct adversarial reconstruction. A failed claim is stopped at its first
> false inference and replaced by either an exact counterexample or a
> narrower open theorem.

Computational regressions were used only to test bookkeeping and finite
models. They did not promote an analytic obligation.

## 3. Independent QA records

| report | role | SHA-256 |
|---|---|---|
| `qa_dependency_status_2026-07-26.md` | source, ledger, dependency, and status-surface audit | `9D89E718AA877515DD18CD5A74498B2B7B52B8BC823DDF7EB5D7E7868F247F2A` |
| `qa_dependency_status_2026-07-26.json` | machine-readable companion snapshot | `FB7AD3CFF86A4BBC00049C485159D3DE3351FA21F39CD8DEB4F1B8E75C8B78D8` |
| `qa_native_kkl_stationary_2026-07-26.md` | line-by-line native stationary reconstruction | `DE82738A8A8494EDC0D9A7A77B4C089FFB968304EADB60E17C0A14E220FC9044` |
| `qa_extremal_wave_2026-07-26.md` | independent falsification audit of the Wave and response arguments | `A7FAD5F48B54B5AF73A3F8EFBBE21D11D5AC503AEE6710C6818B210E24C0AE9F` |

The reports were prepared independently and then reconciled against the
same locked sources.

## 4. Immutable mathematical sources used

The decisive local source files were:

| source | local SHA-256 |
|---|---|
| KKL master, `waves-with-Misha.tex` | `AD4C774806D9902AA54FA31C56AD6146D8034946F19CC5E9CEC3C51A3F94FDD5` |
| KKL stationary include, `not-all-good2.tex` | `B5D40812E40D2E44037A8FC249DB687211CD67275E66EFFF8E7F29BC7CEDFB01` |
| Dudko--Lyubich Feigenbaum source, `Feigen.tex` | `EB8C50CC51039A82317CF1951B1E333F23DF100773F8AD0DF0586AC7CD465DDF` |
| Dudko--Lyubich neutral source, `PseudoSiegelBounds.tex` | `4AE3253817EF8EEB76DF95FA411CB9C2B6CB0642C3C4AED4D8AE8305F2122172` |
| KL06 extremal-width appendix, `appendix.tex` | `EA2BE5CC544100D7931C9992E7ED476EBBE4CCE52FAF620BFF357071CB3916F3` |

The arXiv records were checked at:

- KKL, arXiv:2606.27272, version 1;
- Dudko ICM survey, arXiv:2512.24171, version 1;
- Dudko--Lyubich Feigenbaum, arXiv:2309.02107, version 3;
- Dudko--Luo--Lyubich, arXiv:2509.23031, version 2;
- Dudko--Lyubich neutral, arXiv:2210.09280, version 2; and
- BLOT, arXiv:2205.03157, version 4.

The title of arXiv:2509.23031 was normalized to the current
*Uniform a priori bounds for neutral renormalization. Variation II:
\(\psi^\bullet\)-ql Siegel maps*.

### Source-custody limitation

The project is not yet a completely self-contained source archive. The
dependency audit did not find local files matching five previously recorded
source-member hashes:

```text
D25 main.tex
DL25 main.tex
BLOT no-bounds.tex
CS15 Main.tex
L97 nest.tex
```

The recorded KL05 archive/member is also absent. This is a reproducibility
defect, not evidence that those cited theorems are false. Before calling the
package fully source-locked, restore the exact files or add a custody
manifest containing the immutable external location, arXiv version,
download date, archive hash, extracted member path, and member hash.

## 5. Severity and disposition table

| ID | severity | finding | disposition |
|---|---|---|---|
| QA-M1 | critical | Candidate Lemma 6.1 in `kkl_wave_local_end_collision_reduction.md` has an endpoint off-by-one error. | retracted |
| QA-M2 | critical | Candidate Lemma 6.2 and Theorem 7.1 fail because per-leaf translate span does not control collisions among distinct source components. | retracted; explicit counterexample recorded |
| QA-M3 | critical | The literal broad KKL coefficient-one Wave assertion is false under its printed definitions. | source statement retained only as documentary; no mathematical consumer |
| QA-M4 | high | KKL line 1576 does not prove the preliminary relative telescope and is circular as written. | new open Gate N1 |
| QA-M5 | high | KKL line 1603 lacks a pointwise certificate for two retained, proper, filter-surviving paths with distinct terminal images. | new open Gate N2 |
| QA-M6 | high | The final fixed-component exit lamination, measurable selection, and domination property are not constructed. | new open Gate N3 |
| QA-M7 | high | The final map and degree are mistyped; continuum degree is two, while whole-end degree still requires proof. | corrected proved continuum-degree result plus open Gate N4 |
| QA-D1 | high | The narrative paired-response route and the ledger's native route disagreed. | native route replaced by N1--N4; paired response labeled optional |
| QA-D2 | high | VAAPC clause mappings could be hidden beneath a future proved parent. | promotion guard and focused regression added; clauses remain open |
| QA-D3 | medium | Generated LaTeX suppressed formal hypotheses. | generator fixed; hypotheses and dependencies now print separately |
| QA-D4 | medium | Several locked source members are missing locally. | explicitly unresolved source-custody item |
| QA-D5 | medium | Optional, legacy, and documentary nodes were not visibly distinguished. | documentary role added and machine-enforced; optional/legacy prose corrected; broader role tagging remains nonessential hardening |
| QA-B1 | low | One new display requested an unavailable 8-point typewriter metric. | display converted to an ordinary enumerated ledger-ID list; mathematics unchanged |

## 6. Exact cyclic-cover counterexample

### 6.1 Construction

Let

\[
 S_H=\{z:0<\operatorname{Im}z<H\},\qquad T(z)=z+1.
\]

For a fixed integer \(M\ge2\), define

\[
 A_M=S_H/\langle T^M\rangle,\qquad
 A_1=S_H/\langle T\rangle,
\]

and let

\[
 f:A_M\longrightarrow A_1
\]

be the degree-\(M\) annular covering induced by the identity on \(S_H\).
Choose a finite ideal marking on the lower boundary of \(A_1\). Inside
one target fundamental collar, choose a proper marked ideal
quadrilateral \(Q\) carrying a Wave \(\mathcal F\) whose extremal width is

\[
 \mathcal W(\mathcal F)=w.
\]

The cross-ratio of the four ideal endpoints can be chosen so that \(w\)
is arbitrarily large, while the marking can be refined so that every leaf
is a KKL marked path.

Let

\[
 A'=f^*\mathcal F.
\]

The source family is the union of \(M\) disjoint conformal lifts of
\(\mathcal F\). Therefore the equality case of the finite Parallel Law
gives

\[
 \mathcal W(A')=Mw. \tag{6.1}
\]

Every lifted parametrized path pushes to the same target parametrized path.
The printed pushforward is a path family, not a multiplicity-weighted
current. Hence

\[
 f_*A'=\mathcal F,\qquad \mathcal W(f_*A')=w. \tag{6.2}
\]

The entire lower source boundary component is an allowed multi-interval
under the printed definitions, \(A'\) ends there, and the boundary/collar
degree on that entire component is unambiguously \(M\).

### 6.2 Contradiction

The literal coefficient-one assertion would supply a universal
\(c_{\rm W}\) and a target Wave \(A\subset f_*A'\) such that

\[
 \mathcal W(A')
 \le
 \mathcal W(A)+c_{\rm W}(1+\log M).
\]

Equations (6.1)--(6.2) imply

\[
 (M-1)w\le c_{\rm W}(1+\log M). \tag{6.3}
\]

Set \(M=2\) and let \(w\to\infty\). The right-hand side is fixed and the
left-hand side diverges, contradicting (6.3).

If one adds an unstated unique-smallest-base convention, one
zero-extremal-width outer leaf forces a connected common base without
changing either side of the contradiction.

### 6.3 Exact scope

This counterexample does **not** refute the Dudko--Lyubich annular theorem
for one Wave above one fixed boundary interval \(J\). The positive-width
translated lift components do not all crest above one such \(J\).

Therefore the safe fork is:

1. prove a restricted single-crest, single-rectangle, or
   nonrepetition Wave theorem and prove that every proof-used KKL packet
   satisfies that restriction; or
2. retain the repeated source conductance coordinates and charge their
   multiplicity linearly.

The scalar full-base degree cannot compress \(M\) independent width-\(w\)
source coordinates into one width-\(w\) target coordinate with only an
\(O(\log M)\) loss.

## 7. Width calculations that survived

### 7.1 Monotonicity

For \(\Gamma_1\subset\Gamma_2\),

\[
 \mathcal W(\Gamma_1)\le\mathcal W(\Gamma_2).
\]

Every retained use of subfamily monotonicity has this direction.

### 7.2 Exact occurrence Series law

If every leaf of \(S\) contains pairwise disjoint ordered subpaths from
families \(\Gamma^1,\ldots,\Gamma^r\), then

\[
 \mathcal W(S)
 \le
 \bigoplus_{i=1}^r\mathcal W(\Gamma^i),
\qquad
 \bigoplus_i x_i
 =
 \left(\sum_i x_i^{-1}\right)^{-1}.
\]

With exact occurrence families \(B^i\) and holomorphic images
\(\Gamma^i\), the one-sided transformation rule

\[
 \mathcal W(\Gamma^i)\le\mathcal W(B^i)
\]

gives

\[
 \mathcal W(S)\le\bigoplus_i\mathcal W(B^i).
\]

This remains proved under its explicit full-width, untrimmed,
leafwise-disjoint occurrence hypotheses.

### 7.3 Conditional paired-response algebra

If a separately proved coefficient-one packet theorem gives

\[
 \mathcal W(B^i)\le\mathcal W(C^i)+C_b
\]

for every actual source packet, and
\(M_C=\max_i\mathcal W(C^i)\), then

\[
 \mathcal W(S)
\le
\bigoplus_{i=1}^r(M_C+C_b)
=\frac{M_C+C_b}{r}.
\]

Thus

\[
 M_C\ge r\mathcal W(S)-C_b. \tag{7.1}
\]

The algebra in (7.1) is correct. Its source-Wave hypothesis is open, and
collision alone does not construct a common ambient output Wave. This
result is therefore an optional conditional route, not a native KKL
dependency.

## 8. Native KKL stationary reconstruction

Fix the source's parabolic bound \(b\) and

\[
 N=b+3,\qquad m=N-1=b+2.
\]

### 8.1 Preliminary telescope

The intended induction requires

\[
 \mathcal W(A_n\setminus A_{n+1})\le C_b
 \qquad(0\le n<N-1). \tag{8.1}
\]

The printed comparison at line 1576 instead attempts to control
\(A_n\setminus A'_{n+1}\) by an output difference that can be empty when
\(A_{n+1}=A'_{n+1}\), even though
\(A_n\setminus A'_{n+1}\) contains the unknown family
\(A_n\setminus A_{n+1}\). It is therefore unsupported and circular.
An aggregate bound for the total extracted Wave cannot imply the
relative complementary-family estimate (8.1).

Once (8.1) is independently proved, nestedness gives the valid finite
telescope

\[
 \mathcal W(A_0)
 \le
 \mathcal W(A_{N-1})
 +\sum_{n=0}^{N-2}
   \mathcal W(A_n\setminus A_{n+1}).
\]

This is Gate N1.

### 8.2 Pointwise break

For \(n\in\{b,b+1\}\), \(h=n+1\), and one occurrence
\(\alpha\in A_h\) avoiding the chosen separator, the two named portions
must be certified as:

1. retained proper depth-\(h\) components of the same occurrence;
2. survivors of every fine-marking and coarse-subordination filter;
3. compatible with the same stopping horizon; and
4. distinct after \(f^h\) as unparametrized terminal marked paths.

Only these facts imply that \(F_*^h\alpha\) contains two paths and
contradict \(h\)-step unbreakability. Distinct source sheets do not by
themselves imply distinct untagged images.

This is Gate N2.

### 8.3 Final measurable exit

At \(m=b+2\), choose one actual final component \(Q\). For every
\(\alpha\in A_m\), one must select a retained proper restriction
\(\beta_\alpha\) joining \(Q\) to
\(\mathcal K^m\setminus Q\), prove the selection measurable, specify the
repeated-incidence convention, and prove that every full restriction
\(\iota_m^*\alpha\) contains its selected leaf. Only then does the source
domination lemma yield

\[
 \mathcal W(A_m)\le\mathcal W(B),
\qquad B=\{\beta_\alpha:\alpha\in A_m\}.
\]

The printed proof does not perform this construction.

This is Gate N3.

### 8.4 Correct map, index, and degree

The final family is \(A_{N-1}=A_{b+2}\); \(A_N\) is not defined.
The covering lemma must be applied to \(f^m\), not to the dynamical
symbol \(F^m\).

Along the canonical continuum itinerary, the degrees are

\[
 1\cdot2\cdot1=2.
\]

Thus the printed degree-one assertion is false. The exact continuum
degree does not automatically certify the degree on the whole marked
ending multi-interval. A safe global bound is

\[
 d\le2^m=2^{b+2}.
\]

After Gate N3 supplies the actual marked ending family, the general
covering estimate gives

\[
 \mathcal W(B)\le d\,\mathcal W(C)+2d.
\]

The correctly typed fixed-\(b\) conclusion is

\[
 O_b\!\left(1+\mathcal W(\mathcal RF)\right),
\]

and becomes \(O_b(\mathcal W(\mathcal RF))\) only under an explicit
large-width hypothesis that absorbs the additive constant.

This is Gate N4.

### 8.5 Minimal active dependency

The machine ledger now records

```text
KKL_STATIONARY_RELATIVE_WAVE_CONTINUATION          [proved]
KKL_STATIONARY_POINTWISE_TWO_PATH_BREAK            [open]
KKL_STATIONARY_FINAL_FIXED_COMPONENT_EXIT          [open]
KKL_STATIONARY_TYPED_BOUNDED_DEGREE_PUSHFORWARD    [open]
    ->
KKL_PARABOLIC_WAVE_STATIONARY_PROOF_REPAIR         [open]
```

The four gates are not interchangeable.  Gate N1 was subsequently
proved by the integration recorded in Section 16; the following
logical separations still govern the three remaining gates:

- N2 does not imply the relative width bound N1;
- N2 does not assemble the measurable family required by N3;
- N3 does not repair the pointwise break at line 1603; and
- N4 cannot be applied before N3 supplies the correct family and marked
  ending multi-interval.

## 9. Dependency and tooling corrections

The following changes were made:

1. `KKL_WAVE_PUSHFORWARD_STATED` is an imported **documentary source
   record** only. It has no mathematical consumer, and the validator now
   rejects any dependency or hypothesis that tries to use it.
2. `DL23_ANNULAR_WAVE_BUFFER_EXTRACTION` records the narrower native
   one-common-interval theorem.
3. `KKL_LAMINATION_PUSHFORWARD_DEGREE_BOUND` records the valid general
   degree-dependent estimate.
4. `KKL_BROAD_WAVE_PUSHFORWARD_COUNTEREXAMPLE` is proved.
5. `KKL_WAVE_PUSHFORWARD_UNIFORM_PACKET_CONSTANT` remains open and now
   demands either a coherent-packet theorem or a multiplicity-aware
   replacement.
6. The conditional paired-response algebra depends only on exact Series
   conductance and lists the open packet theorem as a formal hypothesis.
7. The native stationary repair depends only on N1--N4.
8. The degree-two node was narrowed to the actual continuum-degree
   calculation.
9. The ledger generator now prints `Formal hypotheses` separately from
   `Proof dependencies`.
10. The proof audit rejects a proved/imported parent whose clause maps
    directly to an open target. `maps_to` remains a downstream
    correspondence and is not silently converted into a dependency edge.
11. The schema now records non-gating ledger roles. A
    `documentary_source_record` may report what a source prints but cannot
    license a mathematical dependency or hypothesis.
12. Four focused adversarial ledger-tooling regressions were added and
    incorporated into the complete regression suite.

The machine ledger at this pre-N1 QA freeze had SHA-256

```text
8ABD83C94A2AC621206B5FA7C2A593933428142A0D3489E455BDDB67109CF1A7
```

## 10. Corrections to research documents

The false collision reduction is visibly marked `RETRACTED`. Historical
analysis is retained only for forensic traceability. The active status was
reconciled in:

- `README.md`;
- `source_ledger.md`;
- `dependency_audit.md`;
- `manuscript.md`;
- `adversarial_audit.md`;
- `research_log.md`;
- `kkl_wave_uniform_constant_source_audit.md`;
- `kkl_stationary_typed_paired_wave_realization.md`;
- the machine ledger and generated appendix; and
- the LaTeX manuscript and release metadata.

Old counts and old “next theorem” statements are explicitly labeled
pre-QA or historical where retained.

## 11. Validation record

### 11.1 Machine checks

The following commands passed:

```text
python -m py_compile audit_proof.py
python -m py_compile audit_ledger_tooling_regressions.py
python -m py_compile audit_transfer_regressions.py
python -m py_compile latex/generate_ledger_tex.py
python audit_ledger_tooling_regressions.py
python audit_proof.py
python audit_transfer_regressions.py
```

The proof audit reported:

```text
ledger: valid (430 obligations)
statuses: imported=30, proved=292, open=108
target: MLC [open]
```

All focused ledger tests and all diagnostic transfer regressions passed.
Those tests validate bookkeeping and stated finite identities; they do not
prove an analytic open gate.

### 11.2 LaTeX and PDF

The final LaTeX build:

- regenerated the 430-entry appendix;
- ran TeX and BibTeX to completion;
- produced no TeX, BibTeX, citation, reference, overfull-box, or
  underfull-box warning;
- produced 196 pages and 5,956,250 bytes; and
- is byte-identical to the released PDF.

Build and release SHA-256:

```text
8CAFE3A0FC0663B0B71B174CD8314F9DC6B3D4E4C3090B11EC11007518908A39
```

Extracted text confirms:

```text
430 obligations
30 imported
292 proved
108 open
this manuscript does not claim an unconditional proof
the cyclic-cover obstruction
the four open native stationary gates
the optional status of the paired-response route
```

No massive visual scan was performed. Pages 112--113, changed by the
stationary QA insertion, and page 124, containing the documentary-role
ledger entry, were rendered and inspected. No clipping, overlap, broken
glyph, or unreadable identifier was found.

The pre-QA PDF was preserved at
`tmp/pdfs/marked_width_mlc_manuscript_preqa_2026-07-26.pdf`.
The intermediate pre-role-guard PDF was preserved at
`tmp/pdfs/marked_width_mlc_manuscript_pre_documentary_guard_2026-07-26.pdf`.

## 12. Global dependency verdict

The QA pass improves correctness but does not substantially shorten the
global proof:

```text
MLC
├── H1_MARKED_CONSTRUCTION                 open
├── MBTT                                   open
├── H3_COERCIVITY                          open
├── H4_RIGIDITY                            open
└── existing conditional reductions        proved only conditionally
```

UPTCR remains a formal six-clause closure proposition. Its clauses are not
proved merely because many local compiler and no-go statements now exist.
VAAPC-I remains open because the actual complete-horizon carrier package has
not been constructed.

The KKL stationary repair is a narrower source-repair project. Closing it
would remove one important primitive/parabolic obstruction; it would not by
itself prove UPTCR or MLC.

## 13. Gate N1 acceptance specification (subsequently passed)

The proof-development task frozen by this report was

```text
KKL_STATIONARY_RELATIVE_WAVE_CONTINUATION
```

not the optional paired-response realization.

### 13.1 Falsifiable statement

Fix \(b\), set \(N=b+3\), and use the actual source-defined nested
stationary occurrence families \(A_n\). Prove that there is a constant
\(C_b<\infty\), depending only on \(b\), such that for every
\(0\le n<N-1\),

\[
 \mathcal W(A_n\setminus A_{n+1})\le C_b. \tag{13.1}
\]

The proof must construct an occurrence-compatible Borel continuation
through the actual one-step Wave extraction. It must identify, before
measuring:

1. the original source occurrence;
2. the retained source restriction and its target occurrence;
3. every discarded restriction;
4. the fine and coarse endpoint markings;
5. the source and target Wave bases;
6. the sheet and parent-component data;
7. the buffer or collar charged to each discarded occurrence; and
8. the rule preventing duplicated transverse mass.

Modulo a width-zero exceptional family, the retained and discarded
occurrence sets must form a genuine measurable partition of the
proof-used source family.

### 13.2 Quantitative requirement

The argument must derive (13.1) from a **relative** extraction estimate.
The following are inadmissible:

- subtracting two aggregate upper bounds;
- replacing \(A_n\setminus A_{n+1}\) by an unrelated output difference;
- invoking the literal broad KKL coefficient-one Wave assertion;
- treating several source sheets with one target image as one
  conductance coordinate; or
- charging an unbounded multiplicity by \(O(\log d)\).

Before a coefficient-one Wave estimate is used, one of the following must
be proved:

1. **coherent-packet branch:** the actual source packet is supported in
   one common-crest/single-coordinate geometry, with no repeated
   positive-width source coordinate collapsing to the same target
   coordinate; or
2. **multiplicity-aware branch:** the source is partitioned into coherent
   coordinates and every target-collapse equivalence class is charged by
   a proved linear conductance term whose total is bounded by \(C_b\).

### 13.3 Acceptance test

Gate N1 was promoted only after:

1. the objects are the actual locked KKL occurrence families, not a finite
   ribbon-tree surrogate;
2. every selection is Borel or is obtained by a sourced measurable
   lamination theorem;
3. every curve family is correctly typed in its marked surface;
4. all discarded width is charged exactly once;
5. \(C_b\) is uniform over the stationary packet and independent of
   satellite period, rotation denominator, and local marking
   cardinality;
6. the cyclic-cover counterexample is excluded by a proved hypothesis,
   not by relabeling; and
7. no step invokes the stationary proposition being repaired.

### 13.4 Failure certificate

If (13.1) is false, stop at the first actual stationary block and record:

```text
stage n
source occurrence and Wave base
all coherent source coordinates
their widths
target-collapse equivalence classes
sheet and parent-component data
fine/coarse marking decisions
unbounded discarded-width mechanism
```

The required replacement invariant is then the vector of coherent source
conductances together with the target-collapse equivalence relation. A
scalar Wave width or scalar full-base degree is known to be insufficient.

## 14. Final skeptic checklist

Before the next promotion, explicitly answer:

1. Is the source family one Wave in the exact printed sense?
2. Is the stronger common-crest or nonrepetition property actually proved?
3. Is the family a set, multiset, weighted WAD, or measured lamination?
4. Can distinct source occurrences have the same untagged target path?
5. Does every selected component survive both endpoint filters?
6. Are properness and end-properness being kept distinct?
7. Is degree measured on a continuum, one access, a collar, or the whole
   ending multi-interval?
8. Is an aggregate estimate being misused as a relative estimate?
9. Is measurability proved before extremal width is assigned?
10. Is any additive constant being absorbed without a lower-width
    hypothesis?
11. Does any dependency path pass through a documentary-only node?
12. Are MLC, UPTCR, VAAPC-I, MBTT, coercivity, and rigidity still visibly
    open?

## 15. Pre-N1 stopping-point conclusion

The QA pass is complete as a falsification, correction, and release audit.
It has not closed MLC. It has prevented a false Wave theorem from entering
the proof chain and reduced the immediate native stationary task to a
precise relative-continuation theorem with a counterexample-sensitive
acceptance standard.

The next stage was required to attempt Gate N1 only. If N1 had failed on an actual
stationary packet, the failure must be used to enlarge the state by the
minimal multiplicity-aware conductance invariant before any further global
proof construction resumes.

## 16. Gate N1 integration addendum

Gate N1 passed the acceptance specification in Section 13.  The frozen
proof is `kkl_stationary_relative_wave_continuation.md`, SHA-256
`ADFC7BCD5A73CE7E7ABE12C11C3E2C4D778826B995BF9114C6F8B431EF38094F`.
The final integration audit is
`kkl_stationary_n1_integration_audit_20260726.md`.

We use only the rectifiable sub-scope of the native Dudko--Lyubich
Wave lemma.  The pre-pruning Borel atlas first splits the KKL packet, after round-annulus
uniformization, into a Borel rectifiable core and a zero-width
nonrectifiable family.  The native lemma is invoked only on the core.

The decisive analytic repair is then relative rather than aggregate.
In the native Dudko--Lyubich proof, the discarded rectifiable family is the union of
\(T=O(\log m)\) nonzero deck-span packets of \(O(1)\) width and one
final \(O(1)\) outer buffer.  The Parallel Law therefore gives

\[
 \mathcal W(\mathscr S\setminus\mathscr S^{\rm new})
 \le C(1+\log m).
\]

For the stationary degree-two packet this is absolute.  The Borel
width-envelope theorem replaces the potentially non-Borel discard by
a Borel super-discard with an arbitrarily small extra charge.  The
Borel ordered-Wave realization then supplies the complete occurrence
code, prime-end markings, singleton target direction, common
whole-component target-Wave typing, and full source saturation.
Sequential degree-two relative transfer proves

\[
 \mathcal W(A_n\setminus A_{n+1})\le C_b
 \qquad(0\le n<N-1),
\]

with \(C_b\) independent of the rotation denominator and all analytic
widths.

Two independent A/B source audits rejected the unsupported shortcut
from “genuine subwave” to measurable retained support.  The promoted
proof uses only the native proof-internal deletion estimate, so that
semantic gap is not a dependency.

The post-integration machine ledger contains:

```text
437 obligations
31 imported
299 proved
107 open
KKL_STATIONARY_RELATIVE_WAVE_CONTINUATION proved
KKL_STATIONARY_POINTWISE_TWO_PATH_BREAK open
KKL_STATIONARY_FINAL_FIXED_COMPONENT_EXIT open
KKL_STATIONARY_TYPED_BOUNDED_DEGREE_PUSHFORWARD open
MLC open
UPTCR open
VAAPC-I open
```

Gate N1 is the only gate promoted by this addendum.

<div align="center">

# A Marked-Width Reduction of Mandelbrot Local Connectivity

**Public research archive · manuscript · proof-obligation ledger · computational dossier**

Assembled, authored, audited, and publicly released by **Matthew Robert Wesney**

[![Research status: MLC open](https://img.shields.io/badge/status-MLC%20open-8a5a00?style=flat-square)](https://dovvnloading.github.io/loops-research-archive/#frontier)
[![Manuscript: 214 pages](https://img.shields.io/badge/manuscript-214%20pages-2f3e46?style=flat-square)](./marked_width_mlc_manuscript.pdf)
[![Proof ledger: 465 obligations](https://img.shields.io/badge/ledger-465%20obligations-2f3e46?style=flat-square)](https://dovvnloading.github.io/loops-research-archive/#ledger)
[![Proved: 316](https://img.shields.io/badge/proved-316-1f6f43?style=flat-square)](https://dovvnloading.github.io/loops-research-archive/#ledger)
[![Open: 115](https://img.shields.io/badge/open-115-8a5a00?style=flat-square)](https://dovvnloading.github.io/loops-research-archive/#ledger)

[**Explore the project page**](https://dovvnloading.github.io/loops-research-archive/) · [**Read the manuscript**](./marked_width_mlc_manuscript.pdf) · [**Read Paper 1**](./papers/paper1_canonical_localization/paper1_forced_noninjectivity_sheet_kernel_v1.0.1.pdf) · [**Read Paper 2**](./papers/paper2_rooted_end_compactification/paper2_direct_decoration_rooted_end_compactification_v1.0.1.pdf) · [**Inspect the proof ledger**](https://dovvnloading.github.io/loops-research-archive/#ledger) · [**Browse the research dossier**](./dossier.html)

</div>

> [!IMPORTANT]
> **The Mandelbrot Local Connectivity conjecture remains open.** This archive does not claim an unconditional proof of MLC. It presents a source-locked conditional reduction, records the hypotheses on which that implication depends, and exposes unresolved obligations rather than hiding them.

## Research program

This project studies the Mandelbrot Local Connectivity conjecture through a marked backward-transition framework for mixed renormalization towers. Its proposed state is not an unmarked continuum: it retains the ambient marked surface, a regularized carrier, satellite or neutral access data, a finite postcritical record, prime-end or sectorial boundary data, and the declared curve family.

The manuscript develops finite root-pullback and inverse-tree reductions, exact critical-value and attachment formulae, finite routing, a common-domain theorem, finite Wave-horizon closure under stated hypotheses, and source-locked corrections and no-go results. The final passage to MLC is conditional on open compactness, transition, and rigidity inputs.

## Paper 1 — forced noninjectivity and the sheet kernel

**Paper 1:** [*Forced Noninjectivity and the Sheet Kernel at Primitive Canonical Localization Seeds*](./papers/paper1_canonical_localization/paper1_forced_noninjectivity_sheet_kernel_v1.0.1.pdf) — 37 pages, Version 1.0.1, dated 2026-07-27.

A central structural discovery made while adversarially testing the marked-carrier proposal is that Kahn's canonical localization does **not** preserve global injectivity at ordinary primitive canonical seeds. The published localization machinery is deliberately formulated in terms of immersions rather than embeddings. Paper 1 shows that this caution is sharp: for every ordinary quadratic-like restriction of a quadratic polynomial that is primitively renormalizable of period $p>1$, the canonically localized inclusion is forced to be noninjective. This is a forcing theorem at every seed in the stated class, not merely an example showing that failure is possible.

### Mechanism of the forced collision

For $F=f^p$, the total degree is $2^p$, while the central component has degree $2$. The pulled central continuum therefore has $2^p-2$ excess components. The canonical source and target localizations treat these components asymmetrically: a peripheral loop around an excess component survives outside the source localization subgroup but becomes null after the corresponding target-side hole is filled. Its lifted endpoints are distinct in the source and identified by the localized inclusion.

The component count $2^p-2$ is an elementary degree budget and is **not** presented as the novelty. The new content claimed by Paper 1 is the identification of the actual dynamical subgroup defect, its canonical kernel model, and the peripheral-winding quotient that detects exponentially many independent directions.

### Canonical resolution and new sheet invariant

The noninjective localized inclusion admits a canonical resolution on the complementary-cover locus. It factors as a covering $q$ onto an embedded intermediate cover; within the paper's based commuting comparison class, that intermediate cover is unique. If $H_s$ and $H_t$ are the source and target localization subgroups and $K=a_*^{-1}(H_t)$ is the reflected subgroup, then the based sheet fiber is $K/H_s$, and it is infinite.

Paper 1 further identifies that fiber with the hole-filling kernel:

$$
N_{\mathrm{fill}}=\ker(a_*),\qquad
K=N_{\mathrm{fill}}\rtimes H_s,\qquad
N_{\mathrm{fill}}\twoheadrightarrow \mathbb{Z}^{\,2^p-2}.
$$

Consequently, the forgotten sheet system has at least $2^p-2$ independent peripheral winding coordinates. No finite raw list of sheets, tiles, or bounded-multiplicity labels can be complete without an additional theorem producing a future-faithful finite quotient.

| Paper 1 result | Meaning for the research program |
|---|---|
| **Forced canonical collision** | Global embedding preservation fails at every ordinary primitive canonical seed of period $p>1$. |
| **Covering/embedding resolution** | The correct localized object is an embedded intermediate cover together with its covering map and sheet transport, rather than an embedded pseudo-piece alone. |
| **Infinite coset fiber** | The sheet defect is intrinsically infinite; finite sheet bookkeeping cannot represent the unquotiented canonical localization. |
| **Kernel normal form and winding surjection** | The defect is the kernel of the source-to-target hole-filling map and carries a surjection onto $\mathbb{Z}^{2^p-2}$. This kernel identification and winding quotient are the paper's principal quantitative novelty. |
| **Exact propagation** | The collision and fiber data persist through the full, unselected exact Kahn equalizer tower on the complementary-cover locus. |
| **Abstract sharpness tests** | Two counterexamples show that the source hypotheses alone cannot restore injectivity, either for the annular collar model or for an abstract ψ-quadratic-like pair. |

### Consequence for the marked-width proposal

Paper 1 changes the admissible state space for the broader program. Any argument consuming canonical localization must retain the coset-valued sheet fibration and its path-lifting transport, synchronize the removed obstacle packet, or prove a faithful quotient theorem preserving every path, access, and observable used later. Treating the localized inclusion as a globally embedded carrier silently discards infinitely many sheets and is invalid at the ordinary primitive canonical seeds covered by the theorem.

The result is corrective with respect to an embedding-preservation route explored in this research program; it does **not** contradict Kahn or Kahn-Lyubich, whose published statements assert immersion rather than global embedding. The closest published anticipation is the observation that a component-index map can be surjective without being injective; Paper 1 upgrades that possibility to a forced collision for the glued canonical localization and then derives the sheet kernel, winding quotient, infinitude, transport, and exact base-change structure.

> [!CAUTION]
> Paper 1 does not prove or refute MLC, rigidity, a priori bounds, or local connectivity. It does not disturb the dynamical covering arrow, the embedded inner collar, the homeomorphism on filled sets, or the exact pullback squares. Its unconditional core is at ordinary primitive canonical seeds. Applications to Kahn-Lyubich decoration stages require an additional stage-alignment hypothesis and are deferred to a sequel; Paper 1 makes no decoration-stage realization claim.

## Paper 2 — direct-decoration rooted-end compactification

**Paper 2:** [*The Direct-Decoration Rooted-End Compactification*](./papers/paper2_rooted_end_compactification/paper2_direct_decoration_rooted_end_compactification_v1.0.1.pdf) — 20 pages, Version 1.0.1, dated 2026-07-27.

At a Kahn–Lyubich direct-decoration scale, and under the paper's explicit finite-depth graph-avoidance and standing hypotheses, Paper 2 realizes the binary end compactification inside one quadratic dynamical plane. Two univalent inverse branches generate finite fibers $K_w$ and nested end fibers $E_\omega$; their union $H_\partial$ is compact, those fibers are exactly its connected components, and the component quotient is the binary address compactification.

| Paper 2 result | Mathematical content |
|---|---|
| **Exact component quotient** | The component projection $\pi_\partial:H_\partial\to\Omega_\partial$ is continuous and closed, with fibers exactly $K_w$ and $E_\omega$. |
| **Shift dynamics away from the root** | On $H_\partial\setminus K_\epsilon$, the return map is a two-sheeted covering descending to first-symbol deletion on the binary address space. |
| **Planar control** | Every component is full, and the complement of $H_\partial$ is connected. |
| **Stable replacement theorem** | Fibers at an arbitrary set of finite addresses can be replaced inside pairwise disjoint Jordan cells without changing the component quotient; full replacements preserve connected complement. |
| **Protected-carrier theorem** | Finitely many protected prime ends can be transported to a full carrier meeting $H_\partial$ exactly in the selected fibers while preserving cyclic order. |

The abstract end compactification of a binary tree is classical. Paper 2's claimed contribution is its realization by direct-decoration inverse branches, puzzle pullbacks, and nested puzzle intersections in one dynamical plane, together with replacement and protected-access theorems in that same planar model.

> [!CAUTION]
> Paper 2 is an exact **one-scale model**. It does not identify the end fibers with small Julia sets, construct a self-return or renormalization map on an individual end fiber, establish cross-scale transitions, or prove MLC.
## Status at the source lock

| Item | Recorded status |
|---|---:|
| Source lock | **2026-07-27** |
| Manuscript | **214 pages** |
| Proof obligations | **465** |
| Proved in this program | **316** |
| Imported from cited literature | **34** |
| Open | **115** |
| Ledger target | **MLC — open** |

The stationary-Wave audit splits the native repair into four gates. The manuscript records the **relative-continuation gate as proved**; **pointwise two-path breaking**, **measurable final fixed-component exit**, and **typed bounded-degree pushforward** remain open. The Universal Protected-Tower Compactness and Rigidity Proposition (UPTCR), VAAPC-I, hypotheses H1–H4, and MLC also remain open.

Status labels are claims about this source-locked snapshot, not substitutes for the definitions, hypotheses, and evidence pointers in the manuscript and ledger.

## What is public here

| Artifact | Purpose |
|---|---|
| [Project page](https://dovvnloading.github.io/loops-research-archive/) | Scholarly overview, mathematical atlas, references, citation, and searchable proof ledger |
| [Main manuscript](./marked_width_mlc_manuscript.pdf) | The 214-page marked-width reduction and its explicit result boundary |
| **Paper 1:** [*Forced Noninjectivity and the Sheet Kernel at Primitive Canonical Localization Seeds*](./papers/paper1_canonical_localization/paper1_forced_noninjectivity_sheet_kernel_v1.0.1.pdf) | The 37-page Version 1.0.1 forced-collision theorem, canonical covering/embedding resolution, sheet-kernel model, and winding invariant |
| **Paper 2:** [*The Direct-Decoration Rooted-End Compactification*](./papers/paper2_rooted_end_compactification/paper2_direct_decoration_rooted_end_compactification_v1.0.1.pdf) | The 20-page Version 1.0.1 construction of the binary rooted-end compactification, exact component quotient, stable infinite replacements, and finite protected-carrier routing |
| [Machine-readable ledger](./ledger.json) | All 465 obligations, dependency links, evidence pointers, and statuses |
| [Unified proof program](./research/mlc_unified/) | Source ledger, dependency and adversarial audits, proof obligations, validations, and research log |
| [Companion papers](./papers/) | Drafts and extracted theorem-level materials for the localization, compactification, and protected-carrier subprograms |
| [Numerical work](./code/) · [results](./results/) · [figures](./figs/) | Reproducible exploratory computations and visual diagnostics; these are supporting evidence, not proof |
| [Research dossier](./dossier.html) | Archive-level synthesis of the public research effort |

This repository is intentionally an **archive of research state**, not a software package. Temporary files, caches, duplicate exports, private correspondence, local-path artifacts, and unrelated working material are withheld from the public snapshot.

## Mathematical lineage and attribution

The project is built in direct conversation with the established complex-dynamics literature. Foundational and frontier credit belongs to the original authors of the results used, tested, corrected, or extended here, including:

| Area | Prior authors and representative sources |
|---|---|
| Polynomial-like mappings and the MLC problem | **Adrien Douady and John H. Hubbard**, [*On the dynamics of polynomial-like mappings*](http://www.numdam.org/item/ASENS_1985_4_18_2_287_0/); **Jean-Christophe Yoccoz**, with Hubbard’s exposition of the local-connectivity theorems |
| Renormalization, rigidity, and a priori bounds | **Mikhail Lyubich**, *Dynamics of quadratic polynomials I–II*; **Jeremy Kahn**, [bounded primitive combinatorics](https://arxiv.org/abs/math/0609045); **Kahn and Lyubich**, [decorations](https://arxiv.org/abs/math/0609046) and [unicritical local connectivity](https://arxiv.org/abs/math/0505194) |
| Satellite and neutral renormalization | **Davoud Cheraghi and Mitsuhiro Shishikura**, [satellite renormalization](https://arxiv.org/abs/1509.07843); **Dzmitry Dudko and Lyubich**, [neutral bounds](https://arxiv.org/abs/2210.09280) and [Feigenbaum points](https://arxiv.org/abs/2309.02107); **Dudko, Yusheng Luo, and Lyubich**, [neutral renormalization II](https://arxiv.org/abs/2509.23031) |
| Bounds, obstructions, and the current frontier | **Alexander Blokh, Genadi Levin, Lex Oversteegen, and Vladlen Timorin**, [maps with no a priori bounds](https://arxiv.org/abs/2205.03157); **Levin**, [rigidity and non-local connectivity](https://arxiv.org/abs/0710.4406); **Kahn, Ilya Kapiamba, and Lyubich**, [parabolically bounded primitive renormalization](https://arxiv.org/abs/2606.27272); **Dudko**, [MLC and renormalization survey](https://arxiv.org/abs/2512.24171) |

The [project page’s reference section](https://dovvnloading.github.io/loops-research-archive/#references) and the manuscript contain the complete source-locked bibliography. These scholars are credited as authors of prior mathematics; they are **not represented as collaborators on this repository**, and no affiliation or endorsement is implied.

## Project authorship and stewardship

**Matthew Robert Wesney** is the named human author, research director, and archive steward of this independent effort. He established the research agenda, selected and locked the source corpus, framed and sequenced the investigations, directed the iterative workflows, adjudicated competing outputs, maintained the proof-obligation and adversarial-audit record, integrated the retained results, authored and curated the manuscript and project page, and authorized the public release.

This work was developed through a sustained human-AI research collaboration. **Anthropic (Fable 5 / Opus 5)** and **OpenAI (GPT-5.6 Sol)** provided substantial assistance throughout the research lifecycle, including adversarial testing of definitions and proof claims, counterexample search, proof-obligation analysis, source comparison, computational design, code generation and review, numerical experimentation, synthesis, manuscript development, technical editing, quality assurance, and archive preparation. Their contribution was integral to the iterative construction and stress-testing of the research program, rather than limited to incidental tooling or copyediting.

The collaboration was directed and orchestrated by Matthew Robert Wesney. He defined the objectives, supplied the research context, assigned and sequenced investigations, evaluated and reconciled model outputs, selected what entered the record, and retained responsibility for all final mathematical claims, status designations, citations, disclosures, and publication decisions. The AI systems are credited as substantial computational research collaborators; they are not human authors, and this acknowledgment does not imply review or endorsement by Anthropic or OpenAI.

Imported theorems remain attributable to their original authors. New arguments, syntheses, status judgments, corrections, and any errors in this archive remain the responsibility of Matthew Robert Wesney.

## Audit and reproducibility discipline

- Every substantive dependency is intended to terminate in an imported, proved, or explicitly open ledger item.
- Imported results are tied to the source-locked literature rather than treated as folklore.
- Counterexamples and no-go results are preserved because they constrain viable formulations.
- Numerical experiments are separated from theorem claims.
- The searchable web ledger is backed by both [`ledger.js`](./ledger.js) and [`ledger.json`](./ledger.json) so the public status map can be inspected without the interface.
- Historical drafts remain visible where they document the evolution of the argument; the main manuscript and source lock define the current public snapshot.

## Citation

Please cite **Wesney** for this archive and manuscript, and separately cite the original literature for any imported theorem used in derivative work.

```bibtex
@misc{wesney2026markedwidth,
  author       = {Wesney, Matthew Robert},
  title        = {A Marked-Width Reduction of Mandelbrot Local Connectivity},
  year         = {2026},
  howpublished = {Public research archive},
  url          = {https://github.com/dovvnloading/loops-research-archive},
  note         = {Research manuscript in progress; source lock 2026-07-27; MLC remains open}
}
```

## Reading order

1. Start with the [project page](https://dovvnloading.github.io/loops-research-archive/) for the scope and result boundary.
2. Read [Paper 1](./papers/paper1_canonical_localization/paper1_forced_noninjectivity_sheet_kernel_v1.0.1.pdf) for the forced canonical collision, its infinite sheet resolution, and the resulting correction to the carrier proposal.
3. Read [Paper 2](./papers/paper2_rooted_end_compactification/paper2_direct_decoration_rooted_end_compactification_v1.0.1.pdf) for the exact one-scale rooted-end compactification, component quotient, replacement theorem, and protected-carrier interface.
4. Read the [main manuscript](./marked_width_mlc_manuscript.pdf) for the full marked-width program, definitions, theorem statements, and open gates.
5. Use the [interactive ledger](https://dovvnloading.github.io/loops-research-archive/#ledger) to trace dependencies and isolate open obligations.
6. Consult [`research/mlc_unified`](./research/mlc_unified/) for the source, dependency, adversarial, and validation record.
7. Treat computations and figures as diagnostics unless a manuscript explicitly promotes them into a proved statement.

---

<div align="center">
<sub>Independent research archive · math.DS · source lock 2026-07-27 · MLC remains open</sub>
</div>
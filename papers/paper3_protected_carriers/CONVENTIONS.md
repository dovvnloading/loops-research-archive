# Drafting conventions for paper3 (Draft I) — binding for every cluster file

## Files

- Source of truth: `SOURCES/digest.txt` (exact text extracted from the
  2026-07-27 manuscript PDF; page markers `@@PAGE n@@`; ligatures may appear
  as `ﬁ` etc. — normalize when transcribing).
- Review being implemented: `REVIEW.md`.
- Reference transcription (previous audited extraction, correct statements
  but too short): `../../research/mlc_separate_papers_bundle/mlc_separate_papers/paper2/protected_carriers.tex`.
- Each cluster file is BODY-ONLY LaTeX (no preamble, no \documentclass, no
  \begin{document}, no \newtheorem, no \newcommand unless truly local).

## Preamble already provides

Macros: `\C` (complex plane), `\Z`, `\Chat` (Riemann sphere), `\Fill`,
`\Exp`, `\Int`, `\dist`, `\id`, `\Om` (Omega), `\Omfree` (Omega_free).
Use `\Subset` for compact containment (the manuscript's ⋐).

Theorem environments (all numbered by section): `theorem`, `proposition`,
`lemma`, `corollary`, `definition`, `example`, `warning`, `openproblem`,
`remark`.

TikZ is loaded with libraries: shapes.geometric, positioning, arrows.meta,
decorations.pathmorphing, patterns. Figures are inline TikZ in `figure`
environments with `\centering`, `\caption`, `\label{fig:...}`.

Cite keys available (do NOT invent others): `DH85`, `Dud25`, `Hat02`,
`KKL26`, `KL08`, `Moo25`, `MWman`, `New51`, `Pom92`, `Why42`.
`MWman` = the source manuscript itself.

## Fixed cross-cluster labels (use EXACTLY these; they are referenced from
other clusters and from the appendix crosswalk)

- B: `thm:no-least` (Thm 6.12), `prop:access-collision` (Prop 6.15),
  `fig:no-least`, `fig:access-collision`, `sec:obstructions`, `eq:B-trace`,
  `subsec:B-moral` (the last three promoted to the fixed contract on
  2026-07-27: cluster A references them)
- A: `sec:intro`, `sec:prelim`, `sec:comparison`
- C: `sec:certificates`, `def:certificate` (Def 10.1), `lem:tree-full` (10.2),
  `lem:crosscut-survival` (10.3), `thm:realization` (10.4),
  `prop:naturality` (10.5), `fig:collar`, `fig:certificate`
- D: `sec:criterion`, `lem:slits` (10.7 repaired), `rem:repair`,
  `thm:free-component` (10.8), `ex:no-common-component`, `fig:separation`
- E: `sec:packets`, `def:packet` (10.9), `lem:packets` (10.10),
  `thm:common-domain` (10.11); `sec:audit`, `lem:fill-absorption` (10.12),
  `lem:port-localization` (10.13), `thm:audit` (10.14),
  `prop:cellwise` (10.15), `ex:merger`, `fig:merger`
- F: `sec:decoration`, `lem:nested-packets` (10.39), `thm:full-fibers` (10.40),
  `lem:jordan-nbhd` (10.41), `thm:gap-cells` (10.42),
  `thm:packet-replacement` (10.43), `lem:impression-port` (10.44),
  `thm:carrier` (10.45), `fig:cells`, `sec:scope`

Internal labels beyond these: prefix with your cluster letter, e.g.
`eq:D-slit-normal`.

## Statement fidelity rules

1. Every reproduced result carries its manuscript number in the bracketed
   title, e.g. `\begin{lemma}[One-ended slits do not disconnect a plane
   domain; manuscript Lemma 10.7, repaired]\label{lem:slits}`.
   All others say `manuscript Theorem 10.4` etc. with no `repaired`.
2. Statements are transcribed faithfully (notational streamlining only).
   The ONLY intentional divergence is the Lemma 10.7 repair and the
   rewritten proof of Theorem 10.8 (cluster D), which must be flagged in
   `rem:repair`.
3. Never promote: no claims about UPTCR, virtual carriers, Wave horizon,
   MLC, or manuscript open problems 10.6/10.50-10.52/10.55/10.57/10.58.
   Mention them only as explicitly open, as the manuscript's Warning 10.59
   does.
4. Proofs may be expanded for readability but must not silently change the
   argument. If you strengthen wording, keep the mathematical content
   identical to the digest.
5. Tone: professional research-paper prose, amsart idiom, no bullet-point
   mathematics outside enumerated theorem clauses, no first-person plural
   excess. English throughout; "fullification" and "atom" are the
   manuscript's terms — keep them but define them at first use.

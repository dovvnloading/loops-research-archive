# Loops research archive

Public archive of computational experiments, manuscripts, theorem ledgers, and audited research on Mandelbrot local connectivity (MLC).

Release snapshot: 2026-07-27.

## Scope and status

The central question is whether the Mandelbrot set is locally connected. MLC remains an open conjecture. Nothing in this archive claims a proof of MLC or density of hyperbolicity.

The repository preserves the computational reconnaissance, working manuscripts, source material authored for this project, reproducible numerical results, theorem-level no-go results, conditional reductions, and audit records produced so far. Individual manuscripts state their hypotheses, non-claims, and machine-assistance disclosures.

## Contents

- [Computational dossier](dossier.html): cited research narrative and numerical findings.

- [Numerical code](code/) and [results](results/): experiments, JSON outputs, and rendered figures.

- [Research notes](docs/): condensed and expanded literature reconnaissance.

- [Paper sources](papers/): current working-paper TeX sources and selected reading PDFs.

- [Unified proof program](research/mlc_unified/): marked-width reduction, theorem ledger, audits, source, figures, and final manuscript PDF.

- [Research push bundles](research/): chronological theorem-level intermediate packages retained as research evidence.

## Reproduction

The numerical experiments use Python 3.12 or newer. Install the dependencies listed in [requirements.txt](requirements.txt), then run the experiment scripts from [code/](code/). The paper sources are standard LaTeX sources; their PDFs are included as reading artifacts and the source files remain authoritative for the working drafts.

## Archive boundary

This public release intentionally excludes private correspondence, external-chat material, copied primary-source archives, local-machine paths, caches, bytecode, temporary renders, build logs, superseded bulk outputs, and uncurated raw workflow data. The local workspace was not modified to create this release.

Please treat all results as research artifacts for independent verification. Cite the individual manuscript or artifact that supports any claim.
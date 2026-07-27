# MLC Research Push II artifacts

This folder contains the theorem-level output for the finite-word second-portrait, end-collapse, and critical-spine push.

- `mlc_research_push_2.md`: full research memo, proofs, attacks, ledger effects, and the revised end-attachment target.
- `mlc_manuscript_insertions_push_2.tex`: ready-to-insert LaTeX theorem package.
- `mlc_manuscript_insertions_push_2.pdf`: compiled and render-verified seven-page insertion package.
- `mlc_ledger_patch_push_2.json`: proposed machine-readable status/dependency update.
- `critical_spine_audit.py`: validator for the stagewise degree-ladder recurrence and criticality swaps.
- `critical_time_shear_example.json`: explicit `(2,1)` versus `(1,2)` audit input.
- `critical_time_shear_report.json`: generated audit report.

The main constructive theorem is the retimed finite-cylinder pseudo-quadratic-like pair

`(f^{N_w+r}, f^{N_w})`,

which transfers every localized root portrait, filled carrier, and finite protected marking to every finite direct-decoration word. The end analysis proves canonical prime-end coding, Euclidean collapse of unrescaled inverse charts, and exact constancy of the normalized internal germ. The remaining end problem is construction of an analytic prime-end blow-up or rescaled marked fiber carrying that germ. The planar-collapse theorem proves that a nondegenerate limit cannot remain locally embedded in the original plane.

The conservative ledger proposal promotes `FINITE_HORIZON_ASSEMBLY`. Promotion of `MAPPING_TELESCOPE` requires rewriting the old under-specified statement with relative-cover compatibility and post-quadratic critical-spine retention. No artifact claims an unconditional proof of MLC.

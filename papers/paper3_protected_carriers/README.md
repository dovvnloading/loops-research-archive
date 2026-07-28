# Paper 3 — Protected planar carriers

This directory contains two intentionally separate research drafts.

- `paper3_draft1.pdf` is the frozen 79-page extraction reviewed on
  2026-07-27. It includes the direct-decoration application now contained in
  Paper 2.
- `paper3_draft2.pdf` is the re-architected standalone paper,
  *Protected planar carriers: separation ledgers and access-preserving
  routing*. It removes that overlap, corrects the prime-end conventions, and
  adds the attachment and limit theory described in `CHANGES_V2.md`.
- `RESEARCH_ASSESSMENT.md` records the repository-wide value, proof, novelty,
  and publication audit, including the remaining project-level gates.
- `QA_REPORT.md` records the zero-warning Draft II release audit and final
  artifact hash.

Draft II is assembled from `skeleton_v2.tex` and the selected files under
`extracted/`. Its build validates assembly, compiles twice under a fixed
source epoch, requires byte-identical PDFs, and runs the release QA. Build it
with Python 3.10 or newer, `pypdf`, and Tectonic. The script uses the
repository-local Tectonic binary when present, then an installed `tectonic`
command; set `PAPER3_TECTONIC` to an executable path to override discovery.
From PowerShell, run:

```powershell
powershell -NoProfile -ExecutionPolicy Bypass -File .\build_v2.ps1
```

The build produces:

- `main_v2.tex` — assembled source;
- `build_v2/main_v2.pdf`, `build_v2/main_v2.log`, and the captured console
  diagnostics;
- `paper3_draft2.pdf` — stable handoff copy;
- `output/pdf/protected_planar_carriers.pdf` — publication artifact.

The paper is a finite planar-topology and proof-technology contribution. It
does not claim a new case of Mandelbrot local connectivity, a virtual carrier,
or closure of any open all-depth gate in the main project.

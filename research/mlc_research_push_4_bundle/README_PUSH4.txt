RESEARCH PUSH IV - END PLUMBING FULL TRACE RESPONSE
Date: 2026-07-25

Verdict
-------
The direct-decoration END_PLUMBING_TRACE_RESPONSE_CONTROL gate is proved for
source-authorized, trace-compatible ray/equipotential collars.

Critical correction
-------------------
The Push III single-edge nodal response estimate did not control arbitrary
H^{1/2} interface traces. It is superseded unless each cross-section is
explicitly shorted to one electrical electrode. The replacement is the exact
full Dirichlet-to-Neumann trace operator and its trace-renormalized long-neck
estimate.


Proof-audit correction
----------------------
The exact mean-collapse theorem distinguishes a formal one-dimensional fixed-shape
trace space from genuine electrical shorting. With constants admissible (the
physical electrode case), mean-only response is exact precisely for constant
traces.

Main formulas
-------------
Exact neck operator:
  N_R = [[A coth(RA), -A csch(RA)],
         [-A csch(RA), A coth(RA)]],
with the zero-mode value 1/R.

Trace-renormalized model:
  two half-cylinder A responses + exact zero-mode resistor 1/R.

Sharp relative error:
  eta(R) = 2/(exp(pi R)-1).

Strict-transition margin:
  mu_eff = mu*(1+eta)/(1-eta),
  strict when eta < (1-mu)/(1+mu).

Files
-----
mlc_research_push_4.md
  Full theorem-level memo and correction analysis.

mlc_manuscript_insertions_push_4.tex
mlc_manuscript_insertions_push_4.pdf
  Six-page, render-verified manuscript insertion.

mlc_ledger_patch_push_4.json
  Proposed machine-readable correction and promotion patch.

full_trace_plumbing_audit.py
full_trace_plumbing_report.json
  500-trial Fourier/Schur-complement stress test.

pdf_preflight_push4.txt
  PDF preflight report.

Remaining global gaps
---------------------
H2_RESPONSE_REALIZATION, a universally bounded response/WAD/Value quotient,
MBTT, geometric coercivity, mixed-tower rigidity, UPTCR, and MLC remain open.

Audit summary
-------------
500 randomized trials passed.
Worst sharp-bound excess: 3.33e-16.
Worst semigroup error: 7.11e-15.
Worst compact-limit bound excess: 8.88e-16.
The scalar-collapse counterexample has zero trace means but energy pi at R=8.

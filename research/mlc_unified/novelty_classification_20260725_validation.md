# Novelty-classification validation

Date: 2026-07-25  
Source: `research/mlc_unified/proof_obligations.json`  
Source SHA-256: `A7DC25D9B2A1753A52C8947C51E63ECE146DE39476DD5B4182BF61AABA5F37C4`

## Result

The sidecar contains exactly one classification record for every obligation whose ledger status is `proved`.

- proved obligations in ledger: **209**
- sidecar entries: **209**
- distinct sidecar IDs: **209**
- missing proved IDs: **0**
- extra IDs: **0**
- duplicate IDs: **0**
- exact ledger-order match: **yes**
- all five required fields present and nonempty: **yes**
- ledger statuses modified: **no**

## Classification counts

| Class | Count |
|---|---:|
| computational/finite diagnostic | 8 |
| negative counterexample/no-go | 41 |
| unclear | 1 |
| standard/classical | 71 |
| direct formal corollary/compiler | 85 |
| potentially original analytic/dynamical theorem | 3 |

Total: **209**.

## Interpretation

`novelty_confidence` is qualitative and does not assert publication priority. The three `candidate_unverified` entries are one dependent direct-decoration construction. The sole `unresolved` entry is the corrected delayed-clone spectral theorem. Negative results are classified by mathematical role even when a tailored counterexample may itself be new.

No classified node closes an open global MLC gate. In particular, the sidecar makes no change to VAAPC-I, UPTCR, MBTT, coercivity, rigidity, or MLC.

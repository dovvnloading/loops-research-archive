---
ledger: NOV26_OPEN_SAT_WAVE
result: evidence
ai: OpenAI ChatGPT, GPT-6 Astra Pro; proof search, numerical exploration and adversarial review
human_review: none
---

<a id="near-parabolic-return-shape-20261127"></a>

# Rejected near-parabolic return-jet route: no new theorem

Ledger statement being addressed:

> Satellite/near-parabolic canonical transfer: The refused primitive v1 types supply neither a complete satellite canonical Wave nor an attachment angular electrode for the three near-parabolic tips.

## Claim

**No mathematical result meeting the requested standard was obtained.** This packet preserves a numerical experiment and the reason the proposed research route was rejected. The front-matter classification is evidence only; it is not a partial theorem, an obstruction theorem, or a submission for ledger promotion. The draft is to be closed without review so the obligation is free again.

The requested result had to be new mathematics bearing directly on the open obligation and a Lean theorem compiled by the unchanged CI with no proof holes or new assumptions. There is no such theorem in this packet.

## Evidence

### Initial claim and actual objects

Baseline main was `fe12f2a86cab3be5d610fcf37781c3ea5e8c3c64`. The draft claim was opened in [PR #258](https://github.com/dovvnloading/loops-research-archive/pull/258), after committing its initial scope in `872e3750792af68b1c92c27acd625c1ed2557416`.

The proposed target concerned the existing actual family
`LoopsParabolic.Shot k t e`. Write c=-7/4+t, f_c(z)=z^2+c,
H_t(y)=-f_c^3(-y), and p=3(k+2). The existing family has
H_t^(k+2)(0)=e and H_t^(k+2)(e)=-e, together with complete real
channel itineraries. Its full physical return has the expansion

    f_c^p(z) = -e + A z^2 + B z^4 + higher terms.

Thus f_c^p(e z)/e has quadratic coefficient A e and quartic
coefficient B e^3. The candidate was a uniform positive lower bound
on the latter, followed by a complete-disk approximation obstruction.

This was deliberately stronger than showing that a finite iterate has
high degree or that one finite coefficient is nonzero. Those facts
would not constitute the requested advance.

### Numerical exploration

[explore_return_jets.py](explore_return_jets.py) uses 60-digit mpmath
arithmetic and heuristic bisections. It records candidate collisions,
not certified roots or every member of the Shot family.

| k | physical p | candidate e | A e | B e^3 |
|---:|---:|---:|---:|---:|
| 4 | 18 | 0.00104545462996 | 1.99977574111 | 0.000224958876675 |
| 8 | 30 | 0.000439393093486 | 1.99985621634 | 0.000143898591833 |
| 16 | 54 | 0.000290871227512 | 1.99988944857 | 0.000110599663206 |
| 32 | 102 | 0.000252051184797 | 1.99989959894 | 0.000100436679843 |
| 64 | 198 | 0.000241760448583 | 1.99990241474 | 0.0000976178734922 |
| 128 | 390 | 0.000239075389319 | 1.99990315864 | 0.0000968732107166 |

The complete printed output, including parameters, collision residuals
and second-flight exits, is in [numerical_output.txt](numerical_output.txt).
The root agent independently reran the same computation to completion
with exit code zero. Residuals smaller than 10^-29 are numerical diagnostics,
not error enclosures or proof. Neither a limit nor a positive uniform
lower bound follows from this table.

Reproduction, requiring mpmath:

    python3 contributions/near_parabolic_return_shape_20261127/explore_return_jets.py

The script is intentionally not called check_* or verify_* and is not
registered as a certificate.

### Quantitative route considered, but not proved

A possible approach to a lower bound on e uses v_t(y)=H_t(y)-y.
If convexity is established on the appropriate corridor and both y and
H_t(y) lie there, then

    H_t'(y) v_t(y) <= v_t(H_t(y)).

This would telescope derivative products during the slow channel flight.
A finite number of exit factors and the actual collision difference
could potentially give a period-independent bound on e. This remains an
unformalized proposed route; its constants and complete quantifiers
have not been certified. It is not counted as a theorem.

### Why the route was rejected

There are two separate failures.

1. **Novelty is not supplied by qualitative nonquadraticity.**
   Blokh, Levin, Oversteegen and Timorin, *Maps with No a Priori Bounds*,
   Communications in Mathematical Physics 406, 141 (2025),
   [Proposition 4.2 and its proof](https://link.springer.com/article/10.1007/s00220-025-05303-8),
   already use Lavaurs convergence near a period-three parabolic parameter
   to construct renormalizations with nondegenerate limiting intervals.
   Their extended limiting return has three critical points.
   Their particular period construction is not identified here with
   every archive Shot. The source does, however, rule out presenting
   broad nonquadratic parabolic-limit behavior as a new discovery.
   Hinkle's [*Parabolic limits of renormalization*](https://doi.org/10.1017/S0143385700000092),
   ETDS 20 (2000), 173-229, supplies additional classical context.

2. **The stronger quantitative candidate still lacks the required relevance.**
   The all-period archive construction uses an invariant-continuum
   criterion for its polynomial-like interpretation. It does not require
   normalized returns to converge to quadratic polynomials.
   The three older finite examples use Taylor estimates and Rouche
   margins, but do not assert a vanishing higher-jet error as p grows.
   Consequently a persistent fourth coefficient would exclude an
   approximation strategy not established as necessary for the missing
   canonical construction. It would not by itself construct or refute
   the proper paths, native marking, attachment electrode, or Wave width.

The precise unresolved work in the selected obligation remains the actual
marked ideal-boundary base and crest, complete proper-path restriction and
covering semantics, the attachment angular electrode, and conformal
width transfer. No relation of the jet candidate to these missing objects
was proved.

### Other routes screened before claiming the target

The archive audit rejected several easier alternatives:

- The finite clone spectrum is already outside the open hard core:
  [virtual core cocycle program, section 1.1](../../research/mlc_unified/virtual_core_cocycle_program.md).
  Further renewal or spectral algebra would miss physical core/WAD incidence.
- Raw inverse-trace hairpins, maximal-component pullback, and simple-parent
  trace classification are already addressed in the
  [immersion marking audit](../../research/independent_audits/immersion_mark_resolution_20261124/NOTE.md)
  and [native marking audit](../../research/independent_audits/native_mark_attack_20261124/NOTE.md).
- The [actual parent supremum convergence packet](../marked_wave_supremum_limit_20261127/NOTE.md)
  already handles complete parent families. Repeating generic supremum
  transport would not settle independent child optima or joint realization.
- For the [canonical q-gamma problem](../../research/independent_audits/canonical_wad_quadrilateral_moduli_20261116/NOTE.md),
  a support-size bound is not an effective deck-word cutoff. No actual
  uniformization or exhaustive ideal-lift estimate was obtained.

These screening observations are not submitted as mathematical progress.

## Dependencies

The selected ledger row is `NOV26_OPEN_SAT_WAVE`; its prerequisites are
`NOV26_SAT_V2` and `NOV26_NEAR_PARAB`.

The current work relies on the archive for the definition and established
properties of the family, but proves no additional Lean statement:

- [Existing near-parabolic family and its scope](../../research/native_wave_transfer/near_parabolic_tip_family.md).
- [Actual family theorem](../../formalization/weighted/ParabolicTipFamily.lean).
- [Two-flight shooting data](../../formalization/weighted/ParabolicTipShooting.lean).
- [Actual channel bounds](../../formalization/weighted/ParabolicTipRate.lean).
- [Complex physical component](../../formalization/weighted/ParabolicComplexComponent.lean).
- [Chosen one-slit contract](../../research/native_wave_transfer/SPECIFICATION_v1_1.md).
- [Separate satellite contract](../../research/native_wave_transfer/SPECIFICATION_v2_satellite.md).
- [Original finite examples](../../research/native_wave_transfer/RESULTS.md).

## Boundary

There is **no new Lean theorem and no CI-certified mathematical advance**.
No canonical Wave, attachment electrode, width-transfer theorem, uniform
jet bound, or counterexample to the ledger statement has been established.
No ledger status or existing proof, project registration, workflow,
validator, toolchain, or dependency pin has been changed.

The local workspace filesystem was full when cloning was attempted; the
clone failed, and no local Lean executable was available on PATH.
Small Python computations could still run. GitHub connector commits and
the existing CI remained available, so the filesystem problem is not
presented as the reason the mathematical route failed. It failed the
relevance requirement before a substantive Lean theorem was obtained.

The draft is closed rather than submitted as a restatement, survey,
formalization of known mathematics, or a purported new obstruction.
The branch preserves the initial claim and this rejected investigation.
The selected obligation remains open.

## Attribution

The physical family and prior proofs belong to the cited archive.
Classical parabolic-implosion results are attributed above. The present
proof search, experiment, prior-art check and relevance review were
AI-assisted by OpenAI ChatGPT, GPT-6 Astra Pro. No human mathematical
review has occurred, and no worldwide priority claim is made.

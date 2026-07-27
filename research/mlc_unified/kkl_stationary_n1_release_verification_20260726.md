# Gate N1 — release verification

## 0. Final verdict

```text
KKL_STATIONARY_RELATIVE_WAVE_CONTINUATION: proved
```

This verification covers Gate N1 only.  Gates N2--N4, the complete
native KKL stationary repair, VAAPC-I, UPTCR, MBTT, coercivity,
rigidity, parameter-fiber shrinking, and MLC remain open.

## 1. Authoritative hashes

| object | SHA-256 |
|---|---|
| machine ledger, `proof_obligations.json` | `1EBE1B13F605D8F4E8F35141D0295BAC0BED9ABF25F83C0870B6C41091CB270B` |
| final integration audit, `kkl_stationary_n1_integration_audit_20260726.md` | `CC6FA48283654801124E8A0D29DE120386FBB7B5DD37A59D2411D32594EF14B3` |
| frozen main N1 proof | `ADFC7BCD5A73CE7E7ABE12C11C3E2C4D778826B995BF9114C6F8B431EF38094F` |
| frozen BOWR proof | `6F9B4085C914BD74DD5030C67F311334A4B4882594E111FF552429E4FCC9D118` |
| frozen Borel width-envelope proof | `9F2ABD1E8DDD0E0E1B4FFC3B55B8DAF3BA64B4BCBE4E9562454A850E5E8422BE` |
| frozen BOWR backward audit | `F9A6BA1C1C9875CDCF1DE1506D3540DB21400FDCAC42B7EDCC3CAD9A574FF0F3` |
| frozen main backward audit | `0E44712DC835004B12A72D4856EEB1AB996ACE2D492E0FDD664523668F1A057E` |
| frozen DL A/B audit 1 | `841DF0993F7C731E772D3333CC758B1C5CDF69B1DD35D008BD66D7EBEE6FE697` |
| frozen DL A/B audit 2 | `4CD2DEE7BC16FEDF4385CA475B1CC67AE160396304FC2CB08DF3CECCABC69C2C` |
| built and released manuscript PDF | `E443B54BB9FAC5D964FB6830AC7C8C8F57DB842EAF6A7478CE8FFBC1923EE999` |

The build and release PDF copies are byte-identical.  The released
artifact is `output/pdf/marked_width_mlc_manuscript.pdf`.

## 2. Closed backward slice

Starting at

```text
KKL_STATIONARY_RELATIVE_WAVE_CONTINUATION
```

the complete machine dependency slice has exactly nine nodes:

| obligation | status |
|---|---|
| `KKL_STATIONARY_RELATIVE_WAVE_CONTINUATION` | proved |
| `KKL_STATIONARY_RELATIVE_WAVE_CONTINUATION_ANALYTIC` | proved |
| `STANDARD_BOREL_ORDERED_WAVE_REALIZATION` | proved |
| `BOREL_WIDTH_ENVELOPE_PRUNING` | proved |
| `DL_RELATIVE_DISCARD_FAMILY_BOUND` | proved |
| `N1_BOREL_RECTIFIABLE_CORE_REDUCTION` | proved |
| `DL_NATIVE_RECTIFIABLE_RELATIVE_DISCARD_BOUND` | imported |
| `N1_PREPRUNING_BOREL_WAVE_ATLAS` | proved |
| `KKL_STATIONARY_ONE_RETAINED_CHAIN` | proved |

The slice contains:

- no open obligation;
- no documentary-source record;
- no broad coefficient-one KKL Wave assertion;
- no optional uniform-packet theorem;
- no Gate-N2 or terminal-alignment assertion; and
- no global rigidity or MLC conclusion.

## 3. Source-semantic decision

The optional measurable-support/additivity derivation was not admitted
to the gating graph.  The frozen Feigen phrase “genuine subwave” does
not explicitly source-lock measurable retained support in the
separate DL2 sense.

The accepted route is:

1. use the pre-pruning Borel atlas to split the KKL packet into a
   rectifiable core and a zero-width nonrectifiable family;
2. invoke only the rectifiable sub-scope of the native DL Wave lemma;
3. bound the explicitly deleted \(T=O(\log m)\) nonzero deck-span
   packets and one bounded outer buffer by the Parallel Law;
4. regularize the complete bounded-width discard by one Borel metric
   envelope; and
5. continue by full source saturation and exact degree-two relative
   transfer.

Thus the proof does not subtract aggregate widths and does not assume
measurability of the native retained support.

## 4. Machine and manuscript validation

The following checks passed:

```text
python audit_proof.py
python audit_ledger_tooling_regressions.py
python audit_transfer_regressions.py
powershell -NoProfile -ExecutionPolicy Bypass -File latex/build.ps1
```

The proof ledger reports:

```text
437 obligations
31 imported
299 proved
107 open
target MLC open
```

All four ledger-tooling regressions and the complete transfer
regression suite passed.  The LaTeX/BibTeX build completed without
warnings, undefined citations, undefined references, overfull boxes,
or underfull boxes.

Extracted PDF text confirms:

```text
Proved Theorem 12.101
Borel leafwise-directed stationary continuation
KKL_STATIONARY_RELATIVE_WAVE_CONTINUATION proved
three distinct open gates
MLC is open
```

The PDF has 198 pages and 5,964,916 bytes.

Several immutable pre-integration snapshots still contain the literal
phrase “Gate N1 remains open pending integration/audit.”  These are:

```text
kkl_stationary_n1_borel_ordered_wave_realization_20260726.md
kkl_stationary_n1_actual_wave_provenance_audit_20260726.md
kkl_stationary_n1_borel_width_envelope_20260726.md
kkl_stationary_n1_borel_width_envelope_redteam_20260726.md
kkl_stationary_n1_bowr_independent_audit_20260726.md
```

Their hashes were intentionally preserved.  Their statements describe
their own pre-integration stopping points and are superseded for live
status by the final integration audit, this verification record, and
the machine ledger.  They are not current open-gate declarations.

## 5. Targeted layout verification

No bulk PDF image sweep was performed.  Only changed manuscript pages
113--115 were rendered and inspected.  The theorem statement, proof
synopsis, equations, three-gate status list, page transitions, and
following section heading have no clipping, overlap, broken glyph,
unreadable identifier, or margin overflow.

## 6. Final scope statement

Gate N1 is a completed local repair of the KKL stationary relative
telescope.  It is not the complete KKL stationary proof and is not a
proof of MLC.  The next logical gate is

```text
KKL_STATIONARY_POINTWISE_TWO_PATH_BREAK
```

but no work on that gate is included in this release.

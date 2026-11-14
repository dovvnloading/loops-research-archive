# One diffraction pattern, eight Mandelbrot roots

November 14, 2026 · Independent research draft

The period-27 airplane root angle in Matthew Robert Wesney’s archive gives a signed binary word with the most ambiguous possible one-dimensional diffraction pattern at its length. The proof extends to every length $3^k$. Its $2^k$ normalized words land at $2^k$ distinct parabolic roots when read as periodic parameter-ray angles. Exactly one of those roots is real.

The normalization fixes the support interval, the first sign and the reading direction. Intensity means the entire continuous-frequency squared Fourier magnitude of the signed word.

| Proof | Result |
|---|---|
| [Extremal binary phase retrieval](diffraction/airplane_phase_retrieval.md) | Unique maximum, all factor choices, exact autocorrelations, and a pair distinguished by one kneading mark per period. |
| [Geometry of the diffraction twins](study/geometry.md) | Distinct landing roots, first real-slice gap hit, minimal sparse kneading readout, phase slope and Hamming distance. [Eight exact period-27 records](study/period27_readout.json). |
| [Reconstructing the tip ray portrait](chords/README.md) | Exactly 19 configurations share the 63 distance lengths. Two multiplicities identify the true one up to rotation. A finite computation and a uniform carry argument classify every Mersenne scale from 6 onward. |
| [Observation length in the real Markov graph](markov/RESEARCH.md) | Seven left/right symbols can identify the inner recurrent component. Twenty-one always do. Includes an all-depth symbolic extension and a three-component weighted resonance. |

## Prior work and evidence

The finite period-27 volume count appears in Katz, Rahman and Ward’s Table 1. Their Theorem 1.1 describes the general reversal mechanism. Baake, Gähler and Grimm studied the underlying generalized Thue–Morse diffraction family. The draft supplies the upper bound and its equality classification at powers of three and the link between that classification and actual parabolic landing roots. The geometric interpretation imports periodic ray landing, tuning, Schleicher’s kneading condition and Zakeri’s real-slice criterion. The accompanying manuscripts identify these dependencies. The modulo-two approach to Littlewood polynomials also appears in work by Bary-Soroker, Hokken, Kozma and Poonen. [Phase retrieval](https://arxiv.org/html/2308.07467v3) · [Substitution spectra](https://arxiv.org/abs/1201.1423) · [Littlewood polynomial factorization](https://arxiv.org/abs/2308.04878)

Baseline commit [0a28eb1](https://github.com/dovvnloading/loops-research-archive/tree/0a28eb11b0a2636db5a766081b1455a346e3837c). The main studies use the established [period-27 center identification](https://github.com/dovvnloading/loops-research-archive/blob/0a28eb11b0a2636db5a766081b1455a346e3837c/research/independent_audits/period27_center_tuning_identification_20261106.md). The two companion studies respectively use the [nonattracting tip portrait](https://github.com/dovvnloading/loops-research-archive/blob/0a28eb11b0a2636db5a766081b1455a346e3837c/results/period27_tip_ray_portrait.json) and the [center’s real Markov graph](https://github.com/dovvnloading/loops-research-archive/blob/0a28eb11b0a2636db5a766081b1455a346e3837c/results/period27_symbolic_marking.json).

## Reproduce

Run from this directory, using Python 3.9 or later with assertions enabled. The four verification programs use the standard library and were run with CPython 3.12.14. They use integer and rational operations for their certificates. No randomness, numerical ray tracing or external network requests enter the checks.

```sh
python3 diffraction/verify_airplane_phase_retrieval.py
python3 study/verify_geometric_readout.py
python3 chords/verify.py --scales 64
python3 markov/verify_markov.py --depth 6
```

In a repository checkout, append `--manifest ../../../results/period27_tip_ray_portrait.json` to the third command and `--manifest ../../../results/period27_symbolic_marking.json` to the fourth to compare against the archive directly. The figure can be reproduced with `python3 study/plot_twins.py twins.png` using NumPy and Matplotlib.

The all-length conclusions rest on the written proofs. The Mersenne deletion classification combines an exhaustive finite bridge through 59 with an argument for all larger scales; the verifier also checks scales 60 through 64 directly. The higher Markov depths refer to the derived symbolic family. The scattering interpretation concerns a signed chain built from the bits. Historical publication priority remains unverified. The archive’s global MLC obligations are outside the claims of this draft.

ChatGPT performed the mathematical exploration, proof drafting, literature search, programming and independent computational checks. [AirplaneDiffraction.lean](../../../AirplaneDiffraction.lean) formalizes the factor-reversal identity over a commutative ring and checks the eight period-27 numerators and their full aperiodic correlations, three distinguishing kneading marks, the single-mark rabbit difference, the first-gap table, and the two gap counts among the nineteen deletion candidates. Run `lake build AirplaneDiffraction` at the repository root. The all-length extremal upper bound, general Mersenne classification, Markov proofs, and analytic ray-landing inputs are in the written arguments. No human peer review is recorded.

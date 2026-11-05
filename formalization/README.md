# Formal proof program (Lean 4)

Formalization is a **separate verification track** for the research archive. Kernel-checked code can establish the exact statement encoded in Lean, but cannot establish that the encoded statement accurately reflects the intended analytical theorem without a mathematical specification review.

## First certified target

The current `LoopsFormal.lean` implements the two-gate return operator whose matrix in the standard basis is
`[[0, 2], [1, 0]]`. It proves for **every natural exponent** that the image of each coordinate basis vector has a zero component, so no power has strictly positive entries. This verifies the imprimitive **reduced return matrix** obstruction used in the Appendix C audit.

This does **not yet** formalize (a) primitivity of the original five-vertex directed graph and each cloned graph, (b) the equality between this explicit operator and the general delayed-clone reduction, or (c) any Mandelbrot-local-connectivity claim. Those are separate formalization obligations. No unproved analytical hypothesis should be silently replaced by a definition.

## Staged roadmap

1. **Finite graph layer (active):** verify the two-state support obstruction; next formalize graph cycle lengths, strong connectivity, and primitivity of every delayed clone. Add the bridge from the weighted return paths to the explicit matrix action.
2. **Exact spectral layer (proposed):** introduce mathlib's finite matrices and prove the block elimination / Schur reduction `rho(H(lambda_n)) = lambda_n^n`, with typed row/column conventions and hypotheses. Formalize the positive-power counterexample separately.
3. **Quantitative Perron layer (proposed):** prove the two-sided eigenvalue bounds under finite nilpotent cross-section hypotheses. The second-order asymptotic requires analytic perturbation and extra formal machinery.
4. **Paper 1 (future):** formalize the abstract subgroup-reflection criterion for maps between covering spaces *before* attempting a quadratic dynamical realization. Verify the hypotheses about local path connectivity, lifting and source/target subgroups.
5. **Paper 3 (future):** isolate elementary finite planar attachment lemmas. General compacta Čech cohomology, prime ends, and inverse-limit arguments may need substantial library development.
6. **MLC gates (not currently formalizable):** the missing actual analytic carrier, calibration, coercivity, and rigidity theorems still require mathematical proofs; Lean does not invent those proofs.

## Reproduce

The repository root has a minimal `lean-toolchain` pin and `lakefile.toml`. Run:

```bash
lake build
```

GitHub Actions checks this on the research pull request. The script rejects placeholders and builds the Lean library. Only treat a file as **kernel-checked** if its build passes, with exact commit SHA and compiler version recorded.

## Review discipline

Maintain separate statuses: *informal argument*, *finite/numerical regression*, *Lean elaboration pending*, *Lean kernel checked*, *meaning/assumption audited*, and *independent specialist reviewed*. None of these automatically upgrades an existing open mathematical research obligation.

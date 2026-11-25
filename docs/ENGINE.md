# Fractal engine architecture and numerical limits

LOOPS has three separate computational boundaries: an interactive GPU engine, a higher-precision numerical worker, and the exact finite research data. Their precision and evidentiary meanings are different. None proves the Mandelbrot Local Connectivity conjecture.

## Interactive renderer

[`FractalViewport.tsx`](../src/components/FractalViewport.tsx) creates and disposes a framework-independent [`FractalEngine`](../src/engine/FractalEngine.ts). React sends scene changes through `setState`; the engine owns canvas sizing, input, the animation loop, shader programs and GPU resources. Navigation and selected parameters return through hooks. React does not own the per-frame rendering computation.

The custom shaders live in [`shaders.ts`](../src/engine/shaders.ts). There are no prerecorded fractal images or remote shader services.

| Scene | Computation | Interpretation |
| --- | --- | --- |
| Mandelbulb | Spherical power iteration with a derivative-based distance estimate, ray marching and orbit-trap shading | A three-dimensional fractal family; not the ordinary complex Mandelbrot set |
| Mandelbox | Box and sphere folds followed by a negative scale, with a distance estimate | A three-dimensional folding fractal; the visible coordinate is half the conventional fold coordinate |
| Quaternion Julia | Quaternion squaring plus a four-component constant, intersected by a movable three-dimensional slice | A slice of a quaternion Julia construction, separate from the complex quadratic family |
| Mandelbrot | Critical-orbit escape iteration for `z → z² + c` with high/low float pairs | Numerical parameter-plane exploration |
| Julia | Escape iteration for `z → z² + c` with a fixed selected complex parameter and high/low float pairs | Numerical dynamical-plane exploration |
| Escape landscape | A 192 × 192 cell mesh whose vertices compute an escape-derived height | A height-field visualization of numerical dynamics; not a physical third dimension of the Mandelbrot set |

Volume shading uses a numerical surface normal, ambient occlusion, short soft-shadow marches, orbit traps and tone mapping. The detail control adjusts the march budget and hit threshold. At finite iteration counts, boundaries and distance estimates are approximations. Floating-point implementation differences can alter fine details.

The quaternion constant is `(Re(c), Im(c), 0.18, 0)`; the slice control sets the fourth initial coordinate. The Mandelbox scale is the negative of its scale control, constrained to magnitude 1.2–3. These choices are implemented directly in the shaders and are not inferred from the repository's complex-dynamics certificates.

### Precision and performance

Volume and landscape shaders use float32 arithmetic. The complex-plane shader implements double-single addition and multiplication using two float32 components, with separately uploaded high and low coordinates. It is finite-precision exploration, not arbitrary precision or a rigorous enclosure.

The interactive complex-plane vertical span is deliberately clamped at `10^-7`; the landscape span is clamped at `10^-4`. Navigation coordinates remain JavaScript numbers. Moving beyond these floors belongs in the separate precision study rather than silently relabeling a collapsed image as deeper detail.

Quality controls cap pixel count and device-pixel ratio. Automatic quality reduces resolution when consecutive drawing frames are slow. Static scenes avoid unnecessary GPU draws. A hidden document pauses scheduling; resize and visibility events invalidate the frame. Context loss preserves scene state and attempts shader/resource reinitialization after browser restoration.

If WebGL2 cannot be created, a progressive float64 CPU Mandelbrot/Julia fallback is available. Its practical iteration budget is capped at 768 and its canvas width at approximately 400 pixels. Three-dimensional scenes still require WebGL2. A shader-compilation or context-recovery failure is surfaced to the interface.

PNG capture reads the actual canvas at its active rendering resolution. It is not an independent supersampled or validated recomputation.

## High-precision study

[`PrecisionStudy.tsx`](../src/components/PrecisionStudy.tsx) is an explicit-render laboratory, backed by [`precision.worker.ts`](../src/workers/precision.worker.ts) and the arithmetic in [`precision.ts`](../src/lib/precision.ts).

The worker follows this pipeline:

1. Validate bounded plain-decimal center strings, a zoom exponent from 0 to 60, image width 128/192/256, and an iteration budget 128/256/512/1024/2048.
2. Parse decimal coordinates as integer numerator/denominator pairs using `BigInt`. Coordinates never pass through JavaScript `Number`.
3. Select fractional precision `max(128, ceil((exponent + 20) × log2(10)))`. The supported zoom range therefore uses 128–266 fractional bits. The extra digits are a practical working margin, not a certified orbit-error bound.
4. Round the center, plane width `10^-exponent`, and pixel centers to a binary fixed-point grid. Pixels use equal spacing on both complex axes, with a 4:3 image aspect ratio.
5. Iterate `z → z² + c` with rounded BigInt fixed-point multiplication and an escape threshold of squared radius 4. Ties round away from zero. An exact repeat of the rounded machine state can skip the remaining finite computation; this is not an analytic periodicity proof.
6. Convert the escaped magnitude to floating point only for smooth display coloring. Non-escaped pixels remain dark. Transfer completed three-row pixel strips back to the visible 2D canvas.

The render begins only after the user presses **Render window**. Cancel and component unmount terminate the worker, including a computation currently inside a row. Main-thread controls remain usable. PNG export becomes available for a completed image and exports the computed pixels.

The initial seahorse window uses width `10^-5`, 256 iterations and 192 × 144 pixels. The deeper seahorse preset uses width `10^-7`, 2,048 iterations and 128 × 96 pixels. A narrow window around a truncated decimal center is exactly the window requested; increasing working precision cannot reconstruct digits that were not supplied. At high magnification, a short iteration budget can produce a uniform image without establishing membership in the set.

These are **rounded numerical calculations**, not interval arithmetic, arbitrary-precision reference-orbit perturbation, or validated escape enclosures. The interface reports arithmetic resolution rather than promising an equal number of correct digits after iteration.

## Exact research boundary

[`math.ts`](../src/lib/math.ts) uses BigInt rational arithmetic for angle normalization, doubling modulo one and binary expansions. Conversion to a drawing coordinate is explicitly numerical. [`prepare_data.py`](../scripts/prepare_data.py) preserves large certificate integers as decimal strings and adds source provenance without changing theorem status.

Straight chords in the atlas encode rational-angle pairings. They are not traced physical external rays. Finite puzzle trees retain their source depth and scope, and unresolved localization fields remain unresolved. The ledger separates original obligations from later updates and displays the original source status and hypotheses. A `proved` ledger entry is not automatically a Lean kernel-checked theorem.

See [DEPLOYMENT.md](DEPLOYMENT.md) for the data manifest, missing-source disclosures, build checks and archive preservation rules.

## Validation

The tests cover exact angle identities, the source ray-access collision, unchanged ledger fields, lossless dyadic brackets, exact decimal parsing before fixed-point rounding, distinct coordinates below float64 resolution, pixel orientation/aspect ratio, known critical orbits and bounded input rejection.

```sh
npm run build
npm test
python3 code/verify_site_integrity.py
```

Browser verification remains necessary for shader compilation, pointer and touch interactions, worker lifecycle, image export, layout and device-specific graphics behavior. The repository's Lean and research verifiers remain independent of the frontend tests.

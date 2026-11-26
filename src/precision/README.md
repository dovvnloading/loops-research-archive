# Exact exploration and numerical rendering

This directory implements the two-dimensional Mandelbrot and Julia explorer.
`ExactView` is the portable source of truth. Real and imaginary coordinates,
the Julia parameter, and the vertical span are decimal strings. Navigation,
journals, shared links, and exported parameters must preserve those strings.

## Supported range

- Vertical spans from `32` through `1e-200`.
- Integer iteration budgets from 64 through 20,000.
- Coordinates between −1,000,000 and 1,000,000; decimal inputs are bounded to
  1,200 characters to prevent unreasonable integer allocations.
- Every result is a finite numerical observation. A dark pixel means that the
  current calculation did not escape within its budget. It is not a certificate
  of set membership, a physical ray landing, or a theorem.

The exact decimal state and the rounded rendering arithmetic have different
roles. Storing a coordinate exactly does not make its rendered orbit exact.

## Rendering paths

At spans of `1e-8` and larger, final samples use JavaScript binary64 arithmetic.
On supported hardware, an OffscreenCanvas WebGL2 double-single shader provides
an earlier preview at shallow scales. The shader uses at most 2,048 iterations;
the following worker calculation uses the requested budget. Software GPU
renderers skip this extra preview. GPU availability is optional.

Below `1e-8`, a rounded BigInt fixed-point reference orbit uses at least 128
fractional bits and approximately 36 decimal guard digits beyond the span's
decimal order. Nearby Mandelbrot points use the perturbation recurrence

```
deltaZ[n+1] = 2 * referenceZ[n] * deltaZ[n] + deltaZ[n]^2 + deltaC
```

Reference values are converted to binary64 without overflowing intermediate
BigInts. Deltas remain binary64; the `1e-200` span limit leaves room for pixel
offsets before that representation underflows. Mandelbrot perturbations rebase
at the critical orbit when the reconstructed value is smaller than the delta.
Julia perturbations use the viewport center as their starting reference and do
not use that critical-point reset.

Severe cancellation (`|Z + delta|² < 1e-7 |Z|²`), nonfinite perturbations, or an
exhausted Julia reference trigger an independent rounded BigInt calculation for
the affected pixel. The repair count is exposed in render statistics. This
criterion is a practical numerical safeguard, not a rigorous error enclosure.
Very difficult Julia regions can require many repairs and render more slowly.

Relevant primary implementation and mathematical references:

- Claude Heiland-Allen, [Deep zoom theory and practice](https://mathr.co.uk/blog/2021-05-14_deep_zoom_theory_and_practice.html).
- Claude Heiland-Allen, [Deep Zoom](https://mathr.co.uk/web/deep-zoom.html), including
  the perturbation and critical-point rebasing recurrences.
- Claude Heiland-Allen, [Perturbation](https://mathr.co.uk/web/m-perturbation.html).

## Scheduling and presentation

Each viewport owns a worker. It renders a coarse image, an intermediate image,
and a full-resolution image in transferable tiles. Generation IDs reject stale
results; cooperative yields allow cancellation during long passes. Unmounting
terminates the worker, and hidden tabs cancel work. Repeated parent renders with
the same mathematical state do not restart the worker.

Pointer navigation reprojects the last image immediately while the new
numerical frame resolves. The reprojection uses the actual clamped scale, so the
depth limit and maximum span remain visually consistent. Pointer capture,
pinch, wheel, keyboard navigation, resizing, and tab visibility are handled by
`PrecisionViewport`.

Completed escape samples are cached separately from coloring. Changing a palette
or exposure recolors the samples without recomputing the orbits. Preview and
final paths share the same palette stops. A saved screenshot records the visible
image; an export render can compute a larger image from the same exact state.

## Validation

`tests/precision-deep.test.ts` checks:

- Exact scientific-notation parsing and separation of points that collapse to
  the same JavaScript number.
- Cursor anchor invariance, deep panning, orientation, and supported bounds.
- Known fixed, periodic, and escaping critical orbits.
- Perturbation samples against independently recomputed BigInt pixels with
  additional guard precision at 20, 60, and 200 decimal depths.
- Julia samples at 100 decimal depth and complex seahorse boundary samples.
- The exact `c = i` parameter at 120 decimal depth, whose critical orbit is
  `0 → i → −1+i → −i → −1+i` and remains resolvable without fabricated digits.
- Deterministic palette conversion without altering the underlying samples.

These are representative numerical checks, not a proof that every supported
pixel is correctly classified. Device performance depends on the location,
iteration budget, frame dimensions, and repair count.

# LOOPS · Fractal Research Engine

LOOPS replaces the previous document-style homepage with an interactive fractal engine and a research workspace. The underlying papers, Lean sources, certificates, verifier programs, and ledger remain part of the repository.

## Start exploring

The **Explore** workspace opens on a Mandelbulb calculated by the custom WebGL2 renderer. Choose a view from the index on the left, edit its parameters in the inspector on the right, and use the tools above the canvas to move through it. Each indexed view loads complete parameter and camera presets.

| Scene | What it represents | Useful controls |
| --- | --- | --- |
| Mandelbulb | A three-dimensional spherical power iteration | Power, iteration count, camera, orbit-trap coloring |
| Mandelbox | Repeated box and sphere folds | Fold scale, iterations, camera |
| Quaternion Julia | A three-dimensional slice of a four-dimensional quaternion iteration | Julia parameter, slice position, camera |
| Mandelbrot plane | Escape-time sampling of parameters for `z → z² + c`, starting at zero | Pan, zoom, iteration budget, select a parameter |
| Julia set | Escape-time sampling of starting points for a fixed complex parameter | Julia parameter, pan, zoom, iteration budget |
| Escape landscape | The complex parameter plane lifted into a numerical escape-time height field | Camera, parameter window, iterations |

The three-dimensional constructions are explicitly distinguished from the ordinary complex Mandelbrot set. The landscape is a height visualization of numerical escape time, not a new certified geometric model.

### Navigation and presentation

| Action | Control |
| --- | --- |
| Orbit a 3D scene / pan a complex plane | Drag |
| Zoom | Scroll, pinch, or `+` / `−` |
| Move the camera / pan by keyboard | Arrow keys |
| Select a complex parameter and open linked Julia comparison | Shift-click the Mandelbrot plane |
| Play or pause scene animation | Space, or the play button |
| Reset the current scene | `R` |
| Toggle focus mode | `H` |
| Fullscreen | `F` |
| Open command palette | Ctrl/Cmd + `K` |
| Open help | `?` |

Scene shortcuts apply to Explore. Form controls retain ordinary keyboard behavior. Research views provide buttons, selects, sliders, and number fields as alternatives to clicking a diagram. Animation begins paused; the interface respects reduced-motion preferences.

**Saved views** are stored in the current browser. Use session export to move a configuration elsewhere. Share links encode the scene state; PNG export saves the rendered viewport. Sessions and images are local exports, not research certificates.

The renderer has automatic, high, balanced, and low quality choices. Automatic quality adjusts render resolution to the available device. Rendering stops when the page is hidden; graphics-context interruption preserves the scene for restoration. Where WebGL2 cannot be initialized, the engine offers a CPU complex-plane fallback and the research workspaces remain available.

## Dynamics: inspect an actual orbit

**Dynamics** connects three views of the quadratic recurrence:

1. A small Mandelbrot parameter map lets you select `c` by position, or enter its real and imaginary components directly.
2. A worker computes a numerical Julia preview for that parameter.
3. The critical orbit starts at zero and appears over the same coordinate system. Step through it, animate it, or select a specific iteration with the slider.

The inspector includes Basilica, dendrite, rabbit, spiral, airplane, and period-27 presets. Several center coordinates are rounded display approximations. The period-27 center's exact rational bracket is available in the Atlas.

The orbit export contains the parameter, iteration limit, calculated points, and a floating-point precision label. The reported “bounded through N” state means only that the orbit did not cross the selected escape bound in those `N` calculations.

## Atlas: interact with the source certificates

The Atlas reads generated data from the original research JSON files. Exact integers beyond JavaScript's safe integer range are preserved as decimal strings, and angle doubling uses `BigInt` rational arithmetic. Conversion to floating point is limited to drawing coordinates.

### Angle portraits

Choose the period-3, period-9, or period-27 tuning scale. The diagram shows the forward angle-pair orbit under doubling, with the active pair highlighted. The inspector preserves the kneading sequence, binary words, internal address, physical return time, coefficient sign, and center bracket from [`period27_symbolic_marking.json`](../results/period27_symbolic_marking.json).

The separate tip portrait shows the nine recorded phase pairs. Its inspector includes the exact dyadic tip bracket and the two source access angles that acquire the same rational image after six doublings. The center and the nearby Misiurewicz tip are different parameters.

The circle's straight chords are combinatorial connections between angles. They are not traced physical external rays. The source's distinction between exact arithmetic, imported ray-landing results, and conditional geometric claims remains visible.

### Puzzle tree

Select a depth from zero through six and choose a recorded ray pair. The inspector shows its inverse-branch word, image pair, first appearance, landing-target label, and membership in the recorded critical-piece boundary. “Follow image pair” moves one level toward the seed. Each level can be exported as JSON.

The source leaves the `O(ξ, η)` localization unassigned. The app displays that fact instead of creating geometric coordinates for it. Analytic dependencies are listed below the diagram.

### Markov spine

The matrix displays the 26-edge real interval adjacency relation from the source certificate. Rows are sources and columns are destinations. Select a source edge and follow an allowed destination to build a graph walk. Component membership, cycle lengths, and the characteristic factorization come from the original data.

This is the real interval Markov spine. It does not establish a native KKL or clone-graph identification; the source's written-versus-formalized verification boundary is retained.

### Renewal clock

Choose a recorded delay to inspect its Perron root, relative gap, correlation time, and scaled-gap diagnostic. The plot joins the recorded numerical values on logarithmic axes. The UI separately checks whether that particular delay also appears in the source's finite exact regression list.

The high-digit numerical diagnostics are not certified enclosures. Finite quotient-ring regressions do not become an all-delay theorem by interpolation.

## Lab: precision and parameter experiments

### Precision study

The precision study uses a dedicated worker and rounded binary fixed-point arithmetic backed by `BigInt`. Real and imaginary centers are accepted as decimal strings, parsed as exact decimal rationals, and then rounded to the selected arithmetic grid. They do not pass through a JavaScript `Number` first.

Choose a window width from `10⁰` to `10⁻⁶⁰`, an iteration budget, and a small image size, then explicitly start the render. Progress arrives in strips, and the worker can be cancelled. A completed image can be exported as PNG.

This is a slower exploratory renderer, not interval arithmetic. Each operation is rounded. Increasing arithmetic precision cannot recover center digits that were never supplied, and an inadequate iteration budget may produce a uniform image. A dark pixel means non-escape within the chosen budget, not a membership certificate.

### Real-slice dynamics

For each real parameter `c`, the orbit diagram discards 384 iterations and plots the next 128. Choose the full real slice, the period-doubling region, or the airplane window. Clicking a column or editing the parameter selects a separate 1,024-iteration orbit for inspection.

The displayed period candidate compares the last 64 orbit values with a `10⁻⁷` tolerance, testing periods through 32. It is a numerical diagnostic; near neutral or repelling cycles, transients and rounding may dominate it. The chosen sample can be exported, or opened as a Julia set in Explore.

### Methods and scope

The final Lab tab explains the distinct roles of a numerical image, an exact finite certificate, a kernel-checked theorem, and an unresolved analytic bridge. These distinctions apply throughout the app.

## Archive: preserve the evidence trail

The proof ledger exposes all 465 baseline obligations and all 46 later research updates. Baseline counts remain separate from updates. Search identifiers, statements, dependencies, hypotheses, classifications, and research groups; filter by source status or later updates.

Each record shows its original status, statement, hypotheses, evidence path, classification where supplied, and recorded dependencies. Selecting an input or dependent opens that record. Source links resolve to the pinned research revision. A source label of `proved` does not automatically mean Lean kernel-checked, and conditional results keep their hypotheses.

The source revision contains 26 ledger entries whose evidence points to seven Markdown files that are absent in that revision. Those entries display **Source file unavailable in this revision** and offer repository search. The app does not manufacture a working source link or erase the record.

The source library indexes 1,085 research files, including papers, documents, JSON certificates, Python verifiers, Lean formalizations, and figures. Search or filter the index, then open the pinned GitHub source or the preserved local file. These counts describe the bundled source snapshot and may change when the data pipeline is regenerated from a later revision.

**MLC remains open.** The application is a research instrument and evidence browser, not a claimed resolution of the conjecture.

## Maintenance

For the build, data generation, integrity checks, and hosting workflow, see [deployment documentation](DEPLOYMENT.md). The research views are in [`src/research`](../src/research), the GPU renderer in [`src/engine`](../src/engine), and shared exact arithmetic in [`src/lib/math.ts`](../src/lib/math.ts).

The generated data manifest records the source revision, source and output hashes, integer encoding, dataset scopes, and unresolved evidence. The UI consumes those generated files and links back to their original sources.

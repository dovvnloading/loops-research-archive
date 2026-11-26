# LOOPS Observatory — user and maintainer handoff

This document describes the version 2 application: five connected workspaces for exploring fractals, running numerical experiments, preserving observations, and reading the underlying research. The application is a React and TypeScript client built with Vite. Rendering, experiments, and journal storage run in the browser.

The distinction that matters throughout the application is **an exact description of a view versus a numerical image of that view**. Decimal coordinates can be saved without losing digits. A rendered pixel still comes from finite, rounded arithmetic and a finite iteration budget. Research claims retain the scope of their original sources.

## 1. The five workspaces

| Workspace      | Implemented workflow                                                                                                                                                                                                   | Where to start                                                                                                 |
| -------------- | ---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | -------------------------------------------------------------------------------------------------------------- |
| **Explore**    | Live Mandelbulb, Mandelbox, quaternion Julia, Mandelbrot, Julia, and escape-landscape views; navigation; model, material, and camera controls; linked Julia view; undo/redo; guided journeys; image and session export | Drag the initial Mandelbulb, then choose a world from the library or a destination below the canvas.           |
| **Atlas**      | Curated mathematical destinations and self-paced journeys; the mathematical atlas exposes exact angle portraits, finite puzzle pullbacks, Markov data, and renewal experiments                                         | Open **Places & journeys** for visual starting points or **Mathematical atlas** for source-linked instruments. |
| **Laboratory** | Parameter expeditions, a critical-orbit microscope, and comparisons of two sampled windows; cancellable workers; manifests; saved results and replay                                                                   | Start with a modest survey, inspect a candidate, and save the experiment to the journal.                       |
| **Journal**    | Saved views, thumbnails, titles, notes, tags, search, branches, side-by-side comparisons, JSON import/export, CSV export, delete with undo                                                                             | Save a view from Explore, add a question in the notes, then branch from that observation.                      |
| **Research**   | Research overview and outstanding gates; obligation ledger and source catalog; dynamics workbench; precision studies                                                                                                   | Read a claim's source and hypotheses before interpreting its status.                                           |

The **Field guide** is a curated explanation with source links and suggested next steps. The command palette searches destinations, application actions, and the source catalog. These are implemented navigation and explanation tools; they do not depend on an external model service.

### A useful first session

1. Open **Eightfold**, change one model or lighting setting, and save the view with a note about the change.
2. Open **The whole map**. Shift-click a point to select a parameter for the linked Julia view. Examine that parameter in the Laboratory's orbit microscope.
3. Save the experiment, open the Journal, and reopen it. Its recorded settings and results are available for inspection; rerun its instrument to obtain a fresh numerical calculation.
4. Export the journal JSON. It is the portable backup of observations, notes, thumbnails, exact view settings, and attached experiment records.

## 2. Coordinates, precision, and mathematical interpretation

### Complex-plane exploration

`ExactView` stores the real and imaginary center, vertical span, and Julia parameter as decimal strings. It also records the family, palette, and iteration budget. The coordinate implementation validates those strings and performs navigation with BigInt fixed-point arithmetic. Journal serialization preserves their decimal spelling, including scientific notation. See [`src/precision/types.ts`](../src/precision/types.ts), [`coordinates.ts`](../src/precision/coordinates.ts), and [`src/journal/codec.ts`](../src/journal/codec.ts).

The supported **vertical span is `32` down to `1e-200`**. The plane explorer accepts **64–20,000 iterations**. The coordinate parser bounds input length and exponent range, and rejects invalid or unsupported values. These are software limits for the 2D explorer, not claims about arbitrary precision in the 3D renderer.

At ordinary scales, final samples use a binary64 worker. At spans below `1e-8`, the renderer builds a BigInt reference orbit, evaluates nearby pixels using perturbation, and uses direct rounded BigInt recurrence for pixels that trigger its numerical repair criteria. Mandelbrot perturbation also rebases its reference index when needed. The worker renders progressively and cancels obsolete generations when the view changes. Palette-only changes can reuse cached samples. The relevant implementations are [`kernel.ts`](../src/precision/kernel.ts) and [`renderer.worker.ts`](../src/precision/renderer.worker.ts).

An optional worker-side WebGL2 preview uses `OffscreenCanvas` and double-single arithmetic at suitable ordinary scales. It is skipped when unavailable or when the detected renderer is software. Final samples are recomputed by the binary64/BigInt path. A fast preview and its settled result can differ. See [`gpu-preview.ts`](../src/precision/gpu-preview.ts).

**A dark pixel means no escape was observed within the current numerical budget.** Rounded periodicity detection, perturbation repair, an estimated attracting period, or a repeated-looking picture does not establish a general membership or equivalence theorem. Increasing precision and iterations is useful evidence checking; it does not turn a rendered image into an interval certificate.

### A concrete deep-zoom starting point

**The imaginary gateway** is an actual preset, not an image asset standing in for a live render:

```json
{
  "family": "mandelbrot",
  "center": { "re": "0", "im": "1" },
  "span": "1e-120",
  "iterations": 2048,
  "palette": "aurora"
}
```

Its center is the exactly specified parameter `c = i`. The critical orbit begins

```text
0 → i → −1 + i → −i → −1 + i → …
```

The span is `10^-120`; this does not require a long approximate decimal expansion of the center. The preset and an independent higher-precision pixel comparison are recorded in [`destinations.ts`](../src/studio/destinations.ts) and [`precision-deep.test.ts`](../tests/precision-deep.test.ts). Those regression samples check the implementation at selected points. They are not a performance or error-bound guarantee for every parameter window at that depth.

### Three-dimensional rendering

Mandelbulb, Mandelbox, and quaternion Julia surfaces use custom WebGL2 ray marching. The quaternion scene is a three-dimensional slice through a four-dimensional iteration. The escape landscape is a display of finite escape-time values as height. These families have separate mathematical meanings and numerical implementations.

Volume precision can be automatic, GPU, or binary64 refinement. The existing Float64 worker provides a slower refinement path near small numerical clearances and a volume fallback when WebGL2 is unavailable. Navigation slows near estimated surfaces. Distance estimates and collision avoidance are numerical heuristics. They do not certify safe distances or support the plane explorer's `1e-200` scale range. Rendering reports its active method and refinement state. See [`FractalEngine.ts`](../src/engine/FractalEngine.ts), [`navigation.ts`](../src/engine/navigation.ts), [`DeepRenderer.ts`](../src/engine/DeepRenderer.ts), and [`volume64.ts`](../src/engine/volume64.ts).

Frame rate and completion time depend on the device, image size, scene, precision, and iteration count. Adaptive and low-power settings reduce work. Hidden or inactive views suspend rendering, and generation checks prevent stale worker results from replacing a newer view. A browser that cannot provide the required drawing or worker facilities receives an explicit error or supported fallback; the research documents remain independently accessible.

## 3. Laboratory observations and replay

The Laboratory has three instruments:

- **Expeditions** sample a rectangular parameter region, classify finite observations, and refine candidate periodic centers. Progress, sample counts, pause/resume, cancellation, and candidate inspection are available. Candidates are numerical findings, not certified new mathematical discoveries.
- **Orbit microscope** follows the critical orbit from `z₀ = 0`, shows numerical return information, and estimates an attracting period and multiplier when the instrument's criteria are met.
- **Compare structures** samples two windows under shared settings and can consider discrete alignments. Its similarity measurements describe the sampled numerical fields, not a proof that two dynamical systems are equivalent.

These instruments use **IEEE-754 binary64**. Their declared budgets and precision are included in `loops-laboratory-v1` manifests. In particular, the comparison instrument rejects pixel spacing beyond its binary64 precision allowance rather than silently claiming the 2D explorer's deep-zoom capabilities. See [`src/laboratory/math.ts`](../src/laboratory/math.ts).

Use **Export experiment** for a portable manifest or **Save experiment** for an attached Journal record. Importing a manifest validates its settings and stored result structure. Reopening a Journal experiment selects its instrument and restores the recorded material. Rerunning produces a new calculation. Comparison scores are recalculated from imported sample arrays instead of trusting a supplied score. Survey previews preserve their recorded sample pixels. These paths are implemented in [`replay.ts`](../src/laboratory/replay.ts).

## 4. Journal, storage, and portability

The Journal prefers IndexedDB. It falls back to local storage when possible, or to temporary in-memory storage when browser storage cannot be used. The interface identifies the active mode and reports save failures. Mutations are serialized; an unsuccessful write leaves previously saved observations intact. Browser storage is specific to the current origin and browser profile. Clearing browser data, private browsing behavior, or storage eviction can remove it.

**Export JSON regularly for a durable, portable backup.** There is no cross-device account synchronization in this client. Moving an exported journal to another device and importing it is the implemented transfer workflow.

| Export or record                           | Contents and intended use                                                                                                                      |
| ------------------------------------------ | ---------------------------------------------------------------------------------------------------------------------------------------------- |
| Journal JSON, `loops-journal`, version 2   | Observations, exact settings, notes, tags, thumbnails, parent relationships, and attached experiments. Use for backup and migration.           |
| Session JSON, `loops-session`, version 2   | One engine state, one exact plane view, and available research provenance. Import through the session action in the navigation/help interface. |
| View link, version 2                       | Encoded mathematical view settings. Journal notes and experiment data are excluded. Access still depends on the site's audience.               |
| Laboratory manifest, `loops-laboratory-v1` | Instrument settings, method, precision declaration, and available recorded results. Import in Laboratory.                                      |
| Motion JSON, `loops-motion`, version 1     | A same-family sequence of 3D keyframes and timing settings. Import in Motion Studio.                                                           |
| Journal or candidate CSV                   | Tabular inspection in other tools. Spreadsheet software may infer numeric types; use JSON for lossless application replay.                     |

Journal imports validate versions, exact coordinate strings, finite data, thumbnails, and branch relationships. Identical records are skipped. Conflicting identifiers are remapped together with affected descendants, preserving existing records. Cyclic branch histories are rejected. Current limits include 1,000 observations and 24 MB per journal import, 2 MB per bitmap thumbnail, and 4 MB per attached experiment. PNG, JPEG, and WebP data thumbnails are supported. Legacy bookmarks and version 1 view/session data have migration paths. See [`codec.ts`](../src/journal/codec.ts), [`store.ts`](../src/journal/store.ts), and [`src/lib/session.ts`](../src/lib/session.ts).

## 5. Images and motion

### PNG export

Image export supports the current viewport or a separate worker render with a longest edge of **1,200, 1,920, or 3,840 pixels**. The actual main viewport supplies the aspect ratio. A worker render can be cancelled. Closing the export dialog cancels its generation. The **escape landscape exports its current rendered viewport** rather than using the volume export kernel.

Plane worker exports use the precision kernel. Volume worker exports use the binary64 ray marcher, so their numerical shading can differ from the interactive GPU preview. A larger image increases sampling density; it does not certify the result or automatically increase every mathematical budget.

PNG files contain an uncompressed UTF-8 **`iTXt` chunk with keyword `LOOPS`**. Its JSON records the image format version, creation time, dimensions, finite-arithmetic statement, engine settings, exact view, and available research source revision. The writer preserves the existing image chunks and computes the inserted chunk's CRC. The application currently restores sessions and journals from JSON; PNG metadata is a portable provenance record, not an implemented PNG-import workflow. See [`ExportDialog.tsx`](../src/studio/ExportDialog.tsx), [`export.worker.ts`](../src/studio/export.worker.ts), [`png.ts`](../src/studio/png.ts), and [`png.test.ts`](../tests/png.test.ts).

### Motion Studio

Open Motion Studio from the volume inspector's **View** section. It supports Mandelbulb, Mandelbox, and quaternion Julia scenes. The preview mirrors the real render canvas. Compose a camera and appearance, capture a keyframe, adjust the view, and capture another. Rename, reorder, replace, or delete keyframes as needed.

Paths support up to **eight same-family keyframes** and **2–90 seconds** of duration. Playback includes scrub, pause, stop, linear or eased interpolation, and an optional closing segment for loops. Orbit angles use the short angular route; flight positions interpolate in world coordinates. Interpolated paths can pass through surfaces. Palette changes occur at keyframes.

Motion uses GPU rendering and pauses the explorer's autorotation while composing. Stop or close restores the original exploration state. Paths persist locally by family and can be exported as JSON.

When the browser supports canvas capture and an appropriate `MediaRecorder` WebM type, **Record WebM** records the actual canvas at a requested 24 fps and downloads the result. Render performance can limit the effective visual frame rate. One complete loop is exported when recording a looping path. Finishing early downloads the recorded clip; closing the studio cancels an unfinished recording. Hidden-tab playback/recording pauses. Unsupported browsers show the recording limitation and retain JSON path export. See [`MotionStudio.tsx`](../src/studio/MotionStudio.tsx).

## 6. Gestures and keyboard controls

Shortcuts apply in their relevant workspace and yield to text editing and dialogs. Buttons and inspector fields provide alternatives to canvas gestures.

| Action                                          | Control                                                                                 |
| ----------------------------------------------- | --------------------------------------------------------------------------------------- |
| Pan a plane / orbit a volume                    | Drag the canvas                                                                         |
| Zoom around the pointer                         | Wheel or pinch                                                                          |
| Zoom a focused plane canvas                     | `+` / `−`; double-click also zooms toward a point                                       |
| Pan a focused plane canvas                      | Arrow keys; Shift reduces the step                                                      |
| Reset the focused plane's center/span           | `Home`                                                                                  |
| Choose coordinates for a linked Julia parameter | Shift-click in the main plane; in a Julia view this uses the clicked point as a new `c` |
| Fly through a volume                            | `W A S D`; `Q` down, `E` up                                                             |
| Rotate a focused volume camera                  | Arrow keys                                                                              |
| Start/pause volume orbit animation              | Space or the animation control                                                          |
| Focus mode                                      | `F`                                                                                     |
| Reset the current destination                   | `R`                                                                                     |
| Save an observation                             | `B` or Ctrl/Cmd + `S`                                                                   |
| Linked Julia view                               | `L`                                                                                     |
| Field guide                                     | `G`                                                                                     |
| Commands and source search                      | Ctrl/Cmd + `K`                                                                          |
| Undo / redo a view change                       | Ctrl/Cmd + `Z` / Ctrl/Cmd + Shift + `Z`                                                 |
| Help                                            | `?`                                                                                     |
| Close a dialog / leave focus or close panels    | `Escape`, according to context                                                          |

Motion playback is user initiated. Interface animation respects reduced-motion preferences. The skip link focuses the current workspace without changing its route.

## 7. Architecture map

| Module                                                                                                                                       | Responsibility                                                                                                                        |
| -------------------------------------------------------------------------------------------------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------- |
| [`src/App.tsx`](../src/App.tsx)                                                                                                              | Workspace routing, current engine/exact state, linked views, session import, journal integration, dialogs, and global shortcuts       |
| [`src/studio/`](../src/studio/)                                                                                                              | Application shell, inspector, destinations, journeys, field guide, command palette, history, export, and motion                       |
| [`src/precision/`](../src/precision/)                                                                                                        | Decimal coordinates, BigInt reference/repair kernel, optional GPU preview, progressive worker rendering, and plane canvas interaction |
| [`src/engine/`](../src/engine/)                                                                                                              | Custom WebGL2 rendering, numerical navigation, Float64 volume refinement, and render lifecycle                                        |
| [`src/laboratory/`](../src/laboratory/)                                                                                                      | Numerical instruments, worker jobs, validation, manifests, and replay                                                                 |
| [`src/journal/`](../src/journal/)                                                                                                            | Versioned snapshot codecs, storage, branching, import/export, and Journal UI                                                          |
| [`src/research/`](../src/research/)                                                                                                          | Source-driven overview, obligation archive, mathematical atlas, dynamics, and precision studies                                       |
| [`scripts/prepare_data.py`](../scripts/prepare_data.py)                                                                                      | Lossless browser datasets, source hashes, scope labels, evidence resolution, and catalog generation                                   |
| [`scripts/copy_archive.py`](../scripts/copy_archive.py)                                                                                      | Copies the research archive into the built site                                                                                       |
| [`scripts/render-exhibits.mjs`](../scripts/render-exhibits.mjs), [`render-precision-exhibits.mjs`](../scripts/render-precision-exhibits.mjs) | Computed destination artwork; live exploration still renders the underlying model                                                     |
| [`tests/`](../tests/)                                                                                                                        | Arithmetic, navigation, lifecycle, sessions, laboratory replay, journal persistence, motion, and PNG regression coverage              |

React manages interface and application state. The numerical kernels are independent modules shared by workers and tests. Rendering jobs use generation identifiers or worker termination to cancel obsolete work. The deployment artifact is static; local experiments do not require a rendering server.

## 8. Development and verification

Use **Node.js 24** and **Python 3.12**, matching the application CI configuration. From the repository root:

```bash
npm ci
npm run dev
```

`predev` generates browser research data. The production checks are:

```bash
npm run build
npm test
python3 code/verify_site_integrity.py
npm run format:check
```

`npm run check` combines the build, tests, and site-integrity verifier. The build runs data preparation, TypeScript checking, Vite packaging, and archive copying. Generated `public/data/` and `dist/` are not the authoritative research sources.

For a suitable local or CI environment with Chrome/Chromium installed:

```bash
npm run build
npm run test:browser
```

The browser smoke script starts the built-site preview on port 4173 and Chrome's debugging endpoint on port 9222. `CHROME_BIN` can select the executable; `SMOKE_SCREENSHOTS=1` enables success screenshots; `SMOKE_OUTPUT` selects its output directory. It uses software WebGL for reproducible CI checks. This does not characterize real-device GPU performance. See [`scripts/smoke_webgl.mjs`](../scripts/smoke_webgl.mjs) and [the site-health workflow](../.github/workflows/site-health.yml).

### Release verification status

**The application is deployed, and the GitHub browser-rendering and validation workflows passed.** Open the published application at [LOOPS Observatory](https://loops-fractal-research.lagging.chatgpt.site), subject to the site's existing access policy. The implementation is available for review in [pull request #126](https://github.com/dovvnloading/loops-research-archive/pull/126).

The verified GitHub review baseline is commit [`9f482ea4f3315c2c04c0b8e156086b16a65ec366`](https://github.com/dovvnloading/loops-research-archive/commit/9f482ea4f3315c2c04c0b8e156086b16a65ec366). This verification record does not imply that the pull request has been merged.

| Verification | Recorded result | Evidence |
| --- | --- | --- |
| Local application checks | Production build, TypeScript, archive integrity, and 75 automated tests passed | Repository test and build commands above; individual cases in `tests/` |
| Site health | Build/integrity checks and the actual browser-rendering job completed successfully | [Run 45732608646](https://github.com/dovvnloading/loops-research-archive/actions/runs/45732608646) |
| Coverage workflow | Completed successfully | [Run 45732608663](https://github.com/dovvnloading/loops-research-archive/actions/runs/45732608663) |
| Research validation | Completed successfully | [Run 45732608724](https://github.com/dovvnloading/loops-research-archive/actions/runs/45732608724) |
| Published application | Sites publication succeeded; a platform-generated screenshot of the deployed Explore page was reviewed | [Published application](https://loops-fractal-research.lagging.chatgpt.site) |

The browser job exercised real application rendering in headless Chrome with software WebGL. It checked WebGL2 fractal pixels, gamma and projection changes, snapshot fidelity, wheel-driven flight, the Mandelbox/quaternion/landscape shaders, Float64 plane rendering, intentional Shift-click Julia linking, exact navigation below binary64 coordinate resolution, workspace lifecycle, portrait projection, Float64 volume refinement, missing-GPU fallback, worker-startup error recovery, and absence of uncaught exceptions. Its machine-readable result and failure diagnostics are produced by [`scripts/smoke_webgl.mjs`](../scripts/smoke_webgl.mjs).

The 120-decimal-scale imaginary-gateway regression is part of the automated numerical tests. The browser smoke test separately exercised deep rendering and navigation below a `1e-60` span. Neither result is a hardware frame-rate benchmark or an exhaustive check of every deep parameter window.

**Target-device and assistive-technology acceptance remains a separate check.** The managed local preview service was unavailable, and direct live-browser review requires the site's authorized sign-in context. CI browser verification completed independently. The browser workflow saves representative desktop/mobile screenshots of the workspaces and export/motion dialogs in its `fractal-browser-rendering` artifact. These support visual review alongside the deployed Explore screenshot; they do not establish hardware frame-rate, touch, screen-reader, or cross-browser acceptance. Keep the following checklist open until those specific checks have been performed and their browser/hardware details recorded.

Remaining representative acceptance checklist:

- [ ] Each family and its model, lighting, and camera controls have been reviewed interactively on the intended hardware and browser matrix.
- [ ] Desktop, touch, keyboard, focus mode, dialogs, and narrow-screen linked views remain usable without losing access to navigation.
- [ ] Linked-view selection, exact parameter labels, and plane navigation have been reviewed visually across desktop and touch layouts.
- [ ] **The imaginary gateway** has been reviewed interactively at `1e-120`, including budget changes, cancellation, and view restoration on representative devices.
- [ ] Hardware WebGL2 and graphics-context loss/recovery have been checked on target devices in addition to the passing CI software-WebGL and missing-GPU cases.
- [ ] A journal observation survives reload; JSON round trips preserve exact coordinates, notes, thumbnails, and branch relationships; blocked/full storage reports the failure.
- [ ] An exported expedition/orbit/comparison reopens in the correct instrument and reruns from its saved settings; cancellation and import validation work.
- [ ] PNG exports have the requested dimensions, parseable `LOOPS` metadata, and unchanged image data; cancelling or closing an export does not produce a later download.
- [ ] Motion playback, scrubbing, looping, early-stop clips, hidden-tab pause, WebM download, and resource cleanup work in each supported target browser.
- [ ] Source links resolve at the pinned revision or to their packaged document; unavailable evidence remains explicitly unavailable.
- [ ] Reduced-motion behavior, focus visibility, command-palette announcements, text contrast, and screen-reader navigation have been reviewed interactively.

## 9. Research provenance and deployment

The research and the application have related but distinct source histories. The current public research baseline is pinned in [`.openai/research-source.json`](../.openai/research-source.json):

```json
{
  "repository": "https://github.com/dovvnloading/loops-research-archive",
  "commit": "073634f4d1727cc1b5261a439c0e08d80b9092c8"
}
```

`prepare_data.py` uses this pin when the commit exists in the local Git history and the relevant research inputs remain unchanged. It preserves integers outside JavaScript's safe range as decimal strings, records SHA-256 hashes and dataset scope, and retains unresolved evidence explicitly. A ledger status of `proved` is not automatically a Lean kernel-checked result. The Mandelbrot local connectivity conjecture remains open.

Catalog links point to the immutable upstream revision only when the packaged file's blob matches that revision. New or changed application documents are linked to their packaged paths. When research itself changes, publish the corresponding research revision and update/verify the pin; do not substitute an application-only Sites commit into GitHub source links.

The existing Sites project is identified by [`.openai/hosting.json`](../.openai/hosting.json), with static output in `dist`. Preserve its opaque `project_id` and existing audience. A release should pair a pushed application commit with the artifact built from that source state, save a version, deploy that saved version, and verify its terminal deployment status. Record the resulting application commit and deployment/version identifiers separately from the pinned research revision.

Data and archive preparation enumerate tracked files. **Stage newly added source/document files before the final release build** so the generated catalog and copied archive include them. Then rebuild, verify, and package the complete `dist` directory, including `index.html`, assets, workers, generated data, exhibits, and research documents.

The repository also retains a GitHub Pages workflow. Its success and a Sites deployment are separate publication events. The Sites application linked in the verification record above has been published successfully. Preserve the recorded distinction between that publication, the passing GitHub checks, and the review/merge state of pull request #126 when reporting this release.

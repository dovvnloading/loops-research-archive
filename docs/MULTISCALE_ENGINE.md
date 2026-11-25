# Multiscale fractal flight

The Mandelbulb, Mandelbox, and quaternion Julia scenes raymarch a numerical iterative distance field on a full-screen triangle. There is no surface mesh in those modes. The separate escape landscape is a deliberately sampled height field.

- Scroll toward a point in the viewport to move the actual camera along its viewing ray, entering flight mode. Drag to look, WASD to translate, Q/E to descend/ascend. The inspector offers equivalent buttons and return to orbit; R resets the view.
- Flight speed scales with a CPU evaluation of the same iterative distance field. Movement is subdivided and conservatively stopped near the numerical surface. Distance estimates are heuristic, not guaranteed collision distances.
- The requested iteration count is a minimum, with additional iterations as estimated clearance decreases, capped at 64 (bulb and quaternion) or 40 (box). The inspector reports the active budget and estimated clearance.
- The ray hit threshold scales with ray travel and pixel footprint, down to a Float32 coordinate floor; normals, occlusion and lighting adapt to the resolved scale. During interaction a reduced-resolution preview is rendered; after input stops intermediate and full quality passes recover spatial detail.
- Camera position is optional in the existing version-one share/session format; old saved orbit views still load.
- This is finite-precision exploration, not infinite zoom, interval arithmetic, or a proof of any dynamical claim. GPU Float32 geometry and numerical distance estimators eventually limit detail. The existing high-precision complex plane laboratory is separate. No WebGPU or perturbation rendering is claimed.

Four curated close-flight entry points (Surface descent, Into the folds, Beyond the slice, Microstructure) are sampled by the same CPU distance-field navigation rather than hand-authored meshes. The inspector flags approaches near the Float32 floor.

## Binary64 close flight

The volume precision selector offers Auto, GPU and CPU Float64. Auto switches near the Float32 floor; GPU mode explicitly retains the original limit. The Float64 implementation runs the same recurrence in a cancellable worker, with its own raymarch, normals and shading, a coarse pass followed by a full pass. It preserves binary64 camera coordinates and uses a conservative 2e-12 world-coordinate floor (rather than 2e-6). This is a numerical budget, not a guaranteed six-decade increase in geometrically reliable detail. The higher iteration cap is 120; the output is capped at 448 pixels on the longest side by default (640 high quality). CPU shading is intentionally not pixel-identical to GPU output. PNG capture waits for a completed pass. Both renderers are finite precision. No arbitrary-precision 3D claim is made.

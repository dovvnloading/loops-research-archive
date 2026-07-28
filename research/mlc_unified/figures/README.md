# Fractal illustration package

This directory contains reproducible parameter-plane and dynamical-plane
renderings for the MLC research documentation. Every image is produced by
direct iteration of

\[
f_c(z)=z^2+c.
\]

The images are mathematical illustrations, not numerical evidence for MLC,
UPTCR, VAAPC-I, analytic coercivity, or any other proof obligation.

## Plates

- `mandelbrot_overview.png`: full parameter plane with six parameters used
  by the dynamical atlas.
- `mandelbrot_multiscale_zoom.png`: three directly rendered scales around a
  seahorse-valley boundary point.
- `julia_dynamical_atlas.png`: Basilica, rabbit, parabolic, Siegel,
  Feigenbaum, and Misiurewicz Julia sets.
- `siegel_critical_orbit.png`: golden-mean Siegel Julia set with the
  computed critical orbit and neutral fixed point.

Exact windows, iteration counts, parameters, and pixel sizes are recorded
in `fractal_render_manifest.json`.

## Regeneration

Fast preview:

```powershell
python research/mlc_unified/figures/generate_fractal_plates.py --quality preview
```

Release-resolution render:

```powershell
python research/mlc_unified/figures/generate_fractal_plates.py --quality print
```

The bounded pixels are drawn dark. Exterior color is a smooth escape-time
coordinate with distance-estimator shading. Coloring improves legibility
but has no theorem status.

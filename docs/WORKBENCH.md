# Research workbench controls

The application chrome uses neutral graphite and steel blue. Palette selection affects the numerical viewport independently. The former glacier palette identifier remains valid for existing version 1 sessions; its colors are now steel blue.

- **Model:** editable power, iterations, escape radius, quaternion slice/Julia parameters, surface detail and landscape relief.
- **View:** precise real/imaginary center and span for parameter planes and landscapes, orbit yaw/pitch/distance, vertical field of view, flight and animation speed.
- **Render:** exposure, orbit coloring, gamma, contrast, saturation, plane band frequency/phase, light azimuth/elevation/intensity, ambient intensity, contour density and quality.
- New values use validated bounds and remain in version 1 JSON exports, bookmarks and share URLs. Old sessions receive defaults. Resetting a scene returns to defaults.
- GPU and Float64 volume renderers share lens, light direction, tone and palette controls; the CPU plane fallback implements escape radius, color bands, palette and tone. Backend shading and precision are not identical. Adaptive resolution is still bounded; numerical visualizations are not mathematical proof certificates.

Numeric fields accept exact finite values on blur or Enter; Escape cancels. The scene viewport remains keyboard accessible. No external runtime dependency or scientific dataset has been added. The existing browser smoke test now adjusts gamma and FOV, checks rendered pixel changes, and decodes the exported URL to verify both values were retained.

# Unbounded-satellite no-bound estimate

## Source-backed correction

Blokh, Levin, Oversteegen, and Timorin prove an upper estimate for a satellite
polynomial-like cycle with relative period (s) and polynomial-like degree
(d_*):

\[
(d_*-1)\operatorname{mod}(U\setminus K_*)
  < \frac{d_*(d_*-1)\pi}{\log(4(s+1))}.
\]

For a quadratic satellite renormalization, (d_*=2), so the available upper
bound is

\[
\operatorname{mod}(U\setminus K_*)
  < \frac{2\pi}{\log(4(s+1))}.
\]

Consequently, as the relative satellite period (s\to\infty), this upper
bound tends to zero. The source also explains that unbounded relative periods
rule out a priori bounds in the satellite case.

Source: <https://publications.hse.ru/pubs/share/direct/1052158150.pdf>

## Consequence for the MLC closure attempt

This rules out a tempting but invalid repair: one cannot close the unbounded
satellite complement by asserting a uniform positive lower modulus for all
quadratic-like returns. The correct bridge must work with degenerating root or
fundamental annuli and retain parabolic/cylinder, Ecalle-phase, critical-access,
and parameter-boundary data.

The estimate does not prove or disprove MLC. It narrows the analytic target and
shows why a source-faithful parabolic/cylinder theorem is necessary.

## Machine audit

`validate_unbounded_satellite_no_bounds.py` evaluates the quadratic bound on an
increasing sequence of periods and returns
`UNBOUNDED_SATELLITE_NO_BOUNDS_ESTIMATE_VALID`. It checks the transcription and
the finite numerical trend; the asymptotic limit is the elementary logarithmic
limit stated above.


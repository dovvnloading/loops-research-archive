# Parabolic satellite anchor: the corrected finite bridge model

## Result

This separate certificate constructs the smallest nontrivial parabolic
satellite anchor exactly. It does not modify the manuscript or original PDFs,
and it does not claim MLC.

Let

    lambda = exp(2*pi*i/3) = (-1 + sqrt(-3))/2,
    z_alpha = lambda/2,
    c_(1/3) = z_alpha - z_alpha^2.

Then (f_c(z)=z^2+c_{(1/3)}) has (z_\alpha) as a fixed point with multiplier
(lambda), so the third iterate has multiplier (1). In exact form,

    c_(1/3) = -1/8 + (3/8)*sqrt(-3).

This is the parabolic root model for the (1/3) satellite attachment to the
main cardioid. In the local coordinate (w=z-z_\alpha), one iterate is

    w |-> lambda*w + w^2.

Composing this germ three times and using (1+\lambda+\lambda^2=0) gives
zero quadratic and cubic coefficients, with a nonzero quartic coefficient.
The finite anchor is therefore genuinely parabolic/cylindrical; it is not a
Siegel map in disguise.

## Why this matters for the global attempt

Dudko's survey describes the correct parabolic enrichment: near-parabolic
return pairs converge to a commuting pair consisting of a parabolic
polynomial and a Lavaurs map, and cylinder renormalization quotients the
Lavaurs return by the parabolic map. It also states that the satellite and
neutral renormalizations are unified only at the level of the still-unfinished
Molecule-renormalization program.

Source: <https://arxiv.org/html/2512.24171>, Sections 3.5--3.8.

Thus the finite model repairs the previous bridge target:

* B1 must first construct a marked parabolic/cylinder pair and its actual
  transitional map;
* the cylinder pair must then be connected to a sector or pseudo-Siegel model
  with uniform distortion;
* the Ecalle phase and critical access must survive every nested satellite
  return; and
* parameter-side boundary control is still required for rigidity.

The exact calculation proves the finite parabolic anchor and exposes the
correct local normal form. It does not prove the uniform cylinder bounds,
Molecule hyperbolicity, virtual interpolation, or global MLC.

## Machine check

`validate_parabolic_satellite_anchor.py` uses exact rational arithmetic in
(\mathbb{Q}(\sqrt{-3})) and returns
`PARABOLIC_SATELLITE_ANCHOR_VALID`.

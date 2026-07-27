# Dyadic Böttcher external-trace isometry

Date: 2026-07-25  
Status: proved for the intrinsic external-sector trace; physical/core welding remains open  
Scope: separate subresearch artifact. Original manuscript and original PDFs are read-only.

## Source input

The checked Kahn--Lyubich decoration source identifies the preimages of the
root vertex by dyadic labels and describes the external arcs of dynamical
geometric puzzle pieces. In the locked `kingdom.tex` source:

- lines 121--130 give the dyadic labels and pullback labels;
- lines 293--301 construct the combinatorial external model;
- lines 309--319 give the external-arc length formula and its depth bound.

For an inverse branch of (f^{q}), the Böttcher angular coordinate has the
form

\[
T_{k,q}(\theta)=\frac{\theta+k}{2^q}\pmod 1.
\]

The integer (k) depends on the chosen source sector. The theorem below is
sectorwise: it does not silently identify different sectors or assert that a
single (k) works globally.

## Theorem

Let (I,Jsubset\mathbb R) be angular intervals and let

\[
T(t)=a+s t,
\qquad s=|J|/|I|>0,
\]

be an orientation-preserving affine rescaling from (I) to (J). For the
homogeneous (H^{1/2}) trace seminorm

\[
 [u]_{\dot H^{1/2}(I)}^2
 =\int_I\int_I
 \frac{|u(x)-u(y)|^2}{|x-y|^2}\,dx\,dy,
\]

the pullback (T^*u=u\circ T) satisfies

\[
 [T^*u]_{\dot H^{1/2}(I)}
 = [u]_{\dot H^{1/2}(J)}.
\tag{E}
\]

Indeed, (x=a+s\xi), (y=a+s\eta) gives (dx,dy=s^2d\xi,d\eta) and
(|x-y|^2=s^2|\xi-\eta|^2); the scale factors cancel exactly.

After normalizing each source and target arc to the unit interval, every
dyadic Böttcher inverse lift (T_{k,q}) is therefore an isometry of the
homogeneous external trace space. Orientation reversal has the same property
after replacing (T) by (a-s t). Constants are quotiented, so no endpoint
value is silently treated as a positive-energy mode.

## What this closes

This proves a uniform source-faithful statement for the **external sector
part** of the welding state:

```text
one declared sector
+ one declared dyadic inverse lift
+ normalized intrinsic H^(1/2) trace
-----------------------------------------------
=> exact norm-one trace transport.
```

The estimate is independent of the satellite period (q), the dyadic depth,
and the physical angular footprint. It supplies the external-coordinate part
of a possible common trace-space construction.

## What this does not close

The source has several exterior sectors and allows the branch integer (k) to
depend on the sector. The theorem does not prove:

- a compatible multisector choice for every infinite address;
- that all physical contact arcs are external sectors;
- a uniformly bounded physical Böttcher-to-core welding map;
- protection of endpoint traces through obstacle and root enlargement;
- uniform coercivity of the core response after welding; or
- a no-bypass serial-width estimate.

Thus this theorem repairs only the external affine-lift component of
`DIRECT_DECORATION_TRACE_WELDING_COMPACTNESS`. The physical/core welding and
all-depth contact graph remain open, so no UPTCR or MLC promotion is justified.

## Machine verification

`validate_dyadic_bottcher_external_trace_isometry.py` checks the exact scale
cancellation symbolically at the coefficient level, verifies dyadic interval
shrinkage and source anchors, and confirms that the theorem is sectorwise and
does not claim a global common inverse lift.

Output: `dyadic_bottcher_external_trace_isometry_20260725.json`; expected status
`DYADIC_BOTTCHER_EXTERNAL_TRACE_ISOMETRY_VALID`; `original_artifacts_written=false`.


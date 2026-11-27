---
ledger: NOV26_OPEN_CREST_LIMIT
result: partial
ai: OpenAI ChatGPT GPT-6 Astra Pro
human_review: none
---

<a id="limiting-crest-gate-20261126"></a>

# Rigorous limiting quadratic crest gate

## Claim

The target is the limiting quadratic model named in the crest asymptotics
note, Q_k(z) = 1 - k z^2. This packet replaces several numerical statements
about that model with exact, whole-interval Lean theorems, and reduces the
actual quadratic-return approximation to explicit real dynamical conditions.

Write K = [17903/10000,17904/10000] and S = [63/1000,33/500]. For every
k in K and s in S, there is a unique u in (-1/100,1/100) such that

    z = -3/4 + s (u + i sqrt(1-u^2)),   Re Q_k(z) = 0.

The first image has positive imaginary part. The third image is real and
satisfies -999/1000 < Q_k^3(z) < -977/1000 < -Q_k^4(0). These are literal
complex iterates, with the circle equation and every rational bound proved.
The angular coordinate has the continuous formula

    u_k(s) = (3/2 - sqrt(8/k + 8 s^2 - 9/4))/(4s).

The selected candidate integral

    C_sel(k) = (2 pi / log 2) integral_[.063,.066] 1/(s arccos u_k(s)) ds

is strictly greater than 1/4. This lower bound holds uniformly on K and uses
integral monotonicity, not numerical quadrature or sampled radii.

The endpoint module describes the same negative-real-part branch by
x_k(s) = -3/8 - sqrt(8/k+8s^2-9/4)/4 and y_k(s)^2 = x_k(s)^2 - 1/k.
On [1/16,1/8], it proves a unique radius r with Q_k^3(x_k(r)+i y_k(r)) = -1,
with 663/10000 < r < 133/2000. It proves strict decrease of the actual third
image, identifies the two sides of this endpoint, and supplies the complex
circle realization. This is a unique endpoint of this model branch.

The full source-model integral is defined with that endpoint:

    C_model(k,r) = (2 pi / log 2) integral_[1/16,r] 1/(s arccos u_k(s)) ds.

The angle stays nondegenerate throughout [1/16,1/8]. Thus this full integral
is well-defined, contains the selected subintegral, and is greater than 1/4.
The sharper coefficient module improves this to C_model(k,r) > 1/3.
The normalization is for one selected descendant, exactly as in the source;
the upper and lower descendants are not added together here.

For the whole radial range [1/16,133/2000], the arc-gate module verifies
all real endpoint itinerary tests, contains every initial-disk image through
step four in |z| < 23/20, and separates the second and third supports into
opposite half-planes. It proves injectivity of the full fourth iterate on
the part of that initial disk whose first image has positive real part.
The model-gate module proves crossing uniqueness on the full upper
semicircle and the strict fourth-image target gate between the second and
fifth critical-orbit cuts.

The persistence module proves an explicit open neighborhood of the interior
crossing and source gate: if H is continuous, maps both coordinate axes into
the real axis, and |H-Q_k| <= 2*10^-6 on |z| <= 23/20, then every s in S has a
crossing in the same angular interval, with positive imaginary first image,
real second and third images, and

    -.999 < Re H^3(z) < -.977 < -Re H^4(0).

All intermediate-domain checks follow from the hypotheses. The proof does
not assume the desired crossing, source gate, or perturbed orbit containment.
It does not assert uniqueness or a continuous selection for arbitrary H.

There is also a theorem about literal quadratic return maps, rather than
an assumed approximation. Let f_c(z)=z^2+c, x_j=f_c^j(0), d=x_p, and let
a_p be the coefficient of z^2 in f_c^p. If p >= 13, -2 <= c <= 0,
0 < d <= 12*4^(-p), and k=-a_p*d lies in K, then

    H(z) = f_c^p(d*z)/d

satisfies |H-Q_k| <= 24*4^(-p) < 2*10^-6 on |z| <= 23/20. Consequently
the actual normalized return has the same whole interior crossing and
third-image/source-cut corridor. No map-approximation, crossing, or
critical-orbit containment assumption appears in that theorem. The latter
containment follows from the invariant real interval [c,-c]. Existence of
the designated parameters satisfying the remaining scale and coefficient
inequalities for every p is not supplied by this conditional theorem.

The exact scaling identity d*H^m(z)=f_c^(m*p)(d*z) is proved for every m.
The unscaled corridor theorem consequently gives an actual point on
|z+3d/4|=d*s, a positive imaginary p-th image, real 2p-th and 3p-th images,
and the literal polynomial inequalities -d < f_c^(3p)(z) < -f_c^(4p)(0).

The parameter module supplies a unique k in K satisfying Q_k^6(0)+Q_k^3(0)=0,
so the model is instantiated rather than postulated. That parameter is
conjugate to the already studied real period-three tip parameter; its
isolation is supporting infrastructure, not the novelty claim of this packet.

## Evidence

The source is research/independent_audits/crest_transport_asymptotics_20261116/NOTE.md,
section "Quantitative near--2 evidence and the open limit". Its finite p <= 16
certificates do not establish its numerical limiting-model conjecture.
The new Lean modules are in formalization/weighted/:

- LimitingCrestParameter.lean: exact critical relation and parameter isolation.
- LimitingCrestGeometry.lean: uniform circle crossing and third-image gates.
- LimitingCrestCoefficient.lean: continuous angle and positive integral bound.
- LimitingCrestEndpoint.lean: unique model endpoint and exact circle realization.
- LimitingCrestArcGates.lean: endpoint itineraries, whole-support disk bounds,
  half-plane separation, and injectivity for the limiting quadratic.
- LimitingCrestModelGates.lean: full semicircle uniqueness and target cut gate.
- LimitingCrestLimit.lean: positive full model integral at the unique endpoint.
- LimitingCrestSharpCoefficient.lean: full model coefficient strictly above 1/3.
- LimitingCrestPerturbation.lean: disk Lipschitz bound and critical-orbit error.
- LimitingCrestPersistence.lean: existence and terminal gate under perturbation.
- LimitingCrestQuadraticReturn.lean: complete nonlinear remainder estimate
  and the source corridor for literal normalized quadratic iterates.

The coefficient proof bounds arccos(u) by 51 pi / 100 and log 2 by 7/10,
giving C_sel >= 100/(561 log 2) > 1/4. The perturbation recurrence is
E_(n+1) = 1+5E_n, E_0=0, so E_4=156. The quadratic critical orbit is proved
to remain in the unit disk, and the perturbed four-step orbit is then proved
to remain in the approximation disk by induction.

For the sharper full coefficient bound, u_k(s) > -1/200 on
[1/16,663/10000], so arccos(u_k(s)) <= 251*pi/500. With m=161/2500,
the affine minorant (2m-s)/m^2 <= 1/s has exact integral 19/322 on that
interval. Consequently C_model >= 9500/(40411*log 2) > 1/3.

For the actual-return theorem, the full remainder E_n(z)=f_c^n(z)-x_n-a_n*z^2
satisfies the exact recurrence

    E_(n+1) = 2*x_n*E_n + (a_n*z^2+E_n)^2.

The proof bounds every complex point of a disk: for n >= 1 and 4^n*r^2 <= 1,
|E_n(z)| <= (4^n*r^2)^2/128 for |z| <= r. It retains all higher-degree
terms. Taking r=(23/20)d and dividing by the actual positive d gives the
stated 24*4^(-p) bound. This is not a truncated Taylor approximation.

All Lean modules and public theorems are registered with the existing build,
source index, and transitive dependency audit. Local Lean is unavailable and
the workspace does not have disk capacity for the toolchain and Mathlib
cache; the repository's unmodified CI is the compiler and kernel authority.
The source checkout is sparse for the same disk constraint; the local packet
and proof-escape checks pass, while the whole-repository source-index check
must run against CI's complete checkout.
The PR's unmodified weighted-kernel workflow checks the complete project and
then audits the transitive axioms of every declaration, including private
helpers. To reproduce the new proof package with the pinned toolchain:

```sh
cd formalization/weighted
lake exe cache get
lake build LimitingCrestSharpCoefficient LimitingCrestArcGates LimitingCrestQuadraticReturn
cd ../..
python -B code/verify_lean_coverage.py --audit weighted
```

The source-coverage audit also rejects prohibited proof tokens. The PR
[PR #233](https://github.com/dovvnloading/loops-research-archive/pull/233)
contains the incremental compiler fixes and the final CI verification record;
no workflow, trusted baseline, or ledger status was weakened for this packet.

## Dependencies

NOV26_CREST_16 supplies the existing finite provenance. The source note
supplies the model and the proposed asymptotic integral, not premises of the
Lean proofs. The proofs use exact rational polynomial inequalities, actual
complex quadratic maps, and Mathlib's elementary analysis. Parameter
existence follows from the intermediate value theorem and a derivative
certificate; no numerical approximation is assumed to be an exact root.

## Boundary

NOV26_OPEN_CREST_LIMIT remains open. The literal-return theorem reduces its
complex approximation step to concrete real scale and coefficient bounds,
but this packet does not construct the archive's designated tip parameter
for every p >= 17 and establish those bounds there. The missing real chart
is the near--2 family at c=-2+t*4^(-p), t in [14,16]: return-value endpoint
signs, parameter monotonicity, quadratic-coefficient control, and the signed
critical relation selecting the tip. The source notes' Chebyshev-angle,
derivative-ratio, and cosine-product estimates are not imported as axioms.
Even after that real chart is formalized, transfer of the whole marked
curve family and its widths needs its regularity and marking arguments.

A possible next real proof uses the positive inverse branch B_c(x)=sqrt(x-c)
and the shooting equation c^2+c=B_c^(p-2)(d), with q=4^(-p),
c in [-2,-2+20q], and d in [0,14q]. Uniform inverse-orbit and product bounds
could establish the shooting signs and |a_p|q>3/20; an intermediate-value
argument could then locate the required quadratic coefficients and force
d<12q. This route is recorded for continuation only: it is not formalized
here, does not count as a result, and still needs the signed tip selection
and marked-curve arguments.

One crossing point at every radius is not by itself a transported Wave arc
family. A candidate integral is not by itself a physical marked width or
an unrestricted canonical supremum. The physical curve transport, prime-end
identification, convergence of widths, and the proposed numerical limit
near 0.347005 remain to be proved. No status record changes are proposed.

## Attribution

Builds on the archive's November 16 crest transport asymptotics and its
explicit limiting quadratic, circle center, angular branch, and terminal
gate. AI assistance covers proof search, Lean implementation, and review;
no independent human review has occurred.

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
about that model with exact, whole-interval Lean statements. The implementation
is undergoing CI verification; the final verification record belongs below.

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
- LimitingCrestPerturbation.lean: disk Lipschitz bound and critical-orbit error.
- LimitingCrestPersistence.lean: existence and terminal gate under perturbation.

The coefficient proof bounds arccos(u) by 51 pi / 100 and log 2 by 7/10,
giving C_sel >= 100/(561 log 2) > 1/4. The perturbation recurrence is
E_(n+1) = 1+5E_n, E_0=0, so E_4=156. The quadratic critical orbit is proved
to remain in the unit disk, and the perturbed four-step orbit is then proved
to remain in the approximation disk by induction.

All Lean modules and public theorems are registered with the existing build,
source index, and transitive dependency audit. Local Lean is unavailable and
the workspace does not have disk capacity for the toolchain and Mathlib
cache; the repository's unmodified CI is the compiler and kernel authority.
The source checkout is sparse for the same disk constraint; the local packet
and proof-escape checks pass, while the whole-repository source-index check
must run against CI's complete checkout.
The second CI run compiled LimitingCrestPerturbation, but two base-module
elaboration errors still blocked the other new modules. Those failures are
being corrected in the draft PR. No complete successful build is asserted
at this stage.

## Dependencies

NOV26_CREST_16 supplies the existing finite provenance. The source note
supplies the model and the proposed asymptotic integral, not premises of the
Lean proofs. The proofs use exact rational polynomial inequalities, actual
complex quadratic maps, and Mathlib's elementary analysis. Parameter
existence follows from the intermediate value theorem and a derivative
certificate; no numerical approximation is assumed to be an exact root.

## Boundary

NOV26_OPEN_CREST_LIMIT remains open. This packet does not yet prove a uniform
approximation theorem for the archive's actual normalized return maps for
all periods p >= 17. The analytic near--2 estimates in the source notes
are not imported as axioms. Transferring the model requires those estimates
in Lean, compatible domains and symmetries, and enough regularity to retain
the curve family and its markings.

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

---
ledger: KKL_STATIONARY_PROOF_USED_PREDECESSOR_SELECTION
result: partial
ai: OpenAI ChatGPT, GPT-6 Astra Pro
human_review: none
---

<a id="stationary-ambient-landing-20261127"></a>

# Ambient analytic collars and canonical landing for closed stationary limbs

Ledger statement being addressed:

> Prove conditional proof-used compatibility through H=b+2: every independently supplied depth-n proper restriction whose deep endpoint follows the declared central small-Julia parent itinerary lands in the canonical Q_0-selected component L_0^n and carries its actual-component address w_n. This is a universal compatibility assertion only; it does not construct the restriction, its endpoint occurrence, or its host. Those existential clauses remain in the incoming-window anchor, so no occurrence is assumed circularly.

## Claim

For the actual complex quadratic polynomial, native two-limb geometry constructs an ambient analytic collar of the entire closed canonical predecessor at every finite depth. Every independently supplied continuous ambient restriction whose projected connected trace stays in that collar, and which has one anchor in the selected source component, agrees everywhere with the canonical analytic inverse. Target landing then forces source landing and every canonical parent address. The source need not lie in the filled Julia set, and its endpoint is not assumed to exist. More generally, nested nonempty connected source tails have their entire source impression exactly identified as the inverse image of the target impression; no singleton or landing assumption is needed for this stronger trace-impression statement.

This is a polynomial ambient realization theorem toward the ledger obligation. It is not a proof of the remaining native psi-quadratic-like source identification. Compilation of the newly submitted sources is pending; until the weighted CI build and transitive audit pass, no theorem in this packet is claimed verified.

### Exact hypotheses and notation

Let K_c be the genuine bounded-orbit filled Julia set already defined by the archive, and F_c its restriction of z ↦ z²+c. Let a be a fixed point. The inputs are:

1. D is an open relative component of K_c minus {a}.
2. E is disjoint from D, and both F_c(D) and F_c(E) contain D.
3. The critical point 0 belongs to D.
4. n is an arbitrary natural number, and W is an arbitrary open planar neighborhood of the closed selected predecessor.

The nonzero condition a ≠ 0 follows from the first and third inputs. No local connectivity of K_c, preselected attachment point at depth n, or ambient inverse extension is assumed.

Write Ω_n = limbItinerary F_c D D n. Equivalently, a point lies in Ω_n exactly when its first n orbit positions and its terminal n-th image belong to D. Closures in this notation are taken in K_c; their subtype images are actual compact sets in the plane.

The conclusion constructs a connected open planar V containing the entire closed limb, a whole component U of (f_c^n)^(-1)(V), and an analytic inverse g on V. The source closure is compact, lies in the prescribed W, and f_c^n is injective on it. The exact identity is

    g(closed D) = closed Ω_n.

For any topological parameter space, preconnected parameter set S with an anchor t0, and continuous ambient trace gamma on S, assume f_c^n(gamma(S)) is contained in V and gamma(t0) belongs to U. Then

    gamma = g composed with f_c^n composed with gamma on S,
    gamma(S) = g(f_c^n(gamma(S))).

For every filter eventually supported on S, convergence of f_c^n(gamma) to y in the closed limb forces convergence of gamma to g(y). Every intermediate image has the canonical closed-parent address and converges accordingly. Interior target points recover the open itinerary; attachment points are included in the closed-limb conclusion.

For nested nonempty preconnected tails S_m inside the same anchored source trace, define the actual trace impressions

    I = intersection_m closure(f_c^n(gamma(S_m))),
    J = intersection_m closure(gamma(S_m)).

If I is contained in the closed target limb, then J = g(I), J is nonempty and connected, and every point of J has the canonical closed-parent itinerary. I may be a nondegenerate continuum. The compact-mark variant places the whole J inside Q_n and records every open parent address.

Here Ω_n denotes the inverse itinerary of the whole limb D. It is not silently identified with the ledger's L_0^n, whose base is a specified carrier contact such as T intersect D. The existing anchored-base component recognition is needed for that further identification.

The anchor must be in the same connected trace that stays over V. An anchor before an excursion outside V does not satisfy the theorem.

A companion compact-mark theorem works for any nonempty compact preconnected Q contained in D, without the global hypothesis 0 belongs to D. It constructs the exact compact marked predecessor Q_n and proves the corresponding ambient landing and parent-address conclusions. Q_n is not relabeled as an entire larger noncompact selected component.

## Evidence

### Proof structure

1. **Ambient confinement and reconstruction.** The image of a continuous restriction on a preconnected source is preconnected. If it lies in the full pullback of V and meets one component U, the entire image lies in U. The constructed left inverse then gives pointwise agreement and exact full-trace equality. Continuity of the analytic inverse converts target convergence into source convergence.

2. **Physical-to-planar component identity.** Complete invariance of the genuine filled Julia set identifies the subtype pullback with the full polynomial pullback. Connected components therefore agree after the subtype inclusion. This prevents an unproved switch from a relative component to a planar one.

3. **Critical exclusion for compact marks.** At any preterminal critical encounter, the next target lies in D. The alternative limb would provide a second point over the critical value, contradicting the singleton fiber of z²+c at c. The terminal point itself may be critical; only times strictly before n are excluded.

4. **Injectivity on the entire closed limb.** The closure of a punctured-space component can add only the puncture. Suppose two different boundary limits of the selected inverse have the same image. At least one source lies inside D. Openness supplies a nearby inverse in D, while density of the selected trace supplies another inverse in a disjoint neighborhood. This contradicts selected interior injectivity. Iteration proves closed-limb injectivity without selecting an attachment endpoint in advance.

5. **Critical exclusion at attachment limits.** The alternative-limb condition and 0 in D force c outside the closed target limb. Every prefix of a closed selected itinerary remains in the closed limb. A preterminal zero would send its next prefix to c, which is impossible. This supplies the critical exclusion on the whole compact closed predecessor, including attachment points.

6. **Constructed analytic collar.** The existing compact-univalence theorem supplies an open planar univalent neighborhood. Compactness, connectedness and exact image identify the compact core as a whole pullback component: locally it equals the full preimage, and a component cannot cross between this compact core and the complement of its open neighborhood. The existing selected analytic-collar construction then gives V, U and g with exact core identity and prescribed ambient confinement.

7. **Complete parent compatibility.** Compact continuous images commute with the closures used here. Combined with the exact existing prefix-image law, this gives every closed parent, and hence every intermediate landing limit. For a target in D, a prefix equal to the fixed cutpoint would force the terminal image to be that cutpoint; this recovers every open parent itinerary.

8. **Exact non-singleton impression transport.** Compactness of the source collar makes the polynomial image commute with the nested intersection of tail closures. Every source cluster has the corresponding target cluster, and injectivity on the entire closed collar identifies it with g of that target. Conversely every target cluster has a source preimage in the same intersection. This proves exact inverse covariance, rather than just a forward image inclusion, and gives nonemptiness, connectedness and all parent addresses without forcing a point impression.

### Lean sources

- [StationaryAmbientLanding.lean](../../formalization/weighted/StationaryAmbientLanding.lean): confinement, pointwise agreement, full-trace equality, filter landing, and the compact-core ambient landing constructor.
- [StationaryLimbCollar.lean](../../formalization/weighted/StationaryLimbCollar.lean): actual filled-set/plane transport, derived critical exclusion, constructed marked-core collar, and `limb_collar_ambient_landing`.
- [StationaryBoundaryExtension.lean](../../formalization/weighted/StationaryBoundaryExtension.lean): closed-limb injectivity and critical exclusion, the full closed-limb analytic collar, exact closed-parent images, and `quadratic_closed_limb_ambient_landing`.

- [StationaryAmbientImpressions.lean](../../formalization/weighted/StationaryAmbientImpressions.lean): exact inverse covariance, anchored tail-impression recognition, and constructed compact-mark and full closed-limb impression theorems.

All 27 public declarations across the four modules are registered in the existing theorem index and weighted Lake targets. No status record or workflow is edited.

### Validation

Lean is unavailable locally, and the local filesystem was already full before checkout. The repository's existing weighted CI is the compilation authority. It builds the modules in the Lean 4 project and audits every declaration's transitive dependencies, permitting only propext, Classical.choice and Quot.sound. Source scans reject unfinished proofs and trust escapes. The final successful run and proof commit will be recorded here after completion.

To reproduce after checkout:

    cd formalization/weighted
    lake build StationaryAmbientLanding StationaryLimbCollar StationaryBoundaryExtension StationaryAmbientImpressions
    cd ../..
    python3 -B code/verify_lean_coverage.py --audit weighted
    python3 -B code/contribute.py check

## Dependencies

Ledger prerequisites: KKL_STATIONARY_SELECTED_PREDECESSOR_CHAIN and KKL_STATIONARY_SELECTED_SMALL_JULIA_PREDECESSOR_CHAIN.

Archive Lean dependencies: StationaryPhysicalItinerary, StationaryFiberDynamics, StationaryLightModel, SaturatedTelescope, TelescopeUnivalentCollars, QuadraticUnivalentNeighborhood and TelescopeConformalInverse. Their existing theorems supply genuine filled-set invariance and openness, selected interior inverse/component recognition, exact prefix images, compact univalent extension and analytic inversion.

PrimeEndSectorImpressions supplies the existing forward covariance and nested connected-impression lemmas. The present inverse-impression theorem additionally constructs the ambient collar, proves exact inverse equality, and selects the complete physical parent itinerary.

The new work uses those archived results as prerequisites. It does not claim their proofs or the classical background as new.

## Boundary

Keep KKL_STATIONARY_PROOF_USED_PREDECESSOR_SELECTION open pending the native identifications below. No ledger status change is proposed.

- The analytic collar is constructed for the actual polynomial z²+c. KKL's native psi-quadratic-like correspondence, its chosen relative-cover lift and its ambient immersion must still be identified with an appropriate ambient inverse. Straightening on the filled set alone does not supply that identification.
- An actual proof-used occurrence must still provide a connected trace or terminal tail whose full projected image lies in the constructed collar, with an anchor in that same selected component. A historical anchor before leaving the collar is insufficient.
- The result does not construct the incoming-window occurrence, host or fine/coarse marked-access coupling. It does not assign an ideal access to a topological end or assert that all accesses land.
- The impression statements concern the specified actual nested ambient traces. Identification of those traces with KKL's exact marked prime-end occurrence or its angular footprint is not assumed proved.
- The collar depends on the parameter, depth and prescribed neighborhood. No uniform collar size, width bound or period-independent metric estimate is proved.
- A compact marked predecessor is kept distinct from a larger selected component. The latter needs the existing anchored-base recognition hypotheses.
- No Wave amplification, H1-H4, UPTCR or MLC is proved.

## Attribution

Kahn, Kapiamba and Lyubich, *MLC for parabolically bounded primitive renormalization*, arXiv:2606.27272v1, section 2.4, supplies the stationary predecessor problem. The archive reconstruction is [the selected-predecessor endpoint note](../../research/mlc_unified/kkl_stationary_n2_selected_predecessor_endpoint.md), especially Lemmas 2.1-2.2, Theorem 4.3 and section 7.

The relative closed-limb geometry was already recorded in that note, and is used here to reach a new ambient analytic and restriction-landing conclusion. Existing [physical itinerary](../stationary_physical_itinerary_20261126/NOTE.md) and [univalent telescope collar](../univalent_telescope_collars_20261126/NOTE.md) contributions are prerequisites, not novelty claims.

OpenAI ChatGPT, GPT-6 Astra Pro performed source comparison, mathematical proof search, Lean development, registration and CI review. Human review: none. No claim of worldwide priority is made.

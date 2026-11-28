---
ledger: NOV26_OPEN_CREST_LIMIT
result: partial
ai: OpenAI ChatGPT, GPT-6 Astra Pro
human_review: none
---

<a id="global-crest-classification-20261127"></a>

# Uniform actual crest gates on the complete parent radius range

## Claim

For every integer return index p at least 17, construct an actual quadratic
parameter and its unique upper-circle crossing family on the entire normalized
parent range [1/16,1/8]. The literal third-return coordinate is strictly
decreasing on that whole interval and crosses -1 exactly once, at a radius
r_p in (663/10000,133/2000).

Throughout the source's original parent interval [1/16,(p-1)/(8p)], the complete
two-sided terminal condition, together with the eight real q/w endpoint tests,
holds exactly on [1/16,r_p). The fourth terminal-image cut also holds there.
There are no later admissible intervals or isolated reentries. The inner
endpoint is included to anchor the relative connected-component statement;
the corresponding open circular collar is (1/16,r_p).

The selected actual radial coefficient, with the original period-dependent
parent normalization, is strictly greater than 1/3 for every p at least 17.
The globally classified endpoints and their full radial coefficients have the
previously proved limiting endpoint and positive limiting coefficient. The
analytic limit is an input; its identification with these globally maximal
algebraically admissible collars is the new assembly.

The parameters and all returns are literal polynomials. No identification
with a physical marked KKL width is asserted.

## Evidence

Research baseline: main commit `665e5f942d6b39902272fe6d8ca2dee6fbca8a6f`.
The draft was opened before the proof development as PR #251; intermediate
proofs and corrections are committed in that PR.

### What was open at this baseline

The archived `actual_maximal_crest_20261127/NOTE.md` explicitly leaves further
components outside S=[1/16,133/2000], the source q/w cuts, and an explicit
first return index unresolved. Its actual endpoint, order, and coefficient
conclusions are eventual. The older all-period signed-chart note proves
parameter facts, real critical-cut order, and a proper p-return; it does not
classify this circular crest or establish its all-period coefficient. The
source `crest_transport_asymptotics_20261116/NOTE.md` certifies the complete
circular calculation only through p=16 and explicitly leaves the all-period
extension open. Those earlier parameter and proper-return results are used
here and are not claimed as new.

| Question | Archived actual-crest theorem | Proved here |
|---|---|---|
| Radius range for terminal exclusion | [1/16,133/2000] | Entire [1/16,1/8], enclosing the original parent |
| Return indices for endpoint and strict order | Sufficiently large, unspecified | Every p at least 17 |
| Additional later admissible components | Not excluded outside S | Excluded by a global set equality |
| Eight actual q/w endpoint cuts | Open | Proved throughout the retained collar |
| Actual radial coefficient above 1/3 | Eventual | Every p at least 17 |
| Full integral limit | Already proved on the initial collar | Same limit for the globally classified collar |

### Literal objects and enlarged analytic control

Write f_c(z)=z^2+c, d=f_c^p(0)>0, and H(z)=f_c^p(dz)/d.
`NearTwoTip.exists_actual_tip` supplies a parameter satisfying `ActualTip`:
the near-minus-two parameter window, positive small return scale, normalized
quadratic coefficient kappa in [1.7903,1.7904], the signed six-versus-three
critical-return relation, and the required bounded critical orbit.

The new estimates prove, on the entire complex disk |z|<=3/2,

    |H(z)-(1-kappa*z^2)| <= 72*4^(-p).

The actual normalized even divided difference is within 61*4^(-p) of its
constant quadratic coefficient and has negative real part. Consequently its
complete fibers satisfy

    H(z)=H(w)  iff  z=w or z=-w

on that disk. These are proved from the full squaring remainder and divided
difference recurrences, not assumed distortion estimates. The larger domain
accommodates the uniform second-phase bound 13/10, beyond the old comparison
radius 23/20.

The crossing family is

    z_p(s)=-3/4+s*(u_p(s)+i*sqrt(1-u_p(s)^2)),
    Re H(z_p(s))=0,  Im H(z_p(s))>0.

It exists on [1/16,1/8], is unique among upper-semicircle crossings, and has
100-Lipschitz angular coordinate. Its first image has norm below 2/5; its
second image is real and lies strictly between 99/100 and 13/10. These
bounds hold for every p at least 17 and every `ActualTip` parameter, not just
a chosen convergent parameter sequence.

### Global rigidity and the unique terminal collision

Let T_p(s)=Re H^3(z_p(s)). Its third image is exactly real. A collision of
terminal coordinates therefore gives a collision of third images. Apply
the complete signed-fiber theorem three times. At the second phase the
positive real sign excludes opposite points; at the first phase the positive
imaginary sign excludes them; at the input phase the strictly negative real
parts exclude them. Thus the input points, and hence their radii, coincide.

This proves global injectivity without assuming terminal order. A continuous
injective real function on an interval has one strict orientation. Exact
endpoint tests

    T_p(663/10000)>-1,   T_p(133/2000)<-1

force the decreasing orientation. The tests compare the actual curve with
the quadratic having its own coefficient kappa_p; no limiting-parameter
threshold is needed. The terminal comparison error is at most 1/100000,
with all three intermediate evaluations in certified disks. Rational model
endpoint margins exceed 1/10000.

The opposite cut is already inactive at the inner radius:

    T_p(1/16)<-Re H^4(0).

Global strict decrease propagates it across the parent. The intermediate
value theorem and injectivity construct r_p and give the exact set equality

    [1/16,(p-1)/(8p)] intersect
      {s : -1<T_p(s)<-Re H^4(0)} = [1/16,r_p).

This excludes every later component and isolated reentry, not merely an
extension of the initial connected component.

### Source cuts and original-plane placement

The positive real fixed cut alpha_p is constructed in (0.518,0.519) and is
unique in the control interval. With q=-3/4+s and w=-3/4-s, exact actual
iteration bounds prove all eight source real tests on [1/16,133/2000]:
the source locations of q,w; their first-image cuts; both second-image
cuts; and the third and fourth q-image cuts. These tests apply to the retained
collar; global terminal exclusion removes the outer radii.

The fourth terminal-image condition follows from the same literal dynamics:
on -1<T_p<-Re H^4(0), evenness and strict decrease of H on the positive real
axis imply

    Re H^2(0) < Re H^4(z_p(s)) < Re H^5(0).

The entire input disk |z+3/4|<=1/8 lies in the already constructed actual
proper central p-return component. After scaling, every candidate parent
circle lies in both the physical central return and the archive's original
return component. At the unique terminal radius the proof produces a point
v_p in both components with

    |v_p+3d/4|=d*r_p,
    Re f_c^p(v_p)=0,   Im f_c^p(v_p)>0,
    f_c^(3p)(v_p)=-d.

This is an exact complex polynomial identity. Component inclusion does not
identify the two components, their prime ends, or their KKL marking.

### Quantitative coefficient for every p at least 17

For the full retained collar define the source-normalized radial integral

    C_p = 2*pi/log(2-2/p)
          * integral_[1/16,r_p] 1/(s*arccos(u_p(s))) ds.

Restriction of the global branch to S gives |u_p(s)|<1/100. Exact sine and
arcsine inequalities imply

    0<arccos(u_p(s)) <= (63/125)*pi.

With m=161/2500, the affine minorant (2m-s)/m^2<=1/s integrates on
[1/16,663/10000] to 19/322. Positivity on the remaining interval and the
endpoint lower bound therefore give

    C_p >= (2375/10143)/log(2-2/p) > 1/3.

The final inequality uses 0<log(2-2/p)<log 2<7/10 and exact rational
arithmetic. It uses neither numerical quadrature nor an eventual convergence
threshold. The affine-minorant technique comes from the archived model
coefficient proof; the new conclusion is for the actual globally classified
collar at every admissible return index.

### The same endpoints have the archived limit

Restrict the global family to S. The global endpoint is an archived
`InitialCollar` endpoint at every index. First-exit uniqueness identifies it
with the endpoint sequence in `ActualCrestIntegral` wherever that earlier
eventual construction applies. The actual angles agree pointwise on the
whole integration interval, so their complete radial integrals agree.
Endpoint and coefficient convergence transfer to the globally classified
sequence. The limiting coefficient above 1/3 is an imported result, not a
newly claimed asymptotic computation or a certificate of the numerical value
0.347005.

### Lean verification

The proof modules are `GlobalCrestEstimates`, `GlobalCrestCrossing`,
`GlobalCrestOrder`, `GlobalCrestSourceGates`, `GlobalCrestEndpointValues`,
`GlobalCrestClassification`, `GlobalCrestPhysical`, `GlobalCrestCoefficient`,
`GlobalCrestFinalCut`, and `GlobalCrestLimit`, all in
`formalization/weighted/`. Build targets and every public theorem are
registered with `code/contribute.py lean-add`.

The first complete CI proof build is commit
[`227800743294fa230527a572f804bf33a3089765`](https://github.com/dovvnloading/loops-research-archive/commit/227800743294fa230527a572f804bf33a3089765),
with the ordinary full build and transitive audit in
[weighted Lean run 46098906835](https://github.com/dovvnloading/loops-research-archive/actions/runs/46098906835).
All ten modules compiled. The unchanged audit checked every declaration in
all 215 weighted modules: 4,963 declarations in total. This includes all 237
declarations from the ten new modules, including private and generated
declarations. Every transitive dependency is among the permitted foundations
`propext`, `Classical.choice`, and `Quot.sound`.

The source-coverage and prohibited-token check passed for all 264 Lean source
files. The contribution intake passes against the unchanged main baseline.
Local checks also compiled the root project and the new crossing, enlarged
estimates, and global collision modules; the full ordinary weighted build and
full declaration audit were performed in CI. The final documentation update
changes no Lean source, and the PR records its current checks separately.

The repository's existing workflows, trusted baseline, and ledger files are
unchanged. Reproduction uses:

    cd formalization/weighted
    lake build
    cd ../..
    python3 -B code/verify_lean_coverage.py --audit weighted
    python3 -B code/contribute.py check

## Dependencies

`NOV26_OPEN_CREST_LIMIT`, `NOV26_CREST_16`; the existing actual-tip,
crossing, divided-difference, limiting-model, and proper-return modules;
the repository's pinned Lean 4.32.0 and Mathlib revision.

## Boundary

`NOV26_OPEN_CREST_LIMIT` remains open; no ledger status change is requested.

- The all-period assertion here means every integer return index p>=17 for
  constructed `ActualTip` parameters. Identification with the source's
  distinguished primitive-component branch, least critical preperiod, and
  primitive renormalization period remains open.
- The exact admissible-set statement concerns the unique upper-circle
  crossing, eight real q/w endpoint cuts, and the two terminal-image cuts.
  Complete complex phase-disk separation, physical KKL access marking,
  genuine marked proper-path survival, prime-end transport, and conformal
  width identification are not established by this contribution.
- The radial coefficient is not an unrestricted Wave optimum or a proved
  physical extremal width. The existing analytic limit is reused; neither
  the displayed decimal near 0.347005 nor a new asymptotic error rate is
  certified here.
- The finite source certificates for p=3,...,16 are not replaced by Lean
  proofs in this packet. No theorem for all p>=3 is asserted.
- No H1-H4, UPTCR, or MLC conclusion is claimed. Novelty is checked against
  the inspected archive, not certified worldwide priority.

## Attribution

The short-window endpoint and radial-integral limit, model coefficient,
actual-tip existence, complete squaring remainder, and proper central return
belong to the archived contributions and are inputs. Several local proof
patterns are extended from those modules; their old conclusions are not
resubmitted as research progress. The new claims are the complete actual
parent exclusion, literal retained source cuts, and explicit p>=17 endpoint
and coefficient conclusions. AI-assisted development and independent AI
scope review; no independent human review. Original work is released under
the repository's CC0 terms.

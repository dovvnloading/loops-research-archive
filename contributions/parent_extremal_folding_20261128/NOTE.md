---
ledger: NOV26_OPEN_OPTIMAL_LIMIT
result: partial
research_status: withdrawn_without_qualifying_result
ai: OpenAI ChatGPT, GPT-6 Astra Pro; research and adversarial review
human_review: none
---

# Withdrawn attempt: exact parent-Wave extremal domain

## Claim

**No qualifying result was established.** The proposed partial result below
was not proved in Lean and is not submitted as a mathematical contribution.
This draft is closed to release the obligation, following AGENTS.md.
The ledger, existing proofs, build configuration and workflows are unchanged.

The target was the exact value and attainment clauses of
NOV26_OPEN_OPTIMAL_LIMIT. Complete parent-supremum convergence was already
proved on main and was not a new target.

The formulas below are retained as an explicitly unvalidated research
checkpoint. They must not be cited as a proved width formula, an optimizer
construction, a sharp physical convergence theorem or a novelty claim.

## Evidence

### 1. Base and exclusion of duplicate work

The investigation started from main commit
6a10209b3cc51878bc45de7668894757b2575e08.

The following are already in the archive:

- contributions/marked_wave_supremum_limit_20261127/NOTE.md proves complete
  actual parent-Wave supremum convergence, with physical disk homotopies
  and an explicit error containing an O(1/p) term.
- contributions/actual_crest_path_width_20261127/NOTE.md proves complete
  circular descendant paths, their actual modulus and a positive limit.
- research/independent_audits/tip_family_wave_gain_correction_20261123/NOTE.md
  proves the corrected independent positive gain and explicitly distinguishes
  it from the incompatible paired-parent problem.
- contributions/uniform_three_return_collar_20261127/NOTE.md already
  supplies all-period actual three-return collars.
- Closed PR #256 already rejected the fixed-reference whole-annulus QC
  obstruction as an easy consequence of archived Joukowski barriers.

Reformalizing any of these would not satisfy this task.

### 2. Candidate finite-disk formula, not a theorem

Let
```text
-R < ell < a < b < r < R,
Omega_R = {z : |z| < R} minus [ell,r].
```
The intended parent class has lower-to-upper bank endpoints over (a,b)
and the literal endpoint-fixed relative homotopy passing around ell.

Set
```text
T_R(x) = R (x-ell) / (R^2-ell*x),
h_R(x) = 2 sqrt(T_R(x)) / (1+T_R(x)),
k_R    = (h_R(b)-h_R(a)) / (h_R(b)+h_R(a)),
E(k)   = K(k) / K(sqrt(1-k^2)),
K(k)   = integral_0^(pi/2) (1-k^2 sin(theta)^2)^(-1/2) dtheta.
```
The proposed identity was P_R = E(k_R), independent of r.

The candidate lower domain is the disk with the entire ray segment
[ell,R) deleted. The explicit coordinate chain is
```text
z -> T_R(z) -> zeta, zeta^2 = -T_R(z)
  -> 2*zeta/(1-zeta^2).
```
On the selected branch this maps the ray-cut disk through the right
half unit disk to the right half-plane.

For an arbitrary parent competitor, one would instead lift its entire
path through zeta^2=-T_R(z), prove opposite endpoint signs from its
actual LeftClass homotopy, and reflect by
```text
zeta -> |Re zeta| + i Im zeta.
```
The symmetric quadrilateral metric is the proposed upper metric.

This is only a route to a proof. In particular, the reflected path may
touch the imaginary axis. Treating it as a path in the open half-plane
without addressing those contacts would be incorrect.

### 3. Limiting expression and proposed sharper rate

Put A=sqrt(a-ell), B=sqrt(b-ell), and k=(B-A)/(B+A).
The proposed limiting value is E(k), which equals the archive's embedded
half-strip lower competitor P_minus.

The formal expansion of the candidate cross-ratio is
```text
k_R = k (1 - 2 A B / R + O(R^-2)).
```
If the unproved physical identity P_R=E(k_R) were established, it would
give a positive first-order finite-radius defect. With the classical
elliptic derivative identity, its proposed coefficient is
```text
P_infinity - P_R
 = pi (A+B)^2 / (4 K(sqrt(1-k^2))^2) * R^-1 + O(R^-2).
```
This is not a proved asymptotic for the archive's width.

For the existing actual-tip normalization,
R_p=2^(-p)/d_p and 0<d_p<=12*4^(-p). Thus an established O(1/R_p)
metric comparison, together with the archived orbit-mark estimates,
would yield an O(2^(-p)) rate instead of the existing generic O(1/p)
escape estimate. A sharp coefficient would additionally require the
appropriate actual-scale limit and its proof.

No such physical rate or coefficient is proved here.

### 4. A tempting incomplete argument was rejected

The proposed limiting metric has squared density proportional to
```text
1 / |(z-ell)(z-a)(z-b)|.
```
Its far-field energy is O(1/R). That fact alone does not bound the
loss of the optimum by O(1/R): deleting all leaves that reach outside
the disk can discard complete leaves, with a larger transverse loss.
It would be a gap to infer the improved physical rate from tail
energy alone.

An alternative geometric route uses the right semidisk map
```text
phi_S(zeta)=zeta/(1-zeta^2/S^2).
```
The candidate electrode cross-ratio is exactly
k*(S^2-A*B)/(S^2+A*B). Semidisks with S^2=R-|ell| and R+|ell|
suggest a sandwich with a common first-order term. This still requires
the same complete metric and foliation bridge, not just its algebra.

### 5. Exact missing proof obligations

No result would count until all of the following are supplied inside the
existing Lean project:

1. Lift every ParentLeaf and its literal RelSlitHomotopy through the
   nonzero square map, deriving the endpoint signs from LeftClass.
2. Prove admissibility of the descended metric for arbitrary continuous
   simple traces, including folding-interface contacts and nonrectifiable
   traces under the existing Hausdorff-length definition.
3. Construct the quadrilateral extremal metric and prove its full area
   and normalization identities; do not add Schwarz-Christoffel or
   extremal-domain facts as axioms or hypotheses that contain the goal.
4. Construct a complete maximizing Borel Wave in the literal physical
   domain, proving pairwise disjoint interiors, bank conditions and the
   full relative homotopy class.
5. Apply the result to the actual polynomial orbit marks and prove the
   quantitative physical conclusion.
6. Compile the theorem in the unchanged CI and pass the transitive
   axiom audit.

The inspected Lean modules provide modulus transport and circular
foliation tools, but not this complete analytic realization. An
algebra-only cross-ratio theorem with these clauses assumed would be
peripheral and is deliberately not submitted.

### 6. Validation outcome

No new Lean source was added. There is therefore no new compiled theorem,
no successful Lean CI result for the candidate, and no audited proof of
the proposed width identity.

The local toolchain was absent and the filesystem had only a few
megabytes free, so a full local installation was unavailable. This is
not the mathematical reason the task failed: the complete proof and
novelty case above were not established. CI could only validate an
actual completed implementation, not the exploratory formulas.

## Dependencies

### Archive sources inspected

- research/tip_family_theorem/THEOREM.md and AUDIT.md.
- research/independent_audits/real_primitive_tip_family_canonical_width_20261116/NOTE.md.
- research/independent_audits/real_primitive_tip_family_canonical_width_sandwich_20261116/NOTE.md.
- research/independent_audits/tip_family_limiting_wave_gain_20261116/NOTE.md.
- research/independent_audits/tip_family_wave_gain_correction_20261123/NOTE.md.
- research/independent_audits/maximal_native_wave_20261123/NOTE.md and H3_WIDTH.md.
- research/independent_audits/canonical_width_attack_20261124/NOTE.md.
- contributions/marked_wave_supremum_limit_20261127/NOTE.md.
- formalization/weighted/MarkedSlitTransport.lean,
  SlitWaveModulus.lean, CrestConformalModulus.lean and
  CircularCrestModulus.lean.

### Classical prior-art boundary

The symmetry and extremal-domain mechanisms are classical, not newly
discovered principles. Relevant sources include:

- C. D. Minda and B. Rodin, "Extremal Length, Extremal Regions and
  Quadratic Differentials", Commentarii Mathematici Helvetici 50 (1975),
  455-475, https://doi.org/10.1007/BF02565762.
- J. A. Jenkins, "On the existence of certain general extremal metrics II",
  Tohoku Mathematical Journal 45 (1993), 249-257, Theorems F and U and
  the boundary-path discussion in section 2,
  https://www.jstage.jst.go.jp/article/tmj1949/45/2/45_2_249/_pdf/-char/en.
- M. Fortier Bourque, "The holomorphic couch theorem", Inventiones
  Mathematicae 212 (2018), 319-406, section 7 on extremal length and slit
  embeddings, https://arxiv.org/html/1503.05473v4.

These general results do not themselves supply a verified application
to this repository's full Borel-Wave and Hausdorff-trace definition.
The limited literature search does not establish worldwide priority
for the proposed finite-disk formula or its physical application.

## Boundary

The proposed partial result was not established. NOV26_OPEN_OPTIMAL_LIMIT
remains open. No exact width, attainment, sharp actual-tip rate, complete
KKL marking, joint parent-child optimum, buffered gain, H1--H4, UPTCR or
MLC conclusion is claimed.

This is a closed research-attempt record, not a contribution ready for
review or a theorem awaiting only routine compilation.

## Attribution

The archive and original authors retain credit for the existing
mathematics. Three parallel AI investigations compared prior work,
checked the candidate geometry and examined literature. Those are not
independent human review. AI assistance is disclosed in the frontmatter.

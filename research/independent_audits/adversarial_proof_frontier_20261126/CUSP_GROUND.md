# The full cusp ground-transfer limit and a nonuniformity obstruction

**Target:** H4_RIGIDITY remains OPEN. This advances the changing-ground interface of [parameter ground transfer](../parameter_ground_transfer_20261126/NOTE.md) and [sharp boundary frontier](../../frontier/sharp_boundary_frontier_20261126/NOTE.md). It combines the kernel theorem of [CUSP_KERNEL.md](CUSP_KERNEL.md) with a physical counterexample to extending its pointwise conclusion uniformly over cusp-scale continua. GPT-6.2 written argument; no independent human review or ledger promotion.

## 1. Definitions and theorem

For simply connected proper plane domain D, let g_D(x,y) be the positive Green kernel, normalized to have singularity −log|x−y|. Its regular part is A_D(x,y)=g_D(x,y)+log|x−y|, continuously extended by A_D(x,x)=log r_D(x). For a nonpolar compact E⊂D let V_D(E) be the infimum of the Green energy over Borel probability measures on E, as in the archive's ground-transfer notes. Polar sets are excluded. Put

    e_(s,t)(F) = V_(D_t)(F)−V_(D_s)(F)−(t−s),   0<s<t,

and K_(s,t)=g_(D_t)−g_(D_s)−(t−s), with the diagonal filled continuously.

Fix 0<α<β, t=u^α, s=u^β, L=log(1/u), a=π log(2)/L. Define b_t=α^(-2), b_s=β^(-2), so b_s<b_t, and S_b=C∖[b,+∞).

**Theorem A (full scaled kernel).** Locally uniformly on S_(b_s) × S_(b_s), including the diagonal,

    K_(s,t)(c₀+a² w,c₀+a² v) → A_(S_(b_t))(w,v)−A_(S_(b_s))(w,v).   (1)

The limit is explicit. With ζ_b(w)=√(1−w/b), of positive real part,

    A_(S_b)(w,v) =
      log[b |ζ_b(w)+ζ_b(v)| |ζ_b(w)+conj(ζ_b(v))|].               (2)

In particular the diagonal limit equals

    log [ b_t |ζ_(b_t)(w)| Re ζ_(b_t)(w)
         / (b_s |ζ_(b_s)(w)| Re ζ_(b_s)(w)) ].                      (3)

At w=0 it is 2 log(β/α), with an O(L^(-2/3)) error by CUSP_RATE.md.

**Theorem B (uniform energy transfer on compact rescaled windows).** For every compact Q⊂S_(b_s), and every nonpolar compact E⊂Q, put F=c₀+a²E. For all sufficiently small u (depending on Q, not E), F⊂D_s, and

    e_(s,t)(F) =
      V_(S_(b_t))(E)−V_(S_(b_s))(E)+o(1),                         (4)

uniformly over all such E, including E=E_u varying arbitrarily with u. In particular the assertion applies to all actual Mandelbrot compacts F with the specified rescaled containment. It does not assert that every E in Q is realized in M; every fixed compact off [0,+∞) is so realized for sufficiently small u by the main-cardioid argument.

## 2. Proof of Theorems A and B

Write Ω_j for (D_j−c₀)/a², j=s,t. For any compact Q⊂S_(b_s), CUSP_KERNEL.md proves eventual containment in both Ω_j and local uniform convergence of the normalized Riemann maps ψ_j:Ω_j→D to the corresponding slit maps ψ_(b_j). By conformal invariance,

    A_(Ω_j)(w,v)=
      log |1−conj(ψ_j(v))ψ_j(w)| − log |(ψ_j(w)−ψ_j(v))/(w−v)|.

On the diagonal the divided difference means ψ'_j(w). It converges uniformly on Q×Q: away from the diagonal this follows directly from uniform convergence; near the diagonal use a finite covering by disks compactly contained in S_(b_s) and Cauchy derivative convergence on slightly smaller disks, then integrate the derivative along the short segment. The limiting divided difference is never zero by univalence off the diagonal and nonzero derivative on it. Both log arguments therefore have positive minima on Q×Q for the limit, and their logarithms converge uniformly. Thus A_(Ω_j)→A_(S_(b_j)) on each such product. The scaling identity for Green functions cancels log a² in the difference, and t−s→0. This proves (1). Formula (2) follows from the right half-plane kernel

    g_(S_b)(w,v)=log |(ζ_b(w)+conj ζ_b(v))/(ζ_b(w)−ζ_b(v))|

and (ζ_b(w)−ζ_b(v))(ζ_b(w)+ζ_b(v))=(v−w)/b. Formula (3) follows by continuity, since r_(S_b)(w)=4b|ζ_b(w)|Re ζ_b(w).

For (4), the singularity −log|w−v| is identical for A_(Ω_j) and A_(S_(b_j)). Their uniform regular-part difference bounds the difference of the energies of every probability with finite logarithmic energy by the same sup norm. Probabilities of infinite logarithmic energy have infinite Green energy in both domains because their regular parts are bounded on E×E. Nonpolarity gives at least one finite-energy probability. Taking infima in both directions proves

    |V_(Ω_j)(E)−V_(S_(b_j))(E)|
      ≤ sup_(Q×Q)|A_(Ω_j)−A_(S_(b_j))| → 0.

This uses no claim that the minimizing measure is the same for the two grounds. Conformal invariance gives V_(D_j)(F)=V_(Ω_j)(E), and (4) follows by subtraction.

## 3. Actual near-cusp ground-loss divergence

**Theorem C (physical obstruction to cusp-scale uniformity).** Fix 0<α<β. There exist closed Euclidean disks F_u entirely in the main hyperbolic cardioid, of diameter comparable to L^(-3) and distance O(L^(-2)) from 1/4, for all sufficiently small u, for which

    e_(u^β,u^α)(F_u) = log L+O(1).                                (5)

At the cusp itself the diagonal penalty converges to the finite value 2 log(β/α). Thus even an O(L^(-2)) parameter neighborhood of the cusp does not inherit the pointwise cusp ground-loss law uniformly over physical nonpolar continua. These witnesses are not a nested renormalization tower.

**Proof.** Let R_u>0 solve G(c₀+a²R_u)=s. Existence with R_u→b_s follows from continuity of G on the real axis and the strict real bracketing from CUSP_KERNEL.md for every pair R_-<b_s<R_+. For example fix a small positive bracket and take the first real crossing; monotonicity from the actual real critical recurrence ensures that every such crossing satisfies R_u→b_s. The same monotonicity implies Ω_s⊂C∖[R_u,+∞) because G≥s on that real ray.

Choose a fixed k>2+2(b_s+2)^(3/2), and for small u take the scaled disk

    E_u = {w: |w−(R_u+i k a)|≤a}.

For all w in E_u, Im w≥(k−1)a, and |w|≤b_s+2 eventually. Thus

    Re √(-w)/|w| ≥ |Im w|/(2|w|^(3/2))
                  ≥ (k−1)a/[2(b_s+2)^(3/2)] > a.

This is the exact attracting-fixed-point criterion, so F_u=c₀+a²E_u is a closed disk wholly inside the actual main cardioid. Its diameter is 2a³ and its distance to c₀ is O(a²). In particular it is nonpolar and contained in D_s.

For the small ground, affine invariance of Green energies and domain monotonicity give

    0≤V_(Ω_s)(E_u)≤V_(C∖[R_u,+∞))(E_u)
                     =V_(C∖[0,+∞))(closed disk centered ik, radius 1).

The last equality uses w↦(w−R_u)/a and the last constant is finite: the disk is compact in the slit domain, its regular part is bounded there, and normalized angular measure on its boundary has finite logarithmic energy (the log singularity on the circle is integrable).

For the large ground, E_u converges as a compact set to b_s∈S_(b_t). All E_u for small u lie in a fixed compact disk Q inside S_(b_t). By the same normalized-map argument as in §2 (using only the large ground), A_(Ω_t) is uniformly bounded on Q×Q. Thus V_(Ω_t)(E_u) differs by O(1) from the infimum of logarithmic energy on E_u. That infimum is log(1/a)+O(1): scale the disk to unit radius, where the energy is bounded below by −log 2 since all pair distances are at most 2, and bounded above by the finite energy of angular measure. Combining the two estimates, using t−s→0 and a=π log(2)/L, gives (5).

This is an actual physical counterexample, not a model kernel. It does not contradict Theorem B, because E_u tends to the excluded small-ground slit endpoint b_s and lies in no fixed compact subset of S_(b_s). For the same reason a naive compactness proof omitting compact rescaled containment would be invalid.

## 4. Adversarial interpretation and scope

The strongest useful conclusion here is a two-part interface: (i) on fixed compact rescaled windows away from the smaller slit, the entire centered transfer kernel and every nonpolar compact's energy difference have an explicit uniform limit; (ii) the exclusion of the moving boundary is essential even for actual continua lying inside one hyperbolic component. The near-cusp divergence arises with both grounds on the same logarithmic scale, not from holding t fixed while s→0.

This does not disprove the archive's conditional shrinking criterion, which uses actual ground comparisons; it excludes a possible unjustified substitute based solely on the cusp center's conformal radius. It also does not show that an actual protected nest realizes these disks or that any such nest has nontrivial intersection. No claim of a counterexample to MLC. No global proof status changes.

Inputs: the classical Green kernel formula, Riemann-map invariance, the actual quadratic parameter uniformization and the proofs in CUSP_KERNEL.md and CUSP_RATE.md. No further imported dynamics theorem. Mathematical novelty relative to the cited archive notes, not established literature priority. The argument is written mathematics, not a formal Lean proof.

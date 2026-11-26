# Localized harmonic barrier: sharper cusp conformal radius error

This replaces the sufficient O(L^(-2/3)) error of [CUSP_RATE.md](CUSP_RATE.md) by O(log L/L), retaining the earlier proof as an independent check. The exact slit kernel and physical near-cusp obstruction in [CUSP_GROUND.md](CUSP_GROUND.md) are unchanged.

**Theorem.** Uniformly for α in each compact positive interval,

    r_(u^α)(1/4) = [4π²(log 2)²/(α² L²)] (1+O(log L/L)),
    L=log(1/u)→∞.                                                 (1)

No matching lower bound for the error or wider literature-priority claim is made. This is a written analytic estimate for the actual quadratic parameter domain, not a new MLC case.

## 1. Setup and exact forbidden-region estimate

Write a=π log(2)/L, b=α^(-2), Ω=(D_(u^α)−1/4)/a². CUSP_RATE §1 gives

    {|w|≤R_-}⊂Ω⊂ C∖[R_+,+∞),
    R_±=b(1±C log L/L).

Set B=R_->0. All constants below are uniform when B ranges over a compact positive interval. On the right half-plane H={Re ζ>0} write ζ=x+iy and use the conformal bijection

    w=B(1−ζ²): H → S_B=C∖[B,+∞).

The point ζ=1 maps to w=0, with derivative of absolute value 2B. Let U be the connected component of {ζ∈H: B(1−ζ²)∈Ω} containing 1. It is simply connected: the intersection Ω∩S_B has simply connected components, since any Jordan curve in one component has its bounded interior in both simply connected domains and hence in that same component. Pull back by the conformal bijection. In particular its conformal radius is well-defined.

We claim that there is a uniform constant C₁≥1 such that every ζ∈H whose w is outside Ω satisfies at least one of

    |ζ|≤1 and x|ζ|≤C₁ a,                          (small)
    |ζ|≥1 and Re(1/ζ)=x/|ζ|²≤C₁ a.               (large)

The closed disk of radius B is included in Ω, so |w|>B. Furthermore w cannot satisfy the cardioid inequality Re√(-w)>a|w| (with root of positive real part); all such points belong to Ω.

If Re w>0, the proof in CUSP_RATE §2 shows |y|>|x|/3, since |1−ζ²|>1 and x²<1+y², hence |y|≥|ζ|/√10. In particular w is nonreal. That same square-root estimate gives

    Re√(-w)/|w| ≥ x|y|/[√B (1+|ζ|²)^(3/2)].

For |ζ|≤1 its right side is at least x|ζ|/√(80B), and for |ζ|≥1 at least x/(√(80B)|ζ|²). Since the left side is ≤a outside Ω, the claim follows with C₁≥√(80B).

If Re w≤0, then Re√(-w)≥√(|w|/2). Failure of the cardioid criterion implies |w|≥1/(2a²), so |ζ|²≥|w|/B−1≥1/(4Ba²) for sufficiently small a. Thus |ζ|≥1 and Re(1/ζ)≤1/|ζ|≤2√B a. Enlarging C₁ proves the claim also in this case. This argument includes real negative w and does not assume the cardioid contains any positive real point.

## 2. A positive harmonic barrier with small cost at 1

The half-plane Green kernel with pole 1 is

    g_H(ζ,1) = log |(ζ+1)/(ζ−1)|
             = (1/2)log(1+4x/|ζ−1|²).

Whenever x≤1/2, the inequality log(1+t)≤t gives g_H(ζ,1)≤8x. Inversion ζ↦1/ζ preserves H, fixes 1 and leaves this kernel invariant.

For (small), x²≤C₁ a and x|y|≤C₁ a. In particular x≤1/2 for small a and

    x(|y|+√a)≤(C₁+√C₁)a.

Let f_a(t)=a/(|t|+√a) for |t|≤2 and f_a(t)=0 otherwise. Define the positive harmonic Poisson integral on H,

    P_a(x+iy) = (1/π) ∫_R x f_a(t)/(x²+(t−y)²) dt.

For (small), |y|≤1 and x≤1/2, so the interval [y−x,y+x] lies in [−2,2] and has Poisson mass exactly 1/2. Consequently,

    P_a(x+iy) ≥ a/[2(|y|+x+√a)]
      ≥ a/[2(√C₁+1)(|y|+√a)]
      ≥ x/[2(√C₁+1)(C₁+√C₁)].

Choose A=16(√C₁+1)(C₁+√C₁). Then A P_a≥8x≥g_H on the small forbidden region. On the large forbidden region, inversion gives g_H≤8 Re(1/ζ)≤8C₁ a for small a. Therefore the single positive harmonic function

    h_a(ζ) = A P_a(ζ)+8C₁ a

majorizes g_H(ζ,1) at every ζ∈H mapping outside Ω.

Its value at the pole is small:

    P_a(1) = (1/π) ∫_[-2,2] a/[(|t|+√a)(1+t²)] dt
            ≤ (2a/π) log((2+√a)/√a)
            = O(a log(1/a)).

In particular h_a(1)=O(a log(1/a)). The logarithmic factor comes from integrating the localized forbidden width, rather than applying its largest value at every imaginary coordinate.

## 3. Green comparison in the actual component

Let g_U(ζ,1) be the positive Green function of U (normalized with logarithmic pole). Domain monotonicity gives g_U≤g_H. The function

    d(ζ)=g_H(ζ,1)−g_U(ζ,1)−h_a(ζ)

is harmonic on U, including across 1 by cancellation of the equal logarithmic singularities. At any finite boundary point in H the point maps outside Ω: otherwise a small connected neighborhood in the open preimage would meet U and belong to the same component, contradicting boundary membership. Since g_U≥0 and h_a is continuous on H, the limsup of d at such a boundary point is ≤0 by §2. At a boundary point on the imaginary axis, g_H→0 and h_a,g_U≥0; the same limsup inequality holds. At infinity g_H→0 uniformly as |ζ|→∞, so limsup d≤0 there as well.

It follows from the maximum principle that d≤0 on U. To avoid any boundary-regularity assumption, for any ε>0 the set {d≥ε} is compactly contained in U by the boundary limsup and infinity estimates, and if nonempty a positive maximum would be attained in the interior. The strong maximum principle and the boundary/infinity estimates rule this out. No extension of a Riemann map to ∂U has been used.

Evaluate at the removable singularity 1. The regular-part identity gives

    0≤log(2/r_U(1))=lim_(ζ→1)(g_H−g_U)≤h_a(1)
        =O(a log(1/a)),

since r_H(1)=2. Thus r_U(1)≥2 exp[−O(a log(1/a))]. The conformal image of U is a subdomain of Ω, so by conformal invariance and monotonicity,

    4B exp[−O(a log(1/a))] ≤ r_Ω(0) ≤ 4R_+.

Substitute B=R_-=b(1−C log L/L), a=π log(2)/L and the upper radial sandwich. This proves (1) uniformly on the stated interval. It also improves the cusp-centered diagonal penalty at levels s=u^β,t=u^α to

    K_(s,t)(1/4,1/4)=2 log(β/α)+O(log L/L),

for fixed 0<α<β, since t−s is negligible. The improvement concerns the cusp center only; the actual disks in CUSP_GROUND Theorem C continue to have loss log L+O(1).

## 4. Proof boundary

The only additional analytic inputs are the half-plane Poisson kernel, Green-function domain monotonicity and the harmonic maximum principle with a removable singularity; the explicit estimates above establish the required majorant on every possible boundary point of the actual component. The proof never supposes its boundary is a graph or is locally connected. The full shape of the complement inside the two forbidden regions is not used. No estimate for an arbitrary primitive or satellite cusp, H4 nest or universal marked-width coercivity is asserted. GPT-6.2 proof search and drafting; human referee and formal verification pending.

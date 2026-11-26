# Quantitative strengthening: explicit conformal subdomain at the cusp

Follow-up to [CUSP_KERNEL.md](CUSP_KERNEL.md). Same actual parameter domains and H4 scope. This is a rate for the conformal radius, not a claimed rate for all normalized conformal maps.

**Theorem.** On any fixed compact interval of α in (0,+∞), as L=log(1/u)→∞,

    r_(u^α)(1/4) = [4π²(log 2)²/(α² L²)] (1+O(L^(-2/3))).       (1)

The constants may depend on the α interval. The exponent 2/3 is a sufficient upper error bound; no optimal error exponent is claimed.

## 1. Uniform radial sandwich

Use a=π log(2)/L and b=α^(-2) as before. The error in CUSP_KERNEL (3) gives, uniformly for R in a compact positive interval,

    log(1/G(1/4+a² R)) = L/√R + O(log L).

Choose an absolute (for the selected α interval) C sufficiently large, and put

    R_- = b(1−C log L/L),     R_+ = b(1+C log L/L).

For large L these are positive. The mean-value theorem for (1±t)^(-1/2) gives strict inequalities log(1/G(1/4+a²R_-))>αL>log(1/G(1/4+a²R_+)). The margin is a positive multiple of C log L, uniformly since α stays bounded away from zero. The real majorant and monotonicity arguments of CUSP_KERNEL therefore give

    closed disk of radius R_- ⊂ Ω_(u,α) ⊂ C ∖ [R_+,+∞).

In particular r_Ω(0)≤4R_+ by conformal radius monotonicity. The disk alone would give only r_Ω(0)≥R_-, losing the factor four.

## 2. A quantitative cardioid-based inclusion lemma

For B>0, 0<δ≤1, 0<η<1, put r=(1−η)/(1+η) and

    φ_B(z)=4Bz/(1+z)²,   |z|<1.

This is the conformal map from the disk onto C ∖ [B,+∞) taking 0 to 0 with positive derivative 4B. We claim that if

    a < η√δ/(10√B),                                           (2)

then every w=φ_B(z), |z|≤r, either satisfies |w|<B(1+δ) or lies in the rescaled main cardioid, meaning that c=1/4+a²w has an attracting fixed point.

Proof: write ζ=(1−z)/(1+z)=x+iy. Then w=B(1−ζ²), x≥η, Re(1/ζ)=x/|ζ|²≥η, and |ζ|≤1/η. These follow from (1−|z|²)/|1±z|²≥(1−r)/(1+r). If |w|≥B(1+δ), then |ζ|²≥δ by the triangle inequality. For these nonzero w we show

    Re √(-w)/|w| ≥ η√δ/(10√B),                              (3)

with the root having positive real part.

If Re w≤0, the root has real part at least √(|w|/2), while |w|≤B(1+η^(-2))≤2B/η²; their quotient is at least η/(2√B), stronger than (3).

If Re w>0 then x²<1+y² and |1−ζ²|≥1. We must have |y|>x/3: otherwise x²<9/8, |ζ|²≤(10/9)x², and

    |1−ζ²|²−1 = |ζ|⁴−2(x²−y²)
      ≤ x²[(100/81)(9/8)−16/9] < 0,

a contradiction. Thus |y|≥|ζ|/√10. In particular y≠0, so w has nonzero imaginary part and the root is well-defined. Using the real part formula for a square root,

    Re √(-w)/|w|
      = |Im w|/[|w| √(2(|w|+Re w))]
      ≥ |Im w|/(2|w|^(3/2))
      ≥ x|y|/[√B (1+|ζ|²)^(3/2)].

If |ζ|≤1, the latter is at least η√δ/(√80√B) by |ζ|≥√δ. If |ζ|≥1, it is at least (x/|ζ|²)/(√80√B)≥η/(√80√B). Both imply (3). Condition (2) gives Re √(-w)>a|w|, equivalent to |1−2a√(-w)|<1, and proves the lemma using the exact fixed-point multiplier equation. In particular there is no hidden assumption of membership of positive real w in the Mandelbrot set.

## 3. Optimize the subdomain loss

Set δ=η=T a^(2/3), B=R_-/(1+δ), where T>0 is a fixed constant large enough that T^(3/2)>10√B for all sufficiently small a and all α in the given interval. Such T exists because B stays bounded above. Then (2) holds, and 0<δ=η<1 eventually. By the lemma, φ_B({|z|≤r}) is contained in the union of the radius-R_- disk and the rescaled main cardioid, hence in Ω_(u,α).

The conformal radius of φ_B(r D) at 0 is 4Br, by the map z↦φ_B(rz). Monotonicity now yields the explicit bounds

    4 R_- (1−η)/[(1+δ)(1+η)] ≤ r_Ω(0) ≤ 4 R_+.

Since log L/L=o(L^(-2/3)), a is a constant times L^(-1), and η=δ=O(L^(-2/3)), (1) follows upon multiplying by a². All inequalities are for the actual domain; no assumptions about its zero-level boundary or crosscuts.

## 4. What is and is not obtained

The elementary real escape-time error alone does not prove this conformal radius error: the essential additional bound is the explicit conformal subdomain inclusion using the complex attracting-fixed-point condition. Conversely a disk exclusion alone cannot identify the factor four. The two scales have been balanced only to prove a sufficient bound. It would be incorrect to infer a matching lower error or claim optimality.

This strengthens the cusp part of the archive's sharp-boundary note but does not furnish the uniform ground-control over a residual infinite renormalization nest required by H4. The local cusp estimate is proved at 1/4, not presumed at every primitive cusp. GPT-6.2 proof derivation and adversarial checking; no independent specialist or proof-kernel verification.

# Bounded additive error in the actual real parabolic transit

This strengthens the intermediate real estimate in [CUSP_KERNEL.md](CUSP_KERNEL.md). The leading π/h law is classical; we make the cancellation explicit because discarding the sign of every integration-step error loses a logarithm.

**Theorem.** For 0<h≤1/8, let N be the first iterate with f_(1/4+h²)^N(0)≥1 and J the first with f_(1/4+h²)^J(0)≥2. Then

    |N−π/h|≤120,    |J−π/h|≤124,

and with the same Green normalization,

    log(1/G(1/4+h²)) = π log(2)/h + O(1).                  (1)

Equivalently there are absolute constants 0<A≤B<∞ such that

    A exp[−π log(2)/h] ≤ G(1/4+h²) ≤ B exp[−π log(2)/h].

These are deliberately loose explicit iteration constants; no assertion is made that N−π/h converges as h→0 (the integer clock itself rules out such an unrestricted limit).

## Proof

Use y_j=f_c^j(0)−1/2 and d_j=y_j²+h². For j<N, −1/2≤y_j<1/2, d_j≤17/64, y_(j+1)=y_j+d_j. As before, y_N∈[1/2,49/64], Σ_(j<N)d_j=y_N−y₀≤81/64<13/10.

With t∈[0,1], define v_j(t)=2y_j t+d_j t². Direct substitution gives

    I_j = ∫_[y_j,y_(j+1)] dv/(v²+h²) = ∫_0^1 dt/(1+v_j(t)).

Since sqrt(d_j)<3/5, the Lipschitz-norm estimate from CUSP_KERNEL §2 gives 1+v_j(t)≥4/25. Moreover

    |v_j(t)|² ≤ (2|y_j|+d_j)²
                ≤ (2+sqrt(d_j))² d_j < 7d_j.

The exact identity (1+v)^(-1)=1−v+v²/(1+v) now implies

    |I_j−(1−y_j)| ≤ d_j/3 + (25/4)·7d_j < 50d_j.       (2)

The leading correction is signed. To sum it without an absolute-value loss, use

    d_(j+1)/d_j = 1+2y_j+d_j = (1+y_j)²+h² ≥ 1/4.

Put z=2y_j+d_j, so |z|²<7d_j. Taylor's theorem along the real segment from 0 to z bounds |log(1+z)−z|≤8z² because the second derivative has magnitude at most 16 there. Thus

    |log(d_(j+1)/d_j)−2y_j|≤57d_j.

This telescopes, giving

    |2 Σ_(j<N)y_j| ≤ |log(d_N/d₀)|+57 Σ_(j<N)d_j.

Here 1≤d_N/d₀<3 since d₀≥1/4, y_N≥1/2 and d_N≤(49/64)²+1/64<3/4. In particular |log(d_N/d₀)|<2. It follows that

    |Σ y_j| ≤ (2+57·13/10)/2.

Summing (2) and using |Σ I_j−π/h|≤4 from the arctangent formula in CUSP_KERNEL §2 gives

    |N−π/h| ≤ 50·13/10+(2+57·13/10)/2+4 < 120.

The J−N bound of four steps and the escape identity in CUSP_KERNEL prove the remaining assertions.

## Consequences and limits

Uniformly for R in compact positive intervals,

    log(1/G(1/4+a²R)) = L/√R+O(1),   a=π log(2)/L.

In [CUSP_RATE.md](CUSP_RATE.md) and [CUSP_HARMONIC_RATE.md](CUSP_HARMONIC_RATE.md) we may therefore replace the radial bracket by

    R_±=α^(-2)(1±C/L)

with C uniform on compact α intervals. The actual first real crossing R_u of G(1/4+a²R_u)=u^α differs from α^(-2) by O(1/L), not merely O(log L/L). This does not eliminate the harmonic barrier's logarithmic cost in the full complex conformal radius estimate; that would require a further analytic argument. It also does not say that the exact real crossing itself has a second-order limit.

The checker now tests the stronger bounded-error statement for the nine dyadic transits. The proof uses only the recurrence, integral substitution and Taylor's theorem. Classical parabolic transit attribution as in CUSP_KERNEL. GPT-6.2 mathematical derivation and coding; independent human review pending.

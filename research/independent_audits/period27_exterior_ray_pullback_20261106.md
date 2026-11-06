# Actual exterior 9-to-3 ray pullback: a sharp 64-sheet loss and normalized trace lift

**Date:** November 6, 2026. **Scope:** the *escaping basin* of the certified real period-27 quadratic, not its interior restrictive puzzle pieces. **Status:** mathematical theorem from the existing Lean-proved center certificate and the classical connected-Julia Böttcher theorem, with an independent exact integer/rational-angle regression. It is **not** a new proof of the classical Böttcher theorem or a KL prime-end/sheet construction. Every global MLC gate remains open.

## 1. Input and geometric setting

Let \(f(z)=z^2+c_*\), where \(c_*\) is the unique real parameter in the archive's exact \(2^{-128}\) bracket for which \(f^{27}(0)=0\) and the critical point has **minimal period 27**. The actual existence and exact-period statements are kernel-checked in [`Period27RealCenter.lean`](../../formalization/weighted/Period27RealCenter.lean), [`Period27RealUniqueness.lean`](../../formalization/weighted/Period27RealUniqueness.lean) and [`Period27RealExactPeriod.lean`](../../formalization/weighted/Period27RealExactPeriod.lean). The bracket lies inside \((-2,-1)\).

The unique finite critical point \(0\) has bounded orbit, so the filled Julia set \(K(f)\) is connected (classical connectedness criterion for quadratic polynomials). The normalized **dynamical-plane** Böttcher coordinate therefore extends to a conformal isomorphism

\[
\phi:\mathbb C\setminus K(f)\ \longrightarrow\ \{w:|w|>1\},
\qquad \phi(f(z))=\phi(z)^2,\qquad \phi(z)/z\to1
\quad(z\to\infty).
\]

This is the classical global extension theorem for a polynomial with connected filled Julia set; see J. Milnor, *Dynamics in One Complex Variable*, §§17–18 (external rays and the Böttcher conjugacy). It is not a claim that the Böttcher coordinate extends **injectively across the Julia boundary**.

Take the actual dynamical-plane target \(w_0=3\). For real \(x\ge3\) and \(-2<c_*<-1\),
\(f(x)\ge x^2-2>x\); hence \(3\) escapes. By real symmetry and normalization, \(R:=\phi(3)>1\) is real. Define the *escaping inverse-ray fiber*
\[
E_n=\{z\in\mathbb C:f^n(z)=3\}.
\]
All points of \(E_n\) are in the escaping basin and have an unambiguous Böttcher address. This is an **actual geometric fiber of the physical map** \(f\), not a formal phase clock or a set of prospective parameter rays.

## 2. Exterior inverse-ray theorem

**Theorem (physical 9-to-3 exterior address projection).** For every \(n\ge0\), \(E_n\) consists of exactly \(2^n\) distinct points
\[
z_{n,k}=\phi^{-1}\!\left(R^{1/2^n}e^{2\pi i k/2^n}\right),
\qquad 0\le k<2^n.
\]
For \(0\le m\le n\), the actual physical transition \(f^{n-m}:E_n\to E_m\) is the surjection
\[
\boxed{\quad f^{n-m}(z_{n,k})=z_{m,\,k\bmod 2^m}.\quad}
\]
Every fiber contains exactly \(2^{n-m}\) distinct external-ray points. In particular,
\[
E_9\xrightarrow[\;f^6\;]{\;64:1\;}E_3,
\qquad |E_9|=512,\quad |E_3|=8.
\]

**Proof.** Since \(3\) escapes, the normalized conformal Böttcher coordinate applies to every one of its iterated inverse images. The equation \(f^n(z)=3\) is therefore equivalent to \(\phi(z)^{2^n}=R\) in \(\{|w|>1\}\). The \(2^n\) complex roots shown above are pairwise distinct; the inverse conformal map supplies precisely the \(2^n\) distinct physical points. Raising their Böttcher coordinates to the \(2^{n-m}\)-th power sends the radius to \(R^{1/2^m}\) and the angle to \(k/2^m\pmod1\), proving the displayed formula. For each \(0\le b<2^m\), the preimages have indices
\(k=b+2^m a\), \(0\le a<2^{n-m}\), proving exact fiber size. \(\square\)

**First explicit physical collision.** The exterior rays at angles \(0\) and \(1/64=8/512\) meet the equipotential \(|\phi|=R^{1/512}\) at **different points** \(z_{9,0}\ne z_{9,8}\), but
\[
f^6(z_{9,0})=f^6(z_{9,8})=z_{3,0}.
\]
This is a genuine collision under a physical holomorphic map *at positive potential*. It is not a statement that the two rays land together on the Julia set.

## 3. Sharp inverse-branch memory and a sectorwise trace calculation

Every 9-level address has a unique split
\[
k=8a+b,\qquad 0\le a<64,\ 0\le b<8.
\]
The coarse 3-level address is \(b\). The six-bit branch tag \(a\) reconstructs the entire finer address, and **64 distinct tags are necessary** if a marking is to distinguish all 64 rays over each coarse point. In particular, no readout depending only on \(b\) can distinguish \(z_{9,0}\) from \(z_{9,8}\). This lower bound concerns this explicit escaping-ray address, **not** an arbitrary future observable and not Paper 1's infinite coset-valued sheet fiber.

There is also an exact *external-sector* analytic consequence. Choose any nondegenerate angular interval \(I\subset(0,1)\) and let
\[
T_a(\theta)=\frac{\theta+a}{64},\qquad I_a=T_a(I),\quad a=0,\dots,63.
\]
The \(I_a\) are disjoint angular sectors of the \(f^6\) inverse image. For \(u\) with finite homogeneous \(\dot H^{1/2}(I)\) seminorm, put \(u_a(t)=u(T_a^{-1}(t))\) on \(I_a\). Changing variables twice, the \(64^{-2}\) Jacobian factor cancels the \(64^{-2}\) distance-squared factor:
\[
[u_a]_{\dot H^{1/2}(I_a)}^2
=\int_{I_a}\!\!\int_{I_a}\frac{|u_a(t)-u_a(s)|^2}{|t-s|^2}\,dt\,ds
=[u]_{\dot H^{1/2}(I)}^2.
\]
Consequently, **on the declared direct sum of 64 separate sector trace spaces**,
\[
\sum_{a=0}^{63}\big[\tfrac18u_a\big]_{\dot H^{1/2}(I_a)}^2
=[u]_{\dot H^{1/2}(I)}^2.
\]
The amplitude \(1/8\) is sharp for this equal-weight, direct-sum isometry. This specializes the archive's earlier [sectorwise Böttcher trace isometry](../mlc_unified/dyadic_bottcher_external_trace_isometry_20260725.md) to an *actual* 9-to-3 physical exterior transition with all 64 branches accounted for. Constants are modded out in the homogeneous trace seminorm. **Cross-sector interaction energy is not included**; the result must not be quoted as an isometry of the global physical boundary/Dirichlet-to-Neumann form.

## 4. Exact reproducibility and first-failure ledger

Run from repository root:

```sh
python research/independent_audits/verify_period27_exterior_pullback.py
```

The standard-library-only program verifies the exact \(2^{-128}\) bracket is contained in \((-2,-1)\), enumerates all **512** finer dyadic angles, checks their \(64\)-fold angular forward images and all 64 inverse-lift formulas, checks each coarse fiber's multiplicity, exhibits the \(k=0,8\) collision, and checks the sectorwise Jacobian/normalization identities with rational arithmetic. It also regression-tests composable dyadic projections across small depths and sampled 27/9/3 indices. **It does not numerically trace Julia rays**. The proof of the physical identification with Böttcher ray coordinates is the classical theorem used in §1–2, not a claim made by the Python `assert`s.

| Interface | Outcome | What remains genuinely missing |
|---|---|---|
| Physical escaping-basin 9-to-3 inverse-ray projection | **Proved from classical Böttcher theory**; exact 64-to-1 map | No identification with KL restrictive-domain sheets |
| Exterior angular inverse branches and branchwise trace | **Explicit** 64 branches; exact sectorwise \(\dot H^{1/2}\) normalized direct-sum identity | Global trace cross-terms, core welding and width calibration |
| Characteristic **parameter** rays of the tuned hyperbolic component | **Not addressed** by these dynamical exterior rays | Identify component containing \(c_*\) and its root portrait |
| Julia-boundary landing, prime ends and same-germ KL accesses | **Open** | Identify actual landing pairs, side markings and sheet/coset functor |
| Paper 2 H3, \(K(f)=J(f)\) | **Fails** at this superattracting center | Requires different, nonattracting parameter for that source theorem |
| H1, H2, H3_COERCIVITY, H4, UPTCR, MLC | **Open / unchanged** | Global geometric and analytic interfaces |

**Important distinction:** the number \(64\) is the degree of the **global escaping-cover** map \(f^6:E_9\to E_3\), not the degree of any constructed KL marked-sheet projection. It gives a concrete test for any future claim that an exterior ray-lift code can be recovered from a coarse three-return address, but it does **not** prove that this is the correct puzzle, renormalization, sheet or prime-end functor in Papers 1–2. There is no claim of novelty for Böttcher's theorem or of a new proof of MLC.
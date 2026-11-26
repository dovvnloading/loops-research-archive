# Actual octal landing quotient, sharp trace contraction and a physical descent obstruction

**2026-11-26. Proposed written analytic strengthening of LANDING-SET and
ROOT-TRACE, on the existing selected real 3/9 Misiurewicz example only.**
Base: main at ee5d5222cf898ea07ceb56c588e1209d84173a29.
No change to a canonical ledger status is proposed.

The [exact reconstruction](README.md) and [measure/trace note](MEASURE_AND_TRACE.md)
identify the complete angular landing set and prove a physical Perron
energy contraction, but explicitly leave the binary-address formula for
the actual landing quotient unproved. Their §7 ordinary interval
energy counterexample uses an illustrative quotient, not the actual
landing map. We supply the missing identification and a counterexample
on the physical interval itself. Independently, the squared contraction
factor is optimal at every iterate, and the centered trace operator has
an explicitly determined spectrum. Neither result compares the trace
energy to canonical Wave width or parameter equilibrium energy.

## 1. Source-locked inputs and notation

Use precisely the objects of [reconstruction, §§1–4](README.md):
the actual degree-two polynomial-like return G=f^3 at the isolated
real parameter, its filled set K3, normalized continuous external-angle
landing map L, disjoint real interval cycle C0=K9, C1=G(C0),
C2=G²(C0), and H=G³ on C1. In particular:

* E1=L⁻¹(C1)=C, the full Cantor set with octal digits 3 and 4.
  T=8θ mod 1 preserves C and L T=H L.
* The actual real-symmetric normalized straightening of G to a real
  quadratic Q_G defines L via its inverse on the quadratic landing map.
  This is the input of [terminal first child, §7](../tip_kl_terminal_first_child_20261106.md)
  and [measure/trace, §6.3](MEASURE_AND_TRACE.md), not a new normalization
  of the angle. In particular L(1−θ)=L(θ) on C because its image is real.
* The actual interval homeomorphism h=h9∘G²:C1→[−2,2] conjugates H
  to q(y)=y²−2. See [interval-root theorem, §3](../tip_interval_root_and_marked_morphism_obstruction_20261106.md)
  and [reconstruction, §2](README.md). No affine or differentiable
  hypothesis on h is used.
* By [measure/trace, §6.1, (29c)](MEASURE_AND_TRACE.md), the normalized
  Hausdorff/Bernoulli probability μ_C on C pushes by L and h to the
  arcsine probability α(dy)=dy/(π√(4−y²)). This was proved using actual
  preimage multisets and Chebyshev moments, without assuming our formula.
* Use exactly the physical energy and Perron operator of
  [measure/trace, (19)–(29)](MEASURE_AND_TRACE.md); in particular their
  intertwining and two-child energy splitting. No new trace theorem
  is used.

Normalize the actual angles by x=7θ−3. Write

\[
 K=7\mathcal C-3=\{\sum_{k\ge1}7\epsilon_k8^{-k}:
                  \epsilon_k\in\{0,1\}\},\quad
 S_0x=x/8,\quad S_1x=(7+x)/8.
\]
Let μ be its fair Bernoulli probability and let
\[
 B(x)=\sum_{k\ge1}\epsilon_k 2^{-k},\qquad
 \ell(x)=h\bigl(L((x+3)/7)\bigr).
\]
The octal expansion in K is unique. The map B is continuous,
nondecreasing, onto [0,1], B_*μ is Lebesgue probability, and
B(1−x)=1−B(x). These facts follow by cylinder order and equal binary
cylinder masses; at a dyadic value the two expansions describe two
distinct K points, not an ambiguity in x. The induced T on K is the
left shift of its digits.

## 2. The actual quotient formula

**Order lemma.** The normalized landing map on the upper angular
half-circle, restricted to angles landing on a real interval, is
monotone in real order (possibly with the reverse orientation
after a real interval coordinate change).

Proof in the straightened quadratic plane: its normalized exterior
Böttcher inverse Ψ commutes with conjugation. This follows by uniqueness
of the normalized coordinate. Injectivity implies that a nonreal
exterior coordinate has nonreal image: otherwise its conjugate would
have the same image. The connected upper exterior half-annulus maps
into the upper half-plane, as its image is upper near infinity by
normalization. Choose a sufficiently large equipotential. Its upper
arc together with the real segment joining its endpoints bounds a Jordan domain in the
upper half-plane (symmetry, injectivity and the two real intersections).
For two distinct angles in (0,1/2) with distinct real landings, their
truncated rays are disjoint simple arcs from the upper equipotential
arc to the real segment; they lie in the domain except for endpoints.
They extend continuously to the stated landings by the input L.
The ordering of endpoints along the real segment must be opposite
to the ordering along the upper arc as one traverses the Jordan
boundary: otherwise the two arcs have alternating endpoints and
intersect by the Jordan separation theorem. Hence increasing angle
has nonincreasing real landing coordinate in the quadratic plane.
Equal landings cause no difficulty. Restrict to the real interval
in question and transport by the straightening and h; the restrictions
of the real-symmetric homeomorphism and h to intervals are monotone,
possibly reversing order. This proves the order lemma without an
assumption on the number of angles landing at one point. ∎

**Theorem 1 (actual formula, all angles).**
\[
 \boxed{h(L(\theta))=2\cos\bigl(2\pi B(7\theta-3)\bigr)
       \quad(\theta\in\mathcal C).} \tag{1}
\]

Proof. The left child S0K corresponds exactly to the angles of C
in (0,1/2). The order lemma makes ℓ on that child monotone. The
reflection x↦1−x exchanges the two children, preserves μ and satisfies
ℓ(1−x)=ℓ(x). Since ℓ(K)=[−2,2], the image of each child is the full
interval. Moreover the pushforward of the normalized probability on
each child is α: the two pushforwards agree by reflection, and their
average is α by the source input.

Thus g(x)=ℓ(S0x) is monotone, continuous, onto, and g_*μ=α.
Its endpoint g(0)=ℓ(0) is either −2 or 2 by monotonicity. The angle
3/7 is fixed by T, so g(0) is fixed by q. Only 2 is fixed among
the two endpoints. This fixes the orientation: g is nonincreasing.

For every x∈K, the arcsine law is nonatomic; hence the possible
plateau g⁻¹(g(x)) has μ-mass zero. Monotonicity therefore gives
\[
 \frac{1}{\pi}\arccos(g(x)/2)
   =\alpha([g(x),2])=\mu(\{y\in K:y\le x\})=B(x).
\]
The last equality follows from binary cylinder masses (including the
two addresses of a dyadic number, each a null singleton). It holds
also at the extreme endpoints. Consequently
g(x)=2cos(πB(x)). Since B(S0x)=B(x)/2, (1) follows on the left
child, and reflection gives it on the right. ∎

No polynomial-like ray was replaced by an ambient f-ray. The Jordan
argument took place in the actual normalized straightening defining
these G-rays; the proof transports its order, not its Euclidean metric.

### Complete fiber census and exact samples

For y∈[−2,2] let t=arccos(y/2)/(2π)∈[0,1/2]. Formula (1) says that
the entire angular fiber of h⁻¹(y) is
\[
 \{\theta\in\mathcal C:B(7\theta-3)=t
                            \ \text{or}\ 1-t\}. \tag{2}
\]
There are no additional G-angles outside C, since C=L⁻¹(C1) was
already established. Each nondyadic binary number in (0,1) has one
expansion, each interior dyadic has two, and 0 and 1 have one each
in the infinite 0/1 expansion convention. Therefore the actual fiber
cardinalities are
\[
 \boxed{\#L^{-1}(h^{-1}(y))=
 \begin{cases}
 2 & y=\pm2,\\
 4 & -2<y<2,\ t\text{ dyadic},\\
 2 & -2<y<2,\ t\text{ nondyadic}.
 \end{cases}} \tag{3}
\]
In the interior the four-access set is exactly the points eventually
mapping to the Chebyshev critical point 0: for t in (0,1/2),
dyadic means that some doubling iterate is 1/4 or 3/4, and the converse
is immediate. It is countable and dense. This is a complete fiber
classification, including irrational angles, not a finite ray census.

| Chebyshev coordinate y | Complete G-angle set |
|---|---|
| 2 | 3/7, 4/7 |
| −2 | 25/56, 31/56 |
| 0 | 193/448, 199/448, 249/448, 255/448 |

Here h⁻¹(−2)=G(0) by the conjugacy normalization and the actual orbit:
G²G(0)=G³(0)=x9 and h9(x9)=−2. The −2 row agrees with the independent
critical-value itinerary in [terminal first child, §7](../tip_kl_terminal_first_child_20261106.md).
All statements concern the same internal G angle coordinate.

## 3. A physical obstruction to ordinary interval energy descent

For clarity use the normalization of [measure/trace, (19)](MEASURE_AND_TRACE.md):
\[
 \mathcal E_K(u)=\iint_{K^2}\frac{|u(x)-u(y)|^2}{|x-y|^{2/3}}
                                 d\mu(x)d\mu(y),\quad
 \mathfrak E(v)=\mathcal E_{\mathcal C}(v\circ L).
\]
The energy is invariant under the affine normalization from C to K
when the actual Hausdorff measure is used as in that note. Thus
\(\mathfrak E(v)=\mathcal E_K(v(L((\cdot+3)/7)))\).
Set A=(4/3)^(2/3), the upper cross-kernel factor. Put
\(\nu=L_*\mu_{\mathcal C}\), the physical reference probability.

**Theorem 2.** There is a sequence of continuous physical observables
v_n:C1→[0,1] such that
\[
 \sup_n \mathfrak E(v_n)\le (7/2)A,\qquad
 \sup_n\|v_n\|_{L^2(\nu)}\le1,\qquad
 [v_n]_{H^{1/2}(C_1)}^2\longrightarrow\infty. \tag{4}
\]
The last seminorm uses ordinary physical real coordinates and Lebesgue
measure, with integrand |v(x)−v(y)|²/|x−y|². It is not the pullback
energy. In particular no bounded comparison into that ordinary
interval energy exists even on continuous fiber-compatible physical
data.

Proof. For n≥2 let ε_n=2^(-n) and let r_n:[0,1]→[0,1] be zero
up to 1/2−ε_n, one from 1/2+ε_n, and linear between. Define
\[
 v_n(z)=r_n\bigl(\pi^{-1}\arccos(h(z)/2)\bigr),\quad z\in C_1.
\]
These are continuous; their pullbacks are automatically constant on the
actual L-fibers. By (1), the rescaled pullback on the left child is
r_n∘B and on the right child is its reflected copy. The explicit
generic ramp estimate [measure/trace, (30)–(32)](MEASURE_AND_TRACE.md)
bounds each child energy by (3/2)A. Reflection preserves μ and the
kernel. The top-level cross term is at most A/2 because all child-to-child
distances are at least 3/4 and all values lie in [0,1].
The exact splitting (20)–(21) therefore gives (4)'s first bound.

Let z0=h⁻¹(0), strictly inside the physical interval. The transition
is contained in the physical interval with endpoints
h⁻¹(2cos(π(1/2±ε_n))). Both endpoints tend to z0. Write a_n>0 for
the maximum of their distances from z0. Choose δ>0 with
[z0−δ,z0+δ] contained in C1. For all sufficiently large n, the
two subintervals [z0−δ,z0−a_n] and [z0+a_n,z0+δ] have opposite
constant values 0 and 1 (in either orientation). Both orders of
these pairs give the lower bound
\[
 [v_n]^2_{H^{1/2}(C_1)}
 \ge 2\int_{a_n}^{\delta}\int_{a_n}^{\delta}
              \frac{ds\,dt}{(s+t)^2}
 =2\log\frac{(\delta+a_n)^2}{4\delta a_n}\ \longrightarrow\infty.
\]
This uses only continuity and injectivity of h, not an affine or
uniform distortion premise. Seminorms here are allowed to take
the value +∞; the divergence already rules out any finite uniform
upper comparison. ∎

In fact the physical step at z0 itself has finite pullback energy
as an L²(ν) class: by (1) it is constant almost everywhere on each
of the four length-two cylinders of K (endpoints have zero mass),
so within-cylinder energy vanishes and the separated cross kernels
are bounded. Its ordinary interval energy is infinite by the same
two-sided integral. The continuous sequence is stronger than a
mere discontinuous representative objection. This result disproves
the stated ordinary interval comparison, not all conceivable
physical Dirichlet/marked-width norms.

## 4. Sharp contraction and complete centered trace spectrum

The next result uses only the established physical Perron intertwining
and energy splitting; it does not need the order lemma for sharpness.
Use Q for the actual degree-two inverse average on C1 (counting
multiplicity), and Uv=v∘H for forward composition. They satisfy
QU=I, including the critical value. On K these lift to P (averaging
the two inverse branches) and composition by the left shift. In
particular the Bernoulli law is invariant under that shift, so ν
is H-invariant and Var_ν(U^j v)=Var_ν(v).

**Theorem 3.** For every n≥1,
\[
 \boxed{\sup_{\substack{\mathfrak E(v)>0\\\mathfrak E(v)<\infty}}
     \frac{\mathfrak E(Q^n v)}{\mathfrak E(v)}=2^{-n}.} \tag{5}
\]
The supremum is not attained. On the complex centered finite-energy
space with norm sqrt(\(\mathfrak E\)), the spectrum of Q is the closed
disk |λ|≤1/√2, and its point spectrum is the open disk |λ|<1/√2.

Proof. The upper bound of (5) is [measure/trace, (29)](MEASURE_AND_TRACE.md).
Write E_m=\(\mathfrak E(U^m v)\) for a fixed nonconstant finite-energy
v. At the first two children the lifted U^m v has identical rescaled
restriction, namely the lift of U^(m−1)v. By (20)–(21),
\[
 E_m=2E_{m-1}+X_m,\qquad
 0\le X_m\le A\operatorname{Var}_{\nu}(v).
 \tag{6}
\]
Indeed the cross-kernel is bounded above by A, and the factor 1/2
in (21) times the double integral of the squared difference of two
independent copies of the same function is its variance. This also
proves finiteness inductively. Thus
\[
 2^{-m}E_m=E_0+\sum_{j=1}^m2^{-j}X_j
 \ \uparrow\ L_v\in[E_0,E_0+A\operatorname{Var}_\nu(v)].
\]
Here L_v>0. By QU=I, for m≥n the ratio for U^m v is
E_(m−n)/E_m→2^(-n). Nonconstant v exists, for instance the physical
coordinate by [measure/trace, §6.3](MEASURE_AND_TRACE.md).
Strictness at every nonconstant input follows because the cross
term in (21) vanishes only if the two branch functions agree
almost everywhere with one common constant (the cross-kernel is
strictly positive). In that case the original function is constant
μ-almost everywhere. Thus for nonconstant v the first contraction
is strict, and further iterations cannot restore equality.

For the spectrum statement, use the complex mean-zero space
\(\mathscr H=\{v\in L^2(\nu):\int v\,d\nu=0,\ \mathfrak E(v)<\infty\}\).
The bound \(\mathfrak E(v)\ge2\|v\|_2^2\) for centered v follows from
the normalized K diameter 1. Completeness in the energy norm:
an energy-Cauchy sequence is L²-Cauchy and has a subsequence converging
almost everywhere, including its pullbacks; Fatou applied to the
energy of differences shows convergence in energy to the L²
limit. Polarization supplies the Hilbert inner product. U and Q
preserve this space, Q by contraction and U by (6), so both are
bounded. The Q operator norm is 1/√2 by (5).

Take v0=h, a nonzero centered finite-energy observable. It is
centered by the arcsine law; Qv0=0 because the two Chebyshev
preimages have opposite signs (the critical double preimage is 0).
For its finite energy, (1) gives the normalized lift 2cos(2πB(x)).
If the longest common octal prefix of x and y has length N,
then |B(x)−B(y)|≤2^(-N) while |x−y|≥(3/4)8^(-N).
Thus \(\mathcal E_K(B)\le A\), and the cosine is Lipschitz as a
function of B.

For every complex λ with |λ|<1/√2 the series
\[
 w_\lambda=\sum_{j\ge0}\lambda^j U^j v_0
\]
converges in \(\mathscr H\) by (6), which bounds
\(\|U^jv_0\|_{\mathscr H}\le
2^{j/2}\sqrt{\mathfrak E(v_0)+A\operatorname{Var}_\nu(v_0)}\).
Termwise application of Q gives Qw_λ=λw_λ, since Qv0=0
and QU=I. The vector is nonzero: bounded I−UQ sends this series
to v0. Thus the open disk lies in the point spectrum. Strict
contraction at nonconstant inputs excludes eigenvalues on its
boundary. Outside the closed disk the usual norm-convergent
Neumann series gives an inverse of λI−Q. Closedness of the
spectrum (openness of the resolvent set follows from the same
Neumann argument) supplies the boundary circle. This proves
the stated spectrum, on this energy norm and not on all of L². ∎

This shows that the previous factor 1/2 cannot be improved for
arbitrary finite-energy physical observables, even at the selected
single actual return. It is a statement about worst-case observables
that depend on n, not a lower decay estimate for every fixed observable.

## 5. Exact finite arithmetic cross-check (not proof of landing)

The following standalone standard-library Python snippet checks
(2) on dyadic levels 1 through 12, using only integer and Fraction
arithmetic. If t=p/2^n is interior, octval(p,n) interprets its n
binary digits as octal digits. The two binary expansions of t
give a terminating ε-word and a prefix p−1 followed by all ones.
The shift relation for folded fibers checks exact ×8 angular
semiconjugacy at these sample addresses. Run with Python 3:

~~~python
from fractions import Fraction as F

def octval(p, n):
    return sum(((p >> j) & 1)*8**j for j in range(n))

def angles(t):
    if t == 0:
        return {F(3, 7)}
    if t == 1:
        return {F(4, 7)}
    n = t.denominator.bit_length() - 1
    assert t.denominator == 2**n
    p = t.numerator
    return {F(3, 7)+F(octval(p,n),8**n),
            F(3, 7)+F(7*octval(p-1,n)+1,7*8**n)}

def folded(t):
    return angles(t) | angles(1-t)

assert folded(F(0)) == {F(3,7),F(4,7)}
assert folded(F(1,2)) == {F(25,56),F(31,56)}
assert folded(F(1,4)) == {F(193,448),F(199,448),F(249,448),F(255,448)}
count = 0
for n in range(1,13):
    for p in range(2**(n-1)+1):
        t = F(p,2**n)
        a = folded(t)
        assert len(a) == (2 if t in (0,F(1,2)) else 4)
        assert {1-x for x in a} == a
        assert {8*x % 1 for x in a} == folded((2*t) % 1)
        count += 1
print(count)
~~~

Observed output: 4107 (includes repetitions of reduced dyadics
across levels). The checks verify the stated sample formula and
its arithmetic, not the analytic identification, Jordan argument,
energy estimates or spectral proof. No full repository test suite
or Lean proof was run. This note is self-contained and has no new
standalone executable or external dependency.

## 6. Status, dependencies and research boundary

Target interfaces: LANDING-SET, ROOT-MEASURE, ROOT-TRACE in
[the physical bridge register](../../../formalization/PHYSICAL_BRIDGES.md).
They were already written; this proposed follow-up adds a precise
physical quotient and sharp/operator-theoretic information and a
negative result at the ordinary interval comparison. The first
unresolved analytic application is still a comparison with the actual
required marked width/physical response or parameter equilibrium
charge; that comparison must be independently specified and proved.
The counterexample says that substituting ordinary interval H^(1/2)
on the strength of the landing-pullback trace bound cannot work.

Credit the existing archive's physical reconstruction and trace proofs,
Douady–Hubbard (straightening, Chapter I §1 Theorem 1; real-equivariant
construction as located in terminal first child §7), and Jonsson (the
trace-space theorem cited in measure/trace §4, not newly applied here).
The new proof uses elementary Jordan separation, cylinder probabilities,
the existing arcsine identity and exact energy splitting. No new external
theorem-level dependency is proposed. We have not independently
re-audited the original straightening/landing source proofs or
recomputed source byte hashes.

The selected parameter and one fixed return are essential. No
uniform renormalization estimate, general immersion MARK theorem,
H1–H4, UPTCR, parameter local connectivity or MLC case is claimed.
No frozen ledger or central bridge registry was edited pending
independent mathematical review; the existing target rows remain
the authoritative statements.

AI disclosure: OpenAI ChatGPT GPT-6.2 used for repository inspection,
proof search, mathematical writing and exact finite arithmetic check.
No independent human specialist review, formal verification or
whole-repository CI verification has been performed.

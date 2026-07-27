# Off-critical cylinder degree obstruction at virtual scale two

Date: 2026-07-25
Status: proved local obstruction; not a proof of MLC. Original manuscript and original PDFs are unchanged.

## Statement

Let f(z) = z^2 + c be the fixed quadratic polynomial in the direct-decoration pullback package. Let P be the first-level Jordan base and let g = f^q.

For every finite off-critical address word w, let Q_w be the actual connected pullback cylinder constructed by the direct-decoration compactification. Then:

1. g^|w|: Q_w -> P is univalent.
2. Every composition of the corresponding finite cylinder maps has degree one.
3. Any proposed degree-two second-scale quadratic-like return whose entire orbit remains inside these off-critical cylinders is impossible.

Consequently, a genuine second-scale quadratic-like base must pass through a separately constructed critical/root transition. It cannot be selected from the address word or from the univalent partial shift alone.

## Proof

The direct-decoration package defines each one-symbol inverse branch phi_a: P -> Q_a as the actual univalent pullback component of P avoiding the propagated critical value. For a finite word w = a_1 ... a_m, Q_w is the actual connected pullback component obtained by composing these branches, and the forward map g^m is the inverse of that composition. A composition of univalent maps is univalent, so its degree is one.

Now suppose a proposed return F = f^r restricted to B has every one-step image inside the same off-critical cylinder chain and has no separately declared root transition. The chain rule gives

    deg(F) = product over j=0,...,r-1 of deg(f: f^j(B) -> f^(j+1)(B)).

Every factor is one because the chain avoids the unique critical point of f. Hence deg(F) = 1, contradicting the required quadratic-like degree two. Therefore a degree-two return requires an intermediate target whose pullback contains the critical value, equivalently a declared critical/root transition.

## Consequence for Xi_2

The outer compactification supplies actual data (Q_w, g^m) for finite addresses and connected end fibers. It does not supply the missing root transition. The first unresolved scale-two record therefore has the more precise form:

    X2 = (Q_w, g^m; B_2,xi, F_2,xi, root_transition, marked_naturality).

Here B_2,xi, the degree-two return F_2,xi, the root transition, and the marked naturality data remain undefined.

This is a strict improvement over treating the entire scale-two interface as unknown: the off-critical portion is proved and the missing work is localized to the critical/root transition and its compatible prime-end marking.

## Source boundary

The result uses only the local statements in virtual_cantor_pullback_compactification.md, especially the actual univalent cylinder construction and its partial shift, together with the quadratic chain rule. It does not use local connectivity, coercivity, rigidity, UPTCR, or MLC.


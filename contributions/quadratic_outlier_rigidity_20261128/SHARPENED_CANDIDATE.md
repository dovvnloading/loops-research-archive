# Sharpened candidate recorded before Lean coding

The earlier [candidate](CANDIDATE.md) proposed full classification of a globally continuous map. Before formalization, an independent algebraic argument found the following stronger parameter theorem. This is the theorem now selected for the MLC criterion; no full-map classification is needed or claimed by this version.

## Parameter theorem

Let $c,d\in\mathbb C$ and let $h:\mathbb C\to\mathbb C$ be any function. Suppose only that $x\mapsto h(x)$ is continuous as a map $\mathbb R\to\mathbb C$, and that for every complex $z$,
$$
h(z^2+c)=h(z)^2+d,\qquad
h(z^2+c+1)=h(z)^2+d+1.
$$
Then $d=c$ or $d=\overline c$.

There is no continuity assumption away from the real axis, and no injectivity, surjectivity, measurability away from that axis, or normalization assumption.

The actual Mandelbrot-fiber criterion is the same as in CANDIDATE.md with this weaker regularity requirement: if each $d$ in a connected fiber admits such an intertwining function, then the fiber is singleton and the actual Mandelbrot set has an open connected neighborhood basis at $c$.

## Exact proof to formalize

1. Surjectivity of $z\mapsto z^2+c$ gives $h(w+1)=h(w)+1$, hence covariance under every integer translation. The identities at $z=0,1$ give $h(0)=0$, so $h(c)=d$.

2. Let $r=p/q$ be rational with integers $p$ and nonzero positive integer $q$. The difference
$$
(r+q)^2-r^2=2p+q^2
$$
is an integer. Apply integer covariance both before and after the quadratic map:
$$
(h(r)+q)^2+d=h(r)^2+d+2p+q^2.
$$
Cancellation gives $h(r)=r$. Continuity on the real axis and rational density imply $h(x)=x$ for all real $x$.

3. For real $t\ge0$, apply the quadratic equation at $\sqrt t$, giving $h(c+t)=d+t$. For negative $t$, first add a sufficiently large integer and then use integer covariance. Thus this identity holds for every real $t$.

4. Applying the quadratic equation at $iy$ gives
$$
h(iy)^2=-y^2 \qquad (y\in\mathbb R).
$$
Write $c=a+ib$ and put $y=-b/2$. Then $(1+iy)^2+c=1-y^2+a$ is real. Evaluating the same quadratic equation there and using unit covariance gives
$$
a=d+2h(iy).
$$
Consequently
$$
(d-a)^2=4h(iy)^2=-b^2.
$$
The two roots are $d=a+ib$ and $d=a-ib$, proving the theorem.

5. In a connected parameter fiber, every point therefore lies in the two-point set $\{c,\overline c\}$. A preconnected subset of a finite Hausdorff set is a singleton. Compactness of the actual bounded-critical-orbit Mandelbrot set and the already proved classical monotone-quotient lemma give the promised neighborhood basis.

## The precise pattern and novelty boundary

The quadratic sends the real axis to the horizontal line through its critical value. The second, unit-shifted polynomial fixes rational arithmetic along the real axis. A point on the vertical axis is then chosen so its unit translate maps back onto the real axis. This crossing of the two images forces the parameter to agree up to conjugation. It does not use critical-orbit samples, mixed-orbit products, projective jets, or the archive's geometric towers.

The rational-fixing argument and continuity/density extension are classical supporting ideas. The proposed specific new statement is rigidity of the actual quadratic parameter under two exact intertwining equations with regularity on only one real line, together with the proved connected-fiber consequence. The fixed finite parameter identities are conclusions of global functional equations; no interpolation or sampling assumption is made.

The earlier classical screen still applies, and becomes sharper: Nakai's linking homeomorphism cannot be assumed when the function is not even required to be continuous away from the real axis. Full-semigroup automorphism theorems also do not supply the two-generator intertwiner. The real-valued $c=d=0$ functional-equation exercise is credited as an antecedent and is not being claimed as new. No checked source directly supplies this arbitrary-complex-parameter, one-line-regularity theorem. Priority remains subject to specialist review.

This addendum is committed before any new Lean source. The first candidate's full-map classification and square-root flow construction are not required for the retained parameter theorem and will not be presented as established by it.

---
ledger: MLC
result: partial
ai: OpenAI ChatGPT, GPT-6 Astra Pro
human_review: none
---

<a id="thurston-fiber-criterion-20261128"></a>

# Quarter-turn rigidity for the actual quadratic family

## Claim

Let $f_c(z)=z^2+c$. For arbitrary complex parameters $c,d$, suppose a
continuous injection $h:\mathbb C\to\mathbb C$ satisfies
$
h(z^2+c)=h(z)^2+d,\qquad h(iz)=ih(z)\qquad(z\in\mathbb C).
$
Then $c=d$. If $c\ne0$, then $h=\mathrm{id}$.

The proposed new ingredient is rigidity of **two specified generators**:
one quadratic and the fixed quarter-turn. There is no postcritical finiteness,
holomorphic or quasiconformal hypothesis on $h$, normalization at infinity,
or assumption that $h$ preserves the full polynomial semigroup.

The companion Lean result proves the following actual MLC implication. Define
$
M=\{c\in\mathbb C:\exists B\in\mathbb R\
                    \forall n\in\mathbb N,\ |f_c^n(0)|\le B\}.
$
Let $q:M\to Y$ be continuous and onto, with preconnected fibers, where $Y$
is Hausdorff and locally connected. Fix $c\in M$. Suppose that for every
$d\in M$ with $q(d)=q(c)$, there exists a continuous injection satisfying the
two displayed intertwining equations. Then
$
q^{-1}(q(c))=\{c\},
$
and every relative neighborhood $U$ of $c$ in $M$ contains a relatively
open connected set $V$ with $c\in V\subseteq U$.
This is local connectivity of the actual bounded-critical-orbit locus at $c$,
in the explicit connected-open-neighborhood-basis form.

Equivalently as an obstruction: every nontrivial such parameter fiber contains
a parameter for which simultaneous quadratic and quarter-turn intertwining
fails. The existence of the intertwiners is an explicit extra condition,
not a conclusion drawn from combinatorial equivalence.

The candidate was stated in [CANDIDATE.md](CANDIDATE.md) and committed before
the first formalization. This packet succeeds the negative screening recorded
in PR #274; it makes a different, concrete quadratic-family claim.

## Evidence

### Exact proof of the rigidity theorem

The quarter-turn relation gives $h(0)=0$ and $h(-z)=-h(z)$.
The quadratic relation at zero then gives $h(c)=d$.

Every complex number has a square root. Applying the quadratic relation to
$z$ and $iz$, and then writing $t=z^2$, gives
$
h(t+c)+h(-t+c)=2d.
$
Set $t=w+c$ and use oddness:
$
h(w+2c)=h(w)+2d.
$
Rotate this identity to obtain
$
h(w+2ic)=h(w)+2id.
$
Induction also gives
$h(w+2nc)=h(w)+2nd$ for every natural $n$, hence $h(2nc)=2nd$.

Now put
$
G(w)=h(2cw)-2dw.
$
The two translation identities give periods $1$ and $i$ for $G$, without
any division by $c$ and including the case $c=0$. Continuity bounds $G$ on
the compact unit square. Reducing real and imaginary coordinates modulo one
therefore gives a single bound for $G$ on the whole plane.

Evaluate this bounded function at $w_n=2cn^2+\tfrac12$. The exact identity
$2cw_n=(2nc)^2+c$ and the quadratic equation yield
$
G(w_n)=h((2nc)^2+c)-2d(2cn^2+\tfrac12)
     =(2nd)^2+d-4cdn^2-d
     =4n^2d(d-c).
$
A bounded sequence of constant multiples of $n^2$ has zero coefficient.
Thus $4d(d-c)=0$. If $d\ne0$, this gives $c=d$.
If $d=0$, injectivity and $h(c)=h(0)=0$ give $c=0=d$.
This proves the parameter statement for every $c,d\in\mathbb C$.

For the strengthening, assume $c\ne0$ and now $d=c$. The bound for $G$,
after rescaling the argument, bounds $g=h-\mathrm{id}$ on the whole plane.
For each $z$ and natural $n$, direct expansion gives
$
g((z+2nc)^2+c)-g(z^2+c)=4nc\,(h(z)-z).
$
The left side stays bounded as $n$ varies, so
$4c(h(z)-z)=0$. Since $c\ne0$, $h(z)=z$ for every $z$.

The bounded-periodic-function and bounded-polynomial-sequence observations are
classical supporting facts. The quadratic-specific step is the generation of
two independent translation laws from the two intertwining equations and their
use in the exact evaluation above.

### Lean statements and validation

The complete proof sources are:

- [QuadraticRotationRigidity.lean](../../formalization/weighted/QuadraticRotationRigidity.lean):
  `parameter_eq_of_quarter_turn_conjugacy` and
  `map_eq_id_of_quarter_turn_conjugacy`, with their algebraic and topological
  supporting lemmas.
- [QuadraticRotationMLC.lean](../../formalization/weighted/QuadraticRotationMLC.lean):
  the bounded-critical-orbit definition `mandelbrot`, its proved compactness,
  `fiber_eq_singleton_of_quarter_turn`,
  `nontrivial_fiber_obstructs_quarter_turn`, and
  `locallyConnectedAt_of_quarter_turn`.

The MLC theorem does not take parameter equality or a singleton-fiber assertion
as a hypothesis. It extracts a concrete map from `QuarterTurnFiber`, applies
the new quadratic rigidity theorem, proves fiber equality, and invokes the
classical compact-monotone-quotient topology theorem.

No local Lean executable is installed in this workspace. The repository's
existing Lean workflows are the compiler and proof-dependency judge.
**Current validation state: CI proof repair submitted; next build pending.**
The first weighted build reached the new rigidity module and reported one
rewrite failure when transporting the proved polynomial identity into the norm
bound. The next revision uses explicit equality congruence. The preceding
algebra and periodic-bound lemmas compiled. See [VALIDATION.md](VALIDATION.md)
for commit and run records.
The two modules are registered as default weighted targets and in both source
and public-theorem indexes. No workflow or audit rule is changed.

### Novelty pre-check: closest classical results

This is a qualified, source-based novelty assessment, not a claim that a finite
search certifies worldwide priority.

1. **Thurston rigidity for postcritically finite maps.** The classical
   characterization theorem treats postcritically finite branched coverings
   with the appropriate orbifold and obstruction conditions. The present
   statement allows arbitrary quadratic parameters, and its hypotheses are
   simultaneous topological intertwining of two concrete maps.
   Source: Douady and Hubbard, *A proof of Thurston's topological
   characterization of rational functions*, Acta Math. 171 (1993), 263–297,
   main characterization theorem.
   [DOI](https://doi.org/10.1007/BF02392534).

2. **Hybrid straightening uniqueness.** Douady and Hubbard,
   *On the dynamics of polynomial-like mappings*, Ann. Sci. ENS 18 (1985),
   287–343, Chapter I, section 1, straightening theorem, requires hybrid
   equivalence; a continuous injection is not such an equivalence.
   The current theorem supplies its own rigidity argument.
   [Primary text](https://pi.math.cornell.edu/~hubbard/PolyLikeMaps.pdf);
   [journal record](https://www.numdam.org/articles/10.24033/asens.1491/).

3. **Full polynomial-semigroup automorphisms.** Cabrera, Makienko and Plaumann,
   *Semigroup representations in holomorphic dynamics*, DCDS 33 (2013),
   1333–1346, Proposition 7 and Theorem 13, classify maps preserving entire
   polynomial or rational semigroups. The hypotheses here mention only the
   specified quadratic and quarter-turn. Showing that this finite pair already
   forces the necessary rigidity is the missing step; the full-semigroup
   theorem cannot simply be applied.
   [Primary text](https://arxiv.org/pdf/1009.3000);
   [DOI](https://doi.org/10.3934/dcds.2013.33.1333).

4. **Shcherbakov–Nakai germ rigidity.** Nakai, *Separatrices for non solvable
   dynamics on $\mathbb C,0$*, Ann. Inst. Fourier 44 (1994), 569–599,
   Theorem 4 and its restatement as Theorem 5.1, concerns nonsolvable
   pseudogroups of holomorphic diffeomorphism germs fixing a common point.
   For $c\ne0$, the quadratic and quarter-turn have no common fixed point,
   and the quadratic is branched at zero. Those hypotheses are not supplied.
   A new reduction to a suitable germ group would itself require proof.
   [Primary text](https://www.numdam.org/article/AIF_1994__44_2_569_0.pdf).

5. **Singleton fibers imply local connectivity.** This is classical supporting
   topology, not the novelty claim. Schleicher,
   *On Fibers and Local Connectivity of Mandelbrot and Multibrot Sets*,
   Proposition 3.5, states the relevant implication for classical parameter
   fibers. Our Lean wrapper uses the more explicitly stated compact-monotone
   quotient hypotheses in the archive's already proved topology module.
   [Primary text](https://arxiv.org/abs/math/9902155).

The earlier finite Thurston-trace candidate was rejected because the
quadratic parameter can already be recovered from a known finite spectral
formula; the present proof uses neither that trace nor its degeneration.
No direct instance of the two-generator statement was located in the archive
or the cited classical sources. Specialist review of priority remains open.

## Dependencies

### The archive's exact open hypothesis

The global open hypothesis between the archive's written reduction and MLC is
`UNIVERSAL_PROTECTED_TOWER_CLOSURE`, named **Universal Protected-Tower
Compactness and Rigidity (UPTCR)**. Its universal quantifiers precede the
parameter choice, and it requires, for every infinitely renormalizable
quadratic, a common tower satisfying six clauses: actual carriers, exact
analytic realization, finite response, backward transition, coercive
compactness, and rigidity with both singleton combinatorial fiber and connected
relative parameter neighborhoods.

The written conditional implication is
[mlc_closure_proposition.md](../../research/mlc_unified/mlc_closure_proposition.md),
section 7, Theorem 7.2. `ResearchGates.lean` formalizes an abstract interface
with explicit `TerminalBridge` and `ComplementTheorem` assumptions; it is
not a Lean proof of those analytic assumptions about the actual family.
The present result neither invokes UPTCR nor marks it solved.

### Formal dependencies of this packet

- `QuadraticRotationRigidity` imports Mathlib only.
- `QuadraticRotationMLC` imports that module, `QuadraticEscape`, and
  `QuadraticMonotoneFiberTopology`.
- The escape module is used only to establish that the bounded-critical-orbit
  Mandelbrot set is closed and compact. The criterion makes no assertion about
  potential density, sampling, or escape-rate estimates.
- The monotone-fiber topology module supplies a classical topology implication.
  The mixed-susceptibility module is not imported and none of its dynamical
  machinery is used.
- Baseline: `0678a66d0915f73214db7899c9591ebb56afb67b`.
- Target obligation: MLC; no status-record change is requested.

## Boundary

The theorem gives an exact additional-coordinate rigidity criterion and its
proved MLC implication. It does **not** prove that members of an unresolved
combinatorial fiber admit quarter-turn-compatible intertwiners. Ordinary
topological conjugacy, agreement of kneading data, or agreement of internal
addresses does not supply that compatibility in this packet.

After the rigidity theorem, the fiber condition is equivalent to a singleton
fiber: necessity follows by choosing the identity map on the diagonal.
Thus the new content is the two-generator rigidity theorem, not a claim that
this condition has already become easier to verify than fiber triviality.
There is currently no new unconditional parameter coverage.

The quotient $q$, its surjectivity, continuity, preconnected fibers, and its
Hausdorff locally connected target are explicit hypotheses. The canonical
pinched-disk quotient is not constructed or identified in Lean here.
Consequently the theorem can be applied to such a quotient only after those
identifications and hypotheses have been supplied.

The open research problem left by this criterion is to construct or obstruct
the extra quarter-turn compatibility on actual unresolved fibers by independent
dynamical information. The submitted Lean development proves the criterion and
the implication to a singleton fiber and actual local connectivity, subject to
the CI validation state above.

The conclusion $h=\mathrm{id}$ needs $c\ne0$. At $c=d=0$, continuous
injective radial power maps commute with both squaring and the quarter-turn,
so parameter rigidity persists but map rigidity fails. Surjectivity and
regularity stronger than continuity were not used.

The excluded archive constructions and excluded metric, sampling, arithmetic,
encounter, potential-density, projective-jet, and mixed-susceptibility routes
are not part of this argument.

## Attribution

Existing archive results and classical results retain their authorship.
The translation-lattice argument and Lean development in this packet were
produced with AI assistance: OpenAI ChatGPT, GPT-6 Astra Pro.
Human review: none. All contribution files follow the repository's CC0 terms.

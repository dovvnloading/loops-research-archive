# Marked collar calibration

## 1. Purpose and status

The finite-horizon construction produces qualitative locally saturated collars but
does not choose them with controlled width. This note identifies:

1. a two-boundary-component case where calibration is exact;
2. why that proof does not extend by simply filling or joining a disconnected marking;
3. the precise vector-valued one-stage theorem still required.

## 2. Exact two-continuum calibration

### Theorem 2.1 (connected-exterior calibration)

Let \(H,E\subset\widehat{\mathbb C}\) be disjoint nondegenerate continua, and assume
\[
  S=\widehat{\mathbb C}\setminus(H\cup E)
\]
is connected. Then \(S\) is a doubly connected Riemann surface. If
\[
  V=\widehat{\mathbb C}\setminus E,
\]
then \(V\) is a conformal disk containing \(H\) and
\[
  V\setminus H=S.
\]
Consequently the target inverse annular width is exactly the marked separating width:
\[
  W(V\setminus H)
  =
  \frac{1}{\operatorname{mod}
    \big(\widehat{\mathbb C}\setminus(H\cup E)\big)}.
\]

**Proof.** The complement of \(V\) is the connected set \(E\), so \(V\) is simply
connected. Its complement after removing \(H\) has exactly the two connected
components \(H\) and \(E\). Since \(S\) is connected, it is doubly connected. The
identity \(V\setminus H=S\) gives the modulus equality. \(\square\)

### Proposition 2.2 (Jordan-collar approximation)

Under the hypotheses of Theorem 2.1, there is an increasing exhaustion by Jordan disks
\[
  H\Subset B_1\Subset B_2\Subset\cdots\Subset V,
  \qquad
  \bigcup_m B_m=V,
\]
such that
\[
  \operatorname{mod}(B_m\setminus H)
  \nearrow
  \operatorname{mod}(V\setminus H)
\]
and hence
\[
  W(B_m\setminus H)\searrow W(V\setminus H).
\]
In particular, for every \(\varepsilon>0\), some Jordan target \(B_m\) satisfies
\[
  W(V\setminus H)
  \le W(B_m\setminus H)
  \le W(V\setminus H)+\varepsilon.
\]

**Proof.** A simply connected plane domain admits an exhaustion by relatively compact
Jordan domains containing any fixed compact subset. The annuli \(B_m\setminus H\)
increase to \(V\setminus H\). Continuity from below of extremal length, equivalently
kernel continuity of annular modulus, gives convergence of the moduli. Positive
reciprocals give the width statement. \(\square\)

### Corollary 2.3

In a one-stage virtual problem whose exterior marking can be represented by one
connected continuum \(E\) without changing the declared homotopy classes, the local
target collar can be calibrated with arbitrarily small additive width error.
Proposition 8.2 of `finite_horizon_inflation.md` then shows that subsequent inflation
does not increase that target inverse modulus.

## 3. Why connected-exterior reduction is not automatic

At a translation or virtual-molecule stage, the exterior marking generally consists of
many components carrying distinct access labels. Replacing them by a connected hull
can:

- cross a declared corridor and delete its curve family;
- merge distinct prime-end accesses;
- change whether a Wave separates the active core from a limb;
- alter the homotopy class transported by a selected inverse branch;
- hide marking cardinality that KKL retains explicitly.

Thus Theorem 2.1 is a recovery theorem, not permission to connect all exterior
obstacles. The no-faithful-bounded-quotient theorem in
`virtual_block_quotient.md` applies here.

### Adversarial test 3.1

Place two labeled obstacle components on opposite sides of a corridor joining the
active core to the outer boundary. Any connecting arc used to turn the obstacles into
one continuum must choose a side or cross the corridor. In the first case it changes a
prime-end access; in the second it destroys the corridor curve family. Therefore a
connected hull is harmless only after a homotopy/access audit, not by planar
connectedness alone.

## 4. Source comparison

KKL26 Section `sec:localization` defines localization by:

1. taking a universal cover of the ambient hyperbolic surface;
2. quotienting by the stabilizer of a lifted boundary curve;
3. cutting along that curve;
4. gluing the nontrivial component to the selected subsurface.

Its canonical \(\psi\)-ql renormalization localizes a small Julia set in the complement
of the rest of its cycle. This supplies the correct categorical surface. It does not
state a universal comparison between:

- a new virtual marked-condenser width;
- the width of the localized \(\psi\)-ql target;
- WAD/translation-corridor widths before localization.

Kahn's induced-map theorem begins only after the localized \(\psi\)-ql width has
already been bounded.

## 5. Required vector state

Let a one-stage marked complement split into an active piece and corridors
\(C_1,\ldots,C_r\). The state retained by the current architecture is
\[
  \mathscr D=
  \big(
    D^{\mathrm{act}},
    W^{\mathrm{std}}_1,\ldots,W^{\mathrm{std}}_r,
    \operatorname{val}(\mathcal O)
  \big).
\]
Raw \(r\) need not be bounded if distinct access labels are retained. The target is a
bounded family of interaction types modulo the accelerated translation action,
together with a relative bound for interactions that traverse a long corridor.

## 6. Marked Collar Calibration Lemma

### One-stage theorem (`OPEN`)

There are universal finite chart types and order-preserving positively homogeneous
forward transition maps \(\Psi_{ut}\) such that, for every selected virtual stage:

1. the full inverse itinerary and separated markings admit the locally saturated
   telescope of Theorem 10.2 in `finite_horizon_inflation.md`;
2. the collars can be chosen so that the localized/inflated state satisfies
   \[
     \mathscr D_{\mathrm{out}}
     \le \Psi_{ut}(\mathscr D_{\mathrm{in}})+\mathbf e;
   \]
3. \(\Psi_{ut}\) depends only on the active interaction type, not on period, corridor
   length, continued-fraction entry, or horizon;
4. every component of \(\mathbf e\) is either universally summable or at most a fixed
   fraction of active degeneration/entropy gain;
5. joining exterior components is allowed only when it preserves every declared
   access and curve-family homotopy class;
6. when the exterior marking is connected, \(\Psi_{ut}\) reduces to the scalar identity and
   \(\mathbf e\) can be made arbitrarily small, recovering Proposition 2.2.

A nonnegative matrix \(A_{ut}\) may replace \(\Psi_{ut}\) only after proving the
balance/bottleneck-chamber condition in `corridor_network_calibration.md`. Harmonic
series laws are not uniformly comparable to a fixed positive linear map.

This theorem is a **forward upper calibration only**. Item 6 shows that an individual
localization/chart step can be the identity, so it must not be required to contract by
itself. To feed the backward record argument, compose such steps with the dynamical
transition of a complete entropy-clock block and prove chart gauges \(L_t,L_u\) and a
uniform \(0<\mu<1\) for the grouped map \(\Psi_B\):
\[
  L_u(\Psi_B(x))\le\mu L_t(x),
\]
with the error controlled as in Lemma 5.4 of `master_transition.md`; alternatively,
one must independently construct a backward componentwise lower transition. Neither
direction reversal follows from the displayed upper estimate alone.

## 7. Proof route and falsification criterion

The most concrete candidate is to use the extremal metric of the marked condenser and
its critical graph:

1. thicken the finite critical graph into the active core;
2. identify maximal cylinder/rectangle components;
3. quotient only their interaction types under the declared translation action;
4. retain long labeled corridors and apply KKL's long-tail estimate;
5. compare the localized collars using overflow, series/parallel laws, and
   quasi-additivity.

This is a route, not a proof. It fails if one can construct a sequence of virtual
stages for which:

- the critical graph has unbounded active branching after translation equivalence; or
- every access-faithful collar loses a fixed positive fraction at each of unboundedly
  many stages, with no entropy charge.

Such a sequence would be an exact counterexample to the present state invariant and
would show which additional marking or energy component must be retained.

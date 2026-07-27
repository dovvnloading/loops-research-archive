# Finite-horizon inflation

## 1. Purpose and status

This note isolates the first open construction in the unified MLC program. It proves
three formal facts:

1. the exact stagewise forward-closure condition needed to define complement
   inclusions;
2. the relative-cover lifting criterion used by inflation;
3. a no-go theorem showing that topological inflation cannot supply a uniform width
   bound.

It also defines the finite-horizon category in which the remaining construction must
land. It does **not** prove that every virtual hull admits such an inflation.

## 2. Source-locked all-horizon model

DL25 defines a \(\psi^\bullet\)-ql Siegel map
\[
  F=(f,\iota):(U,\overline Z_U)\rightrightarrows
  (V,\overline Z)
\]
between conformal disks. The properties used here are:

1. \(f:U\to V\) is a degree-two branched cover with one critical point on
   \(\partial Z_U\);
2. \(\overline Z\) is \(\iota\)-proper and \(\iota\) identifies
   \(\overline Z_U\) homeomorphically with \(\overline Z\);
3. the local maps agree conformally near the Siegel core;
4. for
   \[
     K_{n,U}=f^{-1}(K_{n-1}),\qquad
     K_n=\iota(K_{n,U}),
   \]
   \(\iota:K_{n,U}\to K_n\) is a homeomorphism for every \(n\);
5. \(\iota\) is a covering embedding relative to \(K_1\);
6. every fiber-product iterate
   \(\iota^n:U^n\to V\) is a covering embedding relative to \(K_n\).

DL25 Proposition `prop:g:unwind` constructs this object by inflating a locally
saturated prerenormalization relative to a globally forward-invariant set
\(\Upsilon=f(\Upsilon)\) containing the postcritical set. The source explicitly notes
a possible multiple-component framework, but does not state or prove the virtual
finite-horizon theorem required here.

## 3. Finite-horizon category

### Definition 3.1 (depth-\(q\) \(\psi\)-ql datum)

Let \(q\ge1\). A **depth-\(q\) \(\psi\)-ql datum** is a pair
\[
  F=(f,\iota):(U,K_{1,U})\rightrightarrows(V,K_0)
\]
with the following data and axioms.

1. \(U,V\) are conformal disks, \(f:U\to V\) is a proper degree-two branched
   covering, and \(\iota:U\to V\) is a holomorphic immersion.
2. \(K_0\Subset V\) is compact, connected, and full. Define
   \[
     K_{n,U}=f^{-1}(K_{n-1}),\qquad
     K_n=\iota(K_{n,U})
   \]
   whenever the right side is defined, for \(1\le n\le q\).
3. For \(1\le n\le q\), the selected \(K_{n,U}\) is compact and
   \(\iota:K_{n,U}\to K_n\) is a homeomorphism.
4. \(\iota:U\to V\) is a covering embedding relative to \(K_1\).
5. The fiber products \(U^n\), \(1\le n\le q\), exist in the selected component
   convention, are conformal disks, and
   \(\iota^n:U^n\to V\) is a covering embedding relative to \(K_n\).

When a neutral theorem requires the local Siegel model, the corresponding
depth-\(q\) **\(\psi^\bullet\)-ql Siegel datum** additionally includes the local
conformal identification and rotation hypotheses from DL25. The finite-horizon
definition does not weaken those local analytic hypotheses.

The definition makes no assertion for \(n>q\).

### Lemma 3.2 (truncation)

Every genuine \(\psi\)-ql map satisfying the all-horizon axioms determines a
depth-\(q\) \(\psi\)-ql datum for every finite \(q\).

**Proof.** Retain the original surfaces and maps and restrict the universally
quantified iterated-core and covering-embedding axioms to \(1\le n\le q\).
\(\square\)

### Definition 3.3 (admissible finite-horizon use)

An argument is **admissible through depth \(q\)** only if every dynamical pullback it
uses:

1. has length at most \(q\);
2. stays in the selected fiber-product components;
3. lies in the complement on which the relevant \(\iota^n\) is a covering;
4. encounters no critical value outside the declared marking;
5. transports exactly the declared homotopy class of curves.

This is a use condition, not an automatic consequence of merely counting iterates.

## 4. Stage-dependent partial invariance

Let \(f:\widehat{\mathbb C}\to\widehat{\mathbb C}\) be continuous and let
\(\Upsilon_j,\Upsilon_{j+1}\) be closed sets.

### Lemma 4.1 (complement-inclusion criterion)

The identity on the sphere restricts to an inclusion
\[
 i_j:
 \widehat{\mathbb C}\setminus f^{-1}(\Upsilon_{j+1})
 \hookrightarrow
 \widehat{\mathbb C}\setminus\Upsilon_j
\]
if and only if
\[
 \Upsilon_j\subset f^{-1}(\Upsilon_{j+1}),
\]
equivalently,
\[
 f(\Upsilon_j)\subset\Upsilon_{j+1}.
\]

**Proof.** The complement inclusion is equivalent, after taking complements, to
\(\Upsilon_j\subset f^{-1}(\Upsilon_{j+1})\). The latter is the pointwise statement
\(f(x)\in\Upsilon_{j+1}\) for every \(x\in\Upsilon_j\). \(\square\)

### Corollary 4.2

A finite partial postcritical set does not by itself define even the topological
partial-cover correspondence. It must be forward closed through the declared horizon,
or be replaced by stage-dependent sets satisfying Lemma 4.1.

## 5. Relative-cover lifting

### Lemma 5.1 (based relative-cover lift)

Let \(i:(X',x')\to(X,x)\) be continuous between connected, locally path-connected,
semilocally simply connected spaces. Let
\[
 p':(\widetilde X',\widetilde x')\to(X',x'),
 \qquad
 p:(\widetilde X,\widetilde x)\to(X,x)
\]
be connected covers corresponding to subgroups
\[
 G'=p'_*\pi_1(\widetilde X',\widetilde x')
 \quad\text{and}\quad
 G=p_*\pi_1(\widetilde X,\widetilde x).
\]
There is a based lift
\[
 \widetilde i:\widetilde X'\to\widetilde X,
 \qquad
 p\circ\widetilde i=i\circ p',
\]
if and only if \(i_*(G')\subset G\).

**Proof.** Apply the standard lifting criterion to the map \(i\circ p'\). Its induced
fundamental-group image is \(i_*(G')\). \(\square\)

### Consequence for inflation

For stage \(j\), take
\[
 X'_j=\widehat{\mathbb C}\setminus f^{-1}(\Upsilon_{j+1}),
 \qquad
 X_j=\widehat{\mathbb C}\setminus\Upsilon_j.
\]
Lemma 4.1 supplies the underlying inclusion. Lemma 5.1 then supplies a map between the
chosen relative covers only after the subgroup condition is checked. Local saturation
is used in DL25 to align the annular core subgroups and to exclude unwanted lifts of
the core. Therefore fullness, complement inclusion, lift existence, and
\(\iota\)-properness are four distinct proof obligations.

### Warning 5.2

Lemma 5.1 proves existence of a lift. It does not prove that the lift is an immersion,
a covering embedding on the desired image, or proper relative to a selected core.
Those are analytic/local-saturation conditions in the virtual construction.

## 6. Mapping-telescope construction criterion

### Selected finite-horizon fiber-product assembly (`OPEN`)

Suppose a length-\(q\) virtual block provides stage correspondences
\[
 F_j=(f_j,\iota_j):
 (\mathcal U_j,H'_j)
 \rightrightarrows
 (\mathcal V_{j+1},H_{j+1}),
 \qquad
 \iota_j:\mathcal U_j\to\mathcal V_j,
\]
such that:

1. each \(f_j\) is proper and the product of the stage degrees is \(2\);
2. each \(\iota_j\) is a covering embedding relative to the selected core;
3. \(f_j^{-1}(H_{j+1})=H'_j=\iota_j^{-1}(H_j)\);
4. the component and marking labels match at successive stages;
5. every iterated lift needed through time \(q\) satisfies Definition 3.3;
6. a connected component of every successive fiber product is specified;
7. the selected component routing closes after \(q\) stages, all relevant base-change
   projections are proper with proved degrees, and no additional sheet enters;
8. the selected iterated components are conformal disks and retain the declared
   core/marking labels.

The target conclusion is that the selected fiber-product return has degree \(2\) and
retains the listed stagewise core-properness, covering-embedding, component-label, and
depth-\(q\) admissibility data. Items 6--8 are not consequences of Items 1--5 and have
not been proved for arbitrary virtual blocks.

This target does **not** automatically promote the telescope to the single-disk
depth-\(q\) \(\psi\)-ql datum of Definition 3.1, and this package does not silently use
an undefined “multiple-component depth-\(q\) \(\psi\)-ql” category. Such a promotion
would require a formal component-routing/fiber-product category and proofs that the
DL25/KKL theorems extend to it. The open construction may instead select one genuine
\(\psi\)-ql component or supply that categorical extension. In either route, it must
construct the stages from a virtual hull and verify the hypotheses uniformly.

## 7. Quantitative no-go theorem

### Theorem 7.1 (topology does not control width)

No bound for either the inverse fundamental-annulus modulus or the inverse
core-to-boundary modulus can depend only on the topological finite-horizon data of
Definition 3.1, even if the datum extends to a genuine ordinary quadratic-like map.

**Proof.** For \(R>1\), let
\[
 U_R=\mathbb D_R,\qquad
 V_R=\mathbb D_{R^2},\qquad
 f_R(z)=z^2,
\]
and let \(\iota_R:U_R\hookrightarrow V_R\) be inclusion. The filled set is
\(K=\overline{\mathbb D}\), and
\[
 f_R^{-1}(K)=K=\iota_R^{-1}(K).
\]
All maps have the same degree, filled-set topology, and dynamical marking. However,
\[
 \operatorname{mod}(V_R\setminus U_R)=\frac{\log R}{2\pi},
\qquad
 \operatorname{mod}(V_R\setminus K)=\frac{\log R}{\pi},
\]
so
\[
 \frac{1}{\operatorname{mod}(V_R\setminus U_R)}
 =\frac{2\pi}{\log R},
\qquad
 \frac{1}{\operatorname{mod}(V_R\setminus K)}
 =\frac{\pi}{\log R}.
\]
Both inverse widths tend to \(+\infty\) as \(R\downarrow1\) and to \(0\) as
\(R\to\infty\).
\(\square\)

### Corollary 7.2

Finite-horizon inflation and width calibration are independent obligations. Any valid
width theorem must use quantitative analytic hypotheses not present in the topological
correspondence—such as controlled localization, sectorial geometry, WAD estimates, or
an amortized comparison to a previously normalized checkpoint.

## 8. One-sided inflation monotonicity

The no-go theorem does not mean that the inflation operation itself necessarily
destroys a modulus bound.

### Lemma 8.1 (essential-annulus monotonicity)

Let \(K\) be a nondegenerate full continuum, and let \(B\subset V\) be conformal disks
containing \(K\). Then \(B\setminus K\) is an essential subannulus of \(V\setminus K\)
and
\[
  \operatorname{mod}(B\setminus K)
  \le
  \operatorname{mod}(V\setminus K).
\]
Equivalently, for inverse annular width,
\[
  W(V\setminus K)\le W(B\setminus K).
\]

**Proof.** The inclusion preserves the homotopy class of a loop separating \(K\) from
the outer boundary, so \(B\setminus K\) is an essential subannulus. Monotonicity of
conformal modulus for essential subannuli gives the first inequality; taking positive
reciprocals gives the second. \(\square\)

### Proposition 8.2 (inflation does not increase target inverse modulus)

In the inflation construction of DL25 Proposition `prop:g:unwind`, let \(B\) be the
local target disk, \(K\) its selected full core, and \(V\) the inflated target. Then
\[
  W(V\setminus K)\le W(B\setminus K).
\]

**Proof.** By construction, \(V\) is obtained by gluing a relative cover to \(B\) along
the punctured collar \(B\setminus K\); the copy of \(B\) embeds conformally in \(V\).
Apply Lemma 8.1. \(\square\)

### Limitation 8.3

Proposition 8.2 gives no bound until a local disk \(B\) with controlled
\(W(B\setminus K)\) has been constructed. It also does not compare WAD, peripheral,
vertical, or corridor families under a change of marking. Thus the unresolved analytic
step is a **controlled locally saturated collar theorem**, followed by marked-family
calibration—not an estimate for unrestricted path extension in isolation.

## 9. Revised open theorem

### Finite-Horizon Analytic Inflation Theorem (`OPEN`)

For every virtual block of stopping time \(q\), construct the stage data of
Proposition 6.1 and prove:

1. **forward closure:** the finite orbit/access markings satisfy Lemma 4.1 at every
   stage;
2. **local saturation:** the relative-cover subgroup and core-properness conditions
   hold at every selected component;
3. **orbit sufficiency:** every Wave, Wanderers, covering, and quasi-additivity
   pullback is admissible in the sense of Definition 3.3;
4. **quantitative localization:** for the active and corridor curve families,
   \[
     \mathscr D_{\mathrm{inflated}}
     \preceq A\,\mathscr D_{\mathrm{virtual}}+\mathbf e_B
   \]
   in the appropriate finite cone, where \(A\) belongs to a universal finite chart
   family;
5. **loss budget:** the error \(\mathbf e_B\) is either absolutely summable over the
   block or bounded by a fixed fraction of the active degeneration/accumulated
   entropy;
6. all constants are independent of \(q\), satellite periods, continued-fraction
   entries, corridor length, and transition depth.

Theorem 7.1 shows that Items 4–6 cannot be deduced from Items 1–3. Proposition 8.2
shows, however, that an upper bound for the local target inverse modulus survives
inflation with constant \(1\).

## 10. Conditional local-saturation construction

The following theorem closes the purely local topological construction when a full
inverse itinerary and separated finite-stage obstacles have already been supplied.

### Lemma 10.1 (shrinking a selected pullback component)

Let \(f\) be a quadratic polynomial, let \(K\) be a full continuum, and let \(H\) be a
component of \(f^{-1}(K)\). For every neighborhood \(N\) of \(H\), there is a
neighborhood \(O\) of \(K\) such that the component of \(f^{-1}(O)\) containing \(H\)
has closure in \(N\).

**Proof.** By the quadratic pullback dichotomy, \(f^{-1}(K)\) has one or two compact
components. Hence \(H\) is separated from the other component, if it exists. Choose a
bounded neighborhood \(N'\) with
\[
  H\Subset N'\Subset N
\]
and \(\partial N'\cap f^{-1}(K)=\varnothing\). The compact set
\(f(\partial N')\) is disjoint from \(K\). Choose \(O\) around \(K\) with
\(\overline O\cap f(\partial N')=\varnothing\), which is possible by compact
separation. The pullback component containing \(H\) cannot meet \(\partial N'\), and
its closure cannot acquire a point there because such a point would map into
\(\overline O\cap f(\partial N')\). Hence its closure lies in
\(N'\Subset N\). \(\square\)

### Theorem 10.2 (finite locally saturated telescope)

Let \(f(z)=z^2+c_0\), and let
\[
  H_0,H_1,\ldots,H_q
\]
be nondegenerate full continua such that \(H_j\) is a selected component of
\(f^{-1}(H_{j+1})\). For every \(j\), let \(E_j\) be a compact obstacle set disjoint
from \(H_j\). Assume exactly one target \(H_{j+1}\) contains the critical value \(c_0\);
at every other target stage treat \(c_0\) as an additional obstacle.

Then there are Jordan disks \(B_0,\ldots,B_q\) and, for \(0\le j<q\), selected
components \(A_j\) of \(f^{-1}(B_{j+1})\) such that:

1. \(H_j\Subset A_j\Subset B_j\) and
   \(\overline B_j\cap E_j=\varnothing\);
2. \(f:A_j\to B_{j+1}\) is proper;
3. exactly one stage map has degree two and every other stage map is conformal;
4. with \(\Upsilon_j=H_j\cup E_j\),
   \[
     \Upsilon_j\cap A_j=H_j;
   \]
5. \(\partial A_j\) and \(\partial B_j\) are homotopic relative to
   \(\Upsilon_j\).

Thus every stage is locally saturated in the finite, stage-dependent sense.

**Proof.** Every full plane continuum has a basis of Jordan neighborhoods: apply a
Riemann map from the exterior disk to its simply connected complement and use
equipotentials \(|z|=r>1\). Since \(E_j\) is compact and disjoint from \(H_j\), these
neighborhoods may be chosen with closures disjoint from \(E_j\) and, on noncritical
target stages, from \(c_0\).

Choose control neighborhoods \(C_j\) of \(H_j\) inductively. Start with a Jordan
neighborhood \(C_0\) avoiding \(E_0\). Given \(C_j\), Lemma 10.1 supplies a sufficiently
small Jordan neighborhood \(C_{j+1}\) of \(H_{j+1}\), avoiding its obstacles, whose
selected pullback component has closure in \(C_j\).

Choose \(B_q\Subset C_q\). Define \(A_{q-1}\) as the selected component of
\(f^{-1}(B_q)\). It has closure in \(C_{q-1}\). Choose a Jordan disk
\[
  \overline A_{q-1}\Subset B_{q-1}\Subset C_{q-1}.
\]
Continue backward. At each step, \(B_j\subset C_j\) implies that the selected pullback
component \(A_{j-1}\) has closure in \(C_{j-1}\), so the construction continues through
the finite horizon.

The boundary of every \(B_{j+1}\) avoids the critical value. Therefore its selected
preimage component is a Jordan disk and the restriction to it is proper. It has degree
two exactly when \(B_{j+1}\) contains \(c_0\), which by construction occurs exactly at
the declared critical target.

Finally, \(A_j\Subset B_j\Subset C_j\), and \(C_j\) avoids \(E_j\). The closed annulus
\(\overline B_j\setminus A_j\) contains no point of
\(\Upsilon_j=H_j\cup E_j\). Its two boundary curves are therefore homotopic relative to
\(\Upsilon_j\), and \(\Upsilon_j\cap A_j=H_j\). \(\square\)

### Limitation 10.3

Theorem 10.2 is not yet the virtual-hull construction:

- the virtual program must prove that its proposed stage hulls form the required full
  inverse itinerary;
- all omitted orbit/access data used later must form separated compact obstacle sets;
- forward closure from Lemma 4.1 must still be checked;
- the arbitrary Jordan collars supplied by the theorem have no uniform modulus or WAD
  calibration.

The theorem removes local topological saturation as an independent mystery once those
hypotheses are available. It leaves the quantitative choice of collars open.

## 11. Next proof target

The next nonformal step is a **marked collar calibration lemma for one selected
stage**:

> Starting from a full virtual hull, a forward-closed finite marking, and a specified
> one-critical-step pullback, choose the locally saturated source and target annuli of
> Theorem 10.2 so that the active/corridor curve families before and after
> relative-cover inflation are quantitatively comparable.

Proposition 8.2 controls ordinary target inverse modulus after inflation, but not the
choice of the local collar and not marked families. The proof must expose which width
is lost in that choice. Only after a one-stage estimate is proved can its errors be
tested for summability over an unbounded block.

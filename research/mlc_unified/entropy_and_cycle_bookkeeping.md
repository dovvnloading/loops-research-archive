# Discounted entropy errors and chart-cycle audit

## 1. Purpose and status

This note proves the abstract bookkeeping required before a positive-entropy block can
absorb localization or chart-change errors. It also records a necessary cycle
condition for any common expanding chart gauge.

The results are elementary but exact. They do not prove that KKL Value errors satisfy
the required discounted bound; that remains an analytic obligation.

## 2. Exact iteration formula

Let
\[
  v_{j+1}\le e^{-\epsilon_j}v_j+\eta_j,
  \qquad
  v_j\ge0,
  \qquad
  \epsilon_j,\eta_j\ge0,
  \qquad
  0\le j<m.
\tag{2.1}
\]
Write
\[
  E=\sum_{j=0}^{m-1}\epsilon_j,
  \qquad
  w_j=
  \exp\left(
    -\sum_{k=j+1}^{m-1}\epsilon_k
  \right).
\tag{2.2}
\]

### Lemma 2.1 (discounted Duhamel formula)

Every sequence satisfying (2.1) obeys
\[
  v_m
  \le
  e^{-E}v_0+
  \sum_{j=0}^{m-1}w_j\eta_j.
\tag{2.3}
\]

**Proof.** Induct on \(m\). For the last step, multiply the formula through time
\(m-1\) by \(e^{-\epsilon_{m-1}}\), add \(\eta_{m-1}\), and observe that this inserts
the last factor in every earlier weight. \(\square\)

The position of an error matters: late errors receive less discount than early ones.
Therefore a raw unweighted error sum is not the natural entropy quantity.

## 3. Sufficient entropy charge

### Theorem 3.1 (discounted absorption)

Assume, for some \(0\le\theta<1\) and \(C\ge0\),
\[
  \sum_{j=0}^{m-1}w_j\eta_j
  \le
  \theta(1-e^{-E})v_0+C.
\tag{3.1}
\]
Then
\[
  v_m
  \le
  \left[
    1-(1-\theta)(1-e^{-E})
  \right]v_0+C.
\tag{3.2}
\]
If \(E\ge E_*>0\), the coefficient of \(v_0\) is at most
\[
  \mu_*=
  \theta+(1-\theta)e^{-E_*}
  <1.
\tag{3.3}
\]

**Proof.** Substitute (3.1) into (2.3) and collect the coefficient of \(v_0\):
\[
e^{-E}+\theta(1-e^{-E})
=1-(1-\theta)(1-e^{-E}).
\]
This coefficient decreases with \(E\), giving (3.3). \(\square\)

Thus a positive-entropy block has a uniform affine contraction in the large-Value
regime only after its errors are bounded in the same calibrated Value coordinate and
with the discount appearing in (3.1). More precisely, (3.2) gives strict decrease
whenever
\[
  v_0>\frac{C}{1-\mu_*}.
\tag{3.4}
\]
The constants \(\theta,C,E_*\) must be block-independent.

### Lemma 3.2 (local entropy budget)

The identity
\[
  \sum_{j=0}^{m-1}
  w_j(1-e^{-\epsilon_j})
  =
  1-e^{-E}
\tag{3.5}
\]
holds. Consequently, the local estimates
\[
  \eta_j
  \le
  \theta(1-e^{-\epsilon_j})v_0+\tau_j,
  \qquad
  \tau_j\ge0,
  \qquad
  \sum_jw_j\tau_j\le C,
\tag{3.6}
\]
imply (3.1).

**Proof.** Since
\[
w_j(1-e^{-\epsilon_j})
=
e^{-\sum_{k=j+1}^{m-1}\epsilon_k}
-
e^{-\sum_{k=j}^{m-1}\epsilon_k},
\]
the sum telescopes. Multiply (3.5) by \(\theta v_0\) and add the discounted remainder
bound. \(\square\)

Equation (3.6) is only one sufficient mechanism. A different local potential is
acceptable if its discounted contribution telescopes to a universal endpoint term.

## 4. No-go for qualitative entropy payment

### Proposition 4.1

The lower bound \(\sum_j\epsilon_j\ge E_*>0\) alone does not control the error in
(2.1), even when every \(\eta_j=1\).

**Proof.** Set \(v_0=0\). For a block of length \(m\), take equality in (2.1) with
\[
  \epsilon_j=\frac{E_*}{m},
  \qquad
  \eta_j=1.
\]
Then \(E=E_*\), while every \(w_j\ge e^{-E_*}\). Hence
\[
  v_m=\sum_jw_j\eta_j\ge me^{-E_*}\to\infty.
\]
\(\square\)

Accordingly, "charge the excess to entropy" is not a proof statement unless it is
replaced by (3.1), a verified local criterion such as (3.6), or an equivalent
telescoping estimate.

## 5. Conversion gate

The corridor charge \(4S+C_{\rm net}\kappa\) is measured in WAD/extremal-width units.
The errors \(\eta_j\) in (2.1) are measured in the calibrated Value coordinate. Passing
from the former to the latter requires a proved comparison: for example, uniformly
bounded eigenweight ratios, an error-stable common homogeneous gauge, or a response
form whose terminal normalization is fixed.

Fixed terminal normalization is not sufficient if port compression merges distinct
WAD coordinates with different KKL coefficients. Theorem 7.1 of
`bc1_finite_port_response.md` gives an exact family with fixed total weight and fixed
response but varying Value. The conversion gate must therefore also require
Value-faithful ports, coefficient comparability inside every merged class, or the
retained Value-moment vector \(\mathbf V_B\).

Without that comparison, inserting \(4S+C_{\rm net}\kappa\) into (3.1) is a
coordinate/normalization mismatch.

## 6. Directed chart cycles

Let charts be vertices of a directed graph. An edge \(e:s\to t\) carries an
order-preserving positively homogeneous map
\[
  \Phi_e:\mathcal C_s\to\mathcal C_t
\]
between nonnegative state cones. Only dynamically admissible transition edges and
cycles are considered, and every successive image must lie in the declared domain of
the next edge.

### Proposition 6.1 (cycle obstruction)

Suppose nontrivial chart gauges
\[
  L_t:\mathcal C_t\to[0,\infty)
\]
and a constant \(\lambda>1\) satisfy
\[
  L_t(\Phi_e(x))\ge\lambda L_s(x)
\tag{6.1}
\]
for every edge \(e:s\to t\) and every state in its declared domain. For a directed
cycle \(e_i:t_{i-1}\to t_i\), \(t_k=t_0\), define
\[
  \Phi_\gamma
  =
  \Phi_{e_k}\circ\cdots\circ\Phi_{e_1}.
\]
Then
\[
  L_{t_0}(\Phi_\gamma(x))\ge\lambda^kL_{t_0}(x).
\tag{6.2}
\]
In particular, if
\[
  \Phi_\gamma(x)=a x,
  \qquad
  L_{t_0}(x)>0,
\]
then positive homogeneity forces \(a\ge\lambda^k\). A fixed state, or any periodic ray
with \(a\le1\), is an obstruction.

**Proof.** Apply (6.1) successively along the admissible cycle. If
\(\Phi_\gamma(x)=ax\), positive homogeneity and (6.2) give
\(aL_{t_0}(x)\ge\lambda^kL_{t_0}(x)\). \(\square\)

There is a dual obstruction for the forward-upper interface. If an edge
\(e:s\to t\) carries \(\Psi_e\) and a common gauge satisfies
\[
  L_t(\Psi_e(x))\le\mu L_s(x),
  \qquad 0<\mu<1,
\tag{6.3}
\]
then every admissible \(k\)-cycle satisfies
\[
  L_{t_0}(\Psi_\gamma(x))\le\mu^kL_{t_0}(x).
\tag{6.4}
\]
Hence a periodic ray \(\Psi_\gamma(x)=ax\) with \(L_{t_0}(x)>0\) requires
\(a\le\mu^k\); in particular, an identity cycle also rules out a strict forward
contraction. The proof is the same iteration with the inequalities reversed.

For example, a pure coordinate change and its inverse compose to the identity. Such
changes should not be required to expand separately; group each with the dynamical
step that supplies expansion or contraction before applying the cycle test.

### Audit requirement

Every admissible primitive/neutral/virtual dynamical cycle must therefore be checked
as a composition. Edgewise comparison constants do not establish a common expanding
or contracting Lyapunov calibration.

Proposition 6.1 concerns the leading homogeneous maps. With additive errors, a neutral
cycle may satisfy an affine estimate below a bounded threshold. A full audit must
compose the cycle errors and prove expansion above \(D_*\), or prove that the relative
cycle error is smaller than the expansion margin.

## 7. Open analytic theorem

For each entropy-clock block, prove:

1. a recurrence of the form (2.1) in one calibrated state;
2. the discounted charge (3.1) with universal \(\theta<1\) and \(C\);
3. a source-licensed conversion from corridor, neutral, and localization errors into
   the \(\eta_j\) units;
4. chart gauges satisfying either the backward edgewise expansion inequality or the
   forward edgewise contraction inequality on every admissible dynamical transition,
   after auditing every admissible cycle composition; or a block grouping on which
   such gauges and error estimates hold.

Items 1--3 give the abstract affine entropy contraction once \(E\ge E_*\). Item 4 is a
separate necessary compatibility gate for the backward Lyapunov state; the cycle audit
alone does not construct the gauges.

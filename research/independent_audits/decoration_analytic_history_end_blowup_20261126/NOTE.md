# Analytic histories and ordered external accesses in direct-decoration end blowups

**Base:** e894b7af96659859908ddd75d7c8f4d5d4a88d84 (main, 2026-11-26).
**Target:** VIRTUAL_END_BLOWUP_REALIZATION (open), with DIRECT_DECORATION_END_PRIME_END_COFINALITY and VIRTUAL_DISCONNECTED_MARKING_TRANSFER. Proposed partial analytic construction and an actual quadratic obstruction to uniqueness in a specified normalization. No ledger promotion.

The exact target asks for an analytic rescaled or nontrivial-projection-fiber end space carrying the authorized normalized root pair, protected accesses, obstacles, sheets, critical chronology, shift/fixed-iterate actions, relative covers, proper/end-proper intervals and complete-horizon final-root naturality. We construct the analytic affine-normalized inverse-cylinder history space and its fixed-iterate and child inclusion actions. On the selected actual 3/9 tip we construct the exact additional ordered external-sector mark, and show that the analytic shape fiber at **every** end has cardinality continuum in the closure of finite cylinders; there is even one nested address attaining every shape and both sector phases as subsequential limits. This refutes the stronger claim that one forward address (even with its two prime ends) determines a unique or finite menu of limiting marked affine geometries. It does not refute the actual ledger, which permits nontrivial fibers.

The general limit-geometry/scenery mechanism is classical: see T. Bedford and A. Fisher, *Ratio geometry, rigidity and the scenery process for hyperbolic Cantor sets*, ETDS 17 (1997), 531–564, DOI 10.1017/S0143385797079194, arXiv:math/9405217; H. Araújo and C. G. Moreira, *Stable intersections of conformal Cantor sets*, ETDS 43 (2023), 1–49, DOI 10.1017/etds.2021.97, arXiv:1910.03715. The direct-decoration application, common analytic neighborhood, periodic-multiplier separation at this source-realized parameter, and joint sector-phase compactification below are the proposed archive contribution. We give the needed proofs directly rather than import a general scenery theorem or claim global priority. Only the published abstracts and bibliographic information of these two background papers were checked, not every prior result.

## 1. Source hypotheses and notation

Use the same physical closed Jordan pieces P, Q_L, Q_R as DIRECT_DECORATION_PULLBACK_COMPACTIFICATION (virtual_cantor_pullback_compactification.md §3) and the merged direct-decoration end cofinality audit (research/independent_audits/decoration_end_cofinality_20261126/NOTE.md §§1–4). Let f(z)=z²+c, K(f)=J(f) connected, g=f^q, q>1, and phi_a:P→Q_a⊂P the actual closed-piece inverse homeomorphism, conformal in the interior. The siblings are disjoint compact pieces. Word composition is phi_w=phi_{a1}∘…∘phi_{am}, Q_w=phi_w(P); empty word is the identity. Each puzzle boundary in J consists of finitely many iterated preimages of the dividing fixed point alpha, the remaining boundary being exterior rays/equipotential arcs.

There is a terminal primitive cycle K_i=f^i(K_0), i=0,…,r−1, r>1, pairwise disjoint full compact connected little filled Julia sets, with 0∈K_0 and proper degree-two return; the first critical step has degree two, all remaining steps degree one. Each phase return is noninjective on K_i, by degree two on K_0 and transport along the degree-one tail (see merged cofinality audit Lemma 1). Set C=∪K_i. It is forward invariant, contains every finite critical value of every f^N, and avoids alpha and its preimages: if alpha belonged to C its fixedness would contradict disjointness of the cycle, and forward invariance excludes preimages. Thus C misses the boundary of every Q_w including P. Fix z_0∈int P, and use complex affine normalization at z_0, not arbitrary conformal reparametrization.

For reference, the merged cofinality audit proves that every physical end E_omega=∩ Q_{omega|m} is singleton and uniform full-cylinder shrinking holds at a fixed parameter. We supply the stronger common-neighborhood normality statement needed below independently. The concurrent #162 is a separate quantitative strengthening; our proof does not assume it.

## 2. One common analytic neighborhood for all words

**Lemma 1.** There is a bounded simply connected open W containing P, on which every phi_w extends univalently, with one uniform bound on the images. For every compact L⊂W, diam phi_w(L)→0 uniformly as |w|→∞.

Proof. If |v|=r, Q_v is disjoint from C. Indeed any K_i meeting Q_v lies entirely in its interior because K_i is connected and misses its boundary. But g^r=f^{qr} is injective on Q_v and noninjective on K_i, since f^r maps K_i onto itself noninjectively. Contradiction. (This is the critical-cycle exclusion from the merged cofinality audit.)

For every word w the derivative of g^{|w|} is nonzero on Q_w. It is nonzero in int Q_w by univalence; a boundary critical point would map to ∂P, but its critical value lies in C, which misses ∂P. The polynomial is injective on Q_w. It is therefore injective in some open neighborhood of Q_w: otherwise pairs of distinct points arbitrarily close to Q_w with the same image have subsequences converging to x,y∈Q_w; injectivity gives x=y and local univalence at x contradicts those pairs. Consequently phi_w extends across P for each fixed word.

For each of the finitely many words v of length r choose a bounded simply connected V_v⊃Q_v, disjoint from C. Such neighborhoods exist for the full compact Jordan disk Q_v, for example by exterior uniformization and sufficiently close equipotential curves, or the Jordan Schoenflies theorem. Shrink the just-constructed neighborhood of Q_v on which g^r is injective so that it lies in V_v. Its image is an open neighborhood O_v of P and the extension phi_v maps O_v into V_v.

For every prefix u the polynomial g^{|u|} is an unbranched covering of V_v (all its finite critical values lie in C), so the inverse on Q_v determined by phi_u extends holomorphically and univalently over V_v. Choose the sheet using one point of Q_v. The agreement on all of Q_v follows by connectedness and local inverse uniqueness; denote the extension h_{u,v}. Then h_{u,v}∘phi_v extends phi_{uv} on O_v. Choose one bounded simply connected W containing P compactly, with closure in the intersection of all O_v and the finitely many neighborhoods for shorter words. The same Jordan-neighborhood argument gives W. Every word now extends on W. All long-word images are uniformly bounded by a polynomial escape radius containing all V_v: the inverse of a point in V_v cannot lie outside that radius. The finitely many short words are bounded after the choice of compactly contained W.

Suppose the shrinking claim fails on a compact L⊂W. There is a sequence |w_j|→∞ with diam phi_{w_j}(L) bounded below. By Montel a subsequence tends locally uniformly to h. If h is nonconstant, choose a small disk in W on which h is injective and use Rouché on its boundary to get a fixed nonempty open disk contained in the images of all sufficiently late maps. Its points have bounded g^{|w_j|}-images for arbitrarily large |w_j| (in the chosen disk in W). Thus none can escape, putting that open disk in K(f), which has empty interior. This is impossible. Hence h is constant; locally uniform convergence on L contradicts the lower diameter bound. Uniformity follows by this subsequence contradiction. ∎

In particular P is a compact subset of W, so every E_omega is a singleton e_omega; omega↦e_omega is continuous and injective by disjoint siblings. This proof establishes qualitative shrinking on a common open neighborhood (on its compact subsets), not a uniform-in-parameter rate.

## 3. Normalized affine charts and suffix stability

Choose a bounded connected open V with P⊂V and closure(V)⊂W (e.g. another Jordan neighborhood). Set

\[
 S_w(z)=\frac{\phi_w(z)-\phi_w(z_0)}{\phi'_w(z_0)},\qquad z\in W.
\]

Every S_w is univalent and normalized by S_w(z_0)=0, S'_w(z_0)=1. The Koebe growth theorem after uniformizing W at z_0 implies a bound M on sup_{closure(V)}|S_w| uniform in all w.

**Lemma 2 (uniform suffix estimate).** There are eps_k→0 such that for every prefix u, every word w with |w|≥k,

\[
 \|S_{uw}-S_w\|_{C(\overline V)}\le \epsilon_k .
\]

Proof. For long w, z_w=phi_w(z_0) is in one of the depth-r cylinders, uniformly away from C by Lemma 1's finite exclusion. Fix delta>0 so every disk D(z_w,delta) misses C. Lemma 1 gives B_k=sup_{|w|≥k}diam phi_w(closure V)→0. For large k, B_k≤delta/4. The sheet of the inverse of g^{|u|} sending z_w to phi_{uw}(z_0) is holomorphic univalent on D(z_w,delta), by the same covering argument; write it h. On V, phi_{uw}=h∘phi_w by local equality at z_0 and the identity theorem. For the normalized univalent map
\[
 U(\xi)=[h(z_w+\delta\xi)-h(z_w)]/[\delta h'(z_w)]
\]
on the unit disk, U(0)=0, U'(0)=1, and the Koebe growth theorem bounds |U|≤2 at |xi|=1/2. Cauchy's coefficient estimate gives |U(xi)−xi|≤16|xi|² for |xi|≤1/4 (sum the geometric series from degree 2). Chain rule and this bound give
\[
 |S_{uw}(z)-S_w(z)|
 \le 16 |S_w(z)|\,|\phi_w(z)-z_w|/\delta
 \le 16 M B_k/\delta.
\]
This is independent of u. Take eps_k=16MB_k/delta for sufficiently large k, and 2M for other k. ∎

Let Omega_- be the compact space of left-infinite histories eta=(…,a_2,a_1). Let eta[k]=a_k…a_1 be its length-k suffix. Lemma 2 implies S_{eta[k]} is uniformly Cauchy on closure V. Its limit H_eta is holomorphic univalent on V by locally uniform convergence and the normalized derivative (the usual Hurwitz alternative for univalent maps). It is continuous on closure V, with H_eta(z_0)=0 and H'_eta(z_0)=1. Two histories agreeing on their last k letters have charts within 2 eps_k in sup norm. Hence eta↦H_eta is continuous; the shape space
\[
 \mathcal H=\{H_\eta:\eta\in\Omega_-\}\subset C(\overline V)
\]
is compact. It may identify different histories; no injectivity of eta↦H_eta is claimed.

Appending a letter a on the right defines a continuous map T_a on H, given on int P by
\[
 T_a(H)(z)=
 \frac{H(\phi_a(z))-H(\phi_a(z_0))}
 {H'(\phi_a(z_0))\phi'_a(z_0)} .
\tag{1}
\]
Indeed the same identity holds for finite words, and uniform convergence and Cauchy estimates give (1) with H=H_eta and T_a(H_eta)=H_{eta a}. The expression on int P determines the unique extension in H by the identity theorem. This avoids requiring phi_a(V)⊂V. Continuity on H follows either from the continuous quotient map from compact Omega_- or by compactness and the identity (1). T_a is injective: equality of two outputs gives affine equality of the input functions on the open phi_a(int P), then on V; normalizations force equality. Every suffix w of length k yields the compact set of shapes T_w(H) for histories ending in w (composition of the T maps in chronological append order). It has diameter at most 2 eps_k, by Lemma 2.

For a fixed forward address omega and its prefixes w_m, fill the left side of each word w_m with infinitely many L's to form eta_m. Lemma 2 gives ||S_{w_m}−H_{eta_m}||≤eps_m. Consequently the exact cluster set of S_{w_m} is the image under H of the cluster set of eta_m. Forward prefix convergence does not imply backward-history convergence.

## 4. Nondegeneracy on the archive's actual 3/9 tip

Use the actual real nonattracting tip c_* isolated in the cofinality audit §5 and period27_misiurewicz_tip_ray_access_20261106.md Theorem A:
\[
 c_*\in (N/2^{128},(N+1)/2^{128}),\quad
 N=-607918036626757496169199575185708826140.
\]
The earlier source locks certify this is a Misiurewicz map of exact critical preperiod 10 and eventual period 9 with K=J, and realize the first ambient direct-decoration q=2,n=1 separator with dividing fixed point alpha, other vertex alpha'=-alpha, and actual terminal primitive period-three cycle. In particular the real segment [alpha,alpha'] lies in P; the inverse branches are the two outer real solutions with negative intermediate f-value. These are the explicit hypotheses and actual pieces of §5 of the merged cofinality audit, not a polynomial chosen because a numerical drawing looks similar. We use z_0=0∈int P.

Writing g=f² and using the negative intermediate square-root branch, on the real interval P∩R the branches are
\[
 \phi_L(t)=-\sqrt{-\sqrt{t-c_*}-c_*},
 \qquad \phi_R(t)=-\phi_L(t).
\]
This follows by continuity from t=alpha, where the two roots are alpha and -alpha and the intermediate value is alpha. No square-root sign can switch along the real interval since these maps are univalent and the relevant critical values are avoided on these inverse sheets; the positive radicands can also be seen from the displayed c and vertex bounds. For the particular points below, substitution and the selected root signs suffice.

**Proposition 3.** H_{…LL}≠H_{…RR}.

Assume equality H. By (1) applied to both constant histories, H simultaneously conjugates phi_L and phi_R to affine maps A_L,A_R, respectively, with slopes lambda_L, lambda_R≠0. The derivative identity extends to points of P, including the boundary vertices, since all maps are holomorphic on neighborhoods and H' is nonzero on V. At the branch fixed points, lambda_L=1/g'(alpha) and lambda_R=1/g'(b), where
\[
 \alpha=(1-\sqrt{1-4c_*})/2,\qquad b=(-1+\sqrt{-3-4c_*})/2.
\]
Here alpha=phi_L(alpha); b>0 satisfies b²+b+c_*+1=0, so f(b)=−b−1<0 and g(b)=b, hence b=phi_R(b). Direct differentiation gives g'(z)=4z(z²+c_*), so
\[
 g'(\alpha)=4\alpha^2,\quad g'(b)=4(c_*+1).
\]
For a mixed orbit x=phi_L(y), y=phi_R(x) we would similarly have
\[
 g'(x)g'(y)=g'(\alpha)g'(b).
\tag{2}
\]
This is because the derivative of phi_L∘phi_R at x is lambda_L lambda_R by conjugacy, and is also 1/(g'(x)g'(y)) by the chain rule and inverse identities.

The exact isolator implies −1.786511<c_*<−1.786510. Uniform rational interval arithmetic for this entire wider bracket gives:

* alpha∈(−0.928,−0.926), b∈(0.518,0.519) by endpoint signs of z²−z+c and z²+z+c+1.
* g²(t)−t is positive at t=−0.427, negative at t=−0.426. IVT gives x∈(−0.427,−0.426) with g²(x)=x. Its image y=g(x) is in (0.786,0.790). Both are strictly between alpha and −alpha, with f(x),f(y)<0, and x<0<y. Thus the inverse formulas identify x=phi_L(y), y=phi_R(x), not just an unlabelled algebraic periodic orbit.
* The products are enclosed in disjoint open rational intervals:
\[
 -10.84<16\alpha^2(c_*+1)<-10.79,\qquad
 -10.11<g'(x)g'(y)<-10.00 .
\]
The second interval is computed directly using x∈[−.427,−.426], y∈g([−.427,−.426]), with outward interval operations. No approximate orbit or multiplier is used.

This contradicts (2). ∎

An explicit marker-level consequence: H_L and H_R are not affine-related, since both are normalized. Let e_p=phi_p(alpha) for finite p. These are actual pre-alpha attachments, dense in the end Cantor set by cylinder shrinking. In particular they have an accumulation point inside V. If all of their affine ratios with the two fixed anchor points alpha,−alpha agreed for H_L and H_R, then by the identity theorem the charts would be affine-related. Therefore there exists a third actual pre-alpha attachment for which the ratio differs:
\[
 \frac{H_L(e_p)-H_L(\alpha)}{H_L(-\alpha)-H_L(\alpha)}
 \ne
 \frac{H_R(e_p)-H_R(\alpha)}{H_R(-\alpha)-H_R(\alpha)}.
\tag{3}
\]
The proof does not identify the shortest separating word; existence is exact. This is genuine relative geometry of actual attachment marks, rather than merely a discrepancy in an arbitrary derivative normalization.

**Corollary 4.** At this parameter H is a nonempty perfect compact metric space of cardinality continuum. For any H_eta and any k, the set of shapes with suffix eta[k] contains H_eta, has diameter at most 2 eps_k, and has at least two elements by Proposition 3 and injectivity of T_w. No point is isolated. Compactness and the elementary perfect-set theorem give the asserted cardinality.

A forward infinite word containing every finite word arbitrarily far along it has the entire H as its cluster set of normalized charts. For any eta, choose increasingly late prefixes ending in eta[k]; Lemma 2 approximates H_eta with error tending to zero. The reverse inclusion follows from compactness and the left-padding estimate in §3. Thus one *nested* sequence of actual cylinders converges physically to a singleton but has continuum many normalized subsequential charts. The assertion concerns parametrized affine shapes (with actual marks), not shapes modulo all conformal equivalences.

## 5. Analytic nontrivial-fiber compactification and exact child maps

Let X_+ be the compact space of finite and right-infinite words with finite words isolated (realize finite words by padding with a terminal symbol). Take the graph closure of w↦(w,S_w) in X_+×C(closure V). It is compact: bounded word lengths give a finite set, while words of lengths tending to infinity are at distance eps_|w| from the compact H in the shape coordinate. Its boundary is exactly Omega_+×H. For any omega and eta, w_k=(omega|k) eta[k] approaches omega with S_{w_k}→H_eta; conversely all boundary shape coordinates are in H. This is the minimal Hausdorff graph closure for these two observables, not a claim of minimality for every possible end realization.

Over a graph state gamma=(w,S_w) or (omega,H), put F_gamma=S_w or H and take the compact fiber F_gamma(P) with analytic neighborhood F_gamma(V). The compact total space of fibers is homeomorphic to the graph closure times P by (gamma,z)↦(gamma,F_gamma(z)); compactness, continuity of evaluation and injectivity prove this. The projection to the physical plane is
\[
 \pi(\gamma,F_\gamma(z))=
 \begin{cases}
 \phi_w(z)& \gamma\text{ finite},\\
 e_\omega&\gamma\text{ infinite}.
 \end{cases}
\]
It is continuous: any finite word tending to omega eventually extends each prefix of omega and hence its image lies in shrinking physical cylinders, independently of z. The fiber over an infinite address is nontrivial, and its projection is constant, as required by END_BLOWUP_PROJECTION_NO_GO. There is no claim this is an embedded Jordan domain in the original plane.

Deleting the initial symbol a of a nonempty finite word av sends (av,S_{av}) to (v,S_v) with z unchanged. It extends continuously at ends to (omega,H)↦(shift omega,H), since ||S_{av}−S_v||≤eps_|v|. This intertwines the actual fixed iterate g with pi. Fixed powers follow by composition wherever defined (finite words shorter than that power are outside the partial domain). In the rescaled coordinates the actual finite shift is S_v∘S_{av}^{−1}; the limiting shift is identity on the H coordinate. The root transition is separately typed; no shift through the empty word is asserted.

Appending a on the right is (w,S_w)↦(wa,S_{wa}), and at ends (omega,H)↦(omega,T_a H). It is continuous by (1), compactness, and derivative convergence. The natural child inclusion from the appended fiber into the parent fiber is the **exact affine map**
\[
 \zeta\longmapsto F_\gamma(\phi_a(z_0))+
        F_\gamma'(\phi_a(z_0))\phi_a'(z_0)\,\zeta .
\tag{4}
\]
For finite states it follows by expanding the two affine normalizations; for end states it follows from (1). In source coordinate z it sends z to phi_a(z), hence it is genuinely an inclusion of the transported child piece. The coefficients depend continuously on the state. It intertwines pi with the finite physical child inclusion and its constant infinite projection. Initial-symbol deletion commutes with appending/child inclusion wherever the partial actions are both defined. At the root the deletion is undefined. These are actual inverse-map identities, not a guessed symbolic diagram.

Given an independently authorized root pair F:A→B with closure(A),closure(B)⊂int P, each analytic chart transports the pair to F_gamma∘F∘F_gamma^{-1} on the transported domains. The retimed source-coordinate pair can alternatively retain the target B in the original root coordinate, as in NORMALIZED_RETIMED_GERM_CONSTANCY; do not identify these two target conventions. For any fixed compact labelled root sets/obstacles in P, the maps transport their exact incidence, preserve their conformal marking, and the distances between images of any two fixed disjoint compact sets have a strictly positive minimum over the compact chart space. Indeed the distance is continuous in the uniform norm and positive for each univalent chart. This is only for objects already specified in P and transported by the same chart. It does not authorize an otherwise missing root portrait or prove avoidance of additional ambient obstacles, relative covers or the entire Wave marking.

## 6. The independent two-sector phase at the actual tip

At c_* the merged cofinality audit §5 gives J_+=[1/6,1/3], J_-=[2/3,5/6]. The two actual affine angular lifts of the L branch preserve the sector with lift integers k_+=1,k_−=2; the R branch swaps with k_+=3,k_−=0, in the inverse map theta↦(theta+k)/4. These are the actual landed rays, not independently assigned symbolic marks. Each word has one closed arc in each of the two sectors, lengths 1/(6·4^{|w|}), nested along forward prefixes. Every end omega therefore has exactly two distinct angular limits theta_+(omega),theta_−(omega)=1−theta_+(omega), both with impression e_omega; both are included even at endpoints by the prior cofinality proof.

Label the original root sectors before pullback, not merely the unordered footprint. The destination of root sector j (j=0 for +, j=1 for −) under phi_w is sector j XOR p(w), where p(w)=#R in w mod 2. This follows by composing the two actual permutations. Hence as a sequence of words tends to omega and p(w) is fixed at p, the limiting angle attached to root label j is theta_{j XOR p}(omega). Convergence of the angular arc to that angle is uniform: any word with the same initial k symbols has its relevant destination arc in the length-1/(6·4^k) upper or lower arc of that prefix. The two angles remain separated by circular distance at least 1/3. The phase is observable in the ordered pair, not in the unordered footprint.

**Theorem 5 (joint affine geometry and ordered-sector graph).** At this actual tip the graph closure of w↦(w,S_w,p(w)) has boundary exactly
\[
 \Omega_+\times\mathcal H\times\{0,1\}.
\tag{5}
\]
Indeed for any omega,eta,p, use words w_k=(omega|k) b_k eta[k], choosing a single middle letter b_k=L or R to attain the desired total parity p. Prefix and suffix convergence are unaffected; Lemma 2 proves shape convergence, and parity is exact. Conversely compactness and the previous arguments put all boundary states in the displayed product. Thus past normalized geometry and ordered access phase are independent observable coordinates over each forward end. In particular fixing both the physical point and the ordered sector phase still leaves continuum many marked affine geometries. Formula (5) uses H, the actual quotient of backward histories, not a claim of injectivity of the history map.

The two actions in §5 extend on this graph with deletion of the first symbol toggling p exactly when that symbol is R, and right append toggling p exactly when the appended symbol is R. This agrees with actual sector permutation/forward angular multiplication by four under deletion. On end states it retains the ordered pair of ambient external prime ends and their one-sided endpoint conventions from the cofinality audit. The normalized charts carry the original fixed labelled root arcs; their physical external angular traces have the limiting sector angles just described. No identification of the global Böttcher prime-end circle with a newly uniformized virtual-carrier relative cover is made.

Moreover there is a single nested address omega for which the shape-and-phase cluster set is all H×{0,1}. Enumerate all pairs (finite word s,p) infinitely often. Starting with the empty word, at each stage append one parity-adjusting letter and then s, making the completed prefix end in s and have parity p. The resulting infinite word has arbitrarily late prefixes of every prescribed suffix and parity. For any eta,p, take successively late prefixes ending in eta[k] with parity p. Lemma 2 proves convergence to H_eta and the angular order is fixed. Compactness gives the reverse inclusion. Thus even selecting either ordered sector assignment, a single physically shrinking nested sequence can have continuum many different normalized chart limits.

A compact Hausdorff end realization retaining the finite-word observables (forward address, normalized chart, ordered sectors), with a dense image of finite states and their continuous extensions, maps onto this graph closure. In particular it cannot have only finitely many states over each end: by (5) each forward fiber maps onto H×{0,1}. This obstruction is specifically to retention of the stated observables. Arbitrary conformal reparametrization, as in the retimed root-coordinate identity, removes the affine shape distinction and is not excluded; a proof that all relevant observables factor through that coarser quotient is a separate task.

## 7. Arithmetic diagnostic (standalone, exact)

The following Python 3.13.5 standard-library regression was executed locally and passed. The inequalities are exact Fractions on closed rational intervals. The code confirms the isolator inclusion, signs and the separated products in §4 and verifies the finite implications of the source angular table, including 1,023 words through depth 9 and 1,922 prefix/suffix parity completions. Landing, source-physical realizations, common-neighborhood normality, and infinite shape compactness are not inferred from the regression. It may be copied into a file and run with python -B.

~~~python
from fractions import Fraction as F
from itertools import product
import json

def I(x): return (F(x), F(x))
def add(A,B): return (A[0]+B[0],A[1]+B[1])
def neg(A): return (-A[1],-A[0])
def mul(A,B):
    v=[a*b for a,b in product(A,B)]
    return min(v),max(v)
def sq(A):
    x,y=A
    return (F(0) if x<=0<=y else min(x*x,y*y),max(x*x,y*y))
def within(A,B): return B[0]<=A[0]<=A[1]<=B[1]
def strictly(A,B): return B[0]<A[0]<=A[1]<B[1]
C=(F(-1786511,10**6),F(-1786510,10**6))
n=-607918036626757496169199575185708826140
assert strictly((F(n,2**128),F(n+1,2**128)),C)
def f(X): return add(sq(X),C)
def g(X): return f(f(X))
def dg(X): return mul(I(4),mul(X,f(X)))
A=(F(-928,1000),F(-926,1000))
B=(F(518,1000),F(519,1000))
X=(F(-427,1000),F(-426,1000))
Y=g(X)
assert add(f(I(A[0])),neg(I(A[0])))[0]>0
assert add(f(I(A[1])),neg(I(A[1])))[1]<0
for i,b in enumerate(B):
    P=add(add(f(I(b)),I(b)),I(1))
    assert (P[1]<0 if i==0 else P[0]>0)
assert add(g(g(I(X[0]))),neg(I(X[0])))[0]>0
assert add(g(g(I(X[1]))),neg(I(X[1])))[1]<0
assert strictly(Y,(F(786,1000),F(790,1000)))
for Z in (X,Y,B):
    assert f(Z)[1]<0
    assert strictly(Z,(F(-926,1000),F(926,1000)))
fixed=mul(I(16),mul(sq(A),add(C,I(1))))
mixed=mul(dg(X),dg(Y))
assert strictly(fixed,(F(-1084,100),F(-1079,100)))
assert strictly(mixed,(F(-1011,100),F(-1000,100)))
assert fixed[1]<mixed[0]

J=((F(1,6),F(1,3)),(F(2,3),F(5,6)))
K={'L':(1,2),'R':(3,0)}
def arcs(w):
    out=[]
    for j in (0,1):
        I0=J[j]; s=j
        for a in reversed(w):
            I0=tuple((x+K[a][s])/4 for x in I0)
            s^=(a=='R')
        assert s==(j^(w.count('R')%2))
        assert within(I0,J[s])
        assert I0[1]-I0[0]==F(1,6*4**len(w))
        out.append((s,I0))
    return dict(out)
count=0
for m in range(10):
    for letters in product('LR',repeat=m):
        w=''.join(letters); a=arcs(w); count+=1
        assert set(a)=={0,1}
        if w:
            parent=arcs(w[:-1])
            assert all(within(a[s],parent[s]) for s in (0,1))
assert count==1023
words=[''.join(w) for k in range(5) for w in product('LR',repeat=k)]
parity_count=0
for p,s in product(words,repeat=2):
    for e in (0,1):
        mid='R' if ((p+s).count('R')%2)^e else 'L'
        w=p+mid+s
        assert w.startswith(p) and w.endswith(s) and w.count('R')%2==e
        parity_count+=1
print(json.dumps({
    'fixed_multiplier_product_bounds': ['-271/25','-1079/100'],
    'mixed_multiplier_bounds': ['-1011/100','-10'],
    'angular_words':count,'parity_completions':parity_count,
    'status':'PASS'},indent=2))
~~~

## 8. Adversarial boundary and integration

* Suffix vs prefix: uniform shrinking of physical prefixes does not give convergence of their rescaled charts. The estimates deliberately compare a common suffix under arbitrary extra left prefix, not the reverse.
* Nondegeneracy is actual: no use of an unphysical affine IFS or approximate identification of periodic points. The IVT root and the signs identify the actual inverse sheets. The common-neighborhood lemma includes boundary vertices, necessary for the derivative at alpha.
* Finite vs infinite: exact interval checks establish the small finite multiplier contradiction; analytic steps give compactness, infinite limits, and the continuum cardinality. No finite test is promoted into a limit theorem.
* Observable: the normalized affine embeddings and (3) are marked affine geometry. All H charts on the same source V are conformally equivalent by reparametrization. A pure conformal invariant of a fixed transported root pair may not detect the difference. This is not an obstruction to the already known exact retimed source-coordinate identity.
* No parameter/combinatorics uniformity, no second-scale virtual root authorization, no new analytic closed-fiber realization in the original f-plane, no automatically protected relative-cover access, critical lift or new obstacle avoidance, no proof of proper/end-proper intervals for a relative cover, no final-root enlargement or complete Wave horizon. The full gate remains open; its premise VIRTUAL_FINITE_WORD_ROOT_PORTRAIT_AUTHORIZATION is not supplied. The global Böttcher marks are distinct from relative-carrier prime ends. The end projection is deliberately noninjective. Do not promote H1–H4, UPTCR, rigidity or MLC.

**Exact next obstacle:** determine which of the actual proof-used markings, relative-cover classes and width observables descend to a quotient of this joint shape/access graph; otherwise explicitly carry enough history, and prove naturality for all authorized root enlargements. Formula (5) rules out an unconditional finite menu of affine chart limits but does not rule out a finite sufficient statistic for a specified smaller observable.

**Dependencies/credit:** Kahn–Lyubich, *A priori bounds for some infinitely renormalizable quadratics II. Decorations*, arXiv:math/0609046v2, §2.1 Lemma 2.1, §2.2, pp.5–8, via the source-realized closed puzzle and terminal primitive cycle interfaces in virtual_cantor_pullback_compactification.md §3 and the merged direct-decoration cofinality audit §§1–5; FIRST_DECORATION_SCALE_ESCAPE_ATLAS, CRITICAL_BASE_CYCLE_EXCLUSION, DIRECT_DECORATION_PULLBACK_COMPACTIFICATION. Physical c_* isolator, 3/9 domains, actual ray labels and cofinality are inherited from the earlier Misiurewicz-tip and merged end-cofinality audits; their geometric proofs and hashes were not independently reexecuted. Classical covering lifting for proper holomorphic maps away from critical values, Riemann mapping/exterior uniformization, Montel, Rouché, Hurwitz, Koebe growth, Cauchy estimates and elementary compact metric topology. No a priori bounds used. The retimed formulation and its exact ledger target are critical_chronology_and_retimed_telescope.md §§12–16. The general scenery literature credited at the beginning is background; no result from it is assumed without proof.

Reviewed the repository CONTRIBUTING.md, targeted ledger entries, source puzzle and end notes, and active parallel PR descriptions; not a complete audit of all 465 ledger entries, the full manuscript, or the full prior literature. This submission adds only this note, with the standalone arithmetic diagnostic embedded, pending review. No proof-register, source-index, manuscript or ledger changes and no full CI or Lean run claimed. AI disclosure: OpenAI ChatGPT GPT-6.2 materially assisted the research, analytic derivation, repository and literature inspection, exact arithmetic checker and drafting. No independent human mathematical verification or specialist peer review has been performed.

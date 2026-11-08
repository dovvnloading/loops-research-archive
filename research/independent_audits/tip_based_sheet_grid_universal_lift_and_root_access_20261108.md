# Two independent winding charges and all-sheet ray-lift classification at the actual 3/9 tip

**November 8, 2026. Status:** an exact, source-typed local theorem on Kahn's *actual canonical localization covers* at the nonattracting twice-airplane-tuned period-3/9 Misiurewicz quadratic. It establishes a two-coordinate infinite fine-sheet grid, an optimal universal-cover lifting obstruction, a positive slit-domain lift construction, and the first complete properness/root-compatibility classification **of every fine lift** of the 32 physical source ray accesses. It neither produces a full Kahn–Lyubich \(\lambda,\xi,\eta\) prime-end functor nor proves MLC.

## 1. Physical and source-defined data

At the exact isolated parameter \(c_*\) use \(f(z)=z^2+c_*\). The two actual proper degree-two returns have connected full little Julia sets \(K_9\subset K_3\). Their mutually disjoint phases are
\[
 C_r=f^r(K_3),\quad D_{r,j}=f^{r+3j}(K_9),\qquad 0\le r,j<3.
\]
Choose the common outer Jordan disk \(U^0\), and set
\[
 \Omega_3=U^0\setminus\bigcup_r C_r
 \subset
 \Omega_9=U^0\setminus\bigcup_{r,j} D_{r,j}.
 \tag{1}
\]
The inclusion \(i:\Omega_3\hookrightarrow\Omega_9\) is **physical**, not a six-iterate dynamical map or a pseudo-piece immersion.

Write \(\pi_p:(\widehat T_p,\widehat K_p)\to(T_p,K_p)\), \(T_p=\Omega_p\cup K_p\), for Kahn's canonical marked localization at \(K_p\). Its exterior \(\pi_p:\widehat\Omega_p\to\Omega_p\) is a covering, its marked-root inverse image is \(\widehat K_p\), it is bijective on that root, and it is biholomorphic on an actual neighborhood of the root. These are source conditions of the localization—not hypothetical properties of an arbitrary universal cover. Source: Kahn, *A priori bounds ... I*, §7.4.1 and Theorem 7.12 (original version); the author working draft's equivalent localization in §8.3.1. Exact source geometry and based groups were proved in the archive's tip-localization refinement and iterated/direct localization papers from November 6.

The already merged #55–58 physical ray atlases supply 32 distinct ambient-ray **access classes** landing at 15 physical points of \(K_3\). Exactly eight rays land in \(K_9\), with numerators
\[
 A_8=\{116736,116791,144841,144896,378368,378423,406473,406528\}/523264;
 \tag{2}
\]
the other 24 rays land at twelve distinct points of \(K_3\setminus K_9\) avoiding **every fine-cycle obstacle**. The eight fine rays represent four distinct fine *prime ends* with two rays each, while at the tip the eight rays have only three distinct physical landing points. Do not equate those two counts.

## 2. Actual free-group geometry and two independent integer charges

Use exactly the compatible based meridians of the archive's common-exterior theorem:
\[
\begin{gathered}
\Gamma=\pi_1(\Omega_9,x)=F(b_{r,j}:0\le r,j<3),\qquad
G=\pi_1(\Omega_3,x)=F(a_0,a_1,a_2),\\
i_*(a_r)=\beta_r=b_{r,0}b_{r,1}b_{r,2},\quad
\Gamma_c=i_*(G)=\langle\beta_0,\beta_1,\beta_2\rangle
 \hookrightarrow\Gamma,\\
H=(\pi_9)_*\pi_1(\widehat\Omega_9)=\langle b_{0,0}\rangle.
\end{gathered}\tag{3}
\]
The actual fine based sheet fiber is the *left-coset right-action set* \(H\backslash\Gamma\). In particular \(H\) is **not normal**. Components of the fine preimage above \(\Omega_3\) are the right-\(\Gamma_c\) orbits, indexed by the double cosets \(H\backslash\Gamma/\Gamma_c\).

Let \(w_{r,j}(g)\) be the honest integer winding about physical \(D_{r,j}\), given by abelianization of the nine-component complement. Define
\[
 \boxed{\delta(Hg)=w_{0,1}(g)-w_{0,2}(g),\qquad
        \nu(Hg)=w_{0,2}(g).}\tag{4}
\]
These are well defined on left cosets because every \(h\in H\) has zero winding about \(D_{0,1},D_{0,2}\). In addition \(\delta\) is invariant under *right multiplication by every* \(i_*(a_r)=\beta_r\), so \(\delta\) descends to the double-coset component set; \(\nu\) intentionally does **not**.

### Theorem 2.1 (explicit physical \(\mathbb Z^2\) fine-sheet grid)

For **all** \(k,n\in\mathbb Z\), set
\[
 \boxed{\sigma_{k,n}=H\,b_{0,1}^{\,k}\beta_0^{\,n}\in H\backslash\Gamma.}
 \tag{5}
\]
Then
\[
 \boxed{(\delta(\sigma_{k,n}),\nu(\sigma_{k,n}))=(k,n),\qquad
        \sigma_{k,n}\cdot a_0=\sigma_{k,n+1}.}\tag{6}
\]
The map \((k,n)\mapsto\sigma_{k,n}\) is injective. For each fixed \(k\), the entire integer orbit \(\{\sigma_{k,n}\}_n\) lies within **one** connected component \(R_k\) of \(\pi_9^{-1}(\Omega_3)\); for different \(k\), these components are different. Both the component and within-component fine-sheet sets are countably infinite. This is a \(\mathbb Z^2\) *indexed subset*, not an assertion that \(H\backslash\Gamma\) is a group or is exhausted by those representatives.

*Proof.* The windings of \(b_{0,1}^k\beta_0^n\) about \((D_{0,0},D_{0,1},D_{0,2})\) are \((n,k+n,n)\), giving (6). If two cosets are equal, their two characters are equal, so both indices are equal. Changing \(n\) right-multiplies by \(\beta_0\in\Gamma_c\), preserving the component. Changing \(k\) changes \(\delta\), which is a component invariant. The whole fine fiber is countable because \(\Gamma\) is finitely generated. \(\square\)

This separates *transverse fine-component information* (\(k\)) from *coarse-peripheral winding inside one component* (\(n\)). Earlier examples proved an infinite deck orbit; the present source-specific theorem exhibits two independent, explicitly recoverable unbounded charges in the **same actual physical covering**.

### Theorem 2.2 (universal-cover optimality for complete coarse-exterior lifts)

Let \(Y\to\Omega_3\) be **any connected covering**. A based lift \(Y\to\widehat\Omega_9\) of the composite \(Y\to\Omega_3\xrightarrow{i}\Omega_9\) exists, for any prescribed compatible initial fine sheet, **if and only if** \(Y\to\Omega_3\) is the universal cover.

*Proof.* A subgroup \(J\le G\) supports such a lift precisely when \(i_*(J)\le g^{-1}Hg\) for the conjugating word determined by the initial fine sheet. The earlier based-group embedding gives, for **every** \(g\in\Gamma\),
\[
 \boxed{\Gamma_c\cap g^{-1}Hg=\{1\}.}\tag{7}
\]
For completeness, if \(i_*(u)=g^{-1}b_{0,0}^{m}g\), abelianization of its right side has winding \(m\) about \(D_{0,0}\) and zero about \(D_{0,1}\). Every element in \(\Gamma_c\) has *equal* winding about those two fine components. Thus \(m=0\), \(i_*(u)=1\). The free-product normal form of the three \(\beta_r\) makes \(i_*\) injective, hence \(u=1\). Therefore \(J=1\). Conversely a simply connected universal cover satisfies the ordinary covering-space lifting criterion from any based fine sheet. \(\square\)

**Consequently no finite-degree connected covering of the coarse localized annulus can lift to the fine cover, and neither can any non-universal infinite-degree connected cover.** Its core corresponds to \(a_0\); a connected annular covering with subgroup \(m\mathbb Z\), \(m\ne0\), would send this peripheral power to \(\beta_0^m\), whose winding about \(D_{0,2}\) is \(m\), whereas every conjugate of \(H\) winds there zero. This is a sharp covering-space obstruction, not a claim that no *partial* path lift exists.

## 3. Constructive positive slit transport, without invented boundary extensions

The coarse exterior \(S=\widehat T_3\setminus\widehat K_3\) is a finite-modulus annulus. The explicitly selected restricted component \(R\subset\widehat\Omega_9\) maps to \(S\) by its genuine universal covering \(q:R\to S\), and in conformal charts one can write
\[
 S\simeq\{r<|z|<1\},\quad
 R\simeq\{\log r<\operatorname{Re}w<0\},\qquad q(w)=e^w.
 \tag{8}
\]
Fix the genuine ambient \(114/511\) coarse-root ray access as **one inner prime-end anchor**. A conformal gauge sending it to \(r e^{i\vartheta}\) determines a radial slit \(\Sigma=\{t e^{i\vartheta}:r<t<1\}\). Then \(S^\times=S\setminus\Sigma\) is simply connected, and **every component of \(q^{-1}(S^\times)\) maps biholomorphically onto it**. Fixing an initial fine sheet selects one of these components, giving a complete holomorphic **based interior path-lift functor for all compact paths in that slit domain** (identity, inverses, concatenation and homotopies).

This is a positive minimal one-crosscut resolution of the winding obstruction. The chosen radial slit is *not automatically a physical whole dynamical ray* or a KL \(O/\xi/\eta\) edge. The source's wrapping-end obstruction still forbids extension of the full universal-cover projection at its two infinite-winding ends. No single slit section is claimed root-compatible with all eight selected fine-ray accesses; that would require actual based connector choices.

## 4. Every lift of every one of the 32 genuine ray tails

Let \(\gamma_\theta:(0,1]\to\Omega_3\) be a sufficiently short terminal *physical* external-ray arc at small positive Green level, landing at \(z_\theta\in K_3\). At its chosen initial physical point, the fine fiber has cardinality \(\aleph_0\), and **each based fine sheet gives precisely one lifted ray tail**, by path lifting. Properness means escape from every compact set of the specified surface; \(\widehat\Omega_9\) and the filled \(\widehat T_9\) are deliberately distinguished.

### Theorem 4.1 (the complete rooted-vs-escaping/all-sheet properness dichotomy)

**For each of the eight \(\theta\in A_8\)**, \(z_\theta\in K_9\):

1. \(\gamma_\theta\) is proper in \(\Omega_9\), and **every one** of its countably infinitely many fine lifted tails is proper in the fine exterior \(\widehat\Omega_9\).
2. Exactly **one** lifted tail converges to the uniquely marked point \(\widehat z_\theta\in\widehat K_9\) in the full surface \(\widehat T_9\). Call this the *root-compatible* lift.
3. Every *other* lifted tail escapes every compact subset of the **full** surface \(\widehat T_9\), and so remains proper even after filling in the root. No claim is made about convergence to any specified fine \(\lambda/\xi/\eta\) prime end.

**For each of the 24 \(\theta\in A_{24}\)**, \(z_\theta\) is one of the 12 interior points of \(\Omega_9\):

4. \(\gamma_\theta\) is proper in \(\Omega_3\) but **improper** in \(\Omega_9\). Every fine lifted tail converges to an ordinary interior point of \(\widehat\Omega_9\); **none** is proper in the fine exterior and **none** is root-compatible.

*Proof.* For an eight-ray endpoint, \(z_\theta\) is removed from \(\Omega_9\), so \(\gamma_\theta\) is proper there. A lift of a proper path through a covering is proper: the preimage of a compact set in the lifted exterior is a closed subset of the preimage under the base path of its compact projection. By Kahn's marked-root property \(\pi_9^{-1}(K_9)=\widehat K_9\) and the conformal local inverse of \(\pi_9\) on a neighborhood of \(K_9\), one definite ray lift converges to the unique \(\widehat z_\theta\). If a different lift had a compact accumulation point in \(\widehat T_9\), continuity and root uniqueness would force that accumulation point to be \(\widehat z_\theta\). At a time when the second lift enters the injective root neighborhood it coincides with the distinguished lift, so path-lift uniqueness makes the two lifts identical—contradiction. Hence every non-root lift escapes all compact sets of the filled surface.

For the other 24 rays, the prior physical atlas proves \(z_\theta\) avoids **all** nine fine obstacles and lies in the open \(\Omega_9\). A small evenly covered disk about \(z_\theta\) contains the ray's final tail. Each lifted final tail stays in one sheet of the disk covering and converges to its ordinary interior inverse image of \(z_\theta\). It is therefore nonproper, proving Item 4. \(\square\)

The exact all-sheet output on the 32 distinct coarse accesses is thus:

| Cohort | Fine exterior lifts per ray | Root-compatible fine lifts per ray | Other lifts |
|---|---|---:|---|
| Eight physically fine-surviving rays (four *fine prime-end* classes) | \(\aleph_0\), **all proper** | **1** | \(\aleph_0\) escaping the full \(\widehat T_9\) |
| Twenty-four coarse-only rays (twelve *fine interior* landing points) | \(\aleph_0\), **all improper** | **0** | \(\aleph_0\) converging to fine interior points |

**Non-implication:** *Exactly one root-compatible lift* is **not** *exactly one proper lift*. Indeed for each surviving ray there are infinitely many other proper fine-cover lifts. This distinction is critical for any future KL/KKL use of a singleton proper-restriction hypothesis. The theorem is about **physical source rays lifted through the actual fine localization covering**, not a blanket classification of all proper restriction components in a complete KL proof-used path family.

## 5. What this closes and what it cannot close

This result closes: an explicit \(\mathbb Z^2\) sheet sublattice with its double-coset component interpretation; exact minimality of the universal covering for globally liftable coarse exteriors; a constructive one-slit interior holomorphic lift; and the all-sheet properness / rooted-lift classification for **all 32** actual selected rays. The signed integer free-word verifier checks the lattice on 289 representatives with 83,521 exact coset comparisons and recomputes the 8/24/12 physical labels; a new Lean module verifies the integer character identities and imported 8/24 finite split. The two **infinite** theorems and analytic ray conclusions rest on the written proofs, not on a finite numerical test.

The first remaining marked KL gate is to determine the **actual based coset of the distinguished root-compatible lift for each of eight rays**, with the source's real \(O/\xi/\eta\) pseudo-piece tile, integer winding and endpoint convention. Even with that done, the infinite competing proper non-root lifts require a family-level exclusion or charge; a ray pair count cannot discharge a singleton proper-restriction predicate. Cross-scale global boundary extension, H1–H4, UPTCR and MLC remain **OPEN**.

**Sources and credit:** Jeremy Kahn (canonical localization), Kahn–Lyubich (pseudo-piece ends and naturality), Genadi Levin (ray-to-renormalization prime ends), classical covering-space group theory, and the archive's earlier exact tip, alpha-puzzle and 3/9 localization proofs. OpenAI GPT-6 assisted this mathematical synthesis, exact free-word program and finite Lean module. There has been no independent external expert review or priority determination.

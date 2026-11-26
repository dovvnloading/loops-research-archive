# One dividing vertex suffices: conformal ideal disks for actual KL escape and return phases

**2026-11-26 — independent written proof, awaiting specialist review.** Target: ESCAPE_RETURN_KL_PSEUDOPIECE_CONFORMAL_IDEAL_BOUNDARY, open in the July source-locked ledger. The conclusion holds for every genuine finite ordinary KL puzzle piece in its source category, in particular the actual escape and first-return phases of the archive's first-decoration-scale atlas. It does not cover a virtual or carrier-relative surface merely bearing a puzzle label.

## 1. Source lock and statement

J. Kahn and M. Lyubich, [*A priori bounds for some infinitely renormalizable quadratics: II. Decorations*, IMS 2006/6](https://www.math.stonybrook.edu/preprints/ims06-06.pdf), [published version, Ann. ENS 41 (2008), 57–84](https://doi.org/10.24033/asens.2063). The following locators use printed preprint pages, checked against the rendered pages: §1.1, p. 4 (disks and closed pullbacks); §2.1, pp. 5–6 (ordinary finite puzzles, dividing vertices and escape piece); §2.2, pp. 7–8 (return pullbacks); §2.3, p. 8 (geometric pieces); §3.1 and Lemma 3.1, p. 10 (native psi-ql maps and ordinary restrictions); §3.2.1 and Lemma 3.3, pp. 11–12 (path-space projection and separate universal-cover tiles); Lemma 3.4, pp. 12–13 (covering versus inclusion); §3.2.4, p. 13 (ideal-side labels and continuous inclusion extension).

J. Kahn, [*A priori bounds ... I. Bounded primitive combinatorics*, IMS 2006/5](https://www.math.stonybrook.edu/preprints/ims06-05.pdf), §§3.1–3.2, pp. 9–10 (canonical ideal boundary and disk-uniformization deck-group description). This is a preprint, not a claim of publication.

Use the source's actual marked quadratic-like map with connected full filled continuum \(K\), repelling fixed points and the dividing fixed point \(\alpha\) with \(q>1\) landed external rays. In the first-decoration setting use the polynomial and marked puzzle of [the first-scale atlas, §§3–4](../../mlc_unified/virtual_scale_to_puzzle_selector.md). At a native psi-ql stage use the genuine ordinary restriction furnished by KL Lemma 3.1, with its finite puzzle pieces in the corresponding ambient iterated disk. All pieces considered are source-defined closed Jordan puzzle disks with finite ray/equipotential boundaries. No local connectivity of \(K\) is assumed.

**Theorem.** For each such genuine finite ordinary geometric puzzle piece \(Y\), its native KL pseudo-piece \(\Psi(Y)\) is a hyperbolic conformal disk. Its Kahn ideal closure is the conformal closed disk; the finite native \(\lambda_i,\xi_i,\eta_i\) tiling is of that circle. For each actual puzzle inclusion \(Y\subset Z\), the KL inclusion immersion extends continuously to the two conformal ideal closures. This is not an assertion of injectivity, boundary-valuedness, map properness or extension of a canonical localization comparison.

In particular this proves the intrinsic ideal-boundary assertion for every genuine phase of the actual first-scale escape-return atlas, not just a PCF example.

## 2. The actual path surface and its finite open star

Let \(Y\) have depth \(m\); write \(U_m\) for the ambient open iterated disk of KL §3.2.1, containing the closed ordinary geometric piece (use the larger carrier, not the truncated equipotential as its outer boundary). In these geometric coordinates set

\[
 K_Y=Y\cap K,\qquad S_Y=\overline{K\setminus K_Y},\qquad A_m=U_m\setminus K.
\]

For a native abstract carrier these are the source-identified filled continuum and its subsets in the ambient disk, not their projection to a different carrier. KL defines the actual projection

\[
 \pi_Y:\Psi(Y)\longrightarrow U_m\setminus S_Y
\]

by evaluating the terminal point of the permitted path class. It is a nonconstant holomorphic immersion. Use the path/gluing equivalence of Lemma 3.3, not an identification of points with equal physical projection.

In the open surface the central image consists of constant-path points of \(Y\setminus S_Y\): although the source also speaks of the closed puzzle piece, vertices in \(S_Y\) cannot be interior points of the path surface. Write \(Y_i\) for the finitely many components of \(Y\setminus K_Y\). KL §3.2.1 gives each \(Y_i\) simply connected, and Lemma 3.3 gives disjoint embedded copies \(T_i\) of the universal cover of \(A_m\), glued along exactly \(Y_i\).

Let \(C\) be the central image of \(\operatorname{int}Y\). The closure of \(K\setminus K_Y\) misses \(\operatorname{int}Y\), so the entire central interior is present and is open by invariance of domain (or the local chart of \(\pi_Y\)). Each \(T_i\) is open by its embedded surface chart. Every central boundary point outside \(K\) belongs to a \(Y_i\), hence to \(T_i\). Every central boundary point in \(K\) is a dividing vertex by §2.1 and belongs to \(S_Y\) by Lemma 3.3; it is excluded from the open path surface. The gluing equivalence therefore gives the finite open cover

\[
 \Psi(Y)=C\cup\bigcup_{i=1}^N T_i,\qquad
 T_i\cap T_j=\varnothing\ (i\ne j),\qquad
 C\cap T_i\cong\operatorname{int}Y\cap Y_i.
\]

The last intersection is nonempty and path-connected. Use a homeomorphism of the closed disk onto the Jordan disk \(Y\). The pullback of \(Y_i\) is relatively open in the closed disk: \(Y\setminus K_Y\) is relatively open, and its components are open since the closed disk is locally path-connected. A small radial push of a point gives an interior point of this set. For two interior points, take a path in \(Y_i\) (source simple connectivity). In the closed-disk coordinate its compact image has positive distance from the relative complement, unless that complement is empty, in which case there is nothing to avoid. Multiplying the path by \(1-\varepsilon\) for sufficiently small \(\varepsilon>0\) keeps it in this set and moves it into the open disk. Join each moved endpoint to the original by its short radial segment, also in the same set and the open disk. This proves path-connectedness without assuming the gluing set is open in the full surface.

The central open disk and all tiles are simply connected. Inductively attach \(T_i\): its intersection with the previous open union is precisely \(C\cap T_i\). Van Kampen gives \(\pi_1(\Psi(Y))=1\). This is a finite open-star argument for every phase, including one-vertex off-critical phases; it does not apply van Kampen to a closed central piece.

## 3. One-vertex omitted-value lemma and hyperbolicity

**Lemma.** If \(v\in\partial Y\cap K\) is a dividing puzzle vertex, then \(S_Y\) is infinite.

Indeed \(v\in K_Y\) by the definition of the closed puzzle piece. KL Lemma 3.3 gives \(v\in S_Y\). Hence

\[
 v\in\overline{K\setminus K_Y}\setminus(K\setminus K_Y).
\]

A finite subset of a Hausdorff surface is closed. Thus \(K\setminus K_Y\) is infinite. In fact one can choose distinct points \(w_j\in K\setminus K_Y\) tending to \(v\), using a coordinate neighborhood. Each \(w_j\) belongs to \(S_Y\). This uses the omitted set in the actual native path definition, not an inferred external-ray impression.

Every ordinary depth-zero piece has \(\alpha\) as a vertex. A finite depth-\(m\) piece is the closure of a connected pullback of a depth-zero interior. The pullback maps onto that interior by properness and openness. A sequence there approaching \(\alpha\) has preimages in the chosen piece, and compactness gives a limit mapping to \(\alpha\). This limit is on the boundary (interior points map to the open target). By the source puzzle definition these landed preimages are ray vertices. Thus every genuine ordinary phase has at least one vertex; there is no need to count two distinct vertices. For a genuine geometric bidepth piece the same argument uses its unchanged ray vertices.

The projection \(\pi_Y\) omits \(v,w_1\) (indeed infinitely many points). If \(\Psi(Y)\) were compact its image in the connected ambient disk would be nonempty, open by the open mapping theorem and closed by compactness, hence the whole ambient disk, contradicting omission. This excludes the sphere. Uniformization says a noncompact simply connected Riemann surface is conformally the plane or disk. The ambient \(U_m\) is itself a source disk (open, simply connected), so it is conformally the plane or disk. If \(\Psi(Y)\cong\mathbb C\) and \(U_m\cong\mathbb D\), the projection in uniformizing coordinates is a bounded nonconstant entire map, contrary to Liouville. If \(U_m\cong\mathbb C\), it is a nonconstant entire map omitting at least two distinct finite values, contrary to Little Picard. Therefore

\[
 \boxed{\Psi(Y)\cong\mathbb D.}
\]

For the actual first-scale polynomial one could instead choose a larger finite equipotential and use the bounded physical projection. The omitted-value proof does not silently assume a bounded planar chart on an abstract native carrier. It improves the particular two-vertex verification in [outer-port footprint, Theorem 9.1](../../mlc_unified/direct_decoration_outer_port_footprint.md).

## 4. Every actual escape/return phase

Use the exact notation of the [first-scale atlas, Theorem 4.1](../../mlc_unified/virtual_scale_to_puzzle_selector.md):

\[
 m=nq+1,\quad V_{\rm esc}=Y^m,\quad B_{\rm esc}=\operatorname{int}V_{\rm esc},
 \quad f^{r_i}:W_i\to B_{\rm esc}.
\]

Here \(n\) is the least critical \(q\)-return escape into an off-critical depth-one piece and each \(W_i\) is an actual connected first-return pullback with integer time \(r_i\ge1\). No relation \(r_i=nq\) is asserted. Use the polynomial itself, or the genuine ordinary restriction and its finite proper iterates.

Let \(O\) be the depth-zero open puzzle piece of which \(B_{\rm esc}\) is a component of \(f^{-m}(O)\). Components of these open inverse images are open. The first-return atlas selects \(W_i\) as a component of \(f^{-r_i}(B_{\rm esc})\). For \(0\le k\le r_i\), let \(D_k\) be the component of \(f^{-(r_i-k)}(B_{\rm esc})\) containing \(f^k(W_i)\). Then \(W_i\) is a component of \(f^{-k}(D_k)\): it is contained in that preimage, and any connected enlargement there would lie in \(f^{-r_i}(B_{\rm esc})\). The restriction \(f^k:W_i\to D_k\) is proper, since the inverse image of a compact subset of \(D_k\) is compact for the finite proper iterate and intersection with a component of \(f^{-k}(D_k)\) is closed in it. Its image is nonempty, open and relatively closed, hence all of \(D_k\). Thus \(D_k=f^k(W_i)\).

Further, \(D_k\) is a component of \(f^{-(m+r_i-k)}(O)\): the image under \(f^{r_i-k}\) of any connected subset of that preimage meeting \(D_k\) is connected in \(f^{-m}(O)\) and meets \(B_{\rm esc}\), hence lies in \(B_{\rm esc}\). Component maximality proves the assertion. This gives the natural ordinary-depth representatives of the connected puzzle components in the atlas:

\[
 P_{i,k}=\overline{f^k(W_i)},\qquad
 d_{i,k}=m+r_i-k,\quad 0\le k\le r_i.
\]

If a separate genuine geometric bidepth representative is chosen, its ray vertices are unchanged. The argument concerns connected **open** pullback components and then closures, not components of a closed preimage that may touch at vertices. Every \(P_{i,k}\) and \(V_{\rm esc}\) is therefore covered by the theorem, independently of branch count, return time or chronological degree word. In particular the central first-return phase has not been replaced by a univalent branch.

For a concrete example, [both actual 3/9 tip-stage first children](../tip_kl_terminal_first_child_20261106.md) have \(q=2,n=1,r=3\) in their own stage clocks. The natural depth list is \(6,5,4,3\) at both stages; the second stage's physical polynomial time is multiplied by three. The example is an illustration, not a restriction of the theorem.

## 5. Ideal closures and the exact lift consequence

Kahn I §3.1 identifies the ideal closure of a hyperbolic finite-type surface without cusps by a compact conformal bordered representative. Here the representative is the closed disk. In §3.2's universal-cover formulation the deck group is trivial, so its limit set is empty and one obtains the same closed disk. Disk uniformizations differ by a disk automorphism extending to the circle, so this is intrinsic. KL II §3.2.4 supplies the finite ideal-side tiling and continuous extension for the inclusion immersion of Lemma 3.4(ii). The named sides thus lie in this conformal ideal circle, with the adjacent-tile convention

\[
 \partial^{v_i}\Psi(Y)=\eta_i\cup\xi_{i+1}.
\]

Retain tile tags and order, not just physical landing labels. This invocation concerns intrinsic ideal points, not extension of the physical projection to a potentially non-locally-connected Julia set. The inclusion extension may take ideal points to target interior, as the source explicitly allows. The dynamical covering of Lemma 3.4(i) is a separate arrow: a finite proper holomorphic map of disks has the standard finite Blaschke representation and circle map of its degree, not the immersion's boundary behavior.

**Corollary.** For any supplied actual inclusion between ordinary escape/return puzzle pieces (or with another genuine ordinary piece), the disk and continuous-extension hypotheses of [the maximal-lift theorem, Theorem 3.1](../../mlc_unified/canonical_kl_geometric_trace_proper_end_response.md) are now verified. Each maximal parameter-compatible lift of a supplied proper target path has unique intrinsic source ideal limits at both parameter ends, mapping under the continuous extension to the corresponding target path values. An internal parameter endpoint is still a target-interior break end. This is FULL_KL_PSEUDOPIECE_MAXIMAL_LIFT_PROPERNESS with its domain hypotheses discharged; not a proof of geometric inverse-trace exhaustion, lift existence or uniqueness, tagged protected endpoints or positive Wave width retention. The statement concerns endpoint convergence; it does not add a distinct-end assertion when the two source limits could coincide.

## 6. Dependency and gate accounting

The target's listed prerequisites are FINITE_GRID_AND_TERMINAL_KL_PSEUDOPIECE_CONFORMAL_IDEAL_BOUNDARY and FIRST_DECORATION_SCALE_ESCAPE_ATLAS. The former is not needed for the stronger one-vertex theorem; the latter identifies the actual phases. The independent proof uses KL II's source lemmas and sections above, van Kampen, uniformization, Liouville and Little Picard. No open terminal carrier premise is used.

The old target evidence file direct_decoration_bigraded_kl_stage_grid.md was not present at the pinned base 6ba50a4b452f7703c17200dd3b3bab4b117ee413 (expected unified path returned 404). The first-scale atlas itself and the earlier outer-port proof are present. This audit uses their actual notation rather than reconstructing the missing historical grid.

The frozen graph has no direct consumer of the target row, hence no recorded path from H1, MBTT, H3 or H4 to it. This is a documentary gap, not proof that the mathematical input is irrelevant: the stage-alignment and path-lift obligations require the intrinsic domain hypotheses on these pieces. The corollary makes this usable for supplied ordinary inclusions, but does not supply a binder or certify canonical/relative comparisons. A future dependency revision can record this input where the arrows are consumed rather than silently replacing an open Wave premise.

The full WAVE_TO_KL_ADDRESS_ACCESS_SELECTOR, TERMINAL_WAVE_KL_CONNECTING_SUBFAMILY, TERMINAL_TAGGED_ENDPOINT_ACCESS_MATCH and END_PLUMBING_TRACE_RESPONSE_CONTROL remain open. The dense-obstacle no-go, canonical localization collisions and distinction between intrinsic ideal circles and carrier-relative endpoints are untouched. No uniform separation/modulus bound, trace compactness, width retention, all-scale transition, H1/MBTT/H3/H4 closure, UPTCR or MLC consequence is claimed.

**Proposed classification:** written proof of the target for actual ordinary KL phases in the first-scale atlas, with the stronger ordinary-piece theorem. Keep the July ledger and its mirrors unchanged pending independent review and an explicit dependency update. The new proof register records a direct written result, not a model-to-geometry promotion.

## 7. Reproduction and attribution

From the repository root:

    python3 -B research/independent_audits/kl_escape_return_ideal_boundary_20261126/verify.py
    python3 -B code/verify_physical_bridges.py

The first script is standard-library Python 3. It checks exact integer phase clocks (2,800 finite sanity cases), a graph regression, and source/contract registration, and reports actual ledger dependency paths. Its JSON is metadata, not proof of analytic or topological claims. There are no tolerances or random seeds. The second command checks repository wiring, not mathematics.

AI disclosure: OpenAI ChatGPT GPT-6.2 performed source reading, proof construction, adversarial scope checking and code preparation. No human specialist verification has been performed. Primary attribution is to Kahn and Lyubich for the native puzzle construction and Kahn for the intrinsic ideal boundary, with the classical results identified above. The one-vertex reduction and phase application are the contribution.

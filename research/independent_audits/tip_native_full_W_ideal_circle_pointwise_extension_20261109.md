# The complete original KL W ideal boundary: source-typed pointwise fine-localization extension and obstruction

**November 9, 2026 — proposed theorem for Issue #62.** This is a substantial **pointwise boundary-classification** result for the **actual ordinary** \(G=f^3\) Kahn–Lyubich W pseudo-piece \(\Psi_G(W)\), built from original KL II §3.2.1 path classes and the four genuine universal-cover carrier tiles. It completes the already merged PR #65's strict finite J-side case by treating **all four original finite W vertices, all finite O-side points, and all eight original infinite-winding O/J joints**. It is a theorem about the presence/absence of a **limit in the uncompactified fine canonical surface** for the existing source-native immersion, not a complete continuous map between whole ideal circles, not a theorem about an enlarged boundary compactification, and not the native KKL proper-path/unique-restriction condition.

The source and analytic classification is written mathematics with explicit inherited Kahn/KL hypotheses. Lean checks finite original vertex/cyclic incidence, not analytic covering spaces, whole ideal prime ends or continuous extension.

## 1. The original KL side partition (no synthetic replacement)

Write the original stage as \(G=f^3\), with connected subhyperbolic \(K_3\supset K_9=[-p,p]\). The exact W piece is \(W_G=\operatorname{int}Y_G^6\) with **strict** geometric nesting

\[
K_9\Subset W_G\Subset V_G=\operatorname{int}Y_G^3\subset T_9.
\tag{1}
\]

The previously established range-avoidance proof excludes all eight **other** fine physical phase obstacles from \(V_G\). Thus every point of \(V_G\setminus K_9\) lies in the genuine open fine exterior \(\Omega_9\).

The original \(\Psi_G(W)\) is obtained by gluing four copies of the **universal cover** of \(A_6=\mathcal U_G^6\setminus K_3\) to the four original W exterior sectors. In the actual KL II §3.2.4 conformal ideal circle, tile \(i\) has an O-arc \(\lambda_i\) and two remaining J-arcs \(\xi_i,\eta_i\). They join at the **actual source** boundary incidences

\[
\omega_i^-=\lambda_i\cap\xi_i,\qquad
\omega_i^+=\lambda_i\cap\eta_i,\qquad
v_i=\eta_i\cap\xi_{i+1\bmod4}.
\tag{2}
\]

Here the \(\omega_i^\pm\) are distinct **infinite-deck winding ends**, while the \(v_i\) are four **finite source puzzle vertices**. The source's open W gluing seams are **not** remaining ideal J-sides. In the topological angle-height strip description of a tile, a finite \(\lambda_i^\circ\) point is at *outer* positive carrier height \(t=H_6\), with finite unwrapped angle \(x\in\mathbb R\); strictly finite \(\xi_i^\circ,\eta_i^\circ\) have *inner* height \(t=0\), with unwrapped angles outside the source seam. The only other boundary points are the four \(v_i\) and eight \(\omega_i^\pm\). In particular, the ideal circle is exactly exhausted by these disjoint **types**, not by only the eight real root rays.

Let \(p_W:\Psi_G(W)\to T_9\) denote the previously sourced physical projection, and \(j_W:\Psi_G(W)\to\widehat T_9\) the unique same-root holomorphic immersion with \(\pi_9j_W=p_W\) on the interior. The underlying fine target \(\widehat T_9\) remains **uncompactified**.

## 2. Finite original W vertices: an actual positive theorem from KL naturality

**Theorem 2.1 (all four original finite J-vertices extend to ordinary fine-cover points).** For each \(i=0,1,2,3\), let \(v_i=\eta_i\cap\xi_{i+1}\) be the genuine finite vertex of the original KL W pseudo-piece. Then

\[
j_W(z)\longrightarrow s_{V_G}(v_i)\in
\widehat\Omega_9
\quad\text{as }z\to v_i
\text{ in the original ideal-circle topology.}
\tag{3}
\]

Thus \(j_W\) extends **uniquely and continuously at the original source vertex**. Both adjacent original \(\eta_i\) and \(\xi_{i+1}\) approaches have the **same** fine limit. Moreover the four physical \(v_i\) are distinct actual original depth-six landed vertices, not collapsed synthetic side tags.

**Proof.** The *original* KL II Lemma 3.4(ii) inclusion immersion \(I:\Psi_G(W)\to\Psi_G(V^0)\) extends continuously to the **whole original source ideal boundary** by the explicit KL II §3.2.4 statement. Its value at each W vertex is the **central physical point \(v_i\)**, because \(\overline{W_G}\Subset V_G\); the geometric source W vertex lies strictly *inside* the V central disk, not on a V ideal boundary. The prior source-locked same-root immersion naturality gives \(j_W=j_V\circ I\) on the entire interior, and \(j_V|V_G=s_{V_G}\). As \(z\to v_i\) in the source ideal circle, \(I(z)\to v_i\) in the **ordinary interior** of \(\Psi_G(V^0)\); continuity of \(j_V\) yields (3). Since \(v_i\in\overline W_G\setminus K_9\subset V_G\setminus K_9\subset\Omega_9\), its fine lift is an **ordinary interior** point. The original depth-six source atlas supplies four different landing targets, which are independently checked in the deterministic manifest. \(\square\)

This argument is stronger than relying on an arbitrary bounded path comparison: it uses the **actual source-natural W→V inclusion** and a pre-existing holomorphic target map on a larger source domain.

## 3. Finite original O-side points: positive fine-exterior extensions

**Theorem 3.1 (every finite point of every original \(\lambda_i\) O-arc extends).** Every finite-unwrapped-angle point of \(\lambda_i^\circ\) has a **unique local continuous extension of the given interior** \(j_W\) into the ordinary fine exterior \(\widehat\Omega_9\).

**Proof.** KL II §3.2.4 says \(\lambda_i\) is the outer side of the actual universal carrier tile, and its **finite** strip points project to the external carrier equipotential \(\partial\mathcal U_G^6\) at **strictly positive** Green height \(H_6>0\). The source's positive carrier margin puts this compact equipotential in the ambient fine physical disk \(U^0\), and it is disjoint from \(K_3\) and therefore from **all nine** fine obstacles (three of them contained in \(K_3\), the others physically outside the G carrier). Hence its physical points belong to \(\Omega_9\). For any fixed *finite* outer angle, the source covering strip has a connected prime-end collar whose projection tends continuously to the corresponding physical equipotential point \(q\in\Omega_9\). Choose a small evenly covered disk \(B\Subset\Omega_9\) about \(q\). The collar's connected fine image is in one sheet over \(B\), and composing its physical projection with that sheet's inverse supplies the unique local continuation to the side point. No convergence is asserted at the *infinite* ends \(x\to\pm\infty\). \(\square\)

## 4. All eight native infinite winding O/J joints: a universal nonextension argument

**Theorem 4.1 (every \(\omega_i^\pm\) is nonextendible into the fine surface).** For every one of the source's **eight** actual \(\lambda_i/\xi_i\) or \(\lambda_i/\eta_i\) infinite winding prime ends, **no** continuous map of the **interior** \(\Psi_G(W)\) into \(\widehat T_9\) that commutes with the physical projection \(p_W\) can extend continuously there into \(\widehat T_9\). In particular the actual same-root immersion \(j_W\) cannot extend at any \(\omega_i^\pm\).

**Proof (independent of fine root sheet selection).** In the actual source universal-cover tile \(\widehat A_i\), let \(\tau_i\) be its positive deck generator. KL II §3.2.4 identifies \(\omega_i^\pm\) with the original **infinitely wrapping** ideal path ends, and the archive's earlier source-side atlas §2 provides a standard tail-crosscut proof: for **any fixed interior tile point** \(z\),

\[
\tau_i^n z\longrightarrow\omega_i^+\ (n\to+\infty),
\qquad
\tau_i^n z\longrightarrow\omega_i^-\ (n\to-\infty)
\]

in the *whole glued source pseudo-piece's* ideal compactification. Choose two fixed tile points \(z,w\) whose physical carrier projections differ, \(p_W(z)\ne p_W(w)\), which is possible in the genuine open carrier annulus. Because the tile projection is deck invariant,

\[
p_W(\tau_i^n z)=p_W(z),\quad
p_W(\tau_i^n w)=p_W(w)
\qquad\text{for every }n\in\mathbb Z.
\]

If a projection-commuting continuous extension \(J\) existed at \(\omega_i^+\), continuity of \(\pi_9\) would force **both different constant** physical points \(p_W(z)\) and \(p_W(w)\) to equal the single value \(\pi_9(J(\omega_i^+))\). Contradiction. The same proof with \(n\to-\infty\) rules out \(\omega_i^-\). This uses only the **actual source KL wrapping prime-end topology**, Hausdorffness of \(T_9\), and source deck invariance. It does not depend on an arbitrary nine-cut connector word, a finite coset table, or a physical ray landing in \(K_9\). \(\square\)

The theorem is an **obstruction to extension into this precise uncompactified target**. It does not rule out a different compactification that adds appropriate infinitely winding boundary objects or a proper-path correspondence that is **not** a single-valued continuous map into \(\widehat T_9\).

## 5. Complete pointwise classification of the *entire original ideal circle* (with strict scope)

By original KL II §3.2.4, \(\partial^{\rm id}\Psi_G(W)\) consists of four \(\lambda_i\) O-arcs, eight \(\xi_i/\eta_i\) J-arcs, the four finite vertices and eight wrapping joints. Applying merged PR #65's **complete strict finite inner J-side trichotomy** and Theorems 2.1, 3.1 and 4.1 yields the complete following **pointwise extension status into the uncompactified fine canonical surface**:

| Exact source ideal point type | Physical/cover status | Limit of the existing fine immersion |
|:--|:--|:--|
| Each finite original O-side \(\lambda_i^\circ\) | Positive-height physical equipotential in \(\Omega_9\) | Unique local ordinary fine-cover extension |
| Each of the four finite J-vertices \(v_i\) | \(v_i\in V_G\setminus K_9\subset\Omega_9\) | Unique ordinary fine-cover extension via W→V source naturality |
| Any strict finite J-side \(\xi_i^\circ,\eta_i^\circ\) landing in \(\Omega_9\) | Ordinary fine exterior | Unique local ordinary-cover extension (merged #65) |
| Any strict finite J-side physically landing on \(K_9\) | Marked root | **Root extension only** at source mate tile, zero deck shift; every other such lift escapes (merged #64–65) |
| Any strict finite J-side physically landing in the omitted \(D_{0,1}\cup D_{0,2}\) | Not in physical target | No fine-target extension, proper escape (merged #65) |
| Any of the eight genuine O/J wrapping joints \(\omega_i^\pm\) | Infinite universal-tile winding | **No** continuous projection-compatible extension into the uncompactified fine target |

**What is genuinely classified:** the **individual pointwise extendibility or obstruction** for every one of the original source-defined ideal boundary prime ends, provided the imported source geometry, local connectivity, canonical-localization and Jordan-wake theorems stated in the cited manuscripts hold. This is not a continuous map simultaneously defined on the *entire* ideal circle (impossible because of actual obstructions), and does not determine all fine prime-end boundary labels in an enlarged target.

## 6. Source validation and remaining research frontier

- KL II original §3.2.1 and Lemma 3.3: actual path classes / universal-cover tile source.
- KL II Lemma 3.4(ii) and §3.2.4, original printed pp. 12–13: naturality inclusion extends continuously to the **original source ideal boundary**, finite vertex \(\eta_i\cap\xi_{i+1}\), infinite winding O/J joints.
- Kahn I §7.4.1 Theorem 7.12: genuine fine canonical marked localization and root-neighborhood conformal chart.
- Already merged archive: `tip_kl_terminal_first_child_20261106.md` (strict W⋐V), `tip_kl_pseudopiece_side_atlas_20261106.md` (actual phase avoidance/side atlas/tail crosscuts), `tip_native_finite_J_side_target_trichotomy_20261109.md` (complete strict J-side case).

**Run at repository root:**

```bash
python research/independent_audits/verify_tip_native_full_W_ideal_circle_types.py --check-manifest
lake build TipNativeFullBoundaryTypes
```

The deterministic checker reads the **actual original 24-tile source side atlas**, verifies the four W true vertex ray pairs and their \(\eta_i/\xi_{i+1}\) incidence, strict distinction from V vertices, eight joint labels and two full-deck ends per source tile, the source outer positive height, and 12 finite O-point checks. It also cross-checks merged #65's strict finite J trichotomy rather than reassigning its physical landing labels. The Lean module verifies only finite source endpoint labels and counts. Neither tool formalizes KL ideal prime ends, source holomorphic naturality, Kahn complex charts or global path topology; the written proofs are explicitly conditional on those cited analytic results.

**Actual remaining frontier:** construct the **full source-defined proper-path/path-subordination groupoid**, genuine prescribed cross-scale path comparison and explicit full nonabelian based \(\Gamma=F_9\) defect words for proof-used paths, or a first source-certified failure, **in a target category allowing the appropriate compactified ends**. Merely extending into the uncompactified target is now completely classified pointwise but does not establish unique proper restriction. No promotion of H1–H4, UPTCR, MLC or the 465-entry ledger; specialist analytic review remains necessary. GPT-6 assisted research, exact checker and source comparison; originality/priority and specialist validity remain unestablished.

# Research Push III: adversarial assessment and corrected integration

## 1. Verdict

Research Push III contains four useful analytic/formal advances and one
decisive new obstruction.  It does **not** prove the proposed adaptive
nodal-response theorem, direct-decoration finite-horizon inflation, strict
transition transfer, or planar-free finite-interface execution.

The material adopted after independent reconstruction is:

1. a normalized direct limit of the already realized finite-cylinder copies
   of an independently supplied root portrait, together with its normalized
   shift;
2. exact materialization of a finite shift-graded diagram whose root maps,
   squares, and chart-supported records have already been realized;
3. exact conformal invariance of fully transported extremal-length and
   finite-electrode response data; and
4. the extremal-length series bound under an explicit serial-exhaustion
   hypothesis.

The direct limit is canonically the root portrait in a changing coordinate.
It is not a planar infinite-address component, a new virtual return, or a
relative-cover realization.

The packet's principal new quantitative step fails at the proof level.  A
cut cross-section carries an \(H^{1/2}\) boundary trace, not one scalar
"attachment value."  The scalar two-terminal conductance controls only the
constant trace mode.  The exact cylinder calculation in Section 7 shows that
nonconstant modes are not bounded by that conductance.  A replacement theorem
must control the full trace response (or prove an exact equipotential
collapse) before any response-error, finite-horizon, or transition claim can
be promoted.

No global open obligation is promoted.  In particular,
`FINITE_HORIZON_ASSEMBLY`, `MAPPING_TELESCOPE`,
`H1_FINITE_HORIZON_INFLATION`, `H2_RESPONSE_REALIZATION`, VAAPC-I, UPTCR,
and MLC remain open.

## 2. Artifact lock and reproduction

The supplied archive was copied without modification to

```text
research/mlc_unified/external_inputs/push_3_20260725
```

The original archive has SHA-256

```text
D6A2B5074CF55AB7983AE0E835A4F38B5388DFB4043B3A57E254C9A6EED2DD62
```

The checked extracted inventory is:

| Artifact | SHA-256 |
|---|---|
| `mlc_ledger_patch_push_3.json` | `093A56A0A1D26AB93C85B7446BC75DE5C8BE5312BD110234BEEC3AED29100347` |
| `mlc_manuscript_insertions_push_3.pdf` | `DF8BEC2E1DD9C98B83608C64357F7280973F3B5ABC7F533CE5F627C74E565BE7` |
| `mlc_manuscript_insertions_push_3.tex` | `6D20EE9213D01C0737DB390658B795D2B77333398567FF4BB9FEBD06B16F39A3` |
| `mlc_research_push_3.md` | `3E35915426F9EF0D75F32223F93311A4FB4D52EB0CB052AF515B87E0963ED1C0` |
| `plumbing_response_audit.py` | `C6B2B7F18721B4DAC2E0FCAD31C9CFCE717EBDD6A27359C3AB3B2EB3F8FB8E8B` |
| `plumbing_response_audit_stdout.txt` | `A4CB857C0141960938DE63FBA58BA88F74B16C08FA8940571C9EE9EC1BB5A9BA` |
| `plumbing_response_report.json` | `A4CB857C0141960938DE63FBA58BA88F74B16C08FA8940571C9EE9EC1BB5A9BA` |
| `README_PUSH3.txt` | `9CE4268A32A80C52217A1F7C5CFEABE621A37F75340EE77CED75243CA5603B74` |
| `SHA256SUMS.txt` | `C36365A9EF0D52FEB178C63DE99263FE1D481350E331BEA446D8C8972BF152F1` |

Every bundled hash agrees with `SHA256SUMS.txt`.  The supplied finite-network
script was rerun for 250 randomized trials and reproduced its qualitative
result.  It tests finite scalar conductance graphs only.  It has no
representation of a cross-section trace space and therefore cannot test the
analytic gap in Section 7.

The supplied PDF was text-extracted and all seven pages were rendered and
visually inspected.  It is cleanly typeset.  `README_PUSH3.txt` calls it a
six-page note; the actual PDF and TeX output have seven pages.  This is a
packaging defect, not a mathematical one.

## 3. Source and dependency boundary

The packet was compared with:

- the locked Kahn--Lyubich direct-decoration source and the existing
  `DIRECT_DECORATION_PULLBACK_COMPACTIFICATION`;
- Dudko's virtual-hull discussion in arXiv:2512.24171;
- Kahn--Kapiamba--Lyubich's scope statement in arXiv:2606.27272;
- `critical_chronology_and_retimed_telescope.md`;
- `finite_horizon_inflation.md`;
- `network_response_state.md`;
- `bc1_finite_port_response.md`; and
- the authoritative `proof_obligations.json`.

The public sources support actual first-decoration puzzle pullbacks in their
native setting.  They do not supply a virtual scale-two root portrait,
complete protected marking, relative-cover telescope, or arbitrary
virtual-Molecule finite-horizon assembly.

Three dependency names in the supplied ledger patch are stale or absent:

| Supplied name | Authoritative status |
|---|---|
| `FINITE_CYLINDER_SECOND_PORTRAIT_TRANSFER` | absent; the narrow proved result is `RETIMED_FINITE_CYLINDER_PAIR` |
| `NORMALIZED_END_GERM_CONSTANCY` | absent; the narrow proved result is `NORMALIZED_RETIMED_GERM_CONSTANCY` |
| `MARKED_FINITE_HORIZON_ASSEMBLY` | absent; `FINITE_HORIZON_ASSEMBLY` is present and open |

The patch is therefore not schema-safe or dependency-safe.  In particular,
renaming `FINITE_HORIZON_ASSEMBLY` does not discharge its open
relative-cover, prime-end, properness, and end-properness clauses.

## 4. Correct normalized end theorem

Let \(P,Q_a,g,\phi_a\) be an already realized direct-decoration inverse
system, let \(F:A\to B\) and \(\jmath:A\hookrightarrow B\) be an
independently realized root pair with \(A\Subset P^\circ\), and let

\[
 h_w=g^{|w|}|_{Q_w}:Q_w\longrightarrow P,\qquad
 A_w=h_w^{-1}(A).
\]

For a fixed infinite address \(\omega\), write \(w_m=\omega|m\) and define

\[
 t_m=(h_{w_{m+1}}|_{A_{w_{m+1}}})^{-1}
          \circ h_{w_m}|_{A_{w_m}}.
\tag{4.1}
\]

### Theorem 4.1 (`NORMALIZED_END_DIRECT_LIMIT`)

The direct system \((A_{w_m},t_m)\) has a canonical Riemann-surface direct
limit \(\widehat A_\omega\), and the maps \(h_{w_m}\) induce a
biholomorphism

\[
 h_\omega:\widehat A_\omega\longrightarrow A.
\tag{4.2}
\]

The retimed pairs descend to

\[
 \widehat G_\omega=F\circ h_\omega,\qquad
 \widehat I_\omega=\jmath\circ h_\omega.
\tag{4.3}
\]

Every record explicitly defined by pullback under \(h_{w_m}\) descends and
is exactly the corresponding root record.  This conclusion constructs no
map from \(\widehat A_\omega\) to the planar impression \(E_\omega\).

#### Proof

Define \(\widehat A_\omega\) as the quotient of
\(\bigsqcup_m A_{w_m}\) by the equivalence relation generated by
\((z,m)\sim(t_mz,m+1)\).  Equation (4.1) gives

\[
 h_{w_{m+1}}(t_mz)=h_{w_m}(z).
\tag{4.4}
\]

Hence

\[
 h_\omega([z,m])=h_{w_m}(z)
\tag{4.5}
\]

is well defined.  For any \(y\in A\), the point
\((h_{w_m}|_{A_{w_m}})^{-1}(y)\) represents the same equivalence class at
every level, so (4.5) is onto and one-to-one.  Use (4.5) as the global
chart on the quotient.  This makes \(\widehat A_\omega\) Hausdorff and
turns \(h_\omega\) into a biholomorphism; it avoids any unsupported general
claim about quotients of Riemann surfaces.

The finite retimed maps are \(F\circ h_{w_m}\) and
\(\jmath\circ h_{w_m}\).  Equation (4.4) proves compatibility, so they
descend and give (4.3).  A pulled record has the form
\((h_{w_m})^{-1}R\); (4.4) proves its compatibility, and (4.2) identifies
it with \(R\).  Nothing in this construction defines a planar projection
to \(E_\omega\). \(\square\)

### Proposition 4.2 (normalized shift)

Deletion of the first address symbol induces a biholomorphism

\[
 \widehat S_\omega:
 \widehat A_\omega\longrightarrow\widehat A_{\sigma\omega}
\]

with

\[
 h_{\sigma\omega}\circ\widehat S_\omega=h_\omega.
\tag{4.6}
\]

Thus the shift is the identity in root coordinates, while still retaining
its actual dynamical label \(g=f^q\).

#### Proof

For \(w=a_1\cdots a_{m+1}\), the inverse-branch convention gives

\[
 g\circ\phi_w=\phi_{a_2\cdots a_{m+1}},
\]

and therefore

\[
 h_{a_2\cdots a_{m+1}}\circ g=h_w
\tag{4.7}
\]

on the relevant pulled domain.  Equation (4.7) is compatible with (4.1)
on the cofinal subsystem of positive levels.  It induces the stated map,
and (4.6) proves bijectivity and holomorphicity. \(\square\)

## 5. Finite shift-graded materialization

### Theorem 5.1 (`DEPTH_GRADED_CYLINDER_MATERIALIZATION`)

Let \(\mathcal D\) be a finite diagram built from:

1. actual composable root restrictions and actual root commuting squares;
2. geometric presentation changes;
3. forward address shifts; and
4. records already certified to be natural under the relevant root charts.

Assume the vertices carry an integer grading \(s\) preserved by root and
presentation edges and satisfying \(s(u)=s(v)+1\) on every forward shift
\(u\to v\).  Then one integer \(M\) realizes vertex \(v\) at cylinder
depth \(M+s(v)\).  Every dynamical edge is an actual polynomial iterate,
every presentation edge remains a separately typed conformal coordinate
change, and every already certified root square still commutes.

This theorem does not construct a root restriction, prime-end action,
relative cover, protected carrier, or finite-horizon assembly.

#### Proof

Choose \(M\ge-\min_v s(v)\).  Pull the complete supplied root datum at
\(v\) back by the cylinder chart of depth \(M+s(v)\).  Equal grades put
the endpoints of root and presentation edges at equal depth, so their
actual root formulas and squares pull back verbatim.  Across a shift edge,
the source depth is one greater than the target depth; (4.7) therefore
realizes the edge by \(g=f^q\).  Since the diagram is finite, compact
containment of all supplied root domains is preserved by one common \(M\).
Composition of actual restrictions is an actual iterate on its stated
nonempty domain.  No unsupplied analytic structure is created. \(\square\)

The grading condition is necessary for a single physical presentation.  If
two paths identify the same vertex after different net numbers of shifts,
that vertex would require two distinct depths.  Duplicating the vertex
unfolds the diagram; silently identifying the two presentations does not.

## 6. Conformal observables and the conditional series law

### Theorem 6.1 (`END_CHART_OBSERVABLE_INVARIANCE`)

Under the biholomorphisms in Section 4, every fully transported curve family
has the same extremal length.  Every finite smooth-electrode surface, with
electrode order transported by the same chart, has the same
Dirichlet-to-Neumann response matrix.  Algebraic parallel sums and
Schur-complement eliminations commute with these identities.

#### Proof

In real dimension two, both extremal length and Dirichlet energy are
conformally invariant.  The response matrix is the quadratic form obtained
by minimizing that energy over the fixed electrode trace class.  A marked
conformal bijection identifies the two admissible classes and preserves
their energies, hence the quadratic forms and matrices agree.  Parallel
addition and Schur complementation are deterministic algebraic operations
on the equal matrices. \(\square\)

The qualification "fully transported" is essential.  The theorem does not
show that the number of electrodes is bounded, that a port quotient is
future closed, or that KKL Value is determined by the response.

### Theorem 6.2 (`SERIAL_EXHAUSTION_RESISTANCE_BOUND`)

Let \(C_1,\ldots,C_m\) be pairwise interior-disjoint quadrilaterals in a
marked localization.  Suppose every curve in a family \(\Gamma\) contains,
in order, a subcurve crossing each \(C_j\) between its declared horizontal
sides.  If \(R_j\) is the extremal length of that crossing family, then

\[
 \operatorname{Ext}(\Gamma)\ge\sum_{j=1}^m R_j.
\tag{6.1}
\]

Consequently its reciprocal conductance, when defined, is at most
\((\sum_jR_j)^{-1}\).

#### Proof

For each \(j\), choose an admissible metric \(\rho_j\) for the crossing
family in \(C_j\), normalized so every crossing has \(\rho_j\)-length at
least \(1\).  For positive numbers \(a_j\), put
\(\rho=\sum_j a_j\rho_j\), extending each metric by zero.  Every
\(\gamma\in\Gamma\) has \(\rho\)-length at least \(\sum_j a_j\), while
interior disjointness gives

\[
 \operatorname{Area}(\rho)=
 \sum_j a_j^2\operatorname{Area}(\rho_j).
\]

Optimizing first over approximating extremal metrics and then over
\((a_j)\), with \(a_j\) proportional to \(R_j\), gives (6.1).  This is the
extremal-length series law. \(\square\)

Equation (6.1) is conditional on the no-bypass, intact-wall, intact-cell
hypothesis.  The bundle does not source-lock that hypothesis for every
direct-decoration or virtual-Molecule corridor.

## 7. Exact obstruction to scalar nodal response

The proof of Push III Theorem 17 says that a minimizer on a cut component
has one "free attachment value."  This is false for an ordinary cut
cross-section.  Its trace is a function, and the natural cut condition is
Neumann, not equipotential Dirichlet.

The missing modes can be seen exactly on the flat cylinder

\[
 C_L=[0,L]\times(\mathbb R/2\pi\mathbb Z).
\]

For the constant boundary values \(1\) at \(x=0\) and \(0\) at \(x=L\),
the minimizer is \(1-x/L\), with energy

\[
 E_0(L)=\frac{2\pi}{L}.
\tag{7.1}
\]

This is the scalar two-terminal conductance used in the packet.

For the trace \(\cos(k\theta)\) at \(x=0\) and \(0\) at \(x=L\), the
harmonic minimizer is

\[
 u_k(x,\theta)=
 \frac{\sinh(k(L-x))}{\sinh(kL)}\cos(k\theta).
\tag{7.2}
\]

Green's identity gives

\[
 \begin{aligned}
 E_k(L)
 &=\int_{C_L}|\nabla u_k|^2\,dA\\
 &=\int_0^{2\pi}
      u_k(0,\theta)\bigl(-\partial_xu_k(0,\theta)\bigr)\,d\theta\\
 &=\pi k\coth(kL).
 \end{aligned}
\tag{7.3}
\]

Thus \(E_0(L)\to0\), while \(E_k(L)\to\pi k\).  In particular, no estimate
of the form

\[
 E(\varphi)\le C\,E_0(L)\operatorname{osc}(\varphi)^2
\tag{7.4}
\]

with \(C\) independent of \(L\) can hold for arbitrary interface traces.
For \(\varphi=\cos\theta\), the left side is at least \(\pi\), whereas the
right side tends to zero.

### Theorem 7.1 (`SCALAR_NECK_TRACE_MODE_NO_GO`)

Constant-mode two-terminal conductance does not control the energy of
arbitrary boundary traces across a long analytic neck.  Therefore a scalar
conductance graph cannot by itself justify replacing cut analytic
interfaces by scalar nodes.

#### Proof

Equations (7.1)--(7.4) are an explicit counterexample. \(\square\)

This result attacks the proof mechanism, not every possible nodal-limit
theorem.  A valid replacement may still hold if one proves one of:

1. every proof-used interface is an actual equipotential electrode, so only
   the constant mode is admissible;
2. the nonconstant trace modes have a uniformly summable Dirichlet-to-Neumann
   bound after the chosen cut; or
3. the state retains the required finite- or infinite-dimensional trace
   response rather than collapsing it to one scalar.

The corresponding open obligation is
`END_PLUMBING_TRACE_RESPONSE_CONTROL`.

## 8. Claim-by-claim disposition

| Push III claim | Disposition | Reason |
|---|---|---|
| `VIRTUAL_END_DIRECT_LIMIT` | **Adopt, renamed and narrowed** | `NORMALIZED_END_DIRECT_LIMIT` is a coordinate direct limit of an independently supplied root pair; it is not a planar virtual component. |
| End-shift naturality | **Adopt inside the narrow theorem** | Exact under the inverse-word convention; dynamics and presentation depth remain separately typed. |
| Closed support relation | **Mathematically valid but no new promotion** | It repackages the already proved compact rooted-end component package and does not select a planar point or analytic end return. |
| `DEPTH_GRADED_END_DIAGRAM_REALIZATION` | **Adopt, renamed and narrowed** | Exact only for already actual root restrictions, squares, and chart-supported records; it constructs no relative cover or marked assembly. |
| `INTRINSIC_FINITE_PSEUDOPUZZLE_ATLAS` | **Hold** | External marking does not by itself prove the stated separation, landing/cofinality, niceness, first-return, and source-authorization clauses. |
| `RECURSIVE_FIBERED_PORTRAIT_COMPILER` | **Hold** | It depends on the held atlas theorem and assumes the next localized renormalization. |
| `DIRECT_DECORATION_FIBER_RESPONSE_IDENTITY` | **Adopt, renamed and narrowed** | Exact for observables whose complete definitions are transported by a marked conformal isomorphism. |
| `DIRECT_DECORATION_SERIAL_NECK` | **Adopt only as a conditional abstract series theorem** | The series law is correct; universal source realization of intact no-bypass walls and cells is not proved. |
| `ADAPTIVE_NODAL_RESPONSE_APPROXIMATION` | **Reject as proved** | The argument collapses a functional trace to a scalar.  Section 7 gives the exact missing-mode obstruction. |
| `DIRECT_DECORATION_PROTECTED_END_MATERIALIZATION` | **No new promotion** | Existing `DIRECT_DECORATION_FINITE_PROTECTED_CARRIER` covers finite isolated packets under its precise port hypotheses.  Compatibility with every neck cross-section is asserted, not proved. |
| `DIRECT_DECORATION_FINITE_HORIZON_INFLATION` | **Reject as proved** | It invokes open `FINITE_HORIZON_ASSEMBLY` and the failed nodal-response step. |
| `DIRECT_DECORATION_STRICT_TRANSITION_TRANSFER` | **Reject as proved** | It depends on the failed response bound and does not state the exact input/output perturbation alignment needed by the one-sided gauge estimate. |
| `PLANAR_FREE_FINITE_INTERFACE_EXECUTION` | **Reject as proved** | It depends on the rejected carrier/response/assembly chain. |
| Deletion of planar component identification from the critical path | **Reject** | The proposed alternative execution theorem is not proved, so no dependency deletion follows. |

## 9. One-sided transition audit

The error-stability inequality

\[
 L(Z+\Delta)\le L(Z)+C_L\|\Delta\|
\tag{9.1}
\]

controls an explicitly identified output perturbation.  It does not relate
an arbitrary physical input \(Z_{\rm in}^{\rm vir}\) to the root input
\(Z_{\rm in}\).  A corrected transfer lemma must state and prove either

\[
 Z_{\rm in}^{\rm vir}=Z_{\rm in},
\qquad
 Z_{\rm out}^{\rm vir}=Z_{\rm out}+\Delta_{\rm out},
\tag{9.2}
\]

or a two-sided input/output stability estimate in the directions required
by the contraction inequality.  Push III does not make (9.2) part of the
theorem's hypotheses.  Even after this typing repair, transition transfer
still depends on `END_PLUMBING_TRACE_RESPONSE_CONTROL` and on an
independently proved strict root alternative.

## 10. Ledger and manuscript decision

The authoritative ledger records the four narrow positive tools and the
trace-mode no-go theorem as proved.  It records
`END_PLUMBING_TRACE_RESPONSE_CONTROL` as open and adds it to
`H2_RESPONSE_REALIZATION`.

No supplied Push III theorem is copied verbatim into the manuscript.  The
integrated section:

- proves the normalized direct limit by a global root chart;
- states exactly which finite diagrams can be materialized;
- keeps source authorization and relative-cover assembly open;
- gives the conditional series law;
- includes the cylinder trace-mode counterexample; and
- rejects all downstream response, transition, and MLC promotions.

The finite graph script and the new cylinder regression are diagnostic
checks only.  The proofs above, not those computations, determine ledger
status.

## 11. Net advance and immediate next theorem

The valid advance is a precise normalization tool:

\[
\text{already realized finite-cylinder portraits}
\quad\Longrightarrow\quad
\text{one exact root-coordinate direct system}.
\]

It removes no source-facing construction gate.  The new obstruction sharpens
the response problem:

\[
\boxed{
\text{control the full analytic trace response of each materialized neck,}
}
\]

either by an exact electrode-collapse theorem or by a uniform
Dirichlet-to-Neumann mode estimate compatible with the protected carrier and
future-observable port state.

Only after that theorem is proved may the nodal-response approximation be
revisited.  The independent source authorization, marked finite-horizon
assembly, mixed strict transition, coercivity, and rigidity gates remain
open.  Consequently the manuscript continues to make no unconditional MLC
claim.

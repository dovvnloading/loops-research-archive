# Issue 29: resolution by an actual canonical sheet collision

**Date:** 2026-11-06. **Disposition:** the explicit source-defined
fiber/side/coset-collision alternative in
[Issue #29](https://github.com/dovvnloading/loops-research-archive/issues/29).
This is a finite two-scale negative resolution with supporting positive
geometry. It is not a faithful all-scale transport theorem or a promotion
of a source-locked MLC obligation.

## 1. The decisive comparison and its failure

At the exact certified nonattracting parameter, let `K9⊂K3` be the filled
sets of the degree-two returns `f^9` and `f^3`. The
[canonical comparison theorem](tip_iterated_direct_canonical_localization_embedding_20261106.md)
constructs the following actual surfaces and maps:

| Object or map | Definition and proved property |
| --- | --- |
| `V3` | Canonical period-three target, with full coarse root `K3` |
| `T_it⊂V3` | Remove the two noncentral inner phase roots and mark the remaining smaller root `K9` |
| `rho:V_(3,3)→T_it` | The next canonical localization, retaining `K9` on both sides |
| `J:V_(3,3)→V9` | Canonical comparison with the direct period-nine target; a strict open holomorphic embedding |
| `U=J(V_(3,3))⊂V9` | The canonically specified open fine domain, containing its entire marked root |
| `L=rho∘J^(-1):U→T_it⊂V3` | A genuine source-defined fine-to-coarse-ambient local cover |
| `P=Psi_(canonical G)(P_G)` | Native KL pseudo-piece for the actual canonical coarse map, using its full native annular tiles |
| `e_dir:P→U` | The canonical localized immersion, satisfying `L e_dir=Pi`, where `Pi` is the native pseudo-piece projection followed by the inclusion immersion |

The target marking of `L` is **the smaller root `K9`**. This is Kahn's
canonical renormalization convention, even though its ambient surface is
the period-three surface.

Choose either native tile of `P`, its positive deck generator `t`, and
any interior tile point `z`. Theorem 7.1 proves that the points

\[
e_{\rm dir}(t^n z),\qquad n\in\mathbb Z,
\]

are pairwise distinct actual canonical period-nine sheets, while

\[
\mathcal L(e_{\rm dir}(t^n z))=\Pi(z)
\qquad\text{for every }n\in\mathbb Z.
\]

The exact based subgroup is `H=<b_(0,0)>` in the free group `F0` on the
three inner meridians. A positive native tile core winds once around
**each** of the three inner roots. No nonzero power can lie in a
conjugate of `H`, because its winding about the second inner root is
nonzero. This proves the all-integer sheet separation; the native
projection's deck invariance proves the collision. The proof retains
the full coset fiber and transport along every path.

The actual native tile's infinitely wrapping joints are

\[
\omega_i^-=\lambda_i\cap\xi_i,\qquad
\omega_i^+=\lambda_i\cap\eta_i.
\]

Here `lambda` is the KL outer boundary, and `xi,eta` are its Julia-side
arcs. Theorem 8.1 proves that `L e_dir` cannot extend continuously at
either joint. Two deck orbits approach the same source joint while
their images remain distinct constant interior points of `V3`.

The source object is the **native coarse-stage pseudo-piece immersed
into the actual fine canonical surface**. The proof does not rename it
a native fine-stage pseudo-piece or assume that `e_dir` extends to a
separately identified fine prime end. The failure concerns the displayed
whole-mark diagram and the actual fine-sheet fiber of `L`.

## 2. Every objective and its evidence

| Issue objective | Resolution and evidence | Exact boundary |
| --- | --- | --- |
| 1. Same-parameter holomorphic geometry | [Complex 3/9 certificate](nonattracting_tip_complex_two_scale_20261106.md): proper degree-two restrictions, nested Jordan domains, connected roots and separated phases at the nonattracting tip | Written Rouché/Riemann–Hurwitz arguments interpret deterministic margins; these are not all formalized in Lean |
| 2. Source KL stopping/nest and closed pieces | [Top puzzle](kl_tip_primitive_puzzle_and_localization_20261106.md) and [terminal first child](tip_kl_terminal_first_child_20261106.md): `q=2,n=1`, `P=Y1`, `V0=Y3`, `W=Y6`, `chi=1`, exact `QL,QR`, and the same `K3,K9` as the complex restrictions | Stage return three is distinguished from physical returns three/nine |
| 3. Landed rays, accesses and sides used in the proof | [Ambient ray tree](tip_puzzle_ray_tree_20261106.md), [internal-to-ambient lifts](tip_internal_puzzle_ambient_lifts_20261106.md), and [side atlas](tip_kl_pseudopiece_side_atlas_20261106.md): two depth-six landed tables and all 24 ordinary tiles for `P,QL,QR,V0,W` at both stages | Rational labels are topological accesses; the native comparison transfers their ordered endpoints through the embedded root collar, without inventing a global physical conformal angle coordinate |
| 4. Source-defined cover/groupoid and a faithful map or explicit collision | [Canonical comparison](tip_iterated_direct_canonical_localization_embedding_20261106.md), §§2–8: same-root map, complete based fiber/path naturality, strict embedding `J`, actual projection `L`, native lift, infinite fine-sheet collision and named-joint failure | **Negative alternative satisfied.** No faithful whole-mark extension is claimed; the fiber collision is not categorical nonfaithfulness on fixed-endpoint homotopy classes |
| 5. Independent old-center identity | [Center-identification theorem](period27_center_tuning_identification_20261106.md): the certified period-27 center belongs to `A*A*A`, using the precise real-center root-ray result and tuning theorem | That distinct superattracting center still fails Paper 2's local `K=J` hypothesis |

The table is an acceptance map for the issue, not a replacement for the
complete proofs in the linked notes.

## 3. Two additional distinctions now proved

The [root-topology theorem](tip_interval_root_and_marked_morphism_obstruction_20261106.md)
proves the exact equality

\[
K_9=[x_9,x_{18}],\qquad x_{18}=-x_9,
\]

and exhibits a four-arm embedded star in `K3`. A compact source root of
a nonconstant holomorphic Kahn marked morphism maps onto its connected
target root. Pulling back the star would force branching inside an
interval. Thus **no holomorphic marked morphism with full source root
`K9` and full target root `K3` exists**, in any neighborhoods of the
full roots. Every physical iterate also fails the inverse-root condition
already as a germ at zero. This obstruction is distinct from the valid
smaller-root projection in §1.

The [access-lift theorem](tip_localization_access_lifts_and_germ_alignment_20261106.md)
also closes an interpretation gap in the earlier common-exterior
argument. Its annular comparison has two open boundary intervals and
integer-valued access lifts, but lifting its target to a universal tile
gives a biholomorphism. Its annular fibers alone were therefore not a
named KL tile collision. The native construction in §1 supplies the
additional source identification instead of assuming it.

## 4. Reproduction, sources and review boundary

The two new deterministic certificates are:

```bash
python research/independent_audits/verify_tip_root_topology.py --check-manifest
python research/independent_audits/verify_tip_kl_side_atlas.py --check-manifest
```

Their manifests record [all nine exact interval phases](../../results/tip_root_interval_geometry.json)
and the [24-tile ordinary side atlas](../../results/tip_kl_side_atlas.json).
The research workflow runs these alongside the existing interval, ray,
nest, provenance and Lean checks. Python verifies finite arithmetic and
manifest reproduction. The open mapping, straightening, all-word
free-product, localization and prime-end arguments remain written
analytic proofs; green CI is not a formalization of those proofs.

The [version-locked source audit](tip_kl_marking_source_types_20261106.md)
records the inspected PDFs, hashes and corrected printed page numbers.
The decisive source inputs are Kahn I v3, marked-pair definitions on
p. 43, Theorem 7.12 on p. 44, and the nested-period construction in
Theorem 7.13(2) on pp. 45–46; and KL II, pseudo-pieces and naturality
on pp. 11–13, with the boundary definitions in §3.2.4 on p. 13.
The extra strict embedding and collision arguments are proved in the
new note and are not attributed as statements of those sources.

**What remains open:** a separately specified protected comparison away
from the named wrapping joints, or a transition retaining additional
unwrapped data, may behave differently. No universal no-go theorem for
all such choices is asserted. The global marked carrier, quantitative
calibration, coercivity, rigidity, UPTCR and MLC remain open at their
source-locked statuses. The 465-entry ledger is unchanged.

**Attribution:** the cited authors supply the imported theory. OpenAI
GPT-6 Astra Pro assisted the new proof development, source comparison,
code and exposition. Separate AI agents cross-checked the map typing,
root obstruction, double-coset embedding and native endpoint argument.
No independent human specialist review or source-author endorsement is
represented.

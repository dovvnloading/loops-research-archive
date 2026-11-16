# Native Wave Transfer Laboratory — additive primitive record v1.1

**Compatibility contract.** This file defines an *additional*, explicitly tagged
real-slit experiment. It does not modify §SPECIFICATION.md§ (v1), its registry,
§regenerate.py§, §regenerate_period4.py§, any old fixture, or any old manifest.
The satellite §SPECIFICATION_v2_satellite.md§ remains independent. The source
and proof status for **each new output leaf** are machine-checked in
§source_contracts/primitive_v1_1_field_sources.json§. The read-only checker is
§regenerate_primitive_v1_1.py --check§; an explicit reviewed §--write§ alone
updates §experiment_manifests/near_parabolic_primitive_v1_1.json§.

## 1. Which "small" intervals? Three different maps must not be conflated

Write §f=f_c(z)=z²+c§, §G=f^p:V_p→U_p§, and
§K_0=K(G)§. For the three already certified parameter intervals §p=24,27,30§,
the old exact checker proves that §G§ has restricted degree two,
§K_0=[-a,a]§ (identification of the *whole* little Julia set uses the
explicitly noted analytic backward-density/straightening input),
§G(0)=-a§, §G(±a)=a§ and
§G^{-1}(K_0)∩V_p=K_0§. It proves pairwise disjoint enclosures for the
**ambient** sets §K_j=f^j(K_0)§, §0≤j<p§. Thus their ambient arity is §p§,
while the **inner G-return** has **one** invariant Chebyshev interval.
Neither number is automatically the number of vertices of a KKL
§f§-Hubbard tree.

Sources: [KKL arXiv:2606.27272v1, §2.3](https://arxiv.org/abs/2606.27272v1)
defines a renormalization of period §p§, its *primitive* disjointness and
its separate *prime* condition (no smaller period);
[Lyubich, Dynamics of Quadratic Polynomials, I–II, Part II §9,
renormalization definitions](https://www.math.stonybrook.edu/~mlyubich/Archive/Selected/puzzle.pdf)
and [Kahn–Lyubich, *A priori bounds for some infinitely renormalizable quadratics: III. Molecules*, §§1, 2.2](https://arxiv.org/abs/0712.2444)
distinguish primitive from satellite combinatorics. Disjoint phase balls
are a physical primitive witness, **not** a proof of prime combinatorics
or the hypotheses of every KKL ψ-ql theorem.

[KKL §2.5](https://arxiv.org/abs/2606.27272v1) defines the Hubbard hull
§T§ as the smallest connected set containing the **cycle**
§∪_j f^j(K_0)§, and marks the *entire* component sets
of §K̂§ as vertices; its edges are components of §T\K̂§.
Its Perron matrix is induced by **both** §f§ and §ι§ and assumes the
primitively *renormalizable*, periodically repelling ψ-ql setting.
It is **not** the same as the degenerate **local return-slit hull**
§T_G=K_0§. For the present three tips we certify
§T_G'=G^{-1}(T_G)∩V_p=T_G§, hence **zero local return-slit
attachments and zero local complementary edges**. We do **not** infer
that the ambient KKL §T_f§ has no edges/attachments, nor manufacture a
KKL §T_F§ matrix or a Perron root from a 0-by-0 matrix.

## 2. A reproducible **chosen** ideal marking, not an invented canonical one

For the real-slit complement §U_p\K_0§ the inner Carathéodory circle
has an upper and a lower open side, separated by the two tip accesses.
Choose these as **two target open ideal intervals** §I_upper,I_lower§.
Its outer ideal-boundary component is a **single whole-circle interval**.
The source marking is the covering pullback (§f_*§ of KKL §6.1§):
the inverse of the two target side intervals under §G§ consists of
**four** intervals, in cyclic real-slit order

```text
S_upper_negative, S_upper_positive, S_lower_positive, S_lower_negative.
```

Here "negative" and "positive" refer to the real half of §K_0§
bordered by the access. The return has one critical turn at §0§,
with §G'<0§ on §(-a,0)§ and §G'>0§ on §(0,a)§, because all
noncentral critical phase disks exclude 0 and §G(0)=-a<G(a)=a§.
Consequently, with target order upper=0, lower=1, the **covering**
§f_*§ has §source_to_target=[1,0,1,0]§ (orientation reverses on
the negative half). Each target side has two covering preimages.

The **immersion pullback** §ι^*§ is **not this covering table**.
For the physical inclusion
§ι:V_p\K_0↪U_p\K_0§, the upper target side pulls back to the
connected cyclic pair §[S_upper_negative,S_upper_positive]§ and the
lower to §[S_lower_positive,S_lower_negative]§; thus its source-side
labels are §[0,0,1,1]§. KKL §6.1, Proposition 6.5 identifies an
§ι^*§ block with the inclusion preimage **plus the complete Carathéodory
boundary of each new tree component attached there**. As the *local
return-slit* §T_G'\T_G§ is empty, this model has no added component
boundary. Proposition 6.6 establishes refinement in its stated KKL
setting. The finite four-atom local table is obtained by the explicit
real-slit side convention and the return dynamics; it is **not** claimed
as a canonical full §f§-ambient KKL marking.

Citations by changed field:

| v1.1 field | Mathematical justification / limit |
| --- | --- |
| §members[].ambient_phase_count§, §inner_return_interval_count§ | KKL §2.3 (small Julia images); existing exact near-parabolic manifest §finite_selected_members§ |
| §members[].local_hull§, §preimage_local_hull§, §local_attachment_count§ | exact return-inverse exhaustion in §regenerate_near_parabolic.py:certify_member§; KKL §§2.5, 6.1 for **analogous** hull and attachment definitions |
| §members[].ideal_boundary.*§ | chosen upper/lower real-slit marking; KKL Appendix A.1 (an ideal marking is a freely refinable partition into open boundary intervals) |
| §members[].operations.covering_f_star.*§ | strict degree-two certificate and branch signs; KKL §6.1's covering action |
| §members[].operations.immersion_iota_star.*§ | actual source inclusion, no local attachments; KKL §6.1, Propositions 6.5–6.6 |
| §members[].local_edges.*§ | empty complement §T_G\K_0§; KKL §2.5 defines edges of a *different*, ambient tree |
| §members[].restrictions.*§ and §members[].wave.*§ | KKL Appendix A.1 and A.3.2–A.3.4 require specified full proper paths and actual marked waves |
| §members[].collar.*§ and §members[].resistance.*§ | old strict Rouché subcollar; [archive annular contact-resistance theorem](../independent_audits/kkl_annular_contact_resistance_crossover_20261107.md), §1 and §6, explicitly *conditional* on a full attachment electrode |
| §members[].parameter_bracket.*§ and §members[].complex_certificates.*§ | immutable §near_parabolic_primitive_tips.json§ and its outward §2^-256§-dyadic recomputation |

The machine registry elaborates each output **leaf**, source ID, type and status.
All local atom counts are exact *given the stated slit-Carathéodory
identification and declared cut*, rather than canonical or universal
counts. Adding even one extra cut legitimately changes the count; v1.1
must never silently present 2/4 as a marking-independent invariant.

## 3. Source-imposed refusals (null is neither zero nor false)

The one-interval local model has no nontrivial complementary **local**
edge, so its finite local edge-incidence matrix is the empty 0-by-0
matrix (§[]§), with no Perron eigenvalue. **The actual ambient KKL old-edge
matrix and Perron root are not computed** and are recorded as §null§;
an empty 0-by-0 matrix does not have eigenvalue 0.
The two local inner side intervals have zero incidence with *local*
complementary edges; whether either is a **closed KKL Wave crest**
is **undetermined**.

No target proper path with fully specified ideal endpoints, homotopy
class and source path family has been supplied for these tips.
A local degree-two covering has two unramified side lift *germs*,
and inclusion has one germ; these **are not** the filtered
§2-versus-1§ multiplicities of the old crossing/avoiding circles.
KKL Appendix A.1/A.3.2 filters short intervals and same-block
restrictions of **whole paths**, so filtered multiplicities, parent
and child Wave families, exact Wave widths and harmonic equality
are all §null§, not §0§ or §false§. No assertion of width
degeneration is justified by a Rouché lower margin alone.

For every §p§, the outward arithmetic proves §V_p⊂D(0,7R_p/8)§,
hence the **ordinary quadratic-like annulus** has modulus
at least §log(8/7)/(2π)§. This is *not* an enclosure for
the KKL **attachment** collar height §h§. With **zero local
new attachments** no nonempty attached Carathéodory electrode
has a defined angular width §0<ell<π§. The model's §h§, §ell§
and §h*log(1/ell)§ are §null§ (never substitute §ell=0§).
The archive's [contact-resistance crossover](../independent_audits/kkl_annular_contact_resistance_crossover_20261107.md)
is a theorem for a separately specified free-outer Neumann condenser,
**not** an identity for canonical Waves. No three-point correlation
or width-degeneration claim is made.

## 4. Why v1 is exactly preserved

The contract is a **disjoint tagged union**, not a migration of its
semantics: legacy §mode="v1-three-inner-phase"§ dispatches only to
unchanged §regenerate.py§ / §regenerate_period4.py§ and their old
fixtures/contracts/serialization. New §mode="v1.1-one-inner-return-slit"§
uses only this separate checker, new field registry, new manifest, and
a view of the locked pre-existing near-parabolic certificate. Algebraically
the general side/hull definitions reduce to the v1 ones when the
actual §G§-cycled little Julia intervals number three, the
physical tree and cuts are those supplied by the v1 examples, and
the unchanged v1 path/Wave definitions are selected. **All old
ids, cut orders, orientations, filters, symbolic width expressions and
canonical JSON byte encodings remain those of v1, not recalculated
using the new 2/4-atom refinement.** This is the explicit
identity embedding §j(v1_record)=(mode="v1-three-inner-phase",v1_record)§,
with inverse projection §π∘j=id§. It would be invalid to deduce that
all primitive renormalizations have the same tree or finite marking.

The checker first recomputes and compares the original near-parabolic
manifest *byte by byte*, invokes its source Git-blob locks, and compares
the old physical v1 p=3/p=4 projections; existing v1
§--check§ commands and all prior unit tests still run independently
in CI. No old file may be rewritten.

## 5. Trust boundary and reproduction

**Certified finite arithmetic:** the existing three adjacent-dyadic
root isolations, restricted degree, primitive disk separations,
central monotonicity, local invariant interval and inverse
exhaustion, the local return-slit attachment/edge counts and the
round subcollar bound. **Explicit analytic input:** identifying
the *whole* inner filled Julia with the real slit and its
Carathéodory-side parametrization, as already stated by the old
near-parabolic audit. **Exact conditional bookkeeping:** the chosen
2-target/4-source side partition and two distinct pullback maps.
**Numerical only:** decimal parameter labels in old §RESULTS.md§,
never used in code. **Open/undefined:** prime condition and canonical
ambient ψ-ql tree/edge operator, whole-path filters, Wave widths and
harmonic relation, actual attachment §h,ell§, any resistance-crossover
comparison, and the infinite parabolic-tail limit.

Use (at repository root):

```sh
python research/native_wave_transfer/regenerate_primitive_v1_1.py --check
python research/native_wave_transfer/regenerate_near_parabolic.py --check
python research/native_wave_transfer/regenerate.py --check
python research/native_wave_transfer/regenerate_period4.py --check
python -m unittest discover -s research/native_wave_transfer -p 'test_*.py' -v
```

The v1.1 manifest is sorted, ASCII-escaped, two-space JSON with a trailing
newline. Its lock includes code, fixture, field registry and old
near-parabolic manifest SHA-256. Default mode is **read-only**; failures
on source drift, missing citation, unknown field, mixing the actions,
a forged Wave datum, missing manifest or changed output are deliberate.

# Partial virtual-scale-two root-transition certificate

Date: 2026-07-25
Status: proved in the native terminal category; incomplete for the virtual-Molecule problem. Original manuscript and original PDFs are unchanged.

## 1. Certificate input

Use the source-locked periodically repelling primitive terminal return

    F_term = f^P: A_0 -> B,

where A_0 and B are the actual Jordan domains, K_0 is the terminal small
filled Julia set, and K_i = f^i(K_0) is the complete primitive cycle. Let
H_term be the native Hubbard-tree carrier of that cycle.

The terminal anchor supplies the following actual data:

- a genuine holomorphic proper return map F_term;
- a degree-two critical stage at K_0 and degree-one stages at the other
  primitive-cycle components;
- the exact component itinerary K_0 -> K_1 -> ... -> K_{P-1} -> K_0;
- a canonical ideal side I_{1->0} determined by the first edge of the native
  Hubbard-tree path from K_1 to K_0; and
- a connected forward-invariant native carrier H_term.

## 2. Degree and marking proof

Primitivity makes the K_i pairwise disjoint, and the unique critical point of
f lies in K_0 and in no other K_i. Therefore the one-step degree word of the
terminal cycle, beginning at K_0, is

    (2, 1, ..., 1).

The native Hubbard graph is a finite tree. The path from the vertex of K_1 to
the vertex of K_0 has a unique first edge at K_1. The side of K_1 containing
that edge is therefore canonical and is the native ideal side I_{1->0}.

This proves a typed root transition in the native terminal category:

    tau_root: K_0 -> K_{q mod P}

for the outer q-step bookkeeping, together with the separately defined
proper terminal return F_term and its ideal marking.

## 3. Exact limitation

This certificate does not prove that F_term is the requested virtual-scale-two
return. The missing conditions are:

1. an actual second-scale base B_{2,xi} inside the relevant outer cylinder or
   end fiber;
2. an equality or proved conjugacy between the virtual marked return and
   F_term;
3. compatibility of tau_root with the univalent partial shift on every finite
   outer cylinder;
4. a protected prime-end/crosscut chain for I_{1->0} in the partial carrier;
5. the complete second-scale access, obstacle, and Wave-demand ledger; and
6. naturality under authorized root enlargement.

Thus the native anchor removes the degree and ideal-side ambiguity at the root,
but the corridor-to-root bridge remains the first unproved virtual condition.

## 4. Promotion decision

Promote only the native terminal root-transition record. Keep
`VIRTUAL_DISCONNECTED_MARKING_TRANSFER`, `VIRTUAL_VERTEX_PACKAGE_SELECTOR`,
`VIRTUAL_PROTECTED_ROUTING_CERTIFICATE`, UPTCR, and MLC open.

## 5. Local sources

- `terminal_hubbard_anchor.md`, Sections 3, 5, and 7;
- `virtual_cantor_pullback_compactification.md`, Sections 7 and 10;
- `virtual_s2_offcritical_degree_obstruction_20260725.md`.


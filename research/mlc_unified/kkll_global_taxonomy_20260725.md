# KKL global-regime taxonomy: source-locked correction

## What the June 2026 paper actually proves

Kahn--Kapiamba--Lyubich prove beau bounds and rigidity for a class of prime
primitive types that is parabolically bounded. The paper's Theorem C is a
class theorem; it is not a statement that every quadratic parameter has MLC.

Source: <https://arxiv.org/html/2606.27272>

## The four-way frontier

The introduction classifies families of prime types using three quantities:
the eventual limb depth (l), continued-fraction height (h), and continued-
fraction depth (d). It records four regimes:

1. anti-molecule/bounded satellite: l, h, d bounded;
2. near-parabolic: h unbounded while l and d are bounded;
3. near-neutral: d unbounded while l is bounded; and
4. virtually-satellite: l unbounded.

The corresponding tools are puzzle, near-parabolic, sectorial/molecule, and
virtual near-molecule primitive renormalization. The paper explicitly says
that the general neutral theory is believed to be promotable to all forms of
unbounded satellite renormalization. That wording is a research direction,
not an imported theorem. It also lists the virtual-renormalization paper as
"In preparation."

## Consequence for the active proof

This source sharpens the missing global theorem. A valid closure must provide
both:

* a theorem promoting the sectorial/neutral bounds to every realizable
  unbounded satellite family, including the rational parabolic/cylinder
  boundary; and
* the virtual-renormalization carrier, interpolation, and rigidity theorem for
  the l-unbounded regime.

The KKL primitive theorem does not supply either item. The local ledger keeps
them open, so the global MLC target is not promoted.

## Machine check

`validate_kkll_global_taxonomy.py` locks the downloaded source PDF hash

`4C08805384B473DC0E55D76491C52C9FBE7C027E6DA301F2C365A170ED7D9140`

and checks the class scope, four-way taxonomy, prospective wording, and
in-preparation virtual-renormalization boundary. It returns
`KKL_GLOBAL_TAXONOMY_SOURCE_VALID` with
`original_artifacts_written=false`.

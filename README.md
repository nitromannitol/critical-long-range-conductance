# Critical long-range conductance

[![Build](https://github.com/nitromannitol/critical-long-range-conductance/actions/workflows/build.yml/badge.svg)](https://github.com/nitromannitol/critical-long-range-conductance/actions/workflows/build.yml)
[![Independent comparators](https://github.com/nitromannitol/critical-long-range-conductance/actions/workflows/comparator.yml/badge.svg)](https://github.com/nitromannitol/critical-long-range-conductance/actions/workflows/comparator.yml)
[![Lean 4.35.0-rc2](https://img.shields.io/badge/Lean-4.35.0--rc2-blue)](lean-toolchain)

A Lean 4 and Mathlib formalization of *Quantitative homogenization for the critical
long-range random conductance model*, Ahmed Bou-Rabee and Paul Dario,
[arXiv:2604.21143](https://arxiv.org/abs/2604.21143). It covers both arXiv versions:
`LongRangeHeat` formalizes the second version, which proves homogenization of the heat
equation, and `LongRange` formalizes the first version.

## Second version

`LongRangeHeat` formalizes the second arXiv version, whose source is
[`paper/critical-long-range-rw-v2.tex`](paper/critical-long-range-rw-v2.tex). Every labeled
theorem, lemma and proposition is proved: Theorem 1.1 (quantitative homogenization of the heat
equation), Theorem 1.2 (the annealed invariance principle, in its scaled and unscaled forms),
Lemmas 2.1–2.3, 3.1 and 3.3, and Propositions 3.2 and 4.1–4.3, together with the scaling
obstruction stated after Theorem 1.1.
[CORRESPONDENCE.md](CORRESPONDENCE.md#heat-kernel-version) lists the Lean declaration of each
result.

No result of this version takes a cited hypothesis: every result that the formal proofs quote
from the literature is proved in the library. These are the on-diagonal bound of
Murugan–Saloff-Coste (Theorem 1.1, for the critical lattice kernel), the Kallenberg–Aldous
criterion for convergence in `D([0, ∞), ℝ^d)`, and the Nash inequality (Proposition 3.1(ii))
and Davies estimate (Theorem 4.4 with Example 4.3) of Chen–Kim–Kumagai–Wang. Theorem 1.1 is
`main_theorem`; Propositions 4.1–4.3 and both forms of Theorem 1.2 are the exports ending in
`_unconditional`. Earlier forms of these statements, which take cited inputs as hypotheses, are
kept unchanged; see [CITED_INPUTS.md](CITED_INPUTS.md#heat-kernel-version).

The formal proof of Step 2 of Proposition 4.1, the off-diagonal heat-kernel bound, follows a
different route from the paper. The paper uses the stability theory of Chen–Kumagai–Wang, as
extended to graphs by Malmquist; these results are neither formalized nor assumed. The
formalization deletes the jumps longer than a scale comparable to `|x - y|` and applies the
Chen–Kim–Kumagai–Wang Davies estimate to the truncated walk, with the Nash inequality obtained
from Step 1. The statement of Proposition 4.1 is unchanged.
[CORRESPONDENCE.md](CORRESPONDENCE.md#deviations-from-the-papers-proofs) records this and the
other places where a formal proof departs from the paper's argument.

## First version

The library `LongRange` formalizes arXiv:2604.21143v1. Import `LongRange` for the complete library or
`LongRange.Statements` for the source-facing statements. The 23 theorem exports and
three complete definition exports are listed in [CORRESPONDENCE.md](CORRESPONDENCE.md),
which also distinguishes supporting proof ingredients, repeated assertions and context.

The main theorem `LongRange.Statements.main_theorem` produces an actual `H10 U` weak
solution, proves uniqueness among all weak solutions in that space, and identifies its
unique continuous classical representative. It gives the quantitative error bound
`C / sqrt |log ε|` above a measurable random minimal scale with an exponential tail.
The library also supplies the quenched invariance principle, tightness, corrector
estimates, lattice sums and configuration-uniform heat-kernel estimates.

The environment consists of independent identically distributed uniformly elliptic
unordered-edge conductances. The critical kernel uses Euclidean distance. Integer sites
represent physical positions `ε * q`; corrector slopes use those positions. The actual
variational corrector and full and killed path-law densities retain their definition
bodies and characterization theorems.

These results are conditional on a finite list of **16 explicit cited propositions**,
formulated in the library and its pinned Lattice-Probability dependency. They are
assumptions, not proofs of the outside papers. Different exports use different subsets;
[CITED_INPUTS.md](CITED_INPUTS.md) lists the exact names. The paper's applications and
adapters are proved in the library.

The April version carries 135 modules under `LongRange/Support` from Lattice-Probability
revision `47027b49b6660ee34c323869b0c88b7eb72f1124`, alongside the currently pinned
Lattice-Probability dependency.

## Reading and building

The Lean toolchain, Mathlib and Lattice-Probability versions are pinned in
`lean-toolchain`, `lakefile.lean` and `lake-manifest.json`. With Elan installed:

```sh
lake exe cache get
lake build LongRange LongRangeHeat
python3 scripts/check_axioms.py
```

`check_axioms.py` checks every public statement and definition export against the allowed
axioms `propext`, `Classical.choice` and `Quot.sound`. Explicit cited hypotheses are
ordinary proposition parameters and are separate from this kernel axiom check.

The Build workflow checks main-branch pushes and pull requests. The Independent comparators
workflow runs by manual dispatch; the badges above link to the current hosted results. See
[the comparison instructions](LongRangeAudit/README.md).

## Copied code

Two modules under `LongRange/HeatKernel/` contain code copied from Leonardo Bonanno's
[`lean-formalizations`](https://github.com/leobon12/lean-formalizations), commit `fdb5cad`:
the complexification of real square-summable sequence operators. This code is copied
source, not a dependency. Each file names its source modules and lists its changes in its
header; [`NOTICE`](NOTICE) gives the details.

## Paper and citation

[paper/](paper/) contains the source of the second version and, for the first version, the
original source, a corrected companion, the required figures and an exact changes record. The
companion's abstract and three main theorem statements are unchanged from the first version,
and its [compiled PDF](paper/critical-long-range-rw-revised.pdf) is included.
See [CITATION.cff](CITATION.cff) for citation data.

The Lean code was written with AI coding agents under the direction of the authors.

The Lean code is licensed under the Apache License 2.0; see [LICENSE](LICENSE). A license
for the paper source in [paper/](paper/) has not yet been selected.

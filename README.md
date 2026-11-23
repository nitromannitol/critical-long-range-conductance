# Critical long-range conductance

[![Build](https://github.com/nitromannitol/critical-long-range-conductance/actions/workflows/build.yml/badge.svg)](https://github.com/nitromannitol/critical-long-range-conductance/actions/workflows/build.yml)
[![Independent comparators](https://github.com/nitromannitol/critical-long-range-conductance/actions/workflows/comparator.yml/badge.svg)](https://github.com/nitromannitol/critical-long-range-conductance/actions/workflows/comparator.yml)
[![Lean 4.35.0-rc2](https://img.shields.io/badge/Lean-4.35.0--rc2-blue)](lean-toolchain)

A Lean 4 and Mathlib formalization of *Quantitative homogenization for the critical
long-range random conductance model*, Ahmed Bou-Rabee and Paul Dario,
[arXiv:2604.21143](https://arxiv.org/abs/2604.21143). `LongRangeHeat` formalizes the second
arXiv version, which proves homogenization of the heat equation, and `LongRange` formalizes the
first version.

## Second version

`LongRangeHeat` formalizes the second arXiv version, whose source is
[`paper/critical-long-range-rw-v2.tex`](paper/critical-long-range-rw-v2.tex). Every labeled
theorem, lemma and proposition is proved: Theorem 1.1 (quantitative homogenization of the heat
equation), Theorem 1.2 (the annealed invariance principle, in its scaled and unscaled forms),
Lemmas 2.1–2.3, 3.1 and 3.3, and Propositions 3.2 and 4.1–4.3, together with the scaling
obstruction stated after Theorem 1.1.
[CORRESPONDENCE.md](CORRESPONDENCE.md#heat-kernel-version) lists the Lean declaration of each
result.

No result takes a cited hypothesis: the results that the formal proofs use from the literature
are proved in the library. These are the on-diagonal bound of Murugan–Saloff-Coste
(Theorem 1.1, for the critical lattice kernel), the Kallenberg–Aldous criterion for convergence
in `D([0, ∞), ℝ^d)`, and the Nash inequality (Proposition 3.1(ii)) and Davies estimate
(Theorem 4.4 with Example 4.3) of Chen–Kim–Kumagai–Wang. Theorem 1.1 is `main_theorem`;
Propositions 4.1–4.3 and both forms of Theorem 1.2 are the exports ending in `_unconditional`.
[CITED_INPUTS.md](CITED_INPUTS.md#heat-kernel-version) lists these inputs and their proofs.

The formal proof of Step 2 of Proposition 4.1, the off-diagonal heat-kernel bound, follows a
different route from the paper. The paper uses the stability theory of Chen–Kumagai–Wang, as
extended to graphs by Malmquist; these results are neither formalized nor assumed. The
formalization deletes the jumps longer than a scale comparable to `|x - y|` and applies the
Chen–Kim–Kumagai–Wang Davies estimate to the truncated walk, with the Nash inequality obtained
from Step 1; see [CORRESPONDENCE.md](CORRESPONDENCE.md#deviations-from-the-papers-proofs).

## First version

`LongRange` formalizes arXiv:2604.21143v1. Import `LongRange` for the complete library or
`LongRange.Statements` for the statements; [CORRESPONDENCE.md](CORRESPONDENCE.md) lists the
23 theorem exports and three definition exports.

The main theorem `LongRange.Statements.main_theorem` produces an `H10 U` weak solution, proves
its uniqueness among weak solutions in that space, and identifies its continuous classical
representative. It gives the quantitative error bound `C / sqrt |log ε|` above a measurable
random minimal scale with an exponential tail. The library also proves the quenched invariance
principle, tightness, corrector estimates, lattice sums and heat-kernel estimates uniform in the
conductances.

The conductances are independent, identically distributed and uniformly elliptic, indexed by
unordered edges, and the critical kernel uses the Euclidean distance. These results take
**16 cited propositions** as explicit hypotheses, formulated in the library and in
Lattice-Probability; [CITED_INPUTS.md](CITED_INPUTS.md) lists them and the exports that use
each.

## Building

The Lean toolchain, Mathlib and Lattice-Probability versions are pinned in
`lean-toolchain`, `lakefile.lean` and `lake-manifest.json`. With Elan installed:

```sh
lake exe cache get
lake build LongRange LongRangeHeat
python3 scripts/check_axioms.py
```

`check_axioms.py` checks that every public export uses only the axioms `propext`,
`Classical.choice` and `Quot.sound`. Cited hypotheses are ordinary parameters of the theorems,
so this check does not cover them. The badges above link to the build and comparator results;
see [the comparison instructions](LongRangeAudit/README.md).

## Copied code

Two modules under `LongRange/HeatKernel/` contain code copied from Leonardo Bonanno's
[`lean-formalizations`](https://github.com/leobon12/lean-formalizations), commit `fdb5cad`:
the complexification of real square-summable sequence operators. Each file names its source
modules and lists its changes in its header; [`NOTICE`](NOTICE) gives the details.
`LongRange/Support` contains 135 modules from Lattice-Probability revision
`47027b49b6660ee34c323869b0c88b7eb72f1124`.

## Paper and citation

[paper/](paper/) contains the sources of both versions, a corrected companion of the first
version with its [compiled PDF](paper/critical-long-range-rw-revised.pdf), and the figures.
See [CITATION.cff](CITATION.cff) for citation data.

The Lean code was written with AI coding agents under the direction of the authors. It is
licensed under the Apache License 2.0; see [LICENSE](LICENSE).

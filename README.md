# Critical long-range conductance

[![Build](https://github.com/nitromannitol/critical-long-range-conductance/actions/workflows/build.yml/badge.svg)](https://github.com/nitromannitol/critical-long-range-conductance/actions/workflows/build.yml)
[![Independent comparators](https://github.com/nitromannitol/critical-long-range-conductance/actions/workflows/comparator.yml/badge.svg)](https://github.com/nitromannitol/critical-long-range-conductance/actions/workflows/comparator.yml)
[![Lean 4.32.0](https://img.shields.io/badge/Lean-4.32.0-blue)](lean-toolchain)

A Lean 4 and Mathlib formalization of *Quantitative homogenization for the critical
long-range random conductance model*, Ahmed Bou-Rabee and Paul Dario,
[arXiv:2604.21143v1](https://arxiv.org/abs/2604.21143v1).

The public library is `LongRange`. Import `LongRange` for the complete library or
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

These results are conditional on a finite list of **16 explicit cited propositions** in
the pinned Lattice-Probability dependency. They are assumptions, not proofs of the outside
papers. Different exports use different subsets; [CITED_INPUTS.md](CITED_INPUTS.md)
lists the exact names. The paper's applications and adapters are proved in the library.

## Reading and building

The Lean toolchain, Mathlib and Lattice-Probability versions are pinned in
`lean-toolchain`, `lakefile.lean` and `lake-manifest.json`. With Elan installed:

```sh
lake exe cache get
lake build LongRange
python3 scripts/check_axioms.py
```

`check_axioms.py` checks every public statement and definition export against the allowed
axioms `propext`, `Classical.choice` and `Quot.sound`. Explicit cited hypotheses are
ordinary proposition parameters and are separate from this kernel axiom check.

A clean build compiled 9,099 jobs with zero warnings and errors, using fresh project and
Lattice-Probability build directories and the official Mathlib cache. The in-checkout axiom
audit checked all 26 public exports and found only the three allowed kernel axioms.

The independent comparisons passed for the main theorem and both formulations of the
invariance principle in this release checkout, including dependency comparison, NanoDa
and Lean kernel replay.

The Build workflow checks main-branch pushes and pull requests. The Independent comparators
workflow runs by manual dispatch; the badges above link to the current hosted results. See
[the comparison instructions](LongRangeAudit/README.md).

## Paper and citation

[paper/](paper/) contains the original source, corrected companion, required figure and
an exact changes record. Its abstract and three main theorem statements are unchanged.
The [corrected article PDF](paper/critical-long-range-rw-revised.pdf) is included.
See [CITATION.cff](CITATION.cff) for citation data.

A publication license has not yet been selected for the software or paper source.
No software license grant is asserted by this repository.

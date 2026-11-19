# Critical long-range conductance

[![Build](https://github.com/nitromannitol/critical-long-range-conductance/actions/workflows/build.yml/badge.svg)](https://github.com/nitromannitol/critical-long-range-conductance/actions/workflows/build.yml)
[![Independent comparators](https://github.com/nitromannitol/critical-long-range-conductance/actions/workflows/comparator.yml/badge.svg)](https://github.com/nitromannitol/critical-long-range-conductance/actions/workflows/comparator.yml)
[![Lean 4.35.0-rc2](https://img.shields.io/badge/Lean-4.35.0--rc2-blue)](lean-toolchain)

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

These results are conditional on a finite list of **13 explicit cited propositions** in
the library and its pinned Lattice-Probability dependency. They are assumptions, not proofs of the outside
papers. Different exports use different subsets; [CITED_INPUTS.md](CITED_INPUTS.md)
lists the exact names. The paper's applications and adapters are proved in the library.

## Heat-kernel version

`LongRangeHeat` contains the formalization of the heat-kernel version in
[`paper/heat-kernel-without-ECP-v2.tex`](paper/heat-kernel-without-ECP-v2.tex).
Theorem 1.1, the scaled and unscaled annealed invariance principles (Theorem 1.2),
and supporting results are listed in
[CORRESPONDENCE.md](CORRESPONDENCE.md#heat-kernel-version). The on-diagonal bound of
Proposition 4.1, which the paper takes from Murugan–Saloff-Coste (Theorem 1.1), is proved
in the library for the critical lattice kernel, with one constant for all admissible
conductance fields. The exports `heat_kernel_bounds_proved`, `aldous_condition_proved`,
`fdd_convergence_proved`, `annealed_invariance_principle_proved` and
`unscaled_invariance_principle_proved` state Propositions 4.1–4.3 and both forms of
Theorem 1.2 without a Murugan–Saloff-Coste hypothesis. They take the Chen–Kim–Kumagai–Wang
Nash and Davies estimates as explicit hypotheses, and both invariance-principle forms also
take two Ethier–Kurtz criteria; see [CITED_INPUTS.md](CITED_INPUTS.md). The exports of the
same names without `_proved` are unchanged and still take the uniform Murugan–Saloff-Coste
estimate as a hypothesis. The forms `annealed_invariance_principle_kallenberg` and
`unscaled_invariance_principle_kallenberg` do not take the Ethier–Kurtz criteria, since the
Kallenberg–Aldous criterion is proved in the library.

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

[paper/](paper/) contains the original source, corrected companion, required figure and
an exact changes record. Its abstract and three main theorem statements are unchanged.
The [corrected article PDF](paper/critical-long-range-rw-revised.pdf) is included.
See [CITATION.cff](CITATION.cff) for citation data.

The Lean code is licensed under the Apache License 2.0; see [LICENSE](LICENSE). A license
for the paper source in [paper/](paper/) has not yet been selected.

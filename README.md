# Quantitative homogenization for the critical long-range random conductance model

[![CI](https://github.com/nitromannitol/critical-long-range-conductance/actions/workflows/build.yml/badge.svg?branch=main)](https://github.com/nitromannitol/critical-long-range-conductance/actions/workflows/build.yml)
[![Comparator audit](https://github.com/nitromannitol/critical-long-range-conductance/actions/workflows/comparator.yml/badge.svg?branch=main)](https://github.com/nitromannitol/critical-long-range-conductance/actions/workflows/comparator.yml)

A Lean 4 formalization of the paper

> Ahmed Bou-Rabee and Paul Dario,
> [*Quantitative homogenization for the critical long-range random conductance model*](https://arxiv.org/abs/2604.21143),
> arXiv:2604.21143.

The paper studies a random walk on `ℤᵈ` with random conductances and long jumps, at the critical
jump exponent where the walk is superdiffusive by a logarithmic factor. It proves that solutions of
the rescaled heat equation of the walk are within order `|ln ε|^(−1/2)` of those of a
constant-coefficient heat equation, and an annealed invariance principle. Every labelled result of
the second arXiv version is proved in Lean, with no `sorry`, only the standard axioms and no
hypothesis beyond the setting of the paper. The first arXiv version, whose main theorems differ, is
formalized too; its theorems take results from the literature as hypotheses, listed under
[What is assumed](#what-is-assumed-first-version).

## The paper

Consider a random walk on `ℤᵈ` that jumps from `x` to `y` at rate `a({x,y}) |x − y|^(−d−α)`. The
conductances `a({x,y})` are random, indexed by unordered pairs, and take values in `[λ, 1/λ]`. For
`α < 2` the rescaled walk converges to a stable process, and for `α > 2` to Brownian motion. At the
critical value `α = 2`, the second moment of the jumps diverges logarithmically, and the walk is
superdiffusive by a logarithmic factor. The paper treats this critical case.

**Second version.** The conductances are independent, with values in `[λ, 1/λ]` and mean `1`; they
need not be identically distributed. For a lattice spacing `ε ∈ (0, 1/2)`, let
`κ_ε = εᵈ Σ_{0 < |z| ≤ 1} |z|^(−d)` over `z ∈ εℤᵈ`, so that `κ_ε` is of order `|ln ε|`, and let

> `L^ε v(x) = (εᵈ/κ_ε) Σ_{z ∈ εℤᵈ ∖ {0}} a(x, x+z) |z|^(−d−2) (v(x+z) − v(x))`.

For `f ∈ C_c^∞(ℝᵈ)`, let `u_ε` solve the lattice heat equation `∂_t u_ε = L^ε u_ε` on `εℤᵈ` with
`u_ε(0) = f`, and let `ū` solve `∂_t ū = (1/(2d)) Δū` on `ℝᵈ` with `ū(0) = f`. The norm is
`‖v‖ = (εᵈ Σ_{x ∈ εℤᵈ} v(x)²)^(1/2)`. A random variable `X` satisfies `X ≤ 𝒪₂(A)` if
`E[exp((max(X, 0)/A)²)] ≤ 2`, which gives `P[X ≥ rA] ≤ 2e^(−r²)`.

- **Theorem 1.1 (quantitative homogenization of the heat equation).** There is `C(d, λ, f)` such
  that, for every `T ≥ 0` and `ε ∈ (0, 1/2)`,
  `sup_{0 ≤ t ≤ T} ‖u_ε(t) − ū(t)‖ ≤ 𝒪₂(C (1 + T) / |ln ε|^(1/2))`.
- **Theorem 1.2 (annealed invariance principle).** Let `X^ε` be the walk with generator `L^ε`
  started from `0`. Under the annealed law, averaged over the conductances, `X^ε` converges in law
  to `d^(−1/2) W` in `D([0, ∞), ℝᵈ)`, where `W` is a standard Brownian motion.

In the original scaling, the walk `Y` on `ℤᵈ` with jump rates `a({x,y}) |x − y|^(−d−2)` satisfies
`(n ln n)^(−1/2) Y_{nt} → (|S^(d−1)|/(2d))^(1/2) W`. The effective diffusivity depends on the law of
the conductances only through their mean. The paper also notes a deterministic scaling obstruction
to any rate better than `|ln ε|^(−1)` in Theorem 1.1.

**First version.** The conductances are independent and identically distributed (Assumption (U)).
Theorem 1.1 proves homogenization of the elliptic equation `μu − L^ε u = f` on a bounded domain
with `C^(2,σ)` boundary, with zero boundary values. The error in `L²` is at most `C/√|ln ε|`
whenever `|ln ε|` exceeds a random minimal scale with an exponential tail. Theorem 1.2 is a quenched
invariance principle: for almost every realization of the conductances, the walk started from a
compactly supported density converges to `X₀ + (E[a]/d)^(1/2) W`.

## The main theorems in Lean

| Paper | Lean declaration |
| --- | --- |
| Second version, Theorem 1.1 | `LongRangeHeat.Statements.main_theorem` |
| Second version, Theorem 1.2 | `LongRangeHeat.Statements.annealed_invariance_principle_unconditional` |
| Second version, Theorem 1.2 in the original scaling | `LongRangeHeat.Statements.unscaled_invariance_principle_unconditional` |
| First version, Theorem 1.1 | `LongRange.Statements.main_theorem` |
| First version, Theorem 1.2 | `LongRange.Statements.quenched_invariance_principle_intro` |

The statements of the second version are in
[`LongRangeHeat/Statements/`](LongRangeHeat/Statements/), one file per result. Those of the first
version are in [`LongRange/Statements/`](LongRange/Statements/), and `import LongRange.Statements`
loads them all.

How to read the statements:

- The law of the conductances is `ConductanceLaw P lam a` in the second version: the variables
  `a ω e` are independent, measurable, in `[λ, 1/λ]` and have mean `1`. Each theorem holds for every
  probability space carrying such a law; a constant in a statement is chosen before the space.
- `X ≤ 𝒪₂(A)` is `IsOq P 2 X A`. The lattice and continuum solutions are `latticeHeat` and
  `continuumHeat`. The Lean form of Theorem 1.1 also states that the error is square-summable at
  each time and bounded on `[0, T]`, so that the supremum is finite.
- In Theorem 1.2, the Brownian motion is a law `B` on `C([0, ∞), ℝᵈ)` with
  `IsStandardBrownianLaw B`, and the measurability of the map `W ↦ d^(−1/2) W` into
  `D([0, ∞), ℝᵈ)` is part of the conclusion. The annealed law is `annealedLaw`.
- The first-version exports take the cited results as their first arguments, then the setting of
  the paper, with Assumption (U) as `AssumptionU P lam a`. `LongRange.Statements.main_theorem` also
  produces the weak solution in `H10 U`, proves its uniqueness and identifies its continuous
  classical representative.

## All numbered results

The table lists each numbered result of the second version with the Lean declaration that proves it,
in the namespace `LongRangeHeat.Statements`. None of these declarations takes a cited result as a
hypothesis.

| Paper | Lean declaration | Content |
| --- | --- | --- |
| Theorem 1.1 | `main_theorem` | Homogenization of the heat equation at the rate `\|ln ε\|^(−1/2)`. |
| Theorem 1.2 | `annealed_invariance_principle_unconditional` | Annealed convergence of `X^ε` to `d^(−1/2) W` in `D([0, ∞), ℝᵈ)`. |
| Lemma 2.1 | `dirichlet_form` | Integration by parts for `L^ε`, and coercivity of its Dirichlet form up to the factor `κ_ε⁻¹`. |
| Lemma 2.2 | `sampling` | Uniform lattice `L²` bounds on the derivatives of `ū(s, · + y)`. |
| Lemma 2.3 (i) | `O_squares` | `X ≤ 𝒪₂(A)` if and only if `X² ≤ 𝒪₁(A²)`. |
| Lemma 2.3 (ii) | `O_expectation` | `X ≤ 𝒪₂(A)` implies `E[max(X, 0)] ≤ 2A`. |
| Lemma 2.3 (iii) | `O_sums` | Countable sums of `𝒪_q` bounds. |
| Lemma 2.3 (iv) | `O_integrals` | Time integrals of `𝒪_q` bounds. |
| Lemma 2.3 (v) | `O_constants` | A constant `A` satisfies `A ≤ 𝒪_q(2A)`. |
| Lemma 3.1 | `mean_operator_consistency` | `ū` solves the lattice equation with mean conductances up to an error `C/κ_ε`. |
| Proposition 3.2 | `forcing_representation` | The random term equals `κ_ε⁻¹ ⟨G, Dv⟩` up to `C κ_ε⁻¹ ‖v‖`. |
| Lemma 3.3 | `G_gaussian_tails` | `‖G(s, ·)‖ ≤ 𝒪₂(C)`, uniformly in `ε` and `s`. |
| Proposition 4.1 | `heat_kernel_bounds_unconditional` | On-diagonal bound `C h^(−d/2)` and displacement bound for the heat kernel of `L^ε`. |
| Proposition 4.2 | `aldous_condition_unconditional` | Aldous' condition for `X^ε` under the annealed law. |
| Proposition 4.3 | `fdd_convergence_unconditional` | Convergence of the finite-dimensional laws of `X^ε` to those of `d^(−1/2) W`. |

The scaling obstruction stated after Theorem 1.1 is `scaling_obstruction`. The heat equations
(1.4) and (1.5), and several displayed estimates, are also proved;
[`CORRESPONDENCE.md`](CORRESPONDENCE.md#heat-kernel-version) lists them. For the first version,
[`CORRESPONDENCE.md`](CORRESPONDENCE.md) maps each labelled statement to its Lean declaration, 23
theorem exports and three definitions in all.

## What is assumed (first version)

This section concerns the first version only; the second version assumes nothing. The exports of
the first version take 16 cited propositions as explicit hypotheses, each a `Prop` in the namespace
`LatticeProb.External`. [`CITED_INPUTS.md`](CITED_INPUTS.md) links each to its exact Lean
statement. Each bullet says which of the two main theorems of the first version take it.

- Existence of a classical solution of the Dirichlet problem; GT, Theorem 6.14.
  `GilbargTrudingerExistence`. Theorems 1.1 and 1.2.
- Regularity up to the boundary of solutions of the Dirichlet problem; GT, Theorem 6.19.
  `GilbargTrudingerBoundaryRegularity`. Theorems 1.1 and 1.2.
- The global Schauder estimate; GT, Theorem 6.6. `GilbargTrudingerSchauderEstimate`. Theorems 1.1
  and 1.2.
- The supremum estimate of the maximum principle; GT, Theorem 3.7. `GilbargTrudingerSupEstimate`.
  Theorems 1.1 and 1.2. Proved in Lattice-Probability.
- Extension of Hölder functions from a domain; GT, Lemma 6.37. `GilbargTrudingerHolderExtension`.
  Theorems 1.1 and 1.2. Proved in Lattice-Probability.
- Approximation in the Sobolev space with zero boundary values; GT, Section 7.5.
  `GilbargTrudingerZeroBoundaryApproximation`. Theorem 1.1.
- Uniqueness of weak solutions of the homogeneous problem; GT, Corollary 8.2.
  `GilbargTrudingerWeakHomogeneousUniqueness`. Theorem 1.1. Proved in Lattice-Probability.
- The discrete on-diagonal heat-kernel bound; MSC, Theorem 1.1, estimate (10). `MuruganSaloffCoste`.
  Theorem 1.2.
- The same bound with the dependence of the constant traced through the proof; MSC, Theorem 1.1.
  `MuruganSaloffCosteUniform`. Other exports only.
- Ultracontractivity implies a Nash inequality; CKKW, Proposition 3.1(ii).
  `ChenKimKumagaiWangNash`. Theorem 1.2. Proved in this repository.
- The Davies upper bound for the heat kernel; CKKW, Theorem 4.4 with Example 4.3.
  `ChenKimKumagaiWangDavies`. Theorem 1.2. Proved in this repository.
- Convergence of semigroups from convergence of generators; EK, Chapter 1, Theorem 6.1,
  (c) implies (a). `EthierKurtzTrotterKato`. Theorem 1.2.
- A criterion for relative compactness in Skorokhod space; EK, Chapter 3, Theorem 8.6, (b) implies
  (a). `EthierKurtzRelativeCompactness`. Theorem 1.2.
- The stopping-time criterion for relative compactness; EK, Chapter 3, Theorem 8.6, (c) implies (a),
  and Remark 8.7(b). `EthierKurtzRelativeCompactnessStopping`. Other exports only.
- Convergence in law from relative compactness and convergence of finite-dimensional laws; EK,
  Chapter 3, Theorem 7.8(b). `EthierKurtzConvergenceFromFdd`. Theorem 1.2.
- The Skorokhod space on a finite horizon is Polish; Billingsley, Theorems 12.1 and 12.2.
  `BillingsleySkorokhodPolish`. Other exports only.

GT is Gilbarg–Trudinger, *Elliptic Partial Differential Equations of Second Order* (Springer, 2001
reprint). MSC is Murugan–Saloff-Coste, *Anomalous threshold behavior of long range random walks*,
Electron. J. Probab. 20 (2015), no. 74. CKKW is Chen–Kim–Kumagai–Wang, *Heat kernel upper bounds for
symmetric Markov semigroups*, J. Funct. Anal. 281 (2021), 109074. EK is Ethier–Kurtz, *Markov
Processes: Characterization and Convergence* (Wiley, 1986). Billingsley is *Convergence of
Probability Measures*, second edition (Wiley, 1999).

So Theorem 1.1 of the first version takes seven inputs and Theorem 1.2 takes eleven. Five of the
sixteen are proved, as marked, but the first-version exports take them as hypotheses, as released.

## Corrections

The second version is formalized as printed. The Lean statements of the first version follow
arXiv:2604.21143v1, included unchanged as
[`paper/critical-long-range-rw.tex`](paper/critical-long-range-rw.tex). The corrected companion
[`paper/critical-long-range-rw-revised.tex`](paper/critical-long-range-rw-revised.tex) keeps the
abstract and the statements of the main theorems, and lists its changes at its start:

- three local corrections, C1 to C3, in the introduction and in the proof of a proposition;
- a gap in the printed proof of the off-diagonal heat-kernel bound, G1, with a repaired proof;
- clarifications of constants, filtrations and citations (O2 to O6, R1), and a simpler route to the
  invariance principle (A1).

[`paper/CHANGES.diff`](paper/CHANGES.diff) is the complete diff against the original source.

## Scope

- **Departures from the proofs of the second version.** The formal proofs differ from the paper at
  five steps, D1 to D5, described in
  [`CORRESPONDENCE.md`](CORRESPONDENCE.md#deviations-from-the-papers-proofs). The main one is Step 2
  of Proposition 4.1, the off-diagonal bound. The paper uses the stability theory of
  Chen–Kumagai–Wang, extended to graphs by Malmquist; these results are neither formalized nor
  assumed. The formal proof deletes the long jumps and applies the Davies bound of
  Chen–Kim–Kumagai–Wang to the truncated walk, following the draft
  [`paper/heat-kernel-without-ECP-v2.tex`](paper/heat-kernel-without-ECP-v2.tex).
- **Cited inputs of the second version.** The on-diagonal bound of Murugan–Saloff-Coste is proved for
  the critical lattice kernel, the case the paper uses. The Kallenberg–Aldous criterion for
  convergence in `D([0, ∞), ℝᵈ)` is proved in its sufficiency direction, which is the direction
  Theorem 1.2 uses.
- **Other forms.** Propositions 4.1 to 4.3 and Theorem 1.2 of the second version also have forms that
  take cited results as hypotheses; [`CITED_INPUTS.md`](CITED_INPUTS.md#heat-kernel-version) lists
  them. The forms ending in `_unconditional`, used in the tables above, take none.
- **Generator series.** The statements of Lemmas 2.1 and 3.1 and Proposition 3.2 use the pointwise
  series defining the generator without asserting that it converges; see
  [`CORRESPONDENCE.md`](CORRESPONDENCE.md#generator-series-in-the-statements).
- **First version.** The conductances are indexed by unordered edges, and the kernel uses the
  Euclidean distance.

## Checking the proofs

- **No `sorry`.** `LongRange` and `LongRangeHeat` have none. The comparator challenges under
  [`LongRangeAudit/`](LongRangeAudit/) contain intentional `sorry`s at the statements, which the
  matching solutions prove.
- **Standard axioms only.** [`scripts/check_axioms.py`](scripts/check_axioms.py) prints the axioms of
  every public export of both versions and fails on any axiom other than `propext`,
  `Classical.choice` and `Quot.sound`. Cited hypotheses are ordinary parameters of the theorems, so
  this check does not cover them.
- **Independent check of the statements.** Four comparator pairs in
  [`LongRangeAudit/`](LongRangeAudit/) restate Theorems 1.1 and 1.2 of each version.
  [leanprover/comparator](https://github.com/leanprover/comparator) compares the dependency closures,
  checks the axioms, and replays the proofs in the Lean kernel and the independent nanoda kernel. See
  [`LongRangeAudit/README.md`](LongRangeAudit/README.md).
- **Continuous integration.** The build workflow ([`build.yml`](.github/workflows/build.yml), the
  **CI** badge) builds both libraries on every push to `main` and every pull request, rejects
  warnings and runs the axiom check. The comparator workflow
  ([`comparator.yml`](.github/workflows/comparator.yml), the **Comparator audit** badge) runs the
  four pairs and is started manually.

`LongRange/`, `LongRangeHeat/` and their root modules contain 559 Lean files with 87,404 lines, built
on mathlib and Lattice-Probability.

## Building

The Lean toolchain, Mathlib and Lattice-Probability versions are pinned in
`lean-toolchain`, `lakefile.lean` and `lake-manifest.json`. With Elan installed:

```sh
lake exe cache get
lake build LongRange LongRangeHeat
python3 scripts/check_axioms.py
```

The pins are Lean `v4.35.0-rc2`, mathlib at `065356127b1dc0016f66b7283ce0ce2c4055aa55` and
[Lattice-Probability](https://github.com/nitromannitol/Lattice-Probability) at
`721505023bc12a20241c73449ec33339fcf4555f`. `import LongRangeHeat` loads the second version and
`import LongRange` the first. To run the comparators locally, follow
[`LongRangeAudit/README.md`](LongRangeAudit/README.md), which uses
[`scripts/run_comparators.py`](scripts/run_comparators.py).

## Repository layout

```text
LongRangeHeat.lean, LongRangeHeat/   the second version; Statements/ holds the exports
LongRange.lean, LongRange/           the first version; Statements/ holds the exports, and
                                     Support/ the general results and the cited inputs
LongRangeAudit/                      the comparator pairs
paper/                               the sources of both versions, the corrected companion, figures
docs/                                notes on the proof of the Murugan–Saloff-Coste bound
scripts/                             check_axioms.py and run_comparators.py
CORRESPONDENCE.md                    paper and Lean, result by result, and the departures
CITED_INPUTS.md                      the cited propositions and the exports that take them
NOTICE                               the copied code
```

## How this was built

The Lean code was written with AI assistance, using models from Anthropic (Claude) and OpenAI (GPT),
under the direction of the authors. Every proof is checked by the Lean kernel.

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

## License

The Lean code is licensed under the Apache License 2.0; see [LICENSE](LICENSE).

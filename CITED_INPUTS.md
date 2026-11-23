# Explicit cited propositions

These 16 proposition definitions live in the namespace `LatticeProb.External`. Six
Gilbarg–Trudinger formulations are supplied by the pinned Lattice-Probability revision
`721505023bc12a20241c73449ec33339fcf4555f`; the other ten are defined in this repository under
`LongRange/Support/External`. They are explicit hypotheses wherever used. The paper's
applications are proved. The exports of the April version take them exactly as released. The
cited inputs of the heat-kernel version and their status are listed under
[Heat-kernel version](#heat-kernel-version).

The links below give the complete Lean proposition bodies, their source carriers,
quantifier order, constants and bibliographic details at an immutable revision.
The count is of registered proposition formulations, rather than distinct references or
logically independent assumptions. In particular, the library proves that the uniform
Murugan–Saloff-Coste formulation implies the other formulation.

| Proposition in `LatticeProb.External` | Cited result | Exact Lean statement |
| --- | --- | --- |
| `GilbargTrudingerExistence` | GT, Theorem 6.14: classical Dirichlet existence | [source](LongRange/Support/External/GilbargTrudingerExistence.lean) |
| `GilbargTrudingerBoundaryRegularity` | GT, Theorem 6.19: boundary regularity | [source](https://github.com/nitromannitol/Lattice-Probability/blob/721505023bc12a20241c73449ec33339fcf4555f/LatticeProb/External/GilbargTrudinger.lean) |
| `GilbargTrudingerSchauderEstimate` | GT, Theorem 6.6: Schauder estimate | [source](https://github.com/nitromannitol/Lattice-Probability/blob/721505023bc12a20241c73449ec33339fcf4555f/LatticeProb/External/GilbargTrudinger.lean) |
| `GilbargTrudingerSupEstimate` | GT, Theorem 3.7: supremum estimate | [source](https://github.com/nitromannitol/Lattice-Probability/blob/721505023bc12a20241c73449ec33339fcf4555f/LatticeProb/External/GilbargTrudinger.lean) |
| `GilbargTrudingerHolderExtension` | GT, Lemma 6.37: Hölder extension | [source](https://github.com/nitromannitol/Lattice-Probability/blob/721505023bc12a20241c73449ec33339fcf4555f/LatticeProb/External/GilbargTrudinger.lean) |
| `GilbargTrudingerZeroBoundaryApproximation` | GT, §7.5: approximation in the Sobolev space with zero boundary values | [source](https://github.com/nitromannitol/Lattice-Probability/blob/721505023bc12a20241c73449ec33339fcf4555f/LatticeProb/External/GilbargTrudingerSobolev.lean) |
| `GilbargTrudingerWeakHomogeneousUniqueness` | GT, Corollary 8.2: uniqueness of homogeneous weak solutions | [source](https://github.com/nitromannitol/Lattice-Probability/blob/721505023bc12a20241c73449ec33339fcf4555f/LatticeProb/External/GilbargTrudingerSobolev.lean) |
| `MuruganSaloffCoste` | MSC, Theorem 1.1, estimate (10): discrete on-diagonal bound | [source](LongRange/Support/External/MuruganSaloffCoste.lean) |
| `MuruganSaloffCosteUniform` | MSC, the same theorem with constant dependence traced through its proof | [source](LongRange/Support/External/MuruganSaloffCosteUniform.lean) |
| `ChenKimKumagaiWangNash` | CKKW, Proposition 3.1(ii): ultracontractivity implies a Nash inequality | [source](LongRange/Support/External/ChenKimKumagaiWang.lean) |
| `ChenKimKumagaiWangDavies` | CKKW, Theorem 4.4 and Example 4.3: Davies upper bound | [source](LongRange/Support/External/ChenKimKumagaiWang.lean) |
| `EthierKurtzTrotterKato` | EK, Chapter 1, Theorem 6.1(c) ⇒ (a): semigroup convergence | [source](LongRange/Support/External/EthierKurtzTrotterKato.lean) |
| `EthierKurtzRelativeCompactness` | EK, Chapter 3, Theorem 8.6(b) ⇒ (a): relative compactness | [source](LongRange/Support/External/EthierKurtzSkorokhod.lean) |
| `EthierKurtzRelativeCompactnessStopping` | EK, Chapter 3, Theorem 8.6(c) ⇒ (a), Remark 8.7(b): stopping-time criterion | [source](LongRange/Support/External/EthierKurtzStopping.lean) |
| `EthierKurtzConvergenceFromFdd` | EK, Chapter 3, Theorem 7.8(b): convergence from finite-dimensional laws | [source](LongRange/Support/External/EthierKurtzSkorokhod.lean) |
| `BillingsleySkorokhodPolish` | Billingsley, Theorems 12.1–12.2, with pp. 131 and 166: finite-horizon Skorokhod space | [source](LongRange/Support/External/BillingsleySkorokhod.lean) |

GT denotes Gilbarg–Trudinger, *Elliptic Partial Differential Equations of Second Order*,
Springer, Classics in Mathematics (2001 reprint). MSC denotes Murugan–Saloff-Coste,
*Anomalous threshold behavior of long range random walks*, Electronic Journal of
Probability 20 (2015), no. 74. CKKW denotes Chen–Kim–Kumagai–Wang, *Heat kernel upper
bounds for symmetric Markov semigroups*, Journal of Functional Analysis 281 (2021), 109074.
EK denotes Ethier–Kurtz, *Markov Processes: Characterization and Convergence*, Wiley (1986).
Billingsley refers to *Convergence of Probability Measures*, second edition, Wiley (1999).

The original source cites Chen–Kumagai–Wang (2019) for its off-diagonal heat-kernel bound. The
corrected proof route of the companion uses the Chen–Kim–Kumagai–Wang (2021) Nash and Davies
results, recorded in its bibliography; the formal proof of Step 2 of Proposition 4.1 in the
heat-kernel version uses the same two results.
The applications to the lattice kernel, truncation, normalization, uniform constants,
stopping times and finite-horizon laws are proved in the library.

Three of the Gilbarg–Trudinger formulations are proved at the pinned Lattice-Probability
revision:
[`GilbargTrudingerSupEstimate`](https://github.com/nitromannitol/Lattice-Probability/blob/721505023bc12a20241c73449ec33339fcf4555f/LatticeProb/Analysis/Elliptic/SupEstimateProved.lean),
[`GilbargTrudingerHolderExtension`](https://github.com/nitromannitol/Lattice-Probability/blob/721505023bc12a20241c73449ec33339fcf4555f/LatticeProb/Analysis/Elliptic/HolderExtensionProved.lean)
and
[`GilbargTrudingerWeakHomogeneousUniqueness`](https://github.com/nitromannitol/Lattice-Probability/blob/721505023bc12a20241c73449ec33339fcf4555f/LatticeProb/Analysis/Elliptic/WeakHomogeneousUniquenessProved.lean).
`ChenKimKumagaiWangNash` and `ChenKimKumagaiWangDavies` are proved in this repository
([`chenKimKumagaiWangNash_holds`](LongRange/Support/External/ChenKimKumagaiWangNashProof.lean),
[`chenKimKumagaiWangDavies_holds`](LongRange/Support/External/ChenKimKumagaiWangDaviesProof.lean)).
The April exports still list these as hypotheses, as released.

## Heat-kernel version

The formalization of the second version uses four cited inputs. All four are proved in the
library, and the exports ending in `_unconditional` take no cited hypothesis. For Step 2 of
Proposition 4.1 the paper quotes the stability theory of Chen–Kumagai–Wang (2021) and its
extension to graphs by Malmquist (2023); the formal proof replaces them by the two
Chen–Kim–Kumagai–Wang results below (see D1 in [CORRESPONDENCE.md](CORRESPONDENCE.md)).

| Cited input | Status | Lean |
| --- | --- | --- |
| MSC, Theorem 1.1: on-diagonal bound (Proposition 4.1, Step 1) | proved for the critical lattice kernel, the case the paper uses | `LatticeProb.Graph.LongRangeKernel.weightedLattice_critical_diagonal`, `LatticeProb.Graph.LongRangeKernel.weightedLattice_evenKernelSup_le` |
| CKKW, Proposition 3.1(ii): Nash inequality (formal proof of Proposition 4.1, Step 2) | proved as formulated | `LatticeProb.External.chenKimKumagaiWangNash_holds` |
| Kallenberg (2002), Theorems 16.10 and 16.11, and Aldous (1978): tightness and identification in `D([0, ∞), ℝ^d)` (Theorem 1.2) | proved (the sufficiency direction, for proper separable state spaces) | `LatticeProb.Cadlag.HalfLine.tendsto_of_ordered_fdd_of_optional_increment` |
| CKKW, Theorem 4.4 with Example 4.3: Davies upper bound (formal proof of Proposition 4.1, Step 2) | proved as formulated | `LatticeProb.External.chenKimKumagaiWangDavies_holds` |

Theorems 16.10 and 16.11 of Kallenberg are on pp. 313 and 314 of the second edition (2002). The
general weighted-graph formulations `MuruganSaloffCoste` and `MuruganSaloffCosteUniform` are not
proved. Neither are the Ethier–Kurtz formulations `EthierKurtzRelativeCompactnessStopping` and
`EthierKurtzConvergenceFromFdd`; the forms of Theorem 1.2 below that do not take them use the
Kallenberg–Aldous criterion instead.

Hypotheses of the heat exports, all in `LongRangeHeat.Statements`:

| Paper result | Export | Cited hypotheses |
| --- | --- | --- |
| Proposition 4.1 | `heat_kernel_bounds_unconditional` | none |
| Proposition 4.2 | `aldous_condition_unconditional` | none |
| Proposition 4.3 | `fdd_convergence_unconditional` | none |
| Theorem 1.2 | `annealed_invariance_principle_unconditional` | none |
| Theorem 1.2, unscaled form | `unscaled_invariance_principle_unconditional` | none |
| Proposition 4.1 | `heat_kernel_bounds_of_davies` | `ChenKimKumagaiWangDavies` |
| Proposition 4.2 | `aldous_condition_of_davies` | `ChenKimKumagaiWangDavies` |
| Proposition 4.3 | `fdd_convergence_of_davies` | `ChenKimKumagaiWangDavies` |
| Theorem 1.2 | `annealed_invariance_principle_of_davies` | `ChenKimKumagaiWangDavies` |
| Theorem 1.2, unscaled form | `unscaled_invariance_principle_of_davies` | `ChenKimKumagaiWangDavies` |
| Propositions 4.1–4.3 | `heat_kernel_bounds_proved`, `aldous_condition_proved`, `fdd_convergence_proved` | `ChenKimKumagaiWangNash`, `ChenKimKumagaiWangDavies` |
| Theorem 1.2, both forms | `annealed_invariance_principle_kallenberg`, `unscaled_invariance_principle_kallenberg` | `MuruganSaloffCosteUniform`, `ChenKimKumagaiWangNash`, `ChenKimKumagaiWangDavies` |
| Theorem 1.2, both forms | `annealed_invariance_principle_proved`, `unscaled_invariance_principle_proved` | `ChenKimKumagaiWangNash`, `ChenKimKumagaiWangDavies`, `EthierKurtzRelativeCompactnessStopping`, `EthierKurtzConvergenceFromFdd` |
| Propositions 4.1–4.3 | `heat_kernel_bounds`, `aldous_condition`, `fdd_convergence` | `MuruganSaloffCosteUniform`, `ChenKimKumagaiWangNash`, `ChenKimKumagaiWangDavies` |
| Theorem 1.2, both forms | `annealed_invariance_principle`, `unscaled_invariance_principle` | `MuruganSaloffCosteUniform`, `ChenKimKumagaiWangNash`, `ChenKimKumagaiWangDavies`, `EthierKurtzRelativeCompactnessStopping`, `EthierKurtzConvergenceFromFdd` |

Theorem 1.1 and the other heat exports take no cited hypotheses. The forms without a suffix
are the statements as first formalized and are kept unchanged; each later form drops
hypotheses that have been proved or replaced by proved results.

Checking that the public exports use only `propext`, `Classical.choice` and `Quot.sound`
does not prove these hypotheses: they are ordinary proposition parameters of the theorems.
Different exports use different subsets, visible directly in their declarations.

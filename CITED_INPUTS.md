# Explicit cited propositions

These 16 proposition definitions live in `LatticeProb.External` at the pinned
Lattice-Probability revision `47027b49b6660ee34c323869b0c88b7eb72f1124`.
They are explicit hypotheses wherever used. Their statements are formalized; the cited
results themselves remain unproved inputs. The paper's applications are proved.

The links below give the complete Lean proposition bodies, their source carriers,
quantifier order, constants and bibliographic details at the immutable dependency revision.
The count is of registered proposition formulations, rather than distinct references or
logically independent assumptions. In particular, the library proves that the uniform
Murugan–Saloff-Coste formulation implies the other formulation.

| Proposition in `LatticeProb.External` | Cited result | Exact Lean statement |
| --- | --- | --- |
| `GilbargTrudingerExistence` | GT, Theorem 6.14: classical Dirichlet existence | [source](https://github.com/nitromannitol/Lattice-Probability/blob/47027b49b6660ee34c323869b0c88b7eb72f1124/LatticeProb/External/GilbargTrudingerExistence.lean) |
| `GilbargTrudingerBoundaryRegularity` | GT, Theorem 6.19: boundary regularity | [source](https://github.com/nitromannitol/Lattice-Probability/blob/47027b49b6660ee34c323869b0c88b7eb72f1124/LatticeProb/External/GilbargTrudinger.lean) |
| `GilbargTrudingerSchauderEstimate` | GT, Theorem 6.6: Schauder estimate | [source](https://github.com/nitromannitol/Lattice-Probability/blob/47027b49b6660ee34c323869b0c88b7eb72f1124/LatticeProb/External/GilbargTrudinger.lean) |
| `GilbargTrudingerSupEstimate` | GT, Theorem 3.7: supremum estimate | [source](https://github.com/nitromannitol/Lattice-Probability/blob/47027b49b6660ee34c323869b0c88b7eb72f1124/LatticeProb/External/GilbargTrudinger.lean) |
| `GilbargTrudingerHolderExtension` | GT, Lemma 6.37: Hölder extension | [source](https://github.com/nitromannitol/Lattice-Probability/blob/47027b49b6660ee34c323869b0c88b7eb72f1124/LatticeProb/External/GilbargTrudinger.lean) |
| `GilbargTrudingerZeroBoundaryApproximation` | GT, §7.5: approximation in the Sobolev space with zero boundary values | [source](https://github.com/nitromannitol/Lattice-Probability/blob/47027b49b6660ee34c323869b0c88b7eb72f1124/LatticeProb/External/GilbargTrudingerSobolev.lean) |
| `GilbargTrudingerWeakHomogeneousUniqueness` | GT, Corollary 8.2: uniqueness of homogeneous weak solutions | [source](https://github.com/nitromannitol/Lattice-Probability/blob/47027b49b6660ee34c323869b0c88b7eb72f1124/LatticeProb/External/GilbargTrudingerSobolev.lean) |
| `MuruganSaloffCoste` | MSC, Theorem 1.1, estimate (10): discrete on-diagonal bound | [source](https://github.com/nitromannitol/Lattice-Probability/blob/47027b49b6660ee34c323869b0c88b7eb72f1124/LatticeProb/External/MuruganSaloffCoste.lean) |
| `MuruganSaloffCosteUniform` | MSC, the same theorem with constant dependence traced through its proof | [source](https://github.com/nitromannitol/Lattice-Probability/blob/47027b49b6660ee34c323869b0c88b7eb72f1124/LatticeProb/External/MuruganSaloffCosteUniform.lean) |
| `ChenKimKumagaiWangNash` | CKKW, Proposition 3.1(ii): ultracontractivity implies a Nash inequality | [source](https://github.com/nitromannitol/Lattice-Probability/blob/47027b49b6660ee34c323869b0c88b7eb72f1124/LatticeProb/External/ChenKimKumagaiWang.lean) |
| `ChenKimKumagaiWangDavies` | CKKW, Theorem 4.4 and Example 4.3: Davies upper bound | [source](https://github.com/nitromannitol/Lattice-Probability/blob/47027b49b6660ee34c323869b0c88b7eb72f1124/LatticeProb/External/ChenKimKumagaiWang.lean) |
| `EthierKurtzTrotterKato` | EK, Chapter 1, Theorem 6.1(c) ⇒ (a): semigroup convergence | [source](https://github.com/nitromannitol/Lattice-Probability/blob/47027b49b6660ee34c323869b0c88b7eb72f1124/LatticeProb/External/EthierKurtzTrotterKato.lean) |
| `EthierKurtzRelativeCompactness` | EK, Chapter 3, Theorem 8.6(b) ⇒ (a): relative compactness | [source](https://github.com/nitromannitol/Lattice-Probability/blob/47027b49b6660ee34c323869b0c88b7eb72f1124/LatticeProb/External/EthierKurtzSkorokhod.lean) |
| `EthierKurtzRelativeCompactnessStopping` | EK, Chapter 3, Theorem 8.6(c) ⇒ (a), Remark 8.7(b): stopping-time criterion | [source](https://github.com/nitromannitol/Lattice-Probability/blob/47027b49b6660ee34c323869b0c88b7eb72f1124/LatticeProb/External/EthierKurtzStopping.lean) |
| `EthierKurtzConvergenceFromFdd` | EK, Chapter 3, Theorem 7.8(b): convergence from finite-dimensional laws | [source](https://github.com/nitromannitol/Lattice-Probability/blob/47027b49b6660ee34c323869b0c88b7eb72f1124/LatticeProb/External/EthierKurtzSkorokhod.lean) |
| `BillingsleySkorokhodPolish` | Billingsley, Theorems 12.1–12.2, with pp. 131 and 166: finite-horizon Skorokhod space | [source](https://github.com/nitromannitol/Lattice-Probability/blob/47027b49b6660ee34c323869b0c88b7eb72f1124/LatticeProb/External/BillingsleySkorokhod.lean) |

GT denotes Gilbarg–Trudinger, *Elliptic Partial Differential Equations of Second Order*,
Springer, Classics in Mathematics (2001 reprint). MSC denotes Murugan–Saloff-Coste,
*Anomalous threshold behavior of long range random walks*, Electronic Journal of
Probability 20 (2015), no. 74. CKKW denotes Chen–Kim–Kumagai–Wang, *Heat kernel upper
bounds for symmetric Markov semigroups*, Journal of Functional Analysis 281 (2021), 109074.
EK denotes Ethier–Kurtz, *Markov Processes: Characterization and Convergence*, Wiley (1986).
Billingsley refers to *Convergence of Probability Measures*, second edition, Wiley (1999).

The original source cites Chen–Kumagai–Wang (2019). The corrected proof route uses the
Chen–Kim–Kumagai–Wang (2021) Nash and Davies results, recorded in the corrected bibliography.
The applications to the lattice kernel, truncation, normalization, uniform constants,
stopping times and finite-horizon laws are proved in the library.

Checking that the public exports use only `propext`, `Classical.choice` and `Quot.sound`
does not prove these hypotheses: they are ordinary proposition parameters of the theorems.
Different exports use different subsets, visible directly in their declarations.

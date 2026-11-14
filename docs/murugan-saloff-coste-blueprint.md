# Murugan–Saloff-Coste on-diagonal estimates

This is a research blueprint, not a proof, a source audit, or an assertion that the
cited estimates have been formalized. Its proposed boundaries require statement and
assumption review before implementation. The source is Murugan and Saloff-Coste,
[*Anomalous threshold behavior of long range random walks*](https://personal.math.ubc.ca/~mathav/index_files/moment.pdf),
Electronic Journal of Probability 20 (2015), no. 74, Theorem 1.1. Page and equation
references below refer to this paper. External results invoked by the paper have not
been independently audited here.

## Exact interfaces

The repository revision is `2f6b763405870ed127c9c31ba6681eb58b41c9f7` and its
`lake-manifest.json` pins Lattice-Probability (LP) to
`47027b49b6660ee34c323869b0c88b7eb72f1124`. The pinned files were compared
byte-for-byte with the raw files at that revision:

| Declaration | LP path and line | SHA-256 of file |
|---|---|---|
| `LatticeProb.External.MuruganSaloffCoste` | `LatticeProb/External/MuruganSaloffCoste.lean:23` | `5fd8decdd6b7aca538eba1d813d02990d0e51866259e5b1a3008b60f280765db` |
| `LatticeProb.External.MuruganSaloffCosteUniform` | `LatticeProb/External/MuruganSaloffCosteUniform.lean:26` | `11de94beb287009bc7d20269bad156002098d86f5bfb21718c2dafa7251c9574` |

Both are definitions of propositions, not proofs. The former quantifies a type `X`,
weighted graph `G`, infinitude and connectivity, profiles `V, φ`, exponent `γ`, and
kernel `k`. It assumes bounded positive vertex masses, positive continuous strictly
increasing doubling `V`, homogeneous volume comparison, a positive lower bound on
reference edge transition probabilities, `γ > 1`, the upper and paired-time lower
sub-Gaussian bounds, continuous `φ ≥ 1` with positive regular variation index,
Markov normalization, symmetry, and two-sided jump comparison. For each admissible
inverse scale `ζ`, it concludes a *single* positive `C` giving both bounds on
`sup_x k_{2n}(x,x)` for every `n : ℕ`, including zero. This `C` is chosen after `k`
and `ζ`; all earlier existential comparison constants may influence it.

The uniform definition moves `k` and its Markov, symmetry and comparison premises
after `∃ C`, while placing `ζ` and a fixed positive `C_φ` before it. It also retains
both inequalities and all natural times. Its order is
`∀ G,V,φ,γ [graph hypotheses] ζ [inverse] C_φ [positive], ∃ C > 0,
∀ k [Markov] [symmetric] [J_φ with this C_φ], ∀ n, ...`.
Thus the literal theorem's `∀ k, ∃ C` does not by itself furnish this `∃ C, ∀ k`.
`uniform_implies_literal` in the uniform file at line 60 proves the reverse
implication, conditional on the uniform proposition.

The graph structure (`Graph/LongRangeKernel/WeightedGraph.lean:21–85`) has a
locally finite simple graph and symmetric nonnegative edge weights positive exactly
on edges; vertex mass is the neighbor sum, balls are closed, volume is an `ENNReal`
sum, the reference density is `weight/(mass x * mass y)`, density powers use
weighted convolution, and time zero is inverse mass on the diagonal. `IsMarkovDensity`
requires each weighted row sum equal one. `Scale.lean:16–39` defines `η` by the
integral formula with value `γ * φ 0` at zero and requires both asymptotic inverse
compositions, continuity, monotonicity and `ζ ≥ 1`. `ENNReal.ofReal` converts all
real comparisons, so positivity and finite-mass conversions must be proved explicitly.
The source assumes the same density normalization and closed balls (pp. 2–4). A
full check of measurable/countable operator domains and all `ENNReal` conversions
remains necessary; no equivalence to the paper's operator language is assumed here.

The independent CLRC vocabulary declaration at
`LongRangeAudit/QuenchedInvariance/Vocabulary/MuruganSaloffCoste.lean:28` uses its
own graph and scale vocabulary. `SolutionBridge.lean:79` proves the implication from
that independent input to the production input using copies and definitional
identities; it does not prove either input. The literal branch is used in
`LongRange/HeatKernel/OnDiagonal.lean:69` and ultimately in walk tightness and the
quenched invariance statement. The separate uniform branch is essential for
`LongRange/HeatKernel/UniformOnDiagonal.lean:146`: `∃ C > 0` precedes all fields
`a` obeying `lam ≤ a e ≤ lam⁻¹`, all `t : ℝ≥0` and `x,y`. Its line 255 specializes
to constant conductance in dimension one. `LongRange/Statements/HeatKernel.lean:17`
exports the former; uniform off-diagonal and rescaled estimates also consume it.

## Source dependency graph

Arrows mean mathematical dependencies to be proved or explicitly supplied, not extra
premises to add to either proposition. Source pages identify the written route;
external inputs have not been expanded into a complete proof graph.

1. **Standing setup (pp. 2–4):** weighted graph, induced measure, volume doubling,
   reference sub-Gaussian estimates, regular variation and `(J_φ)`. Derive polynomial
   volume ratios (4), finiteness/countability of balls, Markov/self-adjoint operator
   calculus and the supremum/`L¹ → L²` identity (9). The paper cites [17] for (9).
2. **Reference graph regularization (p. 8–10):** define `Q=(P+P²)/2`; expand its
   powers as a binomial mixture to derive Lemma 2.2 (22)–(23) from (6)–(7), doubling
   and the binomial concentration estimate (24). Lemma 1.4's spectral inequality
   gives Lemma 2.3 comparing `P` and `Q` resistances; Lemma 2.2 plus energy
   telescoping gives Lemma 2.4 (25)–(28).
3. **Subordination (pp. 10–13):** regular variation and Potter estimates ensure
   convergence and normalization of `c_φ Σ_{n≥1} Q^{2⌊n^γ⌋}/(n φ(n))`. Lemma 2.2,
   volume ratios, Potter bounds and integral comparisons yield Proposition 2.5,
   the two-sided kernel comparison (30). Its Dirichlet form is comparable to that
   of every `K` with the fixed `(J_φ)` constant. Together with Lemma 2.4 and the
   sum-to-integral estimate (37), this yields pseudo-Poincaré Proposition 2.1 (20).
4. **Scale analysis (pp. 13–14):** Lemma 3.1 uses Bingham–Goldie–Teugels [8],
   Propositions 1.5.8, 1.5.9a, 1.5.10, 1.5.12, 1.5.1 and Theorems 1.8.2 and 1.5.3:
   show `η` has index `min(β,γ)`, `η ≤ Cφ`, the monotone envelope is asymptotic to
   `η`, and any admissible `ζ` has the necessary inverse comparisons (40) and
   regular-variation bounds. The theorem asks for the supplied inverse, so the
   comparison must cover *every* `ζ` satisfying the Lean predicate, not just a
   specially chosen inverse.
5. **Upper branch (pp. 14–17):** averaging on balls, (3), pseudo-Poincaré and
   positivity of `K²` give Nash inequality Theorem 3.2. A Nash-to-ultracontractivity
   result [17, Thm 2.2.1] or [9, Prop IV.1], the integral estimates in Theorem 3.3,
   Potter's theorem [8, Thm 1.5.6] and (40) yield the upper half of (10).
6. **Lower branch (pp. 17–19):** Lemma 1.5 (self-adjointness and Cauchy–Schwarz)
   gives spectral-radius bound (57). The resistance lower bound (8), cited from
   Grigor'yan–Telcs [21, Thm 3.1], and Lemma 2.3 produce finite-support test functions
   with (61). Proposition 2.5 and Lemma 1.4 bound their `K²` energy by the series
   (62). The tail estimate [8, Prop 1.5.10], Potter and integral comparison
   (63)–(64) yield `λ(B(x,R)) ≥ 1-C/η(R)`, and (40) gives the lower half for large
   times. The paper dispatches remaining times using `(J_φ)` (p. 19); this finite-time
   step needs an explicit uniform proof, including `n=0`.
7. **Assembly:** Theorems 3.3 and 4.1 imply Theorem 1.1, with one enlarged constant
   for both sides. The uniform proposition needs the entire graph implemented with
   constants chosen before the variable kernel; then `uniform_implies_literal`
   supplies the literal production interface. An independent vocabulary proof or
   exact source audit is still required for the independent declaration.

## Constant dependence and unresolved obligations

The paper states Theorems 3.3 and 4.1 for a fixed kernel, without explicitly
quantifying the uniform form. The displayed route suggests uniformity because `K`
enters Proposition 2.1 through comparison with `Q_φ`, and in (59) through its
comparison with the same subordinate kernel. This is a proposed argument, not a
verified uniform theorem: check every implicit constant, all operator identities,
external theorems and thresholds, keeping the graph, `V`, `φ`, `γ`, `ζ`, graph
comparison witnesses and `C_φ` fixed before choosing any bound. In particular,
small-time lower bounds and the `n=0` upper and lower bounds must depend only on
those fixed data; upper bounds can use Markov normalization and bounded inverse
masses, while a uniform lower bound for finite positive times needs the diagonal
part of `(J_φ)` and the fixed mass and profile bounds. Verify exact constants and
all cases before relying on this sketch.

The source uses results beyond the article: (8) from [21]; regular variation and
asymptotic inversion from [8]; (9) and Nash-to-ultracontractivity from [17] or [9].
Their assumptions, proof availability, and quantitative constant dependence are
open. The fixed-data uniformity claim and the source-to-Lean translation therefore
remain open. The paper's regular-variation assumptions do not require `φ` to be
monotone; adding such a condition is not an admissible shortcut.

## Reuse and proposed implementation boundaries

LP `Prob/RegularVariation.lean` defines regular variation and provides Potter
bounds with an **antitone** hypothesis; these cannot directly be applied to general
`IsJumpScale`. `Graph/LongRangeKernel/Scale.lean` establishes positivity and
integrability of the scale. The pinned LP provides lattice-specific volume,
Gaussian and inverse-scale results (`LatticeDistance`, `LatticeGaussianLower`,
`CriticalAsymptotics`, `CriticalVolume`) and a conditional
`External.lattice_uniform_estimate` at uniform file line 69. These discharge
reference-lattice hypotheses only after the uniform proposition is assumed. The
consumer uses `unitRates_density_profile_uniform`, `densityPower_one_eq`,
`kernelPow_le_sqrt_diag_half` and `poisson_average_profile_le` to pass from that
conditional discrete-time bound to a uniform continuous-time bound. The lower half
of the general cited proposition is retained even though this consumer uses the
upper half. LP `Network/Variational.lean` and `Graph/Nash.lean` are possible
infrastructure, not established matches for the graph resistance or general Nash
results. A search of available Mathlib and LP material found no full MSC proof;
no Armstrong repository match is identified. These are discovery results, not
exhaustive nonexistence claims.

Candidate boundaries, subject to review and exact source-facing interfaces:

1. Countable weighted graph density/operator and Dirichlet-form infrastructure,
   including identity (9) and spectral comparisons.
2. General nonmonotone regular variation, inversion, Potter and sum/integral
   estimates, with dependence on the fixed profiles recorded.
3. `Q` heat estimates and subordinate kernel comparison, then pseudo-Poincaré.
4. Nash inequality and quantitative ultracontractivity for the upper bound.
5. Source-audited resistance estimate and finite-support test functions; lower
   bound via spectral radius and explicit small times.
6. Joint uniform two-sided assembly; literal and independent-vocabulary adapters,
   followed by consumer and axiom checks. No proof boundary is a new assumption.

The resistance theorem and analytic black boxes may themselves require substantial
separate projects. Each boundary must identify exact hypotheses, upstream proofs,
constant scope and independent source review before it is treated as a proof task.

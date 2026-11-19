# Paper–Lean correspondence

The specification is *Quantitative homogenization for the critical long-range random
conductance model*, arXiv:2604.21143v1, included unchanged in `paper/`.
The corrected companion preserves the abstract and all three main theorem statements.
Paper labels identify the source statements. The table includes semantic units, consumed
proof ingredients, repetitions and context; these categories do not count as additional theorems.
All 23 theorem exports and three complete definition exports are available through
`import LongRange.Statements`. A compiling declaration alone does not certify a source match.
Cited propositions remain explicit assumptions; see [CITED_INPUTS.md](CITED_INPUTS.md).

The main export produces an actual `H10 U` weak solution, proves uniqueness among all
`H10 U` weak solutions, and identifies its unique continuous classical representative.
Sites denote physical positions `ε * q`; corrector slopes use these positions.
The lattice kernel and source diameters use the Euclidean norm.
The heat-kernel constants are chosen before the admissible conductance field.
The three definitions retain their complete bodies and associated characterizations.

| Paper label or source unit | Role | Lean declaration or supporting ingredients |
| --- | --- | --- |
| `sumesonthelattice`, `e.lattice.upper`, `e.lattice.upperlong`, `e.lattice.diagonal`, `e.lattice.mixed` | numbered assertion | `LongRange.Statements.lattice_sums` |
| `l.path` | numbered assertion | `LongRange.Statements.path_counting` |
| `l.single.scale`, `e.single.scale` | numbered assertion | `LongRange.Statements.single_scale_estimate` |
| `p.poincare`, `e.poincare` | numbered assertion | `LongRange.Statements.poincare` |
| `l.corrector.monotonicity`, `e.corrector.monotonicity`, `e.corrector.monotonicity.norms` | numbered assertion | `LongRange.Statements.corrector_monotonicity` |
| `p.dirichlet`, `e.dirichlet.as` | numbered assertion | `LongRange.Statements.corrector_energy_bound` |
| `p.corrector.domain`, `e.defcorrector`, `e.corrector.bounds` | numbered assertion | `LongRange.Statements.corrector_domain_bound` |
| `prop:concentrationineq`, `ineq:Hoeffdinginfinitesum` | numbered assertion | `LongRange.Statements.hoeffding_infinite` |
| `prop.McDiarmid` | numbered assertion | `LongRange.Statements.mcdiarmid` |
| `main.thm`, `e.main.equations`, `e.minimal.scale`, `e.quenched.rate` | numbered assertion | `LongRange.Statements.main_theorem` |
| `p.heatkernel`, `e.hk.upper` | numbered assertion | `LongRange.Statements.heatkernel_onDiagonal` |
| `p.heatkernel.offdiag`, `e.hk.offdiag` | numbered assertion | `LongRange.Statements.heatkernel_offDiagonal` |
| `t.qip`, `e.geps`, `e.barsigma` | numbered assertion | `LongRange.Statements.quenched_invariance_principle` |
| `t.walk.intro` | numbered assertion | `LongRange.Statements.quenched_invariance_principle_intro` |
| `p.tightness` | numbered assertion | `LongRange.Statements.tightness` |
| Finite-horizon Aldous criterion with marginal tightness and stopping increments. | numbered assertion | `LongRange.Statements.aldous` |
| `e.nu`, `eq:elleqdefnu`, `eq:comparisonnuandphi` | independent assertion | `LongRange.Statements.corrector_linear_quadratic` |
| `rem:nu-lower-bound`, `eq:nu-lower`, `sec:poincare` | independent assertion | `LongRange.Statements.corrector_energy_lower_bound` |
| `eq:scalingidentities` | independent assertion | `LongRange.Statements.weak_scaling_obstruction` |
| `e.hk.offdiag.rescaled` | independent assertion | `LongRange.Statements.rescaled_kernel`<br>`LongRange.Statements.rescaled_density`<br>`LongRange.Statements.rescaled_killed_density` |
| `eq:gissolenoidal` | semantic assertion | `LongRange.Statements.solenoidal_equivalence` |
| `e.Hm1crit` | definition semantics | `LongRange.Statements.critical_dual_norm`<br>`LongRange.Statements.critical_dual_characterization` |
| `e.nu`, `eq:elleqdefnu`, `eq:comparisonnuandphi` | definition semantics | `correctorFunctional`<br>`correctorEnergy`<br>`IsCorrectorMinimizer`<br>`IsCorrectorSolution`<br>`summable_correctorFunctional`<br>`existsUnique_correctorMinimizer`<br>`isCorrectorMinimizer_iff`<br>`corrector_wellDefined`<br>`correctorEnergy_eq_neg_functional`<br>`correctorEnergy_nonneg`<br>`correctorEnergy_eq_bilinForm`<br>`correctorEnergy_comparison` |
| `e.Leps`, `a.U` | definition semantics | `jumpKernel`<br>`kappa`<br>`latticeSet`<br>`SupportedIn`<br>`l2NormSq`<br>`linearFn`<br>`AssumptionU`<br>`meanConductance`<br>`generator`<br>`summable_generator_bounded`<br>`summable_generator_affine` |
| `e.H1crit` | definition semantics | `h1CritSq`<br>`bilinForm`<br>`summable_h1CritSq`<br>`bilinForm_self_bounds` |
| `e.Daeps` | semantic assertion | `bilinForm_self_bounds` |
| `e.kappaeps` | consumed implementation | `LongRange.Statements.lattice_sums`<br>`kappa_asymptotic`<br>`kappa_le`<br>`le_kappa` |
| Minimal-scale threshold, exponential tail, infinity convention for no admissible threshold. | consumed implementation | `LongRange.Statements.main_theorem`<br>`measurable_minimalScale`<br>`mem_of_minimalScale_le`<br>`measure_minimalScale_tail`<br>`main_theorem` |
| Expected upper/lower corrector scale, with no matching error lower bound. | repetition | `LongRange.Statements.corrector_energy_bound`<br>`LongRange.Statements.corrector_energy_lower_bound` |
| Annulus sum tends to d*V_d*log(2) with o(1) error. | independent assertion | `LongRange.Statements.annulus_limit`<br>`kappa_half_sub_eq_annulus_sum`<br>`tendsto_kappa_half_sub`<br>`kappa_half_ratio_order`<br>`annulus_limit` |
| `main.thm`, `e.main.equations`, `e.minimal.scale`, `e.quenched.rate` | consumed implementation | `LongRange.Statements.main_theorem`<br>`LongRange.Statements.weak_scaling_obstruction`<br>`classical_solution_has_weak_graph`<br>`exists_weak_classical_solution`<br>`exists_weak_solution_main_estimate`<br>`weak_source_scaling_obstruction`<br>`main_theorem`<br>`weak_scaling_obstruction` |
| `e.jump.rates`, `fig:qip` | repetition | `LongRange.Statements.main_theorem`<br>`LongRange.Statements.quenched_invariance_principle_intro` |
| `eq:upperboundO2norm` | cited material | `OsBound`<br>`osBound_const`<br>`osBound_moment` |
| `e.Sk`, `e.slab.mass` | proof ingredient | `LongRange.Statements.single_scale_estimate`<br>`LongRange.Statements.poincare` |
| `fig:pathcount` | proof ingredient | `LongRange.Statements.path_counting` |
| `eq:upperboundnusolenoidal`, `fig:cycle`, `e.gp.def`, `eq:nonnearestg`, `ineqforgp`, `def:defsigmap`, `eq:defnepsstep2`, `eq:expectationF`, `eq:estimateLRterm`, `eq:upperboundsigmaSR`, `eq:influenceshortrangeedges` | proof ingredient | `LongRange.Statements.corrector_energy_bound` |
| `e.Tk`, `e.contraction`, `e.exit`, `e.triangle`, `e.energy.control`, `fig:slab` | proof ingredient | `LongRange.Statements.single_scale_estimate` |
| Disjoint-shell summation and normalization. | proof ingredient | `LongRange.Statements.poincare` |
| Energy bound and Poincare consequence. | proof ingredient | `LongRange.Statements.corrector_domain_bound` |
| Variational comparison and norm consequence. | proof ingredient | `LongRange.Statements.corrector_monotonicity` |
| `e.defHomogtheorem`, `e.ubar0`, `e.weps`, `e.weps.approx`, `e.product.bi.phi`, `e.Rtilde`, `e.rdef`, `e.r.lip`, `e.residual.decomp`, `e.E1sm.def`, `e.E1bd.def`, `e.E2.def`, `e.second.moment.normalised`, `e.block.eps`, `e.micro.corrector`, `e.scaling.L2`, `e.scaling.H1`, `e.phi.enlarged`, `e.phi.block`, `e.Am.fail`, `e.Rtilde.bounds`, `e.B1.bound`, `e.E1bd.CS`, `e.E1bd.bound`, `e.F1.micro`, `e.F1.fixed`, `e.F1.modulus`, `e.F1.fail`, `e.quenched.onblock` | proof ingredient | `LongRange.Statements.main_theorem` |
| `e.displacement.tail` | proof ingredient | `LongRange.Statements.tightness` |
| `e.resolvent.conv`, `e.semigroup.convergence`, `e.Xi.recursion`, `e.killed.markov` | proof ingredient | `LongRange.Statements.quenched_invariance_principle` |
| `e.lattice.sub`, `e.lattice.integral`, `e.shell.asymp` | proof ingredient | `LongRange.Statements.lattice_sums` |
| `p.heatkernel.offdiag`, `e.hk.offdiag` | proof ingredient | `LongRange.Statements.heatkernel_offDiagonal` |
| Priority, unpursued extensions, shell-CLT intuition and related literature. | context | Context or cited material |
| Bibliography and end matter; cited inputs are assumptions when explicit in Lean. | context | Context or cited material |

## Heat-kernel version

The following refers to [`heat-kernel-without-ECP-v2.tex`](paper/heat-kernel-without-ECP-v2.tex).
Names below are in `LongRangeHeat.Statements`. Where a result has several exports, the first one
listed has the fewest cited hypotheses; [CITED_INPUTS.md](CITED_INPUTS.md#heat-kernel-version)
lists the hypotheses of each.

| Paper result | Lean declaration |
| --- | --- |
| Theorem 1.1 | `main_theorem` |
| Theorem 1.2 | `annealed_invariance_principle_unconditional` (also `annealed_invariance_principle_of_davies`, `annealed_invariance_principle_kallenberg`, `annealed_invariance_principle_proved`, `annealed_invariance_principle`) |
| Theorem 1.2, unscaled form | `unscaled_invariance_principle_unconditional` (also `unscaled_invariance_principle_of_davies`, `unscaled_invariance_principle_kallenberg`, `unscaled_invariance_principle_proved`, `unscaled_invariance_principle`) |
| Lemma 2.1 | `dirichlet_form` |
| Lemma 2.2 | `sampling` |
| Lemma 2.3 | `O_squares`, `O_expectation`, `O_sums`, `O_sums_countable`, `O_integrals`, `O_constants` |
| Lemma 3.1 | `mean_operator_consistency` |
| Proposition 3.2 | `forcing_representation` (also `forcing_representation_of_increment`) |
| Lemma 3.3 | `G_gaussian_tails` (also `G_gaussian_tails_of_increment`) |
| Proposition 4.1 | `heat_kernel_bounds_unconditional` (also `heat_kernel_bounds_of_davies`, `heat_kernel_bounds_proved`, `heat_kernel_bounds`) |
| Proposition 4.1, Step 1, discrete on-diagonal bound | `LatticeProb.Graph.LongRangeKernel.weightedLattice_critical_diagonal`, `LatticeProb.Graph.LongRangeKernel.weightedLattice_evenKernelSup_le` |
| Proposition 4.1, Step 2, Nash inequality | `LatticeProb.External.chenKimKumagaiWangNash_holds` |
| Proposition 4.1, Step 2, Davies estimate | `LatticeProb.External.chenKimKumagaiWangDavies_holds` |
| Proposition 4.2 | `aldous_condition_unconditional` (also `aldous_condition_of_davies`, `aldous_condition_proved`, `aldous_condition`) |
| Proposition 4.3 | `fdd_convergence_unconditional` (also `fdd_convergence_of_davies`, `fdd_convergence_proved`, `fdd_convergence`) |
| (1.3), (1.4): the lattice and continuum heat equations | `lattice_heat_equation`, `continuum_heat_equation` |
| (1.7), scaling identities and normalization | `scaling_identity`, `kappa_halving_increment`, `kappa_halving`, `scaling_obstruction` |
| (2.3) | `second_moment` |
| (2.6), (2.7) | `increment_bound`, `taylor_bound` |
| (3.2) | `telescoping` |
| Measurability of the maps in Proposition 4.3 and Theorem 1.2 | `measurable_fdd_maps`, `measurable_scaled_path` |

`lattice_heat_equation` states that the exponential series defining `latticeHeat` converges,
that it solves (1.3) with the restricted initial data and summable generator series, and that it
is the only bounded classical solution. `continuum_heat_equation` states that `continuumHeat`
solves (1.4) with initial data `f`, including the right time derivative at every `t ≥ 0` that
Lemma 3.1 uses through `derivWithin`. `measurable_fdd_maps` and `measurable_scaled_path` state
that the evaluation maps and space-time scalings along which Proposition 4.3 and the unscaled
form of Theorem 1.2 push laws forward are measurable.

### Cited inputs

The step of Proposition 4.1 that the paper takes from Murugan–Saloff-Coste,
*Electronic Journal of Probability* 20 (2015), Theorem 1.1, is proved in the library for the
critical lattice kernel, following Sections 2 and 3 of that article (the subordinated kernel,
the pseudo-Poincaré inequality, the Nash inequality and its iteration), with one constant for
all kernels satisfying the lower jump bound. Chen–Kim–Kumagai–Wang, *Journal of Functional
Analysis* (2021), Proposition 3.1(ii), is proved as formulated, following Coulhon's argument
(*J. Funct. Anal.* 141 (1996), Proposition II.2) for the semigroup `e^{-δt} P_t`; the
monotonicity of the profile and `δ ≥ 0` are not used. Theorem 1.2 is proved along the paper's
route from Propositions 4.2 and 4.3 and the criterion of Kallenberg (2002), Theorems 16.10 and
16.11, with Aldous (1978), proved in `LongRangeHeat/KallenbergCriterion.lean`. The paper prints
these as Theorems 14.10 and 14.11; in the second edition (2002) cited in its bibliography they
are Theorems 16.10 (p. 313) and 16.11 (p. 314), with Lemmas 16.12–16.13 used in the proof of the
latter. The paper source in `paper/` is kept as written; the library text uses the second-edition
numbers. Chen–Kim–Kumagai–Wang, Theorem 4.4 with Example 4.3 (the Davies estimate), is proved
as formulated (`LongRange/Support/External/ChenKimKumagaiWangDaviesProof.lean`, with the
argument in `LongRange/Support/Analysis/Davies/`), following the source's proof of Theorem 4.4
through Proposition 4.5 with `s = 1/2`: the perturbed semigroup, the derivative of
`‖P^ψ_t f‖_{2p}^{2p}`, the comparison with the Nash profile, the geometric time grid
`t(1 - λ^{-k})` with the product of Example 4.3, duality and the semigroup law, and the
reduction from `θ` to `c₁⁻¹ θ*(c₂⁻¹ ·)`. No cited input of the heat-kernel version remains a
hypothesis.

### Deviations from the paper's proofs

The formalization proves the paper's statements; at the following steps the proof differs
from the paper's argument.

* **D1. Proposition 4.1, Step 2, the off-diagonal bound (4.5).** The paper applies the stability
  theorem of Chen–Kumagai–Wang (Theorem 1.15) on graphs, with Malmquist (2023), checking
  FK(φ) via their Proposition 7.6, the jump upper bound J_{φ,≤} from `a ≤ λ⁻¹`, and CSJ(φ) from
  an explicit cutoff. The formalization truncates the jumps at a scale ρ with a Meyer
  comparison (`LongRange/HeatKernel/Truncated.lean`), obtains a Nash inequality for the
  truncated form from the on-diagonal decay by Chen–Kim–Kumagai–Wang, Proposition 3.1(ii),
  applies their Davies bound (Theorem 4.4 with Example 4.3) with Euclidean tent functions
  (`Tent.lean`, `UniformDavies.lean`), and combines three truncation regimes into the minimum
  bound (`PropositionA.lean`, `UniformOffDiagonal.lean`). The conclusion (4.5) and the uniform
  constant `C(d, λ)` are the paper's. Both Chen–Kim–Kumagai–Wang results used on this route are
  proved; the stability theorem of Chen–Kumagai–Wang is not used.
* **D2. Theorem 1.2, assembly.** `annealed_invariance_principle` and
  `annealed_invariance_principle_proved` obtain relative compactness from the stopping-time
  criterion of Ethier–Kurtz (Chapter 3, Theorem 8.6(c) ⇒ (a), Remark 8.7(b)), with compact
  containment from Proposition 4.1(ii), and convergence from Ethier–Kurtz, Theorem 7.8(b). The
  forms ending in `_kallenberg` and `_of_davies` follow the paper: conditions (i) and (ii) of the
  Kallenberg–Aldous criterion, from Propositions 4.3 and 4.2. The criterion is proved for proper
  separable metric state spaces, with convergence of the finite-dimensional laws at all times
  and only its sufficiency direction, which is what the theorem uses.
* **D3. Proposition 4.2.** The paper applies the strong Markov property at the stopping times
  `τ_n`. The formalization proves the increment bound conditionally on events of the canonical
  σ-algebra at fixed times (`Aldous.lean`), applies it at the dyadic approximations
  `⌈2^k τ⌉ / 2^k` from above, and lets `k → ∞` by right continuity of the paths: the textbook
  proof of the strong Markov property, used in inequality form.
* **D4. Proposition 4.3, end of Step 1 and Step 2.** The paper extends the convergence of
  `∫ g` from `g ∈ C_c^∞` to `C_0(ℝ^d)` by density and uses Stone–Weierstrass density of tensor
  products in `C_0((ℝ^d)^k)`. The formalization proves tightness of the annealed
  finite-dimensional laws from Proposition 4.1(ii) (`FddTight.lean`) and convergence of the
  integrals of products `∏_{j ∈ S} (c_j + ψ_j)` over a separating subalgebra of bounded
  continuous functions (`FddAlgebra.lean`, `FddWeak.lean`), and concludes by Mathlib's
  `ProbabilityMeasure.tendsto_of_tight_of_separatesPoints`.
* **D5. (2.6) and (2.7).** The paper uses Taylor's formula with integral remainder for `ū_s`,
  Minkowski's inequality in `L²(εℤ^d)` and Lemma 2.2 at the translates `y = θz`. The
  formalization (`Sampling.lean`) bounds the increment `f(· + z) - f`, respectively the Taylor
  remainder of `f`, pointwise by `C min(|z|, 1)`, respectively `C |z|³`, with support in two
  balls, writes the increment or remainder of `ū_s` as the heat flow of that of `f`, and
  concludes by the counting and Jensen steps of the proof of Lemma 2.2.

The proofs of the cited inputs differ from their sources as follows. Murugan–Saloff-Coste: the
weak law in the binomial window is obtained from a Chernoff bound for `n ≥ 128` and a finite
minimum; an explicit integral test and a factorial bound replace Potter's bound and
Bingham–Goldie–Teugels 1.5.10; the block ratio is `2n / b` instead of `4R^γ / k^γ`; the
balancing radius is found by the intermediate value theorem with the explicit scale
`s / (1 + log(1 + s))` instead of `η̃ ∘ V⁻¹`; and Theorem 3.3 is obtained by the integral
comparison of Pittet–Saloff-Coste (survey Theorem 3.3.2) applied to `‖K^n δ_x‖²` instead of
(49)–(55). Kallenberg–Aldous: the modulus condition is used in the form of explicit partitions
with small oscillation (the modified modulus of Ethier–Kurtz, Chapter 3), bounded through outer
measure, so that measurability of the modulus is not needed; completeness of the Skorokhod space
follows Ethier–Kurtz, Chapter 3, Theorem 5.6. Chen–Kim–Kumagai–Wang, Theorem 4.4 with
Example 4.3:

* The source works with a regular Dirichlet form on `L²(E; m)`. The formalization proves the
  estimate for symmetric jump forms with killing on a finite set, where the semigroup is a
  matrix exponential, every norm is a finite sum and the exponents `2p = 2^k` are natural
  numbers (`FiniteForm.lean` to `DaviesFinite.lean`). It passes to the countable state space
  through the chains killed outside finite sets `U ↑ S`: their kernels converge to the full
  kernel (`KilledConvergence.lean`), the energy of the extension by zero is the killed form, so
  the Nash inequality restricts (`KilledEnergy.lean`), and the finite Davies functional is at
  most the full one (`Killed.lean`).
* Example 4.3 takes the perturbation inequality for the twisted form from Carlen–Kusuoka–Stroock
  (their (3.10) and the end of the proof of their Theorem 3.9), which the source does not
  reprove. For jump forms it is proved directly from two-point inequalities
  (`Perturbation.lean`, `PowerInequality.lean`, `PowerPerturbation.lean`, `TwistedForm.lean`,
  `TwistedPowerForm.lean`), with `s = 1/2`, error `Λ(ψ)²` at `p = 1` and `(2p + 1) Λ(ψ)²` for
  `p ≥ 2`, in place of the source's `(1 + 8p²) Λ(ψ)²`. Only the error at `p = 1` enters the
  conclusion.
* The source integrates the differential inequality for the normalized power sums with the
  chain rule for `∫ 1/θ`, which needs continuity of `θ`; Theorem 4.4 does not assume it. The
  formalization integrates against the monotone lower profile `c₁⁻¹ θ*(c₂⁻¹ ·)` and replaces
  the chain rule by a comparison of right Dini derivatives (`Comparison.lean`).
* The passage from the `L^{2p}` bounds to the pointwise bound uses
  `|f(i)| ≤ (∑_j |f(j)|^q)^{1/q}` at each grid level and a single limit along the grid, instead
  of a limit of norms as `p → ∞`. The duality step bounds `P^ψ_{2s}(i, j)` by Cauchy–Schwarz
  in `P^ψ_{2s} = P^ψ_s P^ψ_s`, with the columns of `P^ψ_s` the rows of `P^{-ψ}_s` by symmetry.

### Generator series in the statements

The pointwise series defining `generator` and `meanGenerator`
(`LongRange/Model/Operator.lean`) appear in the bounds of `dirichlet_form`,
`forcing_representation` and `mean_operator_consistency` without a summability conjunct. A
complete export would add companion statements asserting, for each lattice function `v` in those
bounds, `∀ q, Summable (fun w => if hw : w = 0 then 0 else a (edgeAdd q w hw) * (v (q + w) - v q)
* jumpKernel (physical ε w))`, and the analogous statement for the kernel of `meanGenerator`.
They would follow from `summable_generatorPair`, `memL2_generator` and
`summable_generator_of_bounded`; `lattice_heat_equation` contains this statement for
`latticeHeat`.

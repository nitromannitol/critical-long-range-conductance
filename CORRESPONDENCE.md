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

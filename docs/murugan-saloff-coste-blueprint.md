# Murugan–Saloff-Coste: critical lattice upper estimate

This blueprint inventories a proposed proof; it proves no heat-kernel estimate and
adds no assumption to a source theorem. The target is the critical lattice upper
estimate needed by the present consumers, not the general weighted-graph two-sided
Murugan–Saloff-Coste propositions. In particular, proving the target does not prove
`MuruganSaloffCoste` or `MuruganSaloffCosteUniform`.

The source is Murugan and Saloff-Coste, [*Anomalous threshold behavior of long
range random walks*](https://personal.math.ubc.ca/~mathav/index_files/moment.pdf),
Electronic Journal of Probability 20 (2015), no. 74. Page numbers below refer to
the linked **24-page preprint**, not the journal pagination. Theorem 3.3 is the
fixed-kernel upper estimate; the paper does not explicitly supply the uniform
quantifier order below.

## Exact targets

At repository revision `2f6b763405870ed127c9c31ba6681eb58b41c9f7`, the manifest
pins Lattice-Probability (LP) at `47027b49b6660ee34c323869b0c88b7eb72f1124`.
Pinned `LatticeProb/External/MuruganSaloffCosteUniform.lean:69–82` gives the
lattice interface conditionally on the general uniform proposition. The target
is exactly its upper conclusion without that condition or the lower conjunct:

```lean
∀ {d : ℕ} (hd : 0 < d) (C_φ : ℝ), 0 < C_φ →
  ∃ C : ℝ, 0 < C ∧ ∀ k : Site d → Site d → ℝ≥0∞,
    IsMarkovDensity (weightedLattice d hd).mass k →
    (∀ x y, k x y = k y x) →
    (∀ x y,
      ENNReal.ofReal (C_φ⁻¹ / (latticeVolumeProfile d ((lattice d).dist x y) *
        quadraticScale ((lattice d).dist x y))) ≤ k x y ∧
      k x y ≤ ENNReal.ofReal (C_φ / (latticeVolumeProfile d ((lattice d).dist x y) *
        quadraticScale ((lattice d).dist x y)))) →
    ∀ n : ℕ,
      evenKernelSup (weightedLattice d hd).mass k n ≤
        ENNReal.ofReal (C / latticeVolumeProfile d (criticalInverse n))
```

The constant is chosen after `d` and the fixed positive `C_φ`, before `k`, and
works for every natural `n`, including zero. The distance is the pinned graph
distance, the mass is the pinned counting mass, the power is weighted density
convolution, and the profiles and `ENNReal.ofReal` normalization are exactly
those in the pinned interface. No heat-kernel bound, Nash inequality, MSC
proposition, or uniformity assumption may be added to this statement.

The source-facing completion target is the exact conclusion of
`LongRange/Statements/HeatKernel.lean:17–25` without `hMSC`:

```lean
(d : ℕ) (hd : 1 ≤ d) {lam : ℝ} (hlam : 0 < lam) :
  ∃ C : ℝ, 0 < C ∧ ∀ a : Edge d → ℝ,
    ∀ ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹,
    ∀ (t : ℝ≥0) (x y : Site d),
      ((unitRates hd hlam a ha).transitionKernel t x).real {y} ≤
        C * (1 + t * Real.log (2 + t)) ^ (-((d : ℝ) / 2))
```

The existing declaration remains frozen; introduce a reviewed successor and
adapters under the applicable freeze workflow. The target quantifies one `C`
before every admissible field `a`, time and sites. It retains the existing
unit-rate transition kernel and ellipticity premises verbatim.

## Actual consumers and available inputs

The pinned general `MuruganSaloffCoste.lean:23` and
`MuruganSaloffCosteUniform.lean:26` define **unproved propositions**. The
former chooses its constant after the kernel and the latter before the kernel;
`uniform_implies_literal` at `Uniform.lean:60` is proved only conditionally.
Their file SHA-256 values are respectively
`5fd8decdd6b7aca538eba1d813d02990d0e51866259e5b1a3008b60f280765db` and
`11de94beb287009bc7d20269bad156002098d86f5bfb21718c2dafa7251c9574`.
The independent CLRC vocabulary proposition and `SolutionBridge.lean:79` are
also conditional; the bridge proves an implication, not the cited input.

`LongRange/HeatKernel/UniformOnDiagonal.lean:146–185` calls the conditional
lattice specialization and uses only `(hbound' n).2`. Its result feeds
`UniformDavies.lean:29–37`, `UniformOffDiagonal.lean:21–34`, `Rescaled.lean:114–127`,
`RescaledKilled.lean:93–109`, and the exports in
`Statements/HeatKernelOffDiagonal.lean` and `Statements/RescaledKernel.lean`.
`OnDiagonal.lean:69–108` applies the literal proposition but likewise uses only
its upper part; that branch feeds truncated/off-diagonal estimates, walk
tightness and quenched invariance. The uniform theorem also specializes at
`UniformOnDiagonal.lean:255`. Independently check **every** literal, uniform,
and independent-vocabulary consumer presently threading `hMSC` when successor
adapters are installed. Other named inputs to those consumers remain their own
obligations; this upper estimate does not close them. No current consumer
identified here requires the resistance or lower-bound programme.

Permitted mathematical inputs and their actual status:

| Input | Status and role |
|---|---|
| Markov row sum, symmetry, and the displayed two-sided jump comparison for the variable kernel | Exactly the target premises; the comparison includes the diagonal. |
| Pinned lattice definitions and lemmas: counting mass, distance, volume and inverse-scale comparison, reference Gaussian estimates | Proved source declarations; inspect their imported closures and axiom sets before relying on them. `lattice_evenKernelSup_zero` is already proved at `Uniform.lean:90–96`, unconditionally in `k`. |
| `unitRates_density_profile_uniform`, `densityPower_one_eq`, `kernelPow_le_sqrt_diag_half`, `poisson_average_profile_le` | Existing proofs used by the conditional continuous-time assembly; the assembly still depends on the open upper estimate. |
| Fixed reference-kernel upper estimate from MSC preprint Theorem 3.3, pp. 15–17 | Written for a fixed admissible kernel, **not proved in Lean**; its assumptions and every external dependency must be formalized and audited. It is not an additional premise of the target. |
| The reference-kernel construction, uniform energy comparison, holding bound, operator/spectral estimates, Nash inversion and scalar recursion | Mathematical route sketched below; these are **open Lean obligations**, not allowed assumptions. |
| Mathlib and pinned LP results with matching statements and audited closures | Reuse when available. LP's regular-variation Potter result assumes antitonicity and does not directly establish the general MSC scale theorem. `Network/Variational.lean` and `Graph/Nash.lean` are possible infrastructure, not verified matches. |

The Armstrong repository survey identifies no matching MSC result; its closest
Nash upper theorem concerns a continuum local PDE, not this discrete long-range
kernel. No exhaustive nonexistence claim is made.

## Source route and remaining boundaries

Preprint pp. 2–4 give the standing assumptions, density conventions and the
fixed-kernel theorem; pp. 9–10 give Lemmas 2.2–2.4, p. 11 Proposition 2.5,
pp. 12–13 Proposition 2.1, pp. 13–14 Lemma 3.1, pp. 14–15 Theorem 3.2,
and pp. 15–17 Theorem 3.3. External regular-variation and Nash/operator inputs
used there remain open until proved and audited. A source-to-Lean account must
also justify countable operator domains and `ENNReal`/real conversions.

At the end of the proof of Theorem 3.2 (p. 15), positivity of `K²` alone is
not the needed comparison. The diagonal of `(J_φ)` and the mass bounds yield a
uniform `α > 0` with `k(x,x) μ(x) ≥ α`; the paper derives
`E_K(f) ≤ α⁻¹ E_{K²}(f)`. On the critical counting lattice the proposed route
may use the sharper comparison `E_{K²} ≥ 2α E_K`, justified by the spectral
argument below. The holding constant must be fixed independently of the
variable kernel.

A mathematical uniformity check fixes `w(x,y) =
[(1 + dist(x,y))^d (1 + dist(x,y))^2]⁻¹`, proves `0 < Z = Σ_y w(0,y) < ∞`,
and takes the fixed symmetric Markov kernel `S = w/Z`. After the fixed-kernel
MSC upper estimate is proved for `S`, it supplies a super-Poincaré estimate
`‖f‖₂² ≤ 2m E_S(f) + B(1+m log(2+m))^(-d/2) ‖f‖₁²` for `m ≥ 1`.
For all admissible `K`, the jump comparison gives `E_S ≤ (C_φ/Z) E_K`;
the diagonal gives `k(x,x) ≥ α = min(1/2, 1/(2 C_φ)) > 0`.
Writing `K = α I + (1-α)R` with symmetric Markov contraction `R` gives
spectrum in `[2α-1,1]` and hence `E_{K²} ≥ 2α E_K`. Choosing `m` by
inverting `m log(2+m)` yields a uniform logarithmic Nash inequality. Applying
it to `K^n δ_x` gives a scalar recursion for `K^{2n}(x,x)` and the desired
profile; use the proved lattice inverse-scale comparison. At `n=0` the pinned
zero-time theorem gives exactly one. This is a mathematical route, not a Lean
proof, and the fixed-kernel source estimate is still open.

| Remaining boundary | Size | Open work |
|---|---|---|
| Fixed lattice reference kernel and MSC fixed-kernel upper estimate | XL | Summability/normalization, applicability of MSC, its source and external inputs; no upper estimate is currently available as an unconditional Lean input. |
| Counting-space operators and energy comparison | L/XL | Domains, contractions, symmetric energy, spectral/functional-calculus and density conversions; prove uniform holding and comparison from the displayed premises. |
| Super-Poincaré, logarithmic Nash and recursion | L/XL | Obtain fixed-kernel super-Poincaré, quantitative inverse estimates and scalar iteration with constants uniform in the variable kernel. Split into exact bounded statements before allocation. |
| Consumer assembly and audits | L | Adapt both upper-only consumer branches and the independent vocabulary under the freeze workflow; preserve all other premises, check all actual consumers, builds and axiom closure. Split into bounded statements after interfaces are approved. |

## Next bounded leaf

**Owner:** c2, subject to the LP owner's allocation and a dedicated LP worktree.
**Size:** S. **Proposed file:**
`LatticeProb/Graph/LongRangeKernel/CriticalHolding.lean` (new, not a frozen
statement file). **Source:** pinned `Uniform.lean:69–77`,
`Lattice.lean:26,76`, `CriticalScale.lean:18`, and MSC preprint p. 15,
lines around the diagonal `(J_φ)` argument. This leaf extracts the exact
holding lower bound already implicit in the selected comparison:

```lean
∀ {d : ℕ} (hd : 0 < d) (C_φ : ℝ)
  (k : Site d → Site d → ℝ≥0∞),
  (∀ x y,
    ENNReal.ofReal (C_φ⁻¹ / (latticeVolumeProfile d ((lattice d).dist x y) *
      quadraticScale ((lattice d).dist x y))) ≤ k x y ∧
    k x y ≤ ENNReal.ofReal (C_φ / (latticeVolumeProfile d ((lattice d).dist x y) *
      quadraticScale ((lattice d).dist x y)))) →
  ∀ x, ENNReal.ofReal (C_φ⁻¹) ≤ k x x
```

The graph-distance diagonal and definitions of the two profiles are proved
inputs; the displayed comparison is exactly a target premise. Neither a Markov
nor symmetry premise is needed for this leaf. It is a small component, not the
energy comparison or the uniform upper theorem. **Acceptance:** compile the
new file in the allocated LP worktree using the prescribed LP lane, check
`#print axioms` of the exact declaration for only `propext`,
`Classical.choice`, and `Quot.sound`, and independently compare binders and
profile normalization against the pinned target. Do not mark the source theorem
proved on this leaf's acceptance.

Blueprint acceptance is a document review only. Source completion separately
requires exact successor and consumer composition, clean builds, independent
statement/binder/definition and axiom audits, and no unproved analytic input in
the theorem closure.

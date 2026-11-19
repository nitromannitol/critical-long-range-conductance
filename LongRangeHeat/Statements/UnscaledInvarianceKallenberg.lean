import LongRangeHeat.UnscaledLimit
import LongRangeHeat.Statements.InvariancePrincipleKallenberg

/-!
# The unscaled annealed invariance principle through the Kallenberg–Aldous criterion

The unscaled form of Theorem 1.2 (`thm:IP`) for the unit walk with jump rates
`a({x,y}) |x-y|^(-d-2)`, as stated in the paragraph following that theorem, deduced from
`annealed_invariance_principle_kallenberg`. The statement is that of
`unscaled_invariance_principle`, without the two Ethier–Kurtz criteria among its hypotheses.
-/

namespace LongRangeHeat.Statements

open MeasureTheory Filter LatticeProb LatticeProb.Cadlag.HalfLine LatticeProb.Euclidean.Lattice
open scoped Topology
open LongRange (Edge)

/-- **Theorem 1.2** (`thm:IP`, unscaled form). For `d ≥ 1`, the unit walk started at the
origin under its annealed law satisfies
`((n log n)^(-1/2) Y_(nt))_(t ≥ 0) ⇒ (|S^(d-1)|/(2d))^(1/2) W` in
`D([0, ∞), ℝ^d)`, where `W` is standard Brownian motion. Here
`A = d * π^(d/2) / Γ(d/2 + 1) = |S^(d-1)|`. At `n = 0` an arbitrary positive clock is used,
and at `n = 0` and `n = 1` the space factor `(n log n)^(-1/2)` evaluates to `0`; neither
affects the limit.

The heat-kernel inputs `hMSC`, `hNash`, and `hDavies` are those of
`annealed_invariance_principle_kallenberg`. -/
theorem unscaled_invariance_principle_kallenberg
    (hMSC : LatticeProb.External.MuruganSaloffCosteUniform)
    (hNash : LatticeProb.External.ChenKimKumagaiWangNash)
    (hDavies : LatticeProb.External.ChenKimKumagaiWangDavies)
    {d : ℕ} (hd : 1 ≤ d) {lam : ℝ} {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (a : Ω → Edge d → ℝ) (hP : ConductanceLaw P lam a)
    (B : ProbabilityMeasure (BrownianPath d))
    (hB : IsStandardBrownianLaw (B : Measure (BrownianPath d))) :
    let A : ℝ := (d : ℝ) *
      (Real.pi ^ ((d : ℝ) / 2) / Real.Gamma ((d : ℝ) / 2 + 1))
    let F : BrownianPath d → PathSpace d := fun w =>
      D.ofContinuous ⟨fun t => Real.sqrt (A / (2 * d)) • w t,
        w.continuous.const_smul (Real.sqrt (A / (2 * d)))⟩
    ∃ _ : Measurable F,
      Tendsto (fun n : ℕ => (unitAnnealedLaw hd P a hP).map
        (scaledPath (Real.sqrt ((n : ℝ) * Real.log n))⁻¹ (naturalClock n)))
        atTop (𝓝 (B.map F)) :=
  ⟨measurable_scaledBrownianPath _,
    normalizedUnitLaw_tendsto_of_annealed hd P a hP B
      (annealed_invariance_principle_kallenberg hMSC hNash hDavies hd P a hP B hB).2⟩

end LongRangeHeat.Statements

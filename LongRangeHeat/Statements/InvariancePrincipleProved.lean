import LongRangeHeat.InvariancePrinciple
import LongRangeHeat.Statements.FddProved
import LongRangeHeat.InvariancePrincipleProved

/-!
# Theorem 1.2: the annealed invariance principle

Statement of Theorem 1.2 (`thm:IP`) of the heat-kernel version: for the walks `X^ε` under the
annealed law `P^ann_0 = E[P^a_0]`, the laws converge weakly in `D([0, ∞), ℝ^d)` to the law of
`d^{-1/2} W`, where `W` is a standard Brownian motion in `ℝ^d`.
-/

namespace LongRangeHeat.Statements

open MeasureTheory Filter LatticeProb LatticeProb.Cadlag.HalfLine LatticeProb.Euclidean.Lattice
open scoped Topology
open LongRange (Edge)

/-- **Theorem 1.2** (`thm:IP`, annealed invariance principle). Let `d ≥ 1`, let `P` be a
conductance law with ellipticity `λ ∈ (0, 1]` on a probability space `Ω`, and let `W` be a
standard Brownian motion in `ℝ^d` (given by a standard Brownian law `B` on `C([0, ∞), ℝ^d)`). Then
the law of the walk `X^ε` under the annealed law `P^ann_0 = E[P^a_0]` converges weakly in
`D([0, ∞), ℝ^d)`, for the Skorokhod topology, to the law of `d^{-1/2} W` as `ε → 0` in `(0, 1/2)`.
The measurability of `W ↦ d^{-1/2} W` as a map into `D([0, ∞), ℝ^d)` is part of the conclusion.

The heat-kernel inputs of Proposition 4.1 enter as the hypotheses `hNash` and `hDavies`.
The paper obtains tightness and the identification of the limit from Kallenberg (2002,
Theorems 14.10 and 14.11) and Aldous (1978); the same two steps are the cited criteria of
Ethier–Kurtz (Chapter 3, Theorem 8.6 and Theorem 7.8(b)) taken as the hypotheses `hEK` and
`hFdd`. Proposition 4.3 is used as a proved result. -/
theorem annealed_invariance_principle_proved
    (hNash : LatticeProb.External.ChenKimKumagaiWangNash)
    (hDavies : LatticeProb.External.ChenKimKumagaiWangDavies)
    (hEK : LatticeProb.External.EthierKurtzRelativeCompactnessStopping)
    (hFdd : LatticeProb.External.EthierKurtzConvergenceFromFdd)
    {d : ℕ} (hd : 1 ≤ d) {lam : ℝ}
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (a : Ω → Edge d → ℝ)
    (hP : ConductanceLaw P lam a)
    (B : ProbabilityMeasure (BrownianPath d))
    (hB : IsStandardBrownianLaw (B : Measure (BrownianPath d))) :
    let s : ℝ := (d : ℝ) ^ (-(1 : ℝ) / 2)
    let F : BrownianPath d → PathSpace d := fun w =>
      D.ofContinuous ⟨fun t => s • w t, w.continuous.const_smul s⟩
    ∃ _ : Measurable F,
      Tendsto (fun ε : Set.Ioo (0 : ℝ) (1 / 2) => annealedLaw hd P a hP ε.2.1)
        (Filter.comap Subtype.val (𝓝 0)) (𝓝 (ProbabilityMeasure.map B F)) :=
  ⟨measurable_scaledBrownianPath _,
    annealed_invariance_of_fdd_convergence_proved hNash hDavies hEK hFdd hP B _
      fun ε hε hε0 _ hk ts hts =>
        fdd_convergence_proved hNash hDavies hd P a hP B hB hk ts hts ε hε hε0⟩

end LongRangeHeat.Statements

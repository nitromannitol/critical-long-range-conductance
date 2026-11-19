import LongRangeHeat.KallenbergAnnealedFinal

/-!
# Theorem 1.2 through the Kallenberg–Aldous criterion

Theorem 1.2 (`thm:IP`) of the heat-kernel version, proved along the paper's route: Proposition
4.3 gives convergence of the finite-dimensional laws, Proposition 4.2 gives Aldous' condition,
and the Kallenberg–Aldous criterion in `D([0, ∞), ℝ^d)` (Kallenberg (2002), Theorems 16.10 and
16.11; Aldous (1978)), proved in `LongRangeHeat.KallenbergCriterion`, gives tightness and the
identification of the limit. The statement is that of `annealed_invariance_principle`, without
the two Ethier–Kurtz criteria among its hypotheses.
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

The heat-kernel inputs of Proposition 4.1 enter as the hypotheses `hMSC`, `hNash` and `hDavies`.
Tightness and the identification of the limit are proved from Propositions 4.2 and 4.3 by the
criterion of Kallenberg (2002, Theorems 16.10 and 16.11) and Aldous (1978). -/
theorem annealed_invariance_principle_kallenberg
    (hMSC : LatticeProb.External.MuruganSaloffCosteUniform)
    (hNash : LatticeProb.External.ChenKimKumagaiWangNash)
    (hDavies : LatticeProb.External.ChenKimKumagaiWangDavies)
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
    annealed_invariance_of_kallenberg hMSC hNash hDavies hd P a hP B hB⟩

end LongRangeHeat.Statements

import LongRangeHeat.KallenbergAnnealedBounded

/-!
# Probability budgets for annealed paths

A geometric allocation of exceptional probabilities yields a uniformly
high-probability totally bounded set of annealed paths.
-/

namespace LongRangeHeat

open Filter MeasureTheory LatticeProb LatticeProb.Cadlag.HalfLine LatticeProb.External
open scoped ENNReal Topology
open LongRange (Edge)

/-- The annealed laws assign arbitrarily small probability to the complement
of a common totally bounded set. -/
theorem annealed_exists_totallyBounded_measure_compl_le
    (hMSC : MuruganSaloffCosteUniform)
    (hNash : ChenKimKumagaiWangNash)
    (hDavies : ChenKimKumagaiWangDavies)
    {d : ℕ} (hd : 1 ≤ d) {lam : ℝ}
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (a : Ω → Edge d → ℝ)
    (hP : ConductanceLaw P lam a)
    (ε : ℕ → ℝ) (hε : ∀ n, ε n ∈ Set.Ioo (0 : ℝ) (1 / 2))
    (hε0 : Tendsto ε atTop (𝓝 0)) (t : ℕ → Time) (ht0 : ∀ k, 0 < t k)
    (ht : Tendsto t atTop atTop) (η : ℕ → ℝ) (hη : ∀ k, 0 < η k)
    (hη0 : Tendsto η atTop (𝓝 0)) {r : ℝ} (hr : 0 < r) :
    ∃ A : Set (PathSpace d), TotallyBounded A ∧ ∀ n,
      (annealedLaw hd P a hP (hε n).1 : Measure (PathSpace d)) Aᶜ ≤ ENNReal.ofReal r := by
  let p : ℕ → ℝ := fun k => (r / 2) / 2 / 2 ^ k
  have hp : ∀ k, 0 < p k := by
    intro k
    dsimp [p]
    positivity
  have hsum : (∑' k, ENNReal.ofReal (p k)) = ENNReal.ofReal (r / 2) := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => (hp k).le)]
    · simp only [p, tsum_geometric_two']
    · exact summable_geometric_two' (r / 2)
  obtain ⟨A, hA, hbound⟩ := annealed_exists_totallyBounded hMSC hNash hDavies hd P a hP
    ε hε hε0 t ht0 ht η hη hη0 p p hp hp
  refine ⟨A, hA, fun n => (hbound n).trans ?_⟩
  rw [hsum, ← ENNReal.ofReal_add (by positivity) (by positivity)]
  have : r / 2 + r / 2 = r := by ring
  rw [this]

/-- The annealed laws are uniformly concentrated on totally bounded sets. -/
theorem annealed_exists_totallyBounded_measure_compl
    (hMSC : MuruganSaloffCosteUniform)
    (hNash : ChenKimKumagaiWangNash)
    (hDavies : ChenKimKumagaiWangDavies)
    {d : ℕ} (hd : 1 ≤ d) {lam : ℝ}
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (a : Ω → Edge d → ℝ)
    (hP : ConductanceLaw P lam a)
    (ε : ℕ → ℝ) (hε : ∀ n, ε n ∈ Set.Ioo (0 : ℝ) (1 / 2))
    (hε0 : Tendsto ε atTop (𝓝 0)) {r : ℝ} (hr : 0 < r) :
    ∃ A : Set (PathSpace d), TotallyBounded A ∧ ∀ n,
      (annealedLaw hd P a hP (hε n).1 : Measure (PathSpace d)) Aᶜ ≤ ENNReal.ofReal r := by
  let t : ℕ → Time := fun k => (k : Time) + 1
  let η : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have ht0 : ∀ k, 0 < t k := by intro k; simp [t]
  have ht : Tendsto t atTop atTop := by
    exact tendsto_atTop_mono (fun k => by simp [t])
      tendsto_natCast_atTop_atTop
  have hη : ∀ k, 0 < η k := by intro k; dsimp [η]; positivity
  have hη0 : Tendsto η atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  exact annealed_exists_totallyBounded_measure_compl_le hMSC hNash hDavies hd P a hP
    ε hε hε0 t ht0 ht η hη hη0 hr

end LongRangeHeat

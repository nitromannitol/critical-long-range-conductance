import LongRangeHeat.Scaling
import LongRangeHeat.ScalingObstruction

/-!
# Scaling identities for the heat equations

The identities and the annular normalization increment in equation (1.9).
-/

namespace LongRangeHeat.Statements

open Filter Topology Asymptotics LatticeProb LatticeProb.Euclidean.Lattice LongRange
open LatticeProb.Euclidean.LatticeAnnulusRiemann

open scoped ContDiff

noncomputable section

/-- Equation (1.9): halving space changes the lattice and continuum time scales. -/
theorem scaling_identity {d : ℕ} (hd : 1 ≤ d) {ε : ℝ}
    (hε : ε ∈ Set.Ioo (0 : ℝ) (1 / 2)) (a : Edge d → ℝ)
    (f : (Fin d → ℝ) → ℝ) {t : ℝ} (ht : 0 ≤ t) (q : Site d) :
    latticeHeat (ε / 2) a (fun x => f (2 • x)) t q =
        latticeHeat ε a f ((4 * kappa d ε / kappa d (ε / 2)) * t) q ∧
      continuumHeat (fun x => f (2 • x)) t ((1 / 2 : ℝ) • physical ε q) =
        continuumHeat f (4 * t) (physical ε q) := by
  exact ⟨latticeHeat_half hd ⟨hε.1, by linarith [hε.2]⟩ a f t q,
    continuumHeat_half hd f ht _⟩

/-- The normalization increment in equation (1.9) is an annular sum with the stated limit. -/
theorem kappa_halving_increment {d : ℕ} (hd : 1 ≤ d) :
    (∀ ε : ℝ, 0 < ε → kappa d (ε / 2) - kappa d ε =
      ∑ w ∈ annulusIndices d (1 / ε),
        Real.rpow (radius (physical 1 w)) (-(d : ℝ))) ∧
    Tendsto (fun ε : ℝ => kappa d (ε / 2) - kappa d ε) (𝓝[>] 0)
      (𝓝 ((d : ℝ) *
        (Real.pi ^ ((d : ℝ) / 2) / Real.Gamma ((d : ℝ) / 2 + 1)) * Real.log 2)) :=
  ⟨fun _ hε => kappa_half_sub_eq_annulus_sum hε, tendsto_kappa_half_sub hd⟩

/-- The halving increment and its exact logarithmic normalization, as in equation (1.9). -/
theorem kappa_halving {d : ℕ} (hd : 1 ≤ d) :
    (∀ ε : ℝ, 0 < ε → kappa d (ε / 2) - kappa d ε =
      ∑ w ∈ annulusIndices d (1 / ε),
        Real.rpow (radius (physical 1 w)) (-(d : ℝ))) ∧
    Tendsto (fun ε : ℝ => kappa d (ε / 2) - kappa d ε) (𝓝[>] 0)
      (𝓝 ((d : ℝ) *
        (Real.pi ^ ((d : ℝ) / 2) / Real.Gamma ((d : ℝ) / 2 + 1)) * Real.log 2)) ∧
    Tendsto (fun ε : ℝ =>
      ((kappa d (ε / 2) - kappa d ε) / kappa d (ε / 2)) * |Real.log ε|)
      (𝓝[>] 0) (𝓝 (Real.log 2)) := by
  exact ⟨(kappa_halving_increment hd).1, (kappa_halving_increment hd).2,
    kappa_half_ratio_tendsto hd⟩

/-- The deterministic scaling obstruction following equation (1.9): the heat errors for `f`
at spacing `ε` and for `f(2 ·)` at spacing `ε / 2` cannot both be `o(|log ε|⁻¹)`. -/
theorem scaling_obstruction {d : ℕ} (hd : 1 ≤ d)
    {lam : ℝ} (hlam : 0 < lam) {a : Edge d → ℝ}
    (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹)
    {f : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (hf0 : f ≠ 0) {T : ℝ} (hT : 0 < T) :
    (∀ ε ∈ Set.Ioo (0 : ℝ) (1 / 2),
      BddAbove ((fun s => latticeNorm ε (fun q => latticeHeat ε a f s q -
        continuumHeat f s (physical ε q))) '' Set.Icc 0 T) ∧
      BddAbove ((fun s => latticeNorm (ε / 2) (fun q =>
        latticeHeat (ε / 2) a (fun x => f ((2 : ℝ) • x)) s q -
        continuumHeat (fun x => f ((2 : ℝ) • x)) s (physical (ε / 2) q))) '' Set.Icc 0 T) ∧
      ∀ s ∈ Set.Icc 0 T,
        MemL2 (fun q => latticeHeat ε a f s q - continuumHeat f s (physical ε q)) ∧
        MemL2 (fun q => latticeHeat (ε / 2) a (fun x => f ((2 : ℝ) • x)) s q -
          continuumHeat (fun x => f ((2 : ℝ) • x)) s (physical (ε / 2) q))) ∧
    ¬ ((fun ε : ℝ => latticeHeatErrorSup ε a f T) =o[𝓝[>] 0]
        (fun ε : ℝ => |Real.log ε|⁻¹) ∧
      (fun ε : ℝ => latticeHeatErrorSup (ε / 2) a (fun x => f ((2 : ℝ) • x)) T) =o[𝓝[>] 0]
        (fun ε : ℝ => |Real.log ε|⁻¹)) := by
  have hpoint : ∃ x, f x ≠ 0 := by
    by_contra h
    apply hf0
    funext x
    have h' := not_exists.mp h x
    simpa only [not_not, Pi.zero_apply] using h'
  obtain ⟨x, hx⟩ := hpoint
  obtain ⟨hf₂, hfc₂⟩ := smooth_compactSupport_dilate hf hfc
  constructor
  · intro ε hε
    have hεh : 0 < ε / 2 := by linarith [hε.1]
    have hεh1 : ε / 2 ≤ 1 := by linarith [hε.2]
    have hε1 : ε ≤ 1 := by linarith [hε.2]
    have hb1 := bddAbove_latticeHeat_error (T := T) hd hε.1 hε1 hlam ha hf hfc
    have hb2 := bddAbove_latticeHeat_error_half (T := T) hd hε hlam ha hf hfc
    refine ⟨by simpa only [restrict] using hb1, hb2, ?_⟩
    obtain ⟨R, hR⟩ := exists_sampledHeat_uniform_l2_bound hd hε.1 hε1 hf.continuous hfc
    obtain ⟨R₂, hR₂⟩ := exists_sampledHeat_uniform_l2_bound hd hεh hεh1 hf₂.continuous hfc₂
    intro s hs
    constructor
    · simpa only [restrict] using memL2_sub
        (memL2_latticeHeat hd hε.1 hlam ha hfc s) (hR s hs.1).1
    · simpa only [restrict] using memL2_sub
        (memL2_latticeHeat hd hεh hlam ha hfc₂ s) (hR₂ s hs.1).1
  · rintro ⟨h1, h2⟩
    apply LongRangeHeat.scaling_obstruction hd hlam ha hf hfc hx hT
    constructor
    · simpa only [div_eq_mul_inv, inv_inv, mul_comm] using h1.tendsto_div_nhds_zero
    · simpa only [div_eq_mul_inv, inv_inv, mul_comm] using h2.tendsto_div_nhds_zero

end
end LongRangeHeat.Statements

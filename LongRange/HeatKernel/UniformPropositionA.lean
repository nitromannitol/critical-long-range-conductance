import LongRange.HeatKernel.PropositionA

/-!
# Uniform off-diagonal bounds for indexed heat kernels

The truncation argument chooses one explicit constant from the dimension and the four
common input constants. Only after this choice does it specialize to an indexed kernel.
-/

namespace LongRange

open LatticeProb LatticeProb.Euclidean.Lattice
open scoped NNReal

noncomputable section

variable {d : ℕ}

/-- Common on-diagonal, Meyer and Davies constants give a common spatial bound
for an arbitrary indexed family, including an empty family. -/
theorem offDiagonal_of_truncated_bounds_uniform {Index : Type*} (hd : 1 ≤ d)
    (u : Index → ℝ≥0 → Site d → Site d → ℝ)
    (uρ : Index → ℝ → ℝ≥0 → Site d → Site d → ℝ)
    {Ca L A B : ℝ}
    (hODB : ∀ i t x y, u i t x y ≤
      Ca * (1 + t * Real.log (2 + t)) ^ (-((d : ℝ) / 2)))
    (hM2 : ∀ i (ρ : ℝ), 0 < ρ → ∀ t x y,
      u i t x y ≤ uρ i ρ t x y + L * max 1 ρ ^ (-((d : ℝ) + 2)) * t)
    (hzero : ∀ i (ρ : ℝ), 0 < ρ → ρ < 1 → ∀ t x y, x ≠ y → uρ i ρ t x y = 0)
    (hDav : ∀ i (ρ : ℝ), 1 ≤ ρ → ∀ σ : ℝ, 0 ≤ σ →
      ∀ t : ℝ≥0, 0 < t → ∀ x y,
      uρ i ρ t x y ≤ A * (t * (1 + Real.log (1 + t))) ^ (-((d : ℝ) / 2)) *
        Real.exp (B * ρ ^ (-(2 : ℝ)) * t) *
        Real.exp (-(σ * radius (physical 1 (y - x)) / ρ) +
          B * σ ^ 2 * Real.exp (2 * σ) * (1 + Real.log ρ) * t / ρ ^ 2)) :
    ∃ C : ℝ, 0 < C ∧ ∀ i (t : ℝ≥0), 0 < t → ∀ x y, x ≠ y →
      u i t x y ≤ C * t * Real.log (2 + radius (physical 1 (y - x))) /
        radius (physical 1 (y - x)) ^ (d + 2) := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  let γ : ℝ := 1 / (3 * ((d : ℝ) / 2 + 2))
  have hγ : 0 < γ := by dsimp only [γ]; positivity
  have hγone : γ ≤ 1 := by
    dsimp only [γ]
    apply (div_le_one (by positivity)).mpr
    linarith
  let D : ℝ := (1 + 1 / Real.log 2) ^ ((d : ℝ) / 2)
  let P : ℝ := 2 ^ ((d : ℝ) / 2) + ((d : ℝ) / 2 + 1) ^ ((d : ℝ) / 2 + 1)
  let K : ℝ := |A| * Real.exp (5 * |B|) * P
  let E : ℝ := |L| / γ ^ (d + 2)
  let H : ℝ := |Ca| * D * (2 / γ ^ (d + 2))
  let S : ℝ := 2 * K / γ ^ (d + 2)
  have hD : 0 ≤ D := (by positivity)
  have hP : 0 ≤ P := add_nonneg (by positivity) (by positivity)
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hH : 0 ≤ H := by dsimp only [H]; positivity
  have hS : 0 ≤ S := by dsimp only [S]; positivity
  let C : ℝ := 1 + E + H + S
  refine ⟨C, by dsimp only [C]; positivity, ?_⟩
  intro i t ht x y hxy
  let r : ℝ := radius (physical 1 (y - x))
  have hr : 1 ≤ r := one_le_radius_displacement hxy
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have htpos : 0 < (t : ℝ) := ht
  have hρpos : 0 < γ * r := mul_pos hγ hrpos
  let F : ℝ := (t : ℝ) * Real.log (2 + r) / r ^ (d + 2)
  have hF : 0 ≤ F := by
    dsimp only [F]
    exact div_nonneg (mul_nonneg t.coe_nonneg
      (zero_le_one.trans (one_le_log_two_add hr))) (pow_nonneg hrpos.le _)
  change u i t x y ≤ C * (t : ℝ) * Real.log (2 + r) / r ^ (d + 2)
  suffices hfinal : u i t x y ≤ C * F by simpa only [F, mul_div_assoc, mul_assoc] using hfinal
  by_cases hsmall : γ * r < 1
  · have hu := offDiagonal_of_small_truncation (u i) (uρ i) hγ (hM2 i) (hzero i) t hxy hsmall
    have hu' : u i t x y ≤ E * F := by
      convert hu using 1
      dsimp only [E, F, r]
      ring
    exact hu'.trans (mul_le_mul_of_nonneg_right (by dsimp only [C]; linarith) hF)
  · have hρ : 1 ≤ γ * r := le_of_not_gt hsmall
    by_cases hlarge : (γ * r) ^ 2 / (1 + Real.log (γ * r)) ≤ (t : ℝ)
    · have hp := onDiagonal_profile_le (d := d) hρ hlarge
      have hv := inverse_volume_le_spatial (d := d) hγ hγone hr hρ hlarge
      have hlogt : 0 ≤ Real.log (2 + (t : ℝ)) := Real.log_nonneg (by linarith)
      have hprofile : 0 ≤ (1 + (t : ℝ) * Real.log (2 + t)) ^ (-((d : ℝ) / 2)) :=
        Real.rpow_nonneg (by positivity) _
      have hu : u i t x y ≤ |Ca| * (D / (γ * r) ^ d) := by
        calc
          u i t x y ≤ Ca * (1 + (t : ℝ) * Real.log (2 + t)) ^ (-((d : ℝ) / 2)) :=
            hODB i t x y
          _ ≤ |Ca| * (D / (γ * r) ^ d) := by
            exact mul_le_mul (le_abs_self Ca) hp hprofile (abs_nonneg Ca)
      have hu' : u i t x y ≤ H * F := by
        calc
          u i t x y ≤ |Ca| * (D / (γ * r) ^ d) := hu
          _ = (|Ca| * D) * (1 / (γ * r) ^ d) := by ring
          _ ≤ (|Ca| * D) * (2 / γ ^ (d + 2) * t * Real.log (2 + r) /
              r ^ (d + 2)) := mul_le_mul_of_nonneg_left hv (by positivity)
          _ = H * F := by dsimp only [H, F]; ring
      exact hu'.trans (mul_le_mul_of_nonneg_right (by dsimp only [C]; linarith) hF)
    · have htime : (t : ℝ) ≤ (γ * r) ^ 2 / (1 + Real.log (γ * r)) :=
        (lt_of_not_ge hlarge).le
      have hlogρ := Real.log_nonneg hρ
      have hw : (t : ℝ) * (1 + Real.log (γ * r)) / (γ * r) ^ 2 ≤ 1 := by
        apply (div_le_one (sq_pos_of_pos hρpos)).mpr
        exact (le_div_iff₀ (by positivity : 0 < 1 + Real.log (γ * r))).mp htime
      have hratio : r / (γ * r) = 3 * ((d : ℝ) / 2 + 2) := by
        dsimp only [γ]
        field_simp
      have htr := davies_profile_le hρ htpos hw hratio
        (fun σ hσ => hDav i (γ * r) hρ σ hσ t ht x y)
      have hscaled := scaled_logarithmic_bound (d := d) hγ hγone hr t.coe_nonneg hK
      have htr' : uρ i (γ * r) t x y ≤ S * F := by
        calc
          _ ≤ K * t * (1 + Real.log (γ * r)) / (γ * r) ^ (d + 2) := htr
          _ ≤ (2 * K / γ ^ (d + 2)) * t * Real.log (2 + r) / r ^ (d + 2) := hscaled
          _ = S * F := by dsimp only [S, F]; ring
      have herr : L * max 1 (γ * r) ^ (-((d : ℝ) + 2)) * t ≤ E * F := by
        convert truncation_error_le (d := d) hγ hr t.coe_nonneg using 1
        dsimp only [E, F]
        ring
      calc
        u i t x y ≤ uρ i (γ * r) t x y +
            L * max 1 (γ * r) ^ (-((d : ℝ) + 2)) * t := hM2 i _ hρpos t x y
        _ ≤ S * F + E * F := add_le_add htr' herr
        _ = (S + E) * F := by ring
        _ ≤ C * F := mul_le_mul_of_nonneg_right (by dsimp only [C]; linarith) hF

end

end LongRange

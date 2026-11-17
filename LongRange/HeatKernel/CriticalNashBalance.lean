import LongRange.HeatKernel.CriticalNashEnergy
import LongRange.HeatKernel.CriticalNashRadius

/-!
# Balanced critical Nash estimate

A balancing radius controls its lattice volume in terms of the square and
absolute sums of the function.
-/

open LatticeProb
open scoped NNReal ENNReal

namespace LatticeProb.Graph.LongRangeKernel

/-- The balanced two-term estimate, with constants uniform over the kernel. -/
theorem weightedLattice_critical_balanced {d : ℕ} (hd : 0 < d)
    (C : ℝ) (hC : 0 < C) :
    ∃ D : ℝ, 0 < D ∧ ∀ (k : Site d → Site d → ℝ≥0∞),
      (∀ x, ∑' y, k x y = 1) → (∀ x y, k x y = k y x) →
      (∀ x y, ENNReal.ofReal (C⁻¹ /
        (latticeVolumeProfile d ((weightedLattice d hd).graph.dist x y : ℝ) *
          quadraticScale ((weightedLattice d hd).graph.dist x y : ℝ))) ≤ k x y) →
      ∀ f : lp (fun _ : Site d => ℝ) 2,
        Summable (fun x => |f x|) → 0 < realKernelEnergy k f →
        ∃ R : ℝ, 1 ≤ R ∧
          criticalNashRadiusScale d R * realKernelEnergy k f =
            2 * criticalNashRadiusScale d 1 * (∑' x, |f x|) ^ 2 ∧
          (∑' x, f x ^ 2) * latticeVolumeProfile d R ≤ D * (∑' x, |f x|) ^ 2 := by
  obtain ⟨A, B, hA, hB, htwo⟩ := weightedLattice_critical_two_term hd C hC
  have hF : 0 < criticalNashRadiusScale d 1 :=
    lt_of_lt_of_le (by norm_num) (le_criticalNashRadiusScale d (le_refl 1))
  refine ⟨2 * A * criticalNashRadiusScale d 1 + B, by positivity, ?_⟩
  intro k hk hsym hlower f hf hE
  have hbound := realKernelEnergy_le_two_tsum_abs_sq k hk hsym f hf
  obtain ⟨R, hR, hbalance⟩ := exists_criticalNash_balancing_radius d hE hbound
  refine ⟨R, hR, hbalance, ?_⟩
  have hV : 0 < latticeVolumeProfile d R := by
    unfold latticeVolumeProfile
    positivity
  have htwo' := htwo k hk hsym hlower R hR f hf
  calc
    _ ≤ (A * (R ^ 2 / Real.log (1 + R)) * realKernelEnergy k f +
        B * (∑' x, |f x|) ^ 2 / latticeVolumeProfile d R) * latticeVolumeProfile d R :=
      mul_le_mul_of_nonneg_right htwo' hV.le
    _ = A * (criticalNashRadiusScale d R * realKernelEnergy k f) +
        B * (∑' x, |f x|) ^ 2 := by
      unfold criticalNashRadiusScale
      field_simp
    _ = _ := by rw [hbalance]; ring

/-- Zero energy forces the square sum to vanish for a critical kernel. -/
theorem weightedLattice_critical_square_sum_eq_zero_of_energy_eq_zero
    {d : ℕ} (hd : 0 < d) (C : ℝ) (hC : 0 < C)
    (k : Site d → Site d → ℝ≥0∞)
    (hk : ∀ x, ∑' y, k x y = 1) (hsym : ∀ x y, k x y = k y x)
    (hlower : ∀ x y, ENNReal.ofReal (C⁻¹ /
      (latticeVolumeProfile d ((weightedLattice d hd).graph.dist x y : ℝ) *
        quadraticScale ((weightedLattice d hd).graph.dist x y : ℝ))) ≤ k x y)
    (f : lp (fun _ : Site d => ℝ) 2) (hf : Summable (fun x => |f x|))
    (hE : realKernelEnergy k f = 0) : (∑' x, f x ^ 2) = 0 := by
  obtain ⟨A, B, hA, hB, htwo⟩ := weightedLattice_critical_two_term hd C hC
  let Q : ℝ := ∑' x, f x ^ 2
  let L : ℝ := ∑' x, |f x|
  have hQ : 0 ≤ Q := tsum_nonneg (fun _ => sq_nonneg _)
  by_contra hn
  have hQpos : 0 < Q := lt_of_le_of_ne hQ (Ne.symm hn)
  let R := 1 + (B * L ^ 2 + 1) / Q
  have hR : 1 ≤ R := by
    dsimp [R]
    exact le_add_of_nonneg_right (div_nonneg (by positivity) hQ)
  have hV : 0 < latticeVolumeProfile d R := by
    unfold latticeVolumeProfile
    positivity
  have hRV : R ≤ latticeVolumeProfile d R := by
    unfold latticeVolumeProfile
    have hpow : 1 + R ≤ (1 + R) ^ d := le_self_pow₀ (by linarith) hd.ne'
    linarith
  have ht := htwo k hk hsym hlower R hR f hf
  rw [hE, mul_zero, zero_add] at ht
  change Q ≤ B * L ^ 2 / latticeVolumeProfile d R at ht
  have hQV := (le_div_iff₀ hV).1 ht
  have hQR : Q * R ≤ B * L ^ 2 :=
    (mul_le_mul_of_nonneg_left hRV hQ).trans hQV
  have heq : Q * (R - 1) = B * L ^ 2 + 1 := by
    dsimp [R]
    field_simp
    ring
  nlinarith

end LatticeProb.Graph.LongRangeKernel

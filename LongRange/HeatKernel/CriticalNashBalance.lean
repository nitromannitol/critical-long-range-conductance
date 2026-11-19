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

/-- The balanced volume estimate yields the energy form of the Nash bound. -/
theorem criticalNash_bound_of_balance {d : ℕ} {Q L E D R : ℝ}
    (hR : 1 ≤ R)
    (hbalance : criticalNashRadiusScale d R * E =
      2 * criticalNashRadiusScale d 1 * L ^ 2)
    (hvolume : Q * latticeVolumeProfile d R ≤ D * L ^ 2) :
    Q ≤ D / (2 * criticalNashRadiusScale d 1) *
      (R ^ 2 / Real.log (1 + R)) * E := by
  have hF : 0 < criticalNashRadiusScale d 1 :=
    lt_of_lt_of_le (by norm_num) (le_criticalNashRadiusScale d (le_refl 1))
  have hV : 0 < latticeVolumeProfile d R := by
    unfold latticeVolumeProfile
    positivity
  have hL : L ^ 2 = criticalNashRadiusScale d R * E /
      (2 * criticalNashRadiusScale d 1) := by
    apply (eq_div_iff (by positivity : 2 * criticalNashRadiusScale d 1 ≠ 0)).2
    linarith
  calc
    Q ≤ D * L ^ 2 / latticeVolumeProfile d R := (le_div_iff₀ hV).2 hvolume
    _ = D / (2 * criticalNashRadiusScale d 1) *
        (R ^ 2 / Real.log (1 + R)) * E := by
      rw [hL]
      unfold criticalNashRadiusScale
      field_simp

/-- The critical Nash bound at the balancing radius, uniformly in the kernel. -/
theorem weightedLattice_critical_nash_at_radius {d : ℕ} (hd : 0 < d)
    (C : ℝ) (hC : 0 < C) :
    ∃ D N : ℝ, 0 < D ∧ 0 < N ∧ ∀ (k : Site d → Site d → ℝ≥0∞),
      (∀ x, ∑' y, k x y = 1) → (∀ x y, k x y = k y x) →
      (∀ x y, ENNReal.ofReal (C⁻¹ /
        (latticeVolumeProfile d ((weightedLattice d hd).graph.dist x y : ℝ) *
          quadraticScale ((weightedLattice d hd).graph.dist x y : ℝ))) ≤ k x y) →
      ∀ f : lp (fun _ : Site d => ℝ) 2,
        Summable (fun x => |f x|) → 0 < realKernelEnergy k f →
        ∃ R : ℝ, 1 ≤ R ∧
          (∑' x, f x ^ 2) * latticeVolumeProfile d R ≤ D * (∑' x, |f x|) ^ 2 ∧
          (∑' x, f x ^ 2) ≤ N * (R ^ 2 / Real.log (1 + R)) * realKernelEnergy k f := by
  obtain ⟨D, hD, hb⟩ := weightedLattice_critical_balanced hd C hC
  have hF : 0 < criticalNashRadiusScale d 1 :=
    lt_of_lt_of_le (by norm_num) (le_criticalNashRadiusScale d (le_refl 1))
  refine ⟨D, D / (2 * criticalNashRadiusScale d 1), hD, by positivity, ?_⟩
  intro k hk hsym hlower f hf hE
  obtain ⟨R, hR, hbalance, hvolume⟩ := hb k hk hsym hlower f hf hE
  exact ⟨R, hR, hvolume, criticalNash_bound_of_balance hR hbalance hvolume⟩

/-- The volume bound controls the balancing radius by the inverse volume profile. -/
theorem le_rpow_inv_of_latticeVolumeProfile_le {d : ℕ} (hd : 0 < d)
    {R T : ℝ} (hR : 1 ≤ R) (hT : latticeVolumeProfile d R ≤ T) :
    1 + R ≤ T ^ (1 / (d : ℝ)) := by
  have hdpos : 0 < (d : ℝ) := by exact_mod_cast hd
  have hbase : 0 ≤ 1 + R := by linarith
  have hpow := Real.rpow_le_rpow (show 0 ≤ latticeVolumeProfile d R by
      unfold latticeVolumeProfile; positivity) hT (by positivity : 0 ≤ 1 / (d : ℝ))
  have heq : latticeVolumeProfile d R ^ (1 / (d : ℝ)) = 1 + R := by
    unfold latticeVolumeProfile
    rw [← Real.rpow_natCast, ← Real.rpow_mul hbase]
    have : (d : ℝ) * (1 / (d : ℝ)) = 1 := by field_simp
    rw [this, Real.rpow_one]
  rwa [heq] at hpow

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

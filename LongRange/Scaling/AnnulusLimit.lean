import LongRange.Appendix.Kappa
import LatticeProb.Euclidean.LatticeAnnulusRiemann

/-!
# The normalization increment on halving the mesh

The exact integer annulus identity and its Euclidean limit give the normalization increment
`d V_d log 2` displayed in the introduction. The positive limiting increment and the existing
logarithmic bounds give the two-sided order of the normalization ratio at every small scale.
-/

noncomputable section

open Filter Topology
open LatticeProb.Euclidean.Lattice LatticeProb.Euclidean.Shell
open LatticeProb.Euclidean.LatticeAnnulusRiemann

namespace LongRange

/-- Halving the mesh adds exactly the strict-inner, closed-outer integer annulus. -/
theorem kappa_half_sub_eq_annulus_sum {d : ℕ} {ε : ℝ} (hε : 0 < ε) :
    kappa d (ε / 2) - kappa d ε =
      ∑ w ∈ annulusIndices d (1 / ε),
        Real.rpow (radius (physical 1 w)) (-(d : ℝ)) := by
  classical
  have hhalf : 0 < ε / 2 := by positivity
  have hrad (η : ℝ) (hη : 0 < η) (w : LatticeProb.Site d) :
      w ∈ unitBallIndices d η ↔ w ≠ 0 ∧ radius (physical 1 w) ≤ 1 / η := by
    rw [mem_unitBallIndices hη, radius_physical_eq_mul hη.le,
      mul_comm η, ← le_div_iff₀ hη]
  have hsub : unitBallIndices d ε ⊆ unitBallIndices d (ε / 2) := by
    intro w hw
    obtain ⟨hw0, hw⟩ := (hrad ε hε w).mp hw
    apply (hrad (ε / 2) hhalf w).mpr
    refine ⟨hw0, hw.trans ?_⟩
    exact one_div_le_one_div_of_le hhalf (by linarith)
  have heq : unitBallIndices d (ε / 2) \ unitBallIndices d ε =
      annulusIndices d (1 / ε) := by
    ext w
    rw [Finset.mem_sdiff, hrad (ε / 2) hhalf, hrad ε hε,
      mem_annulusIndices (by positivity)]
    have he : 1 / (ε / 2) = 2 * (1 / ε) := by ring
    rw [he]
    constructor
    · rintro ⟨⟨hw0, hw⟩, hn⟩
      exact ⟨lt_of_not_ge (fun h => hn ⟨hw0, h⟩), hw⟩
    · rintro ⟨hw1, hw2⟩
      have hw0 : w ≠ 0 := by
        intro hz
        have hr : radius (physical 1 w) = 0 := by simp [hz, physical, radius]
        have hp : 0 < 1 / ε := by positivity
        linarith
      exact ⟨⟨hw0, hw2⟩, fun h => not_le_of_gt hw1 h.2⟩
  rw [kappa_eq_integer_sum hhalf, kappa_eq_integer_sum hε,
    ← Finset.sum_sdiff hsub, heq, add_sub_cancel_right]
  rfl

/-- The exact normalization increment tends to the Euclidean annulus integral. -/
theorem tendsto_kappa_half_sub {d : ℕ} (hd : 1 ≤ d) :
    Tendsto (fun ε : ℝ => kappa d (ε / 2) - kappa d ε) (𝓝[>] 0)
      (𝓝 ((d : ℝ) *
        (Real.pi ^ ((d : ℝ) / 2) / Real.Gamma ((d : ℝ) / 2 + 1)) * Real.log 2)) := by
  have ht := (tendsto_annulus_sum hd).comp
    (show Tendsto (fun ε : ℝ => 1 / ε) (𝓝[>] 0) atTop by
      simpa only [one_div] using (tendsto_inv_nhdsGT_zero (𝕜 := ℝ)))
  rw [unitBallVolume_eq_pi_div_gamma] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (kappa_half_sub_eq_annulus_sum hε).symm

/-- The normalization ratio has two-sided inverse-logarithmic order at all small scales. -/
theorem kappa_half_ratio_order {d : ℕ} (hd : 1 ≤ d) :
    ∃ c C δ : ℝ, 0 < c ∧ 0 < C ∧ 0 < δ ∧ ∀ ε : ℝ,
      ε ∈ Set.Ioo (0 : ℝ) δ →
        c / |Real.log ε| ≤ kappa d (ε / 2) / kappa d ε - 1 ∧
        kappa d (ε / 2) / kappa d ε - 1 ≤ C / |Real.log ε| := by
  let A : ℝ := (d : ℝ) * unitBallVolume d * Real.log 2
  have hA : 0 < A := mul_pos
    (mul_pos (Nat.cast_pos.mpr (by omega)) (unitBallVolume_pos d))
    (Real.log_pos (by norm_num))
  have ht : Tendsto (fun ε : ℝ => kappa d (ε / 2) - kappa d ε)
      (𝓝[>] 0) (𝓝 A) := by
    simpa only [A, unitBallVolume_eq_pi_div_gamma] using tendsto_kappa_half_sub hd
  have hevent : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      A / 2 < kappa d (ε / 2) - kappa d ε ∧
        kappa d (ε / 2) - kappa d ε < 2 * A :=
    ht.eventually (Ioo_mem_nhds (by linarith) (by linarith))
  obtain ⟨δ, hδ, hinc⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hevent
  obtain ⟨c₀, hc₀, hlower⟩ := le_kappa hd
  obtain ⟨C₀, hC₀, hupper⟩ := kappa_le d
  refine ⟨A / (4 * C₀), 2 * A / c₀, min δ (min (1 / 2) (Real.exp (-1))),
    by positivity, by positivity, lt_min hδ (lt_min (by norm_num) (Real.exp_pos _)), ?_⟩
  intro ε hε
  have hεδ : ε < δ := hε.2.trans_le (min_le_left _ _)
  have hsmall : ε < min (1 / 2) (Real.exp (-1)) :=
    hε.2.trans_le (min_le_right _ _)
  have hεone : ε ∈ Set.Ioo (0 : ℝ) 1 :=
    ⟨hε.1, (hsmall.trans_le (min_le_left _ _)).trans (by norm_num)⟩
  have hlogneg : Real.log ε < -1 := by
    have h := Real.log_lt_log hε.1 (hsmall.trans_le (min_le_right _ _))
    simpa only [Real.log_exp] using h
  have hL : 1 ≤ |Real.log ε| := by rw [abs_of_neg (by linarith)]; linarith
  have hLpos : 0 < |Real.log ε| := lt_of_lt_of_le zero_lt_one hL
  have hk := kappa_pos hd hεone
  obtain ⟨hi, hi'⟩ := hinc ⟨hε.1, hεδ⟩
  have hκlo : c₀ * |Real.log ε| ≤ kappa d ε := by
    calc
      _ ≤ c₀ * (1 + |Real.log ε|) := by gcongr; linarith
      _ ≤ _ := hlower ε hεone
  have hκhi : kappa d ε ≤ 2 * C₀ * |Real.log ε| := by
    calc
      _ ≤ C₀ * (1 + |Real.log ε|) := hupper ε hεone
      _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_left hL hC₀.le]
  have heq : kappa d (ε / 2) / kappa d ε - 1 =
      (kappa d (ε / 2) - kappa d ε) / kappa d ε := by
    exact div_sub_one hk.ne'
  rw [heq]
  constructor
  · rw [div_le_div_iff₀ hLpos hk]
    calc
      A / (4 * C₀) * kappa d ε ≤
          A / (4 * C₀) * (2 * C₀ * |Real.log ε|) :=
        mul_le_mul_of_nonneg_left hκhi (by positivity)
      _ = A / 2 * |Real.log ε| := by field_simp; ring
      _ ≤ (kappa d (ε / 2) - kappa d ε) * |Real.log ε| :=
        mul_le_mul_of_nonneg_right hi.le hLpos.le
  · rw [div_le_div_iff₀ hk hLpos]
    calc
      (kappa d (ε / 2) - kappa d ε) * |Real.log ε| ≤
          (2 * A) * |Real.log ε| := mul_le_mul_of_nonneg_right hi'.le hLpos.le
      _ = (2 * A / c₀) * (c₀ * |Real.log ε|) := by field_simp
      _ ≤ (2 * A / c₀) * kappa d ε :=
        mul_le_mul_of_nonneg_left hκlo (by positivity)

end LongRange

import LongRange.Statements.RescaledKernel
import LongRange.Statements.HeatKernel
import LongRangeHeat.SecondMoment

/-!
# Heat-kernel bounds for the rescaled walk

Proof of Proposition 4.1 (`prop:hk`) from the microscopic heat-kernel bounds of the unit walk and
the time change `t = h / (κ_ε ε²)`.
-/

namespace LongRangeHeat

open LatticeProb LatticeProb.Euclidean.Lattice Set
open scoped NNReal
open LongRange (kappa kappa_le Edge unitRates)

noncomputable section

/-- For `B > 0` there is `c > 0` with `c (1 + L) ≤ log (2 + e^{L/2} / B)` for every `L ≥ 0`. -/
theorem exists_mul_le_log_two_add_exp {B : ℝ} (hB : 0 < B) :
    ∃ c : ℝ, 0 < c ∧ ∀ L : ℝ, 0 ≤ L → c * (1 + L) ≤ Real.log (2 + Real.exp (L / 2) / B) := by
  set M := max B 1 with hM
  have hM1 : 1 ≤ M := le_max_right _ _
  have hMB : B ≤ M := le_max_left _ _
  have hlogM : 0 ≤ Real.log M := Real.log_nonneg hM1
  have hMpos : 0 < M := lt_of_lt_of_le one_pos hM1
  refine ⟨min (1 / 8) (Real.log 2 / (1 + (4 * Real.log M + 2))),
    lt_min (by norm_num) (div_pos (Real.log_pos one_lt_two) (by linarith)), fun L hL => ?_⟩
  have hu : 0 ≤ Real.exp (L / 2) / B := div_nonneg (Real.exp_pos _).le hB.le
  have h2 : Real.log 2 ≤ Real.log (2 + Real.exp (L / 2) / B) :=
    Real.log_le_log (by norm_num) (by linarith)
  have h3 : L / 2 - Real.log M ≤ Real.log (2 + Real.exp (L / 2) / B) := by
    have hle : Real.exp (L / 2) / M ≤ 2 + Real.exp (L / 2) / B := by
      have := div_le_div_of_nonneg_left (Real.exp_pos (L / 2)).le hB hMB
      linarith
    calc L / 2 - Real.log M = Real.log (Real.exp (L / 2) / M) := by
          rw [Real.log_div (Real.exp_pos _).ne' hMpos.ne', Real.log_exp]
      _ ≤ _ := Real.log_le_log (div_pos (Real.exp_pos _) hMpos) hle
  rcases le_or_gt L (4 * Real.log M + 2) with hLM | hLM
  · refine le_trans ?_ h2
    calc min (1 / 8) (Real.log 2 / (1 + (4 * Real.log M + 2))) * (1 + L)
        ≤ (Real.log 2 / (1 + (4 * Real.log M + 2))) * (1 + (4 * Real.log M + 2)) :=
          mul_le_mul (min_le_right _ _) (by linarith)
            (by linarith) (div_nonneg (Real.log_pos one_lt_two).le (by linarith))
      _ = Real.log 2 := by field_simp
  · refine le_trans ?_ h3
    calc min (1 / 8) (Real.log 2 / (1 + (4 * Real.log M + 2))) * (1 + L)
        ≤ (1 / 8) * (1 + L) := mul_le_mul_of_nonneg_right (min_le_left _ _) (by linarith)
      _ ≤ L / 2 - Real.log M := by linarith

variable {d : ℕ}

/-- `log (2 + s) ≤ 9 log (2 + ρ) (s / ρ)^{1/2}` for `0 < ρ ≤ s`. -/
theorem log_two_add_le {ρ s : ℝ} (hρ : 0 < ρ) (hs : ρ ≤ s) :
    Real.log (2 + s) ≤ 9 * Real.log (2 + ρ) * (s / ρ) ^ (1 / 2 : ℝ) := by
  set q := s / ρ with hq
  have hq1 : 1 ≤ q := by rw [hq, le_div_iff₀ hρ]; linarith
  have hs0 : 0 ≤ s := by linarith
  have hsplit : Real.log (2 + s) ≤ Real.log (2 + ρ) + Real.log (1 + q) := by
    rw [← Real.log_mul (by positivity) (by positivity)]
    refine Real.log_le_log (by positivity) ?_
    have : (2 + ρ) * (1 + q) = 2 + ρ + 2 * q + s := by
      rw [hq]; field_simp; ring
    rw [this]
    have : 0 ≤ q := by linarith
    linarith
  have hq2 : (1 + q) ^ (1 / 2 : ℝ) ≤ 2 * q ^ (1 / 2 : ℝ) := by
    have h1 : 1 + q ≤ 2 * q := by linarith
    calc (1 + q) ^ (1 / 2 : ℝ) ≤ (2 * q) ^ (1 / 2 : ℝ) :=
          Real.rpow_le_rpow (by linarith) h1 (by norm_num)
      _ = 2 ^ (1 / 2 : ℝ) * q ^ (1 / 2 : ℝ) := Real.mul_rpow (by norm_num) (by linarith)
      _ ≤ 2 * q ^ (1 / 2 : ℝ) := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (by linarith) _)
          calc (2 : ℝ) ^ (1 / 2 : ℝ) ≤ 2 ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
            _ = 2 := Real.rpow_one 2
  have hlog1 : Real.log (1 + q) ≤ 4 * q ^ (1 / 2 : ℝ) := by
    have := Real.log_le_rpow_div (x := 1 + q) (ε := 1 / 2) (by linarith) (by norm_num)
    calc Real.log (1 + q) ≤ (1 + q) ^ (1 / 2 : ℝ) / (1 / 2) := this
      _ ≤ 2 * q ^ (1 / 2 : ℝ) / (1 / 2) := by gcongr
      _ = 4 * q ^ (1 / 2 : ℝ) := by ring
  have hq3 : 1 ≤ q ^ (1 / 2 : ℝ) := Real.one_le_rpow hq1 (by norm_num)
  have hl2 : 1 / 2 ≤ Real.log (2 + ρ) := by
    have := Real.log_two_gt_d9
    have : Real.log 2 ≤ Real.log (2 + ρ) := Real.log_le_log (by norm_num) (by linarith)
    linarith
  nlinarith

/-- A nonzero integer point whose Euclidean norm exceeds `1` has norm at least `√2`. -/
theorem sqrt_two_le_radius {z : Site d} (hz : 1 < radius (physical 1 z)) :
    Real.sqrt 2 ≤ radius (physical 1 z) := by
  have hsum : ∑ k, (physical 1 z k) ^ 2 = ((∑ k, z k ^ 2 : ℤ) : ℝ) := by
    simp [physical]
  unfold radius at hz ⊢
  rw [hsum] at hz ⊢
  have h1 : (1 : ℝ) < ((∑ k, z k ^ 2 : ℤ) : ℝ) := by
    have := (Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 1)).mp hz
    simpa using this
  have h2 : (1 : ℤ) < ∑ k, z k ^ 2 := by exact_mod_cast h1
  have h3 : (2 : ℝ) ≤ ((∑ k, z k ^ 2 : ℤ) : ℝ) := by exact_mod_cast h2
  exact Real.sqrt_le_sqrt h3

/-- The tail sum `ε^d ∑_{|z| > R} log (2 + |z| / ε) / |z|^{d+2}` over the points `z` of `εℤ^d` is
at most `C log (2 + R / ε) / R²` for `R ≥ ε` (summable). -/
theorem exists_tail_sum_le (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε ∈ Ioo (0 : ℝ) 1, ∀ R : ℝ, ε ≤ R →
      Summable (fun z : Site d => if R < radius (physical ε z) then
        Real.log (2 + radius (physical ε z) / ε) / radius (physical ε z) ^ (d + 2) else 0) ∧
      ε ^ d * ∑' z : Site d, (if R < radius (physical ε z) then
        Real.log (2 + radius (physical ε z) / ε) / radius (physical ε z) ^ (d + 2) else 0) ≤
        C * Real.log (2 + R / ε) / R ^ 2 := by
  obtain ⟨C₁, hC₁, hext⟩ := LatticeProb.Euclidean.Estimates.exterior_rpow_sum_bound d hd
    ((d : ℝ) + 3 / 2) (by linarith)
  refine ⟨9 * C₁, by positivity, fun ε hε R hεR => ?_⟩
  have hε0 : 0 < ε := hε.1
  have hR0 : 0 < R := lt_of_lt_of_le hε0 hεR
  have hsq : 1 < Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  set R' := max R (Real.sqrt 2 * ε) with hR'
  have hR'R : R ≤ R' := le_max_left _ _
  have hR'ε : ε < R' := lt_max_of_lt_right (by nlinarith)
  have hR'0 : 0 < R' := lt_trans hε0 hR'ε
  set ε' := ε / R' with hε'
  have hε'mem : ε' ∈ Ioo (0 : ℝ) 1 := ⟨div_pos hε0 hR'0, (div_lt_one hR'0).mpr hR'ε⟩
  obtain ⟨hS, hB⟩ := hext ε' hε'mem
  set α : ℝ := (d : ℝ) + 3 / 2 with hα
  have hrad : ∀ z : Site d, radius (physical ε' z) = radius (physical ε z) / R' := fun z => by
    rw [radius_physical_eq_mul hε'mem.1.le, radius_physical_eq_mul hε0.le, hε']
    ring
  set M : ℝ := 9 * Real.log (2 + R / ε) * R ^ (-(1 / 2 : ℝ)) * R' ^ (-α) with hM
  have hlogR : 0 ≤ Real.log (2 + R / ε) := Real.log_nonneg (by
    have : 0 ≤ R / ε := div_nonneg hR0.le hε0.le
    linarith)
  have hM0 : 0 ≤ M := by positivity
  set g : Site d → ℝ := fun z => if R < radius (physical ε z) then
        Real.log (2 + radius (physical ε z) / ε) / radius (physical ε z) ^ (d + 2) else 0 with hg
  set F : Site d → ℝ := fun z => if 1 ≤ radius (physical ε' z) then
        (radius (physical ε' z)) ^ (-α) else 0 with hF
  have hF0 : ∀ z, 0 ≤ F z := fun z => by
    simp only [hF]; split_ifs
    · exact Real.rpow_nonneg (radius_nonneg _) _
    · exact le_rfl
  have hg0 : ∀ z, 0 ≤ g z := fun z => by
    simp only [hg]; split_ifs
    · refine div_nonneg (Real.log_nonneg ?_) (pow_nonneg (radius_nonneg _) _)
      have : 0 ≤ radius (physical ε z) / ε := div_nonneg (radius_nonneg _) hε0.le
      linarith
    · exact le_rfl
  have hgF : ∀ z, g z ≤ M * F z := fun z => by
    by_cases hz : R < radius (physical ε z)
    · have hρ : 1 < radius (physical 1 z) := by
        have := radius_physical_eq_mul hε0.le z
        by_contra hcon
        have hcon' := not_lt.mp hcon
        nlinarith [radius_nonneg (physical 1 z)]
      have hR'r : R' ≤ radius (physical ε z) := by
        refine max_le hz.le ?_
        have := sqrt_two_le_radius hρ
        rw [radius_physical_eq_mul hε0.le]
        nlinarith
      have h1 : 1 ≤ radius (physical ε' z) := by
        rw [hrad z, le_div_iff₀ hR'0]; linarith
      simp only [hg, hF, hz, h1, ↓reduceIte]
      rw [hrad z]
      set r := radius (physical ε z) with hr
      have hr0 : 0 < r := lt_trans hR0 hz
      have hlog := log_two_add_le (ρ := R / ε) (s := r / ε) (div_pos hR0 hε0)
        (div_le_div_of_nonneg_right hz.le hε0.le)
      rw [div_div_div_cancel_right₀ hε0.ne'] at hlog
      have hpow : r ^ (d + 2) = r ^ ((d : ℝ) + 2) := by
        rw [← Real.rpow_natCast]; push_cast; rfl
      have hrR : (r / R) ^ (1 / 2 : ℝ) = r ^ (1 / 2 : ℝ) * R ^ (-(1 / 2 : ℝ)) := by
        rw [Real.div_rpow hr0.le hR0.le, Real.rpow_neg hR0.le, div_eq_mul_inv]
      have hrα : r ^ (-α) = (r / R') ^ (-α) * R' ^ (-α) := by
        rw [← Real.mul_rpow (div_nonneg hr0.le hR'0.le) hR'0.le, div_mul_cancel₀ _ hR'0.ne']
      have hmain : r ^ (1 / 2 : ℝ) / r ^ ((d : ℝ) + 2) = r ^ (-α) := by
        rw [← Real.rpow_sub hr0]
        congr 1
        rw [hα]; ring
      calc Real.log (2 + r / ε) / r ^ (d + 2)
          ≤ 9 * Real.log (2 + R / ε) * (r / R) ^ (1 / 2 : ℝ) / r ^ (d + 2) :=
            div_le_div_of_nonneg_right hlog (pow_nonneg hr0.le _)
        _ = 9 * Real.log (2 + R / ε) * R ^ (-(1 / 2 : ℝ)) *
              (r ^ (1 / 2 : ℝ) / r ^ ((d : ℝ) + 2)) := by
            rw [hrR, hpow]; ring
        _ = M * (r / R') ^ (-α) := by
            rw [hmain, hrα, hM]; ring
    · simp only [hg, hF, hz, ↓reduceIte]
      split_ifs
      · exact mul_nonneg hM0 (Real.rpow_nonneg (radius_nonneg _) _)
      · simp
  have hsum : Summable g :=
    Summable.of_nonneg_of_le hg0 hgF (hS.mul_left M)
  refine ⟨hsum, ?_⟩
  have h1 : ∑' z, g z ≤ M * ∑' z, F z := by
    rw [← tsum_mul_left]
    exact hsum.tsum_le_tsum hgF (hS.mul_left M)
  have hεd : ε ^ d = R' ^ d * ε' ^ d := by
    rw [hε', div_pow]; field_simp
  have hεpos : 0 < ε' ^ d := pow_pos hε'mem.1 d
  calc ε ^ d * ∑' z, g z ≤ ε ^ d * (M * ∑' z, F z) :=
        mul_le_mul_of_nonneg_left h1 (pow_nonneg hε0.le _)
    _ = M * R' ^ d * (ε' ^ d * ∑' z, F z) := by rw [hεd]; ring
    _ ≤ M * R' ^ d * C₁ :=
        mul_le_mul_of_nonneg_left hB (mul_nonneg hM0 (pow_nonneg hR'0.le _))
    _ = 9 * C₁ * Real.log (2 + R / ε) * (R ^ (-(1 / 2 : ℝ)) * R' ^ (-(3 / 2 : ℝ))) := by
        have : R' ^ (-α) * R' ^ d = R' ^ (-(3 / 2 : ℝ)) := by
          rw [← Real.rpow_natCast, ← Real.rpow_add hR'0]
          congr 1
          rw [hα]; ring
        rw [hM]
        calc 9 * Real.log (2 + R / ε) * R ^ (-(1 / 2 : ℝ)) * R' ^ (-α) * R' ^ d * C₁
            = 9 * C₁ * Real.log (2 + R / ε) * R ^ (-(1 / 2 : ℝ)) * (R' ^ (-α) * R' ^ d) := by ring
          _ = _ := by rw [this]; ring
    _ ≤ 9 * C₁ * Real.log (2 + R / ε) * (R ^ (-(1 / 2 : ℝ)) * R ^ (-(3 / 2 : ℝ))) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hR0.le _)
        exact Real.rpow_le_rpow_of_nonpos hR0 hR'R (by norm_num)
    _ = 9 * C₁ * Real.log (2 + R / ε) / R ^ 2 := by
        rw [← Real.rpow_add hR0]
        rw [show -(1 / 2 : ℝ) + -(3 / 2) = -((2 : ℕ) : ℝ) by push_cast; ring,
          Real.rpow_neg hR0.le, Real.rpow_natCast]
        ring

/-- For `h ≥ ε`, `κ_ε ≤ C log (2 + h / (κ_ε ε²))`: the time `t = h / (κ_ε ε²)` of the unit walk has
`log (2 + t) ≥ c |ln ε| ≥ c' κ_ε`. -/
theorem exists_kappa_le_mul_log (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε ∈ Ioo (0 : ℝ) (1 / 2), ∀ h : ℝ, ε ≤ h →
      kappa d ε ≤ C * Real.log (2 + h / (kappa d ε * ε ^ 2)) := by
  obtain ⟨Ck, hCk, hk⟩ := kappa_le d
  obtain ⟨c, hc, hlog⟩ := exists_mul_le_log_two_add_exp (B := 2 * Ck) (by positivity)
  refine ⟨Ck / c, div_pos hCk hc, fun ε hε h hεh => ?_⟩
  have hε0 : 0 < ε := hε.1
  have hε1 : ε < 1 := by linarith [hε.2]
  have hκ := hk ε ⟨hε0, hε1⟩
  have hκpos : 0 < kappa d ε := LongRange.kappa_pos hd ⟨hε0, hε1⟩
  set L := |Real.log ε| with hL
  have hL0 : 0 ≤ L := abs_nonneg _
  have hLeq : L = -Real.log ε := abs_of_neg (Real.log_neg hε0 hε1)
  set s := Real.exp (L / 2) with hs
  have hspos : 0 < s := Real.exp_pos _
  have hs2 : s ^ 2 = ε⁻¹ := by
    rw [hs, ← Real.exp_nat_mul, hLeq]
    push_cast
    rw [show (2 : ℝ) * (-Real.log ε / 2) = -Real.log ε by ring, Real.exp_neg,
      Real.exp_log hε0]
  have h1L : 1 + L ≤ 2 * s := by
    have := Real.add_one_le_exp (L / 2)
    linarith
  have hκs : kappa d ε ≤ 2 * Ck * s := by nlinarith
  have ht : s / (2 * Ck) ≤ h / (kappa d ε * ε ^ 2) := by
    have hsε : s ^ 2 * ε = 1 := by rw [hs2]; field_simp
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_pos hκpos hε0, mul_nonneg hε0.le (sub_nonneg.mpr hεh)]
  have hmono : Real.log (2 + s / (2 * Ck)) ≤ Real.log (2 + h / (kappa d ε * ε ^ 2)) :=
    Real.log_le_log (by positivity) (by linarith)
  have := hlog L hL0
  rw [← hs] at this
  rw [div_mul_eq_mul_div, le_div_iff₀ hc]
  nlinarith

/-- The on-diagonal bound (i): `ε^{-d} P_x[X_h = y] ≤ C h^{-d/2}` for `h ≥ ε`. -/
theorem heat_kernel_on_diagonal (hMSC : External.MuruganSaloffCosteUniform) (hd : 1 ≤ d)
    {lam : ℝ} (hlam : 0 < lam) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, ∀ hε : ε ∈ Ioo (0 : ℝ) (1 / 2), ∀ a : Edge d → ℝ,
      ∀ ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹, ∀ x y : Site d, ∀ h : ℝ≥0, ε ≤ h →
      (ε ^ d)⁻¹ * ((LongRange.walkRates hd hε.1 hlam a ha).transitionKernel h x).real {y} ≤
        C / (h : ℝ) ^ ((d : ℝ) / 2) := by
  obtain ⟨C₁, hC₁, hdiag⟩ := LongRange.Statements.heatkernel_onDiagonal hMSC d hd hlam
  obtain ⟨Ck, hCk, hlogk⟩ := exists_kappa_le_mul_log hd
  refine ⟨C₁ * Ck ^ ((d : ℝ) / 2), by positivity, fun ε hε a ha x y h hεh => ?_⟩
  have hε0 : 0 < ε := hε.1
  have hεmem : ε ∈ Ioo (0 : ℝ) 1 := ⟨hε0, by linarith [hε.2]⟩
  have hκ : 0 < kappa d ε := LongRange.kappa_pos hd hεmem
  have hh0 : 0 < (h : ℝ) := lt_of_lt_of_le hε0 hεh
  have heq := LongRange.rescaledDensity_eq_unit hd hεmem hlam a ha h x y
  change (ε ^ d)⁻¹ * ((LongRange.walkRates hd hε.1 hlam a ha).transitionKernel h x).real {y} = _
    at heq
  rw [heq]
  set t' : ℝ≥0 := NNReal.mk (1 / (kappa d ε * ε ^ 2)) (by positivity [LongRange.kappa_pos hd hεmem])
    * h with ht'
  have ht'val : (t' : ℝ) = h / (kappa d ε * ε ^ 2) := by
    rw [ht', NNReal.coe_mul, NNReal.coe_mk]; ring
  have ht'pos : 0 < (t' : ℝ) := by rw [ht'val]; positivity
  have hlog : kappa d ε ≤ Ck * Real.log (2 + (t' : ℝ)) := by
    rw [ht'val]; exact hlogk ε hε h hεh
  have hu : (h : ℝ) / (Ck * ε ^ 2) ≤ (t' : ℝ) * Real.log (2 + (t' : ℝ)) := by
    have hlog' : kappa d ε / Ck ≤ Real.log (2 + (t' : ℝ)) := by
      rw [div_le_iff₀ hCk]; linarith
    calc (h : ℝ) / (Ck * ε ^ 2) = (t' : ℝ) * (kappa d ε / Ck) := by
          rw [ht'val]; field_simp
      _ ≤ (t' : ℝ) * Real.log (2 + (t' : ℝ)) := mul_le_mul_of_nonneg_left hlog' ht'pos.le
  have hbase : 0 < (h : ℝ) / (Ck * ε ^ 2) := by positivity
  have h1 := hdiag a ha t' x y
  have h2 : (1 + (t' : ℝ) * Real.log (2 + (t' : ℝ))) ^ (-((d : ℝ) / 2)) ≤
      ((h : ℝ) / (Ck * ε ^ 2)) ^ (-((d : ℝ) / 2)) :=
    Real.rpow_le_rpow_of_nonpos hbase (by linarith) (by
      have : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
      linarith)
  have hε2 : (ε ^ 2) ^ ((d : ℝ) / 2) = ε ^ d := by
    rw [← Real.rpow_natCast ε 2, ← Real.rpow_mul hε0.le]
    rw [show ((2 : ℕ) : ℝ) * ((d : ℝ) / 2) = (d : ℝ) by push_cast; ring, Real.rpow_natCast]
  have h3 : ((h : ℝ) / (Ck * ε ^ 2)) ^ (-((d : ℝ) / 2)) =
      Ck ^ ((d : ℝ) / 2) * ε ^ d / (h : ℝ) ^ ((d : ℝ) / 2) := by
    rw [Real.rpow_neg hbase.le, ← Real.inv_rpow hbase.le, inv_div,
      Real.div_rpow (by positivity) hh0.le, Real.mul_rpow hCk.le (by positivity), hε2]
  have hεd : 0 < ε ^ d := pow_pos hε0 d
  calc (ε ^ d)⁻¹ * ((unitRates hd hlam a ha).transitionKernel t' x).real {y}
      ≤ (ε ^ d)⁻¹ * (C₁ * (1 + (t' : ℝ) * Real.log (2 + (t' : ℝ))) ^ (-((d : ℝ) / 2))) :=
        mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hεd.le)
    _ ≤ (ε ^ d)⁻¹ * (C₁ * (Ck ^ ((d : ℝ) / 2) * ε ^ d / (h : ℝ) ^ ((d : ℝ) / 2))) := by
        rw [← h3]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hC₁.le)
          (inv_nonneg.mpr hεd.le)
    _ = C₁ * Ck ^ ((d : ℝ) / 2) / (h : ℝ) ^ ((d : ℝ) / 2) := by
        field_simp

end

end LongRangeHeat

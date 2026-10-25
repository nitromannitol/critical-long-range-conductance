import LongRange.Model.Kernel

/-!
# Off-diagonal bounds from truncation

The three truncation regimes give `offDiagonal_of_truncated_bounds` from on-diagonal
control, the Meyer comparison, vanishing below the first jump, and a truncated Davies bound.
All lattice distances use the Euclidean radius of the physical displacement.
-/

namespace LongRange

open LatticeProb LatticeProb.Euclidean.Lattice
open scoped NNReal

noncomputable section

variable {d : ℕ}

/-- Distinct integer sites have Euclidean separation at least one. -/
theorem one_le_radius_displacement {x y : Site d} (hxy : x ≠ y) :
    1 ≤ radius (physical 1 (y - x)) :=
  lattice_radius_ge_one (sub_ne_zero.mpr hxy.symm)

/-- The spatial logarithm absorbs a constant on lattice separations. -/
theorem one_le_log_two_add {r : ℝ} (hr : 1 ≤ r) : 1 ≤ Real.log (2 + r) := by
  apply (Real.le_log_iff_exp_le (by linarith : 0 < 2 + r)).mpr
  exact Real.exp_one_lt_three.le.trans (by linarith)

/-- The scaled spatial logarithm is controlled without changing the Euclidean scale. -/
theorem one_add_log_mul_le {γ r : ℝ} (hγ : 0 < γ) (hγone : γ ≤ 1)
    (hr : 1 ≤ r) : 1 + Real.log (γ * r) ≤ 2 * Real.log (2 + r) := by
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hlog := Real.log_le_log (mul_pos hγ hrpos)
    (show γ * r ≤ 2 + r by nlinarith)
  have hone := one_le_log_two_add hr
  linarith

/-- The Meyer error at radius `γ r` has the required spatial decay. -/
theorem truncation_error_le {γ r t L : ℝ} (hγ : 0 < γ) (hr : 1 ≤ r)
    (ht : 0 ≤ t) :
    L * max 1 (γ * r) ^ (-((d : ℝ) + 2)) * t ≤
      |L| / γ ^ (d + 2) * t * Real.log (2 + r) / r ^ (d + 2) := by
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hρ : 0 < γ * r := mul_pos hγ hrpos
  have hp : 0 ≤ max 1 (γ * r) ^ (-((d : ℝ) + 2)) := (by positivity)
  have hdec := Real.rpow_le_rpow_of_nonpos (z := -((d : ℝ) + 2)) hρ (le_max_right 1 (γ * r))
    (neg_nonpos.mpr (by positivity))
  have hcast : -((d : ℝ) + 2) = -((d + 2 : ℕ) : ℝ) := by push_cast; ring
  have hright : (γ * r) ^ (-((d : ℝ) + 2)) =
      (γ ^ (d + 2) * r ^ (d + 2))⁻¹ := by
    rw [hcast, Real.rpow_neg hρ.le, Real.rpow_natCast, mul_pow]
  rw [hright] at hdec
  have hlog := one_le_log_two_add hr
  calc
    L * max 1 (γ * r) ^ (-((d : ℝ) + 2)) * t ≤
        |L| * max 1 (γ * r) ^ (-((d : ℝ) + 2)) * t := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_abs_self L) hp) ht
    _ ≤ |L| * (γ ^ (d + 2) * r ^ (d + 2))⁻¹ * t := by gcongr
    _ = |L| / γ ^ (d + 2) * t / r ^ (d + 2) := by ring
    _ ≤ |L| / γ ^ (d + 2) * t * Real.log (2 + r) / r ^ (d + 2) := by
      apply div_le_div_of_nonneg_right _ (pow_nonneg hrpos.le _)
      exact le_mul_of_one_le_right (by positivity) hlog

/-- Below the first lattice jump, the truncated kernel vanishes and only Meyer remains. -/
theorem offDiagonal_of_small_truncation
    (u : ℝ≥0 → Site d → Site d → ℝ)
    (uρ : ℝ → ℝ≥0 → Site d → Site d → ℝ)
    {L γ : ℝ} (hγ : 0 < γ)
    (hM2 : ∀ ρ : ℝ, 0 < ρ → ∀ t x y,
      u t x y ≤ uρ ρ t x y + L * max 1 ρ ^ (-((d : ℝ) + 2)) * t)
    (hzero : ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∀ t x y, x ≠ y → uρ ρ t x y = 0)
    (t : ℝ≥0) {x y : Site d} (hxy : x ≠ y)
    (hsmall : γ * radius (physical 1 (y - x)) < 1) :
    u t x y ≤ |L| / γ ^ (d + 2) * t *
      Real.log (2 + radius (physical 1 (y - x))) /
        radius (physical 1 (y - x)) ^ (d + 2) := by
  have hr := one_le_radius_displacement hxy
  have hρ := mul_pos hγ (lt_of_lt_of_le zero_lt_one hr)
  have hm := hM2 _ hρ t x y
  rw [hzero _ hρ hsmall t x y hxy, zero_add] at hm
  exact hm.trans (truncation_error_le (d := d) hγ hr t.coe_nonneg)

/-- The logarithmic diffusion time is at least its spatial radius. -/
theorem radius_le_logarithmic_time {ρ : ℝ} (hρ : 1 ≤ ρ) :
    ρ ≤ ρ ^ 2 / (1 + Real.log ρ) := by
  have hpos : 0 < ρ := lt_of_lt_of_le zero_lt_one hρ
  have hlog : 0 ≤ Real.log ρ := Real.log_nonneg hρ
  have hupper := Real.log_le_sub_one_of_pos hpos
  apply (le_div_iff₀ (by positivity : 0 < 1 + Real.log ρ)).mpr
  nlinarith

/-- At the logarithmic diffusion time the on-diagonal denominator controls radius squared. -/
theorem sq_le_time_log_mul {ρ t : ℝ} (hρ : 1 ≤ ρ)
    (ht : ρ ^ 2 / (1 + Real.log ρ) ≤ t) :
    ρ ^ 2 ≤ (1 + 1 / Real.log 2) * (t * Real.log (2 + t)) := by
  have hρpos : 0 < ρ := lt_of_lt_of_le zero_lt_one hρ
  have hlρ : 0 ≤ Real.log ρ := Real.log_nonneg hρ
  have htime : ρ ≤ t := (radius_le_logarithmic_time hρ).trans ht
  have htpos : 0 < t := hρpos.trans_le htime
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2 : Real.log 2 ≤ Real.log (2 + t) :=
    Real.log_le_log (by norm_num) (by linarith)
  have hlogρ : Real.log ρ ≤ Real.log (2 + t) :=
    Real.log_le_log hρpos (by linarith)
  have hone : 1 ≤ Real.log (2 + t) / Real.log 2 :=
    (le_div_iff₀ hl2).mpr (by simpa using hlog2)
  have hsum : 1 + Real.log ρ ≤
      (1 + 1 / Real.log 2) * Real.log (2 + t) := by
    calc
      1 + Real.log ρ ≤ Real.log (2 + t) / Real.log 2 + Real.log (2 + t) :=
        add_le_add hone hlogρ
      _ = _ := by ring
  have hsq := (div_le_iff₀ (by positivity : 0 < 1 + Real.log ρ)).mp ht
  exact hsq.trans (by nlinarith only [mul_le_mul_of_nonneg_left hsum htpos.le])


/-- A squared radius to the negative half dimension is the inverse volume. -/
theorem sq_rpow_neg_half (ρ : ℝ) (hρ : 0 ≤ ρ) :
    (ρ ^ 2) ^ (-((d : ℝ) / 2)) = (ρ ^ d)⁻¹ := by
  rw [← Real.rpow_natCast ρ 2, ← Real.rpow_mul hρ]
  have hexp : (2 : ℝ) * (-((d : ℝ) / 2)) = -(d : ℝ) := by ring
  norm_num only [Nat.cast_ofNat]
  rw [hexp, Real.rpow_neg hρ, Real.rpow_natCast]

/-- The on-diagonal profile at large times has inverse-volume decay. -/
theorem onDiagonal_profile_le {ρ t : ℝ} (hρ : 1 ≤ ρ)
    (ht : ρ ^ 2 / (1 + Real.log ρ) ≤ t) :
    (1 + t * Real.log (2 + t)) ^ (-((d : ℝ) / 2)) ≤
      (1 + 1 / Real.log 2) ^ ((d : ℝ) / 2) / ρ ^ d := by
  have hρpos : 0 < ρ := lt_of_lt_of_le zero_lt_one hρ
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hD : 0 < 1 + 1 / Real.log 2 := by positivity
  have hs := sq_le_time_log_mul hρ ht
  have hbase : ρ ^ 2 / (1 + 1 / Real.log 2) ≤ 1 + t * Real.log (2 + t) := by
    apply (div_le_iff₀ hD).mpr
    nlinarith only [hs, hD]
  have hpow := Real.rpow_le_rpow_of_nonpos (z := -((d : ℝ) / 2))
    (div_pos (sq_pos_of_pos hρpos) hD)
    hbase (neg_nonpos.mpr (by positivity))
  calc
    _ ≤ (ρ ^ 2 / (1 + 1 / Real.log 2)) ^ (-((d : ℝ) / 2)) := hpow
    _ = _ := by
      rw [Real.div_rpow (sq_nonneg ρ) hD.le, sq_rpow_neg_half ρ hρpos.le,
        Real.rpow_neg hD.le]
      simp only [div_eq_mul_inv, inv_inv]
      ring

/-- Above the diffusion time, inverse-volume decay implies the desired spatial bound. -/
theorem inverse_volume_le_spatial {γ r t : ℝ} (hγ : 0 < γ) (hγone : γ ≤ 1)
    (hr : 1 ≤ r) (hρ : 1 ≤ γ * r)
    (ht : (γ * r) ^ 2 / (1 + Real.log (γ * r)) ≤ t) :
    1 / (γ * r) ^ d ≤
      2 / γ ^ (d + 2) * t * Real.log (2 + r) / r ^ (d + 2) := by
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hρpos : 0 < γ * r := mul_pos hγ hrpos
  have hlρ : 0 ≤ Real.log (γ * r) := Real.log_nonneg hρ
  have hlog := one_add_log_mul_le hγ hγone hr
  have htime : 0 ≤ t := (hρpos.trans_le ((radius_le_logarithmic_time hρ).trans ht)).le
  have hs := (div_le_iff₀ (by positivity : 0 < 1 + Real.log (γ * r))).mp ht
  have hmain : (γ * r) ^ 2 ≤ 2 * t * Real.log (2 + r) :=
    hs.trans (by nlinarith only [mul_le_mul_of_nonneg_left hlog htime])
  apply (div_le_div_iff₀ (pow_pos hρpos d) (pow_pos hrpos (d + 2))).mpr
  rw [one_mul, mul_pow]
  have hprod : r ^ (d + 2) * γ ^ (d + 2) ≤
      (2 * t * Real.log (2 + r)) * (γ ^ d * r ^ d) := by
    calc
      r ^ (d + 2) * γ ^ (d + 2) =
          (γ * r) ^ 2 * (γ ^ d * r ^ d) := by
        rw [pow_add, pow_add, mul_pow]
        ring
      _ ≤ (2 * t * Real.log (2 + r)) * (γ ^ d * r ^ d) :=
        mul_le_mul_of_nonneg_right hmain (by positivity)
  have hdiv := (le_div_iff₀ (pow_pos hγ (d + 2))).mpr hprod
  convert hdiv using 1; ring


/-- A logarithmic power is controlled by a linear spatial power, with explicit constant. -/
theorem one_add_log_rpow_le {ρ p : ℝ} (hρ : 1 ≤ ρ) (hp : 1 ≤ p) :
    (1 + Real.log ρ) ^ p ≤ p ^ p * ρ := by
  have hρpos : 0 < ρ := lt_of_lt_of_le zero_lt_one hρ
  have hppos : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hlog := Real.log_le_sub_one_of_pos
    (Real.rpow_pos_of_pos hρpos (1 / p))
  rw [Real.log_rpow hρpos] at hlog
  have hbase : 1 + Real.log ρ ≤ p * ρ ^ (1 / p) := by
    have hm := mul_le_mul_of_nonneg_left hlog hppos.le
    have heq : p * (1 / p * Real.log ρ) = Real.log ρ := by field_simp
    rw [heq] at hm
    linarith
  calc
    (1 + Real.log ρ) ^ p ≤ (p * ρ ^ (1 / p)) ^ p :=
      Real.rpow_le_rpow (by positivity [Real.log_nonneg hρ]) hbase hppos.le
    _ = p ^ p * ρ := by
      rw [Real.mul_rpow hppos.le (by positivity),
        ← Real.rpow_mul hρpos.le]
      simp only [one_div_mul_cancel hppos.ne', Real.rpow_one]

/-- Cancellation of the time and volume powers in the small-time profile estimate. -/
theorem truncated_profile_identity {t H J ρ : ℝ} (ht : 0 < t) (hH : 0 < H)
    (hJ : 0 < J) (hρ : 0 < ρ) :
    (t * J) ^ (-((d : ℝ) / 2)) *
        (t * H / ρ ^ 2) ^ ((d : ℝ) / 2 + 1) * ρ ^ d =
      (t * H / ρ ^ 2) * (H / J) ^ ((d : ℝ) / 2) := by
  have hsq : (ρ ^ 2) ^ ((d : ℝ) / 2) = ρ ^ d := by
    rw [← Real.rpow_natCast ρ 2, ← Real.rpow_mul hρ.le]
    have hexp : (2 : ℝ) * ((d : ℝ) / 2) = d := by ring
    norm_num only [Nat.cast_ofNat]
    rw [hexp, Real.rpow_natCast]
  rw [Real.rpow_add (div_pos (mul_pos ht hH) (sq_pos_of_pos hρ)), Real.rpow_one,
    Real.rpow_neg (mul_pos ht hJ).le,
    Real.mul_rpow ht.le hJ.le,
    Real.div_rpow (mul_pos ht hH).le (sq_nonneg ρ),
    Real.mul_rpow ht.le hH.le, hsq, Real.div_rpow hH.le hJ.le]
  have htne := (Real.rpow_pos_of_pos ht ((d : ℝ) / 2)).ne'
  have hJne := (Real.rpow_pos_of_pos hJ ((d : ℝ) / 2)).ne'
  have hρne := (pow_pos hρ d).ne'
  field_simp

/-- The normalized small-time profile is uniformly bounded over all radii and times. -/
theorem truncated_profile_le {ρ t : ℝ} (hρ : 1 ≤ ρ) (ht : 0 < t)
    (hw : t * (1 + Real.log ρ) / ρ ^ 2 ≤ 1) :
    (t * (1 + Real.log (1 + t))) ^ (-((d : ℝ) / 2)) *
        (t * (1 + Real.log ρ) / ρ ^ 2) ^ ((d : ℝ) / 2 + 1) * ρ ^ d ≤
      2 ^ ((d : ℝ) / 2) + ((d : ℝ) / 2 + 1) ^ ((d : ℝ) / 2 + 1) := by
  have hρpos : 0 < ρ := lt_of_lt_of_le zero_lt_one hρ
  have hH : 0 < 1 + Real.log ρ := by positivity [Real.log_nonneg hρ]
  have hlJ : 0 ≤ Real.log (1 + t) := Real.log_nonneg (by linarith)
  have hJ : 0 < 1 + Real.log (1 + t) := by positivity
  have ha : 0 ≤ (d : ℝ) / 2 := by positivity
  rw [truncated_profile_identity ht hH hJ hρpos]
  by_cases hlarge : ρ ^ (1 / 2 : ℝ) ≤ t
  · have hl := Real.log_le_log (Real.rpow_pos_of_pos hρpos (1 / 2 : ℝ))
      (show ρ ^ (1 / 2 : ℝ) ≤ 1 + t by linarith)
    rw [Real.log_rpow hρpos] at hl
    have hratio : (1 + Real.log ρ) / (1 + Real.log (1 + t)) ≤ 2 := by
      apply (div_le_iff₀ hJ).mpr
      linarith
    have hpow := Real.rpow_le_rpow (div_pos hH hJ).le hratio ha
    calc
      _ ≤ 1 * 2 ^ ((d : ℝ) / 2) :=
        mul_le_mul hw hpow (by positivity) (by norm_num)
      _ ≤ _ := by
        have hp : 0 ≤ ((d : ℝ) / 2 + 1) ^ ((d : ℝ) / 2 + 1) := by positivity
        linarith
  · have htupper : t ≤ ρ ^ (1 / 2 : ℝ) := (lt_of_not_ge hlarge).le
    have hratio : (1 + Real.log ρ) / (1 + Real.log (1 + t)) ≤
        1 + Real.log ρ := by
      apply (div_le_iff₀ hJ).mpr
      nlinarith only [hlJ, hH]
    have hpow := Real.rpow_le_rpow (div_pos hH hJ).le hratio ha
    have hlogbound := one_add_log_rpow_le hρ
      (show 1 ≤ (d : ℝ) / 2 + 1 by linarith only [ha])
    have hroot : ρ ^ (1 / 2 : ℝ) ≤ ρ := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le hρ (by norm_num : (1 / 2 : ℝ) ≤ 1)
    calc
      _ ≤ (ρ ^ (1 / 2 : ℝ) * (1 + Real.log ρ) / ρ ^ 2) *
          (1 + Real.log ρ) ^ ((d : ℝ) / 2) := by
        apply mul_le_mul _ hpow (by positivity) (by positivity)
        gcongr
      _ = ρ ^ (1 / 2 : ℝ) * (1 + Real.log ρ) ^ ((d : ℝ) / 2 + 1) / ρ ^ 2 := by
        rw [Real.rpow_add hH, Real.rpow_one]
        ring
      _ ≤ ρ * (((d : ℝ) / 2 + 1) ^ ((d : ℝ) / 2 + 1) * ρ) / ρ ^ 2 := by
        gcongr
      _ = ((d : ℝ) / 2 + 1) ^ ((d : ℝ) / 2 + 1) := by
        field_simp
      _ ≤ _ := le_add_of_nonneg_left (by positivity)


/-- The quadratic Davies penalty is uniformly bounded after exponential damping. -/
theorem sq_mul_exp_neg_le_four {σ : ℝ} (hσ : 0 ≤ σ) :
    σ ^ 2 * Real.exp (-σ) ≤ 4 := by
  have he := Real.add_one_le_exp (σ / 2)
  have hhalf : σ / 2 ≤ Real.exp (σ / 2) := by linarith
  have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ σ / 2) hhalf 2
  have hexp : Real.exp (σ / 2) ^ 2 = Real.exp σ := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  rw [hexp] at hsq
  have hbound : σ ^ 2 ≤ 4 * Real.exp σ := by nlinarith only [hsq]
  calc
    σ ^ 2 * Real.exp (-σ) ≤ 4 * Real.exp σ * Real.exp (-σ) := by gcongr
    _ = 4 := by rw [mul_assoc, ← Real.exp_add]; norm_num

/-- The logarithmic choice of Davies parameter converts the spatial exponential to a power. -/
theorem davies_exponential_le {w z B κ : ℝ} (hw : 0 < w) (hwone : w ≤ 1)
    (hz : 0 ≤ z) (hzone : z ≤ 1) :
    let σ := -Real.log w / 3
    Real.exp (B * z) *
        Real.exp (-3 * κ * σ + B * σ ^ 2 * Real.exp (2 * σ) * w) ≤
      Real.exp (5 * |B|) * w ^ κ := by
  dsimp only
  let σ := -Real.log w / 3
  have hσ : 0 ≤ σ := by
    dsimp only [σ]
    have := Real.log_nonpos hw.le hwone
    linarith
  have hlog : Real.log w = -3 * σ := by dsimp only [σ]; ring
  have hwexp : w = Real.exp (-3 * σ) := by rw [← hlog, Real.exp_log hw]
  have hpen : 0 ≤ σ ^ 2 * Real.exp (2 * σ) * w := by positivity
  have hpenbound : σ ^ 2 * Real.exp (2 * σ) * w ≤ 4 := by
    rw [hwexp, mul_assoc, ← Real.exp_add]
    have heq : 2 * σ + -3 * σ = -σ := by ring
    rw [heq]
    exact sq_mul_exp_neg_le_four hσ
  have hB : B * z ≤ |B| :=
    (mul_le_mul_of_nonneg_right (le_abs_self B) hz).trans
      (mul_le_of_le_one_right (abs_nonneg B) hzone)
  have hBpen : B * (σ ^ 2 * Real.exp (2 * σ) * w) ≤ 4 * |B| :=
    (mul_le_mul_of_nonneg_right (le_abs_self B) hpen).trans
      (by nlinarith only [mul_le_mul_of_nonneg_left hpenbound (abs_nonneg B)])
  have hexp : B * z + (-3 * κ * σ + B * σ ^ 2 * Real.exp (2 * σ) * w) ≤
      5 * |B| + Real.log w * κ := by
    rw [hlog]
    nlinarith only [hB, hBpen]
  calc
    _ = Real.exp (B * z + (-3 * κ * σ + B * σ ^ 2 * Real.exp (2 * σ) * w)) :=
      (Real.exp_add _ _).symm
    _ ≤ Real.exp (5 * |B| + Real.log w * κ) := Real.exp_le_exp.mpr hexp
    _ = _ := by rw [Real.exp_add, ← Real.rpow_def_of_pos hw]


/-- The optimized Davies estimate has the logarithmic spatial decay before scaling. -/
theorem davies_profile_le {ρ r t A B v : ℝ} (hρ : 1 ≤ ρ) (ht : 0 < t)
    (hwone : t * (1 + Real.log ρ) / ρ ^ 2 ≤ 1)
    (hratio : r / ρ = 3 * ((d : ℝ) / 2 + 2))
    (hDav : ∀ σ : ℝ, 0 ≤ σ →
      v ≤ A * (t * (1 + Real.log (1 + t))) ^ (-((d : ℝ) / 2)) *
        Real.exp (B * ρ ^ (-(2 : ℝ)) * t) *
        Real.exp (-(σ * r / ρ) +
          B * σ ^ 2 * Real.exp (2 * σ) * (1 + Real.log ρ) * t / ρ ^ 2)) :
    v ≤ (|A| * Real.exp (5 * |B|) *
        (2 ^ ((d : ℝ) / 2) + ((d : ℝ) / 2 + 1) ^ ((d : ℝ) / 2 + 1))) *
      t * (1 + Real.log ρ) / ρ ^ (d + 2) := by
  have hρpos : 0 < ρ := lt_of_lt_of_le zero_lt_one hρ
  have hlρ := Real.log_nonneg hρ
  have hH : 0 < 1 + Real.log ρ := by positivity
  let w := t * (1 + Real.log ρ) / ρ ^ 2
  have hw : 0 < w := div_pos (mul_pos ht hH) (sq_pos_of_pos hρpos)
  have hwle : w ≤ 1 := hwone
  let σ := -Real.log w / 3
  have hσ : 0 ≤ σ := by
    dsimp only [σ]
    have := Real.log_nonpos hw.le hwle
    linarith
  have hz : 0 ≤ t / ρ ^ 2 := by positivity
  have hzone : t / ρ ^ 2 ≤ 1 := by
    have hs := (div_le_iff₀ (sq_pos_of_pos hρpos)).mp hwone
    apply (div_le_iff₀ (sq_pos_of_pos hρpos)).mpr
    nlinarith only [mul_nonneg ht.le hlρ, hs]
  have hexp := davies_exponential_le (B := B) (κ := (d : ℝ) / 2 + 2) hw hwle hz hzone
  change Real.exp (B * (t / ρ ^ 2)) *
      Real.exp (-3 * ((d : ℝ) / 2 + 2) * σ + B * σ ^ 2 * Real.exp (2 * σ) * w) ≤
        Real.exp (5 * |B|) * w ^ ((d : ℝ) / 2 + 2) at hexp
  have heq₁ : B * ρ ^ (-(2 : ℝ)) * t = B * (t / ρ ^ 2) := by
    rw [Real.rpow_neg hρpos.le, Real.rpow_two]
    ring
  have heq₂ : -(σ * r / ρ) +
      B * σ ^ 2 * Real.exp (2 * σ) * (1 + Real.log ρ) * t / ρ ^ 2 =
      -3 * ((d : ℝ) / 2 + 2) * σ + B * σ ^ 2 * Real.exp (2 * σ) * w := by
    rw [mul_div_assoc, hratio]
    dsimp only [w]
    ring
  have hbound := hDav σ hσ
  rw [heq₁, heq₂, mul_assoc (A * _)] at hbound
  have hlJ : 0 ≤ Real.log (1 + t) := Real.log_nonneg (by linarith)
  have hφ : 0 ≤ (t * (1 + Real.log (1 + t))) ^ (-((d : ℝ) / 2)) :=
    Real.rpow_nonneg (mul_nonneg ht.le (by linarith)) _
  have hopt : v ≤ |A| * Real.exp (5 * |B|) *
      ((t * (1 + Real.log (1 + t))) ^ (-((d : ℝ) / 2)) *
        w ^ ((d : ℝ) / 2 + 2)) := by
    calc
      v ≤ A * (t * (1 + Real.log (1 + t))) ^ (-((d : ℝ) / 2)) *
          (Real.exp (B * (t / ρ ^ 2)) * Real.exp
            (-3 * ((d : ℝ) / 2 + 2) * σ + B * σ ^ 2 * Real.exp (2 * σ) * w)) :=
        hbound
      _ ≤ |A| * (t * (1 + Real.log (1 + t))) ^ (-((d : ℝ) / 2)) *
          (Real.exp (5 * |B|) * w ^ ((d : ℝ) / 2 + 2)) := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_right (le_abs_self A) hφ
        · exact hexp
        · positivity
        · positivity
      _ = _ := by ring
  have hprof := truncated_profile_le (d := d) hρ ht hwone
  have hcancellation :
      (t * (1 + Real.log (1 + t))) ^ (-((d : ℝ) / 2)) * w ^ ((d : ℝ) / 2 + 2) =
      ((t * (1 + Real.log (1 + t))) ^ (-((d : ℝ) / 2)) *
        w ^ ((d : ℝ) / 2 + 1) * ρ ^ d) * (w / ρ ^ d) := by
    have he : (d : ℝ) / 2 + 2 = ((d : ℝ) / 2 + 1) + 1 := by ring
    rw [he, Real.rpow_add hw, Real.rpow_one]
    field_simp
  rw [hcancellation] at hopt
  calc
    v ≤ |A| * Real.exp (5 * |B|) *
        ((2 ^ ((d : ℝ) / 2) + ((d : ℝ) / 2 + 1) ^ ((d : ℝ) / 2 + 1)) *
          (w / ρ ^ d)) := by
      exact hopt.trans (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hprof (by positivity)) (by positivity))
    _ = _ := by
      dsimp only [w]
      rw [pow_add]
      ring


/-- Rescaling the cutoff transports its logarithmic decay to the original separation. -/
theorem scaled_logarithmic_bound {γ r t K : ℝ} (hγ : 0 < γ) (hγone : γ ≤ 1)
    (hr : 1 ≤ r) (ht : 0 ≤ t) (hK : 0 ≤ K) :
    K * t * (1 + Real.log (γ * r)) / (γ * r) ^ (d + 2) ≤
      (2 * K / γ ^ (d + 2)) * t * Real.log (2 + r) / r ^ (d + 2) := by
  have hlog := one_add_log_mul_le hγ hγone hr
  calc
    _ ≤ K * t * (2 * Real.log (2 + r)) / (γ * r) ^ (d + 2) := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hlog (mul_nonneg hK ht)) (by positivity)
    _ = _ := by rw [mul_pow]; ring

/-- On-diagonal decay, Meyer comparison, sub-unit vanishing and a truncated Davies bound
imply the off-diagonal estimate, with a constant depending only on the input constants. -/
theorem offDiagonal_of_truncated_bounds (hd : 1 ≤ d)
    (u : ℝ≥0 → Site d → Site d → ℝ)
    (uρ : ℝ → ℝ≥0 → Site d → Site d → ℝ)
    {Ca L A B : ℝ}
    (hODB : ∀ t x y, u t x y ≤
      Ca * (1 + t * Real.log (2 + t)) ^ (-((d : ℝ) / 2)))
    (hM2 : ∀ ρ : ℝ, 0 < ρ → ∀ t x y,
      u t x y ≤ uρ ρ t x y + L * max 1 ρ ^ (-((d : ℝ) + 2)) * t)
    (hzero : ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∀ t x y, x ≠ y → uρ ρ t x y = 0)
    (hDav : ∀ ρ : ℝ, 1 ≤ ρ → ∀ σ : ℝ, 0 ≤ σ →
      ∀ t : ℝ≥0, 0 < t → ∀ x y,
      uρ ρ t x y ≤ A * (t * (1 + Real.log (1 + t))) ^ (-((d : ℝ) / 2)) *
        Real.exp (B * ρ ^ (-(2 : ℝ)) * t) *
        Real.exp (-(σ * radius (physical 1 (y - x)) / ρ) +
          B * σ ^ 2 * Real.exp (2 * σ) * (1 + Real.log ρ) * t / ρ ^ 2)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ≥0), 0 < t → ∀ x y, x ≠ y →
      u t x y ≤ C * t * Real.log (2 + radius (physical 1 (y - x))) /
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
  intro t ht x y hxy
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
  change u t x y ≤ C * (t : ℝ) * Real.log (2 + r) / r ^ (d + 2)
  suffices hfinal : u t x y ≤ C * F by simpa only [F, mul_div_assoc, mul_assoc] using hfinal
  by_cases hsmall : γ * r < 1
  · have hu := offDiagonal_of_small_truncation u uρ hγ hM2 hzero t hxy hsmall
    have hu' : u t x y ≤ E * F := by
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
      have hu : u t x y ≤ |Ca| * (D / (γ * r) ^ d) := by
        calc
          u t x y ≤ Ca * (1 + (t : ℝ) * Real.log (2 + t)) ^ (-((d : ℝ) / 2)) :=
            hODB t x y
          _ ≤ |Ca| * (D / (γ * r) ^ d) := by
            exact mul_le_mul (le_abs_self Ca) hp hprofile (abs_nonneg Ca)
      have hu' : u t x y ≤ H * F := by
        calc
          u t x y ≤ |Ca| * (D / (γ * r) ^ d) := hu
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
        (fun σ hσ => hDav (γ * r) hρ σ hσ t ht x y)
      have hscaled := scaled_logarithmic_bound (d := d) hγ hγone hr t.coe_nonneg hK
      have htr' : uρ (γ * r) t x y ≤ S * F := by
        calc
          _ ≤ K * t * (1 + Real.log (γ * r)) / (γ * r) ^ (d + 2) := htr
          _ ≤ (2 * K / γ ^ (d + 2)) * t * Real.log (2 + r) / r ^ (d + 2) := hscaled
          _ = S * F := by dsimp only [S, F]; ring
      have herr : L * max 1 (γ * r) ^ (-((d : ℝ) + 2)) * t ≤ E * F := by
        convert truncation_error_le (d := d) hγ hr t.coe_nonneg using 1
        dsimp only [E, F]
        ring
      calc
        u t x y ≤ uρ (γ * r) t x y +
            L * max 1 (γ * r) ^ (-((d : ℝ) + 2)) * t := hM2 _ hρpos t x y
        _ ≤ S * F + E * F := add_le_add htr' herr
        _ = (S + E) * F := by ring
        _ ≤ C * F := mul_le_mul_of_nonneg_right (by dsimp only [C]; linarith) hF

end

end LongRange

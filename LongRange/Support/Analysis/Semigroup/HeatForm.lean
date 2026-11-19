import LongRange.Support.Analysis.Semigroup.HeatKernelSplit

/-!
# The quadratic form of the transition semigroup

For symmetric bounded rates and a square-summable `f`, the function
`a(t) = ∑ᵢ f i (P_t f)(i)` equals `∑ᵢ (P_s f)(i) (P_u f)(i)` whenever `s + u = t`. Hence `a` is
nonnegative, `a(2s) = ‖P_s f‖²`, and `a(s + u)² ≤ a(2s) a(2u)` by Cauchy–Schwarz. Near time
zero, `a(t) = ‖f‖² - t E(f) + O(t²)` with explicit constants. If the transition probabilities
at time `t` are at most `B`, then `a(t) ≤ B ‖f‖₁²`.
-/

namespace LatticeProb.JumpChain.BoundedRates

open MeasureTheory
open scoped NNReal

noncomputable section

variable {S : Type*} [MeasurableSpace S] [Countable S] [MeasurableSingletonClass S]

/-- The quadratic form `t ↦ ∑ᵢ f i (P_t f)(i)` of the transition semigroup. -/
def heatForm (rates : BoundedRates S) (f : S → ℝ) (t : ℝ≥0) : ℝ :=
  ∑' i, f i * kernelApply (rates.heatKernel t) f i

/-- At time zero the quadratic form is the squared norm. -/
theorem heatForm_zero (rates : BoundedRates S) (f : S → ℝ) :
    rates.heatForm f 0 = ∑' i, f i ^ 2 :=
  tsum_congr fun i ↦ by rw [rates.kernelApply_heatKernel_zero, sq]

/-- The quadratic form at a sum of times is the inner product of the two evolved functions. -/
theorem heatForm_add (rates : BoundedRates S) (hs : ∀ i j, rates.q i j = rates.q j i)
    {f : S → ℝ} (hf : Summable fun i ↦ f i ^ 2) (s u : ℝ≥0) :
    rates.heatForm f (s + u) =
      ∑' i, kernelApply (rates.heatKernel s) f i * kernelApply (rates.heatKernel u) f i := by
  have hu := (rates.isSymmKernel_heatKernel hs u).summable_kernelApply_sq hf
  calc
    rates.heatForm f (s + u) =
        ∑' i, f i * kernelApply (rates.heatKernel s) (kernelApply (rates.heatKernel u) f) i :=
      tsum_congr fun i ↦ by
        rw [rates.kernelApply_heatKernel_add hs s u (abs_le_sqrt_tsum_sq hf) i]
    _ = _ := (rates.isSymmKernel_heatKernel hs s).tsum_mul_kernelApply_comm hu hf

/-- At twice a time the quadratic form is the squared norm of the evolved function. -/
theorem heatForm_add_self (rates : BoundedRates S) (hs : ∀ i j, rates.q i j = rates.q j i)
    {f : S → ℝ} (hf : Summable fun i ↦ f i ^ 2) (s : ℝ≥0) :
    rates.heatForm f (s + s) = ∑' i, kernelApply (rates.heatKernel s) f i ^ 2 := by
  rw [rates.heatForm_add hs hf]
  exact tsum_congr fun i ↦ (sq _).symm

/-- The quadratic form of the transition semigroup is nonnegative. -/
theorem heatForm_nonneg (rates : BoundedRates S) (hs : ∀ i j, rates.q i j = rates.q j i)
    {f : S → ℝ} (hf : Summable fun i ↦ f i ^ 2) (t : ℝ≥0) : 0 ≤ rates.heatForm f t := by
  have h := rates.heatForm_add_self hs hf (t / 2)
  rw [add_halves] at h
  rw [h]
  exact tsum_nonneg fun i ↦ sq_nonneg _

/-- Cauchy–Schwarz for the evolved functions: the quadratic form is midpoint log-convex. -/
theorem heatForm_add_sq_le (rates : BoundedRates S) (hs : ∀ i j, rates.q i j = rates.q j i)
    {f : S → ℝ} (hf : Summable fun i ↦ f i ^ 2) (s u : ℝ≥0) :
    rates.heatForm f (s + u) ^ 2 ≤ rates.heatForm f (s + s) * rates.heatForm f (u + u) := by
  rw [rates.heatForm_add hs hf s u, rates.heatForm_add_self hs hf s,
    rates.heatForm_add_self hs hf u]
  exact sq_tsum_mul_le_tsum_sq_mul
    ((rates.isSymmKernel_heatKernel hs s).summable_kernelApply_sq hf)
    ((rates.isSymmKernel_heatKernel hs u).summable_kernelApply_sq hf)

/-- The midpoint form of log-convexity. -/
theorem heatForm_midpoint_sq_le (rates : BoundedRates S)
    (hs : ∀ i j, rates.q i j = rates.q j i) {f : S → ℝ} (hf : Summable fun i ↦ f i ^ 2)
    (s u : ℝ≥0) :
    rates.heatForm f ((s + u) / 2) ^ 2 ≤ rates.heatForm f s * rates.heatForm f u := by
  have h := rates.heatForm_add_sq_le hs hf (s / 2) (u / 2)
  rwa [add_halves, add_halves, ← add_div] at h

/-- An entrywise bound on the transition probabilities bounds the quadratic form through the
squared counting `ℓ¹` norm. -/
theorem heatForm_le_of_heatKernel_le (rates : BoundedRates S) {f : S → ℝ}
    (hf1 : Summable fun i ↦ |f i|) {t : ℝ≥0} {B : ℝ}
    (hB : ∀ i j, rates.heatKernel t i j ≤ B) :
    rates.heatForm f t ≤ B * (∑' i, |f i|) ^ 2 := by
  set F := ∑' i, |f i|
  have hrow (i : S) : Summable fun j ↦ rates.heatKernel t i j * |f j| :=
    hf1.of_nonneg_of_le (fun j ↦ mul_nonneg (rates.heatKernel_nonneg t i j) (abs_nonneg _))
      fun j ↦ mul_le_of_le_one_left (abs_nonneg _) (rates.heatKernel_le_one t i j)
  have happly (i : S) :
      |kernelApply (rates.heatKernel t) f i| ≤ ∑' j, rates.heatKernel t i j * |f j| := by
    have hn : Summable fun j ↦ ‖rates.heatKernel t i j * f j‖ :=
      (hrow i).congr fun j ↦ by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (rates.heatKernel_nonneg t i j)]
    have h := norm_tsum_le_tsum_norm hn
    simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (rates.heatKernel_nonneg t i _)] at h
    exact h
  have happlyB (i : S) : |kernelApply (rates.heatKernel t) f i| ≤ B * F :=
    (happly i).trans (((hrow i).tsum_le_tsum
      (fun j ↦ mul_le_mul_of_nonneg_right (hB i j) (abs_nonneg _)) (hf1.mul_left B)).trans_eq
        tsum_mul_left)
  have happly1 (i : S) : |kernelApply (rates.heatKernel t) f i| ≤ F :=
    (happly i).trans ((hrow i).tsum_le_tsum
      (fun j ↦ mul_le_of_le_one_left (abs_nonneg _) (rates.heatKernel_le_one t i j)) hf1)
  have hsum : Summable fun i ↦ |f i * kernelApply (rates.heatKernel t) f i| :=
    (hf1.mul_right F).of_nonneg_of_le (fun i ↦ abs_nonneg _) fun i ↦ by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (happly1 i) (abs_nonneg _)
  calc
    rates.heatForm f t ≤ |rates.heatForm f t| := le_abs_self _
    _ ≤ ∑' i, |f i * kernelApply (rates.heatKernel t) f i| := by
      rw [heatForm]
      have h := norm_tsum_le_tsum_norm (f := fun i ↦ f i * kernelApply (rates.heatKernel t) f i)
        (by simpa only [Real.norm_eq_abs] using hsum)
      simpa only [Real.norm_eq_abs] using h
    _ ≤ ∑' i, |f i| * (B * F) :=
      hsum.tsum_le_tsum (fun i ↦ by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (happlyB i) (abs_nonneg _)) (hf1.mul_right _)
    _ = B * F ^ 2 := by
      rw [tsum_mul_right]
      ring

/-- The quadratic form split at first order in time. -/
theorem heatForm_eq_split (rates : BoundedRates S) (hs : ∀ i j, rates.q i j = rates.q j i)
    {f : S → ℝ} (hf : Summable fun i ↦ f i ^ 2) (t : ℝ≥0) :
    rates.heatForm f t =
      Real.exp (-(rates.R * t)) * ∑' i, f i ^ 2 +
        Real.exp (-(rates.R * t)) * (rates.R * t) *
          (∑' i, f i ^ 2 - rates.energy f / rates.R) +
        ∑' i, f i * kernelApply (rates.heatRemainder t) f i := by
  have hp := (rates.isSymmKernel_p hs).summable_mul_kernelApply hf hf
  have hT := (rates.isSymmKernel_heatRemainder hs t).summable_mul_kernelApply hf hf
  rw [← rates.tsum_mul_kernelApply_p hs hf]
  calc
    rates.heatForm f t = ∑' i, (Real.exp (-(rates.R * t)) * f i ^ 2 +
        Real.exp (-(rates.R * t)) * (rates.R * t) * (f i * kernelApply rates.p f i) +
          f i * kernelApply (rates.heatRemainder t) f i) :=
      tsum_congr fun i ↦ by
        rw [rates.kernelApply_heatKernel_split hs t (abs_le_sqrt_tsum_sq hf) i]
        ring
    _ = _ := by
      rw [((hf.mul_left _).add (hp.mul_left _)).tsum_add hT,
        (hf.mul_left _).tsum_add (hp.mul_left _), tsum_mul_left, tsum_mul_left]

/-- Lower first-order bound for the quadratic form near time zero. -/
theorem heatForm_lower (rates : BoundedRates S) (hs : ∀ i j, rates.q i j = rates.q j i)
    {f : S → ℝ} (hf : Summable fun i ↦ f i ^ 2) (h : ℝ≥0) :
    ∑' i, f i ^ 2 - h * rates.energy f - 2 * rates.R ^ 2 * (∑' i, f i ^ 2) * h ^ 2 ≤
      rates.heatForm f h := by
  have hT := (rates.isSymmKernel_heatRemainder hs h).abs_tsum_mul_kernelApply_le
    one_sub_exp_neg_sub_nonneg hf
  rw [rates.heatForm_eq_split hs hf h]
  set r := ∑' i, f i ^ 2
  set E := rates.energy f
  set Q := ∑' i, f i * kernelApply (rates.heatRemainder h) f i
  set a := Real.exp (-(rates.R * h))
  have hE : 0 ≤ E := rates.energy_nonneg f
  have hr : 0 ≤ r := tsum_nonneg fun i ↦ sq_nonneg _
  have hh : (0 : ℝ) ≤ h := h.coe_nonneg
  have hx : 0 ≤ rates.R * h := mul_nonneg rates.R_pos.le hh
  have hexp : 1 - rates.R * h ≤ a := by linarith [Real.add_one_le_exp (-(rates.R * h))]
  have ha1 : a ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have h1 : (1 - (rates.R * h) ^ 2) * r ≤ a * (1 + rates.R * h) * r :=
    mul_le_mul_of_nonneg_right (by nlinarith) hr
  have hahE : a * (h * E) ≤ h * E := mul_le_of_le_one_left (mul_nonneg hh hE) ha1
  have hsplit : a * (rates.R * h) * (r - E / rates.R) = a * (rates.R * h) * r - a * (h * E) := by
    field_simp [rates.R_pos.ne']
  have hQ := (abs_le.mp hT).1
  rw [hsplit]
  nlinarith

/-- Upper first-order bound for the quadratic form near time zero. -/
theorem heatForm_upper (rates : BoundedRates S) (hs : ∀ i j, rates.q i j = rates.q j i)
    {f : S → ℝ} (hf : Summable fun i ↦ f i ^ 2) (h : ℝ≥0) :
    rates.heatForm f h ≤
      ∑' i, f i ^ 2 - h * rates.energy f + rates.R * h ^ 2 * rates.energy f := by
  have hT := (rates.isSymmKernel_heatRemainder hs h).abs_tsum_mul_kernelApply_le
    one_sub_exp_neg_sub_nonneg hf
  rw [rates.heatForm_eq_split hs hf h]
  set r := ∑' i, f i ^ 2
  set E := rates.energy f
  set Q := ∑' i, f i * kernelApply (rates.heatRemainder h) f i
  set a := Real.exp (-(rates.R * h))
  have hE : 0 ≤ E := rates.energy_nonneg f
  have hh : (0 : ℝ) ≤ h := h.coe_nonneg
  have hexp : 1 - rates.R * h ≤ a := by linarith [Real.add_one_le_exp (-(rates.R * h))]
  have hahE : (1 - rates.R * h) * (h * E) ≤ a * (h * E) :=
    mul_le_mul_of_nonneg_right hexp (mul_nonneg hh hE)
  have hsplit : a * (rates.R * h) * (r - E / rates.R) = a * (rates.R * h) * r - a * (h * E) := by
    field_simp [rates.R_pos.ne']
  have hQ := (abs_le.mp hT).2
  rw [hsplit]
  nlinarith

end

end LatticeProb.JumpChain.BoundedRates

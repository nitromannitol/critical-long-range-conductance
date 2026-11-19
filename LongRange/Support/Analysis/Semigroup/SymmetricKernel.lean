import LongRange.Support.Analysis.KernelPowersCS
import LongRange.Support.Analysis.WeightedSquareSeries

/-!
# Symmetric kernels acting on square-summable functions

A nonnegative symmetric kernel whose rows are summable with total mass at most `c` acts on real
functions by summation against counting measure. On square-summable functions this action is
symmetric for the counting inner product, multiplies the squared norm by at most `c ^ 2`, and
composes with the convolution of kernels. Cauchy–Schwarz for square-summable families is
included for the inner products that appear.
-/

namespace LatticeProb

noncomputable section

variable {X : Type*}

/-- Counting-measure action of a kernel on a real function. -/
def kernelApply (M : X → X → ℝ) (f : X → ℝ) (x : X) : ℝ := ∑' y, M x y * f y

/-- A nonnegative symmetric kernel whose rows are summable with total mass at most `c`. -/
structure IsSymmKernel (M : X → X → ℝ) (c : ℝ) : Prop where
  nonneg : ∀ x y, 0 ≤ M x y
  symm : ∀ x y, M x y = M y x
  summable : ∀ x, Summable (M x)
  tsum_le : ∀ x, ∑' y, M x y ≤ c

/-- A square-summable function is bounded by the square root of its squared norm. -/
theorem abs_le_sqrt_tsum_sq {f : X → ℝ} (hf : Summable fun x ↦ f x ^ 2) (x : X) :
    |f x| ≤ Real.sqrt (∑' y, f y ^ 2) :=
  Real.abs_le_sqrt (hf.le_tsum x fun y _ ↦ sq_nonneg (f y))

/-- The product of two square-summable functions is summable. -/
theorem summable_mul_of_summable_sq {f g : X → ℝ} (hf : Summable fun x ↦ f x ^ 2)
    (hg : Summable fun x ↦ g x ^ 2) : Summable fun x ↦ f x * g x := by
  apply ((hf.add hg).div_const 2).of_norm_bounded
  intro x
  rw [Real.norm_eq_abs, abs_mul]
  nlinarith [sq_nonneg (|f x| - |g x|), sq_abs (f x), sq_abs (g x)]

/-- Cauchy–Schwarz for square-summable real families. -/
theorem sq_tsum_mul_le_tsum_sq_mul {f g : X → ℝ} (hf : Summable fun x ↦ f x ^ 2)
    (hg : Summable fun x ↦ g x ^ 2) :
    (∑' x, f x * g x) ^ 2 ≤ (∑' x, f x ^ 2) * ∑' x, g x ^ 2 := by
  have habs : Summable fun x ↦ |f x| * |g x| := by
    simpa only [abs_mul] using (summable_mul_of_summable_sq hf hg).abs
  have hcs := tsum_mul_le_sqrt_mul_sqrt (fun x ↦ |f x|) (fun x ↦ |g x|)
    (fun x ↦ abs_nonneg _) (fun x ↦ abs_nonneg _) habs
    (by simpa only [sq_abs] using hf) (by simpa only [sq_abs] using hg)
  simp only [sq_abs] at hcs
  have htri : |∑' x, f x * g x| ≤ ∑' x, |f x| * |g x| := by
    have h := norm_tsum_le_tsum_norm (f := fun x ↦ f x * g x)
      (by simpa only [Real.norm_eq_abs, abs_mul] using habs)
    simpa only [Real.norm_eq_abs, abs_mul] using h
  have hA : 0 ≤ ∑' x, f x ^ 2 := tsum_nonneg fun x ↦ sq_nonneg _
  have hB : 0 ≤ ∑' x, g x ^ 2 := tsum_nonneg fun x ↦ sq_nonneg _
  calc
    (∑' x, f x * g x) ^ 2 = |∑' x, f x * g x| ^ 2 := (sq_abs _).symm
    _ ≤ (Real.sqrt (∑' x, f x ^ 2) * Real.sqrt (∑' x, g x ^ 2)) ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) (htri.trans hcs) 2
    _ = (∑' x, f x ^ 2) * ∑' x, g x ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hA, Real.sq_sqrt hB]

namespace IsSymmKernel

variable {M : X → X → ℝ} {c : ℝ}

/-- Each entry is at most the bound on the row masses. -/
theorem le (hM : IsSymmKernel M c) (x y : X) : M x y ≤ c :=
  ((hM.summable x).le_tsum y fun z _ ↦ hM.nonneg x z).trans (hM.tsum_le x)

/-- The row bound is nonnegative as soon as there is a row. -/
theorem nonneg_bound (hM : IsSymmKernel M c) (x : X) : 0 ≤ c :=
  (tsum_nonneg (hM.nonneg x)).trans (hM.tsum_le x)

/-- A bounded function is summable against every row. -/
theorem summable_mul_of_abs_le (hM : IsSymmKernel M c) {f : X → ℝ} {C : ℝ}
    (hf : ∀ y, |f y| ≤ C) (x : X) : Summable fun y ↦ M x y * f y := by
  apply ((hM.summable x).mul_right C).of_norm_bounded
  intro y
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hM.nonneg x y)]
  exact mul_le_mul_of_nonneg_left (hf y) (hM.nonneg x y)

/-- A square-summable function is summable against every row. -/
theorem summable_mul (hM : IsSymmKernel M c) {f : X → ℝ}
    (hf : Summable fun x ↦ f x ^ 2) (x : X) : Summable fun y ↦ M x y * f y :=
  hM.summable_mul_of_abs_le (abs_le_sqrt_tsum_sq hf) x

/-- The square of a square-summable function is summable against every row. -/
theorem summable_mul_sq (hM : IsSymmKernel M c) {f : X → ℝ}
    (hf : Summable fun x ↦ f x ^ 2) (x : X) : Summable fun y ↦ M x y * f y ^ 2 := by
  refine hM.summable_mul_of_abs_le (f := fun y ↦ f y ^ 2) (C := ∑' y, f y ^ 2) (fun y ↦ ?_) x
  rw [abs_of_nonneg (sq_nonneg _)]
  exact hf.le_tsum y fun z _ ↦ sq_nonneg (f z)

/-- The action of the kernel on a bounded function is bounded. -/
theorem abs_kernelApply_le (hM : IsSymmKernel M c) {f : X → ℝ} {C : ℝ}
    (hf : ∀ y, |f y| ≤ C) (x : X) : |kernelApply M f x| ≤ c * C := by
  have hC : 0 ≤ C := (abs_nonneg _).trans (hf x)
  have hs := hM.summable_mul_of_abs_le hf x
  calc
    |kernelApply M f x| ≤ ∑' y, |M x y * f y| := by
      rw [kernelApply]
      have h := norm_tsum_le_tsum_norm (f := fun y ↦ M x y * f y)
        (by simpa only [Real.norm_eq_abs] using hs.abs)
      simpa only [Real.norm_eq_abs] using h
    _ ≤ ∑' y, M x y * C := by
      refine hs.abs.tsum_le_tsum (fun y ↦ ?_) ((hM.summable x).mul_right C)
      rw [abs_mul, abs_of_nonneg (hM.nonneg x y)]
      exact mul_le_mul_of_nonneg_left (hf y) (hM.nonneg x y)
    _ = (∑' y, M x y) * C := tsum_mul_right
    _ ≤ c * C := mul_le_mul_of_nonneg_right (hM.tsum_le x) hC

/-- Joint summability of the kernel against the square of the first variable. -/
theorem summable_prod_mul_sq_left (hM : IsSymmKernel M c) {f : X → ℝ}
    (hf : Summable fun x ↦ f x ^ 2) :
    Summable fun p : X × X ↦ M p.1 p.2 * f p.1 ^ 2 := by
  refine (summable_prod_of_nonneg (f := fun p : X × X ↦ M p.1 p.2 * f p.1 ^ 2)
    fun p ↦ mul_nonneg (hM.nonneg _ _) (sq_nonneg _)).2
    ⟨fun x ↦ (hM.summable x).mul_right (f x ^ 2), ?_⟩
  refine (hf.mul_left c).of_nonneg_of_le
    (fun x ↦ tsum_nonneg fun y ↦ mul_nonneg (hM.nonneg _ _) (sq_nonneg _)) fun x ↦ ?_
  change ∑' y, M x y * f x ^ 2 ≤ c * f x ^ 2
  rw [tsum_mul_right]
  exact mul_le_mul_of_nonneg_right (hM.tsum_le x) (sq_nonneg _)

/-- Joint summability of the kernel against the square of the second variable. -/
theorem summable_prod_mul_sq_right (hM : IsSymmKernel M c) {f : X → ℝ}
    (hf : Summable fun x ↦ f x ^ 2) :
    Summable fun p : X × X ↦ M p.1 p.2 * f p.2 ^ 2 := by
  refine (hM.summable_prod_mul_sq_left hf).prod_symm.congr fun p ↦ ?_
  simp only [Prod.fst_swap, Prod.snd_swap]
  rw [hM.symm]

/-- Symmetry moves the square onto the summation variable of the row mass. -/
theorem tsum_tsum_mul_sq_right (hM : IsSymmKernel M c) {f : X → ℝ}
    (hf : Summable fun x ↦ f x ^ 2) :
    ∑' x, ∑' y, M x y * f y ^ 2 = ∑' x, (∑' y, M x y) * f x ^ 2 := by
  calc
    ∑' x, ∑' y, M x y * f y ^ 2 = ∑' p : X × X, M p.1 p.2 * f p.2 ^ 2 :=
      ((hM.summable_prod_mul_sq_right hf).tsum_prod).symm
    _ = ∑' p : X × X, M p.1 p.2 * f p.1 ^ 2 := by
      rw [← (Equiv.prodComm X X).tsum_eq]
      refine tsum_congr fun p ↦ ?_
      simp only [Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap]
      rw [hM.symm]
    _ = ∑' x, ∑' y, M x y * f x ^ 2 := (hM.summable_prod_mul_sq_left hf).tsum_prod
    _ = ∑' x, (∑' y, M x y) * f x ^ 2 := tsum_congr fun x ↦ tsum_mul_right

/-- Weighted Cauchy–Schwarz along one row. -/
theorem sq_kernelApply_le (hM : IsSymmKernel M c) {f : X → ℝ}
    (hf : Summable fun x ↦ f x ^ 2) (x : X) :
    kernelApply M f x ^ 2 ≤ c * ∑' y, M x y * f y ^ 2 :=
  (LatticeProb.sq_tsum_mul_le (hM.nonneg x) (hM.summable x) (hM.summable_mul hf x)
    (hM.summable_mul_sq hf x)).trans (mul_le_mul_of_nonneg_right (hM.tsum_le x)
      (tsum_nonneg fun y ↦ mul_nonneg (hM.nonneg x y) (sq_nonneg _)))

/-- The action of the kernel preserves square summability. -/
theorem summable_kernelApply_sq (hM : IsSymmKernel M c) {f : X → ℝ}
    (hf : Summable fun x ↦ f x ^ 2) : Summable fun x ↦ kernelApply M f x ^ 2 :=
  (((hM.summable_prod_mul_sq_right hf).prod).mul_left c).of_nonneg_of_le
    (fun _ ↦ sq_nonneg _) (hM.sq_kernelApply_le hf)

/-- The action of the kernel multiplies the squared norm by at most `c ^ 2`. -/
theorem tsum_kernelApply_sq_le (hM : IsSymmKernel M c) (hc : 0 ≤ c) {f : X → ℝ}
    (hf : Summable fun x ↦ f x ^ 2) :
    ∑' x, kernelApply M f x ^ 2 ≤ c ^ 2 * ∑' x, f x ^ 2 := by
  have hrow : Summable fun x ↦ (∑' y, M x y) * f x ^ 2 :=
    (hf.mul_left c).of_nonneg_of_le
      (fun x ↦ mul_nonneg (tsum_nonneg (hM.nonneg x)) (sq_nonneg _))
      fun x ↦ mul_le_mul_of_nonneg_right (hM.tsum_le x) (sq_nonneg _)
  calc
    ∑' x, kernelApply M f x ^ 2 ≤ ∑' x, c * ∑' y, M x y * f y ^ 2 :=
      (hM.summable_kernelApply_sq hf).tsum_le_tsum (hM.sq_kernelApply_le hf)
        (((hM.summable_prod_mul_sq_right hf).prod).mul_left c)
    _ = c * ∑' x, (∑' y, M x y) * f x ^ 2 := by
      rw [tsum_mul_left, hM.tsum_tsum_mul_sq_right hf]
    _ ≤ c * ∑' x, c * f x ^ 2 :=
      mul_le_mul_of_nonneg_left (hrow.tsum_le_tsum
        (fun x ↦ mul_le_mul_of_nonneg_right (hM.tsum_le x) (sq_nonneg _))
        (hf.mul_left c)) hc
    _ = c ^ 2 * ∑' x, f x ^ 2 := by
      rw [tsum_mul_left]
      ring

/-- The quadratic form of the kernel is bounded by `c` times the squared norm. -/
theorem abs_tsum_mul_kernelApply_le (hM : IsSymmKernel M c) (hc : 0 ≤ c) {f : X → ℝ}
    (hf : Summable fun x ↦ f x ^ 2) :
    |∑' x, f x * kernelApply M f x| ≤ c * ∑' x, f x ^ 2 := by
  have hr : 0 ≤ ∑' x, f x ^ 2 := tsum_nonneg fun x ↦ sq_nonneg _
  refine abs_le_of_sq_le_sq ?_ (mul_nonneg hc hr)
  calc
    (∑' x, f x * kernelApply M f x) ^ 2 ≤ (∑' x, f x ^ 2) * ∑' x, kernelApply M f x ^ 2 :=
      sq_tsum_mul_le_tsum_sq_mul hf (hM.summable_kernelApply_sq hf)
    _ ≤ (∑' x, f x ^ 2) * (c ^ 2 * ∑' x, f x ^ 2) :=
      mul_le_mul_of_nonneg_left (hM.tsum_kernelApply_sq_le hc hf) hr
    _ = (c * ∑' x, f x ^ 2) ^ 2 := by ring

/-- The counting inner product of a square-summable function with the action is summable. -/
theorem summable_mul_kernelApply (hM : IsSymmKernel M c) {f g : X → ℝ}
    (hf : Summable fun x ↦ f x ^ 2) (hg : Summable fun x ↦ g x ^ 2) :
    Summable fun x ↦ g x * kernelApply M f x :=
  summable_mul_of_summable_sq hg (hM.summable_kernelApply_sq hf)

/-- The bilinear expression of the inner product is jointly summable. -/
theorem summable_prod_mul_kernel (hM : IsSymmKernel M c) {f g : X → ℝ}
    (hf : Summable fun x ↦ f x ^ 2) (hg : Summable fun x ↦ g x ^ 2) :
    Summable fun p : X × X ↦ g p.1 * (M p.1 p.2 * f p.2) := by
  refine (((hM.summable_prod_mul_sq_left hg).add
    (hM.summable_prod_mul_sq_right hf)).div_const 2).of_norm_bounded fun p ↦ ?_
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (hM.nonneg _ _)]
  have hm := hM.nonneg p.1 p.2
  nlinarith [mul_nonneg hm (sq_nonneg (|g p.1| - |f p.2|)), sq_abs (g p.1), sq_abs (f p.2)]

/-- The inner product with the action as a sum over pairs. -/
theorem tsum_mul_kernelApply_eq_tsum_prod (hM : IsSymmKernel M c) {f g : X → ℝ}
    (hf : Summable fun x ↦ f x ^ 2) (hg : Summable fun x ↦ g x ^ 2) :
    ∑' x, g x * kernelApply M f x = ∑' p : X × X, g p.1 * (M p.1 p.2 * f p.2) := by
  rw [(hM.summable_prod_mul_kernel hf hg).tsum_prod]
  exact tsum_congr fun x ↦ tsum_mul_left.symm

/-- The action of a symmetric kernel is symmetric for the counting inner product. -/
theorem tsum_mul_kernelApply_comm (hM : IsSymmKernel M c) {f g : X → ℝ}
    (hf : Summable fun x ↦ f x ^ 2) (hg : Summable fun x ↦ g x ^ 2) :
    ∑' x, g x * kernelApply M f x = ∑' x, kernelApply M g x * f x := by
  calc
    ∑' x, g x * kernelApply M f x = ∑' p : X × X, g p.1 * (M p.1 p.2 * f p.2) :=
      hM.tsum_mul_kernelApply_eq_tsum_prod hf hg
    _ = ∑' p : X × X, f p.1 * (M p.1 p.2 * g p.2) := by
      rw [← (Equiv.prodComm X X).tsum_eq (fun p : X × X ↦ f p.1 * (M p.1 p.2 * g p.2))]
      refine tsum_congr fun p ↦ ?_
      simp only [Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap]
      rw [hM.symm p.2 p.1]
      ring
    _ = ∑' x, f x * kernelApply M g x := (hM.tsum_mul_kernelApply_eq_tsum_prod hg hf).symm
    _ = ∑' x, kernelApply M g x * f x := tsum_congr fun x ↦ mul_comm _ _

/-- Acting twice is acting by the convolution, on bounded functions. -/
theorem kernelApply_kernelApply {N : X → X → ℝ} {c' : ℝ} (hM : IsSymmKernel M c)
    (hN : IsSymmKernel N c') {f : X → ℝ} {C : ℝ} (hf : ∀ y, |f y| ≤ C) (x : X) :
    kernelApply M (kernelApply N f) x = kernelApply (kernelComp M N) f x := by
  have hpair : Summable fun p : X × X ↦ M x p.1 * N p.1 p.2 := by
    refine (summable_prod_of_nonneg (f := fun p : X × X ↦ M x p.1 * N p.1 p.2)
      fun p ↦ mul_nonneg (hM.nonneg _ _) (hN.nonneg _ _)).2
      ⟨fun y ↦ (hN.summable y).mul_left (M x y), ?_⟩
    refine ((hM.summable x).mul_right c').of_nonneg_of_le
      (fun y ↦ tsum_nonneg fun z ↦ mul_nonneg (hM.nonneg _ _) (hN.nonneg _ _)) fun y ↦ ?_
    change ∑' z, M x y * N y z ≤ M x y * c'
    rw [tsum_mul_left]
    exact mul_le_mul_of_nonneg_left (hN.tsum_le y) (hM.nonneg x y)
  have hs : Summable (Function.uncurry fun y z ↦ M x y * (N y z * f z)) := by
    refine (hpair.mul_right C).of_norm_bounded fun p ↦ ?_
    change ‖M x p.1 * (N p.1 p.2 * f p.2)‖ ≤ M x p.1 * N p.1 p.2 * C
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (hM.nonneg _ _),
      abs_of_nonneg (hN.nonneg _ _), mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hf _) (hN.nonneg _ _))
      (hM.nonneg _ _)
  calc
    kernelApply M (kernelApply N f) x = ∑' y, ∑' z, M x y * (N y z * f z) :=
      tsum_congr fun y ↦ tsum_mul_left.symm
    _ = ∑' z, ∑' y, M x y * (N y z * f z) := hs.tsum_comm.symm
    _ = kernelApply (kernelComp M N) f x := by
      refine tsum_congr fun z ↦ ?_
      rw [kernelComp, ← tsum_mul_right]
      exact tsum_congr fun y ↦ by ring

end IsSymmKernel

end

end LatticeProb

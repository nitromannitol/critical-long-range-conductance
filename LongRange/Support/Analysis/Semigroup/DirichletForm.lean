import LongRange.Support.Analysis.Semigroup.SymmetricKernel
import LongRange.Support.Prob.JumpChain.Generator

/-!
# The jump generator and its Dirichlet form

For symmetric bounded rates, the jump generator `L f (i) = ∑ⱼ q i j (f j - f i)` and the
Dirichlet form `E(f, g) = ½ ∑ᵢ ∑ⱼ q i j (f j - f i) (g j - g i)` satisfy Green's formula
`∑ᵢ g i L f (i) = -E(f, g)` on square-summable functions. The uniformized matrix acts as the
identity plus `L / R`, so its quadratic form is the squared norm minus `E(f, f) / R`.
-/

namespace LatticeProb.JumpChain.BoundedRates

noncomputable section

variable {S : Type*}

/-- The jump generator acting on real functions. -/
def generator (rates : BoundedRates S) (f : S → ℝ) (i : S) : ℝ :=
  ∑' j, rates.q i j * (f j - f i)

/-- The Dirichlet energy with the one-half normalization. -/
def energy (rates : BoundedRates S) (f : S → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑' i, ∑' j, rates.q i j * (f j - f i) ^ 2

/-- The Dirichlet energy is nonnegative. -/
theorem energy_nonneg (rates : BoundedRates S) (f : S → ℝ) : 0 ≤ rates.energy f :=
  mul_nonneg (by norm_num) (tsum_nonneg fun i ↦ tsum_nonneg fun j ↦
    mul_nonneg (rates.q_nonneg i j) (sq_nonneg _))

/-- Symmetric rates form a symmetric kernel with row masses at most `R`. -/
theorem isSymmKernel_q (rates : BoundedRates S) (hs : ∀ i j, rates.q i j = rates.q j i) :
    IsSymmKernel rates.q rates.R where
  nonneg := rates.q_nonneg
  symm := hs
  summable := rates.summable
  tsum_le := rates.total_le

/-- A summable majorant for the pair sums in Green's formula. -/
theorem summable_prod_q_mul_sq_add (rates : BoundedRates S)
    (hs : ∀ i j, rates.q i j = rates.q j i) {f g : S → ℝ}
    (hf : Summable fun i ↦ f i ^ 2) (hg : Summable fun i ↦ g i ^ 2) :
    Summable fun p : S × S ↦
      rates.q p.1 p.2 * (f p.1 ^ 2 + f p.2 ^ 2 + g p.1 ^ 2 + g p.2 ^ 2) := by
  have hq := rates.isSymmKernel_q hs
  refine ((((hq.summable_prod_mul_sq_left hf).add (hq.summable_prod_mul_sq_right hf)).add
    (hq.summable_prod_mul_sq_left hg)).add (hq.summable_prod_mul_sq_right hg)).congr fun p ↦ ?_
  ring

/-- The pair summand of the generator side of Green's formula is summable. -/
theorem summable_prod_mul_generator (rates : BoundedRates S)
    (hs : ∀ i j, rates.q i j = rates.q j i) {f g : S → ℝ}
    (hf : Summable fun i ↦ f i ^ 2) (hg : Summable fun i ↦ g i ^ 2) :
    Summable fun p : S × S ↦ g p.1 * (rates.q p.1 p.2 * (f p.2 - f p.1)) := by
  refine (rates.summable_prod_q_mul_sq_add hs hf hg).of_norm_bounded fun p ↦ ?_
  have hq := rates.q_nonneg p.1 p.2
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hq]
  have hsub := abs_sub (f p.2) (f p.1)
  have h1 : |g p.1| * |f p.2 - f p.1| ≤ f p.1 ^ 2 + f p.2 ^ 2 + g p.1 ^ 2 + g p.2 ^ 2 := by
    nlinarith [sq_nonneg (|g p.1| - |f p.2|), sq_nonneg (|g p.1| - |f p.1|), sq_abs (g p.1),
      sq_abs (f p.1), sq_abs (f p.2), abs_nonneg (g p.1), sq_nonneg (g p.2)]
  calc
    |g p.1| * (rates.q p.1 p.2 * |f p.2 - f p.1|) =
        rates.q p.1 p.2 * (|g p.1| * |f p.2 - f p.1|) := by ring
    _ ≤ rates.q p.1 p.2 * (f p.1 ^ 2 + f p.2 ^ 2 + g p.1 ^ 2 + g p.2 ^ 2) :=
      mul_le_mul_of_nonneg_left h1 hq

/-- The pair summand of the form side of Green's formula is summable. -/
theorem summable_prod_mul_form (rates : BoundedRates S)
    (hs : ∀ i j, rates.q i j = rates.q j i) {f g : S → ℝ}
    (hf : Summable fun i ↦ f i ^ 2) (hg : Summable fun i ↦ g i ^ 2) :
    Summable fun p : S × S ↦ rates.q p.1 p.2 * ((f p.2 - f p.1) * (g p.2 - g p.1)) := by
  refine ((rates.summable_prod_q_mul_sq_add hs hf hg).mul_left 2).of_norm_bounded fun p ↦ ?_
  have hq := rates.q_nonneg p.1 p.2
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hq]
  have h1 : |f p.2 - f p.1| * |g p.2 - g p.1| ≤
      2 * (f p.1 ^ 2 + f p.2 ^ 2 + g p.1 ^ 2 + g p.2 ^ 2) := by
    have ha : |f p.2 - f p.1| * |g p.2 - g p.1| ≤
        (|f p.2 - f p.1| ^ 2 + |g p.2 - g p.1| ^ 2) / 2 := by
      nlinarith [sq_nonneg (|f p.2 - f p.1| - |g p.2 - g p.1|)]
    rw [sq_abs, sq_abs] at ha
    nlinarith [sq_nonneg (f p.2 + f p.1), sq_nonneg (g p.2 + g p.1)]
  calc
    rates.q p.1 p.2 * (|f p.2 - f p.1| * |g p.2 - g p.1|) ≤
        rates.q p.1 p.2 * (2 * (f p.1 ^ 2 + f p.2 ^ 2 + g p.1 ^ 2 + g p.2 ^ 2)) :=
      mul_le_mul_of_nonneg_left h1 hq
    _ = 2 * (rates.q p.1 p.2 * (f p.1 ^ 2 + f p.2 ^ 2 + g p.1 ^ 2 + g p.2 ^ 2)) := by ring

/-- The inner product with the generator is summable on square-summable functions. -/
theorem summable_mul_generator (rates : BoundedRates S)
    (hs : ∀ i j, rates.q i j = rates.q j i) {f g : S → ℝ}
    (hf : Summable fun i ↦ f i ^ 2) (hg : Summable fun i ↦ g i ^ 2) :
    Summable fun i ↦ g i * rates.generator f i :=
  (rates.summable_prod_mul_generator hs hf hg).prod.congr fun i ↦ by
    change ∑' j, g i * (rates.q i j * (f j - f i)) = g i * rates.generator f i
    rw [tsum_mul_left, generator]

/-- **Green's formula** for symmetric bounded rates on square-summable functions. -/
theorem tsum_mul_generator (rates : BoundedRates S)
    (hs : ∀ i j, rates.q i j = rates.q j i) {f g : S → ℝ}
    (hf : Summable fun i ↦ f i ^ 2) (hg : Summable fun i ↦ g i ^ 2) :
    ∑' i, g i * rates.generator f i =
      -((1 / 2 : ℝ) * ∑' i, ∑' j, rates.q i j * ((f j - f i) * (g j - g i))) := by
  have hA := rates.summable_prod_mul_generator hs hf hg
  have hB := rates.summable_prod_mul_form hs hf hg
  have hgen : ∑' i, g i * rates.generator f i =
      ∑' p : S × S, g p.1 * (rates.q p.1 p.2 * (f p.2 - f p.1)) := by
    rw [hA.tsum_prod]
    exact tsum_congr fun i ↦ tsum_mul_left.symm
  have hswap : ∑' p : S × S, g p.1 * (rates.q p.1 p.2 * (f p.2 - f p.1)) =
      ∑' p : S × S, g p.2 * (rates.q p.1 p.2 * (f p.1 - f p.2)) := by
    rw [← (Equiv.prodComm S S).tsum_eq
      (fun p : S × S ↦ g p.2 * (rates.q p.1 p.2 * (f p.1 - f p.2)))]
    refine tsum_congr fun p ↦ ?_
    simp only [Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap]
    rw [hs p.2 p.1]
  have hA' : Summable fun p : S × S ↦ g p.2 * (rates.q p.1 p.2 * (f p.1 - f p.2)) :=
    hA.prod_symm.congr fun p ↦ by
      simp only [Prod.fst_swap, Prod.snd_swap]
      rw [hs p.2 p.1]
  have hsum : ∑' p : S × S, g p.1 * (rates.q p.1 p.2 * (f p.2 - f p.1)) +
      ∑' p : S × S, g p.2 * (rates.q p.1 p.2 * (f p.1 - f p.2)) =
      -∑' p : S × S, rates.q p.1 p.2 * ((f p.2 - f p.1) * (g p.2 - g p.1)) := by
    rw [← hA.tsum_add hA', ← tsum_neg]
    exact tsum_congr fun p ↦ by ring
  rw [hgen, ← hB.tsum_prod]
  rw [← hswap] at hsum
  linarith

/-- Green's formula on the diagonal: the generator quadratic form is minus the energy. -/
theorem tsum_mul_generator_self (rates : BoundedRates S)
    (hs : ∀ i j, rates.q i j = rates.q j i) {f : S → ℝ}
    (hf : Summable fun i ↦ f i ^ 2) :
    ∑' i, f i * rates.generator f i = -rates.energy f := by
  rw [rates.tsum_mul_generator hs hf hf, energy]
  congr 2
  exact tsum_congr fun i ↦ tsum_congr fun j ↦ by ring

/-- The uniformized matrix acts as the identity plus the generator divided by `R`. -/
theorem kernelApply_p (rates : BoundedRates S) {f : S → ℝ} {C : ℝ}
    (hf : ∀ j, |f j| ≤ C) (i : S) :
    kernelApply rates.p f i = f i + rates.generator f i / rates.R := by
  have h := rates.uniformized_generator i f hf
  rw [kernelApply, generator, ← h]
  field_simp [rates.R_pos.ne']
  ring

/-- The quadratic form of the uniformized matrix is the squared norm minus `E(f) / R`. -/
theorem tsum_mul_kernelApply_p (rates : BoundedRates S)
    (hs : ∀ i j, rates.q i j = rates.q j i) {f : S → ℝ}
    (hf : Summable fun i ↦ f i ^ 2) :
    ∑' i, f i * kernelApply rates.p f i = ∑' i, f i ^ 2 - rates.energy f / rates.R := by
  have hgen := rates.summable_mul_generator hs hf hf
  calc
    ∑' i, f i * kernelApply rates.p f i =
        ∑' i, (f i ^ 2 + (f i * rates.generator f i) / rates.R) := by
      refine tsum_congr fun i ↦ ?_
      rw [rates.kernelApply_p (abs_le_sqrt_tsum_sq hf) i]
      ring
    _ = ∑' i, f i ^ 2 + (∑' i, f i * rates.generator f i) / rates.R := by
      rw [hf.tsum_add (hgen.div_const _), tsum_div_const]
    _ = ∑' i, f i ^ 2 - rates.energy f / rates.R := by
      rw [rates.tsum_mul_generator_self hs hf]
      ring

end

end LatticeProb.JumpChain.BoundedRates

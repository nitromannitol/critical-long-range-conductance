import LongRange.TwoScale.ResidualDefs
import LongRange.Calculus.Summability

/-!
# Splitting the smooth error

The background conductance separates the smooth error into a deterministic Taylor defect
and a conductance fluctuation. The homogenized equation cancels the second-order term.
-/

namespace LongRange

open LatticeProb LatticeProb.Euclidean.Lattice
open scoped Topology

noncomputable section

variable {d : ℕ}

/-- The smooth error splits at any background coefficient satisfying the homogenized PDE. -/
theorem smoothError_eq_split (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε) {lam : ℝ}
    (hlam : 0 < lam) {a : Edge d → ℝ} (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹)
    {U : Set (Fin d → ℝ)} (hUo : IsOpen U) (μ m : ℝ)
    {f v ū : (Fin d → ℝ) → ℝ} (hv : Set.EqOn v ū U)
    (hpde : ∀ x ∈ U, μ * ū x - m / (2 * d) * Elliptic.laplacian ū x = f x)
    {B₀ B₁ : ℝ} (hB₀ : ∀ x, |v x| ≤ B₀) (hB₁ : ∀ x, ‖fderiv ℝ v x‖ ≤ B₁)
    {q : Site d} (hq : q ∈ latticeSet ε U) :
    smoothError ε a μ f v q =
      m * (ε ^ d / kappa d ε * ∑' w : Site d, jumpKernel (physical ε w) *
          smoothRemainder v (physical ε q) (physical ε w) -
        Elliptic.laplacian v (physical ε q) / (2 * d)) +
      smoothFluctuation ε a m v q := by
  classical
  have hx : physical ε q ∈ U := hq
  have heq : v =ᶠ[𝓝 (physical ε q)] ū :=
    Filter.eventuallyEq_of_mem (hUo.mem_nhds hx) hv
  have hder := (heq.iteratedFDeriv (𝕜 := ℝ) 2).eq_of_nhds
  have hlap : Elliptic.laplacian v (physical ε q) =
      Elliptic.laplacian ū (physical ε q) := by
    unfold Elliptic.laplacian Elliptic.secondPartial
    rw [hder]
  have hp : f (physical ε q) - μ * v (physical ε q) =
      -(m / (2 * d)) * Elliptic.laplacian v (physical ε q) := by
    rw [hv hx, hlap, ← hpde _ hx]
    ring
  let F := fun w : Site d => jumpKernel (physical ε w) *
    smoothRemainder v (physical ε q) (physical ε w)
  let A := fun w : Site d => if hw : w = 0 then 0 else
    a (edgeAdd q w hw) * jumpKernel (physical ε w) *
      smoothRemainder v (physical ε q) (physical ε w)
  have hdom : Summable (fun w : Site d =>
      2 * B₀ * jumpKernel (physical ε w) +
        B₁ * (jumpKernel (physical ε w) * radius (physical ε w))) :=
    ((summable_jumpKernel hd hε).mul_left (2 * B₀)).add
      ((summable_jumpKernel_firstMoment hd hε).mul_left B₁)
  have hbound (w : Site d) : ‖F w‖ ≤
      2 * B₀ * jumpKernel (physical ε w) +
        B₁ * (jumpKernel (physical ε w) * radius (physical ε w)) := by
    dsimp only [F]
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (jumpKernel_nonneg _)]
    exact (mul_le_mul_of_nonneg_left
      (TaylorHolder.remainder_le_linear hB₀ hB₁ _ _) (jumpKernel_nonneg _)).trans_eq
        (by ring)
  have hF : Summable F := hdom.of_norm_bounded hbound
  have hA : Summable A := (hdom.mul_left lam⁻¹).of_norm_bounded (fun w => by
    by_cases hw : w = 0
    · simp only [A, dif_pos hw, norm_zero]
      exact mul_nonneg (inv_nonneg.mpr hlam.le) ((norm_nonneg (F w)).trans (hbound w))
    · have habs : |a (edgeAdd q w hw)| ≤ lam⁻¹ := by
        rw [abs_of_nonneg (hlam.le.trans (ha _).1)]
        exact (ha _).2
      simp only [A, dif_neg hw]
      calc
        _ = |a (edgeAdd q w hw)| * ‖F w‖ := by
          simp only [F, Real.norm_eq_abs, abs_mul, mul_assoc]
        _ ≤ lam⁻¹ * _ := mul_le_mul habs (hbound w) (norm_nonneg _)
          (inv_nonneg.mpr hlam.le))
  have hzero : F 0 = 0 := by
    have hz : physical ε (0 : Site d) = 0 := by
      ext i
      simp only [physical, Pi.zero_apply, Int.cast_zero, mul_zero]
    simp only [F, hz, jumpKernel_zero, zero_mul]
  have hfluct : (fun w : Site d => if hw : w = 0 then 0 else
      (a (edgeAdd q w hw) - m) * jumpKernel (physical ε w) *
        smoothRemainder v (physical ε q) (physical ε w)) =
      (fun w => A w - m * F w) := by
    funext w
    by_cases hw : w = 0
    · subst w
      simp only [A, dif_pos rfl, hzero, mul_zero, sub_zero, dite_true]
    · simp only [dif_neg hw, A, F]
      ring
  unfold smoothError smoothFluctuation
  rw [hp, hfluct, hA.tsum_sub (hF.mul_left m), tsum_mul_left]
  change _ + ε ^ d / kappa d ε * ∑' w, A w = _
  ring

end
end LongRange

import Mathlib

/-!
# An algebra of tensor products that separates points

For `k` observation times, the linear combinations of the products
`x ↦ ∏_j (c_j + ψ_j(x_j))`, with constants `c_j` and `ψ_j ∈ C_c^∞(ℝ^d)`, form a star subalgebra of
the bounded continuous functions on `(ℝ^d)^k` that separates points. The weak convergence of
probability measures on `(ℝ^d)^k` follows from the convergence of the integrals of these products
(Stone–Weierstrass in the form of `ProbabilityMeasure.tendsto_of_tight_of_separatesPoints`).
-/

namespace LongRangeHeat

open Set BoundedContinuousFunction
open scoped ContDiff BoundedContinuousFunction

noncomputable section

variable {d k : ℕ}

/-- The test functions: `C_c^∞(ℝ^d)`. -/
def IsTestFunction (ψ : (Fin d → ℝ) → ℝ) : Prop :=
  ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ

theorem IsTestFunction.zero : IsTestFunction (0 : (Fin d → ℝ) → ℝ) :=
  ⟨contDiff_const, HasCompactSupport.zero⟩

theorem IsTestFunction.add {ψ φ : (Fin d → ℝ) → ℝ} (hψ : IsTestFunction ψ)
    (hφ : IsTestFunction φ) : IsTestFunction (ψ + φ) :=
  ⟨hψ.1.add hφ.1, hψ.2.add hφ.2⟩

theorem IsTestFunction.smul {ψ : (Fin d → ℝ) → ℝ} (hψ : IsTestFunction ψ) (c : ℝ) :
    IsTestFunction (c • ψ) :=
  ⟨hψ.1.const_smul c, hψ.2.smul_left⟩

theorem IsTestFunction.mul {ψ φ : (Fin d → ℝ) → ℝ} (hψ : IsTestFunction ψ)
    (hφ : IsTestFunction φ) : IsTestFunction (ψ * φ) :=
  ⟨hψ.1.mul hφ.1, hψ.2.mul_right⟩

/-- Two points of `ℝ^d` are separated by a test function. -/
theorem exists_testFunction_separating {p q : Fin d → ℝ} (h : p ≠ q) :
    ∃ ψ : (Fin d → ℝ) → ℝ, IsTestFunction ψ ∧ ψ p ≠ ψ q := by
  have hr : 0 < dist q p := dist_pos.2 h.symm
  let f : ContDiffBump p := ⟨dist q p / 2, dist q p, by positivity, by linarith⟩
  refine ⟨f, ⟨f.contDiff, f.hasCompactSupport⟩, ?_⟩
  rw [f.one_of_mem_closedBall (Metric.mem_closedBall_self f.rIn_pos.le),
    f.zero_of_le_dist (le_of_eq rfl)]
  norm_num

/-- The product `x ↦ ∏_j (c_j + ψ_j(x_j))` on `(ℝ^d)^k`. -/
def tensorFun (c : Fin k → ℝ) (ψ : Fin k → (Fin d → ℝ) → ℝ)
    (x : Fin k → EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∏ j, (c j + ψ j (WithLp.ofLp (x j)))

/-- The linear combinations of the products `tensorFun c ψ` with test functions `ψ_j`. -/
def tensorSpan (d k : ℕ) : Submodule ℝ ((Fin k → EuclideanSpace ℝ (Fin d)) → ℝ) :=
  Submodule.span ℝ {F | ∃ (c : Fin k → ℝ) (ψ : Fin k → (Fin d → ℝ) → ℝ),
    (∀ j, IsTestFunction (ψ j)) ∧ F = tensorFun c ψ}

theorem tensorFun_mem (c : Fin k → ℝ) {ψ : Fin k → (Fin d → ℝ) → ℝ}
    (hψ : ∀ j, IsTestFunction (ψ j)) : tensorFun c ψ ∈ tensorSpan d k :=
  Submodule.subset_span ⟨c, ψ, hψ, rfl⟩

theorem tensorFun_mul (c c' : Fin k → ℝ) (ψ ψ' : Fin k → (Fin d → ℝ) → ℝ) :
    tensorFun c ψ * tensorFun c' ψ' =
      tensorFun (c * c') (fun j => c j • ψ' j + c' j • ψ j + ψ j * ψ' j) := by
  funext x
  simp only [tensorFun, Pi.mul_apply, ← Finset.prod_mul_distrib, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul]
  refine Finset.prod_congr rfl fun j _ => ?_
  ring

theorem mul_mem_tensorSpan {F G : (Fin k → EuclideanSpace ℝ (Fin d)) → ℝ}
    (hF : F ∈ tensorSpan d k) (hG : G ∈ tensorSpan d k) : F * G ∈ tensorSpan d k := by
  refine Submodule.span_induction (p := fun F _ => F * G ∈ tensorSpan d k) ?_ ?_ ?_ ?_ hF
  · rintro _ ⟨c, ψ, hψ, rfl⟩
    refine Submodule.span_induction (p := fun G _ => tensorFun c ψ * G ∈ tensorSpan d k) ?_ ?_ ?_ ?_
      hG
    · rintro _ ⟨c', ψ', hψ', rfl⟩
      rw [tensorFun_mul]
      exact tensorFun_mem _ fun j =>
        (((hψ' j).smul _).add ((hψ j).smul _)).add ((hψ j).mul (hψ' j))
    · simp
    · intro G₁ G₂ _ _ h₁ h₂
      rw [mul_add]
      exact add_mem h₁ h₂
    · intro r G₁ _ h₁
      rw [mul_smul_comm]
      exact Submodule.smul_mem _ _ h₁
  · simp
  · intro F₁ F₂ _ _ h₁ h₂
    rw [add_mul]
    exact add_mem h₁ h₂
  · intro r F₁ _ h₁
    rw [smul_mul_assoc]
    exact Submodule.smul_mem _ _ h₁

/-- The star subalgebra of bounded continuous functions on `(ℝ^d)^k` given by the linear
combinations of the products `∏_j (c_j + ψ_j(x_j))`. -/
def tensorAlgebra (d k : ℕ) : StarSubalgebra ℝ ((Fin k → EuclideanSpace ℝ (Fin d)) →ᵇ ℝ) where
  carrier := {G | (G : (Fin k → EuclideanSpace ℝ (Fin d)) → ℝ) ∈ tensorSpan d k}
  mul_mem' := fun {G H} hG hH => by
    simpa using mul_mem_tensorSpan hG hH
  one_mem' := by
    have : (1 : (Fin k → EuclideanSpace ℝ (Fin d)) → ℝ) = tensorFun 1 0 := by
      funext x
      simp [tensorFun]
    rw [Set.mem_ofPred_eq, BoundedContinuousFunction.coe_one, this]
    exact tensorFun_mem _ fun j => IsTestFunction.zero
  add_mem' := fun {G H} hG hH => by
    simpa using add_mem hG hH
  zero_mem' := by
    rw [Set.mem_ofPred_eq]
    simp
  algebraMap_mem' := fun r => by
    have : ((algebraMap ℝ ((Fin k → EuclideanSpace ℝ (Fin d)) →ᵇ ℝ) r : _) :
        (Fin k → EuclideanSpace ℝ (Fin d)) → ℝ) = r • tensorFun 1 0 := by
      funext x
      simp [tensorFun, BoundedContinuousFunction.algebraMap_apply]
    rw [Set.mem_ofPred_eq, this]
    exact Submodule.smul_mem _ _ (tensorFun_mem _ fun j => IsTestFunction.zero)
  star_mem' := fun {G} hG => by
    simpa using hG

theorem mem_tensorAlgebra {G : (Fin k → EuclideanSpace ℝ (Fin d)) →ᵇ ℝ} :
    G ∈ tensorAlgebra d k ↔ (G : (Fin k → EuclideanSpace ℝ (Fin d)) → ℝ) ∈ tensorSpan d k :=
  Iff.rfl

/-- A property of functions that holds for the products `∏_j (c_j + ψ_j(x_j))` and is stable
under sums and scalar multiples holds on the whole algebra. -/
theorem tensorAlgebra_induction {Q : ((Fin k → EuclideanSpace ℝ (Fin d)) → ℝ) → Prop}
    (h0 : Q 0) (hadd : ∀ F G, Q F → Q G → Q (F + G)) (hsmul : ∀ (r : ℝ) F, Q F → Q (r • F))
    (hgen : ∀ (c : Fin k → ℝ) (ψ : Fin k → (Fin d → ℝ) → ℝ), (∀ j, IsTestFunction (ψ j)) →
      Q (tensorFun c ψ)) {G : (Fin k → EuclideanSpace ℝ (Fin d)) →ᵇ ℝ}
    (hG : G ∈ tensorAlgebra d k) : Q G := by
  refine Submodule.span_induction (p := fun F _ => Q F) ?_ h0 (fun F G _ _ => hadd F G)
    (fun r F _ => hsmul r F) hG
  rintro _ ⟨c, ψ, hψ, rfl⟩
  exact hgen c ψ hψ

/-- The generators `x ↦ ψ(x_j)` belong to the algebra. -/
theorem coord_mem_tensorAlgebra {ψ : (Fin d → ℝ) → ℝ} (hψ : IsTestFunction ψ) (j : Fin k)
    (G : (Fin k → EuclideanSpace ℝ (Fin d)) →ᵇ ℝ)
    (hG : ∀ x, G x = ψ (WithLp.ofLp (x j))) : G ∈ tensorAlgebra d k := by
  have : (G : (Fin k → EuclideanSpace ℝ (Fin d)) → ℝ) =
      tensorFun (fun i => if i = j then 0 else 1) (fun i => if i = j then ψ else 0) := by
    funext x
    rw [hG x]
    simp only [tensorFun]
    rw [Finset.prod_eq_single j]
    · simp
    · intro i _ hi
      simp [hi]
    · simp
  rw [mem_tensorAlgebra, this]
  exact tensorFun_mem _ fun i => by
    by_cases h : i = j
    · simpa [h] using hψ
    · simpa [h] using IsTestFunction.zero

/-- The algebra separates the points of `(ℝ^d)^k`. -/
theorem separatesPoints_tensorAlgebra (d k : ℕ) :
    ((tensorAlgebra d k).map (toContinuousMapStarₐ ℝ)).SeparatesPoints := by
  unfold Subalgebra.SeparatesPoints Set.SeparatesPoints
  intro x y hxy
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hxy
  obtain ⟨ψ, hψ, hne⟩ := exists_testFunction_separating
    (show WithLp.ofLp (x j) ≠ WithLp.ofLp (y j) from fun h => hj (WithLp.ofLp_injective 2 h))
  let G : (Fin k → EuclideanSpace ℝ (Fin d)) →ᵇ ℝ :=
    BoundedContinuousFunction.ofNormedAddCommGroup
      (fun z => ψ (WithLp.ofLp (z j)))
      (hψ.1.continuous.comp ((PiLp.continuous_ofLp 2 (fun _ : Fin d => ℝ)).comp
        (continuous_apply j)))
      (‖(hψ.1.continuous.bounded_above_of_compact_support hψ.2).choose‖)
      (fun z => by
        simpa using ((hψ.1.continuous.bounded_above_of_compact_support hψ.2).choose_spec _).trans
          (le_abs_self _))
  refine ⟨_, ⟨(toContinuousMapStarₐ ℝ) G, ⟨G, coord_mem_tensorAlgebra hψ j G (fun z => rfl), rfl⟩,
    rfl⟩, ?_⟩
  exact hne

end

end LongRangeHeat

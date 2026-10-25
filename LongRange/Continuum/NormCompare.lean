import LatticeProb.Analysis.Elliptic.Holder
import Mathlib.Analysis.Normed.Module.Multilinear.Curry

/-!
# Coordinate bounds for derivative operator norms

Coordinate supremum and Hölder bounds control the operator norms of the first and second
Fréchet derivatives. Hölder increments use the Euclidean radius of the coordinate carrier.
-/

namespace LongRange

open scoped BigOperators
open LatticeProb.Elliptic LatticeProb.Euclidean.Lattice

noncomputable section

variable {d : ℕ}

/-- A linear operator is bounded by the sum of its coordinate images. -/
private lemma norm_le_sum_basis {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : (Fin d → ℝ) →L[ℝ] F) : ‖L‖ ≤ ∑ i, ‖L (Pi.single i 1)‖ := by
  classical
  apply L.opNorm_le_bound (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  intro x
  have hx : x = ∑ i : Fin d, x i • Pi.single i (1 : ℝ) := pi_eq_sum_univ' x
  calc
    ‖L x‖ = ‖∑ i, x i • L (Pi.single i 1)‖ := by
      conv_lhs => rw [hx]
      simp only [map_sum, map_smul]
    _ ≤ ∑ i, ‖x i • L (Pi.single i 1)‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖L (Pi.single i 1)‖ * ‖x‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul, mul_comm]
      exact mul_le_mul_of_nonneg_left (norm_le_pi_norm x i) (norm_nonneg _)
    _ = _ := (Finset.sum_mul _ _ _).symm

/-- A scalar linear form is bounded by the sum of its absolute coordinate entries. -/
lemma norm_le_sum_apply_single (L : (Fin d → ℝ) →L[ℝ] ℝ) :
    ‖L‖ ≤ ∑ i, |L (Pi.single i 1)| := by
  simpa only [Real.norm_eq_abs] using norm_le_sum_basis L

/-- A bilinear form is bounded by the sum of its absolute coordinate entries. -/
lemma norm_le_sum_apply_single₂
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => Fin d → ℝ) ℝ) :
    ‖A‖ ≤ ∑ i, ∑ j, |A ![Pi.single i 1, Pi.single j 1]| := by
  classical
  rw [← A.curryLeft_norm]
  apply (norm_le_sum_basis A.curryLeft).trans
  apply Finset.sum_le_sum
  intro i _
  let E := continuousMultilinearCurryFin1 ℝ (Fin d → ℝ) ℝ
  rw [← E.norm_map (A.curryLeft (Pi.single i 1))]
  have heval (j : Fin d) :
      E (A.curryLeft (Pi.single i 1)) (Pi.single j 1) =
        A ![Pi.single i 1, Pi.single j 1] := by
    apply congrArg A
    ext k
    fin_cases k <;> rfl
  simpa only [heval] using norm_le_sum_apply_single (E (A.curryLeft (Pi.single i 1)))

/-- A component bounded by a finite real constant has a bounded real supremum. -/
private lemma abs_le_of_supNorm_le {N : ℝ} (hN : 0 ≤ N)
    {f : (Fin d → ℝ) → ℝ} (h : supNorm Set.univ f ≤ ENNReal.ofReal N)
    (x : Fin d → ℝ) : |f x| ≤ N := by
  exact (abs_le_supNorm_toReal (h.trans_lt ENNReal.ofReal_lt_top) (Set.mem_univ x)).trans
    ((ENNReal.toReal_mono ENNReal.ofReal_ne_top h).trans_eq (ENNReal.toReal_ofReal hN))

/-- Each value supremum is a component of the coordinate second Hölder norm. -/
private lemma supNorm_le_c2HolderNorm (σ : ℝ) (v : (Fin d → ℝ) → ℝ) :
    supNorm Set.univ v ≤ c2HolderNorm σ Set.univ v := by
  unfold c2HolderNorm
  exact le_self_add.trans (le_self_add.trans le_self_add)

/-- Each first derivative supremum is bounded by the coordinate second Hölder norm. -/
private lemma partial_supNorm_le_c2HolderNorm (σ : ℝ) (v : (Fin d → ℝ) → ℝ)
    (i : Fin d) : supNorm Set.univ (partialDeriv i v) ≤ c2HolderNorm σ Set.univ v := by
  unfold c2HolderNorm
  have hi : supNorm Set.univ (partialDeriv i v) ≤
      ∑ k : Fin d, supNorm Set.univ (partialDeriv k v) :=
    Finset.single_le_sum
      (f := fun k : Fin d => supNorm Set.univ (partialDeriv k v))
      (fun _ _ => bot_le) (Finset.mem_univ i)
  exact hi.trans (le_add_self.trans (le_self_add.trans le_self_add))

/-- Each second derivative supremum is bounded by the coordinate second Hölder norm. -/
private lemma second_supNorm_le_c2HolderNorm (σ : ℝ) (v : (Fin d → ℝ) → ℝ)
    (i j : Fin d) :
    supNorm Set.univ (secondPartial i j v) ≤ c2HolderNorm σ Set.univ v := by
  unfold c2HolderNorm
  have hj : supNorm Set.univ (secondPartial i j v) ≤
      ∑ k : Fin d, supNorm Set.univ (secondPartial i k v) :=
    Finset.single_le_sum
      (f := fun k : Fin d => supNorm Set.univ (secondPartial i k v))
      (fun _ _ => bot_le) (Finset.mem_univ j)
  have hi : (∑ k : Fin d, supNorm Set.univ (secondPartial i k v)) ≤
      ∑ l : Fin d, ∑ k : Fin d, supNorm Set.univ (secondPartial l k v) :=
    Finset.single_le_sum
      (f := fun l : Fin d => ∑ k : Fin d, supNorm Set.univ (secondPartial l k v))
      (fun _ _ => bot_le) (Finset.mem_univ i)
  exact (hj.trans hi).trans (le_add_self.trans le_self_add)

/-- Each second derivative seminorm is bounded by the coordinate second Hölder norm. -/
private lemma second_holder_le_c2HolderNorm (σ : ℝ) (v : (Fin d → ℝ) → ℝ)
    (i j : Fin d) :
    holderSeminorm σ Set.univ (secondPartial i j v) ≤ c2HolderNorm σ Set.univ v := by
  unfold c2HolderNorm
  have hj : holderSeminorm σ Set.univ (secondPartial i j v) ≤
      ∑ k : Fin d, holderSeminorm σ Set.univ (secondPartial i k v) :=
    Finset.single_le_sum
      (f := fun k : Fin d => holderSeminorm σ Set.univ (secondPartial i k v))
      (fun _ _ => bot_le) (Finset.mem_univ j)
  have hi : (∑ k : Fin d, holderSeminorm σ Set.univ (secondPartial i k v)) ≤
      ∑ l : Fin d, ∑ k : Fin d, holderSeminorm σ Set.univ (secondPartial l k v) :=
    Finset.single_le_sum
      (f := fun l : Fin d => ∑ k : Fin d, holderSeminorm σ Set.univ (secondPartial l k v))
      (fun _ _ => bot_le) (Finset.mem_univ i)
  exact (hj.trans hi).trans le_add_self

/-- A global coordinate Hölder norm bounds every value of the function. -/
theorem abs_le_of_c2HolderNorm {σ N : ℝ} {v : (Fin d → ℝ) → ℝ}
    (hN : 0 ≤ N) (h : c2HolderNorm σ Set.univ v ≤ ENNReal.ofReal N)
    (x : Fin d → ℝ) : |v x| ≤ N :=
  abs_le_of_supNorm_le hN ((supNorm_le_c2HolderNorm σ v).trans h) x

/-- A global coordinate Hölder norm bounds the first derivative operator norm. -/
theorem norm_fderiv_le_of_c2HolderNorm {σ N : ℝ} {v : (Fin d → ℝ) → ℝ}
    (hN : 0 ≤ N) (h : c2HolderNorm σ Set.univ v ≤ ENNReal.ofReal N)
    (x : Fin d → ℝ) : ‖fderiv ℝ v x‖ ≤ d * N := by
  apply (norm_le_sum_apply_single _).trans
  calc
    _ ≤ ∑ _ : Fin d, N := Finset.sum_le_sum fun i _ =>
      abs_le_of_supNorm_le hN ((partial_supNorm_le_c2HolderNorm σ v i).trans h) x
    _ = _ := by simp

/-- A global coordinate Hölder norm bounds the second derivative operator norm. -/
theorem norm_iteratedFDeriv_two_le_of_c2HolderNorm {σ N : ℝ}
    {v : (Fin d → ℝ) → ℝ} (hN : 0 ≤ N)
    (h : c2HolderNorm σ Set.univ v ≤ ENNReal.ofReal N) (x : Fin d → ℝ) :
    ‖iteratedFDeriv ℝ 2 v x‖ ≤ d ^ 2 * N := by
  apply (norm_le_sum_apply_single₂ _).trans
  calc
    _ ≤ ∑ _ : Fin d, ∑ _ : Fin d, N :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
        abs_le_of_supNorm_le hN ((second_supNorm_le_c2HolderNorm σ v i j).trans h) x
    _ = _ := by simp; ring

/-- Coordinate Hölder increments control the second derivative operator increments. -/
theorem norm_iteratedFDeriv_two_sub_le_of_c2HolderNorm {σ N : ℝ}
    {v : (Fin d → ℝ) → ℝ} (hN : 0 ≤ N)
    (h : c2HolderNorm σ Set.univ v ≤ ENNReal.ofReal N) (x y : Fin d → ℝ) :
    ‖iteratedFDeriv ℝ 2 v x - iteratedFDeriv ℝ 2 v y‖ ≤
      d ^ 2 * N * radius (x - y) ^ σ := by
  have hcoord (i j : Fin d) :
      |secondPartial i j v x - secondPartial i j v y| ≤ N * radius (x - y) ^ σ := by
    have hs := (second_supNorm_le_c2HolderNorm σ v i j).trans h
    have hh := (second_holder_le_c2HolderNorm σ v i j).trans h
    have hf : c0HolderNorm σ Set.univ (secondPartial i j v) < ⊤ := by
      exact ENNReal.add_lt_top.mpr
        ⟨hs.trans_lt ENNReal.ofReal_lt_top, hh.trans_lt ENNReal.ofReal_lt_top⟩
    apply (abs_sub_le_holderSeminorm_toReal hf (Set.mem_univ x) (Set.mem_univ y)).trans
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (radius_nonneg _) _)
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hh).trans_eq
      (ENNReal.toReal_ofReal hN)
  apply (norm_le_sum_apply_single₂ _).trans
  calc
    _ ≤ ∑ _ : Fin d, ∑ _ : Fin d, N * radius (x - y) ^ σ :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hcoord i j
    _ = _ := by simp; ring

end
end LongRange

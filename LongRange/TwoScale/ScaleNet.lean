import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Range
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Finite nets of scales

Every nonempty closed real interval has a finite net of any positive mesh.
The number of grid points is bounded by the interval length divided by the mesh, plus one.
-/

namespace LongRange

/-- A closed real interval admits a net of mesh `δ` with at most its length over `δ`,
plus one, points. -/
theorem exists_scale_net {lo hi δ : ℝ} (hlo : lo ≤ hi) (hδ : 0 < δ) :
    ∃ N : Finset ℝ, (∀ η ∈ N, lo ≤ η ∧ η ≤ hi) ∧
      ((N.card : ℝ) ≤ (hi - lo) / δ + 1) ∧
      ∀ x, lo ≤ x → x ≤ hi → ∃ η ∈ N, |x - η| ≤ δ := by
  classical
  let K : ℕ := ⌊(hi - lo) / δ⌋₊
  let N := (Finset.range (K + 1)).image (fun k : ℕ => lo + k * δ)
  have hK : (K : ℝ) ≤ (hi - lo) / δ :=
    Nat.floor_le (div_nonneg (sub_nonneg.mpr hlo) hδ.le)
  refine ⟨N, ?_, ?_, ?_⟩
  · intro η hη
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hη
    have hkK : k ≤ K := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    have hkreal : (k : ℝ) ≤ K := by exact_mod_cast hkK
    have hupper : (k : ℝ) * δ ≤ hi - lo :=
      (le_div_iff₀ hδ).mp (hkreal.trans hK)
    constructor
    · exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg k) hδ.le)
    · linarith
  · have hcard : N.card ≤ K + 1 := by
      exact (Finset.card_image_le).trans_eq (Finset.card_range (K + 1))
    have hcardreal : (N.card : ℝ) ≤ (K : ℝ) + 1 := by exact_mod_cast hcard
    linarith
  · intro x hxlo hxhi
    let k : ℕ := ⌊(x - lo) / δ⌋₊
    have hkK : k ≤ K := Nat.floor_mono (by
      exact (div_le_div_iff_of_pos_right hδ).mpr (sub_le_sub_right hxhi lo))
    have hk : k ∈ Finset.range (K + 1) :=
      Finset.mem_range.mpr (Nat.lt_succ_of_le hkK)
    refine ⟨lo + k * δ, Finset.mem_image_of_mem _ hk, ?_⟩
    have hleft : (k : ℝ) * δ ≤ x - lo :=
      (le_div_iff₀ hδ).mp (Nat.floor_le (div_nonneg (sub_nonneg.mpr hxlo) hδ.le))
    have hright : x - lo < ((k : ℝ) + 1) * δ :=
      (div_lt_iff₀ hδ).mp (Nat.lt_floor_add_one ((x - lo) / δ))
    rw [abs_of_nonneg (by linarith : 0 ≤ x - (lo + k * δ))]
    linarith

end LongRange

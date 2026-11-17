import LongRangeHeat.KallenbergBoundedCollection
import LongRangeHeat.KallenbergAnnealedContainment

/-!
# Totally bounded sets for the annealed walks

The stopping-time and displacement estimates yield a common totally bounded
set with a prescribed countable family of probability budgets.
-/

namespace LongRangeHeat

open Filter MeasureTheory LatticeProb LatticeProb.Cadlag.HalfLine LatticeProb.External
open scoped ENNReal Topology
open LongRange (Edge)

/-- Countable partition and containment budgets bound the complement of one totally bounded set. -/
theorem annealed_exists_totallyBounded
    (hMSC : MuruganSaloffCosteUniform)
    (hNash : ChenKimKumagaiWangNash)
    (hDavies : ChenKimKumagaiWangDavies)
    {d : ℕ} (hd : 1 ≤ d) {lam : ℝ}
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (a : Ω → Edge d → ℝ)
    (hP : ConductanceLaw P lam a)
    (ε : ℕ → ℝ) (hε : ∀ n, ε n ∈ Set.Ioo (0 : ℝ) (1 / 2))
    (hε0 : Tendsto ε atTop (𝓝 0)) (t : ℕ → Time) (ht0 : ∀ k, 0 < t k)
    (ht : Tendsto t atTop atTop) (η : ℕ → ℝ) (hη : ∀ k, 0 < η k)
    (hη0 : Tendsto η atTop (𝓝 0)) (p q : ℕ → ℝ) (hp : ∀ k, 0 < p k)
    (hq : ∀ k, 0 < q k) :
    ∃ A : Set (PathSpace d), TotallyBounded A ∧ ∀ n,
      (annealedLaw hd P a hP (hε n).1 : Measure (PathSpace d)) Aᶜ ≤
        (∑' k, ENNReal.ofReal (p k)) + ∑' k, ENNReal.ofReal (q k) := by
  choose δ hδ hδbound using fun k =>
    annealed_exists_uniform_oscillation_partition hMSC hNash hDavies hd P a hP ε hε hε0
      (t k) (ht0 k) (hη k) (ENNReal.ofReal_pos.mpr (hp k))
  choose S hS hSbound using fun k =>
    annealed_exists_compact_containment hMSC hNash hDavies hd P a hP ε hε hε0
      (t k) (hq k)
  obtain ⟨A, hA, hbound⟩ := exists_totallyBounded_measure_compl_le t δ η ht hδ hη hη0
    S hS (fun n => (annealedLaw hd P a hP (hε n).1 : Measure (PathSpace d)))
    (fun _ => id) (fun k => ENNReal.ofReal (p k)) (fun k => ENNReal.ofReal (q k))
    (fun n k => (hδbound k n).le) (fun n k => hSbound k n)
  exact ⟨A, hA, hbound⟩

end LongRangeHeat

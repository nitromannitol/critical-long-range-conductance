import LongRangeHeat.KallenbergHitting

/-!
# Oscillation partitions

The successive oscillation times yield partitions with controlled oscillation
when their gaps are not too short.
-/

namespace LatticeProb.Cadlag.HalfLine

open Set
open scoped ENNReal NNReal

variable {E : Type} [MetricSpace E]

/-- A finite partition of `[0,t)` whose nonterminal intervals have length at
least `δ` and whose oscillation on each interval is at most `η`. -/
def HasOscillationPartition (x : D E) (t : Time) (δ η : ℝ) : Prop :=
  ∃ K : ℕ, 0 < K ∧ ∃ cut : ℕ → Time,
    cut 0 = 0 ∧ cut K = t ∧
    (∀ i, i < K → cut i < cut (i + 1)) ∧
    (∀ i, i + 1 < K → δ ≤ (cut (i + 1) : ℝ) - (cut i : ℝ)) ∧
    ∀ i, i < K → ∀ s u : Time,
      cut i ≤ s → s < cut (i + 1) → cut i ≤ u → u < cut (i + 1) →
      dist (x.1 s) (x.1 u) ≤ η


/-- The modified oscillation modulus, truncated at one. -/
noncomputable def truncatedModifiedModulus (x : D E) (t : Time) (δ : ℝ) : ℝ≥0∞ :=
  min (⨅ η : ℝ≥0, ⨅ (_ : HasOscillationPartition x t δ (η : ℝ)), (η : ℝ≥0∞)) 1

/-- Lowering the required minimum interval length preserves a partition. -/
theorem HasOscillationPartition.mono {x : D E} {t : Time} {δ δ' η : ℝ}
    (h : HasOscillationPartition x t δ η) (hδ : δ' ≤ δ) :
    HasOscillationPartition x t δ' η := by
  obtain ⟨K, hK, cut, h0, ht, hstrict, hwidth, hosc⟩ := h
  exact ⟨K, hK, cut, h0, ht, hstrict, fun i hi => hδ.trans (hwidth i hi), hosc⟩

/-- An oscillation partition bounds the modified modulus. -/
theorem truncatedModifiedModulus_le_of_partition {x : D E} {t : Time} {δ η : ℝ}
    (hη : 0 ≤ η) (h : HasOscillationPartition x t δ η) :
    truncatedModifiedModulus x t δ ≤ ENNReal.ofReal η := by
  calc
    _ ≤ ⨅ η : ℝ≥0, ⨅ (_ : HasOscillationPartition x t δ (η : ℝ)), (η : ℝ≥0∞) :=
      min_le_left _ _
    _ ≤ (η.toNNReal : ℝ≥0∞) := by
      have hh : HasOscillationPartition x t δ (η.toNNReal : ℝ) := by
        simpa only [Real.coe_toNNReal _ hη] using h
      exact iInf_le_of_le η.toNNReal (iInf_le _ hh)
    _ = ENNReal.ofReal η := rfl

/-- Long enough gaps in the successive oscillation times produce a partition
whose oscillation is at most twice the threshold. -/
theorem hasOscillationPartition_of_oscillation_gaps {Ω : Type} (Y : Ω → D E)
    (T t : Time) (ht : 0 < t) {ζ δ : ℝ} (hζ : 0 ≤ ζ) (hδ : 0 < δ)
    (m : ℕ) (w : Ω) (hm : t ≤ oscillationTime Y T ζ m w)
    (hgap : ∀ i, i < m → oscillationTime Y T ζ (i + 1) w < t →
      δ ≤ (oscillationTime Y T ζ (i + 1) w : ℝ) - (oscillationTime Y T ζ i w : ℝ)) :
    HasOscillationPartition (Y w) t δ (2 * ζ) := by
  classical
  let α : ℕ → Time := fun i => oscillationTime Y T ζ i w
  have hex : ∃ i, t ≤ α i := ⟨m, hm⟩
  let K := Nat.find hex
  have hKm : K ≤ m := Nat.find_min' hex hm
  have hK : t ≤ α K := Nat.find_spec hex
  have hKpos : 0 < K := by
    apply (Nat.find_pos hex).mpr
    change ¬ t ≤ 0
    exact not_le_of_gt ht
  have hbefore (i : ℕ) (hi : i < K) : α i < t := lt_of_not_ge (Nat.find_min hex hi)
  let cut : ℕ → Time := fun i => if i = K then t else α i
  have hc0 : cut 0 = 0 := by
    simp only [cut, ne_of_lt hKpos, ite_false, α, oscillationTime]
  have hcK : cut K = t := by simp only [cut, ite_true]
  refine ⟨K, hKpos, cut, hc0, hcK, ?_, ?_, ?_⟩
  · intro i hi
    have hik : i ≠ K := ne_of_lt hi
    by_cases hn : i + 1 = K
    · simp only [cut, hik, ite_false, hn, ite_true]
      exact hbefore i hi
    · have his : i + 1 < K := lt_of_le_of_ne (Nat.succ_le_of_lt hi) hn
      have hgi := hgap i (lt_of_lt_of_le hi hKm) (hbefore (i + 1) his)
      have hreal : (α i : ℝ) < (α (i + 1) : ℝ) := by linarith
      simpa only [cut, hik, hn, ite_false] using NNReal.coe_lt_coe.mp hreal
  · intro i hi
    have hik : i ≠ K := by omega
    have his : i + 1 ≠ K := ne_of_lt hi
    simpa only [cut, hik, his, ite_false, α] using
      hgap i (by omega) (hbefore (i + 1) hi)
  · intro i hi s u hcs hs hcu hu
    have hik : i ≠ K := ne_of_lt hi
    have hstart : cut i = α i := by simp only [cut, hik, ite_false]
    have hend : cut (i + 1) ≤ α (i + 1) := by
      by_cases hn : i + 1 = K
      · simp only [cut, hn, ite_true]
        simpa only [hn] using hK
      · simp only [cut, hn, ite_false, le_refl]
    apply dist_le_between_oscillationTimes Y T hζ i w
    · simpa only [hstart] using hcs
    · exact hs.trans_le hend
    · simpa only [hstart] using hcu
    · exact hu.trans_le hend


/-- Every càdlàg path admits a sufficiently fine small-oscillation partition. -/
theorem exists_pos_hasOscillationPartition (x : D E) (t : Time) (ht : 0 < t)
    {η : ℝ} (hη : 0 < η) : ∃ δ : ℝ, 0 < δ ∧ HasOscillationPartition x t δ η := by
  classical
  let Y : Unit → D E := fun _ => x
  let T : Time := t + 1
  let ζ : ℝ := η / 2
  have hζ : 0 < ζ := half_pos hη
  have htT : t < T := lt_add_of_pos_right _ zero_lt_one
  obtain ⟨m, hm⟩ := exists_le_oscillationTime Y T t htT.le hζ ()
  let α : ℕ → Time := fun k => oscillationTime Y T ζ k ()
  have hex : ∃ k, t ≤ α k := ⟨m, hm⟩
  let K := Nat.find hex
  have hK : t ≤ α K := Nat.find_spec hex
  have hKpos : 0 < K := by
    apply (Nat.find_pos hex).mpr
    change ¬ t ≤ 0
    exact not_le_of_gt ht
  have hbefore (i : ℕ) (hi : i < K) : α i < t := lt_of_not_ge (Nat.find_min hex hi)
  let gap : ℕ → ℝ := fun i => (α (i + 1) : ℝ) - (α i : ℝ)
  have hgap (i : ℕ) (hi : i ∈ Finset.range K) : 0 < gap i := by
    have hi' : i < K := Finset.mem_range.mp hi
    have hstrict := lt_nextOscillationTime Y (oscillationTime Y T ζ i) T hζ ()
      ((hbefore i hi').trans htT)
    have hreal : (α i : ℝ) < (α (i + 1) : ℝ) := by exact_mod_cast hstrict
    dsimp [gap]
    linarith
  have hnonempty : (Finset.range K).Nonempty := ⟨0, Finset.mem_range.mpr hKpos⟩
  let δ : ℝ := (Finset.range K).inf' hnonempty gap
  have hδ : 0 < δ := (Finset.lt_inf'_iff hnonempty).mpr hgap
  have hp := hasOscillationPartition_of_oscillation_gaps Y T t ht hζ.le hδ K () hK
    (fun i hi _ => Finset.inf'_le gap (Finset.mem_range.mpr hi))
  refine ⟨δ, hδ, ?_⟩
  simpa only [Y, ζ, show 2 * (η / 2) = η by ring] using hp

end LatticeProb.Cadlag.HalfLine

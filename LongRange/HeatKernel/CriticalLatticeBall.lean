import LongRange.HeatKernel.CriticalBallAverage
import LongRange.HeatKernel.CriticalSubordinateLower
import LongRange.Support.Graph.LongRangeKernel.LatticeVolume

/-!
# Finite lattice balls

The coordinate graph balls are finite and their cardinalities equal their volumes.
-/

open LatticeProb
open scoped NNReal ENNReal

namespace LatticeProb.Graph.LongRangeKernel

/-- The graph ball about zero, represented as a finite set. -/
noncomputable def latticeGraphBall (d r : ℕ) : Finset (Site d) :=
  (boxFinset (0 : Site d) r).filter (fun z => graphNorm z ≤ r)

/-- Membership in the finite graph ball is expressed by the graph norm. -/
theorem mem_latticeGraphBall {d r : ℕ} {z : Site d} :
    z ∈ latticeGraphBall d r ↔ graphNorm z ≤ r := by
  classical
  simp only [latticeGraphBall, Finset.mem_filter]
  constructor
  · exact And.right
  · intro hz
    exact ⟨mem_boxFinset_zero_iff.mpr ((supNorm_le_graphNorm z).trans hz), hz⟩

/-- Every graph ball contains zero. -/
theorem latticeGraphBall_nonempty (d r : ℕ) : (latticeGraphBall d r).Nonempty := by
  refine ⟨0, mem_latticeGraphBall.mpr ?_⟩
  simp only [graphNorm_zero, Nat.zero_le]

/-- The counting volume of a graph ball is its cardinality. -/
theorem weightedLattice_volume_eq_latticeGraphBall_card {d : ℕ} (hd : 0 < d)
    (r : ℕ) : (weightedLattice d hd).volume 0 r = (latticeGraphBall d r).card := by
  classical
  rw [weightedLattice_volume_eq_tsum hd]
  rw [tsum_eq_sum (s := latticeGraphBall d r)]
  · calc
      _ = ∑ _z ∈ latticeGraphBall d r, (1 : ℝ≥0∞) := by
        apply Finset.sum_congr rfl
        intro z hz
        simp only [Nat.cast_le, mem_latticeGraphBall.mp hz, ↓reduceIte]
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  · intro z hz
    have hz' : ¬ (graphNorm z : ℝ) ≤ r := by
      simpa only [Nat.cast_le, ← mem_latticeGraphBall] using hz
    simp only [hz', ↓reduceIte]

/-- Lattice ball cardinalities dominate the polynomial volume profile. -/
theorem latticeVolumeProfile_le_card_latticeGraphBall {d : ℕ} (hd : 0 < d) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℕ, 1 ≤ r →
      latticeVolumeProfile d r ≤ C * (latticeGraphBall d r).card := by
  obtain ⟨C, hC, hvol⟩ := weightedLattice_volume_comparable hd
  refine ⟨C, by linarith, ?_⟩
  intro r hr
  have hr' : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have h := (hvol 0 r hr').1
  rw [weightedLattice_volume_eq_latticeGraphBall_card hd r] at h
  have hreal := ENNReal.toReal_mono (by simp) h
  have hp : 0 ≤ C⁻¹ * latticeVolumeProfile d r := by
    unfold latticeVolumeProfile
    positivity
  rw [ENNReal.toReal_ofReal hp, ENNReal.toReal_natCast] at hreal
  exact (inv_mul_le_iff₀ (by linarith : 0 < C)).mp hreal

/-- At quadratic time, the averaged walk is uniformly positive on a graph ball. -/
theorem weightedLattice_averaged_ball_lower {d : ℕ} (hd : 0 < d) :
    ∃ b : ℝ, 0 < b ∧ ∀ (r : ℕ), 1 ≤ r → ∀ (x z : Site d),
      z ∈ latticeGraphBall d r →
      b / latticeVolumeProfile d (3 * r) ≤
        (densityPower (weightedLattice d hd).mass
          (averagedDensity (weightedLattice d hd).mass
            (weightedLattice d hd).referenceDensity) (2 * r ^ 2) x (x + z)).toReal := by
  obtain ⟨c, hc, δ, hδ, hblock⟩ := weightedLattice_averaged_quadratic_block_lower hd
  let e : ℝ≥0∞ := 8⁻¹ * min δ 1
  have hepos : 0 < e := by
    dsimp [e]
    exact ENNReal.mul_pos (by norm_num) (lt_min hδ (by norm_num)).ne'
  have hetop : e < ∞ := by
    dsimp [e]
    exact ENNReal.mul_lt_top (by simp) ((min_le_right δ 1).trans_lt ENNReal.one_lt_top)
  have hereal : 0 < e.toReal := ENNReal.toReal_pos hepos.ne' hetop.ne
  let b := e.toReal * c * Real.exp (-(1 / (2 * c)))
  refine ⟨b, by dsimp [b]; positivity, ?_⟩
  have hm : ∀ x, (weightedLattice d hd).mass x ≠ 0 := by
    intro x
    simp only [weightedLattice_mass, ne_eq, one_ne_zero, not_false_eq_true]
  have hp := averagedDensity_isMarkov (weightedLattice d hd).mass hm _
    (weightedLattice_isMarkovDensity hd)
  intro r hr x z hz
  have hdist : (weightedLattice d hd).graph.dist x (x + z) ≤ r := by
    change (lattice d).dist x (x + z) ≤ r
    rw [lattice_dist_eq_graphNorm hd]
    simpa only [add_sub_cancel_left] using mem_latticeGraphBall.mp hz
  have hb := hblock x (x + z) r (r - 1) hr hdist (by omega) (by omega)
  have hpow : r - 1 + 1 = r := by omega
  rw [hpow] at hb
  have he : e ≤ 8⁻¹ * δ := by
    dsimp [e]
    gcongr
    exact min_le_left δ 1
  have hlower : e * ENNReal.ofReal
      (c / latticeVolumeProfile d (3 * r) * Real.exp (-(1 / (2 * c)))) ≤
      densityPower (weightedLattice d hd).mass
        (averagedDensity (weightedLattice d hd).mass
          (weightedLattice d hd).referenceDensity) (2 * r ^ 2) x (x + z) :=
    (mul_le_mul_left he _).trans hb
  have hrow := densityPower_isMarkov (weightedLattice d hd).mass hm _ hp (2 * r ^ 2) x
  have hle := ENNReal.le_tsum (f := fun y => densityPower (weightedLattice d hd).mass
    (averagedDensity (weightedLattice d hd).mass (weightedLattice d hd).referenceDensity)
      (2 * r ^ 2) x y * ((weightedLattice d hd).mass y : ℝ≥0∞)) (x + z)
  rw [hrow] at hle
  have hfinite : densityPower (weightedLattice d hd).mass
      (averagedDensity (weightedLattice d hd).mass
        (weightedLattice d hd).referenceDensity) (2 * r ^ 2) x (x + z) < ∞ := by
    apply lt_of_le_of_lt _ ENNReal.one_lt_top
    simpa only [weightedLattice_mass, ENNReal.coe_one, mul_one] using hle
  have hv : 0 < latticeVolumeProfile d (3 * r) := by
    unfold latticeVolumeProfile
    positivity
  have hreal := ENNReal.toReal_mono hfinite.ne hlower
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at hreal
  dsimp [b]
  convert hreal using 1
  ring

/-- The reciprocal ball cardinality is bounded by a quadratic-time transition density. -/
theorem weightedLattice_ball_card_inv_le_power {d : ℕ} (hd : 0 < d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (r : ℕ), 1 ≤ r → ∀ (x z : Site d),
      z ∈ latticeGraphBall d r →
      ((latticeGraphBall d r).card : ℝ)⁻¹ ≤ C *
        (densityPower (weightedLattice d hd).mass
          (averagedDensity (weightedLattice d hd).mass
            (weightedLattice d hd).referenceDensity) (2 * r ^ 2) x (x + z)).toReal := by
  obtain ⟨b, hb, hlower⟩ := weightedLattice_averaged_ball_lower hd
  obtain ⟨A, hA, hvol⟩ := latticeVolumeProfile_le_card_latticeGraphBall hd
  let M : ℝ := (3 : ℝ) ^ d * A
  have hM : 0 < M := by dsimp [M]; positivity
  refine ⟨M / b, by positivity, ?_⟩
  intro r hr x z hz
  have hcard : 0 < ((latticeGraphBall d r).card : ℝ) := by
    exact_mod_cast (latticeGraphBall_nonempty d r).card_pos
  have hv : 0 < latticeVolumeProfile d (3 * r) := by
    unfold latticeVolumeProfile
    positivity
  have hprofile : latticeVolumeProfile d (3 * r) ≤ M * (latticeGraphBall d r).card := by
    calc
      latticeVolumeProfile d (3 * r) ≤ (3 : ℝ) ^ d * latticeVolumeProfile d r := by
        unfold latticeVolumeProfile
        rw [← mul_pow]
        apply pow_le_pow_left₀ (by positivity)
        nlinarith [Nat.cast_nonneg (α := ℝ) r]
      _ ≤ M * (latticeGraphBall d r).card := by
        dsimp [M]
        nlinarith [hvol r hr]
  have hk := hlower r hr x z hz
  have hk0 : 0 ≤ (densityPower (weightedLattice d hd).mass
      (averagedDensity (weightedLattice d hd).mass
        (weightedLattice d hd).referenceDensity) (2 * r ^ 2) x (x + z)).toReal :=
    ENNReal.toReal_nonneg
  have hmul := mul_le_mul_of_nonneg_left hprofile hk0
  have hk' := (div_le_iff₀ hv).mp hk
  have hfinal : b ≤ (densityPower (weightedLattice d hd).mass
      (averagedDensity (weightedLattice d hd).mass
        (weightedLattice d hd).referenceDensity) (2 * r ^ 2) x (x + z)).toReal *
        (M * (latticeGraphBall d r).card) := hk'.trans hmul
  rw [← one_div, div_le_iff₀ hcard]
  have hdiv : 1 ≤ ((densityPower (weightedLattice d hd).mass
      (averagedDensity (weightedLattice d hd).mass
        (weightedLattice d hd).referenceDensity) (2 * r ^ 2) x (x + z)).toReal *
          (M * (latticeGraphBall d r).card)) / b :=
    (le_div_iff₀ hb).2 (by simpa only [one_mul] using hfinal)
  convert hdiv using 1
  ring

/-- A quadratic-time loss controls the squared deviation from a lattice ball average. -/
theorem weightedLattice_ball_average_le_power_loss {d : ℕ} (hd : 0 < d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (r : ℕ), 1 ≤ r → ∀ f : lp (fun _ : Site d => ℝ) 2,
      (∑' x, (f x - finsetTranslateAverage (latticeGraphBall d r) f x) ^ 2) ≤
        C * (‖f‖ ^ 2 - ‖(markovOperatorCLM
          (averagedDensity (weightedLattice d hd).mass
            (weightedLattice d hd).referenceDensity)
          (by
            intro x
            simpa only [weightedLattice_mass, ENNReal.coe_one, mul_one] using
              averagedDensity_isMarkov (weightedLattice d hd).mass
                (by intro y; simp only [weightedLattice_mass, ne_eq, one_ne_zero, not_false_eq_true])
                _ (weightedLattice_isMarkovDensity hd) x)
          (averagedDensity_symmetric (weightedLattice d hd).mass
            (by intro y; simp only [weightedLattice_mass, ne_eq, one_ne_zero, not_false_eq_true])
            _ (weightedLattice d hd).referenceDensity_symmetric) ^ (r ^ 2)) f‖ ^ 2) := by
  obtain ⟨C, hC, hbound⟩ := weightedLattice_ball_card_inv_le_power hd
  refine ⟨2 * C, by positivity, ?_⟩
  intro r hr f
  let k := averagedDensity (weightedLattice d hd).mass
    (weightedLattice d hd).referenceDensity
  have hm : ∀ y, (weightedLattice d hd).mass y ≠ 0 := by
    intro y
    simp only [weightedLattice_mass, ne_eq, one_ne_zero, not_false_eq_true]
  have hk : ∀ x, ∑' y, k x y = 1 := by
    intro x
    simpa only [k, weightedLattice_mass, ENNReal.coe_one, mul_one] using
      averagedDensity_isMarkov (weightedLattice d hd).mass hm _
        (weightedLattice_isMarkovDensity hd) x
  have hsym : ∀ x y, k x y = k y x :=
    averagedDensity_symmetric (weightedLattice d hd).mass hm _
      (weightedLattice d hd).referenceDensity_symmetric
  have hmass : (weightedLattice d hd).mass = fun _ => 1 := by
    funext x
    exact weightedLattice_mass hd x
  have h := finsetTranslateAverage_sq_tsum_le_power_loss (latticeGraphBall d r)
    (latticeGraphBall_nonempty d r) k hk hsym (r ^ 2) C hC.le
    (by
      intro x z hz
      simpa only [k, ← hmass] using hbound r hr x z hz) f
  exact h

end LatticeProb.Graph.LongRangeKernel

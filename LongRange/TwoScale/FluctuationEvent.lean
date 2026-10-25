import LongRange.TwoScale.FluctuationModulus
import LongRange.TwoScale.FluctuationFixed
import LongRange.TwoScale.ScaleNet
import LongRange.TwoScale.Blocks
import LongRange.TwoScale.Scaling
import LongRange.TwoScale.L2Part

/-!
# Finite events for the block fluctuation

Finite scale and site sets give measurable fluctuation events with a Gaussian union bound.
The scale modulus extends their pointwise control to every scale in a block window.
-/

namespace LongRange

open MeasureTheory LatticeProb LatticeProb.Euclidean.Lattice

noncomputable section

variable {d : ℕ}

/-- A finite family of measurable Gaussian variables is simultaneously bounded outside
an exceptional set whose measure is bounded by the sum of the individual tails. -/
theorem finite_gaussian_event {Ω ι : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (I : Finset ι) (X : ι → Ω → ℝ) (θ : ι → ℝ)
    (hX : ∀ i ∈ I, Measurable (X i))
    (hbound : ∀ i ∈ I, OsBound P 2 (θ i) (fun ω => |X i ω|))
    (t : ℝ) (ht : 1 ≤ t) :
    ∃ G : Set Ω, MeasurableSet G ∧
      P Gᶜ ≤ ∑ _i ∈ I, ENNReal.ofReal (Real.exp (-(t ^ (2 : ℝ)))) ∧
      ∀ ω ∈ G, ∀ i ∈ I, |X i ω| ≤ t * θ i := by
  classical
  let G : Set Ω := ⋂ i ∈ I, {ω | |X i ω| ≤ t * θ i}
  refine ⟨G, I.measurableSet_biInter (fun i hi =>
    measurableSet_le (hX i hi).abs measurable_const), ?_, ?_⟩
  · have heq : Gᶜ = ⋃ i ∈ I, {ω | t * θ i < |X i ω|} := by
      ext ω
      simp only [G, Set.mem_compl_iff, Set.mem_iInter, Set.mem_setOf_eq,
        Set.mem_iUnion, not_forall, not_le, exists_prop]
    rw [heq]
    apply (measure_biUnion_finset_le I _).trans
    apply Finset.sum_le_sum
    intro i hi
    apply le_trans (measure_mono (fun ω hω => ?_)) (hbound i hi t ht)
    change t * θ i < |X i ω| at hω
    change t * θ i < max |X i ω| 0
    exact lt_of_lt_of_le hω (le_max_left _ _)
  · intro ω hω i hi
    exact Set.mem_iInter.mp (Set.mem_iInter.mp hω i) hi

/-- The fixed-scale concentration theorem produces a measurable event on any finite
set of scales and sites, with the exact sum of Gaussian tail probabilities. -/
theorem smoothFluctuation_finite_event (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
      {lam : ℝ} {a : Ω → Edge d → ℝ}, ∀ hA : AssumptionU P lam a,
      ∀ (N : Finset ℝ), (∀ η ∈ N, η ∈ Set.Ioo (0 : ℝ) 1) →
      ∀ (Q : Finset (Site d)) (v : (Fin d → ℝ) → ℝ) (B : ℝ),
      ContDiff ℝ 2 v → (∀ x, |v x| ≤ B) → (∀ x, ‖fderiv ℝ v x‖ ≤ B) →
      (∀ x, ‖iteratedFDeriv ℝ 2 v x‖ ≤ B) → ∀ t : ℝ, 1 ≤ t →
      ∃ G : Set Ω, MeasurableSet G ∧
        P Gᶜ ≤ ∑ _p ∈ N ×ˢ Q, ENNReal.ofReal (Real.exp (-(t ^ (2 : ℝ)))) ∧
        ∀ ω ∈ G, ∀ η ∈ N, ∀ q ∈ Q,
          |smoothFluctuation η (a ω) (meanConductance P hA.one_le_dim a) v q| ≤
            t * (C * lam⁻¹ * B / kappa d η) := by
  obtain ⟨C, hC, hc⟩ := smoothFluctuation_osBound d
  refine ⟨C, hC, ?_⟩
  intro Ω _ P lam a hA N hN Q v B hv hv0 hv1 hv2 t ht
  obtain ⟨G, hG, htail, hgood⟩ := finite_gaussian_event P (N ×ˢ Q)
    (fun p ω => smoothFluctuation p.1 (a ω) (meanConductance P hA.one_le_dim a) v p.2)
    (fun p => C * lam⁻¹ * B / kappa d p.1)
    (fun p hp => (hc hA p.1 (hN p.1 (Finset.mem_product.mp hp).1)
      v B hv hv0 hv1 hv2 p.2).1)
    (fun p hp => (hc hA p.1 (hN p.1 (Finset.mem_product.mp hp).1)
      v B hv hv0 hv1 hv2 p.2).2) t ht
  refine ⟨G, hG, htail, ?_⟩
  intro ω hω η hη q hq
  exact hgood ω hω (η, q) (Finset.mem_product.mpr ⟨hη, hq⟩)

/-- A finite scale net controls the fluctuation at every scale of the same block
window, with the explicit modulus error and no intersection over all scales. -/
theorem smoothFluctuation_le_of_scale_net (hd : 1 ≤ d) {σ : ℝ}
    (hσ : 0 < σ) (hσ1 : σ ≤ 1) (c C₀ K lam B : ℝ)
    (hc : 0 < c) (hcC : c ≤ C₀) (hlam : 0 < lam) :
    ∃ A : ℝ, 0 < A ∧ ∀ (v : (Fin d → ℝ) → ℝ), ContDiff ℝ 2 v →
      (∀ x, |v x| ≤ B) → (∀ x, ‖fderiv ℝ v x‖ ≤ B) →
      (∀ x, ‖iteratedFDeriv ℝ 2 v x‖ ≤ B) →
      (∀ x y, ‖iteratedFDeriv ℝ 2 v x - iteratedFDeriv ℝ 2 v y‖ ≤
        B * radius (x - y) ^ σ) → ∀ m : ℕ, 1 ≤ m →
      ∀ (N : Finset ℝ) (δ R : ℝ),
      (∀ η ∈ N, η ∈ Set.Ioo (0 : ℝ) 1 ∧ c / 3 ^ m ≤ η ∧ η ≤ C₀ / 3 ^ m) →
      (∀ ε, c / 3 ^ m ≤ ε → ε ≤ C₀ / 3 ^ m → ∃ η ∈ N, |ε - η| ≤ δ) →
      ∀ (a : Edge d → ℝ) (m₀ : ℝ), (∀ e, |a e - m₀| ≤ lam⁻¹) →
      ∀ q : Site d, radius (physical 1 q) ≤ K * 3 ^ m →
      (∀ η ∈ N, |smoothFluctuation η a m₀ v q| ≤ R) →
      ∀ ε : ℝ, ε ∈ Set.Ioo (0 : ℝ) 1 → c / 3 ^ m ≤ ε → ε ≤ C₀ / 3 ^ m →
        |smoothFluctuation ε a m₀ v q| ≤ R + A * ((3 ^ m * δ) ^ σ + 1 / m) := by
  obtain ⟨A, hA, hmod⟩ := smoothFluctuation_modulus hd hσ hσ1 c C₀ K lam B hc hcC hlam
  refine ⟨A, hA, ?_⟩
  intro v hv hv0 hv1 hv2 hvH m hm N δ R hN hnet a m₀ ha q hq hgood ε hε hlo hhi
  obtain ⟨η, hη, hdist⟩ := hnet ε hlo hhi
  obtain ⟨hηrange, hηlo, hηhi⟩ := hN η hη
  have hdiff := hmod v hv hv0 hv1 hv2 hvH m hm ε η hε hηrange hlo hhi
    hηlo hηhi q hq a m₀ ha
  have hp : (3 ^ m * |ε - η|) ^ σ ≤ (3 ^ m * δ) ^ σ :=
    Real.rpow_le_rpow (by positivity)
      (mul_le_mul_of_nonneg_left hdist (by positivity)) hσ.le
  calc
    _ ≤ |smoothFluctuation η a m₀ v q| +
        |smoothFluctuation ε a m₀ v q - smoothFluctuation η a m₀ v q| :=
      by
        have h := abs_add_le (smoothFluctuation η a m₀ v q)
          (smoothFluctuation ε a m₀ v q - smoothFluctuation η a m₀ v q)
        have heq : smoothFluctuation η a m₀ v q +
            (smoothFluctuation ε a m₀ v q - smoothFluctuation η a m₀ v q) =
            smoothFluctuation ε a m₀ v q := by ring
        rwa [heq] at h
    _ ≤ R + A * ((3 ^ m * |ε - η|) ^ σ + 1 / m) :=
      add_le_add (hgood η hη) hdiff
    _ ≤ _ := add_le_add le_rfl
      (mul_le_mul_of_nonneg_left (add_le_add hp le_rfl) hA.le)

/-- No positive scale belongs to the zeroth block. -/
lemma blockIndex_ne_zero (U : Set (Fin d → ℝ)) {ε : ℝ} (hε : 0 < ε) :
    TwoScale.blockIndex U ε hε ≠ 0 := by
  have h := (TwoScale.blockIndex_spec U hε).1
  omega

/-- Bounded conductance deviations give a deterministic pointwise bound at every
admissible scale, using the genuine absolutely summable remainder kernel. -/
theorem smoothFluctuation_abs_bound (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, ε ∈ Set.Ioo (0 : ℝ) 1 →
      ∀ (v : (Fin d → ℝ) → ℝ) (B L : ℝ), ContDiff ℝ 2 v →
      (∀ x, |v x| ≤ B) → (∀ x, ‖fderiv ℝ v x‖ ≤ B) →
      (∀ x, ‖iteratedFDeriv ℝ 2 v x‖ ≤ B) → 0 ≤ L →
      ∀ (a : Edge d → ℝ) (m₀ : ℝ), (∀ e, |a e - m₀| ≤ L) →
      ∀ q : Site d, |smoothFluctuation ε a m₀ v q| ≤ C * B * L := by
  classical
  obtain ⟨C, hC, hbound⟩ := smoothRemainder_kernel_abs_sum_bound d
  refine ⟨1 / 2 + C, by positivity, ?_⟩
  intro ε hε v B L hv hv0 hv1 hv2 hL a m₀ ha q
  have hB : 0 ≤ B := (abs_nonneg _).trans (hv0 0)
  obtain ⟨hs, hb⟩ := hbound ε hε v B hv hv0 hv1 hv2 q
  let f := fun w : Site d => if hw : w = 0 then (0 : ℝ) else
    (a (edgeAdd q w hw) - m₀) * jumpKernel (physical ε w) *
      smoothRemainder v (physical ε q) (physical ε w)
  let g := fun w : Site d => if w = 0 then (0 : ℝ) else
    jumpKernel (physical ε w) * |smoothRemainder v (physical ε q) (physical ε w)|
  have hfg (w : Site d) : ‖f w‖ ≤ L * g w := by
    dsimp [f, g]
    split_ifs with hw
    · simp only [abs_zero, mul_zero, le_refl]
    · rw [abs_mul, abs_mul,
        abs_of_nonneg (jumpKernel_nonneg _)]
      calc
        _ ≤ L * jumpKernel (physical ε w) *
            |smoothRemainder v (physical ε q) (physical ε w)| :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (ha _) (jumpKernel_nonneg _)) (abs_nonneg _)
        _ = _ := by ring
  have hk := kappa_pos hd hε
  have hsum : |∑' w, f w| ≤ L * ∑' w, g w := by
    simpa only [Real.norm_eq_abs, tsum_mul_left] using
      (tsum_of_norm_bounded (hs.mul_left L).hasSum hfg)
  change |ε ^ d / kappa d ε * ∑' w, f w| ≤ _
  rw [abs_mul, abs_of_nonneg (div_nonneg (pow_nonneg hε.1.le _) hk.le)]
  calc
    _ ≤ ε ^ d / kappa d ε * (L * ∑' w, g w) :=
      mul_le_mul_of_nonneg_left hsum
        (div_nonneg (pow_nonneg hε.1.le _) hk.le)
    _ = L * (ε ^ d * ∑' w, g w) / kappa d ε := by ring
    _ ≤ L * (B / 2 * kappa d ε + C * B) / kappa d ε :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hb hL) hk.le
    _ = L * (B / 2 + C * B / kappa d ε) := by field_simp
    _ ≤ L * (B / 2 + C * B) := by
      apply mul_le_mul_of_nonneg_left _ hL
      exact add_le_add_right (div_le_self (mul_nonneg hC.le hB)
        (one_le_kappa hd hε)) _
    _ = _ := by ring

/-- A bounded domain has uniformly bounded physical lattice volume at all scales
in `(0,1)`, with its Euclidean diameter used in the lattice counting estimate. -/
theorem lattice_volume_bound {U : Set (Fin d → ℝ)} (hU : Bornology.IsBounded U) :
    ∃ V : ℝ, 0 < V ∧ ∀ ε : ℝ, ε ∈ Set.Ioo (0 : ℝ) 1 →
      ε ^ d * (latticeSet ε U).ncard ≤ V := by
  obtain ⟨V, hV, hcount⟩ := ncard_latticeSet_le d (euclideanDiam U)
  refine ⟨V, hV, ?_⟩
  intro ε hε
  have hc := mul_le_mul_of_nonneg_left (hcount U hU le_rfl ε hε)
    (pow_nonneg hε.1.le d)
  have hid : ε ^ d * (V * ε ^ (-(d : ℝ))) = V := by
    rw [Real.rpow_neg hε.1.le, Real.rpow_natCast]
    field_simp [ne_of_gt hε.1]
  exact hc.trans_eq hid

/-- Uniform ellipticity controls each conductance deviation from the actual mean,
pointwise in the random environment. -/
lemma AssumptionU.abs_sub_mean_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {lam : ℝ} {a : Ω → Edge d → ℝ} (hA : AssumptionU P lam a)
    (ω : Ω) (e : Edge d) :
    |a ω e - meanConductance P hA.one_le_dim a| ≤ lam⁻¹ := by
  obtain ⟨hml, hmu⟩ := hA.mean_mem_Icc
  obtain ⟨hal, hau⟩ := hA.bounds ω e
  apply abs_le.mpr
  constructor <;> linarith [hA.lam_pos]

/-- On any fixed finite collection of positive blocks the fluctuation has the
required inverse square root bound for every environment, with no exceptional set. -/
theorem smoothFluctuation_small_block_bound (hd : 1 ≤ d) (lam B : ℝ)
    (hlam : 0 < lam) {U : Set (Fin d → ℝ)} (hU : Bornology.IsBounded U) (m₀ : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
      {a : Ω → Edge d → ℝ}, ∀ _hA : AssumptionU P lam a,
      ∀ v : (Fin d → ℝ) → ℝ, ContDiff ℝ 2 v →
      (∀ x, |v x| ≤ B) → (∀ x, ‖fderiv ℝ v x‖ ≤ B) →
      (∀ x, ‖iteratedFDeriv ℝ 2 v x‖ ≤ B) → ∀ ω : Ω,
      ∀ m : ℕ, m ≤ m₀ → ∀ ε : ℝ, ∀ hε : ε ∈ Set.Ioo (0 : ℝ) 1,
      TwoScale.blockIndex U ε hε.1 = m →
        l2Norm ε U (smoothFluctuation ε (a ω) (meanConductance P hd a) v) ≤
          C / Real.sqrt m := by
  obtain ⟨D, hD, hpoint⟩ := smoothFluctuation_abs_bound hd
  obtain ⟨V, hV, hvol⟩ := lattice_volume_bound hU
  let A := D * |B| * lam⁻¹ * Real.sqrt V
  refine ⟨A * Real.sqrt m₀ + 1, by dsimp [A]; positivity, ?_⟩
  intro Ω _ P a hA v hv hv0 hv1 hv2 ω m hm ε hε hblock
  have hB : 0 ≤ B := (abs_nonneg _).trans (hv0 0)
  have hpoint' (q : Site d) :
      |smoothFluctuation ε (a ω) (meanConductance P hd a) v q| ≤ D * B * lam⁻¹ :=
    hpoint ε hε v B lam⁻¹ hv hv0 hv1 hv2 (inv_nonneg.mpr hlam.le)
      (a ω) _ (hA.abs_sub_mean_le ω) q
  have hnorm := l2Norm_le_of_count hε.1 hU
    (mul_nonneg (mul_nonneg hD.le hB) (inv_nonneg.mpr hlam.le))
    (hvol ε hε) _ (fun q _ => hpoint' q)
  have hmpos : 0 < m := Nat.pos_of_ne_zero (by
    intro hz
    exact blockIndex_ne_zero U hε.1 (hblock.trans hz))
  have hspos : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hmpos)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hnorm' : l2Norm ε U
      (smoothFluctuation ε (a ω) (meanConductance P hd a) v) ≤ A := by
    simpa only [A, abs_of_nonneg hB] using hnorm
  apply hnorm'.trans
  apply (le_div_iff₀ hspos).mpr
  have hs : Real.sqrt (m : ℝ) ≤ Real.sqrt (m₀ : ℝ) :=
    Real.sqrt_le_sqrt (by exact_mod_cast hm)
  exact (mul_le_mul_of_nonneg_left hs hA).trans (le_add_of_nonneg_right zero_le_one)

/-- The integer box is finite because it is the lattice set of a bounded physical cube. -/
lemma integerBox_finite (d n : ℕ) : (integerBox d n).Finite := by
  rw [← latticeSet_cube zero_lt_one]
  exact latticeSet_finite zero_lt_one (cube_isBounded 1 n)

/-- The Euclidean radius of a site in a triadic integer box is at most its side
length times the square root of the dimension. -/
lemma radius_le_of_mem_integerBox {n : ℕ} {q : Site d} (hq : q ∈ integerBox d n) :
    radius (physical 1 q) ≤ Real.sqrt d * 3 ^ n := by
  have hp : (0 : ℝ) < 3 ^ n := by positivity
  have hs : ∑ i : Fin d, (physical 1 q i) ^ 2 ≤ (d : ℝ) * (3 ^ n) ^ 2 := by
    calc
      _ ≤ ∑ _i : Fin d, (3 ^ n : ℝ) ^ 2 := Finset.sum_le_sum (fun i _ => by
        have hi : |physical 1 q i| ≤ (3 : ℝ) ^ n := by
          simpa only [physical, one_mul] using (hq i).le.trans (by linarith)
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hp.le).mpr hi)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
  apply (sq_le_sq₀ (radius_nonneg _) (by positivity)).mp
  rw [radius_sq, mul_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
  exact hs

/-- The enlarged cube in the block geometry contains every sampled site of the domain. -/
lemma latticeSet_subset_integerBox_of_block {U : Set (Fin d → ℝ)} {ε : ℝ}
    (hε : 0 < ε) {m L : ℕ}
    (hU : U ⊆ TwoScale.openCube 0 (ε * 3 ^ (m + L - 1))) :
    latticeSet ε U ⊆ integerBox d (m + L) := by
  intro q hq
  have hx := hU hq
  have hp : (3 : ℝ) ^ (m + L - 1) ≤ 3 ^ (m + L) :=
    pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)
  have hc : physical ε q ∈ cube ε (m + L) := by
    intro i
    have hi := hx i
    simp only [Pi.zero_apply, sub_zero] at hi
    exact hi.trans_le (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hp hε.le) (by norm_num))
  rw [← latticeSet_cube hε]
  exact hc

/-- A finite net event gives a uniform discrete L² estimate throughout a block
window. The exceptional probability retains the exact finite Gaussian sum. -/
theorem smoothFluctuation_block_net_event (hd : 1 ≤ d) {σ : ℝ}
    (hσ : 0 < σ) (hσ1 : σ ≤ 1) (c C₀ lam B : ℝ)
    (hc : 0 < c) (hcC : c ≤ C₀) (hlam : 0 < lam)
    {U : Set (Fin d → ℝ)} (hU : Bornology.IsBounded U) (L : ℕ) :
    ∃ A D V : ℝ, 0 < A ∧ 0 < D ∧ 0 < V ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {a : Ω → Edge d → ℝ},
      ∀ _hA : AssumptionU P lam a, ∀ v : (Fin d → ℝ) → ℝ,
      ContDiff ℝ 2 v → (∀ x, |v x| ≤ B) → (∀ x, ‖fderiv ℝ v x‖ ≤ B) →
      (∀ x, ‖iteratedFDeriv ℝ 2 v x‖ ≤ B) →
      (∀ x y, ‖iteratedFDeriv ℝ 2 v x - iteratedFDeriv ℝ 2 v y‖ ≤
        B * radius (x - y) ^ σ) → ∀ m : ℕ, 1 ≤ m →
      C₀ / 3 ^ m < 1 → ∀ δ t : ℝ, 0 < δ → 1 ≤ t →
      ∃ (N : Finset ℝ) (G : Set Ω),
        (∀ η ∈ N, c / 3 ^ m ≤ η ∧ η ≤ C₀ / 3 ^ m) ∧
        (N.card : ℝ) ≤ ((C₀ - c) / 3 ^ m) / δ + 1 ∧
        MeasurableSet G ∧
        P Gᶜ ≤ ∑ _p ∈ N ×ˢ (integerBox_finite d (m + L)).toFinset,
          ENNReal.ofReal (Real.exp (-(t ^ (2 : ℝ)))) ∧
        ∀ ω ∈ G, ∀ (ε : ℝ) (_hε : ε ∈ Set.Ioo (0 : ℝ) 1),
          c / 3 ^ m ≤ ε → ε ≤ C₀ / 3 ^ m →
          U ⊆ TwoScale.openCube 0 (ε * 3 ^ (m + L - 1)) →
          l2Norm ε U (smoothFluctuation ε (a ω) (meanConductance P hd a) v) ≤
            (t * D / m + A * ((3 ^ m * δ) ^ σ + 1 / m)) * Real.sqrt V := by
  classical
  let K : ℝ := Real.sqrt d * 3 ^ L
  obtain ⟨A, hA, hext⟩ := smoothFluctuation_le_of_scale_net hd hσ hσ1
    c C₀ K lam B hc hcC hlam
  obtain ⟨F, hF, hfinite⟩ := smoothFluctuation_finite_event d
  obtain ⟨b, hb, hkappa⟩ := le_kappa_block hd C₀ (hc.trans_le hcC)
  obtain ⟨V, hV, hvol⟩ := lattice_volume_bound hU
  let D : ℝ := F * lam⁻¹ * |B| / b + 1
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨A, D, V, hA, hD, hV, ?_⟩
  intro Ω _ P a hAss v hv hv0 hv1 hv2 hvH m hm hhi δ t hδ ht
  have hp : (0 : ℝ) < 3 ^ m := by positivity
  obtain ⟨N, hN, hcard, hnet⟩ := exists_scale_net
    (div_le_div_of_nonneg_right hcC hp.le) hδ
  have hNrange (η : ℝ) (hη : η ∈ N) : η ∈ Set.Ioo (0 : ℝ) 1 :=
    ⟨(div_pos hc hp).trans_le (hN η hη).1, ((hN η hη).2).trans_lt hhi⟩
  let Q := (integerBox_finite d (m + L)).toFinset
  obtain ⟨G, hG, htail, hgood⟩ :=
    hfinite hAss N hNrange Q v B hv hv0 hv1 hv2 t ht
  refine ⟨N, G, hN, ?_, hG, htail, ?_⟩
  · simpa only [sub_div] using hcard
  intro ω hω ε hε hlo hupper hcontain
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm)
  have hB : 0 ≤ B := (abs_nonneg _).trans (hv0 0)
  have ht0 : 0 ≤ t := zero_le_one.trans ht
  have hnetgood (q : Site d) (hq : q ∈ Q) (η : ℝ) (hη : η ∈ N) :
      |smoothFluctuation η (a ω) (meanConductance P hd a) v q| ≤ t * D / m := by
    have hk := hkappa m hm η (hNrange η hη) (hN η hη).2
    have hbmul : 0 < b * (m : ℝ) := mul_pos hb hmpos
    have hnum : 0 ≤ F * lam⁻¹ * B := by positivity
    calc
      _ ≤ t * (F * lam⁻¹ * B / kappa d η) := hgood ω hω η hη q hq
      _ ≤ t * (F * lam⁻¹ * B / (b * m)) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left hnum hbmul hk) ht0
      _ = t * (F * lam⁻¹ * |B| / b) / m := by
        rw [abs_of_nonneg hB]
        ring
      _ ≤ _ := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) ht0) hmpos.le
  have hM : 0 ≤ t * D / m + A * ((3 ^ m * δ) ^ σ + 1 / m) := by positivity
  apply l2Norm_le_of_count hε.1 hU hM (hvol ε hε)
  intro q hq
  have hqbox := latticeSet_subset_integerBox_of_block hε.1 hcontain hq
  have hqQ : q ∈ Q := (integerBox_finite d (m + L)).mem_toFinset.mpr hqbox
  have hqrad : radius (physical 1 q) ≤ K * 3 ^ m := by
    calc
      _ ≤ Real.sqrt d * 3 ^ (m + L) := radius_le_of_mem_integerBox hqbox
      _ = _ := by dsimp [K]; rw [pow_add]; ring
  exact hext v hv hv0 hv1 hv2 hvH m hm N δ (t * D / m)
    (fun η hη => ⟨hNrange η hη, hN η hη⟩) hnet (a ω)
    (meanConductance P hd a) (hAss.abs_sub_mean_le ω) q hqrad
    (hnetgood q hqQ) ε hε hlo hupper

/-- A triadic integer box has at most the cardinality of the closed integer cube
of coordinate radius `3^n`, bounded here by `3^(d*(n+1))`. -/
lemma integerBox_ncard_le (d n : ℕ) :
    ((integerBox d n).ncard : ℝ) ≤ (3 : ℝ) ^ (d * (n + 1)) := by
  classical
  let Q := Fintype.piFinset (fun _ : Fin d =>
    Finset.Icc (-(3 ^ n : ℤ)) (3 ^ n))
  have hsub : integerBox d n ⊆ (Q : Set (Site d)) := by
    intro q hq
    rw [Finset.mem_coe, Fintype.mem_piFinset]
    intro i
    have hp : (0 : ℝ) < 3 ^ n := by positivity
    have hi : |(q i : ℝ)| ≤ (3 : ℝ) ^ n := (hq i).le.trans (by linarith)
    have hi' : |q i| ≤ (3 : ℤ) ^ n := by exact_mod_cast hi
    exact Finset.mem_Icc.mpr (abs_le.mp hi')
  have hc : Q.card = (2 * (3 ^ n : ℤ) + 1).toNat ^ d := by
    simp only [Q, Fintype.card_piFinset, Int.card_Icc]
    have he : (3 : ℤ) ^ n + 1 - -(3 ^ n) = 2 * 3 ^ n + 1 := by ring
    simp only [he, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hcount := Set.ncard_le_ncard hsub (Finset.finite_toSet Q)
  rw [Set.ncard_coe_finset, hc] at hcount
  have hcast : ((2 * (3 ^ n : ℤ) + 1).toNat : ℝ) = 2 * (3 : ℝ) ^ n + 1 := by
    have hh : ((2 * (3 ^ n : ℤ) + 1).toNat : ℤ) = 2 * 3 ^ n + 1 :=
      Int.toNat_of_nonneg (by positivity)
    exact_mod_cast hh
  calc
    _ ≤ ((2 * (3 ^ n : ℤ) + 1).toNat : ℝ) ^ d := by exact_mod_cast hcount
    _ = (2 * (3 : ℝ) ^ n + 1) ^ d := by rw [hcast]
    _ ≤ (3 * (3 : ℝ) ^ n) ^ d := pow_le_pow_left₀ (by positivity)
      (by have hp := one_le_pow₀ (show (1 : ℝ) ≤ 3 by norm_num) (n := n); linarith) d
    _ = _ := by rw [mul_comm (3 : ℝ), ← pow_succ, ← pow_mul]; congr 1; exact Nat.mul_comm _ _

/-- The mesh prescribed by the Hölder exponent has modulus error at most twice
 the inverse square root of the positive block index. -/
lemma scale_mesh_error {σ : ℝ} (hσ : 0 < σ) {m : ℕ} (hm : 1 ≤ m) :
    ((3 : ℝ) ^ m * ((3 ^ m)⁻¹ * (m : ℝ) ^ (-(1 / (2 * σ))))) ^ σ +
        1 / m ≤ 2 / Real.sqrt m := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := zero_lt_one.trans_le hm1
  have hp : (3 : ℝ) ^ m ≠ 0 := by positivity
  have he : -(1 / (2 * σ)) * σ = -(1 / 2 : ℝ) := by field_simp
  have hpow : ((3 : ℝ) ^ m *
      ((3 ^ m)⁻¹ * (m : ℝ) ^ (-(1 / (2 * σ))))) ^ σ = 1 / Real.sqrt m := by
    rw [← mul_assoc, mul_inv_cancel₀ hp, one_mul, ← Real.rpow_mul hm0.le, he,
      Real.rpow_neg hm0.le, ← Real.sqrt_eq_rpow, one_div]
  have hs : Real.sqrt (m : ℝ) ≤ m := Real.sqrt_le_self_iff.mpr (Or.inr hm1)
  have hi : 1 / (m : ℝ) ≤ 1 / Real.sqrt m :=
    one_div_le_one_div_of_le (Real.sqrt_pos.mpr hm0) hs
  rw [hpow]
  calc
    _ ≤ 1 / Real.sqrt m + 1 / Real.sqrt m := add_le_add le_rfl hi
    _ = _ := by ring

/-- The finite Gaussian sum is the product of the two finite cardinalities and
the individual tail, embedded in the nonnegative extended reals. -/
lemma finite_gaussian_sum_eq {α β : Type*} (N : Finset α) (Q : Finset β) (t : ℝ) :
    (∑ _p ∈ N ×ˢ Q, ENNReal.ofReal (Real.exp (-(t ^ (2 : ℝ))))) =
      ENNReal.ofReal ((N.card : ℝ) * Q.card * Real.exp (-(t ^ (2 : ℝ)))) := by
  rw [Finset.sum_const, ← ENNReal.ofReal_nsmul]
  simp only [Finset.card_product, nsmul_eq_mul, Nat.cast_mul]

/-- Polynomial net growth and the triadic site count are absorbed by the Gaussian
exponent, with a constant independent of the block index. -/
lemma block_gaussian_count_bound {r H : ℝ} (hr : 0 ≤ r) (hH : 0 ≤ H)
    (d L m : ℕ) (hm : 1 ≤ m) {n q : ℝ} (hn : 0 ≤ n)
    (hnet : n ≤ H * (m : ℝ) ^ r) (hbox : q ≤ (3 : ℝ) ^ (d * (m + L + 1))) :
    n * q * Real.exp (-((r + d * Real.log 3 + 2) * m)) ≤
      H * 3 ^ (d * (L + 1)) * Real.exp (-(m : ℝ)) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm)
  have hpoly : (m : ℝ) ^ r ≤ Real.exp (r * m) := by
    rw [Real.rpow_def_of_pos hm0]
    apply Real.exp_le_exp.mpr
    have hl : Real.log (m : ℝ) ≤ m :=
      (Real.log_le_sub_one_of_pos hm0).trans (by linarith)
    simpa only [mul_comm] using mul_le_mul_of_nonneg_right hl hr
  have hbox' : q ≤ 3 ^ (d * (L + 1)) * Real.exp ((d * Real.log 3) * m) := by
    have he : Real.exp (((d : ℝ) * Real.log 3) * m) = (3 : ℝ) ^ (d * m) := by
      rw [show ((d : ℝ) * Real.log 3) * m = ((d * m : ℕ) : ℝ) * Real.log 3 by
        push_cast; ring, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 3)]
    rw [he, ← pow_add]
    convert hbox using 1
    congr 1
    ring
  have hnet' := hnet.trans (mul_le_mul_of_nonneg_left hpoly hH)
  calc
    _ ≤ (H * Real.exp (r * m)) *
        (3 ^ (d * (L + 1)) * Real.exp ((d * Real.log 3) * m)) *
        Real.exp (-((r + d * Real.log 3 + 2) * m)) :=
      mul_le_mul_of_nonneg_right
        ((mul_le_mul_of_nonneg_left hbox' hn).trans
          (mul_le_mul_of_nonneg_right hnet' (by positivity))) (Real.exp_pos _).le
    _ = H * 3 ^ (d * (L + 1)) * Real.exp (-2 * m) := by
      rw [show (H * Real.exp (r * m)) *
          (3 ^ (d * (L + 1)) * Real.exp ((d * Real.log 3) * m)) *
          Real.exp (-((r + d * Real.log 3 + 2) * m)) =
          H * 3 ^ (d * (L + 1)) *
            ((Real.exp (r * m) * Real.exp ((d * Real.log 3) * m)) *
              Real.exp (-((r + d * Real.log 3 + 2) * m))) by ring]
      rw [← Real.exp_add, ← Real.exp_add]
      congr 2
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith))
      (mul_nonneg hH (by positivity))

/-- The scale-net cardinality at the prescribed mesh is polynomial in the block
index, with degree determined by the Hölder exponent. -/
lemma scale_mesh_card_bound {σ c C₀ : ℝ} (hσ : 0 < σ) (_hcC : c ≤ C₀)
    {m : ℕ} (hm : 1 ≤ m) {n : ℝ}
    (hn : n ≤ ((C₀ - c) / (3 : ℝ) ^ m) /
      ((3 ^ m)⁻¹ * (m : ℝ) ^ (-(1 / (2 * σ)))) + 1) :
    n ≤ (C₀ - c + 1) * (m : ℝ) ^ (1 / (2 * σ)) := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := zero_lt_one.trans_le hm1
  have hp : (3 : ℝ) ^ m ≠ 0 := by positivity
  have hr : 0 ≤ 1 / (2 * σ) := by positivity
  have hmp : (m : ℝ) ^ (1 / (2 * σ)) ≠ 0 := (Real.rpow_pos_of_pos hm0 _).ne'
  have he : ((C₀ - c) / (3 : ℝ) ^ m) /
      ((3 ^ m)⁻¹ * (m : ℝ) ^ (-(1 / (2 * σ)))) =
      (C₀ - c) * (m : ℝ) ^ (1 / (2 * σ)) := by
    rw [Real.rpow_neg hm0.le]
    field_simp
  have hpow : 1 ≤ (m : ℝ) ^ (1 / (2 * σ)) := Real.one_le_rpow hm1 hr
  calc
    n ≤ (C₀ - c) * (m : ℝ) ^ (1 / (2 * σ)) + 1 := by rwa [he] at hn
    _ ≤ (C₀ - c) * (m : ℝ) ^ (1 / (2 * σ)) +
        (m : ℝ) ^ (1 / (2 * σ)) := add_le_add le_rfl hpow
    _ = _ := by ring

/-- The Gaussian parameter proportional to the square root of the block index
gives the desired inverse square root amplitude after division by the index. -/
lemma sqrt_block_threshold {T D : ℝ} (hT : 0 ≤ T) {m : ℕ} (hm : 1 ≤ m) :
    Real.sqrt (T * m) * D / m = Real.sqrt T * D / Real.sqrt m := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm)
  rw [Real.sqrt_mul hT]
  calc
    _ = Real.sqrt T * D * (Real.sqrt (m : ℝ) / m) := by ring
    _ = _ := by rw [Real.sqrt_div_self]; ring

/-- The measurable finite-net event controls the smooth fluctuation on every scale
of a block, with exponentially decaying exceptional probability. -/
theorem block_fluctuation_event (hd : 1 ≤ d) {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (lam B : ℝ) (hlam : 0 < lam) {U : Set (Fin d → ℝ)} (hUo : IsOpen U)
    (hU : Bornology.IsBounded U) (hne : U.Nonempty) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
      (a : Ω → Edge d → ℝ), AssumptionU P lam a → ∀ v : (Fin d → ℝ) → ℝ,
      ContDiff ℝ 2 v → (∀ x, |v x| ≤ B) → (∀ x, ‖fderiv ℝ v x‖ ≤ B) →
      (∀ x, ‖iteratedFDeriv ℝ 2 v x‖ ≤ B) →
      (∀ x y, ‖iteratedFDeriv ℝ 2 v x - iteratedFDeriv ℝ 2 v y‖ ≤
        B * radius (x - y) ^ σ) → ∀ m : ℕ, ∃ G : Set Ω, MeasurableSet G ∧
        P Gᶜ ≤ ENNReal.ofReal (C * Real.exp (-(c * m))) ∧
        ∀ ω ∈ G, ∀ (ε : ℝ) (hε : ε ∈ Set.Ioo (0 : ℝ) 1),
          TwoScale.blockIndex U ε hε.1 = m →
          l2Norm ε U (smoothFluctuation ε (a ω) (meanConductance P hd a) v) ≤
            C / Real.sqrt m := by
  classical
  obtain ⟨c, C₀, hc, hcC, L, _hL, hgeometry⟩ :=
    TwoScale.block_geometry hd hU hUo hne
  obtain ⟨A, D, V, hA, hD, hV, hnetevent⟩ := smoothFluctuation_block_net_event
    hd hσ hσ1 c C₀ lam B hc hcC hlam hU L
  obtain ⟨m₀, hcut⟩ := pow_unbounded_of_one_lt C₀ (by norm_num : (1 : ℝ) < 3)
  obtain ⟨S, hS, hsmall⟩ := smoothFluctuation_small_block_bound hd lam B hlam hU m₀
  let r : ℝ := 1 / (2 * σ)
  let T : ℝ := r + d * Real.log 3 + 2
  let H : ℝ := C₀ - c + 1
  let F : ℝ := (Real.sqrt T * D + 2 * A) * Real.sqrt V
  let E : ℝ := H * 3 ^ (d * (L + 1))
  let C : ℝ := S + F + E + 1
  have hr : 0 < r := by dsimp [r]; positivity
  have hlog : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hT : 1 ≤ T := by
    dsimp [T]
    have hh := mul_nonneg (Nat.cast_nonneg d) hlog
    linarith
  have hH : 0 < H := by dsimp [H]; linarith
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hSC : S ≤ C := by dsimp [C]; linarith
  have hFC : F ≤ C := by dsimp [C]; linarith
  have hEC : E ≤ C := by dsimp [C]; linarith
  refine ⟨C, 1, by dsimp [C]; positivity, zero_lt_one, ?_⟩
  intro Ω _ P a hAss v hv hv0 hv1 hv2 hvH m
  by_cases hms : m ≤ m₀
  · refine ⟨Set.univ, MeasurableSet.univ, ?_, ?_⟩
    · simp only [Set.compl_univ, measure_empty]
      exact bot_le
    · intro ω _ ε hε hblock
      exact (hsmall hAss v hv hv0 hv1 hv2 ω m hms ε hε hblock).trans
        (div_le_div_of_nonneg_right hSC (Real.sqrt_nonneg _))
  have hm : 1 ≤ m := by omega
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := zero_lt_one.trans_le hm1
  have hp : (0 : ℝ) < 3 ^ m := by positivity
  have hhi : C₀ / 3 ^ m < 1 := by
    rw [div_lt_one hp]
    exact hcut.trans_le (pow_le_pow_right₀ (by norm_num) (by omega))
  let δ : ℝ := (3 ^ m)⁻¹ * (m : ℝ) ^ (-r)
  let t : ℝ := Real.sqrt (T * m)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have ht : 1 ≤ t := Real.one_le_sqrt.mpr (by
    simpa only [one_mul] using mul_le_mul hT hm1 zero_le_one (zero_le_one.trans hT))
  obtain ⟨N, G, _hN, hcard, hG, htail, hgood⟩ :=
    hnetevent hAss v hv hv0 hv1 hv2 hvH m hm hhi δ t hδ ht
  refine ⟨G, hG, ?_, ?_⟩
  · have hnetcard : (N.card : ℝ) ≤ H * (m : ℝ) ^ r :=
      scale_mesh_card_bound hσ hcC hm hcard
    have hcount := block_gaussian_count_bound hr.le hH.le d L m hm
      (Nat.cast_nonneg N.card) hnetcard (integerBox_ncard_le d (m + L))
    have htexp : t ^ (2 : ℝ) = T * m := by
      rw [Real.rpow_two, Real.sq_sqrt (mul_nonneg (zero_le_one.trans hT) hm0.le)]
    have htail' : P Gᶜ ≤ ENNReal.ofReal (E * Real.exp (-(m : ℝ))) := by
      apply htail.trans
      rw [finite_gaussian_sum_eq, htexp]
      apply ENNReal.ofReal_le_ofReal
      simpa only [← Set.ncard_eq_toFinset_card, E, T, Nat.add_assoc] using hcount
    apply htail'.trans
    apply ENNReal.ofReal_le_ofReal
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hEC (Real.exp_pos _).le
  · intro ω hω ε hε hblock
    obtain ⟨hlo, hupper, hcontain⟩ := hgeometry ε hε
    rw [hblock] at hlo hupper hcontain
    have hbound := hgood ω hω ε hε hlo hupper hcontain
    have herror : ((3 : ℝ) ^ m * δ) ^ σ + 1 / m ≤ 2 / Real.sqrt m :=
      scale_mesh_error hσ hm
    calc
      _ ≤ (t * D / m + A * ((3 ^ m * δ) ^ σ + 1 / m)) * Real.sqrt V := hbound
      _ ≤ (t * D / m + A * (2 / Real.sqrt m)) * Real.sqrt V :=
        mul_le_mul_of_nonneg_right
          (add_le_add le_rfl (mul_le_mul_of_nonneg_left herror hA.le))
          (Real.sqrt_nonneg _)
      _ = F / Real.sqrt m := by
        rw [show t * D / m = Real.sqrt T * D / Real.sqrt m from
          sqrt_block_threshold (zero_le_one.trans hT) hm]
        dsimp [F]
        ring
      _ ≤ C / Real.sqrt m := div_le_div_of_nonneg_right hFC (Real.sqrt_nonneg _)

end
end LongRange
